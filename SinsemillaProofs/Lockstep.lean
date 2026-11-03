import SinsemillaProofs.Weighted
import Mathlib.Tactic.LinearCombination

/-!
# The lockstep lane and the fused batch inversion

References:
- `sinsemilla` crate at `elicbarbieri/sinsemilla` commit `eb3e2f50ef363774169ae8f8877712689e654674`
  (branch `perf/hash-many-vartime`), files `src/table.rs` (`add_in_lockstep`,
  `TableDomain::hash_many_vartime`) and `src/lib.rs` (`HashDomain::hash_many_vartime`)

`TableDomain::hash_many_vartime` hashes a batch of equal-length messages together. Every message is
an affine accumulator, a lane, and `add_in_lockstep` advances all lanes by one chunk with a single
field inversion, Montgomery's trick fused into its two passes. `laneStep` is the per-lane branch
structure of that function on raw affine coordinates, with the tests in the Rust's order: the
`x`-test against the doubled entry, then the chord when the `x`-coordinates differ, then the
tangent when the lane *is* the addend (an ordinary doubling, which the specification does not treat
as `⊥`), and `⊥` when it is the addend's negation. `batchInverses` is the fused Montgomery trick
over the live lanes' denominators, in order.

Together the two results say that each live lane receives its own denominator's inverse and then
computes `weightedStep`; a lane that is already `⊥` stays `⊥`, which is the Rust's `continue` and
this model's `Option.bind`. Not modelled: the dispatch between this path and the Jacobian one at
`LOCKSTEP_LANES`, which selects between two evaluators both proved here, and the fallback of
`HashDomain::hash_many_vartime` to `accumulate` for untabled domains and uncovered lengths, which
is the specification's own recurrence rather than the weighted evaluator.
-/

namespace SinsemillaProofs

open Zcash.Circuits
open CompElliptic.CurveForms

/-- One lockstep lane, `lane + addend`, with the tests in the Rust's order: `⊥` when
`lane.x = doubledX` (`doubled[j].x`, the `x` of `[2]·addend`); the chord with denominator
`addend.x − lane.x` when the `x`-coordinates differ; the tangent `3x² / 2y` (Pallas has `a = 0`)
when `lane = addend`; and `⊥` otherwise, where `lane = −addend`. -/
def laneStep (lane addend : Point Fp) (doubledX : Fp) : Option (Point Fp) :=
  if lane.x = doubledX then none
  else if lane.x ≠ addend.x then
    let l := (addend.y - lane.y) / (addend.x - lane.x)
    let x₃ := l ^ 2 - lane.x - addend.x
    some ⟨x₃, l * (lane.x - x₃) - lane.y⟩
  else if lane.y = addend.y then
    let l := 3 * lane.x ^ 2 / (2 * lane.y)
    let x₃ := l ^ 2 - lane.x - addend.x
    some ⟨x₃, l * (lane.x - x₃) - lane.y⟩
  else none

private theorem two_nsmul_eq_add_self (T : Point Fp) : (2 : ℕ) • T = T + T := by
  simp only [Point.nsmul_def, ShortWeierstrass.smul, ShortWeierstrass.zero_add, Point.add_def]

/-- A lockstep lane computes `weightedStep`: the branches line up with `ShortWeierstrass.add`'s, a
shared `x` means `T = ±P` (`x_eq_iff_eq_or_eq_neg`), and `P + P ≠ 𝒪` (`two_pow_nsmul_onCurve`)
keeps the doubling out of the `⊥` set. -/
theorem laneStep_eq_weightedStep {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    laneStep P T ((2 : ℕ) • T).x = weightedStep P T := by
  have hP0 : P ≠ 0 := Point.ne_zero_of_onCurve hP
  have hT0 : T ≠ 0 := Point.ne_zero_of_onCurve hT
  unfold laneStep weightedStep
  by_cases hD : P.x = ((2 : ℕ) • T).x
  · rw [if_pos hD, if_pos (.inl hD)]
  simp only [hD, false_or, if_false]
  by_cases hx : P.x = T.x
  · have hPx : P.x ≠ 0 := fun h => Point.no_onCurve_of_x_zero P.y (by rwa [← h])
    have hyy : P.y + P.y ≠ 0 :=
      add_self_ne_zero (Point.y_ne_zero_of_valid_of_x_ne_zero (.inl hP) hPx)
    rcases (x_eq_iff_eq_or_eq_neg hT hP).mp hx.symm with h | h <;> subst T
    · -- `T = P`: tangent branch
      have h2 : P + P ≠ 0 :=
        two_nsmul_eq_add_self P ▸ Point.ne_zero_of_onCurve (two_pow_nsmul_onCurve hP 1)
      rw [if_neg h2]
      simp only [ne_eq, not_true_eq_false, if_false, if_true, Point.add_def, ShortWeierstrass.add,
        Point.coords, Prod.mk.injEq, hPx, false_and, hyy, pallasA, add_zero, Point.ofCoords]
    · -- `T = −P`: both ⊥ (`ShortWeierstrass.add_neg`)
      have h0 : P + -P = 0 := congrArg Point.ofCoords (ShortWeierstrass.add_neg pallasA P.coords)
      have hne : ¬ P.y = -P.y := fun h => hyy (by linear_combination h)
      simp only [Point.neg_x, Point.neg_y, ne_eq, not_true_eq_false, if_false, hne, h0, if_true]
  · have hsum : P + T ≠ 0 := Point.nondegenerateAdd_eq_add hP0 hT0 hx ▸
      Point.ne_zero_of_onCurve (Point.nondegenerateAdd_onCurve hP hT hx)
    rw [if_pos hx, if_neg hsum, ← Point.nondegenerateAdd_eq_add hP0 hT0 hx]
    simp only [Point.nondegenerateAdd, div_eq_mul_inv, sq]

/-- The fused Montgomery trick one slot at a time. `before` is the product of the denominators
already passed on the forward pass (`product_before`); the result pairs the running inverse once the
backward pass has passed this slot (`inverse`, after `inverse *= denominator`) with the inverses of
`ds`. -/
def batchInverses.go (before : Fp) : List Fp → Fp × List Fp
  | [] => (before⁻¹, [])
  | d :: ds =>
    let (inverse, rest) := batchInverses.go (before * d) ds
    (inverse * d, inverse * before :: rest)

/-- The Rust's fused Montgomery trick over the live lanes' denominators, in order: the descent is
the forward pass (`product *= denominator`), the base case is the single `invert_vartime` of the
total product, and the return is the backward pass (`inverse_here = inverse · product_before`, then
`inverse *= denominator`). -/
def batchInverses (ds : List Fp) : List Fp := (batchInverses.go 1 ds).2

theorem batchInverses_go {before : Fp} (hb : before ≠ 0) {ds : List Fp}
    (h : ∀ d ∈ ds, d ≠ 0) : batchInverses.go before ds = (before⁻¹, ds.map (·⁻¹)) := by
  induction ds generalizing before with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨hd, h⟩ := List.forall_mem_cons.mp h
    simp only [batchInverses.go, ih (mul_ne_zero hb hd) h, List.map_cons, mul_inv,
      inv_mul_cancel_right₀ hd, mul_right_comm before⁻¹, inv_mul_cancel₀ hb, one_mul]

/-- Each live lane receives its own denominator's inverse: with every denominator non-zero, the
fused trick returns exactly the pointwise inverses. -/
theorem batchInverses_eq {ds : List Fp} (h : ∀ d ∈ ds, d ≠ 0) :
    batchInverses ds = ds.map (·⁻¹) :=
  congrArg Prod.snd (batchInverses_go one_ne_zero h)

end SinsemillaProofs
