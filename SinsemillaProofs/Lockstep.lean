import SinsemillaProofs.Weighted

/-!
# `add_in_lockstep` (`table.rs`): one lane, and the fused batch inversion

- `laneStep` = per-lane branch structure of the Rust (first pass tests, second pass formulas), on
  raw affine coordinates (`Lane = (x, y)`)
- `batchInverses` = Montgomery's trick as fused into the two passes (live lanes only)
- Together: `inverse_here = denominator⁻¹`, so each live lane computes `laneStep` = `weightedStep`
- Dead lanes (`None`) stay dead: Rust `continue`, here `Option.bind` in `hash_many_vartime`
-/

namespace SinsemillaProofs

open Zcash.Circuits
open CompElliptic.CurveForms

/-- One lockstep lane: `lane + addend`, tests in Rust order

- `lane.x = doubledX` → ⊥ (`doubledX` = `doubled[j].x` = x of `[2]·addend`)
- `lane.x ≠ addend.x` → chord, denominator `addend.x − x`
- `lane.y = addend.y` (`lane = addend`) → tangent `3x² / 2y` (`a = 0`), an ordinary doubling
- else (`lane = −addend`) → ⊥ -/
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

/-- A lockstep lane computes `weightedStep`: `ShortWeierstrass.add` branches line up; shared `x`
⇒ `T = ±P` (`x_eq_iff_eq_or_eq_neg`), `P + P ≠ 𝒪` (`two_pow_nsmul_onCurve`) -/
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

/-- Rust's fused Montgomery trick over the live lanes' denominators, in order

- Descent = forward pass (`product_before` = `before`, `product *= denominator`)
- Base = the one `invert_vartime` of the total product
- Return = backward pass (`inverse_here = inverse · product_before`, `inverse *= denominator`) -/
def batchInverses (ds : List Fp) : List Fp := (go 1 ds).2
where
  /-- `(inverse once the backward pass has passed this slot, inverses of `ds`)` -/
  go (before : Fp) : List Fp → Fp × List Fp
    | [] => (before⁻¹, [])
    | d :: ds =>
      let (inverse, rest) := go (before * d) ds
      (inverse * d, inverse * before :: rest)

theorem batchInverses_go {before : Fp} (hb : before ≠ 0) {ds : List Fp}
    (h : ∀ d ∈ ds, d ≠ 0) : batchInverses.go before ds = (before⁻¹, ds.map (·⁻¹)) := by
  induction ds generalizing before with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨hd, h⟩ := List.forall_mem_cons.mp h
    simp only [batchInverses.go, ih (mul_ne_zero hb hd) h, List.map_cons, mul_inv,
      inv_mul_cancel_right₀ hd, mul_right_comm before⁻¹, inv_mul_cancel₀ hb, one_mul]

/-- Each live lane receives its own denominator's inverse -/
theorem batchInverses_eq {ds : List Fp} (h : ∀ d ∈ ds, d ≠ 0) :
    batchInverses ds = ds.map (·⁻¹) :=
  congrArg Prod.snd (batchInverses_go one_ne_zero h)

end SinsemillaProofs
