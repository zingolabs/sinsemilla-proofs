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

/-- A lockstep lane computes `weightedStep` (no group facts: `ShortWeierstrass.add` branches
line up, `y ≠ ty` with same `x` on-curve ⇒ `y = −ty` ⇒ `P + T = 𝒪`) -/
theorem laneStep_eq_weightedStep {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    laneStep P T ((2 : ℕ) • T).x = weightedStep P T := by
  sorry

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
  sorry

/-- Each live lane receives its own denominator's inverse -/
theorem batchInverses_eq {ds : List Fp} (h : ∀ d ∈ ds, d ≠ 0) :
    batchInverses ds = ds.map (·⁻¹) := by
  sorry

end SinsemillaProofs
