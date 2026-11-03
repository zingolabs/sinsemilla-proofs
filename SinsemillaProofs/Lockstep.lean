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

/-- A lockstep lane computes `weightedStep` (no group facts: `ShortWeierstrass.add` branches
line up, `y ≠ ty` with same `x` on-curve ⇒ `y = −ty` ⇒ `P + T = 𝒪`) -/
theorem laneStep_eq_weightedStep {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    laneStep P T ((2 : ℕ) • T).x = weightedStep P T := by
  have hP0 : P ≠ 0 := Point.ne_zero_of_onCurve hP
  have hT0 : T ≠ 0 := Point.ne_zero_of_onCurve hT
  unfold laneStep weightedStep
  by_cases hD : P.x = ((2 : ℕ) • T).x
  · simp only [hD, true_or, if_true]
  simp only [hD, false_or, if_false]
  by_cases hx : P.x = T.x
  · have hTx : T.x ≠ 0 := fun h => Point.no_onCurve_of_x_zero T.y (by rwa [← h])
    have hTy : T.y ≠ 0 := Point.y_ne_zero_of_valid_of_x_ne_zero (.inl hT) hTx
    have hPx : P.x ≠ 0 := hx ▸ hTx
    obtain ⟨x, y⟩ := P
    obtain ⟨tx, ty⟩ := T
    simp only at hx hPx hTx hTy
    subst hx
    simp only [ne_eq, not_true_eq_false, if_false]
    have hP0' : ¬ (x, y) = (0, 0) := by simpa [Point.zero_def] using hP0
    rcases Point.y_eq_or_neg_of_same_x (.inl hT) (.inl hP) hTx hPx rfl with hy | hy
    · -- `P = T`: tangent branch, `[2]T ≠ 𝒪` from `two_pow_nsmul_onCurve`
      subst hy
      have h2 : (⟨x, y⟩ : Point Fp) + ⟨x, y⟩ ≠ 0 :=
        two_nsmul_eq_add_self _ ▸ Point.ne_zero_of_onCurve (two_pow_nsmul_onCurve hT 1)
      simp only [if_true, h2, if_false]
      congr 1
      rw [Point.add_def, ShortWeierstrass.add, Point.coords, if_neg hP0', if_neg hP0', if_pos rfl,
        if_neg (add_self_ne_zero hTy)]
      simp only [pallasA, add_zero, Point.ofCoords]
    · -- `P = −T`: both ⊥
      subst hy
      have hne : -ty ≠ ty := fun h => add_self_ne_zero hTy (by linear_combination -h)
      have h0 : (⟨x, -ty⟩ : Point Fp) + ⟨x, ty⟩ = 0 := by
        rw [Point.add_def, ShortWeierstrass.add, Point.coords, Point.coords, if_neg hP0',
          if_neg (by simpa [Point.zero_def] using hT0), if_pos rfl, if_pos (by ring)]
        rfl
      simp only [hne, h0, if_false, if_true]
  · have hsum : P + T ≠ 0 := Point.nondegenerateAdd_eq_add hP0 hT0 hx ▸
      Point.ne_zero_of_onCurve (Point.nondegenerateAdd_onCurve hP hT hx)
    simp only [hx, ne_eq, not_false_eq_true, if_true, hsum, if_false]
    rw [← Point.nondegenerateAdd_eq_add hP0 hT0 hx]
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
    have hd : d ≠ 0 := h d List.mem_cons_self
    rw [batchInverses.go, ih (mul_ne_zero hb hd) fun e he => h e (List.mem_cons_of_mem d he)]
    simp only [List.map_cons, mul_inv, inv_mul_cancel_right₀ hd, mul_right_comm before⁻¹,
      inv_mul_cancel₀ hb, one_mul]

/-- Each live lane receives its own denominator's inverse -/
theorem batchInverses_eq {ds : List Fp} (h : ∀ d ∈ ds, d ≠ 0) :
    batchInverses ds = ds.map (·⁻¹) :=
  congrArg Prod.snd (batchInverses_go one_ne_zero h)

end SinsemillaProofs
