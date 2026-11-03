import SinsemillaProofs.Weighted

/-!
# `Jacobian::step` (`table.rs`, `hash_each_vartime` below `LOCKSTEP_LANES`)

- Soundness: a returned point = `weightedStep` on the affine view, `Z ≠ 0` kept
- Completeness of `none`: `weightedStep` ⊥ ⇒ `none` (no ⊥ hashed silently)
- `none` ⊋ ⊥: also `affine = addend` (a doubling); either way Rust reruns the whole message through
  `hash_to_point` = `weightedHashToPoint` (`weightedHashToPoint_eq_hashToPoint`)
- `FIRST_STEPS` entry `None` → accumulator `None` → same fallback
-/

namespace SinsemillaProofs

open Zcash.Circuits

/-- `(X, Y, Z)` for the affine `(X / Z², Y / Z³)` -/
structure Jac where
  X : Fp
  Y : Fp
  Z : Fp

def Jac.affine (p : Jac) : Point Fp := ⟨p.X / p.Z ^ 2, p.Y / p.Z ^ 3⟩

/-- Rust `Jacobian::step`: `has_x_of`-style test `X = doubled.x · Z²`, then `h = 0`
(`X = addend.x · Z²`), then madd-2007-bl (`Z₃ = 2·Z·h`) -/
def jacStep (p : Jac) (addend doubled : Point Fp) : Option Jac :=
  let zz := p.Z ^ 2
  if p.X = doubled.x * zz then none
  else
    let h := addend.x * zz - p.X
    if h = 0 then none
    else
      let hh := h ^ 2
      let i := 4 * hh
      let j := h * i
      let r := 2 * (addend.y * p.Z * zz - p.Y)
      let v := p.X * i
      let x := r ^ 2 - j - 2 * v
      some ⟨x, r * (v - x) - 2 * (p.Y * j), (p.Z + h) ^ 2 - zz - hh⟩

/-- Exactly which steps are handed back: `x(P) = x([2]T)` (⊥) or `x(P) = x(T)` (`P = −T` ⊥, or
`P = T` doubling) -/
theorem jacStep_eq_none_iff {p : Jac} {T : Point Fp} (hZ : p.Z ≠ 0) :
    jacStep p T ((2 : ℕ) • T) = none ↔
      p.affine.x = ((2 : ℕ) • T).x ∨ p.affine.x = T.x := by
  simp only [jacStep, Jac.affine, div_eq_iff (pow_ne_zero 2 hZ), sub_eq_zero.trans eq_comm]
  split_ifs <;> simp [*]

theorem jacStep_sound {p p' : Jac} {T : Point Fp} (hZ : p.Z ≠ 0) (hP : p.affine.OnCurve)
    (hT : T.OnCurve) (h : jacStep p T ((2 : ℕ) • T) = some p') :
    p'.Z ≠ 0 ∧ weightedStep p.affine T = some p'.affine := by
  obtain ⟨X, Y, Z⟩ := p
  -- reparametrise `X` by `h = T.x·Z² − X` (every madd-2007-bl denominator = power of `2·Z·h`)
  obtain ⟨h', rfl⟩ : ∃ h', X = T.x * Z ^ 2 - h' := ⟨T.x * Z ^ 2 - X, by ring⟩
  simp only [jacStep, sub_sub_cancel] at h
  split_ifs at h with h1 h2
  obtain rfl := Option.some.inj h
  have hzz : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  set P := Jac.affine ⟨T.x * Z ^ 2 - h', Y, Z⟩ with hPdef
  have hx : P.x ≠ T.x := fun hc => h2 (by linear_combination -((div_eq_iff hzz).mp hc))
  have h1' : ¬ P.x = ((2 : ℕ) • T).x := fun hc => h1 ((div_eq_iff hzz).mp hc)
  have hP0 : P ≠ 0 := Point.ne_zero_of_onCurve hP
  have hT0 : T ≠ 0 := Point.ne_zero_of_onCurve hT
  have hsum : P + T ≠ 0 := Point.nondegenerateAdd_eq_add hP0 hT0 hx ▸
    Point.ne_zero_of_onCurve (Point.nondegenerateAdd_onCurve hP hT hx)
  rw [show (Z + h') ^ 2 - Z ^ 2 - h' ^ 2 = 2 * Z * h' by ring]
  refine ⟨mul_ne_zero (mul_ne_zero two_ne_zero hZ) h2, ?_⟩
  rw [weightedStep, if_neg (not_or.mpr ⟨h1', hsum⟩), Option.some.injEq,
    ← Point.nondegenerateAdd_eq_add hP0 hT0 hx]
  have hlam : T.x - (T.x * Z ^ 2 - h') / Z ^ 2 = h' / Z ^ 2 := by field_simp; ring
  have htwo : (2 : Fp) ≠ 0 := two_ne_zero
  simp only [Point.nondegenerateAdd, hPdef, Jac.affine, Point.mk.injEq, hlam, inv_div]
  constructor <;> (field_simp; ring)

/-- Completeness of `none`: `weightedStep` ⊥ ⇒ handed back (contrapositive of `jacStep_sound`) -/
theorem jacStep_none_of_weightedStep_none {p : Jac} {T : Point Fp} (hZ : p.Z ≠ 0)
    (hP : p.affine.OnCurve) (hT : T.OnCurve) (h : weightedStep p.affine T = none) :
    jacStep p T ((2 : ℕ) • T) = none :=
  Option.eq_none_iff_forall_ne_some.mpr fun _ hj =>
    Option.some_ne_none _ ((jacStep_sound hZ hP hT hj).2.symm.trans h)

end SinsemillaProofs
