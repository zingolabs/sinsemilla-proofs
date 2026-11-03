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
  sorry

/-- Soundness: a returned step agrees with `weightedStep`, and keeps `Z ≠ 0` (`Z₃ = 2·Z·h`) -/
theorem jacStep_sound {p p' : Jac} {T : Point Fp} (hZ : p.Z ≠ 0) (hP : p.affine.OnCurve)
    (hT : T.OnCurve) (h : jacStep p T ((2 : ℕ) • T) = some p') :
    p'.Z ≠ 0 ∧ weightedStep p.affine T = some p'.affine := by
  sorry

/-- Completeness of `none`: `weightedStep` ⊥ ⇒ handed back (contrapositive of `jacStep_sound`) -/
theorem jacStep_none_of_weightedStep_none {p : Jac} {T : Point Fp} (hZ : p.Z ≠ 0)
    (hP : p.affine.OnCurve) (hT : T.OnCurve) (h : weightedStep p.affine T = none) :
    jacStep p T ((2 : ℕ) • T) = none := by
  sorry

end SinsemillaProofs
