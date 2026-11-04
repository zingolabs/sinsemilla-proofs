import SinsemillaProofs.Weighted
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Jacobian accumulator step

References:
- `sinsemilla` crate at `elicbarbieri/sinsemilla` commit `6899b8643e48a935b276359434358d9b1ee1989a`
  (branch `perf/hash-many-vartime`), file `src/table.rs` (`Jacobian::step`,
  `TableDomain::hash_each_vartime`)
- Bernstein and Lange, Explicit-Formulas Database, `madd-2007-bl` (Jacobian mixed addition)

Below `LOCKSTEP_LANES` messages, `TableDomain::hash_each_vartime` keeps one Jacobian accumulator
per message and normalises all of them with one shared inversion at the end. `Jacobian::step` adds
one affine table entry by `madd-2007-bl` after two tests on the raw coordinates: the `has_x_of`
test `X = doubled.x · Z²`, which is the rescaled `±` conditions, and `h = 0`, i.e.
`X = addend.x · Z²`. `jacobianStep` is that function on `(X, Y, Z)` for the affine
`(X / Z², Y / Z³)`.

The step is sound, and complete for `⊥`, but its `none` is strictly larger than `⊥`: `h = 0` also
fires when the affine view *equals* the addend, which the specification treats as an ordinary
doubling. The Rust does not distinguish the two cases; on any `none` it reruns the whole message
through `TableDomain::hash_to_point`, which is `weightedHashToPoint` and so, by
`weightedHashToPoint_eq_hashToPoint`, the specification. A `FIRST_STEPS` entry of `None` makes the
accumulator `None` and takes the same fallback. The soundness theorems therefore carry `Z ≠ 0` as
an invariant and state the affine view against `weightedStep`, and `jacobianStep_eq_none_iff` says
exactly which steps are handed back.
-/

namespace SinsemillaProofs

open Zcash.Circuits

/-- A Pallas point in Jacobian coordinates, `(X, Y, Z)` for the affine `(X / Z², Y / Z³)`. The Rust
never holds the identity in this form; the theorems carry `Z ≠ 0` as a hypothesis rather than
bundling it into the type. -/
structure JacobianPoint where
  X : Fp
  Y : Fp
  Z : Fp

/-- The affine view `(X / Z², Y / Z³)`. -/
def JacobianPoint.affine (p : JacobianPoint) : Point Fp := ⟨p.X / p.Z ^ 2, p.Y / p.Z ^ 3⟩

/-- `Jacobian::step`: the `has_x_of`-style test `X = doubled.x · Z²`, then `h = 0`
(`X = addend.x · Z²`), then `madd-2007-bl` with `Z₃ = 2·Z·h`. -/
def jacobianStep (p : JacobianPoint) (addend doubled : Point Fp) : Option JacobianPoint :=
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

/-- Exactly which steps are handed back: those with `x(P) = x([2]T)`, which is `⊥`, or with
`x(P) = x(T)`, which is `⊥` at `P = −T` and a doubling at `P = T`. -/
theorem jacobianStep_eq_none_iff {p : JacobianPoint} {T : Point Fp} (hZ : p.Z ≠ 0) :
    jacobianStep p T ((2 : ℕ) • T) = none ↔
      p.affine.x = ((2 : ℕ) • T).x ∨ p.affine.x = T.x := by
  simp only [jacobianStep, JacobianPoint.affine, div_eq_iff (pow_ne_zero 2 hZ),
    sub_eq_zero.trans eq_comm]
  split_ifs <;> simp [*]

/-- Both soundness facts at once, since they come from the same reparametrisation of `X` by
`h = T.x·Z² − X` (every `madd-2007-bl` denominator is a power of `2·Z·h`); the exported statements
are the projections `jacobianStep_Z_ne_zero` and `affine_jacobianStep`. -/
private theorem jacobianStep_sound {p p' : JacobianPoint} {T : Point Fp} (hZ : p.Z ≠ 0)
    (hP : p.affine.OnCurve) (hT : T.OnCurve) (h : jacobianStep p T ((2 : ℕ) • T) = some p') :
    p'.Z ≠ 0 ∧ weightedStep p.affine T = some p'.affine := by
  obtain ⟨X, Y, Z⟩ := p
  -- reparametrise `X` by `h = T.x·Z² − X` (every madd-2007-bl denominator = power of `2·Z·h`)
  obtain ⟨h', rfl⟩ : ∃ h', X = T.x * Z ^ 2 - h' := ⟨T.x * Z ^ 2 - X, by ring⟩
  simp only [jacobianStep, sub_sub_cancel] at h
  split_ifs at h with h1 h2
  obtain rfl := Option.some.inj h
  have hzz : Z ^ 2 ≠ 0 := pow_ne_zero 2 hZ
  set P := JacobianPoint.affine ⟨T.x * Z ^ 2 - h', Y, Z⟩ with hPdef
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
  simp only [Point.nondegenerateAdd, hPdef, JacobianPoint.affine, Point.mk.injEq, hlam, inv_div]
  constructor <;> (field_simp; ring)

/-- **Soundness, the invariant**: a returned step keeps `Z ≠ 0`, so the shared inversion in
`hash_each_vartime` is over non-zero `Z`s. -/
theorem jacobianStep_Z_ne_zero {p p' : JacobianPoint} {T : Point Fp} (hZ : p.Z ≠ 0)
    (hP : p.affine.OnCurve) (hT : T.OnCurve) (h : jacobianStep p T ((2 : ℕ) • T) = some p') :
    p'.Z ≠ 0 :=
  (jacobianStep_sound hZ hP hT h).1

/-- **Soundness, the value**: a returned step is `weightedStep` on the affine view. -/
theorem affine_jacobianStep {p p' : JacobianPoint} {T : Point Fp} (hZ : p.Z ≠ 0)
    (hP : p.affine.OnCurve) (hT : T.OnCurve) (h : jacobianStep p T ((2 : ℕ) • T) = some p') :
    weightedStep p.affine T = some p'.affine :=
  (jacobianStep_sound hZ hP hT h).2

/-- **Completeness for `⊥`**: where `weightedStep` is `⊥`, the step is handed back, so no `⊥` is
ever hashed silently (the contrapositive of `affine_jacobianStep`). -/
theorem jacobianStep_none_of_weightedStep_none {p : JacobianPoint} {T : Point Fp} (hZ : p.Z ≠ 0)
    (hP : p.affine.OnCurve) (hT : T.OnCurve) (h : weightedStep p.affine T = none) :
    jacobianStep p T ((2 : ℕ) • T) = none :=
  Option.eq_none_iff_forall_ne_some.mpr fun _ hj =>
    Option.some_ne_none _ ((affine_jacobianStep hZ hP hT hj).symm.trans h)

end SinsemillaProofs
