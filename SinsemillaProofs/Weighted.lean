import Zcash.Circuits.Specs.SinsemillaBreak

/-!
# Position-weighted Sinsemilla = the specification's `hashToPoint`, ⊥ included

- Models `TableDomain::hash_to_point` (`table.rs`) at the group level: `generators[w][j]`
  abstracted as `[2^w] S j`, `starts[d][n−1]` as `[2^n] Q`
- `Pᵢ = [2^(n−i)] Accᵢ` (spec accumulators never formed), one addition per word
- ⊥ = Theorem 5.4.4's conditions rescaled by `[2^(n−i)]`: `Acc = ±S` ↦ `P = ±[2]T` (one x test,
  `has_x_of`), `[2]Acc + S = 𝒪` ↦ `P + T = 𝒪` (`acc.is_identity()`)
- Rust: sticky `exceptional` flag, sum keeps going; here `Option.bind` (equal as functions)
- Out of scope: table contents, word packing / `< 2^K` assert, Rust ↔ this model (tests pin both)
-/

namespace SinsemillaProofs

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- One weighted position (loop body of `hash_to_point`): `P + T`, ⊥ where `P.x = ([2]T).x`
(`P = ±[2]T` on-curve) or `P + T = 𝒪`

- `P = 𝒪` unreachable (previous position already ⊥); Rust `has_x_of(𝒪, _)` = true there -/
def weightedStep (P T : Point Fp) : Option (Point Fp) :=
  if P.x = ((2 : ℕ) • T).x ∨ P + T = 0 then none else some (P + T)

/-- Weighted chain from `P`: position with `ms` remaining adds `T = [2^|ms|] S m`
(`generators[n−1−i][m]`), tests `[2]T` (`generators[n−i][m]`) -/
def weightedFrom (S : ℕ → Point Fp) : Point Fp → List ℕ → Option (Point Fp)
  | P, [] => some P
  | P, m :: ms => (weightedStep P ((2 ^ ms.length : ℕ) • S m)).bind (weightedFrom S · ms)

/-- Position-weighted `SinsemillaHashToPoint`: start `[2ⁿ]Q` (`starts[d][n−1]`), one addition per
word -/
def weightedHashToPoint (S : ℕ → Point Fp) (Q : Point Fp) (words : List ℕ) :
    Option (Point Fp) :=
  weightedFrom S ((2 ^ words.length : ℕ) • Q) words

/-! ### Pallas group facts (odd prime order `q`, via `Point.toSW`) -/

theorem not_dvd_two_pow (k : ℕ) : ¬ PALLAS_SCALAR_CARD ∣ 2 ^ k := by
  sorry

/-- `[2^k]` injective on valid points -/
theorem two_pow_nsmul_inj {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) (k : ℕ) :
    (2 ^ k : ℕ) • A = (2 ^ k : ℕ) • B ↔ A = B := by
  sorry

theorem two_pow_nsmul_onCurve {A : Point Fp} (hA : A.OnCurve) (k : ℕ) :
    ((2 ^ k : ℕ) • A).OnCurve := by
  sorry

theorem nsmul_add_of_valid {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) (k : ℕ) :
    k • (A + B) = k • A + k • B := by
  sorry

theorem nsmul_neg_of_valid {A : Point Fp} (hA : A.Valid) (k : ℕ) : k • (-A) = -(k • A) := by
  sorry

theorem two_pow_nsmul_two_nsmul {A : Point Fp} (hA : A.Valid) (k : ℕ) :
    (2 ^ k : ℕ) • ((2 : ℕ) • A) = (2 ^ (k + 1) : ℕ) • A := by
  sorry

/-- Same `x` ↔ equal or opposite (`eq_or_eq_neg_of_x_eq` + `neg_x`) -/
theorem x_eq_iff_eq_or_eq_neg {P X : Point Fp} (hP : P.OnCurve) (hX : X.OnCurve) :
    P.x = X.x ↔ P = X ∨ P = -X := by
  sorry

/-! ### One position -/

/-- Theorem 5.4.4 as a computation: on-curve `step` = `[2]Acc + S m`, ⊥ exactly at `Acc = ±S m`
or `[2]Acc + S m = 𝒪` (`sumZero` ⊆ `Acc = −S m`, `doubleCollision` = third disjunct) -/
theorem step_eq_of_onCurve {S : ℕ → Point Fp} {m : ℕ} {Acc : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) :
    step S m Acc =
      if Acc = S m ∨ Acc = -S m ∨ (2 : ℕ) • Acc + S m = 0 then none
      else some ((2 : ℕ) • Acc + S m) := by
  sorry

theorem step_onCurve {S : ℕ → Point Fp} {m : ℕ} {Acc B : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) (h : step S m Acc = some B) : B.OnCurve := by
  sorry

/-- x test resolved: `weightedStep` on-curve ⊥ exactly at `P = ±[2]T` or `P + T = 𝒪` -/
theorem weightedStep_eq_of_onCurve {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    weightedStep P T =
      if P = (2 : ℕ) • T ∨ P = -((2 : ℕ) • T) ∨ P + T = 0 then none else some (P + T) := by
  sorry

/-- **Per-position theorem**: one weighted step at weight `k` = the spec step, rescaled by `[2^k]`
(⊥ ↔ ⊥, by `two_pow_nsmul_inj`) -/
theorem weightedStep_eq_step {S : ℕ → Point Fp} {m : ℕ} {Acc : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) (k : ℕ) :
    weightedStep ((2 ^ (k + 1) : ℕ) • Acc) ((2 ^ k : ℕ) • S m) =
      (step S m Acc).map ((2 ^ k : ℕ) • ·) := by
  sorry

/-! ### The chain -/

/-- Invariant `P = [2^|ms|] Acc` carried down the chain (induction on `ms` generalizing `Acc`,
`weightedStep_eq_step` + `step_onCurve`) -/
theorem weightedFrom_eq_hashToPoint {S : ℕ → Point Fp} {Acc : Point Fp} {ms : List ℕ}
    (hAcc : Acc.OnCurve) (hS : ∀ m ∈ ms, (S m).OnCurve) :
    weightedFrom S ((2 ^ ms.length : ℕ) • Acc) ms = hashToPoint S Acc ms := by
  sorry

/-- **Main theorem**: the weighted evaluator is the specification's function, ⊥ included

- Hypotheses necessary, not convenient: spec ⊥ at once for `Q = 𝒪` (`accZero`) / `S m = 𝒪`
  (`genZero`), weighted `[2^n]𝒪 = 𝒪`, `P + 𝒪 = P` (no ⊥); known domains have `Q ≠ 𝒪`, group
  hashing never gives `𝒪`
- No bound on `words.length` or on words (`S` total, `q ∤ 2^k`); Rust asserts both -/
theorem weightedHashToPoint_eq_hashToPoint {S : ℕ → Point Fp} {Q : Point Fp}
    {words : List ℕ} (hQ : Q.OnCurve) (hS : ∀ m ∈ words, (S m).OnCurve) :
    weightedHashToPoint S Q words = hashToPoint S Q words := by
  sorry

/-- `FIRST_STEPS[m]` row (`first_steps` in `table.rs`): position 0 alone, per `(Q, n)`

- Entry `None` ↔ `start_x == doubled.x || sum.is_identity()` = `weightedStep` ⊥
- = spec's first step rescaled by `[2^(n−1)]`: `weightedStep_eq_step` at `k = ms.length` -/
theorem weightedHashToPoint_cons (S : ℕ → Point Fp) (Q : Point Fp) (m : ℕ) (ms : List ℕ) :
    weightedHashToPoint S Q (m :: ms) =
      (weightedStep ((2 ^ (ms.length + 1) : ℕ) • Q) ((2 ^ ms.length : ℕ) • S m)).bind
        (weightedFrom S · ms) := by
  sorry

end SinsemillaProofs
