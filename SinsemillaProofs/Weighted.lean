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
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD PALLAS_SCALAR_is_prime)

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

/-! ### Pallas group facts (odd prime order `q`)

- Transport: `ext_toSW_iff` with both sides' validity, push `toSW` through `+ − • 𝒪` by `simp`
  (`Point.toSW_*`, side goals from `Point.valid_*`), then the group law in `SWPoint` -/

theorem not_dvd_two_pow (k : ℕ) : ¬ PALLAS_SCALAR_CARD ∣ 2 ^ k := fun h =>
  absurd (Nat.le_of_dvd two_pos (PALLAS_SCALAR_is_prime.dvd_of_dvd_pow h))
    (by norm_num [PALLAS_SCALAR_CARD])

/-- `[2^k]` injective on valid points (`q ∤ 2^k`, so `[2^k](A − B) = 𝒪` forces `A = B`) -/
theorem two_pow_nsmul_inj {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) (k : ℕ) :
    (2 ^ k : ℕ) • A = (2 ^ k : ℕ) • B ↔ A = B := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul hA _) (Point.valid_nsmul hB _), Point.toSW_nsmul hA,
    Point.toSW_nsmul hB, Point.ext_toSW_iff hA hB]
  refine ⟨fun h => by_contra fun hne => not_dvd_two_pow k ?_, congrArg _⟩
  rw [← Point.addOrderOf_eq (sub_ne_zero.mpr hne), addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_sub, h,
    sub_self]

theorem two_pow_nsmul_onCurve {A : Point Fp} (hA : A.OnCurve) (k : ℕ) :
    ((2 ^ k : ℕ) • A).OnCurve :=
  Point.onCurve_of_valid_of_ne_zero (Point.valid_nsmul (.inl hA) _)
    ((Point.nsmul_eq_zero_iff hA _).not.mpr (not_dvd_two_pow k))

theorem nsmul_add_of_valid {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) (k : ℕ) :
    k • (A + B) = k • A + k • B := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul (Point.valid_add hA hB) k)
    (Point.valid_add (Point.valid_nsmul hA k) (Point.valid_nsmul hB k))]
  simp only [Point.toSW_nsmul, Point.toSW_add, Point.valid_add, Point.valid_nsmul, hA, hB,
    nsmul_add]

theorem nsmul_neg_of_valid {A : Point Fp} (hA : A.Valid) (k : ℕ) : k • (-A) = -(k • A) := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul (Point.valid_neg hA) k)
    (Point.valid_neg (Point.valid_nsmul hA k))]
  simp only [Point.toSW_nsmul, Point.toSW_neg, Point.valid_neg, Point.valid_nsmul, hA, neg_nsmul]

private theorem nsmul_zero_point (n : ℕ) : n • (0 : Point Fp) = 0 := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul Point.valid_zero n) Point.valid_zero]
  simp only [Point.toSW_nsmul, Point.toSW_zero, Point.valid_zero, nsmul_zero]

private theorem nsmul_nsmul_of_valid {A : Point Fp} (hA : A.Valid) (a b : ℕ) :
    a • (b • A) = (b * a) • A := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul (Point.valid_nsmul hA b) a) (Point.valid_nsmul hA _)]
  simp only [Point.toSW_nsmul, Point.valid_nsmul, hA, mul_nsmul]

theorem two_pow_nsmul_two_nsmul {A : Point Fp} (hA : A.Valid) (k : ℕ) :
    (2 ^ k : ℕ) • ((2 : ℕ) • A) = (2 ^ (k + 1) : ℕ) • A := by
  rw [nsmul_nsmul_of_valid hA, pow_succ']

private theorem add_eq_zero_iff_eq_neg_of_valid {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) :
    A + B = 0 ↔ A = -B := by
  rw [Point.ext_toSW_iff (Point.valid_add hA hB) Point.valid_zero,
    Point.ext_toSW_iff hA (Point.valid_neg hB)]
  simp only [Point.toSW_add, Point.toSW_neg, Point.toSW_zero, hA, hB, add_eq_zero_iff_eq_neg]

private theorem add_eq_left_iff_of_valid {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) :
    A + B = A ↔ B = 0 := by
  rw [Point.ext_toSW_iff (Point.valid_add hA hB) hA, Point.ext_toSW_iff hB Point.valid_zero]
  simp only [Point.toSW_add, Point.toSW_zero, hA, hB, add_eq_left]

private theorem add_add_self_of_valid {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) :
    A + B + A = (2 : ℕ) • A + B := by
  rw [Point.ext_toSW_iff (Point.valid_add (Point.valid_add hA hB) hA)
    (Point.valid_add (Point.valid_nsmul hA 2) hB)]
  simp only [Point.toSW_add, Point.toSW_nsmul, Point.valid_add, Point.valid_nsmul, hA, hB]
  abel

/-- Same `x` ↔ equal or opposite (`eq_or_eq_neg_of_x_eq` + `neg_x`) -/
theorem x_eq_iff_eq_or_eq_neg {P X : Point Fp} (hP : P.OnCurve) (hX : X.OnCurve) :
    P.x = X.x ↔ P = X ∨ P = -X :=
  ⟨Point.eq_or_eq_neg_of_x_eq hP hX, by rintro (rfl | rfl) <;> rfl⟩

/-! ### One position -/

/-- Theorem 5.4.4 as a computation: on-curve `step` = `[2]Acc + S m`, ⊥ exactly at `Acc = ±S m`
or `[2]Acc + S m = 𝒪` (`sumZero` ⊆ `Acc = −S m`, `doubleCollision` = third disjunct) -/
theorem step_eq_of_onCurve {S : ℕ → Point Fp} {m : ℕ} {Acc : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) :
    step S m Acc =
      if Acc = S m ∨ Acc = -S m ∨ (2 : ℕ) • Acc + S m = 0 then none
      else some ((2 : ℕ) • Acc + S m) := by
  have hAccV : Acc.Valid := .inl hAcc
  have hSV : (S m).Valid := .inl hS
  have hAcc0 := Point.ne_zero_of_onCurve hAcc
  have hS0 := Point.ne_zero_of_onCurve hS
  show (Acc ⸭ S m).bind (· ⸭ Acc) = _
  by_cases hx : Acc.x = (S m).x
  · -- collision: first `⸭` ⊥, `Acc = ±S m`
    rw [if_pos ((x_eq_iff_eq_or_eq_neg hAcc hS).mp hx |>.imp_right Or.inl)]
    simp only [Point.incompleteAdd_def, hx, or_true, if_true, Point.bot_eq_none, Option.bind_none]
  -- sumZero ⊆ collision: `Acc + S m = 𝒪` ⇒ `S m = −Acc`, same `x`
  have hT0 : Acc + S m ≠ 0 := fun h =>
    hx (by rw [(add_eq_zero_iff_eq_neg_of_valid hAccV hSV).mp h, Point.neg_x])
  have hT := Point.onCurve_of_valid_of_ne_zero (Point.valid_add hAccV hSV) hT0
  have hsum := add_add_self_of_valid hAccV hSV
  -- doubleCollision: `(Acc + S m).x = Acc.x` ⇔ `Acc + S m = −Acc` (`= Acc` ⇒ `S m = 𝒪`, excluded)
  have hx2 : (Acc + S m).x = Acc.x ↔ (2 : ℕ) • Acc + S m = 0 := by
    rw [x_eq_iff_eq_or_eq_neg hT hAcc, add_eq_left_iff_of_valid hAccV hSV, or_iff_right hS0,
      ← add_eq_zero_iff_eq_neg_of_valid (Point.valid_add hAccV hSV) hAccV, hsum]
  have hne := not_or.mp ((x_eq_iff_eq_or_eq_neg hAcc hS).not.mp hx)
  simp only [Point.incompleteAdd_def, hAcc0, hS0, hx, hT0, hx2, hne, or_false, false_or, if_false,
    Point.bot_eq_none, Option.bind_some, hsum]

theorem step_onCurve {S : ℕ → Point Fp} {m : ℕ} {Acc B : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) (h : step S m Acc = some B) : B.OnCurve := by
  rw [step_eq_of_onCurve hAcc hS, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨hc, rfl⟩ := h
  exact Point.onCurve_of_valid_of_ne_zero
    (Point.valid_add (Point.valid_nsmul (.inl hAcc) 2) (.inl hS)) fun h0 => hc (.inr (.inr h0))

/-- x test resolved: `weightedStep` on-curve ⊥ exactly at `P = ±[2]T` or `P + T = 𝒪` -/
theorem weightedStep_eq_of_onCurve {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    weightedStep P T =
      if P = (2 : ℕ) • T ∨ P = -((2 : ℕ) • T) ∨ P + T = 0 then none else some (P + T) := by
  have h2T : ((2 : ℕ) • T).OnCurve := by simpa using two_pow_nsmul_onCurve hT 1
  simp only [weightedStep, x_eq_iff_eq_or_eq_neg hP h2T, or_assoc]

/-- **Per-position theorem**: one weighted step at weight `k` = the spec step, rescaled by `[2^k]`
(⊥ ↔ ⊥, by `two_pow_nsmul_inj`) -/
theorem weightedStep_eq_step {S : ℕ → Point Fp} {m : ℕ} {Acc : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) (k : ℕ) :
    weightedStep ((2 ^ (k + 1) : ℕ) • Acc) ((2 ^ k : ℕ) • S m) =
      (step S m Acc).map ((2 ^ k : ℕ) • ·) := by
  have hAccV : Acc.Valid := .inl hAcc
  have hSV : (S m).Valid := .inl hS
  have hsum :
      (2 ^ (k + 1) : ℕ) • Acc + (2 ^ k : ℕ) • S m = (2 ^ k : ℕ) • ((2 : ℕ) • Acc + S m) := by
    rw [nsmul_add_of_valid (Point.valid_nsmul hAccV 2) hSV, two_pow_nsmul_two_nsmul hAccV]
  have hz := two_pow_nsmul_inj (Point.valid_add (Point.valid_nsmul hAccV 2) hSV) Point.valid_zero k
  rw [nsmul_zero_point] at hz
  rw [weightedStep_eq_of_onCurve (two_pow_nsmul_onCurve hAcc (k + 1)) (two_pow_nsmul_onCurve hS k),
    step_eq_of_onCurve hAcc hS, nsmul_nsmul_of_valid hSV, ← pow_succ, ← nsmul_neg_of_valid hSV,
    hsum]
  simp only [two_pow_nsmul_inj hAccV hSV, two_pow_nsmul_inj hAccV (Point.valid_neg hSV), hz]
  split_ifs <;> rfl

/-! ### The chain -/

/-- Invariant `P = [2^|ms|] Acc` carried down the chain (induction on `ms` generalizing `Acc`,
`weightedStep_eq_step` + `step_onCurve`) -/
theorem weightedFrom_eq_hashToPoint {S : ℕ → Point Fp} {Acc : Point Fp} {ms : List ℕ}
    (hAcc : Acc.OnCurve) (hS : ∀ m ∈ ms, (S m).OnCurve) :
    weightedFrom S ((2 ^ ms.length : ℕ) • Acc) ms = hashToPoint S Acc ms := by
  induction ms generalizing Acc with
  | nil => rfl
  | cons m ms ih =>
    rw [hashToPoint_cons, weightedFrom, List.length_cons,
      weightedStep_eq_step hAcc (hS m List.mem_cons_self) ms.length]
    cases h : step S m Acc with
    | none => rfl
    | some B =>
      exact ih (step_onCurve hAcc (hS m List.mem_cons_self) h)
        fun m' hm' => hS m' (List.mem_cons_of_mem m hm')

/-- **Main theorem**: the weighted evaluator is the specification's function, ⊥ included

- Hypotheses necessary, not convenient: spec ⊥ at once for `Q = 𝒪` (`accZero`) / `S m = 𝒪`
  (`genZero`), weighted `[2^n]𝒪 = 𝒪`, `P + 𝒪 = P` (no ⊥); known domains have `Q ≠ 𝒪`, group
  hashing never gives `𝒪`
- No bound on `words.length` or on words (`S` total, `q ∤ 2^k`); Rust asserts both -/
theorem weightedHashToPoint_eq_hashToPoint {S : ℕ → Point Fp} {Q : Point Fp}
    {words : List ℕ} (hQ : Q.OnCurve) (hS : ∀ m ∈ words, (S m).OnCurve) :
    weightedHashToPoint S Q words = hashToPoint S Q words :=
  weightedFrom_eq_hashToPoint hQ hS

/-- `FIRST_STEPS[m]` row (`first_steps` in `table.rs`): position 0 alone, per `(Q, n)`

- Entry `None` ↔ `start_x == doubled.x || sum.is_identity()` = `weightedStep` ⊥
- = spec's first step rescaled by `[2^(n−1)]`: `weightedStep_eq_step` at `k = ms.length` -/
theorem weightedHashToPoint_cons (S : ℕ → Point Fp) (Q : Point Fp) (m : ℕ) (ms : List ℕ) :
    weightedHashToPoint S Q (m :: ms) =
      (weightedStep ((2 ^ (ms.length + 1) : ℕ) • Q) ((2 ^ ms.length : ℕ) • S m)).bind
        (weightedFrom S · ms) :=
  rfl

end SinsemillaProofs
