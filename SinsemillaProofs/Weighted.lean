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
  intro h
  have h2 := Nat.le_of_dvd two_pos
    (CompElliptic.Fields.Pasta.PALLAS_SCALAR_is_prime.dvd_of_dvd_pow h)
  norm_num [PALLAS_SCALAR_CARD] at h2

/-- `[2^k]` injective on valid points -/
theorem two_pow_nsmul_inj {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) (k : ℕ) :
    (2 ^ k : ℕ) • A = (2 ^ k : ℕ) • B ↔ A = B := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul hA _) (Point.valid_nsmul hB _), Point.toSW_nsmul hA,
    Point.toSW_nsmul hB, Point.ext_toSW_iff hA hB]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  by_contra hne
  have h0 : (2 ^ k) • (A.toSW hA - B.toSW hB) = 0 := by rw [nsmul_sub, h, sub_self]
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, Point.addOrderOf_eq (sub_ne_zero.mpr hne)] at h0
  exact not_dvd_two_pow k h0

theorem two_pow_nsmul_onCurve {A : Point Fp} (hA : A.OnCurve) (k : ℕ) :
    ((2 ^ k : ℕ) • A).OnCurve := by
  refine Point.onCurve_of_valid_of_ne_zero (Point.valid_nsmul (.inl hA) _) ?_
  rw [Ne, Point.nsmul_eq_zero_iff hA]
  exact not_dvd_two_pow k

theorem nsmul_add_of_valid {A B : Point Fp} (hA : A.Valid) (hB : B.Valid) (k : ℕ) :
    k • (A + B) = k • A + k • B := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul (Point.valid_add hA hB) k)
      (Point.valid_add (Point.valid_nsmul hA k) (Point.valid_nsmul hB k)),
    Point.toSW_nsmul (Point.valid_add hA hB) k, Point.toSW_add hA hB,
    Point.toSW_add (Point.valid_nsmul hA k) (Point.valid_nsmul hB k), Point.toSW_nsmul hA,
    Point.toSW_nsmul hB, nsmul_add]

theorem nsmul_neg_of_valid {A : Point Fp} (hA : A.Valid) (k : ℕ) : k • (-A) = -(k • A) := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul (Point.valid_neg hA) k)
      (Point.valid_neg (Point.valid_nsmul hA k)),
    Point.toSW_nsmul (Point.valid_neg hA) k, Point.toSW_neg hA,
    Point.toSW_neg (Point.valid_nsmul hA k), Point.toSW_nsmul hA, neg_nsmul]

private theorem nsmul_zero_point (n : ℕ) : n • (0 : Point Fp) = 0 := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul Point.valid_zero n) Point.valid_zero,
    Point.toSW_nsmul Point.valid_zero n, Point.toSW_zero, nsmul_zero]

private theorem nsmul_nsmul_of_valid {A : Point Fp} (hA : A.Valid) (a b : ℕ) :
    a • (b • A) = (b * a) • A := by
  rw [Point.ext_toSW_iff (Point.valid_nsmul (Point.valid_nsmul hA b) a) (Point.valid_nsmul hA _),
    Point.toSW_nsmul (Point.valid_nsmul hA b) a, Point.toSW_nsmul hA b, Point.toSW_nsmul hA,
    mul_nsmul]

theorem two_pow_nsmul_two_nsmul {A : Point Fp} (hA : A.Valid) (k : ℕ) :
    (2 ^ k : ℕ) • ((2 : ℕ) • A) = (2 ^ (k + 1) : ℕ) • A := by
  rw [nsmul_nsmul_of_valid hA, pow_succ']

/-- Same `x` ↔ equal or opposite (`eq_or_eq_neg_of_x_eq` + `neg_x`) -/
theorem x_eq_iff_eq_or_eq_neg {P X : Point Fp} (hP : P.OnCurve) (hX : X.OnCurve) :
    P.x = X.x ↔ P = X ∨ P = -X := by
  refine ⟨Point.eq_or_eq_neg_of_x_eq hP hX, ?_⟩
  rintro (rfl | rfl)
  · rfl
  · exact (Point.neg_x X).symm

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
  · rw [if_pos ((x_eq_iff_eq_or_eq_neg hAcc hS).mp hx |>.imp_right Or.inl)]
    simp only [Point.incompleteAdd_def, hx, or_true, if_true, Point.bot_eq_none, Option.bind_none]
  have hTV : (Acc + S m).Valid := Point.valid_add hAccV hSV
  have hswT := Point.toSW_add hAccV hSV
  have hT0 : Acc + S m ≠ 0 := by
    intro h
    rw [Point.ext_toSW_iff hTV Point.valid_zero, hswT, Point.toSW_zero] at h
    have hneg : S m = -Acc := by
      rw [Point.ext_toSW_iff hSV (Point.valid_neg hAccV), Point.toSW_neg hAccV]
      exact eq_neg_of_add_eq_zero_right h
    exact hx (by rw [hneg, Point.neg_x])
  have hT : (Acc + S m).OnCurve := Point.onCurve_of_valid_of_ne_zero hTV hT0
  have h2V : ((2 : ℕ) • Acc + S m).Valid := Point.valid_add (Point.valid_nsmul hAccV 2) hSV
  have hsw2 : ((2 : ℕ) • Acc + S m).toSW h2V = (2 : ℕ) • Acc.toSW hAccV + (S m).toSW hSV := by
    rw [Point.toSW_add (Point.valid_nsmul hAccV 2) hSV, Point.toSW_nsmul hAccV]
  have hS0' : (S m).toSW hSV ≠ 0 := by
    rw [Ne, ← Point.toSW_zero, ← Point.ext_toSW_iff hSV Point.valid_zero]
    exact hS0
  have hsum : Acc + S m + Acc = (2 : ℕ) • Acc + S m := by
    rw [Point.ext_toSW_iff (Point.valid_add hTV hAccV) h2V, Point.toSW_add hTV hAccV, hswT, hsw2,
      two_nsmul]
    abel
  have hx2 : (Acc + S m).x = Acc.x ↔ (2 : ℕ) • Acc + S m = 0 := by
    rw [x_eq_iff_eq_or_eq_neg hT hAcc, Point.ext_toSW_iff hTV hAccV,
      Point.ext_toSW_iff hTV (Point.valid_neg hAccV), Point.ext_toSW_iff h2V Point.valid_zero,
      hswT, Point.toSW_neg hAccV, hsw2, Point.toSW_zero, add_eq_left, or_iff_right hS0',
      eq_neg_iff_add_eq_zero, two_nsmul, add_right_comm]
  have hne : ¬ (Acc = S m ∨ Acc = -S m) := fun h => hx ((x_eq_iff_eq_or_eq_neg hAcc hS).mpr h)
  rw [not_or] at hne
  simp only [Point.incompleteAdd_def, hAcc0, hS0, hx, hT0, hx2, hne, or_false, false_or, if_false,
    Point.bot_eq_none, Option.bind_some, hsum]

theorem step_onCurve {S : ℕ → Point Fp} {m : ℕ} {Acc B : Point Fp} (hAcc : Acc.OnCurve)
    (hS : (S m).OnCurve) (h : step S m Acc = some B) : B.OnCurve := by
  rw [step_eq_of_onCurve hAcc hS] at h
  split_ifs at h with hc
  cases h
  exact Point.onCurve_of_valid_of_ne_zero
    (Point.valid_add (Point.valid_nsmul (.inl hAcc) 2) (.inl hS)) (fun h0 => hc (.inr (.inr h0)))

/-- x test resolved: `weightedStep` on-curve ⊥ exactly at `P = ±[2]T` or `P + T = 𝒪` -/
theorem weightedStep_eq_of_onCurve {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    weightedStep P T =
      if P = (2 : ℕ) • T ∨ P = -((2 : ℕ) • T) ∨ P + T = 0 then none else some (P + T) := by
  have h2T := two_pow_nsmul_onCurve hT 1
  rw [pow_one] at h2T
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
  have hz : (2 ^ k : ℕ) • ((2 : ℕ) • Acc + S m) = 0 ↔ (2 : ℕ) • Acc + S m = 0 := by
    conv_lhs => rw [← nsmul_zero_point (2 ^ k)]
    exact two_pow_nsmul_inj (Point.valid_add (Point.valid_nsmul hAccV 2) hSV) Point.valid_zero k
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
  | nil =>
    rw [weightedFrom, hashToPoint_nil, List.length_nil, pow_zero]
    rfl
  | cons m ms ih =>
    rw [hashToPoint_cons, weightedFrom, List.length_cons,
      weightedStep_eq_step hAcc (hS m List.mem_cons_self) ms.length]
    cases h : step S m Acc with
    | none => rfl
    | some B =>
      exact ih (step_onCurve hAcc (hS m List.mem_cons_self) h)
        (fun m' hm' => hS m' (List.mem_cons_of_mem m hm'))

/-- **Main theorem**: the weighted evaluator is the specification's function, ⊥ included

- Hypotheses necessary, not convenient: spec ⊥ at once for `Q = 𝒪` (`accZero`) / `S m = 𝒪`
  (`genZero`), weighted `[2^n]𝒪 = 𝒪`, `P + 𝒪 = P` (no ⊥); known domains have `Q ≠ 𝒪`, group
  hashing never gives `𝒪`
- No bound on `words.length` or on words (`S` total, `q ∤ 2^k`); Rust asserts both -/
theorem weightedHashToPoint_eq_hashToPoint {S : ℕ → Point Fp} {Q : Point Fp}
    {words : List ℕ} (hQ : Q.OnCurve) (hS : ∀ m ∈ words, (S m).OnCurve) :
    weightedHashToPoint S Q words = hashToPoint S Q words := by
  exact weightedFrom_eq_hashToPoint hQ hS

/-- `FIRST_STEPS[m]` row (`first_steps` in `table.rs`): position 0 alone, per `(Q, n)`

- Entry `None` ↔ `start_x == doubled.x || sum.is_identity()` = `weightedStep` ⊥
- = spec's first step rescaled by `[2^(n−1)]`: `weightedStep_eq_step` at `k = ms.length` -/
theorem weightedHashToPoint_cons (S : ℕ → Point Fp) (Q : Point Fp) (m : ℕ) (ms : List ℕ) :
    weightedHashToPoint S Q (m :: ms) =
      (weightedStep ((2 ^ (ms.length + 1) : ℕ) • Q) ((2 ^ ms.length : ℕ) • S m)).bind
        (weightedFrom S · ms) := by
  rfl

end SinsemillaProofs
