import Zcash.Circuits.Specs.SinsemillaBreak
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Position-weighted Sinsemilla as the specification's `hashToPoint`

References:
- Zcash protocol specification §5.4.1.9 (`SinsemillaHashToPoint`) and Theorem 5.4.4 (when the
  incomplete additions along the hash chain are defined)
- `sinsemilla` crate at `elicbarbieri/sinsemilla` commit `6899b8643e48a935b276359434358d9b1ee1989a`
  (branch `perf/hash-many-vartime`: zcash/sinsemilla#9 head `596e662` plus four commits), file
  `src/table.rs` (`TableDomain::hash_to_point`, `FIRST_STEPS`)
- Ironwood at `86e3c7026db8c9af27ca731e6b5c7f2d8fc7f0fc`, modules `Zcash.Circuits.Specs.Sinsemilla`
  (`hashToPoint`, `step`) and `Zcash.Circuits.Specs.SinsemillaBreak` (`hashToPointB`)

The table evaluator never forms the specification's accumulators `Accᵢ`. For an `n`-chunk message
it keeps the position-weighted prefix `Pᵢ = [2^(n−i)] Accᵢ`, starting from `P₀ = [2ⁿ] Q`
(`starts[d][n−1]`) and adding one table entry `Tᵢ = [2^(n−1−i)] S(mᵢ)` (`generators[n−1−i][mᵢ]`)
per chunk, so the doubling inside each specification step is absorbed into the weights and every
position costs one addition. This module models that at the group level: the table rows are the
multiples `[2^w] S m` of an arbitrary generator map `S : ℕ → Point Fp`, and the start table is
`[2ⁿ] Q`. The Rust calls the chunks "words"; the specification's word is used here.

The exceptional cases are the specification's, rescaled. Theorem 5.4.4 makes the step `⊥` exactly
when `Acc = ±S(m)` or `[2]Acc + S(m) = 𝒪`. Multiplying through by `[2^(n−i)]` turns the first pair
into `P = ±[2]T`, a single `x`-coordinate test against the entry one weight up (`has_x_of` against
`generators[n−i][m]`), and the third into `P + T = 𝒪` (`acc.is_identity()`). The Rust keeps a
sticky `exceptional` flag and lets the sum run on; `Option.bind` stops at the first `⊥`. The two
agree as functions, which is all the theorems claim.

`weightedStep` is stated in the specification's literal `⊥`-model (`Option`, `none` for `⊥`) and
not as a Σ-refinement of the kind `hashToPointB` is. The exported results are equalities of
`Option`-valued functions against `hashToPoint`, which is the form Ironwood requires of exported
statements, and break data stays `hashToPointB`'s job; the corollary
`weightedHashToPoint_eq_getLeft?_hashToPointB` records the join with that refinement.

Out of scope, by design: the contents of the tables (that `generators[w][j]` is `[2^w] S(j)` and
`starts[d][n−1]` is `[2ⁿ] Q` is tested in the crate against group hashing, not proved here), the
packing of message bits into chunks and the `< 2^K` assertion on each, and the correspondence
between the Rust and this model, which the crate's differential tests pin from both sides.
-/

namespace SinsemillaProofs

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD PALLAS_SCALAR_is_prime)

/-- One weighted position, the loop body of `TableDomain::hash_to_point`: `P + T`, or `⊥` when
`P.x = ([2]T).x` (on-curve, `P = ±[2]T`) or `P + T = 𝒪`. The identity never reaches this test as
`P`, since the previous position was already `⊥`. -/
def weightedStep (P T : Point Fp) : Option (Point Fp) :=
  if P.x = ((2 : ℕ) • T).x ∨ P + T = 0 then none else some (P + T)

/-- The weighted chain from `P` with the chunks `ms` still to hash: the position with `ms` remaining
adds `T = [2^|ms|] S m` (`generators[n−1−i][m]`) and tests against `[2]T` (`generators[n−i][m]`). -/
def weightedFrom (S : ℕ → Point Fp) : Point Fp → List ℕ → Option (Point Fp)
  | P, [] => some P
  | P, m :: ms =>
    (weightedStep P ((2 ^ ms.length : ℕ) • S m)).bind fun acc => weightedFrom S acc ms

/-- Position-weighted `SinsemillaHashToPoint`: start at `[2ⁿ] Q` (`starts[d][n−1]`) and add one
weighted generator per chunk. -/
def weightedHashToPoint (S : ℕ → Point Fp) (Q : Point Fp) (chunks : List ℕ) :
    Option (Point Fp) :=
  weightedFrom S ((2 ^ chunks.length : ℕ) • Q) chunks

/-! ## Pallas group facts

The group has odd prime order `q`, so `[2^k]` is injective and never lands on the identity. Every
transport to `SWPoint` below is the same three moves: `Point.ext_toSW_iff` with both sides'
validity, `toSW` pushed through `+`, `−`, `•` and `𝒪` by `simp only [Point.toSW_*]`, then the
group law in `SWPoint`. -/

theorem not_dvd_two_pow (k : ℕ) : ¬ PALLAS_SCALAR_CARD ∣ 2 ^ k := fun h =>
  absurd (Nat.le_of_dvd two_pos (PALLAS_SCALAR_is_prime.dvd_of_dvd_pow h))
    (by norm_num [PALLAS_SCALAR_CARD])

/-- `[2^k]` is injective on valid points: `q ∤ 2^k`, so `[2^k](A − B) = 𝒪` forces `A = B`. -/
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

/-- Equal `x`-coordinates on-curve means equal or opposite points: `eq_or_eq_neg_of_x_eq`, with
`neg_x` for the converse. -/
theorem x_eq_iff_eq_or_eq_neg {P X : Point Fp} (hP : P.OnCurve) (hX : X.OnCurve) :
    P.x = X.x ↔ P = X ∨ P = -X :=
  ⟨Point.eq_or_eq_neg_of_x_eq hP hX, by rintro (rfl | rfl) <;> rfl⟩

/-! ## One position -/

/-- **Theorem 5.4.4, as a computation**: on-curve, the specification's step is `[2]acc + S m`, and
`⊥` exactly at `acc = S m`, `acc = −S m`, or `[2]acc + S m = 𝒪`. `incompleteAdd`'s `sumZero`
escape (`acc + S m = 𝒪`) is subsumed by `acc = −S m`, and its `doubleCollision` escape is the third
disjunct. -/
theorem step_eq_of_onCurve {S : ℕ → Point Fp} {m : ℕ} {acc : Point Fp} (hAcc : acc.OnCurve)
    (hS : (S m).OnCurve) :
    step S m acc =
      if acc = S m ∨ acc = -S m ∨ (2 : ℕ) • acc + S m = 0 then none
      else some ((2 : ℕ) • acc + S m) := by
  have hAccV : acc.Valid := .inl hAcc
  have hSV : (S m).Valid := .inl hS
  have hAcc0 := Point.ne_zero_of_onCurve hAcc
  have hS0 := Point.ne_zero_of_onCurve hS
  show (acc ⸭ S m).bind (· ⸭ acc) = _
  by_cases hx : acc.x = (S m).x
  · -- collision: first `⸭` ⊥, `acc = ±S m`
    rw [if_pos ((x_eq_iff_eq_or_eq_neg hAcc hS).mp hx |>.imp_right Or.inl)]
    simp only [Point.incompleteAdd_def, hx, or_true, if_true, Point.bot_eq_none, Option.bind_none]
  -- sumZero ⊆ collision: `acc + S m = 𝒪` ⇒ `S m = −acc`, same `x`
  have hT0 : acc + S m ≠ 0 := fun h =>
    hx (by rw [(add_eq_zero_iff_eq_neg_of_valid hAccV hSV).mp h, Point.neg_x])
  have hT := Point.onCurve_of_valid_of_ne_zero (Point.valid_add hAccV hSV) hT0
  have hsum := add_add_self_of_valid hAccV hSV
  -- doubleCollision: `(acc + S m).x = acc.x` ⇔ `acc + S m = −acc` (`= acc` ⇒ `S m = 𝒪`, excluded)
  have hx2 : (acc + S m).x = acc.x ↔ (2 : ℕ) • acc + S m = 0 := by
    rw [x_eq_iff_eq_or_eq_neg hT hAcc, add_eq_left_iff_of_valid hAccV hSV, or_iff_right hS0,
      ← add_eq_zero_iff_eq_neg_of_valid (Point.valid_add hAccV hSV) hAccV, hsum]
  have hne := not_or.mp ((x_eq_iff_eq_or_eq_neg hAcc hS).not.mp hx)
  simp only [Point.incompleteAdd_def, hAcc0, hS0, hx, hT0, hx2, hne, or_false, false_or, if_false,
    Point.bot_eq_none, Option.bind_some, hsum]

theorem step_onCurve {S : ℕ → Point Fp} {m : ℕ} {acc B : Point Fp} (hAcc : acc.OnCurve)
    (hS : (S m).OnCurve) (h : step S m acc = some B) : B.OnCurve := by
  rw [step_eq_of_onCurve hAcc hS, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨hc, rfl⟩ := h
  exact Point.onCurve_of_valid_of_ne_zero
    (Point.valid_add (Point.valid_nsmul (.inl hAcc) 2) (.inl hS)) fun h0 => hc (.inr (.inr h0))

/-- The `x`-test resolved on-curve: `weightedStep` is `⊥` exactly at `P = ±[2]T` or `P + T = 𝒪`. -/
theorem weightedStep_eq_of_onCurve {P T : Point Fp} (hP : P.OnCurve) (hT : T.OnCurve) :
    weightedStep P T =
      if P = (2 : ℕ) • T ∨ P = -((2 : ℕ) • T) ∨ P + T = 0 then none else some (P + T) := by
  have h2T : ((2 : ℕ) • T).OnCurve := by simpa using two_pow_nsmul_onCurve hT 1
  simp only [weightedStep, x_eq_iff_eq_or_eq_neg hP h2T, or_assoc]

/-- **Per-position theorem**: one weighted step at weight `k` is the specification's step rescaled
by `[2^k]`, with `⊥` on exactly the same inputs; `two_pow_nsmul_inj` carries each exceptional
condition across the rescaling. -/
theorem weightedStep_eq_step {S : ℕ → Point Fp} {m : ℕ} {acc : Point Fp} (hAcc : acc.OnCurve)
    (hS : (S m).OnCurve) (k : ℕ) :
    weightedStep ((2 ^ (k + 1) : ℕ) • acc) ((2 ^ k : ℕ) • S m) =
      (step S m acc).map ((2 ^ k : ℕ) • ·) := by
  have hAccV : acc.Valid := .inl hAcc
  have hSV : (S m).Valid := .inl hS
  have hsum :
      (2 ^ (k + 1) : ℕ) • acc + (2 ^ k : ℕ) • S m = (2 ^ k : ℕ) • ((2 : ℕ) • acc + S m) := by
    rw [nsmul_add_of_valid (Point.valid_nsmul hAccV 2) hSV, two_pow_nsmul_two_nsmul hAccV]
  have hz := two_pow_nsmul_inj (Point.valid_add (Point.valid_nsmul hAccV 2) hSV) Point.valid_zero k
  rw [nsmul_zero_point] at hz
  rw [weightedStep_eq_of_onCurve (two_pow_nsmul_onCurve hAcc (k + 1)) (two_pow_nsmul_onCurve hS k),
    step_eq_of_onCurve hAcc hS, nsmul_nsmul_of_valid hSV, ← pow_succ, ← nsmul_neg_of_valid hSV,
    hsum]
  simp only [two_pow_nsmul_inj hAccV hSV, two_pow_nsmul_inj hAccV (Point.valid_neg hSV), hz]
  split_ifs <;> rfl

/-! ## The chain -/

/-- The invariant `P = [2^|ms|] acc` carried down the chain: induction on `ms` generalising `acc`,
with `weightedStep_eq_step` at each position and `step_onCurve` to keep the hypothesis. -/
theorem weightedFrom_eq_hashToPoint {S : ℕ → Point Fp} {acc : Point Fp} {ms : List ℕ}
    (hAcc : acc.OnCurve) (hS : ∀ m ∈ ms, (S m).OnCurve) :
    weightedFrom S ((2 ^ ms.length : ℕ) • acc) ms = hashToPoint S acc ms := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    rw [hashToPoint_cons, weightedFrom, List.length_cons,
      weightedStep_eq_step hAcc (hS m List.mem_cons_self) ms.length]
    cases h : step S m acc with
    | none => rfl
    | some B =>
      exact ih (step_onCurve hAcc (hS m List.mem_cons_self) h)
        fun m' hm' => hS m' (List.mem_cons_of_mem m hm')

/-- **Main theorem**: the weighted evaluator is the specification's function, `⊥` included, for an
on-curve domain point and on-curve generators at the chunks consumed.

The hypotheses are necessary rather than convenient. At `Q = 𝒪` or `S m = 𝒪` the specification is
`⊥` at once (`accZero`, `genZero`), while the weighted chain sees `[2ⁿ] 𝒪 = 𝒪` and `P + 𝒪 = P` and
carries on; the known domains have `Q ≠ 𝒪`, and group hashing never yields the identity. No bound
on `chunks.length` or on the chunk values is needed, because `S` is total and `q ∤ 2^k`; the Rust
asserts both. -/
theorem weightedHashToPoint_eq_hashToPoint {S : ℕ → Point Fp} {Q : Point Fp}
    {chunks : List ℕ} (hQ : Q.OnCurve) (hS : ∀ m ∈ chunks, (S m).OnCurve) :
    weightedHashToPoint S Q chunks = hashToPoint S Q chunks :=
  weightedFrom_eq_hashToPoint hQ hS

/-- The join with Ironwood's Σ-refinement: forgetting `hashToPointB`'s break data gives the
weighted evaluator, by the main theorem and the projection lemma `getLeft?_hashToPointB`. -/
theorem weightedHashToPoint_eq_getLeft?_hashToPointB {S : ℕ → Point Fp} {Q : Point Fp}
    {chunks : List ℕ} (hQ : Q.OnCurve) (hS : ∀ m ∈ chunks, (S m).OnCurve) :
    weightedHashToPoint S Q chunks = (hashToPointB S Q chunks).getLeft? :=
  (weightedHashToPoint_eq_hashToPoint hQ hS).trans (getLeft?_hashToPointB S Q chunks).symm

/-- Position 0 alone, the `FIRST_STEPS[m]` row of `src/table.rs` (`None` exactly at
`weightedStep`'s `⊥`). -/
theorem weightedHashToPoint_cons (S : ℕ → Point Fp) (Q : Point Fp) (m : ℕ) (ms : List ℕ) :
    weightedHashToPoint S Q (m :: ms) =
      (weightedStep ((2 ^ (ms.length + 1) : ℕ) • Q) ((2 ^ ms.length : ℕ) • S m)).bind
        fun acc => weightedFrom S acc ms :=
  rfl

end SinsemillaProofs
