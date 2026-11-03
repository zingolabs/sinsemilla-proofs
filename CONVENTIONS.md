# Style and quality conventions, derived from Daira-Emma Hopwood's Lean 4

Target: `SinsemillaProofs/{Weighted,Lockstep,Jacobian}.lean`, `README.md`, `lakefile.toml`, repo
layout. Bar: "would Daira-Emma write it this way". Every rule below is derived from code she
wrote, with a verbatim citation; §10 lists what to change here.

**Sources** (all under `SRC = /tmp/claude-1000/-home-elicb-DevProjects-ZingoLabs-zebra/75ca8713-9006-4e0a-926c-2375151d23df/scratchpad/lean/`):

| Alias | Repo | Authorship (`git log --format=%an`) |
|---|---|---|
| `IW/` | daira/ironwood (483 `.lean`) | 100% Daira-Emma Hopwood |
| `CE/` | daira/CompElliptic (46 `.lean`) | 100% Daira-Emma Hopwood |
| `ZL/` | daira/zcash-lean (6 `.lean`, last commit 2026-06) | 100% Daira-Emma Hopwood; **legacy style** (plain `/- -/` comments, `simp_all`, `lemma`; `ZL/Zcash/Math/Curves.lean:7-30`). Not a model; cited only as a counterexample. |
| `daira/clean`, `daira/cryptolib` | forks | **zero commits by her** (Clean = Verified-zkEVM; cryptolib = Alfredo Garcia et al.). Not used. |

Book chapters (`IW/book/src/formal-verification/*.md`, published at `zcash.github.io/ironwood`)
are hers and are cited for scope/CI conventions. Statistics are over the 416 hand-written files of
`IW/Zcash` + `CE/CompElliptic` (generated fixtures/generator tables excluded).

---

## 1. Repository and module organization

**R1.1 — One import root per library; the root file documents that it is an entry point, not a
re-export surface.** `IW/Zcash.lean:1-5`:
```
-- This module serves as the root of the `Zcash` library: its sole import root, so
-- `lake build Zcash` is exactly this file's transitive closure. No module imports it — it is a
-- build entry point, not a re-export surface — ...
```
Our `SinsemillaProofs.lean` has three bare imports and no comment (mechanical fix).

**R1.2 — `lakefile.toml` shape** (`IW/lakefile.toml:1-8`, `CE/lakefile.toml:1-8`, `ZL/lakefile.toml`):
`name`, `version = "0.1.0"`, `keywords = ["cryptography", "math", "protocols"]`, `defaultTargets`,
then `[leanOptions]` with `pp.unicode.fun = true # pretty-prints \`fun a ↦ b\`` and
`autoImplicit = false`. Every git-pinned `[[require]]` says *what* the pin is (`:18`
`# CompElliptic main, at the merge of the Weil-bound reduction (PR #29).`); require order is
justified (`:21-22` `# mathlib last, so that its pinned versions of the common transitive
dependencies ... take precedence over CompPoly's.`); every `[[lean_lib]]` glob has a comment
saying why it exists and what would silently go wrong without it (`:28-56`, `CE/lakefile.toml:15-21`).
Ours: `pp.unicode.fun` uncommented, Ironwood pin undated, glob uncommented, mathlib not last.

**R1.3 — `--wfail` is the CI build and is named in the README.** `IW/README.md:14-24`:
`lake build --wfail   # verify every proof; --wfail makes warnings fail, as CI does`;
`IW/.github/workflows/lean.yml:190` `build-args: "--wfail Zcash FixtureCheck ..."` with the comment
(`:181-186`) that CI names targets explicitly "so CI's build surface is pinned here".
`sorry` is thereby a CI failure even where no census entry reaches it (`book/.../ci-checks.md:17-20`).

**R1.4 — Namespace layout.** Ironwood: `Zcash/Circuits/Specs/` (value-level spec definitions),
`Zcash/Security/` (reductions/games), `Zcash/Common/` (shared leaves), `Zcash/Meta/` (census
machinery), `Zcash/TrustBoundary.lean` (census), `*/Tests/` and `BridgeTests.lean` (empirical and
regression checks in *separate* lake targets so they never enter the production import graph,
`IW/lakefile.toml:58-63,104-114`). A small downstream repo keeps its own package name; a
`Zcash.…` namespace is Ironwood's and must not be squatted (see §10).

**R1.5 — README structure** (`IW/README.md`, `CE/README.md`): title; one-paragraph purpose; "a
successful build *is* the verification" + exact commands (`IW/README.md:13-24`); CI checks and
where they are documented; **Design principles**, *named* (`CE/README.md:11-61`); **Trust
discipline** — which axioms general theorems may use, where the census lives (`:63-114`);
**Status** listing each result with its file path (`:116-152`); **Future work**; **License**
(dual Apache-2.0/MIT); **Acknowledgements** (`:163-165` "Claude Opus 4.8 was used in the
development of this project.").

**R1.6 — Source-level checks are shell/python scripts under `scripts/`, each run as a named CI
step, each with a header comment explaining the failure mode it closes.** `IW/scripts/
check_no_umbrella_imports.sh:1-24`, `check_build_coverage.sh:1-25`, `check_endpoint_census.sh:1-40`;
`IW/.github/workflows/lean.yml:78-110`. The umbrella rule: never `import Mathlib` or
`import Mathlib.Tactic`; import narrow modules (`IW/Zcash/Security/Ledger/MerkleDLR.lean:1-4`:
`import Mathlib.Tactic.FieldSimp` / `Linarith` / `NormNum` / `Ring`). Ours imports only
`Zcash.Circuits.Specs.SinsemillaBreak` — compliant, but the tactic modules we use
(`field_simp`, `linear_combination`, `abel`) arrive transitively; make them explicit.

**R1.7 — Ancillary files.** `lean-toolchain` = the dependency's (`v4.30.0`, matches ours);
`lake-manifest.json` committed; `.gitignore` = `/.lake`, `/.elan`; `_typos.toml` with the ≤3-char
identifier exemption (`IW/_typos.toml:17-20`); CompElliptic files carry a copyright header
(`CE/CompElliptic/TrustBoundary.lean:1-6`), Ironwood files do not (0 of 483) — pick none.

## 2. Module docstrings (`/-! # … -/`)

**R2.1 — Structure:** `# Title` (a noun phrase, often "X = Y" or "X as Z"); a `References:` list
when a spec section or crate is modelled; prose paragraphs explaining what is modelled, the key
notation, and what is deliberately out of scope and why. Full sentences, wrapped ≤ 100 columns.
Three full examples:

`IW/Zcash/Circuits/Specs/Sinsemilla.lean:5-27`:
```
/-!
# Sinsemilla value-level specification

References:
- Zcash protocol specification §5.4.1.9 (`SinsemillaHashToPoint`, `SinsemillaHash`)
- `sinsemilla@0.1` crate (`src/addition.rs`, `src/lib.rs`), the reference
  implementation used by `orchard` and by halo2's conformance tests

Sinsemilla is defined over *incomplete* addition `⸭ : P ∪ {⊥} × P ∪ {⊥} → P ∪ {⊥}`:
the result is `⊥` whenever an operand is `⊥` or the group identity, or the two points
have colliding `x`-coordinates (equal or opposite points); otherwise it agrees with the
group operation. The hash is the `⊥`-propagating chain

    Acc ← Q(D);  for each K-bit chunk mᵢ:  Acc ← (Acc ⸭ S(mᵢ)) ⸭ Acc

and `SinsemillaHash` extracts the `x`-coordinate (`Extract⊥`, with the identity mapped
to zero — our affine encoding of the identity is `(0, 0)`, so plain `.x` agrees).

The hash is a partial function by design: the protocol assumes it is infeasible to find
inputs hashing to `⊥` (finding one yields a discrete logarithm relation, protocol spec
Theorem 5.4.4). Circuit completeness statements therefore assume the hashed message is
non-exceptional, i.e. the spec-level hash is defined.
-/
```

`IW/Zcash/Circuits/Specs/SinsemillaBreak.lean:3-26` (opening):
```
/-!
# Sinsemilla exceptional cases as computed break data

The Σ-refinement of the ⊥-propagating `hashToPoint` chain requested by
the breaks-as-computed-data discipline: instead of collapsing every
incomplete-addition escape to `none`, `hashToPointB` returns `Point ⊕ BreakData`, ...

Fidelity to the specification's literal ⊥-model (§5.4.1.9) is the projection lemma
`getLeft?_hashToPointB`: mapping the break summand to `⊥` yields exactly
`hashToPoint`, so the Σ-form is a refinement — reviewers check the projection
against the spec text, and the refinement only adds the carried data.
```

`IW/Zcash/Circuits/Sinsemilla/Merkle.lean:15-33` ends with a single-line crate reference:
`Reference: \`halo2_gadgets/src/sinsemilla/merkle/chip.rs\`.` The Rust-reference forms she uses:
crate@version + path (`\`sinsemilla@0.1\` crate (\`src/addition.rs\`, \`src/lib.rs\`)`), or a
path inside a named crate; always in backticks, in `References:`/`Reference:` lines.

**R2.2 — Out-of-scope statements are prose with the reason**, e.g. `Sinsemilla.lean:40-42`
"Padding of bit-level messages into chunks (`pad` in the protocol spec) is part of message
construction and happens before this function."; `SinsemillaBreak.lean:352-362` explains why
exported statements do *not* use the break disjunction.

**R2.3 — Section headers inside a module are `/-! ## … -/` (608 uses) or `/-! ### … -/` (152), a
title alone or title + a short paragraph** (`Sinsemilla.lean:318-323`, `SinsemillaBreak.lean:85`,
`:149`, `:241`). Ironwood's `Sinsemilla.lean` uses `###` directly under `#`; `SinsemillaBreak.lean`
uses `##`. Prefer `##`.

**Counterexample (ours):** `Weighted.lean:3-13` is a bullet list of fragments with no
`References:` block and no sentence; `Lockstep.lean:217-225`, `Jacobian.lean:314-322` likewise.

## 3. Declaration docstrings

**R3.1 — Full sentences, terminated, `-/` on the last text line.** Short: one line
(`Sinsemilla.lean:36`: `/-- One Sinsemilla chunk step: \`(acc ⸭ S(m)) ⸭ acc\`. -/`). Long: `/--`
alone on its line, prose, `-/` alone (`Sinsemilla.lean:68-73`, `Pallas.lean:383-391`).

**R3.2 — Coverage is selective, not total.** `Sinsemilla.lean`: 34 docstrings / 43 declarations;
`SinsemillaBreak.lean`: 22 / 31; `Pallas.lean`: 11 / 74. No docstring on: `_nil`/`_cons`/`_append`
chain lemmas (`Sinsemilla.lean:83-116`), `_def`/`_x`/`_y` rfl lemmas (`Pallas.lean:115-118`),
`mono` (`:63`), restatements whose name is the statement (`SinsemillaBreak.lean:126,144,163`),
`instance`s, `two_ne_zero` (`Pallas.lean:230`). Docstring where the name under-determines the
content: the *meaning* of a definition, the hypothesis shape, what a lemma is *for*.

**R3.3 — A docstring says what the statement says, and when non-obvious, what it is for and why
the hypotheses are what they are.** `Sinsemilla.lean:118-119`: `/-- A defined step never lands on
the identity: its second incomplete addition excludes the colliding \`x\`-coordinates of
equal-or-opposite points. -/`. `SinsemillaBreak.lean:388-391` names the consumer. Cross-references
are backticked identifiers (`see \`specOrBreak_hashToPointB_iff_guarded\``), spec sections are
`(§5.4.1.9)` / `protocol spec Theorem 5.4.4`, file paths are backticked.

**R3.4 — Key theorems are announced in bold at the head of the docstring:**
`SinsemillaBreak.lean:120-121` `/-- **Projection lemma**: the Σ-refinement maps onto …`;
`:330-332` `/-- **Theorem 5.4.4, computational**: every break emitted by the Σ-chain is valid — …
Hypotheses are the on-curve facts of the generators actually consumed. -/`; `:400` `/-- **The
or-break disjunction adds no strength over the guarded ⊥-model.** Given only …`. Bold is used
for *that* kind of headline only (also `**Completeness**`, `**Domain-size fact**`); never for emphasis
inside sentences (that is `*italics*`: `:7` "*where*", "*which*").

**R3.5 — Structures/inductives:** a type-level docstring in prose stating what the type is and
how it fits (`Sinsemilla.lean:68-74` `Generators`, `SinsemillaBreak.lean:49-51` `BreakData`,
`Pallas.lean:33-37` `Point`). Fields: *no* docs when the name and type suffice (`BreakData`
`pre chunk rest acc kind`, `Point` `x y`, `Collision` in `RandomOracle.lean:51-55`); inductive
constructors *do* get one-line docs when each encodes a condition (`SinsemillaBreak.lean:34-46`
`/-- first addition, identity accumulator: \`acc = 𝒪\`. -/ | accZero`). `deriving` on the line after
the last field, unindented (`:47`, `:58`).

**R3.6 — `where`-helpers are top-level dotted defs with their own docstring, not `where` blocks:**
`SinsemillaBreak.lean:70-78` `/-- The Σ-refined chain: fold … -/ def hashToPointB.go …` then
`:80-83` `def hashToPointB … := hashToPointB.go S [] Q chunks`. Lemmas about the helper are
`private theorem go_getLeft?` (`:100`), `go_inr` (`:174`). Ours: `batchInverses … where go`
(`Lockstep.lean:288-295`) with a docstring on `go` that is a tuple-shaped fragment.

## 4. Naming

**R4.1 — `theorem`, not `lemma`** (5446 vs 46; `lemma` only for rfl projections in
`Pallas.lean:52-56,115-118,364`). Ours: all `theorem` — compliant.

**R4.2 — Mathlib-style compositional names.** Suffix/infix frequencies over `IW/Zcash/Circuits`
+ `Security`: `_eq` 333, `_of_` 204, `_iff` 34+18, `_ne_zero` 20+9, `_onCurve` 19, `_valid` 14,
`_inj` 8, `_some` 6, `_none` 5. Patterns to copy: `hashToPoint_cons`, `hashToPoint_append_some`,
`step_ne_zero`, `step_valid`, `nsmul_eq_zero_iff`, `y_ne_zero_of_valid_of_x_ne_zero`,
`eq_or_eq_neg_of_x_eq`, `getLeft?_hashToPointB` (projection: `<proj>_<def>`), `hashToPointB_inl`
/ `hashToPointB_inr` (constructor-case lemmas), `chunksOf_mem_lt`, `merkleChunks_eq_chunksOf`,
`stepB_inr`. Private helpers are plain descriptive names (`foldl_none`, `go_inr`,
`collision_resolve`, `step_valid_of_valid`); `_aux` is rare (16 in 483 files).

**R4.3 — Hypothesis names: `h` + capitalised subject, or `h` + short tag.** Top counts: `h`,
`hQ`, `hi`, `hP`, `hS`, `hx`, `hne`, `hbound`; validity/curve variants `hQvalid`
(`Sinsemilla.lean:163`), `haccV` / `haccC` (`SinsemillaBreak.lean:296-297`), `hsplit hpre hEq`
(`:336`); numbered `hc₁ hc₂` (`Sinsemilla.lean:123,129`) or `h1 h2` (`SinsemillaBreak.lean:92`).
Ours (`hP hT hAcc hS hZ hx hne hsum hAccV hSV`) is compliant.

**R4.4 — Variables.** Generators `S : ℕ → Point Fp`; domain point `Q`; accumulator `acc`
(lowercase, 11/11 in Specs — ours uses `Acc`); message `chunks` (the spec's word), tail `ms`/`rest`,
prefix `pre`, word `m`; points `A B` (Sinsemilla) or `p q` (Pallas) or `P` — `P` is also used for a
predicate (`HashGuarded … (P : Point Fp → Prop)`), so do not mix in one file. Lists `l₁ l₂`.
Scalars `k n m`. Our `words` ≠ her `chunks` (see §10).

**R4.5 — Unicode:** `𝒪` for the identity in prose (`SinsemillaBreak.lean:21`), `⊥` for `none` in
prose and *in definitions* via the `Bot (Option α)` instance (`Pallas.lean:349-360`), `⸭` as
`infixl:65` (`:362`), `ℕ`, `Σ`-refinement, `∑ⱼ`, subscripts `l₁ hc₁ x₃`, `−` (U+2212) inside prose
math (`acc = −S m`) but ASCII `-` in code. `(2 : ℕ) • acc` with the explicit `ℕ` ascription
(`:253`).

**R4.6 — `abbrev` vs `def`:** `abbrev` only for transparent type/notation aliases — `Fp`, `Fq`
(`Pallas.lean:20-21`), `EqUpToSign` with the docstring saying *why* (`RandomOracle.lean:45-47`:
"An `abbrev`, so it is definitionally transparent."). Everything with content is `def`.

## 5. Statement style

**R5.1 — Hypotheses are explicit named `OnCurve`/`Valid` facts, never bundled into the point
type.** `Sinsemilla.lean:120-121` `(a_valid : A.Valid) {m : ℕ} (hm : m < 2 ^ K)`;
`SinsemillaBreak.lean:333-335` `(hQ : Q.Valid) (hS : ∀ m ∈ chunks, (S m).OnCurve)`. Weakest
hypothesis that works: `Q.Valid` where `𝒪` is tolerated, `OnCurve` where it is not; table facts as
`∀ m ∈ chunks, (S m).OnCurve` (membership-bounded, not `∀ m`). Ours matches this shape exactly.

**R5.2 — Implicit `{}` for anything determined by a hypothesis; explicit `()` for data the lemma
is "about" with no hypothesis** (`hashToPoint_cons (S) (Q) (m) (ms)` `:92-93` vs
`hashToPoint_valid {Q B} {l} (hQvalid …)` `:181-183`). Ours matches.

**R5.3 — `⊥` is `none`, removed in proofs.** `Pallas.lean:349-353`:
```
-- so we can use the cute ⊥ symbol for `none`
instance {α : Type} : Bot (Option α) := ⟨none⟩

-- but we remove it in proofs
@[simp] theorem bot_eq_none {α : Type} : (⊥ : Option α) = none := rfl
```
Definitions write `⊥` (`:360`), statements `none`/`some` (`SinsemillaBreak.lean:89,146`), proofs
`simp only [..., Point.bot_eq_none, ...]`. Sequencing: `Option.bind` with a named lambda
(`(step S m Q).bind fun acc => hashToPoint S acc ms`, 6/6 in Specs) or `do` (`Pallas.lean:375-377`);
`(·.x)` only for a projection (`Sinsemilla.lean:51`). Ours: `none` in `weightedStep` is fine; the
`·` lambda in `weightedFrom` (`Weighted.lean:32`) deviates.

**R5.4 — Statements are the spec's statement; refinements are projections.** The pattern
(`SinsemillaBreak.lean:60-124`): a Σ-refined definition (`stepB : Point ⊕ BreakKind`) whose branch
structure "mirrors `incompleteAdd`'s conditions in order", a step-level projection
`getLeft?_stepB : (stepB S m acc).getLeft? = step S m acc`, and the chain-level projection
`getLeft?_hashToPointB`. The exported fact is stated against `hashToPoint` (`Sinsemilla.lean:53-58`
`HashGuarded` — "with no break vocabulary"). Our main theorem is already stated against
`hashToPoint` (`Weighted.lean:199-202`) — correct. Whether `weightedStep` should become a
Σ-refinement is a judgment call (§10).

**R5.5 — Conditional statements use `if … then none else some …` on the right-hand side**
(`Pallas.lean:365`, `SinsemillaBreak.lean:251`), continuation indented 4 under `theorem`, the `if`
branch indented a further 2 (ours `Weighted.lean:117-119` — compliant).

**R5.6 — `set_option … in` immediately before the declaration it serves**
(`Sinsemilla.lean:282-284`).

## 6. Proof style

Corpus counts: `simp only` 3898 / `simp [...]` 992 / bare `simp` 261 / `simp_all` 139;
`obtain` 1974 / `rcases` 1420; `omega` 3759, `norm_num` 1425, `decide` 807, `ring` 639,
`linear_combination` 463, `field_simp` 69, `abel` 51; `by_cases` 408 / `split_ifs` 19; `aesop` 42.

**R6.1 — Term mode for one-step proofs**, with `fun` / anonymous constructors
(`Sinsemilla.lean:66` `fun B hB => h B (hg B hB)`; `:78-79` `Or.inl (G.S_onCurve hk)`;
`SinsemillaBreak.lean:122-124`). Tactic mode otherwise, `:= by` at the end of the statement line.

**R6.2 — `simp only` with an explicit lemma list is the default; bare `simp` only to close a
contradictory hypothesis** (`simp at h` after a `none`-case `rw`, `Sinsemilla.lean:125,174`) **or
in `<;> simp_all` after `split_ifs`** (`SinsemillaBreak.lean:92`). `rw [...]` chains are
multi-line with 4-space continuation (`Sinsemilla.lean:277-278`). `show` restates the goal to expose
`foldl` structure (`:96,99,108-110,222`). `unfold f at h` before `split_ifs at h with h1 h2 …`
(`SinsemillaBreak.lean:165-166`). `rw [show … from rfl]` for a definitional step she wants visible
(`Sinsemilla.lean:127-128`). `obtain rfl : A + G.S m + A = B := Option.some.inj h` (`:134`) to
substitute an equation. `cases h : step S m Q with | none => … | some acc => …` for `Option`
(`:97-102`); `induction … generalizing Q with` (`:165`).

**R6.3 — Transport `Point ↔ SWPoint` is always the same three moves:**
`rw [ext_toSW_iff (valid_…) (valid_…)]`, push `toSW` through `+ − •` with `toSW_add`/`toSW_neg`/
`toSW_nsmul`/`toSW_zero`, then the group law in `SWPoint` (`abel`, `add_eq_zero_iff_eq_neg`,
`addOrderOf_dvd_iff_nsmul_eq_zero`). `Pallas.lean:406-416` and `SinsemillaBreak.lean:311-328` are the
canonical instances. Ours (`Weighted.lean:50-104`) does exactly this — keep, but see R6.5.

**R6.4 — Arithmetic closers:** `decide` for closed `Fp` facts the kernel can run
(`Pallas.lean:230` `theorem two_ne_zero : (2 : Fp) ≠ 0 := by decide`), `norm_num [K]` for numeric
unfolding (`Sinsemilla.lean:297`), `omega` for `ℕ` inequalities, `ring`/`linear_combination` for
field identities, `field_simp` sparingly (69), `abel` in the `SWPoint` group.

**R6.5 — In-proof comments are rare and are one-line sentences or equation fragments stating the
case being handled.** Specs dir: 1 comment in 1654 lines; corpus: 1394 `--` lines / 5446
theorems; 399 are of the form `· -- …` opening a bullet case. Examples:
`SinsemillaBreak.lean:300` `-- \`(acc + P) = acc\` or \`(acc + P) = −acc\``; `:310`
`· -- \`acc + P = acc\` forces \`P = 𝒪\` — excluded`; `:318` `· -- \`acc + P = −acc\` gives
\`2·acc + P = 𝒪\``; `SinsemillaDLR.lean:338` `-- The prefix chain as the explicit table combination,
in the reduction's coefficients.`. Ours (`Weighted.lean:126,129,134`, `Lockstep.lean:268,274`,
`Jacobian.lean:365`) matches the density and the shape — keep.

**R6.6 — Column limit is 100** (Mathlib's). Hand-written histogram peaks at 85-99 columns;
696 of ~150k lines exceed 100 (<0.5%, all in long `Snark/` files); `Sinsemilla.lean` max 98,
`SinsemillaBreak.lean` max 86, `MerkleDLR.lean` max 91. Prose in docstrings is typically wrapped
at ~85-95. Ours: max 99, 0 lines > 100 — compliant.

**R6.7 — Indentation:** 2 spaces for proof bodies and `|` match arms; 4 spaces for a continued
statement or a continued `rw`/`simp only` list; `·` bullets with the tactic on the same line.
Blank line between declarations; none between a docstring and its declaration.

## 7. Trust boundary and axiom discipline

**R7.1 — The census is a file, and it is prose-documented.** `IW/Zcash/TrustBoundary.lean:92-139`
(module doc: what the two commands assert, why coverage flows downward only, why endpoints must be
pinned *directly*); `CE/CompElliptic/TrustBoundary.lean:17-41` (three tiers: general theorems —
standard axioms only; kernel-checked closed facts; compiler-trusted closed facts marked
`+native(...)`). Entries are grouped under `/-! ## … -/` with a sentence per group
(`IW:150-156`, `:191-197`) and a `--` line naming the source file (`:199-202`
`-- Indiff.lean: one-oracle indifferentiability at the deployed mappings.`).

**R7.2 — The commands.** `assert_axioms <fully.qualified.name>` bounds a theorem at
`propext`/`Classical.choice`/`Quot.sound`; `+native(<owner decl>, …)` names *exactly* which
`native_decide` certificates it may inherit (`IW:203-206`):
```
assert_axioms Zcash.Security.GroupHash.pallas_indiffFromRO +native(
  CompElliptic.Fields.Pasta.pallasBase,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt,
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_isoGpt)
```
`assert_computable <def> [+choice]` for break-producing `def`s (`IW:280-281`). Names must be fully
qualified (`IW/Zcash/Meta/AxiomCheck.lean:35-39`). Both live in `Zcash.Meta.AxiomCheck`, which
**our repo can import** (we already depend on Ironwood's `Zcash`).

**R7.3 — `native_decide` is confined to closed numeric facts about concrete curves/fields;
general theorems never use it** (`CE/README.md:73-88`). We use none ourselves; our only compiler
trust is inherited through `Point.addOrderOf_eq → pallas_natCard → CompElliptic.…card_eq`
(`Pallas.lean:383-394` documents precisely this inheritance in prose — copy the pattern).

**R7.4 — `sorry` is never committed; `--wfail` fails on it; no `noncomputable` on anything that
produces data** (`RandomOracle.lean:27-33`: "a plain `def`, never `noncomputable`").
`noncomputable` appears only on `PMF`/experiment definitions (94 uses, all `Security/`).

**R7.5 — Per-module census for test/regression files:** `BridgeTests.lean:189-197` pins its own
theorems with `assert_axioms` at the bottom of the file.

## 8. Testing and empirical checks

**R8.1 — `#eval`/`#guard` checks live in dedicated modules under a separate lake target**
(`CircuitCheck`, `SecurityCheck`, `MetaCheck`; `IW/lakefile.toml:92-114`), one `#eval` per file
with a `/-! … -/` comment explaining why it is one (`IW/Zcash/Circuits/Tests/
TestVkLayoutActionBase.lean:16-20`), a named `("check", decide (...))` list with a `--` line per
check (`:35-46`).

**R8.2 — Regression theorems guarding "the protocol distinctions a type-correct refinement can
silently erase"** (`BridgeTests.lean:5-12`): small explicit statements, one-line docstrings, each
censused in the same file (`:189-197`). For this repo see G12.

## 9. Documentation beyond code

**R9.1 — Scope statements are explicit about what is *not* verified**, in numbered or bulleted
prose, naming the issue tracking each gap (`guide.md:67-116`, `:343-360` "The whole set, in one
place"). Ironwood's README delegates this to the book; CompElliptic's README carries it inline
(**Trust discipline**, **Status**). For a small repo, inline (CompElliptic model).

**R9.2 — Rust is referenced by crate@version + file path, functions in backticks**
(`Sinsemilla.lean:10-11`, `Merkle.lean:33`, `IW/Zcash/Snark/**`: `\`plonk/verifier.rs\``).
Never by line number. Ours references `table.rs`, `TableDomain::hash_to_point`,
`add_in_lockstep` without the crate/PR/commit pin.

**R9.3 — Issues/PRs are cited as `repo#N`** (`ironwood#65`, `lean4#7463`, `PR #29`).

**R9.4 — The breaks-as-computed-data discipline is named and linked** wherever an `Option`/`⊕`
modelling choice is made (`RandomOracle.lean:27-33` links
`zcash.github.io/ironwood/formal-verification.html#breaks-as-computed-data`).

---

## 10. Gap analysis for sinsemilla-proofs (prioritised)

Legend: **M** = mechanical (apply as stated); **J** = judgment call (recommendation given).

**G1 (M, highest) — Rewrite every `/-! -/` and `/-- -/` docstring as prose** per §2-3. All of
ours are bullet/fragment lists (`Weighted.lean:3-13,21-24,28-29,34-35,49,106,113-114,149,
156-157,177-178,193-198,204-207`; `Lockstep.lean:217-225,232-237,253-254,283-287,290,306`;
`Jacobian.lean:314-322,328,336-337,353-354,387`). Module docs get `# Title`, `References:`
(protocol spec §5.4.1.9 and Theorem 5.4.4; `sinsemilla` crate @ the exact zcash/sinsemilla#9
commit, `src/table.rs`; Ironwood `Zcash.Circuits.Specs.Sinsemilla` @ pinned rev), then paragraphs
on what is modelled and what is out of scope with reasons. Headline theorems
(`weightedHashToPoint_eq_hashToPoint`, `step_eq_of_onCurve`, `jacStep_sound`) get a bold lead.
Drop docstrings on `rfl` restatements (`weightedHashToPoint_cons`: one line suffices). Scope note:
the global CLAUDE.md "notes, not prose" rule governs `--` code comments; Lean docstrings are the
reviewer-facing document (CLAUDE.md's "user-facing doc strings" exception) and follow her prose.
In-proof `--` comments stay terse — both styles agree (R6.5).

**G2 (M) — Add `SinsemillaProofs/TrustBoundary.lean`** importing `Zcash.Meta.AxiomCheck` and the
three modules, with a §7.1-style module doc, pinning every exported theorem:
`assert_axioms SinsemillaProofs.weightedHashToPoint_eq_hashToPoint +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)`
(inherited via `Point.addOrderOf_eq`; add `pallasBase` only if the build reports it), likewise
`step_eq_of_onCurve`, `weightedStep_eq_step`, `laneStep_eq_weightedStep`, `batchInverses_eq`,
`jacStep_sound`, `jacStep_eq_none_iff`, `jacStep_none_of_weightedStep_none`. Import it last from
`SinsemillaProofs.lean`. If `assert_axioms` rejects a downstream package for an
`ambientPackageRoots` reason, fall back to `#guard_msgs in #print axioms` and say so in the doc.

**G3 (M) — `lakefile.toml`:** add `keywords`; comment `pp.unicode.fun`; date the Ironwood pin
("Ironwood main at <date>, the rev whose `SinsemillaBreak` we state against"); move `mathlib`
last with her comment; comment the `[[lean_lib]]` glob; add any new check targets to
`defaultTargets`.

**G4 (M) — `SinsemillaProofs.lean` root comment** per R1.1, and import `TrustBoundary` last.

**G5 (M) — README restructure** on the CompElliptic model: purpose paragraph; **Why** (keep);
**What is proved** (keep the table; Rust named by crate@commit + file); **Trust discipline** in
prose — general theorems rest on standard axioms, the single inherited `native_decide` certificate
and where it is pinned, what is *not* modelled and why (R9.1); **Verifying the proofs** with
`lake exe cache get` / `lake build --wfail` and "a successful build *is* the verification"
(`IW/README.md:13-24`); **Future work**; **License** (dual); **Acknowledgements** disclosing AI
use (`CE/README.md:163-165`).

**G6 (M) — CI + scripts:** `.github/workflows/lean.yml` running `leanprover/lean-action` with
`build-args: "--wfail <all default targets>"`, plus `scripts/check_no_umbrella_imports.sh` and
`scripts/check_build_coverage.sh` (header comment stating the failure mode each closes, R1.6);
`_typos.toml`; `.gitignore`.

**G7 (M) — Explicit narrow Mathlib imports** for the tactics used (`Mathlib.Tactic.FieldSimp`,
`.LinearCombination`, `.Abel`, `.Ring`, `.NormNum`) rather than relying on transitive arrival
(`MerkleDLR.lean:1-4`).

**G8 (M) — Naming:** `Acc` → `acc` (R4.4); `words` → `chunks` (she models the identical object
as `chunks`; note Rust's "words" in the docstring); `Jac` → `JacobianPoint`, `jacStep` →
`jacobianStep` (`CE/design/naming-survey.md` "coordinate system: Jacobian"); `where go` →
top-level `batchInverses.go` with its own docstring (R3.6). Keep hypothesis names.

**G9 (M) — `weightedFrom` lambda:** `(weightedStep …).bind (weightedFrom S · ms)` →
`.bind fun acc => weightedFrom S acc ms` (R5.3).

**G10 (J) — Σ-refinement of `weightedStep`.** Her Σ pattern exists because *break data* is
consumed downstream (`BreakData` feeds the DLR reduction). Our results are equalities of
`Option`-valued functions exported against `hashToPoint` — exactly the form she requires of
exported statements (R5.4, `SinsemillaBreak.lean:352-356`). **Recommendation: no Σ-refinement.**
State in the module doc that `weightedStep` is deliberately in the literal ⊥-model and break data
is `hashToPointB`'s job, and add the two-line corollary
`weightedHashToPoint_eq_getLeft?_hashToPointB : (hashToPointB S Q chunks).getLeft? =
weightedHashToPoint S Q chunks` (from `getLeft?_hashToPointB` + the main theorem) so reviewers
see the join.

**G11 (J) — Namespace.** Keep `SinsemillaProofs`; do not move under `Zcash.…` (Ironwood's root;
collides on `open`). Note in Future work that the upstream home would be
`Zcash/Circuits/Specs/SinsemillaWeighted.lean`.

**G12 (J) — Smoke check module.** Recommend `SinsemillaProofs/Tests/Smoke.lean` (R8) in its own
`SmokeCheck` target: `#guard`/`example … := by decide` on a 2-3 chunk message over small concrete
on-curve points (the Pallas generator `(-1, 2)` and multiples). It is what she ships beside every
reviewed spec module, and it catches a coordinate typo in `laneStep`/`jacStep` that theorems
relative to `weightedStep` cannot.

**G13 (J) — `jacStep_sound` conjunction** `p'.Z ≠ 0 ∧ weightedStep p.affine T = some p'.affine`.
She names theorems for one conclusion each. **Recommendation:** split into
`jacobianStep_Z_ne_zero` and `affine_jacobianStep`; keep `jacStep_none_of_weightedStep_none`.

**G14 (M) — In-proof comments** already match R6.5; leave them.

**G15 (M) — Licence files:** `LICENSE-APACHE`, `LICENSE-MIT`, README licence wording from
`IW/README.md:34-49`; no per-file headers.
