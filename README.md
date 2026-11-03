# sinsemilla-proofs

Lean 4 proofs that the position-weighted Sinsemilla evaluators of the `sinsemilla` crate
(zcash/sinsemilla#9's tables, `TableDomain::hash_to_point`, and the batched
`hash_many_vartime` paths built on them) compute the Zcash protocol specification's
`SinsemillaHashToPoint` (§5.4.1.9), **including exactly which inputs give ⊥**. Every result is
stated against Ironwood's spec-level definitions (`Zcash.Circuits.Specs.Sinsemilla.hashToPoint`),
so a reviewer trusts no new model of Sinsemilla: the only new definitions are the evaluators
themselves, and the theorems say they equal the specification as functions.

## Why

The specification computes `Accᵢ = (Accᵢ₋₁ ⸭ S(mᵢ)) ⸭ Accᵢ₋₁` with incomplete addition. The table
evaluators never form `Accᵢ`; they compute `Pᵢ = [2^(n−i)] Accᵢ` (one addition per chunk) and
test Theorem 5.4.4's conditions rescaled onto `P`. Equality with the specification in the generic
case is checked by differential tests on random inputs. The ⊥ cases cannot be: no real input
reaches them (finding one is a discrete-log relation, Theorem 5.4.4), so a wrong ⊥ rule passes
every test while the function silently differs from the specification. Merkle roots feed consensus
(Zebra's anchors), so the bar is equality as functions. That is what these proofs establish.

## What is proved

The Rust is the `sinsemilla` crate at `elicbarbieri/sinsemilla` commit
`eb3e2f50ef363774169ae8f8877712689e654674` (branch `perf/hash-many-vartime`: zcash/sinsemilla#9
head `596e662` plus four commits); Ironwood is `daira/ironwood` at
`86e3c7026db8c9af27ca731e6b5c7f2d8fc7f0fc`.

| File | Statement | Rust it models |
|---|---|---|
| `SinsemillaProofs/Weighted.lean` | `step_eq_of_onCurve`: Theorem 5.4.4 as a computation (`step` = `[2]acc + S`, ⊥ at `acc = ±S` or `[2]acc + S = 𝒪`) | — (specification side) |
| `SinsemillaProofs/Weighted.lean` | `weightedStep_eq_step`: one weighted position at weight `k` = the spec step rescaled by `[2^k]`, ⊥ ↔ ⊥ | loop body of `TableDomain::hash_to_point` (`src/table.rs`) |
| `SinsemillaProofs/Weighted.lean` | `weightedHashToPoint_eq_hashToPoint`: weighted evaluator = `hashToPoint` (⊥ included), for on-curve `Q` and generators | `TableDomain::hash_to_point`, at the group level |
| `SinsemillaProofs/Weighted.lean` | `weightedHashToPoint_eq_getLeft?_hashToPointB`: the join with Ironwood's break-data refinement `hashToPointB` | — |
| `SinsemillaProofs/Weighted.lean` | `weightedHashToPoint_cons`: position 0 alone | `FIRST_STEPS` rows (`None` = position-0 ⊥) |
| `SinsemillaProofs/Lockstep.lean` | `laneStep_eq_weightedStep`: one lane (`x` test, chord, tangent when `lane = addend`, ⊥ when `lane = −addend`) = `weightedStep` | `add_in_lockstep` per lane |
| `SinsemillaProofs/Lockstep.lean` | `batchInverses_eq`: the fused Montgomery trick gives each `d⁻¹` | `add_in_lockstep`'s two passes |
| `SinsemillaProofs/Jacobian.lean` | `jacobianStep_Z_ne_zero`, `affine_jacobianStep`: a returned Jacobian step keeps `Z ≠ 0` and is `weightedStep` on the affine view | `Jacobian::step` (below `LOCKSTEP_LANES`) |
| `SinsemillaProofs/Jacobian.lean` | `jacobianStep_none_of_weightedStep_none`, `jacobianStep_eq_none_iff`: every ⊥ is handed back (`None` reruns the message through `hash_to_point`), and exactly which steps are | `Jacobian::step` → `hash_to_point` fallback |

Both variable-time paths reduce to `weightedStep`, so `TableDomain::hash_many_vartime` is covered
through the main theorem. Not covered, by design: `HashDomain::hash_many_vartime` (`src/lib.rs`)
and `hash_words` fall back to `accumulate`, the specification's own recurrence, for untabled
domains, `N = 0`, and `N` past `LONGEST_MESSAGE_WORDS`; that path is the specification, not the
weighted evaluator, and is not modelled.

Each module's docstring states what it models, with references, and what it leaves out and why.
`SinsemillaProofs/Tests/Smoke.lean` runs the evaluators on concrete points (a generic message, a
constructed ⊥, and a doubling the Jacobian step hands back) as `#guard`s in a separate build
target, `SmokeCheck`.

## Trust discipline

The general theorems rest only on Lean's standard axioms, `propext` / `Classical.choice` /
`Quot.sound`. The results that go through the Pallas group order — `[2^k]` is injective and never
lands on the identity because `q ∤ 2^k`, which needs `q` to be the order — additionally inherit
one compiler-trusted closed fact: CompElliptic's point-count witness
`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt`, a `native_decide` certificate reached through
Ironwood's `Zcash.Circuits.Point.addOrderOf_eq`. Nothing in this repository uses `native_decide`,
`sorry`, or `noncomputable`.

That split is checked at build time, not asserted in prose: `SinsemillaProofs/TrustBoundary.lean`
pins every exported theorem with Ironwood's `assert_axioms` (from `Zcash.Meta.AxiomCheck`), the
general ones at the standard tier and the order-dependent ones with `+native(...)` naming exactly
that witness. A theorem that reaches beyond its tier, or a certificate entering or leaving a cone,
fails the build. `SinsemillaProofs.lean` imports the census last, so building the library enforces
it.

What is trusted, and not proved here:

1. Ironwood's spec-level definitions (`hashToPoint`, `step`, incomplete addition) as a faithful
   model of §5.4.1.9, and CompElliptic's Pallas group with its order witness above.
2. The correspondence between the Rust and these models. The models follow the Rust's branch
   structure on raw coordinates, but nothing here reads Rust; the crate's differential tests pin
   both sides against `hash_to_point` and the reference implementation.
3. The table contents: that `generators[w][j]` is `[2^w] S(j)` and `starts[d][n−1]` is `[2ⁿ] Q`
   (tested in the crate against group hashing), together with `pasta_curves`' Jacobian arithmetic
   inside `hash_to_point` (`+=`, `has_x_of`'s `X = x·Z²`), the field arithmetic and
   `invert_vartime`, chunk packing and the `< 2^K` / length assertions, and the dispatch between
   the lockstep and Jacobian paths at `LOCKSTEP_LANES`.

## Verifying the proofs

The development is Lean 4 over Mathlib and Ironwood, and building it re-elaborates every proof — a
successful build *is* the verification. The single command is `lake build --wfail`, with two
one-time prerequisites: install [`elan`](https://github.com/leanprover/elan) (the Lean toolchain
manager, which reads [`lean-toolchain`](lean-toolchain) and installs the pinned toolchain
automatically), then, from the repository root, fetch Mathlib's prebuilt artifacts so it need not
be recompiled from source:

```sh
lake exe cache get   # one-time: download prebuilt Mathlib artifacts
lake build --wfail   # verify every proof; --wfail makes warnings fail, as CI does
```

Ironwood, CompElliptic and their dependencies are built from source on the first run. CI
(`.github/workflows/lean.yml`) runs the same build with the targets named explicitly, plus two
source-level checks under `scripts/`: no Mathlib umbrella imports, and every module reachable
from a default target (so a module no target builds cannot pass by never being elaborated).

## Future work

- The upstream home for these statements would be Ironwood's
  `Zcash/Circuits/Specs/SinsemillaWeighted.lean`; the `SinsemillaProofs` namespace is kept here
  so as not to squat Ironwood's `Zcash` root.
- A Lean-side statement of the table contents (`[2^w] S(j)` from the generator definition) would
  move item 3 above from tests to proof.

## License

Copyright 2026 Eli Barbieri.

All code in this repository is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

## Acknowledgements

The Lean in this repository was written with AI assistance (Claude) and reviewed by the repository
author. It is stated against, and follows the conventions of, Daira-Emma Hopwood's
[Ironwood](https://github.com/daira/ironwood) and
[CompElliptic](https://github.com/daira/CompElliptic).
