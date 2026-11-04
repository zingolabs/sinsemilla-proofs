# sinsemilla-proofs

Lean 4 proofs that the position-weighted Sinsemilla evaluators of the `sinsemilla` crate
(zcash/sinsemilla#9's tables, `TableDomain::hash_to_point`, and the batched
`hash_many_vartime` paths built on them) compute the Zcash protocol specification's
`SinsemillaHashToPoint` ([§5.4.1.9](https://zips.z.cash/protocol/protocol.pdf#concretesinsemillahash)),
**⊥ included**: for an on-curve domain point and on-curve generators, the evaluators and the
specification give ⊥ on the same inputs. Every result is stated against Ironwood's spec-level
definitions (`Zcash.Circuits.Specs.Sinsemilla.hashToPoint`), so the only new definitions are the
evaluators themselves, and the theorems say they equal the specification as functions.

## Why

The specification computes `Accᵢ = (Accᵢ₋₁ ⸭ S(mᵢ)) ⸭ Accᵢ₋₁` with incomplete addition. The table
evaluators never form `Accᵢ`; they compute `Pᵢ = (2^(n−i)) • Accᵢ` (one addition per word) and
test Theorem 5.4.4's conditions rescaled onto `P`. Equality with the specification in the generic
case is checked by differential tests on random inputs. The ⊥ cases are out of a test's reach: no
known input triggers them, since finding one is a discrete-log relation (Theorem 5.4.4), so a
wrong ⊥ rule passes every test while the function silently differs from the specification. Merkle
roots feed consensus (Zebra's anchors), so the bar is equality as functions. That is what these
proofs establish.

## How the proof goes

The specification's step is `Accᵢ = (Accᵢ₋₁ ⸭ S(mᵢ)) ⸭ Accᵢ₋₁`, which on the curve is
`2 • Accᵢ₋₁ + S(mᵢ)`, ⊥ at `Accᵢ₋₁ = ±S(mᵢ)` and at a sum of `𝒪` and nowhere else (Theorem 5.4.4,
restated as a computation in `step_eq_of_onCurve`). The weighted evaluator keeps
`Pᵢ = (2^(n−i)) • Accᵢ` instead and adds `Tᵢ = (2^(n−1−i)) • S(mᵢ)` at each position. Pallas has
odd prime order `q`, so `q ∤ 2^k` (`not_dvd_two_pow`), `(2^k) •` is injective on the group
(`two_pow_nsmul_inj`), and it never sends a curve point to `𝒪` (`two_pow_nsmul_onCurve`). Scaling
each of the three ⊥ conditions by `(2^(n−i+1)) •` is therefore an equivalence. `Accᵢ₋₁ = ±S`
becomes `P = ±(2 • T)`, one `x`-coordinate test because `x(P) = x(X)` iff `P = ±X` on the curve
(`x_eq_iff_eq_or_eq_neg`), and `S = −(2 • Accᵢ₋₁)` becomes `P + T = 𝒪`. That is
`weightedStep_eq_step`: one weighted position at weight `k` is the specification's step with both
sides scaled by `(2^k) •`, ⊥ for ⊥. An induction over the words with the invariant
`P = (2^|remaining|) • Acc` (`weightedFrom_eq_hashToPoint`) gives the main theorem.

The two batched paths are then shown to compute `weightedStep` on raw coordinates. The lockstep
lane matches its four branches against `ShortWeierstrass.add` (`laneStep_eq_weightedStep`). The
Jacobian step reparameterizes `X` as `T.x·Z² − h`, so that every `madd-2007-bl` denominator is a
power of `2·Z·h` (`affine_jacobianStep`).

## What is proved

The Rust is the `sinsemilla` crate at zcash/sinsemilla#9, head
`596e662ebf917edd3bfe0b0d0f1a5d984969e393`, as carried by the fork `zingolabs/sinsemilla` at
`09b92cf4e87bb3f5a803053d457f6604d1a1dce5` (branch `perf/hash-many-vartime`), which adds four
commits on that head. Ironwood is `daira/ironwood` at `86e3c7026db8c9af27ca731e6b5c7f2d8fc7f0fc`.

| File | Statement | Rust it models |
|---|---|---|
| `SinsemillaProofs/Weighted.lean` | `step_eq_of_onCurve`: Theorem 5.4.4 as a computation (`step` = `2 • acc + S`, ⊥ at `acc = ±S` or `2 • acc + S = 𝒪`) | — (specification side) |
| `SinsemillaProofs/Weighted.lean` | `weightedStep_eq_step`: one weighted position at weight `k` = the spec step rescaled by `(2^k) •`, ⊥ ↔ ⊥ | loop body of `TableDomain::hash_to_point` (`src/table.rs`) |
| `SinsemillaProofs/Weighted.lean` | `weightedHashToPoint_eq_hashToPoint`: weighted evaluator = `hashToPoint` (⊥ included), for on-curve `Q` and generators | `TableDomain::hash_to_point`, at the group level |
| `SinsemillaProofs/Weighted.lean` | `weightedHashToPoint_eq_getLeft?_hashToPointB`: the join with Ironwood's break-data refinement `hashToPointB` | — |
| `SinsemillaProofs/Weighted.lean` | `weightedHashToPoint_cons`: position 0 alone | `FIRST_STEPS` rows (`None` = position-0 ⊥) |
| `SinsemillaProofs/Lockstep.lean` | `laneStep_eq_weightedStep`: one lane (`x` test, chord, tangent when `lane = addend`, ⊥ when `lane = −addend`) = `weightedStep` | `add_in_lockstep` per lane |
| `SinsemillaProofs/Lockstep.lean` | `batchInverses_eq`: the fused Montgomery trick gives each `d⁻¹` | `add_in_lockstep`'s two passes |
| `SinsemillaProofs/Jacobian.lean` | `jacobianStep_Z_ne_zero`, `affine_jacobianStep`: a returned Jacobian step keeps `Z ≠ 0` and is `weightedStep` on the affine view | `Jacobian::step` (below `LOCKSTEP_LANES`) |
| `SinsemillaProofs/Jacobian.lean` | `jacobianStep_none_of_weightedStep_none`, `jacobianStep_eq_none_iff`: every ⊥ is handed back (`None` reruns the message through `hash_to_point`), and which steps are, for `Z ≠ 0` | `Jacobian::step` → `hash_to_point` fallback |

Both variable-time paths reduce to `weightedStep`, so `TableDomain::hash_many_vartime` is covered
through the main theorem. Not covered: `HashDomain::hash_many_vartime` (`src/lib.rs`) and
`hash_words` fall back to `accumulate`, the specification's own recurrence, for untabled domains,
`N = 0`, and `N` past `LONGEST_MESSAGE_WORDS`; that path is the specification, not the weighted
evaluator, and is not modeled.

## Checking the model against the Rust

Nothing here reads the Rust, so the one thing a reviewer must check by eye is that each Lean
definition is a transcription of the Rust branch structure. The table lists every test; the
arithmetic between tests is the same formula on both sides.

| Rust (`src/table.rs` unless noted) | Test | Lean |
|---|---|---|
| `TableDomain::hash_to_point`, loop body | `has_x_of(acc, doubled)` then `acc.is_identity()` after `acc += addend` | `weightedStep`: `P.x = (2 • T).x ∨ P + T = 0` |
| `TableDomain::hash_to_point`, start and addends | `starts[d][n−1]`, `generators[n−1−i][word]`, `generators[n−i][word]` | `weightedHashToPoint`: `(2^n) • Q`; `weightedFrom`: `T = (2^|ms|) • S m`, tested against `2 • T` |
| `add_in_lockstep`, forward pass | `x == doubled[j].x` → lane `None` | `laneStep`, first branch → `none` |
| | `x != addend.x` → denominator `addend.x − x` | second branch: chord `(addend.y − lane.y) / (addend.x − lane.x)` |
| | `y == addend.y` → denominator `2y`, slope `3x²·inverse` | third branch: tangent `3x² / 2y` |
| | otherwise → lane `None` | fourth branch → `none` |
| `add_in_lockstep`, both passes | `product *= denominator`; one `invert_vartime`; `inverse * product_before`, `inverse *= denominator` | `batchInverses.go`: descent, base case, return |
| `Jacobian::step` | `x == doubled.x * zz` → `None` | `jacobianStep`, first `if` |
| | `h == 0` where `h = addend.x * zz − x` → `None` | second `if` |
| | `madd-2007-bl`, `z₃ = (z + h)² − zz − hh` | the `some` branch |
| `TableDomain::hash_each_vartime` | accumulator `None` → rerun through `hash_to_point` | `jacobianStep_none_of_weightedStep_none`, `jacobianStep_eq_none_iff` |
| `first_steps` | `start_x == doubled.x \|\| sum.is_identity()` → entry `None` | `weightedHashToPoint_cons` |

The Rust docstrings name the theorem that covers each function, so the two can be read side by
side.

Each module's docstring states what it models, with references, and what it leaves out and why.
`SinsemillaProofs/Tests/Smoke.lean` runs the evaluators on concrete points (a generic message, a
constructed ⊥, and a doubling the Jacobian step hands back) as `#guard`s in a separate build
target, `SmokeCheck`.

## Trust discipline

The general theorems rest only on Lean's standard axioms, `propext` / `Classical.choice` /
`Quot.sound`. The results that go through the Pallas group order — `(2^k) •` is injective and
never lands on the identity because `q ∤ 2^k`, which needs `q` to be the order — additionally
inherit one compiler-trusted closed fact: CompElliptic's point-count witness
`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt`, a `native_decide` certificate reached through
Ironwood's `Zcash.Circuits.Point.addOrderOf_eq`. Nothing in this repository uses `native_decide`,
`sorry`, or `noncomputable`.

That split is checked at build time, not asserted in prose: `SinsemillaProofs/TrustBoundary.lean`
pins every exported theorem with Ironwood's `assert_axioms` (from `Zcash.Meta.AxiomCheck`), the
general ones at the standard tier and the order-dependent ones with `+native(...)` naming that one
witness. A theorem that reaches beyond its tier, or a certificate entering or leaving a cone,
fails the build. `SinsemillaProofs.lean` imports the census last, so building the library enforces
it.

The trusted base, in full:

1. Ironwood's spec-level definitions (`hashToPoint`, `step`, incomplete addition) as a faithful
   model of §5.4.1.9, and CompElliptic's Pallas group with its order witness `q_nsmul_Gpt`.
2. The correspondence between the Rust and these models. The models follow the Rust's branch
   structure on raw coordinates, but nothing here reads Rust; the crate's differential tests pin
   both sides against `hash_to_point` and the reference implementation.
3. The table contents: that `generators[w][j]` is `(2^w) • S(j)` and `starts[d][n−1]` is
   `(2^n) • Q` (tested in the crate against group hashing), together with `pasta_curves`' Jacobian
   arithmetic inside `hash_to_point` (`+=`, `has_x_of`'s `X = x·Z²`), the field arithmetic and
   `invert_vartime`, word packing and the `< 2^K` / length assertions, and the dispatch between
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

## License

Copyright 2026 the sinsemilla-proofs contributors.

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
