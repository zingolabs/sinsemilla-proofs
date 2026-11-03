# sinsemilla-proofs

Lean proofs that the position-weighted Sinsemilla evaluators (zcash/sinsemilla#9's tables and
`TableDomain::hash_many_vartime`) compute the protocol specification's `SinsemillaHashToPoint`,
**including exactly which inputs give ⊥**. Stated against Ironwood's spec-level definitions
(`Zcash.Circuits.Specs.Sinsemilla.hashToPoint`), so a reviewer trusts no new model of Sinsemilla.

## Why

The specification computes `Accᵢ = (Accᵢ₋₁ ⸭ S(mᵢ)) ⸭ Accᵢ₋₁` with incomplete addition. The table
evaluators never form `Accᵢ`; they compute `Pᵢ = [2^(n−i)] Accᵢ` (one addition per word) and test
Theorem 5.4.4's conditions rescaled onto `P`. Equality with the spec in the generic case is checked
by differential tests on random inputs. The ⊥ cases cannot be: no real input reaches them (finding
one is a discrete-log relation), so a wrong ⊥ rule passes every test while the function silently
differs from the spec. Merkle roots feed consensus (Zebra anchors), so the bar is equality as
functions. That is what these proofs establish.

## What

| File | Statement | Rust it models |
|---|---|---|
| `Weighted.lean` | `step_eq_of_onCurve`: Theorem 5.4.4 as a computation (`step` = `[2]Acc + S`, ⊥ at `Acc = ±S` or `[2]Acc + S = 𝒪`) | — (spec side) |
| `Weighted.lean` | `weightedStep_eq_step`: one weighted position at weight `k` = spec step rescaled by `[2^k]`, ⊥ ↔ ⊥ | loop body of `TableDomain::hash_to_point` (#9) |
| `Weighted.lean` | `weightedHashToPoint_eq_hashToPoint`: weighted evaluator = `hashToPoint` (⊥ included), for on-curve `Q` and generators | `TableDomain::hash_to_point`, group level |
| `Weighted.lean` | `weightedHashToPoint_cons`: position 0 alone | `FIRST_STEPS` rows (`None` = position-0 ⊥) |
| `Lockstep.lean` | `laneStep_eq_weightedStep`: one lane (x test, chord, tangent when `lane = addend`, ⊥ when `lane = −addend`) = `weightedStep` | `add_in_lockstep` per lane |
| `Lockstep.lean` | `batchInverses_eq`: fused Montgomery trick gives each `d⁻¹` | `add_in_lockstep`'s two passes |
| `Jacobian.lean` | `jacStep_sound`: a returned Jacobian step = `weightedStep` on the affine view, `Z ≠ 0` kept | `Jacobian::step` (below `LOCKSTEP_LANES`) |
| `Jacobian.lean` | `jacStep_none_of_weightedStep_none`, `jacStep_eq_none_iff`: every ⊥ is handed back (`none` → whole message reruns through `hash_to_point`), and exactly which steps are | `Jacobian::step` → `hash_to_point` fallback |

Both vartime paths reduce to `weightedStep`, so `TableDomain::hash_many_vartime` is covered through
the main theorem. Not covered, by design: `HashDomain::hash_many_vartime` and `hash_words` fall back
to `accumulate` (the specification's own recurrence) for untabled domains, `N = 0`, and `N` past
`LONGEST_MESSAGE_WORDS`; that path is the spec, not the weighted evaluator, and is not modelled.

## Trust boundary

- Ironwood's spec definitions and CompElliptic's Pallas group order (`native_decide` witness)
- Not proved: Rust ↔ these models (differential tests), table contents `[2^w] S_j` and `[2^n] Q`
  (tested against hash-to-curve), `pasta_curves` Jacobian arithmetic inside `hash_to_point` (`+=`,
  `has_x_of`'s `X = x·Z²`), pasta field arithmetic and `invert_vartime`, word packing and the
  `< 2^K` / length asserts, dispatch between the lockstep and Jacobian paths

## Build

```sh
nix shell nixpkgs#elan -c lake exe cache get   # one-time: Mathlib artifacts
nix shell nixpkgs#elan -c lake build
```
