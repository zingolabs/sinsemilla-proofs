import SinsemillaProofs.Weighted
import SinsemillaProofs.Lockstep
import SinsemillaProofs.Jacobian
import Zcash.Meta.AxiomCheck

/-!
# Trust boundary, build-checked

The census that makes this repository's trust claims build-time checks rather than prose. Each
`assert_axioms` below pins an *upper bound* on a theorem's trusted base, so a change that widens
it — a `sorry` reached through some dependency, an unexpected axiom, or `native_decide` where none
was permitted — fails this file rather than passing silently. The command is Ironwood's
(`Zcash.Meta.AxiomCheck`), usable here because the package already depends on `Zcash`. It accepts
a downstream package without change: its compiled-body sweep classifies modules by name root, and
this repository owns no `@[implemented_by]` or `@[extern]` declaration.

Two tiers appear. General theorems rest only on `propext` / `Classical.choice` / `Quot.sound`.
The results that go through the Pallas group order additionally inherit one compiler-trusted
closed fact, CompElliptic's point-count witness `Pallas.q_nsmul_Gpt`, through
`Zcash.Circuits.Point.addOrderOf_eq`: `(2^k) •` is injective and never lands on `𝒪` because
`q ∤ 2^k`, which needs `q` to be the group order. Each such entry names that owner in
`+native(...)`, and the owner list must be exact, so a certificate entering or leaving a cone fails
the build with the list to write. Nothing in this repository uses `native_decide` itself.

`assert_axioms` walks a declaration's transitive dependencies, so coverage flows downwards only:
every exported theorem is pinned here directly rather than left to inherit coverage from some
dependent. `SinsemillaProofs.lean` imports this module last, so building the library enforces the
census.
-/

/-! ## Weighted evaluator

Theorem 5.4.4 as a computation needs no order fact; everything stated at a weight does. -/

-- Weighted.lean: the specification's step, resolved on-curve
assert_axioms SinsemillaProofs.step_eq_of_onCurve

-- Weighted.lean: the per-position theorem, the main theorem, and the join with `hashToPointB`
assert_axioms SinsemillaProofs.weightedStep_eq_step +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms SinsemillaProofs.weightedHashToPoint_eq_hashToPoint +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms SinsemillaProofs.weightedHashToPoint_eq_getLeft?_hashToPointB +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- Weighted.lean: the `FIRST_STEPS` row, a definitional unfolding
assert_axioms SinsemillaProofs.weightedHashToPoint_cons

/-! ## Lockstep lanes -/

-- Lockstep.lean: the lane reaches the order fact through `two_pow_nsmul_onCurve`
assert_axioms SinsemillaProofs.laneStep_eq_weightedStep +native(
  CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms SinsemillaProofs.batchInverses_eq

/-! ## Jacobian accumulators -/

-- Jacobian.lean: field identities only, no order fact
assert_axioms SinsemillaProofs.jacobianStep_Z_ne_zero
assert_axioms SinsemillaProofs.affine_jacobianStep
assert_axioms SinsemillaProofs.jacobianStep_none_of_weightedStep_none
assert_axioms SinsemillaProofs.jacobianStep_eq_none_iff
