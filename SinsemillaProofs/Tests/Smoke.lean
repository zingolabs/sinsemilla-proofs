import SinsemillaProofs.Weighted
import SinsemillaProofs.Lockstep
import SinsemillaProofs.Jacobian

/-!
# Smoke checks on concrete points

Evaluations of the three evaluators on small messages over multiples of the Pallas generator
`G = (−1, 2)`, kept in the `SmokeCheck` target so they never enter the `SinsemillaProofs` import
graph. The theorems relate `laneStep` and `jacobianStep` to `weightedStep`, and `weightedStep` to
the specification; these checks run the definitions as written, and pin the two distinctions a
type-correct statement could still blur: that a constructed exceptional input is `⊥` on every
path, and that the Jacobian step hands back a doubling the specification does not treat as `⊥`.
Each check is a `#guard`, so a failure fails the build.
-/

namespace SinsemillaProofs.Tests.Smoke

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla

/-- The Pallas generator `(−1, 2)`. -/
def G : Point Fp := ⟨-1, 2⟩

/-- Generators `S m = [m + 2] G`: distinct multiples, none the identity for small `m`. -/
def S (m : ℕ) : Point Fp := (m + 2) • G

/-- The lockstep path on one lane: `laneStep` per word at the weights `weightedFrom` uses. -/
def laneChain : Point Fp → List ℕ → Option (Point Fp)
  | P, [] => some P
  | P, m :: ms =>
    let T := (2 ^ ms.length : ℕ) • S m
    (laneStep P T ((2 : ℕ) • T).x).bind fun acc => laneChain acc ms

/-- The Jacobian path: `jacobianStep` per word at the same weights. -/
def jacobianChain : JacobianPoint → List ℕ → Option JacobianPoint
  | p, [] => some p
  | p, m :: ms =>
    let T := (2 ^ ms.length : ℕ) • S m
    (jacobianStep p T ((2 : ℕ) • T)).bind fun acc => jacobianChain acc ms

/-! ## A generic message

Three words from `Q = [11] G`: defined, and the same point on every path. -/

def Q : Point Fp := (11 : ℕ) • G
def words : List ℕ := [0, 1, 2]
def start : Point Fp := (2 ^ words.length : ℕ) • Q

-- the weighted evaluator against the specification, and the result defined
#guard weightedHashToPoint S Q words = hashToPoint S Q words
#guard (hashToPoint S Q words).isSome
-- the lockstep lane from the weighted start
#guard laneChain start words = weightedHashToPoint S Q words
-- the Jacobian accumulator from `Z = 1`, normalised, with `Z ≠ 0` kept
#guard (jacobianChain ⟨start.x, start.y, 1⟩ words).map JacobianPoint.affine
  = weightedHashToPoint S Q words
#guard (jacobianChain ⟨start.x, start.y, 1⟩ words).map (fun p => decide (p.Z ≠ 0)) = some true
-- the fused batch inversion
#guard batchInverses [3, 5, 7] = [3⁻¹, 5⁻¹, 7⁻¹]

/-! ## An exceptional message

`Q = S 0` collides at position 0 (`acc = S m`, the specification's first `⊥` condition; rescaled,
`P₀ = [2]T₀`), so every path is `⊥`. -/

-- the specification and the weighted evaluator
#guard hashToPoint S (S 0) words = none
#guard weightedHashToPoint S (S 0) words = none
-- the lockstep lane and the Jacobian accumulator
#guard laneChain ((2 ^ words.length : ℕ) • S 0) words = none
#guard (jacobianChain ⟨((2 ^ words.length : ℕ) • S 0).x, ((2 ^ words.length : ℕ) • S 0).y, 1⟩
  words).isNone

/-! ## A doubling

One word from `Q = G`, where `S 0 = [2] G = [2] Q`: at weight `0` the accumulator `P = [2] Q`
equals the addend `T = S 0`. The specification and the lane evaluate it (`[4] G`); the Jacobian
step hands it back, which is the `none ⊋ ⊥` of `jacobianStep_eq_none_iff`. -/

#guard hashToPoint S G [0] = some ((4 : ℕ) • G)
#guard weightedHashToPoint S G [0] = some ((4 : ℕ) • G)
#guard laneChain ((2 : ℕ) • G) [0] = some ((4 : ℕ) • G)
#guard (jacobianChain ⟨((2 : ℕ) • G).x, ((2 : ℕ) • G).y, 1⟩ [0]).isNone

end SinsemillaProofs.Tests.Smoke
