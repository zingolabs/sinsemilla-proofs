-- This module serves as the root of the `SinsemillaProofs` library: its sole import root, so
-- `lake build SinsemillaProofs` is exactly this file's transitive closure. No module imports it —
-- it is a build entry point, not a re-export surface. The census in `TrustBoundary` is imported
-- last, so building the library also enforces the axiom bounds; the smoke checks under
-- `SinsemillaProofs/Tests/` are a separate target (`SmokeCheck`) and never enter this closure.
-- `scripts/check_build_coverage.sh` asserts in CI that every module file in the package is
-- reachable from some default target.

import SinsemillaProofs.Weighted
import SinsemillaProofs.Lockstep
import SinsemillaProofs.Jacobian
import SinsemillaProofs.TrustBoundary
