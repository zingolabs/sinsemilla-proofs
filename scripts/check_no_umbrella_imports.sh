#!/usr/bin/env bash
# Check that no Lean file imports the Mathlib umbrella modules.
#
# `import Mathlib` pulls in all of Mathlib, which peaks around 6.5 GB RSS per Lean process, and
# `import Mathlib.Tactic` transitively pulls a large slice of Mathlib's theory (roughly +1.6 s
# import-load time and +1.3 GB RSS per Lean process against the narrow tactic modules a file
# actually needs; Ironwood's measurements, ironwood#153). Nothing else fails when an umbrella
# creeps in — builds just quietly get slow again — so the rule is enforced here.
#
# The rule: no tracked `.lean` file may contain a bare `import Mathlib` or a bare
# `import Mathlib.Tactic` (with or without a trailing comment). Specific submodule imports such
# as `import Mathlib.Tactic.Ring` are fine. If an umbrella import is ever legitimately needed,
# extend this script with an explicit allowlist rather than deleting the check.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail
cd "$(dirname "$0")/.."

# One-or-more whitespace after `import` (not exactly one space), and optional
# `public`/`meta` modifiers, so spacing variants and module-system prefixes
# cannot slip a banned umbrella past the anchor.
violations=$(git ls-files '*.lean' | xargs grep -nE '^(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+Mathlib(\.Tactic)?([[:space:]]|$)' || true)

if [ -n "$violations" ]; then
  echo "::error::bare 'import Mathlib' / 'import Mathlib.Tactic' umbrella imports are not allowed; import the specific Mathlib modules instead (see scripts/check_no_umbrella_imports.sh):"
  echo "$violations"
  exit 1
fi
echo "umbrella imports: none."
