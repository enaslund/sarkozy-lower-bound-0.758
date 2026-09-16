# Source this file in Bash to use the project-local Lean toolchain.
export ELAN_HOME="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$(dirname -- "$ELAN_HOME")/.cache/mathlib"

