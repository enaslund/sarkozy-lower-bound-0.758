#!/usr/bin/env bash
set -euo pipefail

# Run in the project root using the caller's configured Lean environment.
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Finish the large certificate targets one at a time before the full build.
lake build Sarkozy.Odd437MomentData
lake build Sarkozy.OddOrder215
lake build Sarkozy.OddOrder437
lake build Sarkozy.Odd215Moment
lake build Sarkozy.Odd215Certificate
lake build Sarkozy.Odd437Moment
lake build Sarkozy.Odd437WidthHistogram
lake build
lake env lean Check.lean
