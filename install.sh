#!/usr/bin/env bash
# atp-checkers bootstrap script
#
# Installs elan (if missing), fetches the pre-built Mathlib cache, builds the
# linter, and runs a smoke test. Idempotent — safe to re-run.
#
# Usage:
#   ./install.sh              # full bootstrap
#   ./install.sh --no-cache   # skip `lake exe cache get` (forces local Mathlib build)
#   ./install.sh --no-tests   # skip running AtpLinterTest at the end

set -euo pipefail

SKIP_CACHE=0
SKIP_TESTS=0
for arg in "$@"; do
  case "$arg" in
    --no-cache) SKIP_CACHE=1 ;;
    --no-tests) SKIP_TESTS=1 ;;
    -h|--help)
      echo "Usage: $0 [--no-cache] [--no-tests]"
      exit 0
      ;;
    *) echo "Unknown arg: $arg" >&2; exit 1 ;;
  esac
done

say() { printf "\n\033[1;34m==> %s\033[0m\n" "$*"; }
ok()  { printf "\033[1;32mok:\033[0m %s\n" "$*"; }
warn(){ printf "\033[1;33mwarn:\033[0m %s\n" "$*"; }

cd "$(dirname "$0")"
ROOT="$(pwd)"

# --- Python sanity ---------------------------------------------------------
say "Checking Python"
if ! command -v python3 >/dev/null 2>&1; then
  echo "python3 not found on PATH" >&2; exit 1
fi
PYVER="$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
case "$PYVER" in
  3.10|3.11|3.12|3.13) ok "python3 $PYVER" ;;
  *) warn "python3 $PYVER detected; runner requires >= 3.10 — you may need a newer python" ;;
esac

# --- elan (Lean version manager) ------------------------------------------
say "Checking elan / Lean toolchain"
if ! command -v elan >/dev/null 2>&1; then
  say "Installing elan"
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  # shellcheck disable=SC1091
  [ -f "$HOME/.elan/env" ] && . "$HOME/.elan/env"
  export PATH="$HOME/.elan/bin:$PATH"
fi

# lean-toolchain pin forces elan to fetch the right toolchain on first `lake`
TOOLCHAIN="$(cat lean-toolchain)"
say "Ensuring toolchain $TOOLCHAIN is installed"
elan toolchain install "$TOOLCHAIN" >/dev/null
ok "toolchain ready"

# --- Mathlib cache --------------------------------------------------------
if [ "$SKIP_CACHE" -eq 0 ]; then
  say "Fetching pre-built Mathlib oleans (lake exe cache get)"
  if lake exe cache get 2>&1 | tail -5; then
    ok "cache fetched"
  else
    warn "cache fetch failed — falling back to local Mathlib build (slow: ~30 min)"
  fi
else
  warn "skipping cache fetch (--no-cache)"
fi

# --- Build ----------------------------------------------------------------
say "Building linter + dependencies (lake build)"
lake build
ok "build complete"

# --- Smoke test -----------------------------------------------------------
say "Running no-Mathlib smoke test (runner sanity check)"
SMOKE_OUT="$(mktemp -d)"
trap 'rm -rf "$SMOKE_OUT"' EXIT
if python3 -m runner datasets/examples/minimal_no_mathlib.jsonl \
      --workspace . --output "$SMOKE_OUT" --timeout 60 >/dev/null 2>&1; then
  ok "smoke test passed"
else
  warn "smoke test failed — inspect $SMOKE_OUT/logs/"
  trap - EXIT
  exit 1
fi

# --- Test suite -----------------------------------------------------------
if [ "$SKIP_TESTS" -eq 0 ]; then
  say "Building test library (lake build AtpLinterTest)"
  lake build AtpLinterTest
  ok "tests compile cleanly"
fi

say "atp-checkers is ready"
cat <<EOF

Next steps:
  - Lint a dataset:
      python3 -m runner <path/to/dataset.jsonl> -w . -o out/run1 --timeout 30 -j 10
  - Read the README for output format + options:
      less README.md
  - Inspect the 13 checkers at:
      src/AtpLinter/

EOF
