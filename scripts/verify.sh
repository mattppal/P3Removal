#!/usr/bin/env bash
# Rebuild the Palomar package and reject a proof that still contains sorry.
set -euo pipefail
export PATH="${HOME}/.elan/bin:${PATH}"

skip_build=0
if [ "${1:-}" = "--skip-build" ]; then
	skip_build=1
fi

if [ "$skip_build" -eq 0 ]; then
	lake build
fi

if grep -R -n -E --include='*.lean' '\b(sorry|admit)\b' P3Removal Solution.lean; then
	printf '%s\n' "proof modules still contain sorry or admit" >&2
	exit 1
fi

if grep -R -n -E --include='*.lean' '\b(sorry|admit)\b' Challenge.lean | grep -v 'sorry$'; then
	printf '%s\n' "Challenge.lean has a non-statement sorry" >&2
	exit 1
fi

ruby scripts/validate-formalization.rb
