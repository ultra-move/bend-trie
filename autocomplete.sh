#!/bin/bash
# Build once, then run with one-key-at-a-time input.
cd "$(dirname "$0")"
[ autocomplete -nt autocomplete.bend ] || ~/.bend/bin/bend autocomplete.bend -o autocomplete || exit 1
ulimit -s unlimited
if [ -t 0 ]; then
  trap 'stty sane' EXIT
  stty -icanon -echo min 1
fi
./autocomplete
