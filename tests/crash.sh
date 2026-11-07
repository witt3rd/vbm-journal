#!/usr/bin/env bash
# The real crash test: a writer appends durable, signed records in a loop and is killed (SIGKILL) in the middle of one; the journal is then recovered
# and must hold the acknowledged records, in order, signed. Run from tier1.sh after the build.
set -euo pipefail
cd "$(dirname "$0")/.."
bin=.lake/build/bin/vbm-journal-test
dir=$(mktemp -d "$PWD/.lake/crash.XXXXXX")   # on the repository's disk, where fsync is real
trap 'rm -rf "$dir"' EXIT
for round in 1 2 3; do
  rm -f "$dir"/j "$dir"/j.sig "$dir"/j.lock
  "$bin" writer "$dir/j" > "$dir/acks" &
  pid=$!
  sleep 0.$((round * 2))
  kill -9 "$pid"
  wait "$pid" 2>/dev/null || true
  "$bin" verify "$dir/j" "$dir/acks"
done
