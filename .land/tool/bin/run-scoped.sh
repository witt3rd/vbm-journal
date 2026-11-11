#!/usr/bin/env bash
# run-scoped.sh NAME MAXSEC CMD...: run a long runner (the list: scripts/long-runners.txt) in a transient systemd user scope with
# RuntimeMaxSec=MAXSEC, so an aborted run (the caller killed, a SIGKILL included, a terminal gone) cannot leave the runner or its children orphaned:
# the scope is stopped on exit, on a signal and, if even this wrapper dies, by RuntimeMaxSec. Exit status = the command's (124 on the bound).
# Standing rule: nobody kills by a derived pid or a pattern; this helper stops only its own scope, by the unit name it chose.
# Without a usable systemd user manager (hosted CI) it falls back to setsid + timeout --kill-after with a trap that stops its own group: the same three guarantees (bound, abort, reaped on exit).
# `no-build-guard --lint` (Tier 1) fails any script that runs a listed runner without going through here, and runs this helper with a marker present to see it refuse. It ships with the tool: it is found BESIDE the guard.
set -uo pipefail
# The heavy-host guard (docs/no-build-host.md): on a host with a no-build marker nothing starts (exit 2). It runs first, and again in the scoped side (--exec-argfile) just before the command is exec'd. Missing guard = refused.
d=$(dirname "$(readlink -f "$0")"); nbg=$d/no-build-guard; [ -x "$nbg" ] || nbg=
[ -n "$nbg" ] || { echo "run-scoped: REFUSED: no-build-guard is not installed next to this helper" >&2; exit 2; }
"$nbg" || exit 2
# internal: the scoped side. The arguments travel in a NUL-delimited file, because systemd-run's treatment of $ in its own arguments differs between versions.
if [ "${1:-}" = --exec-argfile ]; then mapfile -d '' -t cmd < "$2"; rm -f "$2"; exec "${cmd[@]}"; fi
[ $# -ge 3 ] || { echo "usage: run-scoped.sh NAME MAXSEC CMD..." >&2; exit 2; }
name=$1; max=$2; shift 2
case $name in *[!A-Za-z0-9_-]*|'') echo "run-scoped: bad NAME: $name" >&2; exit 2;; esac
case $max in *[!0-9]*|'') echo "run-scoped: bad MAXSEC: $max" >&2; exit 2;; esac
usable=1
command -v systemd-run >/dev/null 2>&1 || usable=0
systemctl --user is-system-running >/dev/null 2>&1 || [ "$(systemctl --user is-system-running 2>/dev/null)" = degraded ] || usable=0
[ -z "${RUN_SCOPED_NO_SYSTEMD:-}" ] || usable=0   # test hook: force the fallback
if [ $usable = 0 ]; then
  # Fallback (no systemd user manager: hosted CI, containers): the same guarantees by process group. The command runs in its own session (setsid: pgid = the pid held here), under
  # timeout --kill-after for the bound, and a trap stops that group on exit or a signal. Nothing is signalled by pattern or by a derived pid.
  trap 'kill -TERM -- "-${gpid:-0}" 2>/dev/null || true' EXIT
  trap 'kill -TERM -- "-${gpid:-0}" 2>/dev/null || true; exit 143' INT TERM HUP
  setsid timeout --kill-after=10 "$max" "$@" <&0 &
  gpid=$!
  wait $gpid; rc=$?
  trap - EXIT; kill -TERM -- "-$gpid" 2>/dev/null || true   # stragglers of a command that has exited
  exit $rc
fi
unit="vbm-$name-$$-$RANDOM"
stop() { systemctl --user stop "$unit.scope" >/dev/null 2>&1 || true; }
trap 'stop; rm -f "${argf:-}"' EXIT
trap 'stop; exit 143' INT TERM HUP
argf=$(mktemp); printf '%s\0' "$@" > "$argf"
systemd-run --user --scope --quiet --collect --unit="$unit" -p RuntimeMaxSec="$max" -- "$(readlink -f "$0")" --exec-argfile "$argf" <&0 &
wait $!; rc=$?
# a scope that hit RuntimeMaxSec is killed by SIGTERM: report it the way timeout does
[ $rc -ne 143 ] || rc=124
exit $rc
