#!/usr/bin/env bash
# The freeze marker: a file with `key=value` lines that stops every landing except a fix or a revert. Sourced, never run.
#   owner=<who>  reason=<one line>  since=<epoch>  expires=<epoch>
# A freeze has a named owner, an expiry and a clearing action: `land-direct --thaw`, the expiry passing, or a fix landing. An expired marker is not in force.
freeze_field() { sed -n "s/^$2=//p" "$1" 2>/dev/null | sed -n 1p; }
freeze_active() {   # freeze_active FILE: 0 while the marker exists and has not expired; an expired or unreadable-expiry marker is removed only if expired
  [ -e "$1" ] || return 1
  local e; e=$(freeze_field "$1" expires)
  if [[ "$e" =~ ^[0-9]+$ ]] && [ "$e" -le "$(date +%s)" ]; then rm -f "$1"; return 1; fi
  return 0   # no readable expiry: in force (fail closed), `--thaw` clears it
}
freeze_describe() { echo "owner $(freeze_field "$1" owner), expires $(date -u -d "@$(freeze_field "$1" expires)" +%FT%TZ 2>/dev/null || echo '?'): $(freeze_field "$1" reason)"; }
