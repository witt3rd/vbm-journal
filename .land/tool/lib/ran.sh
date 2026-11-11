# Sourced library: ran-evidence for the self-tests (docs/ran-evidence.md). A check that treats "the command failed" or "no output" as success passes when the thing
# under test never ran (a guard refused `lake`, a tool was missing, a script exited early). The class fix: every test script counts the cases it really executed and ends with ONE line
#     ran: NAME: N cases              (N > 0; bin/ran-evidence is the reader: the runners fail a script or gate that does not print it)
# and a refusal, a skip or an exit by a guard is a FAIL, never a pass.
#   ran_case            count one executed case (a check that was evaluated and held). File-backed ($RAN_LOG), so cases in subshells and background jobs count.
#   ran_done NAME       print the evidence line; fails (exit 1) when no case ran.
#   must_fail NAME CMD...   a negative self-test: CMD has to FAIL, for a reason it says (output not empty), and NOT because it was refused or never ran: exit 126 or 127 (not executable,
#                       not found), 124 (timeout), or a heavy-tool guard message ("heavy:", "heavy-guard") is a FAIL of the self-test. A passing must_fail counts one case.
#                       $MUST_FAIL_ERR holds what it said, for a caller that checks the reason.
#                       MUST_FAIL_PREFIX (default empty) is run in front of CMD (a function or command, e.g. `quiet`).
# one counter per script process: a nested script (a test that runs another) sources this again and gets its own, never the parent's
if [ "${RAN_OWNER:-}" != "$$" ]; then RAN_OWNER=$$; RAN_LOG=${TMPDIR:-/tmp}/ran-cases.$$.log; : > "$RAN_LOG"; fi
export RAN_OWNER RAN_LOG
ran_case() { echo . >> "$RAN_LOG"; }
ran_count() { if [ -f "$RAN_LOG" ]; then wc -l < "$RAN_LOG" | tr -d ' '; else echo 0; fi; }   # wc, not grep -c: no pipe
ran_done() {  # ran_done NAME
  local n; n=$(ran_count)
  [ "$n" -gt 0 ] || { echo "ran-evidence: $1: no case ran (a script that ran nothing is not a pass)" >&2; exit 1; }
  rm -f "$RAN_LOG"; echo "ran: $1: $n cases"
}
must_fail() {  # must_fail NAME CMD...
  local n=$1 e rc=0; shift
  e=$(mktemp "${TMPDIR:-/tmp}/neg.XXXXXX")
  # shellcheck disable=SC2086
  ${MUST_FAIL_PREFIX:-} "$@" >"$e" 2>&1 || rc=$?   # stdout and stderr together: a failing command may say why on either
  if [ "$rc" = 0 ]; then echo "self-test: $n did not fail (the check cannot fail)" >&2; rm -f "$e"; exit 1; fi
  case $rc in 124|126|127) echo "self-test: $n failed with exit $rc: the command was refused, missing or timed out, so the check never ran: $(head -c 300 "$e")" >&2; rm -f "$e"; exit 1;; esac
  if grep -qE '(^|[^A-Za-z])heavy(-guard)?:' "$e"; then echo "self-test: $n was refused by a heavy-tool guard, so the check never ran: $(head -c 300 "$e")" >&2; rm -f "$e"; exit 1; fi
  [ -s "$e" ] || { echo "self-test: $n failed without saying why" >&2; rm -f "$e"; exit 1; }
  MUST_FAIL_ERR=$(head -c 4000 "$e"); rm -f "$e"; ran_case   # MUST_FAIL_ERR: what the failing command said (a caller may check the reason)
}
