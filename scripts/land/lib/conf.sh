#!/usr/bin/env bash
# The per-repository configuration (default scripts/land.conf), read by bin/land-direct. Sourced, never run.
#
# The file is DATA, not code: one `LAND_KEY=value` per line, `#` starts a comment line, a value may be wrapped in one pair of single or double
# quotes, nothing is ever expanded or executed while reading it, and an unknown key is an error (a typo must not silently turn a gate off).
# The values that name commands (LAND_GATES_CMD, LAND_TEST_CMD, ...) are run later, by the lander, with `bash -c` inside the scratch worktree.
#
# The keys and their defaults are the stable interface of this tool (README, "Configuration"): conf_defaults sets them, conf_parse reads a file.
land_conf_keys="LAND_BASE LAND_REMOTE LAND_CI_WORKFLOW LAND_TIER1_JOB LAND_RED_MODE LAND_RED_WAIT LAND_GATES_CMD LAND_TEST_CMD LAND_REGEN_CMD LAND_GEN_CMD
 LAND_GENERATED_LIST LAND_PROD_PATHS LAND_BUDGET_LINES LAND_REQUIRE_TRAILERS LAND_CONVENTIONAL LAND_COMMIT_TYPES LAND_PROTECTED LAND_FIX_PATHS
 LAND_APPROVALS LAND_APPROVAL_DAYS LAND_PROTECTED_LIST LAND_PROTECTED_APPROVALS LAND_GATE_APPEND_ONLY LAND_KNOWN_FLAKY LAND_FLAKY_RERUN_WAIT LAND_TIER2_JOB LAND_HOOKS_DIR LAND_AUTO_UPDATE LAND_LOCALE LAND_FAIL_PATTERN LAND_ATTEMPTS LAND_DEADLINE LAND_LOCK_WAIT LAND_TIER1_TIMEOUT LAND_STEP_TIMEOUT LAND_GIT_TIMEOUT"

conf_defaults() {
  LAND_BASE=main; LAND_REMOTE=origin            # the branch landed on, and the remote that holds it
  LAND_GATES_CMD=; LAND_TEST_CMD=               # Tier 1 = the gates command, then the test command, on the rebased combination (at least one is required)
  LAND_REGEN_CMD=; LAND_GEN_CMD=                # regenerate generated files: after a conflict in them / always after the rebase
  LAND_GENERATED_LIST=                          # path (in the repository) of a file listing generated paths, one per line, `#` comments
  LAND_PROD_PATHS=; LAND_BUDGET_LINES=           # LEGACY: the size budget is gone (read and ignored)
  LAND_REQUIRE_TRAILERS=                        # trailer names every commit must carry, space separated (e.g. Task-ID)
  LAND_CONVENTIONAL=1                           # require `type(scope): summary` (or git's own `Revert "..."`)
  LAND_COMMIT_TYPES="feat fix docs chore refactor test perf build ci style revert"
  LAND_PROTECTED=; LAND_FIX_PATHS=              # shell patterns (* matches /): the protected set; the only paths a fix may touch to pass a freeze
  LAND_APPROVALS=; LAND_APPROVAL_DAYS=          # LEGACY: approvals are gone (read and ignored)
  LAND_PROTECTED_LIST=; LAND_PROTECTED_APPROVALS=   # LEGACY (read and ignored)
  LAND_GATE_APPEND_ONLY=                        # LEGACY (read and ignored)
  LAND_HOOKS_DIR=scripts/land.d                 # repository-owned hooks (README, "Hooks")
  LAND_AUTO_UPDATE=none                          # none | patch | minor: what the scheduled workflow may update by itself (land-update --auto); a major release never
  LAND_LOCALE=C                                 # pinned for collation, glob and sort order
  LAND_TIER1_TIMEOUT=1800; LAND_STEP_TIMEOUT=600; LAND_GIT_TIMEOUT=180   # seconds
  LAND_FAIL_PATTERN='^(FAIL|FAILED)([ :]|$)'      # an extended regular expression: the lines of Tier 1's output that name a failure. A landing may pass a Tier 1 that fails ONLY with failures the bare base already has (inherited red)
  LAND_ATTEMPTS=30; LAND_DEADLINE=900           # a landing re-validates when the base moves under it: at most this many attempts, none started after this many seconds (then exit 16)
  LAND_LOCK_WAIT=; LAND_CI_WORKFLOW=; LAND_TIER1_JOB=; LAND_RED_MODE=; LAND_RED_WAIT=; LAND_KNOWN_FLAKY=; LAND_FLAKY_RERUN_WAIT=; LAND_TIER2_JOB=   # LEGACY keys: read and ignored (land-direct names those a land.conf still sets, once): there is no lock since 0.5.0, and landing no longer reads CI (a red main is the watchdog's: bin/land-revert). Still known keys, so an old file keeps loading
}

# conf_parse NAME: read the file's text from stdin; NAME is only used in messages. Returns 2 (with a message) on anything it does not understand.
conf_parse() {
  local name=$1 line n=0 k v
  while IFS= read -r line || [ -n "$line" ]; do
    n=$((n + 1)); line=${line%$'\r'}
    [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    if ! [[ "$line" =~ ^[[:space:]]*(LAND_[A-Z0-9_]+)=(.*)$ ]]; then echo "$name:$n: not a LAND_KEY=value line: $line" >&2; return 2; fi
    k=${BASH_REMATCH[1]}; v=${BASH_REMATCH[2]}
    case " $(echo $land_conf_keys) " in *" $k "*) ;; *) echo "$name:$n: unknown key $k (a typo would silently turn a gate off)" >&2; return 2;; esac
    v=${v%"${v##*[![:space:]]}"}
    if [[ "$v" =~ ^\"(.*)\"$ ]] || [[ "$v" =~ ^\'(.*)\'$ ]]; then v=${BASH_REMATCH[1]}; fi
    printf -v "$k" '%s' "$v"
  done
  return 0
}

# conf_validate: the values the tool relies on must be well formed. Returns 2 with a message otherwise.
conf_validate() {
  local bad= k; b() { [ -n "$bad" ] || bad=$1; }
  [[ "$LAND_BASE" =~ ^[A-Za-z0-9._/-]+$ ]] || b "LAND_BASE is not a branch name ('$LAND_BASE')"
  [[ "$LAND_REMOTE" =~ ^[A-Za-z0-9._/-]+$ ]] || b "LAND_REMOTE is not a remote name ('$LAND_REMOTE')"
  for k in LAND_ATTEMPTS LAND_DEADLINE LAND_TIER1_TIMEOUT LAND_STEP_TIMEOUT LAND_GIT_TIMEOUT; do
    [[ "${!k}" =~ ^[0-9]+$ ]] || b "$k must be a whole number (is '${!k}')"
  done
  [ "$LAND_ATTEMPTS" -ge 1 ] 2>/dev/null || b "LAND_ATTEMPTS must be at least 1 (is '$LAND_ATTEMPTS')"
  case $LAND_AUTO_UPDATE in none|patch|minor) ;; *) b "LAND_AUTO_UPDATE must be none, patch or minor (is '$LAND_AUTO_UPDATE'; a major release is never automatic)";; esac
  [[ "$LAND_REQUIRE_TRAILERS" =~ ^[A-Za-z0-9\ -]*$ ]] || b "LAND_REQUIRE_TRAILERS: trailer names are letters, digits and - separated by spaces"
  [ -n "$LAND_GATES_CMD$LAND_TEST_CMD" ] || b "neither LAND_GATES_CMD nor LAND_TEST_CMD is set: there is no Tier 1, so nothing could gate a landing"
  [ -z "$bad" ] || { echo "land.conf: $bad" >&2; return 2; }
}
