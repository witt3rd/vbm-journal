#!/usr/bin/env bash
# The per-repository configuration (default $LAND_CONF_FILE, lib/paths.sh), read by bin/land-direct. Sourced, never run.
#
# The file is DATA, not code: one `LAND_KEY=value` per line, `#` starts a comment line, a value may be wrapped in one pair of single or double
# quotes, nothing is ever expanded or executed while reading it, and an unknown key is an error (a typo must not silently turn a gate off; a key this
# tool has retired is unknown too, so a land.conf that still names one is refused by name and line instead of being read as if the setting still worked).
# The values that name commands (LAND_GATES_CMD, LAND_TEST_CMD, ...) are run later, by the lander, with `bash -c` inside the scratch worktree.
#
# The keys and their defaults are the stable interface of this tool (README, "Configuration"): conf_defaults sets them, conf_parse reads a file.
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/paths.sh"   # every consumer path, defined once (lib/paths.sh)

land_conf_keys="LAND_BASE LAND_REMOTE LAND_GATES_CMD LAND_TEST_CMD LAND_REGEN_CMD LAND_GEN_CMD LAND_GENERATED_LIST LAND_REQUIRE_TRAILERS
 LAND_CONVENTIONAL LAND_COMMIT_TYPES LAND_PROTECTED LAND_HOOKS_DIR LAND_LOCALE LAND_FAIL_PATTERN LAND_ATTEMPTS LAND_DEADLINE LAND_TIER1_TIMEOUT
 LAND_STEP_TIMEOUT LAND_GIT_TIMEOUT"

# The keys of .land/lean.conf (docs/lean-gates.md): the same grammar and the same parser as land.conf, its own keys (one file per tool, as rustfmt.toml and clippy.toml are).
lean_conf_keys="LAND_LEAN_AXIOM_IMPORTS LAND_LEAN_AXIOM_ROOTS"
lean_conf_defaults() { LAND_LEAN_AXIOM_IMPORTS=; LAND_LEAN_AXIOM_ROOTS=; }   # the modules to import, and the module roots whose constants are audited (space separated)

conf_defaults() {
  LAND_BASE=main; LAND_REMOTE=origin            # the branch landed on, and the remote that holds it
  LAND_GATES_CMD=; LAND_TEST_CMD=               # Tier 1 = the gates command, then the test command, on the rebased combination (at least one is required)
  LAND_REGEN_CMD=; LAND_GEN_CMD=                # regenerate generated files: after a conflict in them / always after the rebase
  LAND_GENERATED_LIST=                          # path (in the repository) of a file listing generated paths, one per line, `#` comments
  LAND_REQUIRE_TRAILERS=                        # trailer names every commit must carry, space separated (e.g. Task-ID)
  LAND_CONVENTIONAL=1                           # require `type(scope): summary` (or git's own `Revert "..."`)
  LAND_COMMIT_TYPES="feat fix docs chore refactor test perf build ci style revert"
  LAND_PROTECTED=                               # shell patterns (* matches /): the gate-defining set
  LAND_HOOKS_DIR=$LAND_HOOKS_DEFAULT            # repository-owned hooks (README, "Hooks")
  LAND_LOCALE=C                                 # pinned for collation, glob and sort order
  LAND_TIER1_TIMEOUT=1800; LAND_STEP_TIMEOUT=600; LAND_GIT_TIMEOUT=180   # seconds
  LAND_FAIL_PATTERN='^(FAIL|FAILED)([ :]|$)'      # an extended regular expression: the lines of Tier 1's output that name a failure. A landing may pass a Tier 1 that fails ONLY with failures the bare base already has (inherited red)
  LAND_ATTEMPTS=30; LAND_DEADLINE=900           # a landing re-validates when the base moves under it: at most this many attempts, none started after this many seconds (then exit 16)
}

# conf_parse NAME [KEYS]: read the file's text from stdin; NAME is only used in messages; KEYS is the list of keys the file may set (default: land.conf's). Returns 2 (with a message) on anything it does not understand.
conf_parse() {
  local name=$1 keys=${2:-$land_conf_keys} line n=0 k v
  while IFS= read -r line || [ -n "$line" ]; do
    n=$((n + 1)); line=${line%$'\r'}
    [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    if ! [[ "$line" =~ ^[[:space:]]*(LAND_[A-Z0-9_]+)=(.*)$ ]]; then echo "$name:$n: not a LAND_KEY=value line: $line" >&2; return 2; fi
    k=${BASH_REMATCH[1]}; v=${BASH_REMATCH[2]}
    case " $(echo $keys) " in *" $k "*) ;; *) echo "$name:$n: unknown key $k (a typo would silently turn a gate off)" >&2; return 2;; esac
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
  [[ "$LAND_REQUIRE_TRAILERS" =~ ^[A-Za-z0-9\ -]*$ ]] || b "LAND_REQUIRE_TRAILERS: trailer names are letters, digits and - separated by spaces"
  [ -n "$LAND_GATES_CMD$LAND_TEST_CMD" ] || b "neither LAND_GATES_CMD nor LAND_TEST_CMD is set: there is no Tier 1, so nothing could gate a landing"
  [ -z "$bad" ] || { echo "land.conf: $bad" >&2; return 2; }
}

# lean_conf_validate: the values of .land/lean.conf are module names, never anything that could be expanded or run. Returns 2 with a message otherwise.
lean_conf_validate() {
  local k
  for k in LAND_LEAN_AXIOM_IMPORTS LAND_LEAN_AXIOM_ROOTS; do
    [[ "${!k}" =~ ^[A-Za-z0-9_.]+( [A-Za-z0-9_.]+)*$ ]] || [ -z "${!k}" ] || { echo "lean.conf: $k holds module names only, separated by spaces (is '${!k}')" >&2; return 2; }
  done
}
