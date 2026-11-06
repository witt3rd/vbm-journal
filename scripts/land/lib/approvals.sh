#!/usr/bin/env bash
# Gate-edit approvals (docs/gate-edit-approvals.md). Sourced by bin/land-direct, never run.
#
# A removed or changed line in a gate-defining file is accepted ONLY on an exact diff-hash match against an approval already on the base branch.
# The approvals file (LAND_APPROVALS, default scripts/gate-edit-approvals.txt) holds one record per line:
#
#     FILE-SET | sha256 of the exact diff of that set | reason | YYYY-MM-DD
#
# FILE-SET is one plain path (a gate-edit approval, as always) or a CANONICAL set: plain paths sorted (C locale), unique, joined by commas, no spaces.
# PROTECTED SETS (LAND_PROTECTED_LIST, optional): a landing whose net diff touches ANY path of the repository's protected-paths list is refused unless an approval whose
# FILE-SET is exactly the touched paths and whose hash is the net diff over exactly those paths is on the base branch (ga_protected below); the same one-time rules apply.
#
# The hash is the sha256 of the CANONICAL DIFF of FILE: what `land-direct --print-gate-diff-hash FILE` prints (ga_canon below: fixed flags, no config, `index` lines dropped).
# The rules (each one has a negative self-test in tests/test_approvals.sh):
#   - approvals are read from the BASE branch, never from the change: a landing cannot approve itself;
#   - an approval lands ALONE: a commit that adds a record changes no other file, adds exactly ONE line and removes none, and so does the landing that holds it (the edit comes in a later landing);
#   - one-time: a landing whose diff of FILE hashes to a record on base must REMOVE that record in the same landing (the consumption); a record is never reusable;
#   - a record removed without being consumed is refused (flagged), unless it is stale (the window closed: tidying up) or withdrawn by an `Approval-Withdrawn: FILE <hash prefix>` trailer in a landing that changes nothing else (announced to the judge);
#   - stale (older than LAND_APPROVAL_DAYS) or future-dated records approve nothing; a malformed or self-referencing record added is refused.
# HONEST LIMIT: an agent with landing rights could write its own approval line. The control is that approvals are visible one-commit records the independent judge
# reads before the edit lands: the approval commit is announced to the judge BEFORE the edit commit, always.

# ga_canon DIR BASE HEAD FILE...: the canonical diff of the file(s) between two trees (stdout). Same flags and no repository or user configuration that changes diff output.
ga_canon() {
  git --literal-pathspecs -C "$1" -c core.quotepath=off -c diff.noprefix=false -c diff.mnemonicPrefix=false -c diff.renames=false -c diff.algorithm=myers -c diff.indentHeuristic=true -c diff.context=0 \
    -c diff.interHunkContext=0 -c core.abbrev=40 -c color.diff=false \
    diff --no-ext-diff --no-textconv --no-color --no-renames --text -U0 --inter-hunk-context=0 --src-prefix=a/ --dst-prefix=b/ "$2" "$3" -- "${@:4}" \
    | sed -E '/^index [0-9a-f]+\.\.[0-9a-f]+( [0-7]+)?$/d'
}
# ga_hash DIR BASE HEAD FILE...: the sha256 of the canonical diff; prints nothing and returns 1 when the file(s) do not differ.
ga_hash() { local c; c=$(ga_canon "$@"; echo x) || return 1; c=${c%x}; [ -n "$c" ] || return 1; printf '%s' "$c" | sha256sum | cut -d' ' -f1; }

ga_rec_re='^([A-Za-z0-9_@+.-][A-Za-z0-9_./@+,.-]*) \| ([0-9a-f]{64}) \| ([^|]|[^|][^|]*[^|]) \| ([0-9]{4}-[0-9]{2}-[0-9]{2})$'
# ga_valid_path P: a plain repository path: no leading dot-slash or slash, no empty or dot components.
ga_valid_path() { [[ "$1" =~ ^[A-Za-z0-9_@+.-][A-Za-z0-9_./@+.-]*$ ]] && [[ "/$1/" != *"/.git/"* ]] && [[ "/$1/" != *"/./"* ]] && [[ "/$1/" != *"/../"* ]] && [[ "$1" != */ ]] && [[ "$1" != *//* ]]; }
# ga_valid_key K: a canonical file-set key: valid plain paths, strictly sorted (C locale), joined by commas (one path is a set of one).
ga_valid_key() { local k=$1 p prev= kp=(); [[ "$k" != *, && "$k" != ,* ]] || return 1; IFS=, read -ra kp <<<"$k"; [ ${#kp[@]} -gt 0 ] || return 1
  for p in "${kp[@]}"; do ga_valid_path "$p" || return 1; [ -z "$prev" ] || [[ "$prev" < "$p" ]] || return 1; prev=$p; done; }
# ga_age_days DATE: whole days between that UTC date and today; returns 1 for a date that does not exist.
ga_age_days() { local t; t=$(date -u -d "$1 00:00:00" +%s 2>/dev/null) || return 1; echo $(( ( $(date -u +%s) - t ) / 86400 )); }
# ga_fresh DATE DAYS: 0 when the record is inside the window: not older than DAYS days, not dated later than tomorrow (an author's clock may lead by a day).
ga_fresh() { local a; a=$(ga_age_days "$1") || return 1; [ "$a" -ge -1 ] && [ "$a" -le "$2" ]; }
# ga_records: read an approvals file on stdin; print each valid record as one line `FILE|HASH|DATE|<the record as written>`; every other non-blank, non-comment line is printed to fd 3 (stderr when not open).
ga_records() {
  local line f h d
  while IFS= read -r line || [ -n "$line" ]; do
    line=${line%$'\r'}
    [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    if [[ "$line" =~ $ga_rec_re ]]; then f=${BASH_REMATCH[1]}; h=${BASH_REMATCH[2]}; d=${BASH_REMATCH[4]}   # (ga_valid_path runs its own match: take these first)
      if ga_valid_key "$f" && date -u -d "$d" +%s >/dev/null 2>&1; then printf '%s|%s|%s|%s\n' "$f" "$h" "$d" "$line"; continue; fi
    fi
    printf '%s\n' "$line" >&3
  done
}

# ga_early DIR COMMITS APPROVALS_PATH: the per-commit rule, before any rebase: a commit that adds an approval record changes no other file. Prints the refusal and returns 1.
ga_early() {
  local d=$1 commits=$2 p=$3 c others added ns
  for c in $commits; do
    added=$(git -C "$d" diff -U0 --no-renames "$c^" "$c" -- "$p" 2>/dev/null | sed -n 's/^+\([^+].*\)$/\1/p' | grep -vE '^[[:space:]]*(#.*)?$' || true)
    [ -n "$added" ] || continue
    others=$(git -C "$d" diff-tree --no-commit-id --name-only -r --no-renames "$c" | grep -vxF -- "$p" || true)
    echo "land-direct: APPROVAL COMMIT: announce to the judge before landing the edit, with the diff hash and the FULL edit diff (${c:0:12} adds a gate-edit approval to $p)"
    if [ -n "$others" ]; then
      echo "land-direct: commit ${c:0:12} adds a gate-edit approval to $p and changes other files ($(echo $others)): an approval lands ALONE, in its own commit and its own landing, and is announced to the judge BEFORE the edit it approves (docs/gate-edit-approvals.md)." >&2
      return 1
    fi
    ns=$(git -C "$d" diff --numstat --no-renames "$c^" "$c" -- "$p" | cut -f1,2)
    if [ "$ns" != "1"$'\t'"0" ]; then
      echo "land-direct: commit ${c:0:12} changes $p by $(tr '\t' '/' <<<"$ns") lines added/removed: an approval commit adds exactly ONE line (one record) and removes none, and changes no other file." >&2
      return 1
    fi
  done
  return 0
}

# ga_withdrawn FILE HASH TRAILERS: 0 when a trailer line `FILE PREFIX` names this record (PREFIX: 12 or more leading hex digits of the hash).
ga_withdrawn() { local tf th; while read -r tf th; do [ "$tf" = "$1" ] && [[ "$2" == "$th"* ]] && return 0; done <<<"$3"; return 1; }

# ---- protected sets (LAND_PROTECTED_LIST): a landing that touches the repository's protected-paths list needs a one-time approval of its exact net diff over exactly the touched paths.
# ga_entries: a protected-paths list on stdin: each valid entry on stdout (a leading `?` marker is dropped; a trailing `/` makes a directory, anything else is a shell pattern, `*` matches `/`), every other
# non-blank, non-comment line on fd 3 (stderr when not open). An entry is plain path characters and `*`; no `..`, no leading `/`.
ga_entries() {
  local line
  while IFS= read -r line || [ -n "$line" ]; do
    line=${line%$'\r'}; [[ "$line" =~ ^[[:space:]]*(#.*)?$ ]] && continue
    line=${line#"${line%%[![:space:]]*}"}; line=${line%"${line##*[![:space:]]}"}; line=${line#\?}
    if [[ "$line" =~ ^[A-Za-z0-9_@+.*-][A-Za-z0-9_./@+.*-]*$ && "/$line/" != *"/../"* && "$line" != *//* ]]; then printf '%s\n' "$line"; else printf '%s\n' "$line" >&3; fi
  done
}
# ga_prot_match PATH ENTRY...: 0 when PATH is under (or is) a directory entry, or matches a pattern entry.
ga_prot_match() { local f=$1 e d; shift; for e in "$@"; do
  if [[ "$e" == */ ]]; then d=${e%/}; [[ "$f" == $d || "$f" == $d/* ]] && return 0; else [[ "$f" == $e ]] && return 0; fi; done; return 1; }
# ga_protected_touched DIR LISTBASE DIFFBASE HEAD LIST EXTRA EXEMPT STATE: the paths of the net diff DIFFBASE..HEAD that the protected set covers, one per line on stdout. The set is the list on LISTBASE united
# with the list on HEAD (a change to the list cannot narrow it for its own landing), plus EXTRA (space separated entries the lander always protects: its configuration and hooks). EXEMPT paths (the approvals
# files) are judged by the approval rules, not by this one. FAILS CLOSED: no list on LISTBASE, an empty list or an entry that is not understood sets ga_ptfail (the reason) and prints nothing. Renames, mode changes,
# symlinks and submodules are plain paths of the diff (no rename detection: both sides of a move are listed). Always returns 0 and never sits in a `||` list, so under the judge's `set -e` any unexpected failure refuses the landing.
ga_protected_touched() {
  local d=$1 lb=$2 db=$3 hd=$4 list=$5 extra=$6 exempt=$7 st=$8 p x
  local -a E=() X=()
  ga_ptfail=
  if ! git -C "$d" cat-file -e "$lb:$list" 2>/dev/null; then ga_ptfail="the protected-paths list $list is not on $lb: an unreadable list protects nothing, so nothing lands (fail closed)"; return 0; fi
  git -C "$d" show "$lb:$list" | ga_entries >"$st/ga-pe-base" 3>"$st/ga-pe-junk"
  if [ -s "$st/ga-pe-junk" ]; then ga_ptfail="the protected-paths list $list on $lb has a line that is not an entry ($(sed -n 1p "$st/ga-pe-junk")): nothing lands (fail closed)"; return 0; fi
  if [ ! -s "$st/ga-pe-base" ]; then ga_ptfail="the protected-paths list $list on $lb has no entries: an empty list protects nothing, so nothing lands (fail closed)"; return 0; fi
  mapfile -t E <"$st/ga-pe-base"
  : > "$st/ga-pe-head"; if git -C "$d" cat-file -e "$hd:$list" 2>/dev/null; then git -C "$d" show "$hd:$list" | ga_entries >"$st/ga-pe-head" 3>/dev/null; fi
  mapfile -t X <"$st/ga-pe-head"; [ ${#X[@]} -eq 0 ] || E+=("${X[@]}")
  for x in $extra; do if ga_valid_path "${x%/}"; then E+=("$x"); fi; done
  git -C "$d" -c core.quotepath=off diff --name-only -z --no-renames "$db" "$hd" >"$st/ga-pe-changed"
  while IFS= read -r -d '' p; do
    case " $exempt " in *" $p "*) continue;; esac
    if ga_prot_match "$p" "${E[@]}"; then printf '%s\n' "$p"; fi
  done <"$st/ga-pe-changed"
}
# ga_protected WT BASE LIST EXTRA EXEMPT STATE USEDFILE: the rule. Touched paths T need an approval on BASE whose set is exactly T and whose hash is the net diff over T, consumed by this landing
# (USEDFILE lists `SET HASH` of the approvals this landing consumed, from ga_file_rules). Refuses through ga_refuse; returns 0.
ga_protected() {
  local wt=$1 base=$2 list=$3 extra=$4 exempt=$5 st=$6 used=$7 key h p bad=
  local -a T=()
  ga_protected_touched "$wt" "$base" "$base" HEAD "$list" "$extra" "$exempt" "$st" >"$st/ga-touched"
  if [ -n "$ga_ptfail" ]; then ga_refuse "$ga_ptfail"; return 0; fi
  mapfile -t T <"$st/ga-touched"
  if [ ${#T[@]} -eq 0 ]; then echo "land-direct: protected set (list $list): none touched"; return 0; fi
  for p in "${T[@]}"; do if ! ga_valid_path "$p"; then bad="$bad $p"; fi; done
  if [ -n "$bad" ]; then ga_refuse "protected path(s) that no approval can name (not a plain repository path):$bad: refused."; return 0; fi
  local -a HARD=() SOFT=(); local why; why=$(ga_reason "$wt" "$base")
  for p in "${T[@]}"; do if ga_hard "$p" $extra; then HARD+=("$p"); else SOFT+=("$p"); fi; done
  if [ ${#SOFT[@]} -gt 0 ]; then
    if [ -n "$why" ]; then echo "land-direct: protected path(s) landed by the Protected: trailer (${SOFT[*]}): $why"
    else ga_refuse "this landing touches protected path(s) (${SOFT[*]}) and no commit carries a 'Protected: <reason>' trailer: add one line saying why (no hash, no approval; the lander's own files and the protected list still need one)."; fi
  fi
  if [ ${#HARD[@]} -eq 0 ]; then return 0; fi
  T=("${HARD[@]}")
  key=$(printf '%s\n' "${T[@]}" | LC_ALL=C sort -u | paste -sd,); IFS=, read -ra T <<<"$key"
  h=$(ga_hash "$wt" "$base" HEAD "${T[@]}" || true)
  if [ -n "$h" ] && grep -qxF -- "$key $h" "$used"; then echo "land-direct: protected set APPROVED: $key (${h:0:12}); the approval is consumed by this landing"; return 0; fi
  ga_refuse "this landing touches the protected set ($key) and no approval for exactly that set and exactly this diff is on the base branch: refused. The approval is a record 'FILE-SET | sha256 | reason | YYYY-MM-DD' (FILE-SET = the touched paths, sorted, comma-joined), landed ALONE and announced to the judge BEFORE the change, and removed by the landing that uses it. Set: $key. Hash: ${h:-none} (land-direct --print-gate-diff-hash @protected)."
}

ga_refuse() { echo "land-direct: $*" >&2; ga_refused=1; }
# ga_reason WT BASE: the reason of the first `Protected: <reason>` trailer of the commits BASE..HEAD (empty when none). A protected path outside the lander's own files lands on this one conscious line, no hash.
ga_reason() { git -C "$1" log --format=%B "$2..HEAD" | tr -d '\r' | sed -nE 's/^Protected: +(.*[^ ].*)$/\1/p' | sed -n 1p; }
# ga_hard PATH EXTRA...: 0 when PATH is the lander's own: its vendored copy and entry script, any signing keys file, and EXTRA (its configuration, hooks directory and the protected-paths list). Only these still need an exact-hash approval.
ga_hard() { local f=$1; shift; ga_prot_match "$f" scripts/land/ scripts/land-direct '*.signers' "$@"; }
# ga_file_rules WT BASEREF AP DAYS STATE USEDOUT EXEMPT: the approval rules R1 to R3 for ONE approvals file AP (read from BASEREF; the landing's copy is only judged). Writes `SET HASH` of every approval the landing
# consumes to USEDOUT. EXEMPT: the approvals files (a record may not name one).
ga_file_rules() {
  local wt=$1 base=$2 ap=$3 days=$4 state=$5 usedout=$6 exempt=$7 f h d line changed others ns p any x
  local B=$state/ga-base.rec H=$state/ga-head.rec ADD=$state/ga-added.rec REM=$state/ga-removed.rec USED=$state/ga-used.rec JB=$state/ga-base.junk JH=$state/ga-head.junk
  local -A fhash=(); local -a kp=()
  : > "$USED"; : > "$usedout"
  if git -C "$wt" cat-file -e "HEAD:$ap" 2>/dev/null && [ "$(git -C "$wt" ls-tree HEAD -- "$ap" | cut -d' ' -f1)" != 100644 ]; then ga_refuse "$ap is not a regular, non-executable file: not landing."; fi
  { git -C "$wt" show "$base:$ap" 2>/dev/null || true; } | ga_records >"$B" 3>"$JB"
  { git -C "$wt" show "HEAD:$ap" 2>/dev/null || true; } | ga_records >"$H" 3>"$JH"
  changed=$(git -C "$wt" -c core.quotepath=off diff --name-only --no-renames "$base" HEAD)
  grep -vxFf "$B" "$H" > "$ADD" || true; grep -vxFf "$H" "$B" > "$REM" || true
  # a line the change adds that is not an approval record: refused (a malformed record must not pass for an approval)
  while IFS= read -r line; do [ -n "$line" ] || continue
    ga_refuse "$ap: a line that is not an approval record ('FILE-SET | sha256 | reason | YYYY-MM-DD'; the file may not be one of these either): $line"
  done < <(grep -vxFf "$JB" "$JH" || true)
  # R1: added records: alone, in the window, not about an approvals file
  if [ -s "$ADD" ]; then
    echo "land-direct: $(wc -l < "$ADD") approval record(s) added to $ap; the edit each approves lands later, in its own landing, and removes the record"
    ns=$(git -C "$wt" diff --numstat --no-renames "$base" HEAD -- "$ap" | cut -f1,2)
    [ "$ns" = "1"$'\t'"0" ] || ga_refuse "this landing adds an approval to $ap but changes it by $(tr '\t' '/' <<<"$ns") lines added/removed: an approval landing adds exactly ONE line (one record), removes none, and carries one approval only."
    others=$(grep -vxF -- "$ap" <<<"$changed" || true)
    [ -z "$others" ] || ga_refuse "this landing adds a gate-edit approval to $ap and changes other files ($(echo $others)): an approval lands ALONE (the same landing as an edit it approves is a self-approval); the edit comes after the judge has read the approval."
    while IFS='|' read -r f h d line; do
      IFS=, read -ra kp <<<"$f"; for p in "${kp[@]}"; do for x in $exempt; do [ "$p" != "$x" ] || ga_refuse "an approval may not name the approvals file itself: $line"; done; done
      ga_fresh "$d" "$days" || ga_refuse "an approval dated $d is outside the window (at most $days days old, not future-dated): $line"
    done < "$ADD"
  fi
  # R3: what the landing's net diff consumes: the base's records whose hash is the net diff of their file set
  while IFS='|' read -r f h d line; do
    [ -n "$f" ] || continue
    IFS=, read -ra kp <<<"$f"; any=0; for p in "${kp[@]}"; do ! grep -qxF -- "$p" <<<"$changed" || any=1; done; [ "$any" = 1 ] || continue
    [ -n "${fhash[$f]+x}" ] || fhash[$f]=$(ga_hash "$wt" "$base" HEAD "${kp[@]}" || true)
    [ "${fhash[$f]}" = "$h" ] || continue
    if ga_fresh "$d" "$days"; then
      printf '%s|%s|%s|%s\n' "$f" "$h" "$d" "$line" >> "$USED"; printf '%s %s\n' "$f" "$h" >> "$usedout"
      grep -qxF -- "$f|$h|$d|$line" "$REM" || { printf '%s|%s\n' "$ap" "$line" >> "$state/ga-autoconsume"; echo "land-direct: the approval for $f (${h:0:12}) is consumed by this landing: the lander deletes its line from $ap"; }
    else ga_refuse "the approval for $f (${h:0:12}, dated $d) is stale (older than $days days): it approves nothing; a new approval commit comes first."
    fi
  done < "$B"
  # R2: a record removed without being consumed is flagged (a stale one may be tidied away; a trailer `Approval-Withdrawn: FILE-SET <first 12+ hex of the hash>` in this landing's commits withdraws a fresh one)
  local wd; wd=$(git -C "$wt" log --format=%B "$base..HEAD" | tr -d '\r' | sed -nE 's/^Approval-Withdrawn: +([^ ]+) +([0-9a-f]{12,64}) *$/\1 \2/p')
  while IFS='|' read -r f h d line; do
    [ -n "$f" ] || continue
    grep -qxF -- "$f|$h|$d|$line" "$USED" && continue
    ga_fresh "$d" "$days" || continue
    if ga_withdrawn "$f" "$h" "$wd"; then   # withdrawn by a trailer: announced, and the landing carries nothing else
      others=$(grep -vxF -- "$ap" <<<"$changed" || true)
      [ -z "$others" ] || ga_refuse "the approval for $f (${h:0:12}) is withdrawn by trailer in a landing that also changes other files ($(echo $others)): a withdrawal lands ALONE."
      echo "land-direct: APPROVAL WITHDRAWN: announce to the judge: $f (${h:0:12}) is withdrawn by trailer without being used"; continue
    fi
    ga_refuse "the approval for $f (${h:0:12}) was removed without being consumed (its diff is not what this landing changes): an approval line is removed only by the landing that uses it, or once it is stale. FLAGGED."
  done < "$REM"
}

# ga_judge WT BASEREF APPROVALS_PATH DAYS APPEND_ONLY_GLOBS STATE_DIR [PROTECTED_LIST PROTECTED_APPROVALS_PATH PROTECTED_EXTRA]: the generic judge on the rebased tree WT against BASEREF. Prints the verdict; returns 0 (nothing refused) or 1 (refused: the reasons are on stderr).
# Writes $STATE_DIR/approved-gate-edits.txt: `SET HASH` of every approval this landing consumes (the hooks read it as $LAND_GATE_APPROVED_FILE).
# PROTECTED_LIST (a path, read from the base branch; empty: the rule is off) turns on the protected-set rule; its approvals live in PROTECTED_APPROVALS_PATH (default: APPROVALS_PATH).
ga_judge() {
  local wt=$1 base=$2 ap=$3 days=$4 globs=$5 state=$6 plist=${7:-} pap=${8:-} pextra=${9:-} f h g e ns del mode changed pused exempt=$3
  local U=$state/ga-used-ap.txt UP=$state/ga-used-pap.txt
  ga_refused=0; : > "$state/ga-autoconsume"
  [ -z "$plist" ] || [ -n "$pap" ] || pap=$ap
  [ -z "$pap" ] || [ "$pap" = "$ap" ] || exempt="$ap $pap"
  ga_file_rules "$wt" "$base" "$ap" "$days" "$state" "$U" "$exempt"; cp "$U" "$state/approved-gate-edits.txt"; pused=$U
  if [ -n "$pap" ] && [ "$pap" != "$ap" ]; then ga_file_rules "$wt" "$base" "$pap" "$days" "$state" "$UP" "$exempt"; cat "$UP" >> "$state/approved-gate-edits.txt"; pused=$UP; fi
  if [ -n "$plist" ]; then ga_protected "$wt" "$base" "$plist" "$pextra" "$exempt" "$state" "$pused"; fi
  changed=$(git -C "$wt" -c core.quotepath=off diff --name-only --no-renames "$base" HEAD)
  # append-only files: a removed or changed line (or a deleted file, a mode change) needs an approval that this landing consumes
  local -a gl=(); read -ra gl <<<"$globs"
  if [ ${#gl[@]} -gt 0 ]; then
    while IFS= read -r f; do [ -n "$f" ] || continue
      e=0; for g in "${gl[@]}"; do [[ "$f" == $g ]] && e=1; done; [ "$e" = 1 ] || continue
      git -C "$wt" cat-file -e "$base:$f" 2>/dev/null || continue                                  # a new file only gains
      ns=$(git -C "$wt" diff --numstat --no-renames "$base" HEAD -- "$f" | cut -f2); del=${ns:-0}; mode=
      git -C "$wt" cat-file -e "HEAD:$f" 2>/dev/null || del=gone
      [ "$(git -C "$wt" ls-tree "$base" -- "$f" | cut -d' ' -f1)" = "$(git -C "$wt" ls-tree HEAD -- "$f" 2>/dev/null | cut -d' ' -f1)" ] || mode=mode
      [ "$del" != 0 ] || [ -n "$mode" ] || continue
      h=$(ga_hash "$wt" "$base" HEAD "$f" || true)
      if [ -n "$h" ] && grep -qxF -- "$f $h" "$U"; then echo "land-direct: gate edit APPROVED: $f (${h:0:12}) removes or changes lines; the approval is consumed by this landing"
      elif [ -n "$(ga_reason "$wt" "$base")" ]; then echo "land-direct: gate edit by the Protected: trailer: $f removes or changes lines: $(ga_reason "$wt" "$base")"
      else
        ga_refuse "$f is a gate-defining file that may only GAIN lines (LAND_GATE_APPEND_ONLY) and this landing removes or changes some ($del removed${mode:+, mode changed}): refused unless an approval for exactly this diff is already on the base branch. The approval is a record in $ap, landed ALONE and announced to the judge BEFORE the edit; hash: $h (land-direct --print-gate-diff-hash $f)."
        git -C "$wt" diff -U0 --no-renames "$base" HEAD -- "$f" | grep -E '^-[^-]' | sed -n '1,6s/^/land-direct:   /p' >&2 || true
      fi
    done <<<"$changed"
  fi
  [ "$ga_refused" = 0 ]
}
# ga_judge_run ARGS...: ga_judge in a bash of its own with `set -e`, which a function called from `||` never has: any command that fails unexpectedly stops the judge, and the landing is refused (fail closed).
ga_judge_run() {
  bash -c 'set -eEuo pipefail; trap '"'"'echo "land-direct: the gate-edit judge failed unexpectedly (line $LINENO): refusing" >&2'"'"' ERR; . "$1"; shift; ga_judge "$@"' _ "${BASH_SOURCE[0]}" "$@"
}
