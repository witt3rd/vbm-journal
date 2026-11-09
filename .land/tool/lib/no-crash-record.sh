#!/usr/bin/env bash
# Sourced library (vendored; never run): the landing's crash-record check and the quiet probe runner. Nothing a landing's tests do on purpose may leave a crash record (systemd-coredump, hence a journal entry and a desktop notice).
#  1. quiet CMD...: run CMD (a probe or mutant that is MEANT to crash) in a subshell with `ulimit -c 0` PLUS the dumpable-clear preload (prctl PR_SET_DUMPABLE 0); the status is CMD's (139 SIGSEGV, 134 SIGABRT).
#     ulimit -c 0 PLUS the dumpable-clear preload (PR_SET_DUMPABLE 0): ulimit alone still writes a crash-journal record (measured on a systemd-coredump host: exit 139, no core file, but a coredumpctl entry and a notice). A static binary ignores the preload.
#  2. nocrash_begin / nocrash_end wrap a whole run; nocrash_end FAILS (returns 1) only for a crash that BELONGS TO THIS LANDING, not for any other crash on the host (another lane's deliberate probe is not this landing's). A journal record is the landing's when ANY holds:
#     a. pid tree: the crashed process's parent (the record's PPid) is the landing's root process (the caller of nocrash_begin, or NOCRASH_ROOT_PID) or a live descendant of it (setsid or systemd-run children included: they keep their parent); the root is
#        identified by pid AND start time (a reused pid is not the root), and the parent must have been born before the crash; b. session: the record's session is the root's session; c. cgroup: its cgroup is the landing's own transient scope (a *.scope leaf
#        other than init/session scopes) or below it; d. its executable or command line is under the landing's private $TMPDIR (when set and not /tmp itself) or the repository.
#     Residual hole (accepted, stated plainly): an orphan that also setsid's, runs from a shared dir and leaves our scope is NOT caught.
#     Fails closed: no begin state (or a bad time) fails the check; an EMPTY id never matches (an empty cgroup or session is not "everything" and not "nothing": it is no match); with no usable scope id at all (no root pid) the broad old filter applies (any
#     executable under /tmp, $TMPDIR or the repository: stricter, never looser). Records come from `journalctl -o json` (NOCRASH_JOURNALCTL names the command; the self-test uses a shim); without it or jq the check is skipped with a note.
nocrash_so=""
nocrash_build() {  # the preload, built once per process tree into a private temp dir
  [ -n "$nocrash_so" ] && [ -f "$nocrash_so" ] && return 0
  local d; d=$(mktemp -d); nocrash_so="$d/quiet.so"
  printf '#include <sys/prctl.h>\n__attribute__((constructor)) static void q(void) { prctl(PR_SET_DUMPABLE, 0, 0, 0, 0); }\n' > "$d/q.c"
  "${CC:-cc}" -shared -fPIC -o "$nocrash_so" "$d/q.c" || { echo "no-crash-record: cannot build the quiet preload with ${CC:-cc}" >&2; return 1; }
}
quiet() { nocrash_build || return 1; ( ulimit -c 0; LD_PRELOAD="$nocrash_so${LD_PRELOAD:+:$LD_PRELOAD}" exec "$@" ); }
nocrash_stat() {  # nocrash_stat PID: "PPID SESSION STARTTICKS" from /proc (the comm field may hold spaces and parens)
  local s; s=$(cat "/proc/$1/stat" 2>/dev/null) || return 1; s=${s##*) }; set -- $s; echo "$2 $4 ${20}"
}
nocrash_begin() {
  nocrash_t0=$(date +%s); nocrash_root=${NOCRASH_ROOT_PID:-$$}; nocrash_tmp=${TMPDIR:-}; [ "$nocrash_tmp" != /tmp ] || nocrash_tmp=; nocrash_repo=$(pwd -P)
  local st; if st=$(nocrash_stat "$nocrash_root"); then set -- $st; nocrash_sid=$2; nocrash_rstart=$3; nocrash_cg=$(sed -n 's/^0:://p' "/proc/$nocrash_root/cgroup" 2>/dev/null); else nocrash_root=; nocrash_sid=; nocrash_rstart=; nocrash_cg=; fi
  command -v "${NOCRASH_JOURNALCTL:-journalctl}" >/dev/null 2>&1 && command -v jq >/dev/null 2>&1 || echo "no-crash-record: SKIPPED (journalctl or jq not available: no crash records to check)" >&2
}
nocrash_save() { printf '%s\n' "t0=$nocrash_t0" "root=$nocrash_root" "sid=$nocrash_sid" "rstart=$nocrash_rstart" "cg=$nocrash_cg" "tmp=$nocrash_tmp" "repo=$nocrash_repo" > "$1"; }
nocrash_load() {  # a fixed set of keys, never sourced or evaluated
  local k v; nocrash_t0=; nocrash_root=; nocrash_sid=; nocrash_rstart=; nocrash_cg=; nocrash_tmp=; nocrash_repo=
  while IFS== read -r k v; do case $k in t0) nocrash_t0=$v;; root) nocrash_root=$v;; sid) nocrash_sid=$v;; rstart) nocrash_rstart=$v;; cg) nocrash_cg=$v;; tmp) nocrash_tmp=$v;; repo) nocrash_repo=$v;; esac; done < "$1"
}
nocrash_own_pid() {  # nocrash_own_pid PPID CRASH_US: is PPID the root or a live descendant of it, born before the crash?
  local p=$1 us=$2 n=0 st ppid start; [ -n "$p" ] && [ "$p" -gt 1 ] 2>/dev/null || return 1
  while [ "$n" -lt 64 ] && [ "$p" -gt 1 ]; do
    st=$(nocrash_stat "$p") || return 1; set -- $st; ppid=$1; start=$3
    if [ "$n" = 0 ]; then [ $(( $(awk '/^btime/{print $2}' /proc/stat) * 1000 + start * 1000 / $(getconf CLK_TCK) )) -le $(( us / 1000 + 1000 )) ] || return 1; fi
    if [ "$p" = "$nocrash_root" ]; then [ "$start" = "$nocrash_rstart" ]; return; fi
    p=$ppid; n=$((n + 1))
  done; return 1
}
nocrash_own() {  # nocrash_own PID PPID SESSION CGROUP EXE CMDLINE CRASH_US
  local pp=$2 sid=$3 cg=$4 exe=$5 cmd=$6 us=$7 leaf=${4##*/}
  if [ -z "$nocrash_root" ]; then case "$exe" in /tmp/*|"${nocrash_tmp:-/nonexistent}"/*|"$nocrash_repo"/*) return 0;; esac; return 1; fi
  [ "$1" = "$nocrash_root" ] || nocrash_own_pid "$pp" "$us" && return 0
  [ -n "$sid" ] && [ "$sid" = "$nocrash_sid" ] && [ "$sid" -gt 1 ] && return 0
  case "$leaf" in *.scope) case "$leaf" in init.scope|session-*) ;; *) [ -n "$nocrash_cg" ] && { [ "$cg" = "$nocrash_cg" ] || [[ "$cg" == "$nocrash_cg"/* ]]; } && return 0;; esac;; esac
  local d; for d in "$nocrash_tmp" "$nocrash_repo"; do [ -n "$d" ] || continue; case "$exe $cmd" in "$d"/*|*" $d/"*) return 0;; esac; done
  return 1
}
nocrash_end() {  # prints the landing's own records and returns 1 when there are any
  local jc=${NOCRASH_JOURNALCTL:-journalctl}
  command -v "$jc" >/dev/null 2>&1 && command -v jq >/dev/null 2>&1 || { echo "no-crash-record: skipped, journalctl or jq not available"; return 0; }
  [[ "${nocrash_t0:-}" =~ ^[0-9]+$ ]] || { echo "no-crash-record: FAILED: no begin state (nocrash_begin was not run, or its state is lost): the check cannot tell whose crash is whose" >&2; return 1; }
  sleep 2   # systemd-coredump records asynchronously
  local out="" pid pp sid cg exe cmd us
  while IFS=$'\t' read -r pid pp sid cg exe us cmd; do
    [ -n "$pid" ] && [ "$us" -ge $((nocrash_t0 * 1000000)) ] 2>/dev/null || continue
    if nocrash_own "$pid" "$pp" "$sid" "$cg" "$exe" "$cmd" "$us"; then out+="pid $pid $exe (parent ${pp:-?}, cgroup ${cg:-?})"$'\n'; fi
  done < <("$jc" -o json --no-pager --since "@$nocrash_t0" MESSAGE_ID=fc2e22bc6ee647b6b90729ab34a250b1 2>/dev/null | jq -r 'select(.COREDUMP_PID != null) | [.COREDUMP_PID, ((.COREDUMP_PROC_STATUS // "") | tostring | capture("PPid:\\s*(?<p>[0-9]+)").p // ""), ((.COREDUMP_PROC_STATUS // "") | tostring | capture("NSsid:\\s*(?<s>[0-9]+)").s // ""), (.COREDUMP_CGROUP // ""), (.COREDUMP_EXE // ""), (.COREDUMP_TIMESTAMP // "0"), (.COREDUMP_CMDLINE // "")] | map(tostring) | @tsv' 2>/dev/null)
  if [ -n "$out" ]; then echo "no-crash-record: FAILED: this landing's own tree left a crash record (a probe that is meant to crash must run under 'quiet' or bin/run-probe):" >&2; printf '%s' "$out" >&2; return 1; fi
  echo "no-crash-record: ok (no crash record belongs to this landing; other processes' crashes are not read)"
}
