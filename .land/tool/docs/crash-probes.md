# Crash probes and the landing's crash-record check

A test that crashes a program on purpose (a probe, a mutant, an ABI check) must leave no crash record: on a host with systemd-coredump every crash is a journal entry and a desktop notice, and a check that reads the host's crash records would otherwise blame a landing for another run's deliberate crash.

## Running a probe: `bin/run-probe`

`run-probe CMD...` runs CMD with **`ulimit -c 0` PLUS the dumpable-clear preload (`PR_SET_DUMPABLE 0`)** in a **private `TMPDIR`** (`mktemp -d`, removed afterwards; never a fixed `/tmp/name`). `ulimit -c 0` alone is not enough: with a piped core pattern (systemd-coredump) a crash under `ulimit -c 0` still writes a journal record (exit 139, no core file, yet a `coredumpctl` entry and a notice; measured). The status is CMD's (139 SIGSEGV, 134 SIGABRT).

It **refuses** (exit 2, nothing runs) a call that raises the core limit (`--core-limit N` with N not 0, or `RUN_PROBE_CORE_LIMIT` not 0), a limit that cannot be lowered to 0, and a missing C compiler. Inside a probe, `run-probe --require` exits 0 only when the process really runs under `run-probe` (core limit 0, the preload present); otherwise it is refused (exit 2). `run-probe --lint LIST [ROOT]` fails when a tracked file runs a probe binary named in LIST outside the helper (a line with `run-probe` or `quiet ` or `# probe-ok` is exempt): wire it into Tier 1 next to the scoped-runner lint.

A statically linked binary ignores the preload: its crash still leaves a record (no core is written).

## The check: `bin/no-crash-record begin|end`

`begin` stamps the time and the landing's identity (the calling process is its root: pid and start time, session, cgroup, private `TMPDIR`, repository) in `$TMPDIR/no-crash-record.state`; `end` fails when a crash record belongs to **this landing**. A wrapper calls it with `exec`. Records come from `journalctl -o json` (needs `jq`; without them the check is skipped with a note).

A record is the landing's when any of: its parent (the record's `PPid`) is the root or a live descendant of it (identified by pid AND start time; the parent must have been born before the crash; a `setsid` child or a `systemd-run --scope` child keeps its parent chain); its session is the root's; its cgroup is the landing's own transient `*.scope` (not `init.scope` or a login session scope) or below it; its executable or command line is under the landing's private `TMPDIR` or the repository.

It fails closed: no begin state, or an unreadable time, fails the check; an empty id matches nothing (never everything); with no usable root pid the broad old filter applies (any executable under `/tmp`, `$TMPDIR` or the repository: stricter, never looser).

**Residual hole (accepted, stated plainly): an orphan that also setsid's, runs from a shared dir and leaves our scope is NOT caught.** A record whose journal entry has no `PPid` falls to the cgroup and directory rules.
