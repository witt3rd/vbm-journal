# The heavy-host guard: no test, mutation run or long runner on a marked host

A machine that someone sits at (a desktop) must never run the heavy work of a repository: a whole-shim mutation run once left 23 orphaned probe processes burning 23 cores for up to 21 hours. The guard makes the helpers **refuse** on such a machine, not merely scope and bound the work.

## The marker

A host is marked by an empty file at **either** place (either present is enough):

- `/etc/vbm/no-build-host` (the system file; written by whoever configures the machine), or
- `<config dir>/vbm/no-build-host`, where the config dir is `${XDG_CONFIG_HOME:-$HOME/.config}` (also looked for under `$HOME/.config` and under the home directory the account database names, so moving a variable hides nothing).

A dangling symlink counts as present. The marker belongs to the machine's owner: a worker does not create, move or remove it.

## What refuses (exit 2, a clear message, **nothing started**)

| Where | How |
|---|---|
| `bin/no-build-guard [-- CMD...]` | the check itself; with `CMD` it execs it after the check. Put it first in any runner that cannot be wrapped (`self` runners). |
| `bin/run-scoped.sh` | calls the guard before anything and again in the scoped side, just before the command is exec'd. A copy with no guard installed next to it refuses too. `templates/run-scoped.sh` is the file a consumer copies. |
| `bin/run-probe` | calls the guard before it compiles or runs anything. |

There is **no override**. `VBM_ALLOW_BUILD_HERE=1` and every other variable are ignored; the system marker's path is a plain assignment in `lib/no-build-host.sh`, not read from the environment. Run the work on a build host.

## The Tier 1 lint: `bin/no-build-guard --lint [ROOT]` (and `--selftest`)

- `bin/run-scoped.sh` calls the guard (a call, not a comment) before the first `systemd-run`, `setsid` or `exec`, and **really refuses**: the lint runs it with a marker present and demands exit 2 with the command not started.
- Every runner declared in `scripts/long-runners.txt` or the optional `scripts/heavy-runners.txt` (one name per line; `NAME` = callers wrap it, `self NAME` = its own file calls `no-build-guard`) is never run outside `run-scoped.sh`, `no-build-guard` or `run-probe` in `scripts/*.sh`, `scripts/wt`, `.land/land-direct`, `scripts/githooks/*` or a workflow. List the mutation runner and the ABI/probe test script there.
- Declared runners with no helper beside the guard fail.

Wire it next to the scoped-runner lint in Tier 1: `.land/tool/bin/no-build-guard --selftest && .land/tool/bin/no-build-guard --lint .`

## Attack list (what it stops, what it cannot)

1. **Bypass by environment** (`VBM_ALLOW_BUILD_HERE=1`, an `ALLOW`-style variable, an exported `nbh_etc`, a moved `XDG_CONFIG_HOME` or `HOME`): stopped. No variable removes a place that is looked at; tested.
2. **Calling the runner directly** (`python3 scripts/mutants.py`, `mise exec -- ...`, a pipeline): stopped for a name on the list by the lint (Tier 1 fails, so it does not land); a `self` runner refuses itself. **Not stopped**: a name that is not on the list, and indirection the lint cannot read (a variable holding the runner, a `bash -c` string, a renamed copy). A guard against accidents, as the scoped-runner lint is.
3. **Calling the scoped side directly** (`run-scoped.sh --exec-argfile F`): stopped, it re-checks before it execs; tested.
4. **Deleting or hiding the marker**: **cannot be prevented.** The marker is the owner's file; whoever can delete it (the owner, the machine's configuration tool, an agent with the owner's rights) can run the work. The defence is to keep it managed by the configuration tool, so a deletion is repaired, and to make deletion visible (a root-owned `/etc` file an unprivileged worker cannot remove).
5. **TOCTOU**: the check is made at the start and again just before the exec; a marker that appears *after* that does not stop a run already started (the bound of `run-scoped.sh`, `RuntimeMaxSec`, still ends it). A marker swapped in a window between check and exec of one command is not a hole: the command either started or did not. A caller that checks and then starts the command by another path is the case for the lint (declare the runner).
6. **Editing the helper or the lint away in a consumer**: the guard, the lint AND the helper (`run-scoped.sh`, beside the guard) are vendored (in `.land/tool/bin/`) and drift-checked against the pin (`land-check`), and the lint finds the helper beside the guard and runs it with a marker present on every Tier 1; only `long-runners.txt` (which runners need scoping) is the consumer's own file, and a repository should list it in its protected set so that an edit of it is a gate edit.
7. **A test or tool that does not go through a helper at all** (plain `lake build`, a compiler loop, `test_abi.sh` not declared): not stopped. Declare it in `scripts/heavy-runners.txt`.
