# Gate-edit approvals

A gate-defining file that may only GAIN lines (a ratchet, a Tier 1 script, an attack list) sometimes needs a line removed or changed for a good reason. The lander never lets a
change decide that for itself. A removed or changed line is accepted **only** on an exact diff-hash match against an **approval that is already on the base branch**.

## The file

`scripts/gate-edit-approvals.txt` (key `LAND_APPROVALS`; it cannot be empty, and the file is always in the protected set). One record per line, `#` comments and blank lines allowed:

    FILE | sha256 of the exact diff of that file | reason | YYYY-MM-DD

`FILE` is a plain repository path, the hash is lower-case hex, the reason is free text without `|`, the date is UTC. Anything else on a line is not an approval, and a line like that
may not be added.

## The hash: the canonical diff

    land-direct --print-gate-diff-hash FILE [<rev>]     # the sha256 on stdout; the record to write on stderr
    land-direct --print-gate-diff FILE [<rev>]          # the canonical diff itself

The canonical diff of FILE is what `git diff --no-ext-diff --no-textconv --no-color --no-renames --text -U0 --diff-algorithm=myers` (fixed prefixes `a/` `b/`, no user or repository diff
configuration, the `index` line dropped) prints for FILE between the **merge base with `origin/<base>`** and `<rev>` (default `HEAD`): the NET diff of the whole landing, not of one commit. The
hash binds the path, the hunks, the mode lines and the removed and added text; it is what the lander computes on the rebased tree, so the author and the judge agree.

## The rules (each has a negative self-test in `tests/test_approvals.sh`, each guard a mutant in `tests/test_mutations.sh`)

1. **Read from the base branch.** The lander reads approvals from `origin/<base>`, never from the change: a landing cannot approve itself. `LAND_GATE_APPEND_ONLY` (shell patterns) names the files that may only gain lines; a
   landing whose net diff removes or changes a line of one (or deletes it, or changes its mode) is refused (exit 12) unless an approval for exactly that diff is on base.
2. **An approval lands alone, first, and it is ONE line.** A commit that adds a record changes no other file, adds exactly ONE line (one record) and removes none; the landing that carries it is the same (one approval per landing, no tidying alongside). It passes Tier 1 like any change. The edit lands in a LATER landing. The approval commit is announced to the
   judge before the edit commit, always, with the diff hash AND the FULL edit diff (`land-direct --print-gate-diff FILE`): the hash binds the exact diff the judge read: `land-direct` prints `APPROVAL COMMIT: announce to the judge before landing the edit`.
3. **One-time.** A landing whose diff of FILE hashes to a record on base must REMOVE that record in the same landing (the consumption), or it is refused. Nothing else keeps a log: the record's disappearance in the landing
   is the log. Removing a record is how it is used up; a record can never approve a second edit. (Adding a record next to the edit is not allowed, see 2; removing one is the consumption.)
4. **A stale approval approves nothing.** A record older than `LAND_APPROVAL_DAYS` (default 7) days, or dated more than a day ahead, is refused when used, and refused when added.
5. **A record removed without being consumed is flagged and refused.** (A stale one may be tidied away: it approves nothing.) A fresh one is **withdrawn** by a trailer `Approval-Withdrawn: FILE <first 12 or more hex digits of its hash>` on a commit of the landing, and that landing changes nothing but the approvals file; `land-direct` prints `APPROVAL WITHDRAWN: announce to the judge`: the withdrawal is as visible as the approval was. Re-dating or editing a record is a removal of the old one. Deleting the file is the same.
6. **Malformed or self-referencing records are refused.** A record that does not parse (or names the approvals file) may not be added.
7. **The judge fails closed.** It runs in a shell of its own with `set -e`: an unexpected failure refuses the landing.

A repository's own `post-rebase` judge (a stricter one) may ask for the approvals this landing consumes: `$LAND_GATE_APPROVED_FILE` lists `FILE HASH` per consumed approval; the lander has already enforced 1 to 7.

## Protected sets: a protected change needs an approval too (`LAND_PROTECTED_LIST`, optional)

Telling an agent "do not land protected changes" does not hold: one misread message lands one. With `LAND_PROTECTED_LIST` set, the lander makes it structural. The key names a **protected-paths list**
in the repository (read from the base branch, like the configuration): one entry per line, a trailing `/` is a directory, anything else is a shell pattern (`*` matches `/`), a leading `?` marks an entry that
may match nothing yet, `#` starts a comment. A landing whose **net diff** (the rebased tree against base) touches ANY path the list covers is **refused (12)** unless the base branch holds a one-time approval for exactly
that set of paths:

    FILE-SET | sha256 of the exact net diff over exactly that set | reason | YYYY-MM-DD

- **The file-set key is canonical**: the touched protected paths, plain repository paths (a leading dot is fine), sorted in the C locale, unique, joined by commas, no spaces: `gate.sh,spec/x`. A key that is not in that form is
  not an approval record, and one path is the single-file record of the gate-edit rule above: the same format, the same rules.
- **The hash** is the sha256 of the canonical diff over exactly those paths: `land-direct --print-gate-diff-hash gate.sh,spec/x` (any order), or `land-direct --print-gate-diff-hash @protected [<rev>]`, which finds the protected paths the
  change touches itself and prints the record to write (`--print-gate-diff` prints the diff the judge reads).
- **Exactly the set**: an approval for a subset or a superset of the touched paths approves nothing, and neither does a hash over a different diff of the same paths. Renames, mode changes, symlinks and submodules are plain paths of the
  diff (no rename detection, so both sides of a move are touched); a directory replaced by a file or a symlink touches everything it covered.
- **The list is protected, and so are the configuration and the hooks**: the list file, the configuration file and `LAND_HOOKS_DIR` are always part of the set, so removing or narrowing an entry (or emptying or deleting the list) is a protected change that needs its own
  approval. The set that applies is the list on base united with the list in the change: a change that adds an entry and edits a file under it needs both. The two approvals files are not part of the set: their own rules (below) govern them.
- **Fails closed**: no list on base, an empty list, or a line that is not an entry refuses every landing (an unreadable list protects nothing).
- **Where the approvals live**: `LAND_PROTECTED_APPROVALS` (a path), default the gate-edit approvals file. A repository that already has an approvals file of its own for something else keeps it separate; a record in one file never approves
  a change judged by the other. Rules 1 to 7 apply to each file: read from base, one line alone in its commit and landing, announced to the judge first, one-time (removed by the landing that uses it), 7 days, withdrawn by an
  `Approval-Withdrawn: FILE-SET <hash prefix>` trailer, malformed or self-referencing records refused.
- **After Tier 1**: when Tier 1 regenerates generated files, the judge runs again on the tree that would land, so a protected generated path cannot change after the verdict.
- **Net diff**: a change and its revert inside one landing touch nothing and need nothing.
- **A revert of a protected change needs the approval too.** A revert that lands protected paths is a protected change like any other: first the approval line (its own landing, announced), then the revert, which removes the line.
  On a **frozen base** only a fix or a revert lands, and the approval landing is neither (it changes only the approvals file), so it is refused (14). A red main no longer stops anything. The path: the operator runs the approval landing with
  `LAND_FIX_FOR_RED=1` (treat this change as a fix so it passes the freeze; operator environment, not policy), announces it to the judge as always, and then lands the revert (a true `git revert` commit, whose message names the commit it undoes, passes a freeze by itself).
  Nothing about the approval is waived: only the freeze is.

## How to edit a gate line (the author's steps)

1. Make the edit in your worktree; commit it. Run `land-direct --print-gate-diff-hash FILE` and note the hash. (Do not land yet.)
2. In a fresh worktree off `origin/<base>`: add the record to `scripts/gate-edit-approvals.txt`, one commit that changes nothing else, `scripts/land-direct`. **Tell the judge before the next step**: the approval is the visible record he reads.
3. When the judge has read it: in the edit's worktree, remove the record (a commit, or in the edit's commit), rebase, `scripts/land-direct`. The same landing carries the edit and the consumption.
4. If the edit is not landed within `LAND_APPROVAL_DAYS`, the approval is stale: a new approval comes first.

## What the protected-set rule stops, and what it does not (stated limit)

**This mechanism stops a MISREAD** (a worker landing a protected change on a message that was not a land decision): without a line on base for that exact set and diff, the lander refuses, whatever the worker believes it was told.
**A DELIBERATE self-approval in two landings** (write the approval line, land it, then land the change) is stopped only by the announcement to the owner and by the operating rule that approval lines land only through the
owner after an explicit land decision. The lander makes the sequence mechanical (never in one landing, one line, exact set and diff, one-time, 7 days); it cannot tell an approval the owner read from one he did not.
A pause or a resume message is never a land decision.

## The honest limit

**An agent with landing rights could write its own approval line.** The control is that approvals are visible one-commit records the independent judge reads before the edit lands, so the approval commit is announced to the judge
BEFORE the edit commit, always. The lander makes the sequence mechanical (rules 1 to 7: no self-approval in the same landing, no reuse, no stale or quiet approval, nothing but the exact diff), not independent: it
cannot tell an approval the judge read from one he did not. The record's own reason line is the place to say why; the announcement is the control.


## 0.6.0: only the lander's own files need an approval
The rules above bind the lander's own files (its vendored copy `scripts/land/`, `scripts/land-direct`, any `*.signers`, the configuration, the hooks directory and the protected-paths list). Every other protected path, and a removed or changed line of an append-only file, lands on a `Protected: <reason>` trailer in a commit of the landing (no hash, no approval record). A landing's used approval line is deleted by the lander. The hash rule in one sentence: land if the approved files' own changed lines are identical to the approved diff, and say so.
