#!/usr/bin/env python3
"""The trust-ledger checker of vbm-land (docs/lean-gates.md; run by `land-lean trust`, which derives the REQUIRED keys from the tree and the configuration).
Every required key (an extern symbol, a C/loader file, a closure module outside the proofs, the Lean runtime pieces, a tool)
must be named by the `Covers:` line of an entry; every `Covers:` token must name a required key (no stale cover); every entry must be complete
(what, where it enters, what is assumed + the contract, the test, owner, a plan from the closed set; `accept` needs a reason); every file an entry cites must exist.
The required set comes from the tree and the compiled closure, never from the ledger, so relabeling a definition cannot shrink it; the self-test removes each entry in turn
and each removal must fail (an entry that covers nothing required is padding and fails too)."""
import os, re, sys
FIELDS = ["What", "Enters", "Assumes", "Test", "Owner", "Plan", "Covers"]
PLANS = ("verify", "replace", "sandbox", "accept")
PATH = re.compile(r"(?<![\w./-])(?:[\w.-]+/)+[\w.-]*\w\.\w+")   # a path with a directory in it; it counts only when its first component exists at the repository root (a URL or a prose fragment does not)

def cited(text, root):
    return [p for p in PATH.findall(text) if os.path.exists(os.path.join(root, p.split("/")[0]))]

def parse(text):
    entries, cur, fld = [], None, None
    for line in text.splitlines():
        h = re.match(r"^### (T\d+)\. (.+)$", line)
        f = re.match(r"^- \*\*(\w+):\*\* ?(.*)$", line)
        if h: cur = {"id": h[1], "title": h[2], "f": {}}; entries.append(cur); fld = None
        elif cur is not None and f and f[1] in FIELDS: fld = f[1]; cur["f"][fld] = f[2]
        elif cur is not None and fld and line.startswith("  "): cur["f"][fld] += " " + line.strip()
        elif not line.strip(): fld = None
    return entries

def check(text, required, root="."):
    """-> (errors, gaps, entries); required: set of keys."""
    errs, gaps, entries = [], 0, parse(text)
    covered = {}
    for e in entries:
        i, f = e["id"], e["f"]
        for k in FIELDS:
            if len(f.get(k, "").strip()) < (3 if k in ("Owner", "Covers") else 12): errs.append(f"{i} {e['title']}: field {k} is missing or empty")
        plan = f.get("Plan", "").strip()
        if not plan.startswith(PLANS): errs.append(f"{i}: Plan must start with one of {'/'.join(PLANS)}")
        if plan.startswith("accept") and "because" not in plan: errs.append(f"{i}: an accepted risk needs a stated reason ('because ...')")
        if not (cited(f.get("Assumes", ""), root) or "no written contract" in f.get("Assumes", "")): errs.append(f"{i}: Assumes must link a contract (a path in this repository) or say 'no written contract'")
        if "no written contract" in f.get("Assumes", ""): gaps += 1
        t = f.get("Test", "")
        if not (cited(t, root) or t.startswith("none")): errs.append(f"{i}: Test must name a test that can fail (a path) or say 'none'")
        for field in ("Enters", "Assumes", "Test"):
            for p in cited(f.get(field, ""), root):
                if not os.path.exists(os.path.join(root, p)): errs.append(f"{i}: {field} cites {p}, which does not exist")
        for tok in re.findall(r"`([^`]+)`", f.get("Covers", "")):
            if tok not in required: errs.append(f"{i}: Covers `{tok}` names nothing the tree or closure requires (stale or misspelled)")
            covered.setdefault(tok, []).append(i)
    for k in sorted(required - set(covered)): errs.append(f"not in the trust ledger: {k}")
    return errs, entries

def main():
    ledger, reqfile = sys.argv[1], sys.argv[2]
    required = {l.strip() for l in open(reqfile) if l.strip()}
    if not os.path.isfile(ledger): print(f"trust ledger: no {ledger}: every repository keeps one (what cannot be proven is marked as trusted)", file=sys.stderr); sys.exit(1)
    text = open(ledger).read()
    errs, entries = check(text, required)
    for e in errs: print(f"trust ledger: {e}", file=sys.stderr)
    if errs or not entries: print(f"trust ledger: FAILS ({len(errs)} problem(s), {len(entries)} entries)", file=sys.stderr); sys.exit(1)
    # negative self-tests: the gate can fail. Removing ANY entry must fail it (each entry is load-bearing); a required key nobody covers must fail it; an empty plan must fail it.
    blocks = re.split(r"(?m)^(?=### T\d+\. )", text)
    head, body = blocks[0], blocks[1:]
    for n in range(len(body)):
        if not check(head + "".join(body[:n] + body[n+1:]), required)[0]: print(f"trust ledger: self-test: removing entry {body[n].splitlines()[0]} did not fail the gate", file=sys.stderr); sys.exit(1)
    if not check(text, required | {"extern:__land_lean_trust_not_in_the_ledger"})[0]: print("trust ledger: self-test: a new boundary with no entry did not fail", file=sys.stderr); sys.exit(1)
    if not check(re.sub(r"(?m)^(- \*\*Plan:\*\*) .*", r"\1 ", text, count=1), required)[0]: print("trust ledger: self-test: an empty plan did not fail", file=sys.stderr); sys.exit(1)
    if not check(re.sub(r"(?m)^(- \*\*Plan:\*\*) accept.*", r"\1 accept", text, count=1) if "Plan:** accept" in text else text + "x", required)[0]: print("trust ledger: self-test: an accept with no reason did not fail", file=sys.stderr); sys.exit(1)
    gaps = sum(1 for e in parse(text) if "no written contract" in e["f"]["Assumes"] or e["f"]["Test"].startswith("none"))
    print(f"trust ledger: {len(entries)} entries ({len(required)} required items covered; {gaps} with no written contract or no test: the gaps; {len(body) + 3} negative self-tests ok)")

if __name__ == "__main__": main()
