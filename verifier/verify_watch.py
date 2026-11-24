"""Inbox watcher: lets a remote solver (Claude in the cloud) get Lean verdicts
without typing into your Terminal.

The solver drops a pair into ~/rh-lean/inbox/:
    <job>.lean   candidate file
    <job>.json   {"original": "<path relative to formal-conjectures>", "theorem": "...",
                  "mode": "prove"}
The watcher runs verifier.py on it and writes ~/rh-lean/outbox/<job>.result.json,
then moves the pair to ~/rh-lean/inbox/done/.

Safety: Lean can run arbitrary code at compile time (#eval, run_cmd, IO actions,
initialize). Candidates containing any of those are refused BEFORE Lean sees them,
so nothing the solver writes can execute on this Mac beyond type-checking.
Originals must live inside formal-conjectures or ~/rh-lean/targets/.

Start:  export PATH=$HOME/.elan/bin:$PATH && cd ~/rh-lean/verifier && python3 verify_watch.py
Stop:   Ctrl-C
"""
import json
import os
import re
import shutil
import time

from verifier import verify, strip_comments

ROOT = os.path.expanduser(os.environ.get("WOWII_ROOT", "~/rh-lean"))
PROJECT = os.path.join(ROOT, "formal-conjectures")
INBOX, OUTBOX = os.path.join(ROOT, "inbox"), os.path.join(ROOT, "outbox")
DONE = os.path.join(INBOX, "done")
TARGETS = os.path.join(ROOT, "targets")

EXEC_BANNED = [
    (r"#eval\b", "#eval"), (r"\brun_cmd\b", "run_cmd"), (r"\brun_elab\b", "run_elab"),
    (r"\brun_meta\b", "run_meta"), (r"\binitialize\b", "initialize"),
    (r"\bbuiltin_initialize\b", "builtin_initialize"), (r"\bIO\.", "IO."),
    (r"#exit\b", "#exit"), (r"\bevalExpr\b", "evalExpr"), (r"@\[\s*init\b", "@[init]"),
    (r"\bimport\s+(?!Mathlib|FormalConjectures)", "import outside Mathlib/FormalConjectures"),
]


def exec_check(text):
    code = strip_comments(text)
    return [label for pat, label in EXEC_BANNED if re.search(pat, code)]


def resolve_original(rel):
    for base in (PROJECT, TARGETS):
        p = os.path.realpath(os.path.join(base, rel))
        if p.startswith(os.path.realpath(base) + os.sep) and os.path.isfile(p):
            return p
    return None


def handle(job):
    lean_p, meta_p = os.path.join(INBOX, job + ".lean"), os.path.join(INBOX, job + ".json")
    out_p = os.path.join(OUTBOX, job + ".result.json")
    t0 = time.time()
    try:
        meta = json.load(open(meta_p))
        cand = open(lean_p).read()
        bad = exec_check(cand)
        orig_p = resolve_original(meta["original"])
        if bad:
            res = {"ok": False, "stage": "exec_guard", "errors": [f"refused: {b}" for b in bad]}
        elif orig_p is None:
            res = {"ok": False, "stage": "setup", "errors": ["original not found under "
                                                           "formal-conjectures/ or targets/"]}
        else:
            res = verify(PROJECT, open(orig_p).read(), cand, meta["theorem"],
                         meta.get("mode", "prove"), int(meta.get("timeout", 600)))
    except Exception as e:  # report, never crash the loop
        res = {"ok": False, "stage": "watcher_error", "errors": [repr(e)]}
    res["job"], res["wall_seconds"] = job, round(time.time() - t0, 1)
    tmp = out_p + ".tmp"
    json.dump(res, open(tmp, "w"), indent=1)
    os.replace(tmp, out_p)  # atomic: the reader never sees a half-written result
    for p in (lean_p, meta_p):
        if os.path.exists(p):
            shutil.move(p, os.path.join(DONE, os.path.basename(p)))
    print(f"[{time.strftime('%H:%M:%S')}] {job}: ok={res.get('ok')} stage={res.get('stage')}",
          flush=True)


def main():
    for d in (INBOX, OUTBOX, DONE, TARGETS):
        os.makedirs(d, exist_ok=True)
    print(f"watching {INBOX}  (Ctrl-C to stop)", flush=True)
    while True:
        jobs = sorted(f[:-5] for f in os.listdir(INBOX)
                      if f.endswith(".json") and os.path.exists(os.path.join(INBOX, f[:-5] + ".lean")))
        for job in jobs:
            # wait until both files have stopped changing (sync from the cloud can lag)
            p1, p2 = os.path.join(INBOX, job + ".lean"), os.path.join(INBOX, job + ".json")
            if time.time() - max(os.path.getmtime(p1), os.path.getmtime(p2)) < 3:
                continue
            handle(job)
        time.sleep(2)


if __name__ == "__main__":
    main()
