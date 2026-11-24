"""Lean verifier for formal-conjectures attempts.

A candidate passes only if ALL hold:
  1. Static checks: no sorry/admit/axiom/unsafe/extern/implemented_by.
  2. Statement lock: the target theorem's statement is byte-identical
     (whitespace-normalized) to the original conjecture file.
  3. `lake env lean` compiles the file with zero errors.
  4. `#print axioms` shows only propext, Classical.choice, Quot.sound.
  5. Type lock: Lean's elaborated type (pp.all) of the theorem equals the original's.

Disproof mode: the candidate must state `theorem <name>_false : ¬ (...)`.
The negated statement can't be locked textually, so disproofs always come back
with needs_human_review=True.

CLI:    python3 verifier.py --project ~/rh-lean/formal-conjectures \
            --original FormalConjectures/WrittenOnTheWallII/GraphConjecture84.lean \
            --candidate attempts/c84_try3.lean --theorem conjecture84
Server: python3 verifier.py --project ... --serve 8765
        POST /check {"original": ..., "candidate_text": ..., "theorem": ..., "mode": "prove"}
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BANNED = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"^\s*axiom\b", "axiom declaration"),
    (r"\bunsafe\b", "unsafe"),
    (r"@\[\s*extern", "extern"),
    (r"implemented_by", "implemented_by"),
    (r"\bdebug\.skipKernelTC\b", "skipKernelTC"),
]


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


def namespace_of(src: str, theorem: str) -> str:
    """Namespace active at the theorem (handles one level of `namespace X ... end X`)."""
    code = strip_comments(src)
    pos = re.search(rf"\btheorem\s+{re.escape(theorem)}\b", code)
    if not pos:
        return ""
    stack = []
    for m in re.finditer(r"^\s*(namespace|end)\s+([\w.]+)", code[: pos.start()], flags=re.M):
        if m.group(1) == "namespace":
            stack.append(m.group(2))
        elif stack and stack[-1] == m.group(2):
            stack.pop()
    return ".".join(stack)


OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def proof_start(rest: str) -> int:
    """Index of the `:=` that starts the proof in `rest` (text from `theorem <name>`).

    A `:=` inside the statement (e.g. `let x := v`) must not count. The proof's `:=` is
    the first one at bracket depth 0 that is followed by `by` or `sorry`.
    (Bug found by control N4: the old code stopped at the first `:=`, so everything after
    a `let` in the statement went unchecked.) Returns -1 if none found."""
    depth = 0
    i = 0
    while i < len(rest) - 1:
        c = rest[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth = max(depth - 1, 0)
        elif depth == 0 and rest.startswith(":=", i):
            nxt = rest[i + 2:].lstrip()
            if re.match(r"(by|sorry)\b", nxt):
                return i
        i += 1
    return -1


def extract_statement(src: str, theorem: str) -> str | None:
    """Whitespace-normalized text from `theorem <name>` up to the proof's `:=`."""
    code = strip_comments(src)
    m = re.search(rf"\btheorem\s+{re.escape(theorem)}\b", code)
    if not m:
        return None
    rest = code[m.start():]
    end = proof_start(rest)
    if end < 0:
        return None
    return " ".join(rest[:end].split())


def statement_matches(original: str, candidate: str, theorem: str) -> tuple[bool, str, str]:
    """Candidate's text from `theorem <name>` must START with the original's full
    statement followed by `:=`. Only the original is parsed for its end point, so the
    candidate's proof style (term mode, `by`, anything) cannot shift the comparison."""
    want = extract_statement(original, theorem)
    code = strip_comments(candidate)
    m = re.search(rf"\btheorem\s+{re.escape(theorem)}\b", code)
    if want is None or not m:
        return False, str(want), "<theorem not found>"
    got = " ".join(code[m.start():].split())
    return got.startswith(want + " :="), want, got[: len(want) + 40]


HELPER_BANNED = r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*" \
    r"(def|abbrev|instance|notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|" \
    r"elab|attribute|set_option|variable|open|namespace|end|section|local|scoped|universe|opaque)\b"


def prefix_lock(original: str, candidate: str, theorem: str) -> list[str]:
    """Candidate must reproduce the original verbatim up to the target theorem;
    anything inserted before the theorem may only be lemma/theorem declarations
    (no defs, instances, notation, options, or namespace changes that could
    silently change what the locked statement means)."""
    pat = rf"(/--(?:(?!-/).)*-/\s*)?(@\[[^\]]*\]\s*)*\btheorem\s+{re.escape(theorem)}\b"
    mo = re.search(pat, original, flags=re.S)
    mc = re.search(pat, candidate, flags=re.S)
    if not mo or not mc:
        return ["target theorem not found for prefix lock"]
    o_pre = " ".join(strip_comments(original[: mo.start()]).split())
    c_pre = " ".join(strip_comments(candidate[: mc.start()]).split())
    if not c_pre.startswith(o_pre):
        return ["text before the theorem was changed (prefix lock)"]
    from collections import Counter

    def banned_lines(text):
        return Counter(" ".join(l.split()) for l in text.splitlines()
                       if re.match(HELPER_BANNED, l))

    extra = banned_lines(strip_comments(candidate[: mc.start()])) - \
        banned_lines(strip_comments(original[: mo.start()]))
    if extra:
        return [f"banned declaration inserted before theorem: {list(extra)[:5]}"]
    return []


def static_check(src: str) -> list[str]:
    code = strip_comments(src)
    return [label for pat, label in BANNED if re.search(pat, code, flags=re.M)]


def parse_axioms(output: str, fqname: str):
    if f"'{fqname}' does not depend on any axioms" in output:
        return []
    m = re.search(rf"'{re.escape(fqname)}' depends on axioms: \[(.*?)\]", output, flags=re.S)
    if not m:
        return None
    return [a.strip() for a in m.group(1).split(",") if a.strip()]


def run_lean(project: str, text: str, timeout: int):
    scratch = os.path.join(project, ".verifier_scratch")
    os.makedirs(scratch, exist_ok=True)
    fd, path = tempfile.mkstemp(suffix=".lean", dir=scratch)
    with os.fdopen(fd, "w") as f:
        f.write(text)
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=project,
                           capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return -1, f"TIMEOUT after {timeout}s"
    finally:
        os.unlink(path)


BEGIN, END = "<<<VERIFIER_TYPE_BEGIN>>>", "<<<VERIFIER_TYPE_END>>>"
_MSG_PREFIX = re.compile(r"^\S*\.lean:\d+:\d+:\s*(?:info|information)?:?\s?", flags=re.M)
_type_cache = {}


def type_probe(fq: str) -> str:
    return (f'\n\n#print "{BEGIN}"\nset_option pp.all true in\n#check @{fq}\n'
            f'#print "{END}"\n')


def parse_type(out: str) -> str | None:
    """Text Lean printed between the two markers, with per-message `file:line:col:` prefixes
    removed (line numbers differ between original and candidate) and whitespace normalized."""
    i, j = out.find(BEGIN), out.rfind(END)
    if i < 0 or j < 0 or j <= i:
        return None
    body = out[i + len(BEGIN): j]
    body = _MSG_PREFIX.sub("", body)
    body = " ".join(body.split())
    return body or None


def original_type(project, original_text, fq, timeout):
    key = (hashlib.sha256(original_text.encode()).hexdigest(), fq)
    if key not in _type_cache:
        _, out = run_lean(project, original_text + type_probe(fq), timeout)
        _type_cache[key] = parse_type(out)
    return _type_cache[key]


def verify(project, original_text, candidate_text, theorem, mode="prove", timeout=600):
    t0 = time.time()
    res = {"ok": False, "mode": mode, "theorem": theorem, "stage": None,
           "errors": [], "axioms": None, "needs_human_review": mode == "disprove"}

    target = theorem if mode == "prove" else f"{theorem}_false"
    bad = static_check(candidate_text)
    if bad:
        res.update(stage="static", errors=[f"banned: {b}" for b in bad])
        return res

    if mode == "prove":
        same, want, got = statement_matches(original_text, candidate_text, theorem)
        if not same:
            res.update(stage="lock", errors=["statement differs from original",
                                             f"original:  {want}", f"candidate: {got}"])
            return res
        perr = prefix_lock(original_text, candidate_text, theorem)
        if perr:
            res.update(stage="lock", errors=perr)
            return res
    elif extract_statement(candidate_text, target) is None:
        res.update(stage="lock", errors=[f"no theorem named {target}"])
        return res

    ns = namespace_of(candidate_text, target)
    fq = f"{ns}.{target}" if ns else target
    # `#print axioms` must sit inside or after the namespace; append at file end with FQ name.
    code, out = run_lean(project, candidate_text + type_probe(fq) + f"\n#print axioms {fq}\n",
                         timeout)
    errs = [l for l in out.splitlines() if ": error" in l or l.startswith("error") or "TIMEOUT" in l]
    if code != 0 or errs:
        res.update(stage="compile", errors=(errs or out.splitlines())[:40])
        return res

    if mode == "prove":
        # Second, independent statement lock: compare the ELABORATED types Lean prints
        # (pp.all) for the original and the candidate. Fails closed if either is unparsable.
        want_t = original_type(project, original_text, fq, timeout)
        got_t = parse_type(out)
        res["type_lock"] = {"original_found": want_t is not None, "candidate_found": got_t is not None}
        if want_t is None or got_t is None:
            res.update(stage="type_lock",
                       errors=["could not read elaborated type (fail closed)",
                               f"original found: {want_t is not None}",
                               f"candidate found: {got_t is not None}"])
            return res
        if want_t != got_t:
            k = next((i for i, (a, b) in enumerate(zip(want_t, got_t)) if a != b),
                     min(len(want_t), len(got_t)))
            lo = max(k - 150, 0)
            res.update(stage="type_lock",
                       errors=[f"elaborated statement type differs at char {k}",
                               f"original:  ...{want_t[lo:k + 150]}...",
                               f"candidate: ...{got_t[lo:k + 150]}..."])
            return res

    axioms = parse_axioms(out, fq)
    res["axioms"] = axioms
    if axioms is None:
        res.update(stage="axioms", errors=["could not parse #print axioms output", out[-2000:]])
        return res
    extra = sorted(set(axioms) - ALLOWED_AXIOMS)
    if extra:
        res.update(stage="axioms", errors=[f"disallowed axioms: {extra}"])
        return res

    res.update(ok=True, stage="passed", seconds=round(time.time() - t0, 1))
    return res


def serve(project, port):
    class H(BaseHTTPRequestHandler):
        def do_POST(self):
            if self.path != "/check":
                self.send_error(404)
                return
            body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
            with open(os.path.join(project, body["original"])) as f:
                original = f.read()
            out = verify(project, original, body["candidate_text"], body["theorem"],
                         body.get("mode", "prove"), body.get("timeout", 600))
            data = json.dumps(out).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

    print(f"verifier on http://127.0.0.1:{port}/check  project={project}")
    ThreadingHTTPServer(("127.0.0.1", port), H).serve_forever()


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", required=True)
    ap.add_argument("--original")
    ap.add_argument("--candidate")
    ap.add_argument("--theorem")
    ap.add_argument("--mode", default="prove", choices=["prove", "disprove"])
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--serve", type=int)
    a = ap.parse_args()
    project = os.path.expanduser(a.project)
    if a.serve:
        serve(project, a.serve)
    else:
        with open(os.path.join(project, a.original)) as f:
            orig = f.read()
        with open(a.candidate) as f:
            cand = f.read()
        print(json.dumps(verify(project, orig, cand, a.theorem, a.mode, a.timeout), indent=2))
