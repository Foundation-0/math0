#!/usr/bin/env python3
"""Generate CONTENTS.md and results/<slug>/README.md from catalog.json.

catalog.json is the single source of truth for what math0 claims. Every entry points at a Lean
file whose final command (#math0_proves / #math0_refutes / #math0_answers) is re-checked by CI.
"""
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO_URL = "https://github.com/Foundation-0/math0"
FC_URL = "https://github.com/google-deepmind/formal-conjectures"

def _tracked_papers():
    """Manuscripts committed to the repository. An untracked paper.pdf is a draft that has not
    passed proofreading yet, so it is not linked."""
    try:
        out = subprocess.run(["git", "ls-files", "--", "results/*/paper.pdf"], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout.split()
    except (OSError, subprocess.CalledProcessError):
        return None
    return {path.split("/")[1] for path in out}


TRACKED_PAPERS = _tracked_papers()


def has_paper(slug):
    if not os.path.exists(os.path.join(ROOT, "results", slug, "paper.pdf")):
        return False
    return TRACKED_PAPERS is None or slug in TRACKED_PAPERS


CLASS_LABEL = {
    "new-result": "New result (open problem settled)",
    "known-result-first-formalization": "First formal proof of a known result",
    "known-result-already-formalized": "Independent formal proof (an implying Lean proof already exists elsewhere)",
    "misformalization": "Misformalization found (upstream statement does not match the problem)",
}
VERB = {
    "proves": "proves",
    "refutes": "refutes (proves the negation of)",
    "answers": "answers",
    "refutes_every_answer": "refutes, for every possible value of its unknown,",
    "settles-proves": "proves",
    "settles-refutes": "refutes (proves the negation of)",
}


MODE_NOTE = {
    "proves": "",
    "refutes": " (negated)",
    "answers": " with its unknown replaced by an explicit value",
    "refutes_every_answer": " negated and universally quantified over the unknown",
    "settles-proves": "",
    "settles-refutes": " (negated)",
}


def upstream_link(e):
    u = e["upstream"]
    if e.get("statement_origin") == "math0":
        return f"[`{u['decl']}`]({u['file']}) (math0, from {e['source']})"
    return f"[`{u['decl']}`]({FC_URL}/blob/{u['commit']}/{u['file']})"


def verification_text(e):
    u = e["upstream"]
    if e.get("statement_origin") == "math0":
        return (
            f"The statement was formalized by math0 from the conjecture in [{e['source']}]({e['source_url']}) "
            f"as [`{u['decl']}`](../../{u['file']}). Its definitions are checked by the kernel against the OEIS data, "
            "and it was reviewed for fidelity and frozen before any proof attempt. The Lean file "
            f"[`{e['lean_file']}`](../../{e['lean_file']}) {VERB[e['mode']]} it; the final command `#math0_settles` checks that "
            "our theorem's type is exactly the statement or its negation and that both use no axioms beyond "
            "`propext`, `Classical.choice` and `Quot.sound`."
        )
    return (
        f"The Lean file [`{e['lean_file']}`](../../{e['lean_file']}) {VERB[e['mode']]} the upstream statement "
        f"{upstream_link(e)} (formal-conjectures at commit `{u['commit'][:7]}`, upstream category "
        f"`{u['category']}`). Its final command `#math0_{e['mode']}` checks that our theorem's type is "
        f"syntactically identical to the upstream statement{MODE_NOTE[e['mode']]} "
        "and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`."
    )


def result_readme(e):
    u = e["upstream"]
    lines = [
        f"# {e['title']}",
        "",
        f"**Classification:** {CLASS_LABEL[e['classification']]}  ",
        f"**Area:** {e['area']}  ",
        f"**Source problem:** {e['source']}  ",
        f"**Date:** {e['date']}",
        "",
        "## Result",
        "",
        e["summary"],
        "",
        "## Verification",
        "",
        verification_text(e),
        "",
    ]
    if e.get("notes"):
        lines += ["## Notes", "", e["notes"], ""]
    if has_paper(e["slug"]):
        lines += ["## Manuscript", "", "[paper.pdf](paper.pdf) ([source](paper.tex))", ""]
    lines += [
        "## Citation",
        "",
        "```bibtex",
        f"@misc{{math0:{e['slug']},",
        "  author       = {{math0}},",
        f"  title        = {{{{{e['title']}}}}},",
        f"  howpublished = {{\\url{{{REPO_URL}/tree/main/results/{e['slug']}}}}},",
        f"  note         = {{Produced by Claude (Anthropic); Lean-verified}},",
        f"  year         = {{{e['date'][:4]}}}",
        "}",
        "```",
        "",
    ]
    return "\n".join(lines)


SHORT = {
    "new-result": "new results",
    "known-result-first-formalization": "first formal proofs of known results",
    "known-result-already-formalized": "independent formal proofs",
    "misformalization": "misformalization reports",
}


def write_highlights(entries, counts):
    """Refresh the generated block between the HIGHLIGHTS markers in README.md."""
    path = os.path.join(ROOT, "README.md")
    text = open(path).read()
    start, end = "<!-- HIGHLIGHTS:START -->", "<!-- HIGHLIGHTS:END -->"
    if start not in text or end not in text:
        return
    lines = [
        start,
        f"**{len(entries)} verified results.** "
        + ", ".join(f"{v} {SHORT[k]}" for k, v in counts.items() if v)
        + ". Full list: [CONTENTS.md](CONTENTS.md).",
        "",
        "New results (open problems settled; each checked by the Lean kernel and judged new by an independent novelty referee):",
        "",
    ]
    for e in entries:
        if e["classification"] == "new-result":
            paper = f" ([paper](results/{e['slug']}/paper.pdf))" if has_paper(e["slug"]) else ""
            lines.append(f"* [{e['title']}](results/{e['slug']}/README.md){paper}")
    lines.append(end)
    pre, rest = text.split(start, 1)
    post = rest.split(end, 1)[1]
    open(path, "w").write(pre + "\n".join(lines) + post)


def main():
    cat = json.load(open(os.path.join(ROOT, "catalog.json")))
    entries = sorted(cat["results"], key=lambda e: (list(CLASS_LABEL).index(e["classification"]), e["area"], e["title"]))
    for e in entries:
        d = os.path.join(ROOT, "results", e["slug"])
        os.makedirs(d, exist_ok=True)
        open(os.path.join(d, "README.md"), "w").write(result_readme(e))
    counts = {k: sum(e["classification"] == k for e in entries) for k in CLASS_LABEL}
    out = [
        "# Contents",
        "",
        f"**{len(entries)} results, every one checked by the Lean kernel against a statement published by a third party.**",
        "",
        "| Classification | Count |",
        "|---|---|",
    ] + [f"| {CLASS_LABEL[k]} | {v} |" for k, v in counts.items()] + [""]
    for k in CLASS_LABEL:
        group = [e for e in entries if e["classification"] == k]
        if not group:
            continue
        out += [f"## {CLASS_LABEL[k]}", "", "| # | Result | Area | Upstream statement | Lean |", "|---|---|---|---|---|"]
        for i, e in enumerate(group, 1):
            out.append(
                f"| {i} | [{e['title']}](results/{e['slug']}/README.md) | {e['area']} | {upstream_link(e)} "
                f"| [{os.path.basename(e['lean_file'])}]({e['lean_file']}) |"
            )
        out.append("")
    open(os.path.join(ROOT, "CONTENTS.md"), "w").write("\n".join(out))
    write_highlights(entries, counts)
    print(f"wrote CONTENTS.md and {len(entries)} result pages")


if __name__ == "__main__":
    sys.exit(main())
