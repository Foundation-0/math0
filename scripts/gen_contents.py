#!/usr/bin/env python3
"""Generate CONTENTS.md and results/<slug>/README.md from catalog.json.

catalog.json is the single source of truth for what math0 claims. Every entry points at a Lean
file whose final command (#math0_proves / #math0_refutes / #math0_answers) is re-checked by CI.
"""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO_URL = "https://github.com/Foundation-0/math0"
FC_URL = "https://github.com/google-deepmind/formal-conjectures"

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
}


MODE_NOTE = {
    "proves": "",
    "refutes": " (negated)",
    "answers": " with its unknown replaced by an explicit value",
    "refutes_every_answer": " negated and universally quantified over the unknown",
}


def upstream_link(e):
    u = e["upstream"]
    return f"[`{u['decl']}`]({FC_URL}/blob/{u['commit']}/{u['file']})"


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
        f"The Lean file [`{e['lean_file']}`](../../{e['lean_file']}) {VERB[e['mode']]} the upstream statement "
        f"{upstream_link(e)} (formal-conjectures at commit `{u['commit'][:7]}`, upstream category "
        f"`{u['category']}`). Its final command `#math0_{e['mode']}` checks that our theorem's type is "
        f"syntactically identical to the upstream statement{MODE_NOTE[e['mode']]} "
        "and that the proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.",
        "",
    ]
    if e.get("notes"):
        lines += ["## Notes", "", e["notes"], ""]
    if os.path.exists(os.path.join(ROOT, "results", e["slug"], "paper.pdf")):
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
    print(f"wrote CONTENTS.md and {len(entries)} result pages")


if __name__ == "__main__":
    sys.exit(main())
