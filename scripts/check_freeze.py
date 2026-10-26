#!/usr/bin/env python3
"""Checks on the statements that math0 formalizes itself (lean/Math0/Statements/).

1. Every file listed in FROZEN.sha256 still has its frozen hash.
2. With --base REF: FROZEN.sha256 is append-only. Every line it had at REF is still present,
   unchanged, so a frozen statement cannot be edited together with its hash.
3. Every catalog result whose statement math0 formalized has its statement listed in FROZEN.sha256.
4. With --base REF --order: for each such result that is new since REF, the commit that added the
   statement's FROZEN.sha256 line is a strict ancestor of the commit that added the proof file.
   That is, the statement was committed, and could be reviewed, before the proof existed in the
   repository. Results listed in FROZEN_WITH_PROOF.txt are exempt: they were frozen by the
   pipeline before 2026-10-26 but committed together with their proofs, so git cannot show the order.
"""
import argparse, hashlib, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STMT_DIR = 'lean/Math0/Statements'
FROZEN = f'{STMT_DIR}/FROZEN.sha256'
LEGACY = f'{STMT_DIR}/FROZEN_WITH_PROOF.txt'


def git(*args):
    return subprocess.run(['git', '-C', ROOT, *args], capture_output=True, text=True)


def parse(text):
    out = {}
    for line in text.splitlines():
        if line.strip():
            h, path = line.split()
            out[path] = h
    return out


def first_commit(args):
    r = git('log', '--reverse', '--format=%H', *args)
    commits = r.stdout.split()
    return commits[0] if commits else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', help='git ref to compare against (e.g. origin/main)')
    ap.add_argument('--order', action='store_true', help='also check freeze-before-proof order')
    a = ap.parse_args()
    errors = []
    frozen_text = open(os.path.join(ROOT, FROZEN)).read()
    frozen = parse(frozen_text)

    # 1. hashes
    for path, h in frozen.items():
        p = os.path.join(ROOT, STMT_DIR, path)
        if not os.path.exists(p):
            errors.append(f'{path}: listed in FROZEN.sha256 but missing')
        elif hashlib.sha256(open(p, 'rb').read()).hexdigest() != h:
            errors.append(f'{path}: changed since it was frozen')

    # 2. append-only
    base_frozen = {}
    if a.base:
        if git('rev-parse', '--verify', '--quiet', a.base + '^{commit}').returncode != 0:
            print(f'note: base {a.base} not found; skipping comparisons against it')
            a.base = None
        else:
            r = git('show', f'{a.base}:{FROZEN}')
            base_frozen = parse(r.stdout) if r.returncode == 0 else {}
            for path, h in base_frozen.items():
                if frozen.get(path) != h:
                    errors.append(f'{path}: its FROZEN.sha256 line changed or was removed since {a.base}')

    # 3. every math0-formalized statement is frozen
    cat = json.load(open(os.path.join(ROOT, 'catalog.json')))['results']
    legacy = set(open(os.path.join(ROOT, LEGACY)).read().split())
    ours = [e for e in cat if e.get('statement_origin') == 'math0']
    for e in ours:
        rel = os.path.relpath(e['upstream']['file'], STMT_DIR)
        if rel not in frozen:
            errors.append(f"{e['id']}: statement {rel} is not listed in FROZEN.sha256")

    # 4. freeze before proof
    if a.order and a.base:
        checked = 0
        for e in ours:
            rel = os.path.relpath(e['upstream']['file'], STMT_DIR)
            if rel in base_frozen or rel in legacy or rel not in frozen:
                continue
            line = f'{frozen[rel]}  {rel}'
            fc = first_commit(['-S', line, '--', FROZEN])
            pc = first_commit(['--diff-filter=A', '--', e['lean_file']])
            if not fc or not pc:
                errors.append(f"{e['id']}: cannot find the commits that froze the statement and added the proof")
            elif fc == pc or git('merge-base', '--is-ancestor', fc, pc).returncode != 0:
                errors.append(f"{e['id']}: statement frozen in {fc[:9]}, which is not a strict ancestor "
                              f"of the proof commit {pc[:9]}")
            else:
                checked += 1
        print(f'freeze-before-proof order verified for {checked} new result(s)')

    for err in errors:
        print('error:', err)
    if errors:
        sys.exit(1)
    print(f'OK: {len(frozen)} frozen statements unchanged; {len(ours)} results use them')


if __name__ == '__main__':
    main()
