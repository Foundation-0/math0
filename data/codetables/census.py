"""Census of open entries in Markus Grassl's tables of bounds on linear codes (codetables.de).

For each field GF(q), fetch the colour table, read every (n, k) entry as lower-upper bounds on the minimum distance,
and count the open entries (lower < upper), the entries whose constructions are marked missing, and the gaps.
Writes a summary JSON (committed) and, with --csv, the full entry list (kept local: the tables are Grassl's work;
fetch them yourself rather than redistributing them).

Usage: python census.py [--csv entries.csv] [--from-dir DIR]   (DIR: saved Tables_color.php pages named q<q>.html)
"""
import argparse, csv, datetime, json, os, re, statistics as st, urllib.request
FIELDS = {2: 256, 3: 243, 4: 256, 5: 130, 7: 100, 8: 130, 9: 130}   # max n per field, from the BKLC index page
URL = 'https://www.codetables.de/BKLC/Tables_color.php?q={q}&n0=1&n1={n}&k0=1&k1={n}'
CELL = re.compile(r'<TD([^>]*)>\s*<A[^>]*title="n=(\d+), k=(\d+)"[^>]*>([^<]+)</A>', re.I)

def entries(html):
    for m in CELL.finditer(html):
        attrs, n, k, val = m.groups()
        val = val.strip()
        lo, hi = val.split('-') if '-' in val else (val, val)
        yield int(n), int(k), int(lo), int(hi), 'FFA0A0' in attrs.upper()

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--csv'); ap.add_argument('--from-dir'); a = ap.parse_args()
    out = {'source': 'https://www.codetables.de/BKLC/ (Markus Grassl)', 'retrieved': datetime.date.today().isoformat(), 'fields': {}}
    rows = []
    for q, nmax in FIELDS.items():
        if a.from_dir:
            html = open(os.path.join(a.from_dir, f'q{q}.html'), encoding='latin-1').read()
        else:
            req = urllib.request.Request(URL.format(q=q, n=nmax), headers={'User-Agent': 'foundation0-census'})
            html = urllib.request.urlopen(req, timeout=300).read().decode('latin-1')
        E = list(entries(html)); rows += [(q,) + e for e in E]
        op = [e for e in E if e[2] < e[3]]; gaps = [e[3] - e[2] for e in op]
        f = {'n_max': nmax, 'entries': len(E), 'open': len(op), 'constructions_missing': sum(e[4] for e in E),
             'median_gap': st.median(gaps) if gaps else 0, 'max_gap': max(gaps) if gaps else 0,
             'open_by_n': {f'{lo}-{lo + 49}': sum(lo <= e[0] < lo + 50 for e in op) for lo in range(1, nmax + 1, 50)}}
        if q == 7:
            f['median_gap_n_le_50'] = st.median([g for e, g in zip(op, gaps) if e[0] <= 50] or [0])
            f['median_gap_n_gt_50'] = st.median([g for e, g in zip(op, gaps) if e[0] > 50] or [0])
            f['open_n_gt_50'] = sum(e[0] > 50 for e in op)
        out['fields'][f'GF({q})'] = f
        print(f"GF({q}): {len(E)} entries, {len(op)} open, {f['constructions_missing']} constructions missing, median gap {f['median_gap']}")
    out['open_total'] = sum(f['open'] for f in out['fields'].values())
    out['open_non_binary'] = out['open_total'] - out['fields']['GF(2)']['open']
    print('open non-binary:', out['open_non_binary'])
    json.dump(out, open(f"census-{out['retrieved']}.json", 'w'), indent=1)
    if a.csv:
        with open(a.csv, 'w', newline='') as fh:
            w = csv.writer(fh); w.writerow(['q', 'n', 'k', 'lower', 'upper', 'construction_missing']); w.writerows(rows)

if __name__ == '__main__':
    main()
