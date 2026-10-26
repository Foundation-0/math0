# Census of open entries in codetables.de (linear codes)

Supporting data for [AREAS.md](../../AREAS.md) §1. It is a snapshot of [codetables.de](https://www.codetables.de),
Markus Grassl's tables of bounds on the minimum distance of linear codes, taken on 18 Oct 2026.

| File | What |
|---|---|
| `census.py` | Fetches each field's table and counts entries, open entries (lower bound < upper bound), entries whose constructions are marked missing, and gap sizes. `--csv FILE` also writes the full entry list for local use. |
| `census-2026-10-18.json` | The counts on 18 Oct 2026. |
| `last-modified-sample-2026-10-18.json` | "Last modified" dates for 210 random entries, 30 per field. |

**Open entries on 18 Oct 2026.**

| Field | Open entries |
|---|---|
| GF(2) | 25,859 |
| GF(3) | 25,684 |
| GF(4) | 29,374 |
| GF(5) | 7,056 |
| GF(7) | 4,071 |
| GF(8) | 7,202 |
| GF(9) | 7,265 |

- **80,652** open entries in the non-binary fields.
- 19,318 non-binary entries are marked "constructions missing".
- For GF(7), the median gap is 3 for n ≤ 50 and 9 for n > 50 (3,296 open entries); the maintainer calls the upper
  bounds for n > 50 "rather weak".
- In the date sample, 77% of the 210 entries were last changed in 2001–2009, 4% in 2025–26, and 24 carry no date.

**Why the full table is not here.** The tables are Grassl's compilation. Run `python census.py --csv entries.csv`
to get your own copy, and send improvements to him at codes@codetables.de. Re-running the census later shows which
entries have moved, and so who else is working on them.
