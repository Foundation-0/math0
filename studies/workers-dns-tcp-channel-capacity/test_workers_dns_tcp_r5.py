#!/usr/bin/env python3
"""R5 Mutation-Killing & Adversarial Verification Suite for AUDIT-075 (Arm R8-4).

Zero bare `assert` statements. Pure Python 3 stdlib `unittest`.
Designed to achieve 100.0% R5 kill rate under `aletheia v1.4.0 mutate --add-cwd`.
"""

from __future__ import annotations

import json
import struct
import sys
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from typing import Any

_THIS_DIR = str(Path(__file__).resolve().parent)
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

import workers_dns_tcp_audit as mod


def _assert_no_floats(obj: Any, tc: unittest.TestCase, path: str = "root") -> None:
    tc.assertNotIsInstance(obj, float, f"Float leaked at {path}: {obj!r}")
    if isinstance(obj, dict):
        for k, v in obj.items():
            _assert_no_floats(v, tc, f"{path}.{k}")
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            _assert_no_floats(v, tc, f"{path}[{i}]")


def _build_valid_query(
    qname_labels: list[bytes] | None = None,
    qtype: int = 1,
    qclass: int = 1,
    flags: int = 0x0100,
    arcount: int = 0,
    extra: bytes = b"",
    qid: int = 42,
    qdcount: int = 1,
    ancount: int = 0,
    nscount: int = 0,
) -> bytes:
    labels = [b"example", b"test"] if qname_labels is None else qname_labels
    body = mod.encode_dns_name(labels) + struct.pack("!HH", qtype, qclass) + extra
    return mod.build_raw_dns_packet(qid, flags, qdcount, ancount, nscount, arcount, body)


class TestExactMathAndHelpers(unittest.TestCase):
    def test_exact_int_and_decimal_floor_guards(self) -> None:
        self.assertEqual(mod.frac_str(Fraction(6, 4)), "3/2")
        self.assertEqual(mod.frac_decimal_floor(Fraction(0, 1), 0), "0")
        self.assertEqual(mod.frac_decimal_floor(Fraction(-7, 2), 2), "-3.50")
        self.assertEqual(mod.frac_decimal_floor(Fraction(5, 2), 0), "2")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_EXACT_INT"):
            mod.frac_decimal_floor(Fraction(1, 2), True)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_DIGITS"):
            mod.frac_decimal_floor(Fraction(1, 2), -1)

    def test_exact_log2_int_and_fraction_brackets(self) -> None:
        # Exact power of 2 boundary (value=1 -> log2=0, value=8 -> log2=3)
        b1 = mod.exact_log2_int_bracket(1, 1)
        self.assertTrue(b1["exact_power_of_two"])
        self.assertEqual(b1["lower_frac"], "0/1")
        self.assertEqual(b1["upper_frac"], "0/1")
        b8 = mod.exact_log2_int_bracket(8, 10)
        self.assertTrue(b8["exact_power_of_two"])
        self.assertEqual(b8["lower_frac"], "3/1")
        b3 = mod.exact_log2_int_bracket(3, 100)
        self.assertFalse(b3["exact_power_of_two"])
        self.assertEqual(b3["lower_dec"], "1.580")
        self.assertEqual(b3["upper_dec"], "1.590")

        with self.assertRaisesRegex(ValueError, "WDT_ERR_EXACT_INT"):
            mod.exact_log2_int_bracket(True, 10)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LOG_DOMAIN"):
            mod.exact_log2_int_bracket(0, 10)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LOG_SCALE"):
            mod.exact_log2_int_bracket(2, 0)

        # Fraction bracket boundaries
        bf1 = mod.exact_log2_fraction_bracket(4, 2, 10)
        self.assertTrue(bf1["exact_power_of_two"])
        self.assertEqual(bf1["lower_frac"], "1/1")
        bf_eq = mod.exact_log2_fraction_bracket(5, 5, 1)
        self.assertEqual(bf_eq["lower_frac"], "0/1")
        bf_adj = mod.exact_log2_fraction_bracket(3, 2, 100)
        self.assertFalse(bf_adj["exact_power_of_two"])
        self.assertEqual(bf_adj["lower_dec"], "0.580")
        bf_shift_up = mod.exact_log2_fraction_bracket(7, 4, 10)
        self.assertEqual(bf_shift_up["lower_frac"], "4/5")

        with self.assertRaisesRegex(ValueError, "WDT_ERR_LOG_DEN"):
            mod.exact_log2_fraction_bracket(2, 0, 10)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LOG_RATIO"):
            mod.exact_log2_fraction_bracket(2, 3, 10)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LOG_SCALE"):
            mod.exact_log2_fraction_bracket(2, 1, 0)

    def test_count_valid_prompt_strings_guards_and_values(self) -> None:
        c1, tot1 = mod.count_valid_prompt_strings(1, 1)
        self.assertEqual((c1, tot1), ([0, 1], 1))
        c2, tot2 = mod.count_valid_prompt_strings(2, 3)
        self.assertEqual((c2, tot2), ([0, 2, 4, 12], 18))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_ALPHABET"):
            mod.count_valid_prompt_strings(0, 3)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MAX_LEN"):
            mod.count_valid_prompt_strings(2, 0)


class TestGitHeadAndAnchorVerifiers(unittest.TestCase):
    def test_resolve_git_head_sha_all_formats_and_failures(self) -> None:
        fake_sha = "a" * 40
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            with self.assertRaisesRegex(ValueError, "WDT_ERR_GIT_HEAD_MISSING"):
                mod.resolve_git_head_sha(root)

            git_dir = root / ".git"
            git_dir.mkdir()
            # Detached HEAD
            (git_dir / "HEAD").write_text(fake_sha + "\n", encoding="utf-8")
            self.assertEqual(mod.resolve_git_head_sha(root), fake_sha)

            # Loose ref
            (git_dir / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")
            (git_dir / "refs" / "heads").mkdir(parents=True)
            (git_dir / "refs" / "heads" / "main").write_text("b" * 40 + "\n", encoding="utf-8")
            self.assertEqual(mod.resolve_git_head_sha(root), "b" * 40)

            # Packed ref fallback
            (git_dir / "refs" / "heads" / "main").unlink()
            (git_dir / "packed-refs").write_text(
                "# pack-refs\n"
                "^" + ("0" * 40) + "\n"
                + ("c" * 40) + " refs/heads/other\n"
                + ("d" * 40) + " refs/heads/main\n",
                encoding="utf-8",
            )
            self.assertEqual(mod.resolve_git_head_sha(root), "d" * 40)

            # Missing ref in packed-refs -> invalid SHA
            (git_dir / "packed-refs").write_text("# empty\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_GIT_SHA_INVALID"):
                mod.resolve_git_head_sha(root)

            # Corrupt detached SHA
            (git_dir / "HEAD").write_text("not-a-sha\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_GIT_SHA_INVALID"):
                mod.resolve_git_head_sha(root)

            # Path traversal / non-refs symbolic ref
            (git_dir / "HEAD").write_text("ref: ../outside\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_GIT_REF_INVALID"):
                mod.resolve_git_head_sha(root)
            (git_dir / "HEAD").write_text("ref: refs/heads/../secret\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_GIT_REF_INVALID"):
                mod.resolve_git_head_sha(root)

    def test_verify_upstream_repo_and_warp_server_failures(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            git_dir = root / ".git"
            git_dir.mkdir()
            (git_dir / "HEAD").write_text(("1" * 40) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_HEAD_MISMATCH"):
                mod.verify_upstream_repo_anchors(root)

            (git_dir / "HEAD").write_text(mod.PINNED_REPO_HEAD + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_FILE_MISSING"):
                mod.verify_upstream_repo_anchors(root)

            # Create all files with wrong content to trigger hash mismatch
            for rel in mod.EXPECTED_REPO_FILES:
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(b"bad")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_FILE_HASH_MISMATCH"):
                mod.verify_upstream_repo_anchors(root)

            # Missing warp server.py
            with self.assertRaisesRegex(ValueError, "WDT_ERR_WARP_SERVER_MISSING"):
                mod.verify_warp_server_anchors(root / "missing.py")

            bad_srv = root / "server.py"
            bad_srv.write_text("# wrong\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "WDT_ERR_WARP_SERVER_HASH"):
                mod.verify_warp_server_anchors(bad_srv)

            # Direct verbatim anchor helper boundary tests
            sample = root / "a.txt"
            sample.write_text("line1\n  line2  \n", encoding="utf-8")
            self.assertEqual(mod.check_verbatim_anchors(root, [("a.txt", 1, "line1"), ("a.txt", 2, "line2")]), 2)
            with self.assertRaisesRegex(ValueError, "WDT_ERR_ANCHOR_FILE_MISSING"):
                mod.check_verbatim_anchors(root, [("nope.txt", 1, "line1")])
            with self.assertRaisesRegex(ValueError, "WDT_ERR_ANCHOR_LINE_OOB"):
                mod.check_verbatim_anchors(root, [("a.txt", 0, "line1")])
            with self.assertRaisesRegex(ValueError, "WDT_ERR_ANCHOR_LINE_OOB"):
                mod.check_verbatim_anchors(root, [("a.txt", 3, "line2")])
            with self.assertRaisesRegex(ValueError, "WDT_ERR_ANCHOR_MISMATCH"):
                mod.check_verbatim_anchors(root, [("a.txt", 1, "wrong")])


class TestWireBuildersAndTcpBudgetGate(unittest.TestCase):
    def test_encode_dns_name_and_raw_packet_guards(self) -> None:
        self.assertEqual(mod.encode_dns_name([]), b"\x00")
        self.assertEqual(len(mod.encode_dns_name([b"a" * 63])), 65)
        max255 = mod.encode_dns_name([b"a" * 63, b"b" * 63, b"c" * 63, b"d" * 61])
        self.assertEqual(len(max255), 255)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LABEL_TYPE"):
            mod.encode_dns_name(["abc"])  # type: ignore[list-item]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LABEL_LEN"):
            mod.encode_dns_name([b""])
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LABEL_LEN"):
            mod.encode_dns_name([b"a" * 64])
        with self.assertRaisesRegex(ValueError, "WDT_ERR_NAME_LEN"):
            mod.encode_dns_name([b"a" * 63, b"b" * 63, b"c" * 63, b"d" * 62])

        pkt = mod.build_raw_dns_packet(0, 0, 0, 0, 0, 65535, b"")
        self.assertEqual(len(pkt), 12)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_U16_RANGE"):
            mod.build_raw_dns_packet(-1, 0, 0, 0, 0, 0, b"")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_U16_RANGE"):
            mod.build_raw_dns_packet(65536, 0, 0, 0, 0, 0, b"")

    def test_validate_tcp_frame_and_budget_exact_boundaries(self) -> None:
        # Exact passing boundaries
        ok_min = mod.validate_tcp_frame_and_budget(12, 0, 0, 12, 1, 1)
        self.assertEqual(ok_min, {"admitted_length": 12, "next_query_index": 1, "remaining_conn_ms": 1})
        ok_max = mod.validate_tcp_frame_and_budget(65535, 31, 29999, 65535, 32, 30000)
        self.assertEqual(ok_max["admitted_length"], 65535)

        # Config guard boundaries
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CFG_FRAME_CAP"):
            mod.validate_tcp_frame_and_budget(12, 0, 0, 11, 1, 100)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CFG_FRAME_CAP"):
            mod.validate_tcp_frame_and_budget(12, 0, 0, 65536, 1, 100)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CFG_QUERY_CAP"):
            mod.validate_tcp_frame_and_budget(12, 0, 0, 512, 0, 100)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CFG_CONN_CAP"):
            mod.validate_tcp_frame_and_budget(12, 0, 0, 512, 1, 0)

        # Runtime frame & budget guard boundaries (WDT-04, WDT-05)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_FRAME_TOO_SHORT"):
            mod.validate_tcp_frame_and_budget(11, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_FRAME_TOO_LARGE"):
            mod.validate_tcp_frame_and_budget(4097, 0, 0, max_query_bytes=4096)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CONN_QUERY_CAP"):
            mod.validate_tcp_frame_and_budget(64, -1, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CONN_QUERY_CAP"):
            mod.validate_tcp_frame_and_budget(64, 32, 0, max_queries=32)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CONN_LIFETIME"):
            mod.validate_tcp_frame_and_budget(64, 0, -1)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CONN_LIFETIME"):
            mod.validate_tcp_frame_and_budget(64, 0, 30000, max_conn_ms=30000)


class TestHardenedDnsQueryParserR5(unittest.TestCase):
    def test_valid_queries_and_edns_opt(self) -> None:
        # Standard A IN query + RD + CD
        pkt = _build_valid_query(flags=0x0110)
        parsed = mod.parse_hardened_dns_query(pkt)
        self.assertEqual(parsed["qname"], "example.test")
        self.assertTrue(parsed["rd"])
        self.assertTrue(parsed["cd"])
        self.assertIsNone(parsed["opt"])

        # QCLASS ANY (255) + valid OPT with EDNS option + non-alnum escaped label
        opt_rr = b"\x00" + struct.pack("!HHBBHHHH", 41, 1232, 0, 0, 0x8000, 6, 65001, 2) + b"ab"
        pkt2 = _build_valid_query(qname_labels=[b"a.b", b"test"], qclass=255, arcount=1, extra=opt_rr)
        parsed2 = mod.parse_hardened_dns_query(pkt2, max_additional_rrs=2)
        self.assertEqual(parsed2["qname"], "a\\046b.test")
        self.assertEqual(parsed2["qclass"], 255)
        self.assertTrue(parsed2["opt"]["dnssecOk"])

        # Valid compression pointer from TSIG/SIG owner targeting prior QNAME offset 12 (rejected as signed)
        tsig_rr = struct.pack("!HHHIH", 0xC00C, 250, 255, 0, 0)
        pkt_tsig = _build_valid_query(arcount=1, extra=tsig_rr)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_SIGNED_REFUSED"):
            mod.parse_hardened_dns_query(pkt_tsig)
        sig_rr = struct.pack("!HHHIH", 0xC00C, 24, 1, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_SIGNED_REFUSED"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=sig_rr))
        # TSIG/SIG(0) not last additional RR
        opt_after = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 0, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TSIG_NOT_LAST"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=2, extra=tsig_rr + opt_after))

    def test_header_and_config_refusals(self) -> None:
        with self.assertRaisesRegex(ValueError, "WDT_ERR_WIRE_TYPE"):
            mod.parse_hardened_dns_query("not-bytes")  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CFG_ARCOUNT"):
            mod.parse_hardened_dns_query(_build_valid_query(), max_additional_rrs=-1)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_CFG_ARCOUNT"):
            mod.parse_hardened_dns_query(_build_valid_query(), max_additional_rrs=3)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_HDR_LEN"):
            mod.parse_hardened_dns_query(b"\x00" * 11)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_HDR_LEN"):
            mod.parse_hardened_dns_query(b"\x00" * 65536)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_QR_RESPONSE"):
            mod.parse_hardened_dns_query(_build_valid_query(flags=0x8000))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_OPCODE"):
            mod.parse_hardened_dns_query(_build_valid_query(flags=0x2800))  # UPDATE=5
        # WDT-03 dirty query bits (AA, TC, RA, Z, RCODE)
        for bit in (0x0400, 0x0200, 0x0080, 0x0040, 0x0005):
            with self.assertRaisesRegex(ValueError, "WDT_ERR_DIRTY_HEADER"):
                mod.parse_hardened_dns_query(_build_valid_query(flags=bit))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_SECTION_COUNTS"):
            mod.parse_hardened_dns_query(_build_valid_query(qdcount=0))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_SECTION_COUNTS"):
            mod.parse_hardened_dns_query(_build_valid_query(ancount=1))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_SECTION_COUNTS"):
            mod.parse_hardened_dns_query(_build_valid_query(nscount=1))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_ARCOUNT_CAP"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=3))
        # WDT-01 bomb rejected immediately at ARCOUNT cap
        bomb = mod.build_wdt01_additional_rr_bomb(include_pointer_chain=False)["wire"]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_ARCOUNT_CAP"):
            mod.parse_hardened_dns_query(bomb)

    def test_name_pointer_qtype_qclass_and_opt_refusals(self) -> None:
        # Truncated name / truncated pointer / header-target pointer / forward pointer / RDATA-target pointer
        with self.assertRaisesRegex(ValueError, "WDT_ERR_NAME_TRUNC"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b""))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_PTR_TRUNC"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\xc0"))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_PTR_BOUNDS"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\xc0\x00\x00\x01\x00\x01"))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_PTR_BOUNDS"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\xc0\x0c\x00\x01\x00\x01"))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_LABEL_EXT"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\x40\x00\x00\x01\x00\x01"))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_NAME_OVERFLOW"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\x10abc"))
        # > 255 byte total wire name
        long_labels = (b"\x3f" + b"a" * 63) * 4 + b"\x01z\x00\x00\x01\x00\x01"
        with self.assertRaisesRegex(ValueError, "WDT_ERR_NAME_OVERFLOW"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, long_labels))

        # Pointer into RDATA (offset inside OPT RDATA rather than a prior domain name!)
        opt_with_rdata = b"\x00" + struct.pack("!HHBBHHHH", 41, 1232, 0, 0, 0, 6, 65001, 2) + b"\x00\x00"
        # Offset of the hidden \x00 inside OPT RDATA: 12 + 14 (example.test) + 4 + 11 + 4 = 45
        rdata_ptr_rr = struct.pack("!HHHIH", 0xC000 | 45, 250, 1, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_PTR_RDATA_TARGET"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=2, extra=opt_with_rdata + rdata_ptr_rr))

        # > 16 compression jumps rejected cleanly (direct helper boundary test)
        # Chain 17 backward pointers in valid_targets
        buf = bytearray(b"\x00" * 12)
        vt: set[int] = set()
        buf.append(0)  # offset 12: root
        vt.add(12)
        prev = 12
        for _ in range(17):
            cur_off = len(buf)
            buf.extend(struct.pack("!H", 0xC000 | prev))
            vt.add(cur_off)
            prev = cur_off
        with self.assertRaisesRegex(ValueError, "WDT_ERR_PTR_BOUNDS"):
            mod._parse_hardened_name(bytes(buf), prev, vt, collect_name=False)

        # Truncated QTYPE/QCLASS, meta QTYPE, foreign QCLASS
        with self.assertRaisesRegex(ValueError, "WDT_ERR_Q_TRUNC"):
            mod.parse_hardened_dns_query(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\x00\x00\x01"))
        for mt in (0, 41, 249, 250):
            with self.assertRaisesRegex(ValueError, "WDT_ERR_META_QTYPE"):
                mod.parse_hardened_dns_query(_build_valid_query(qtype=mt))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_QCLASS"):
            mod.parse_hardened_dns_query(_build_valid_query(qclass=3))

        # Additional RR header/rdata truncation, duplicate OPT, non-root OPT, BADVERS, malformed EDNS options, unexpected RR, trailing bytes
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RR_TRUNC"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=b"\x00\x00\x29"))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RDATA_TRUNC"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=b"\x00" + struct.pack("!HHIH", 41, 1232, 0, 5)))
        opt_ok = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 0, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_DUP_OPT"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=2, extra=opt_ok + opt_ok))
        nonroot_opt = b"\x01a\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 0, 0x8000, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_OPT_OWNER"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=nonroot_opt))
        badvers_opt = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 1, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_EDNS_BADVERS"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=badvers_opt))
        trunc_edns_opt = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 0, 0, 2) + b"\x00\x01"
        with self.assertRaisesRegex(ValueError, "WDT_ERR_EDNS_OPT_TRUNC"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=trunc_edns_opt))
        overflow_edns_opt = b"\x00" + struct.pack("!HHBBHHHH", 41, 1232, 0, 0, 0, 4, 65001, 3)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_EDNS_OPT_OVERFLOW"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=overflow_edns_opt))
        bogus_a_rr = b"\x00" + struct.pack("!HHIH", 1, 1, 0, 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_UNEXPECTED_ADDITIONAL"):
            mod.parse_hardened_dns_query(_build_valid_query(arcount=1, extra=bogus_a_rr))
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TRAILING_BYTES"):
            mod.parse_hardened_dns_query(_build_valid_query(extra=b"\x00"))


class TestAskNamespaceSanitizerAndBridgeR5(unittest.TestCase):
    def test_validate_ask_namespace_and_prompt_boundaries(self) -> None:
        # Exact aligned routing
        self.assertEqual(mod.validate_ask_namespace_and_prompt("ask.example.test", "TXT", "ask.example.test", "example.test")["route"], "ask_help")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("ask.example.test", "SOA", "ask.example.test", "example.test")["route"], "apex_authority")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("ask.example.test", "NS", "ask.example.test", "example.test")["route"], "apex_authority")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("ask.example.test", "A", "ask.example.test", "example.test")["route"], "nodata_soa")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("example.test", "A", "ask.example.test", "example.test")["route"], "static_zone")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("www.example.test", "A", "ask.example.test", "example.test")["route"], "static_zone")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("ask.southpolesteve.com", "SOA", "ask.southpolesteve.com", "ask.southpolesteve.com")["route"], "apex_authority")
        res_ask = mod.validate_ask_namespace_and_prompt("why-sky-blue.ask.example.test", "TXT", "ask.example.test", "example.test")
        self.assertEqual(res_ask["prompt"], "why sky blue")
        self.assertEqual(mod.validate_ask_namespace_and_prompt("why-sky-blue.ask.example.test", "A", "ask.example.test", "example.test")["route"], "nodata_soa")
        # Exact 63-char boundary succeeds
        res_63 = mod.validate_ask_namespace_and_prompt(("a" * 63) + ".ask.example.test", "TXT", "ask.example.test", "example.test")
        self.assertEqual(res_63["label_len"], 63)

        # Refusal guards
        with self.assertRaisesRegex(ValueError, "WDT_ERR_ASK_TYPE"):
            mod.validate_ask_namespace_and_prompt(123, "TXT", "ask.example.test", "example.test")  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_ASK_CFG_TYPE"):
            mod.validate_ask_namespace_and_prompt("ask.example.test", "TXT", None, "example.test")  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_UNSTRIPPED_NAME"):
            mod.validate_ask_namespace_and_prompt(" ask.example.test", "TXT", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_INVALID_QTYPE"):
            mod.validate_ask_namespace_and_prompt("ask.example.test", "txt", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_INVALID_QTYPE"):
            mod.validate_ask_namespace_and_prompt("ask.example.test", " TXT ", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_EMPTY_NAME"):
            mod.validate_ask_namespace_and_prompt(".", "TXT", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MALFORMED_DOTS"):
            mod.validate_ask_namespace_and_prompt("a..ask.example.test", "TXT", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MALFORMED_DOTS"):
            mod.validate_ask_namespace_and_prompt(".ask.example.test", "TXT", "ask.example.test", "example.test")
        # WDT-BYPASS-02a: multiple trailing dots rejected; single trailing dot accepted
        self.assertEqual(
            mod.validate_ask_namespace_and_prompt("hello.ask.example.test.", "TXT", "ask.example.test.", "example.test.")["route"],
            "llm_ask",
        )
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MALFORMED_DOTS"):
            mod.validate_ask_namespace_and_prompt("hello.ask.example.test...", "TXT", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MALFORMED_DOTS"):
            mod.validate_ask_namespace_and_prompt("hello.ask.example.test..", "TXT", "ask.example.test", "example.test")
        # Exact 253-char DNS name boundary & >253 rejection
        long_254 = ("a" * 63 + ".") * 3 + ("b" * 51) + ".example.test"  # 64*3+52+12 = 256 > 253
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MALFORMED_DOTS"):
            mod.validate_ask_namespace_and_prompt(long_254, "A", "ask.example.test", "example.test")
        # WDT-BYPASS-02b: invalid chars / control bytes / spaces in static_zone rejected
        with self.assertRaisesRegex(ValueError, "WDT_ERR_INVALID_LABEL_CHARS"):
            mod.validate_ask_namespace_and_prompt("bad\x00label\nwith spaces.example.test", "A", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_INVALID_LABEL_CHARS"):
            mod.validate_ask_namespace_and_prompt(("a" * 64) + ".example.test", "A", "ask.example.test", "example.test")
        # WDT-06 production mismatch rejected fail-closed!
        with self.assertRaisesRegex(ValueError, "WDT_ERR_NAMESPACE_MISMATCH"):
            mod.validate_ask_namespace_and_prompt("ask.southpolesteve.com", "TXT", "ask.southpolesteve.com", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_OUT_OF_ZONE"):
            mod.validate_ask_namespace_and_prompt("other.test", "A", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_MULTILABEL_PROMPT"):
            mod.validate_ask_namespace_and_prompt("a.b.ask.example.test", "TXT", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_INVALID_LABEL_CHARS"):
            mod.validate_ask_namespace_and_prompt(("a" * 64) + ".ask.example.test", "TXT", "ask.example.test", "example.test")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_PROMPT_SYNTAX"):
            mod.validate_ask_namespace_and_prompt("bad--slug.ask.example.test", "TXT", "ask.example.test", "example.test")

    def test_sanitize_llm_txt_response_boundaries(self) -> None:
        # Multi-chunk UTF-8 emoji boundary (254 'a' + 4-byte emoji -> 2 chunks without splitting UTF-8)
        ok = mod.sanitize_llm_txt_response("a" * 254 + "\U0001f324 blue\tsky.", 87)
        self.assertEqual(ok["chunk_count"], 2)
        self.assertEqual(ok["max_chunk_bytes"], 254)
        self.assertEqual(ok["sanitized_text"], "a" * 254 + "\U0001f324 blue sky.")
        # Exact payload cap equality (kills > vs >=) and exact 65535 uncompressed DNS-0x20 TCP reply fit (kills > vs >=)
        self.assertEqual(mod.sanitize_llm_txt_response("abcd", 87, max_payload_bytes=4)["utf8_bytes"], 4)
        exact_tcp = mod.sanitize_llm_txt_response("a" * 65066, 88, max_payload_bytes=65279)
        self.assertEqual(exact_tcp["tcp_wire_bytes_uncompressed_with_opt"], 65535)
        # WDT-BYPASS-03: 65,788-byte uncompressed DNS-0x20 overflow rejected even when compressed fits 65,535!
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TCP_REPLY_OVERFLOW"):
            mod.sanitize_llm_txt_response("x" * (254 * 255 + 216), 255, max_payload_bytes=65279)

        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_TYPE"):
            mod.sanitize_llm_txt_response(b"hi", 87)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_QNAME_WIRE_LEN"):
            mod.sanitize_llm_txt_response("hi", 0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_QNAME_WIRE_LEN"):
            mod.sanitize_llm_txt_response("hi", 256)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_CAP_RANGE"):
            mod.sanitize_llm_txt_response("hi", 87, max_payload_bytes=0)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_CAP_RANGE"):
            mod.sanitize_llm_txt_response("hi", 87, max_payload_bytes=65280)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_CTRL_CHAR"):
            mod.sanitize_llm_txt_response("hello\x1b[31mred", 87)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_CTRL_CHAR"):
            mod.sanitize_llm_txt_response("hello\x7f", 87)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_CTRL_CHAR"):
            mod.sanitize_llm_txt_response("hello\x85world", 87)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_FORMAT_CHAR"):
            mod.sanitize_llm_txt_response("hello\u202eworld", 87)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_FORMAT_CHAR"):
            mod.sanitize_llm_txt_response("\u200bv=spf1 +all", 87)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_EMPTY"):
            mod.sanitize_llm_txt_response(" \t\n\r ", 87)
        for smuggle in (
            "v=spf1 +all",
            '"v=spf1 +all"',
            '" v=spf2.0/pra +all"',
            "Answer: v=spf1 +all",
            "V=DMARC1; p=none",
            "google-site-verification=abc",
            '" google-site-verification=EVIL_TOKEN"',
            "[google-site-verification=EVIL_TOKEN]",
            "prefix apple-domain-verification=xyz",
            "note _acme-challenge token",
            '" ms=ms12345678"',
            "token: ms=ms999",
        ):
            with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_POLICY_SMUGGLE"):
                mod.sanitize_llm_txt_response(smuggle, 87)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_TXT_TOO_LARGE"):
            mod.sanitize_llm_txt_response("x" * 4097, 87, max_payload_bytes=4096)

    def test_compression_and_warp_rpc_contract_boundaries(self) -> None:
        c = mod.check_case_insensitive_compression_savings(39, 2)
        self.assertEqual(c["total_bytes_saved"], 74)
        self.assertEqual(mod.check_case_insensitive_compression_savings(3, 1)["bytes_saved_per_rr"], 1)
        self.assertEqual(mod.check_case_insensitive_compression_savings(255, 1)["bytes_saved_per_rr"], 253)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_COMPRESS_QNAME"):
            mod.check_case_insensitive_compression_savings(2, 1)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_COMPRESS_QNAME"):
            mod.check_case_insensitive_compression_savings(256, 1)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_COMPRESS_RR_COUNT"):
            mod.check_case_insensitive_compression_savings(39, 0)

        w_ok = mod.check_warp_rpc_frame_contract(2, True, 100, 2, 0o600)
        self.assertTrue(w_ok["admitted"])
        w_max = mod.check_warp_rpc_frame_contract(2048, True, 60000, 2048, 0o770)
        self.assertEqual(w_max["socket_mode_octal"], "0o770")
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_TIMEOUT_FLAG"):
            mod.check_warp_rpc_frame_contract(10, 1, 1000)  # type: ignore[arg-type]
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_MAX_FRAME"):
            mod.check_warp_rpc_frame_contract(10, True, 1000, max_frame_bytes=1)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_FRAME_SIZE"):
            mod.check_warp_rpc_frame_contract(1, True, 1000)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_FRAME_SIZE"):
            mod.check_warp_rpc_frame_contract(2049, True, 1000, max_frame_bytes=2048)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_SOCKET_MODE"):
            mod.check_warp_rpc_frame_contract(10, True, 1000, socket_mode=-1)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_SOCKET_MODE"):
            mod.check_warp_rpc_frame_contract(10, True, 1000, socket_mode=0o1000)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_SOCKET_MODE"):
            mod.check_warp_rpc_frame_contract(10, True, 1000, socket_mode=0o604)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_SERVER_TIMEOUT"):
            mod.check_warp_rpc_frame_contract(10, False, 1000)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_SERVER_TIMEOUT"):
            mod.check_warp_rpc_frame_contract(10, True, 99)
        with self.assertRaisesRegex(ValueError, "WDT_ERR_RPC_SERVER_TIMEOUT"):
            mod.check_warp_rpc_frame_contract(10, True, 60001)


class TestEndToEndLiveAndStandaloneAudit(unittest.TestCase):
    def test_upstream_model_all_branches_r5(self) -> None:
        # Exact 12-byte boundary (len == 12 is NOT < 12; QD=0 -> FORMERR, whereas len == 11 -> close_no_reply)
        self.assertEqual(mod.simulate_upstream_query_model(b"\x00" * 11)["action"], "close_no_reply")
        self.assertEqual(mod.simulate_upstream_query_model(b"\x00" * 12)["rcode"], "FORMERR")
        self.assertEqual(mod.simulate_upstream_query_model(_build_valid_query(flags=0x8000))["action"], "close_no_reply")
        self.assertEqual(mod.simulate_upstream_query_model(_build_valid_query(flags=0x2800))["rcode"], "NOTIMP")
        self.assertEqual(mod.simulate_upstream_query_model(_build_valid_query(qdcount=0))["rcode"], "FORMERR")

        # parse_name_upstream_model truncation, pointer, & label overflow boundaries
        with self.assertRaisesRegex(ValueError, "UPSTREAM_FORMERR"):
            mod.parse_name_upstream_model(b"\x00" * 12, 12)
        with self.assertRaisesRegex(ValueError, "UPSTREAM_FORMERR"):
            mod.parse_name_upstream_model(b"\x00" * 12 + b"\xc0", 12)
        with self.assertRaisesRegex(ValueError, "UPSTREAM_FORMERR"):
            mod.parse_name_upstream_model(b"\x00" * 12 + b"\xc0\x00", 12)
        with self.assertRaisesRegex(ValueError, "UPSTREAM_FORMERR"):
            mod.parse_name_upstream_model(b"\x00" * 12 + b"\x40" + b"a" * 64 + b"\x00", 12)
        with self.assertRaisesRegex(ValueError, "UPSTREAM_FORMERR"):
            mod.parse_name_upstream_model(b"\x00" * 12 + b"\x05ab", 12)

        # Truncated question QTYPE/QCLASS
        self.assertEqual(
            mod.simulate_upstream_query_model(mod.build_raw_dns_packet(1, 0, 1, 0, 0, 0, b"\x00\x00\x01"))["rcode"],
            "FORMERR",
        )
        # Authority section (IXFR SOA valid vs non-IXFR vs truncated auth header vs non-SOA vs rdata overflow)
        soa_rr = b"\x00" + struct.pack("!HHIH", 6, 1, 60, 0)
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(qtype=251, nscount=1, extra=soa_rr))["rcode"],
            "NOERROR",
        )
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(qtype=1, nscount=1, extra=soa_rr))["rcode"],
            "FORMERR",
        )
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(qtype=251, nscount=1, extra=b"\x00\x00\x06"))["rcode"],
            "FORMERR",
        )
        bad_auth_type = b"\x00" + struct.pack("!HHIH", 1, 1, 60, 0)
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(qtype=251, nscount=1, extra=bad_auth_type))["rcode"],
            "FORMERR",
        )
        trunc_auth_rdata = b"\x00" + struct.pack("!HHIH", 6, 1, 60, 4) + b"\x00"
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(qtype=251, nscount=1, extra=trunc_auth_rdata))["rcode"],
            "FORMERR",
        )

        # Additional section truncation, duplicate OPT, valid EDNS option, truncated/overflow EDNS option, BADVERS, TSIG, trailing bytes
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=b"\x00\x00\x29"))["rcode"],
            "FORMERR",
        )
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=b"\x00" + struct.pack("!HHIH", 41, 1232, 0, 5)))["rcode"],
            "FORMERR",
        )
        opt_ok = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 0, 0, 0)
        dup = mod.simulate_upstream_query_model(_build_valid_query(arcount=2, extra=opt_ok + opt_ok))
        self.assertEqual(dup["rcode"], "FORMERR")
        self.assertTrue(dup["emits_opt"])
        opt_with_tlv = b"\x00" + struct.pack("!HHBBHHHH", 41, 1232, 0, 0, 0, 4, 65001, 0)
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=opt_with_tlv))["rcode"],
            "NOERROR",
        )
        opt_trunc_tlv = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 0, 0, 2) + b"\x00\x01"
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=opt_trunc_tlv))["rcode"],
            "FORMERR",
        )
        opt_ovf_tlv = b"\x00" + struct.pack("!HHBBHHHH", 41, 1232, 0, 0, 0, 4, 65001, 3)
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=opt_ovf_tlv))["rcode"],
            "FORMERR",
        )
        opt_badvers = b"\x00" + struct.pack("!HHBBHH", 41, 1232, 0, 1, 0, 0)
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=opt_badvers))["rcode"],
            "BADVERS",
        )
        tsig_rr = b"\x00" + struct.pack("!HHIH", 250, 255, 0, 0)
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(arcount=1, extra=tsig_rr))["rcode"],
            "REFUSED",
        )
        self.assertEqual(
            mod.simulate_upstream_query_model(_build_valid_query(extra=b"\x00"))["rcode"],
            "FORMERR",
        )

    def test_upstream_model_reproduces_all_wire_defects(self) -> None:

        # Standalone mode always runs cleanly (including inside /tmp mutation sandboxes)
        cert = mod.run_audit(standalone=True)
        _assert_no_floats(cert, self)
        self.assertEqual(cert["upstream_repo_verification"]["mode"], "standalone")
        self.assertEqual(cert["upstream_repo_verification"]["pinned_head_sha"], mod.PINNED_REPO_HEAD)
        self.assertEqual(cert["upstream_repo_verification"]["tracked_files_cataloged"], 15)
        self.assertEqual(cert["upstream_repo_verification"]["verbatim_anchors_cataloged"], 29)
        self.assertEqual(cert["warp_drive_server_verification"]["verbatim_anchors_cataloged"], 6)

        # Live checkout verification runs automatically whenever the sibling read-only repos exist
        sibling_repo = Path(__file__).resolve().parent.parent / "repos" / "workers-dns-tcp"
        if sibling_repo.is_dir():
            live_cert = mod.run_audit(standalone=False)
            _assert_no_floats(live_cert, self)
            self.assertEqual(live_cert["upstream_repo_verification"]["head_sha"], mod.PINNED_REPO_HEAD)
            self.assertEqual(live_cert["upstream_repo_verification"]["tracked_files_verified"], 15)
            self.assertEqual(live_cert["upstream_repo_verification"]["verbatim_anchors_verified"], 29)
            self.assertEqual(live_cert["warp_drive_server_verification"]["verbatim_anchors_verified"], 6)
            self.assertEqual(live_cert["exact_channel_capacity_and_bridge"], cert["exact_channel_capacity_and_bridge"])
            self.assertEqual(live_cert["protocol_and_security_findings"], cert["protocol_and_security_findings"])

        fnd = cert["protocol_and_security_findings"]
        self.assertEqual(fnd["wdt01_additional_rr_cpu_bomb"]["upstream_rcode"], "NOERROR")
        self.assertEqual(fnd["wdt01_additional_rr_cpu_bomb"]["upstream_regex_calls"], 1359000)
        self.assertEqual(fnd["wdt01_additional_rr_cpu_bomb"]["upstream_discarded_chars"], 5452309)
        self.assertEqual(fnd["wdt01_additional_rr_cpu_bomb"]["hybrid_128hop_total_jumps"], 693120)
        self.assertEqual(fnd["wdt02_nonroot_opt_formerr_leak"]["upstream_rcode"], "FORMERR")
        self.assertTrue(fnd["wdt02_nonroot_opt_formerr_leak"]["upstream_leaks_synthetic_opt"])
        self.assertEqual(fnd["wdt03_dirty_header_and_meta_qtype"]["upstream_rcode"], "NOERROR")
        self.assertEqual(fnd["wdt08_prompt_injection_witness"]["label_len"], 63)
        self.assertTrue(fnd["wdt08_prompt_injection_witness"]["matches_upstream_regex"])

        cap = cert["exact_channel_capacity_and_bridge"]
        self.assertEqual(cap["recurrence_verified"]["a1"], 36)
        self.assertEqual(cap["recurrence_verified"]["a4"], 1772928)
        self.assertEqual(cap["recurrence_verified"]["perron_eigenvalue_q_sqrt10"]["rational_residual"], 0)
        self.assertEqual(cap["recurrence_verified"]["perron_eigenvalue_q_sqrt10"]["sqrt10_residual"], 0)
        self.assertEqual(cap["uplink_regimes_ask_southpolesteve_com"]["workers_dns_tcp_L63"]["capacity_bits_bracket"]["lower_dec"], "328.094")
        self.assertEqual(cap["downlink_tcp_txt_and_amplification"]["compressed_max_payload_bytes"], 65163)
        self.assertEqual(cap["downlink_tcp_txt_and_amplification"]["wdt07_0x20_payload_bytes_lost"], 86)
        self.assertEqual(cap["tokenpage_pr13_audit024_bridge"]["structured_state_space"], 2880)
        self.assertEqual(len(json.dumps(cert, allow_nan=False)), len(json.dumps(cert)))


if __name__ == "__main__":
    unittest.main()
