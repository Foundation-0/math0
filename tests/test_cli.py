import io
import json
import os
import unittest
from contextlib import redirect_stdout, redirect_stderr

from gfq.cli import main

ROOT = os.path.join(os.path.dirname(__file__), "..")


class TestCLI(unittest.TestCase):
    def run_cli(self, argv):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            rc = main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_golay_example(self):
        rc, out, _ = self.run_cli(
            ["--q", "3", os.path.join(ROOT, "examples", "golay11.txt")])
        self.assertEqual(rc, 0)
        self.assertIn("[11,6,5]", out)
        self.assertIn("True", out)  # certificate check passed

    def test_golay_json(self):
        rc, out, _ = self.run_cli(
            ["--q", "3", "--json", "--method", "bz",
             os.path.join(ROOT, "examples", "golay11.txt")])
        self.assertEqual(rc, 0)
        data = json.loads(out)
        self.assertEqual((data["n"], data["k"], data["d"]), (11, 6, 5))
        self.assertTrue(data["certificate_checked"])
        self.assertEqual(sum(1 for a in data["codeword_certificate"] if a), 5)

    def test_wrong_field_element_error(self):
        import tempfile
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
            f.write("1 4\n0 1\n")
            path = f.name
        try:
            rc, _, err = self.run_cli(["--q", "3", path])
        finally:
            os.unlink(path)
        self.assertEqual(rc, 1)
        self.assertIn("error", err)

    def test_incomplete_exit_code_2(self):
        import tempfile
        from gfq import GF, codes
        G = codes.hamming_generator(GF(4), 3)
        with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
            f.write("\n".join(" ".join(map(str, r)) for r in G))
            path = f.name
        try:
            rc, out, _ = self.run_cli(
                ["--q", "4", "--method", "bz", "--max-enum", "1", path])
        finally:
            os.unlink(path)
        self.assertEqual(rc, 2)
        self.assertIn("INCOMPLETE", out)


if __name__ == "__main__":
    unittest.main()
