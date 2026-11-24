#!/usr/bin/env python3
"""
Self-test of `scripts/check_lean_commands.py`.

Each planted command or name fails the check, and the same text in a comment, a string or a longer
name does not. An allowlist entry allows its line only, and an unused or malformed entry fails.
The committed libraries pass with the committed allowlist, and the planted forged module of
`scripts/replay-fixtures/` fails.

    python3 -I scripts/test_check_lean_commands.py
"""

import contextlib
import importlib.util
import io
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("check", ROOT / "scripts/check_lean_commands.py")
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def words(text: str) -> list[str]:
    """The words that the check reports in `text`."""
    return [word for _, word, _ in c.findings_of(text)]


def run(paths: list[str], allowlist: str) -> tuple[int, str]:
    """Run the check on `paths` with an allowlist of the given text, and return its status and output."""
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write(allowlist)
    out = io.StringIO()
    try:
        with contextlib.redirect_stdout(out):
            status = c.check(paths, Path(f.name))
    finally:
        Path(f.name).unlink()
    return status, out.getvalue()


class Planted(unittest.TestCase):
    def test_each_command_fails(self):
        for line, word in [
            ("run_cmd logInfo m!\"x\"", "run_cmd"),
            ("run_meta pure ()", "run_meta"),
            ("run_elab pure ()", "run_elab"),
            ("#eval 1 + 1", "#eval"),
            ("#eval! 1 + 1", "#eval!"),
            ("elab \"x\" : term => pure (mkConst ``True)", "elab"),
            ("local elab \"x\" : term => pure (mkConst ``True)", "elab"),
            ("elab_rules : term | `(x) => pure (mkConst ``True)", "elab_rules"),
            ("initialize registerTraceClass `x", "initialize"),
            ("builtin_initialize pure ()", "builtin_initialize"),
            ("simproc reduceX (f _) := fun _ => pure .continue", "simproc"),
            ("dsimproc reduceY (f _) := fun _ => pure .continue", "dsimproc"),
            ("unsafe def f : Nat := 0", "unsafe"),
        ]:
            with self.subTest(line=line):
                self.assertIn(word, words(line))

    def test_each_name_fails(self):
        for line, word in [
            ("  setEnv env", "setEnv"),
            ("  Lean.modifyEnv fun e => e", "Lean.modifyEnv"),
            ("  addDecl d", "addDecl"),
            ("  Lean.addAndCompile d", "Lean.addAndCompile"),
            ("  (← getEnv).toKernelEnv", "toKernelEnv"),
            ("  Environment.ofKernelEnv k", "Environment.ofKernelEnv"),
            ("  Lean.Kernel.Environment.add", "Lean.Kernel.Environment.add"),
            ("open Lean.Kernel in", "Lean.Kernel"),
            ("set_option debug.skipKernelTC true in", "debug.skipKernelTC"),
            ("  evalConst Nat `x", "evalConst"),
            ("  mkConst `_private.Lean.Environment.0.add", "_private.Lean.Environment.0.add"),
            ("  mkConst `«_private».Lean.x", "_private.Lean.x"),
        ]:
            with self.subTest(line=line):
                self.assertIn(word, words(line))

    def test_each_attribute_fails(self):
        for line in ["@[term_elab foo] def f := 0", "@[simp, command_elab foo] def f := 0",
                     "@[tactic foo] def f := 0", "@[init g] def f := 0"]:
            with self.subTest(line=line):
                self.assertTrue(any(w.startswith("@[") for w in words(line)))

    def test_one_finding_per_line_and_word(self):
        found = c.findings_of("theorem a : True := trivial\nrun_cmd setEnv e\n")
        self.assertEqual([(n, w) for n, w, _ in found], [(2, "run_cmd"), (2, "setEnv")])


class NotCode(unittest.TestCase):
    def test_comments_strings_and_longer_names_pass(self):
        text = "\n".join([
            "-- run_cmd setEnv",
            "/-- `elab` and `#eval` in a doc comment -/",
            "/- outer /- nested run_meta -/ still a comment: addDecl -/",
            "def s : String := \"run_cmd setEnv \\\" initialize\"",
            "def r : String := r#\"elab \"unsafe\" \"#",
            "def ch : Char := '\"'",
            "theorem h' : True := trivial",
            "def isUnsafe (x : Nat) := x",
            "open Lean Elab Term in",
            "def initializeFoo := 0",
            "def elabX := 0",
            "def xs := [1, 2].map (·.succ)",
            "macro \"narrow\" : tactic => `(tactic| rfl)",
            "@[simp] theorem t : True := trivial",
        ])
        self.assertEqual(c.findings_of(text), [])

    def test_lines_keep_their_numbers(self):
        text = "/- a\nb\nc -/\n\"x\ny\"\nrun_cmd pure ()\n"
        self.assertEqual([n for n, _, _ in c.findings_of(text)], [6])


class Allowlist(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = Path(self.dir.name) / "M.lean"
        self.path.write_text(
            "elab \"one%\" : term => pure (Lean.mkConst ``True)\n"
            "-- a comment\n"
            "elab \"two%\" : term => pure (Lean.mkConst ``True)\n",
            encoding="utf-8")
        self.rel = self.path.as_posix()

    def tearDown(self):
        self.dir.cleanup()

    def test_no_entry_fails(self):
        status, out = run([self.rel], "")
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:1: elab", out)
        self.assertIn(f"{self.rel}:3: elab", out)

    def test_an_entry_allows_its_line_only(self):
        status, out = run([self.rel], f"{self.rel} | elab : term => pure (Lean.mkConst ``True) | reason\n")
        # Both lines have the same code once the strings are removed, so one entry allows both.
        self.assertEqual(status, 0, out)
        self.path.write_text(self.path.read_text() + "run_cmd pure ()\n", encoding="utf-8")
        status, out = run([self.rel], f"{self.rel} | elab : term => pure (Lean.mkConst ``True) | reason\n")
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:4: run_cmd", out)

    def test_an_unused_entry_fails(self):
        allow = (f"{self.rel} | elab : term => pure (Lean.mkConst ``True) | reason\n"
                 f"{self.rel} | initialize | reason\n")
        status, out = run([self.rel], allow)
        self.assertEqual(status, 1)
        self.assertIn(f"unused allowlist entry: {self.rel} | initialize", out)

    def test_an_entry_without_reason_fails(self):
        status, out = run([self.rel], f"{self.rel} | elab : term => pure (Lean.mkConst ``True) |\n")
        self.assertEqual(status, 1)
        self.assertIn("an entry needs a path, a code line and a reason", out)


class Repository(unittest.TestCase):
    def test_the_libraries_pass(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            status = c.check(c.LIBRARIES, c.ALLOWLIST)
        self.assertEqual(status, 0, out.getvalue())

    def test_the_forged_fixture_fails(self):
        status, out = run(["scripts/replay-fixtures"], "")
        self.assertEqual(status, 1)
        for word in ("run_cmd", "setEnv", "ofKernelEnv", "toKernelEnv", "Kernel.Environment", "elab"):
            self.assertIn(word, out)


if __name__ == "__main__":
    unittest.main()
