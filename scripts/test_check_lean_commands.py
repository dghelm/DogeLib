#!/usr/bin/env python3
"""
Self-test of `scripts/check_lean_commands.py`.

Each planted command, name and registration attribute fails the check, including an attribute in an
`attribute [...]` command or across lines, and a macro that expands to `run_cmd`. The same text in a
comment, a string or a longer name does not. An allowlist entry allows one construct with its digest:
a second construct with the same first line, a changed construct and a repeated construct fail, and
so does an unused or malformed entry. The committed libraries pass with the committed allowlist, and
the planted forged module of `scripts/replay-fixtures/` fails.

    python3 -I scripts/test_check_lean_commands.py
"""

import contextlib
import hashlib
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
            ("macro \"narrow\" : tactic => `(tactic| rfl)", "macro"),
            ("macro_rules | `(x) => `(1)", "macro_rules"),
            ("#guard 1 + 1 == 2", "#guard"),
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
        for text, line in [
            ("@[term_elab foo] def f := 0", 1),
            ("@[simp, command_elab foo] def f := 0", 1),
            ("@[tactic foo] def f := 0", 1),
            ("@[init g] def f := 0", 1),
            ("@[macro foo] def f := 0", 1),
            ("@[builtin_command_elab foo] def f := 0", 1),
            ("@[local builtin_tactic foo] def f := 0", 1),
            ("attribute [command_elab probeCmd] probeHandler", 1),
            ("attribute [local term_elab x] h", 1),
            ("attribute\n  [builtin_init g] f", 2),
            ("@[\n  command_elab probeCmd2\n]\ndef probeHandler2 : CommandElab := fun _ => pure ()", 2),
            ("@[simp,\n  Lean.Elab.Command.command_elab x] def f := 0", 2),
        ]:
            with self.subTest(text=text):
                self.assertIn(line, [n for n, w, _ in c.findings_of(text) if w.startswith("@[")])

    def test_the_reviewed_probes_fail(self):
        # The probes of the independent review of pull request 206: a command elaborator registered
        # through the `attribute` command, and a macro that expands to `run_cmd`.
        attribute = "\n".join([
            "import Lean",
            "open Lean Elab Command",
            "syntax (name := probeCmd) \"probe_command\" : command",
            "def probeHandler : CommandElab := fun _ => logInfo \"probe handler ran\"",
            "attribute [command_elab probeCmd] probeHandler",
            "probe_command",
        ])
        self.assertEqual([(n, w) for n, w, _ in c.findings_of(attribute)], [(5, "@[command_elab")])
        macro = "\n".join([
            "import Lean",
            "",
            "macro \"probe_macro\" : command => do",
            "  let body ← `(doSeq| Lean.logInfo \"macro handler ran\")",
            "  return ⟨Lean.Syntax.node .none",
            "    (Lean.Name.str (Lean.Name.str .anonymous \"Lean\") \"runCmd\")",
            "    #[Lean.Syntax.atom .none \"run_cmd\", body.raw]⟩",
            "",
            "probe_macro",
        ])
        self.assertEqual([(n, w) for n, w, _ in c.findings_of(macro)], [(3, "macro")])

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
            "@[simp] theorem t : True := trivial",
            "@[macro_inline, inline] def m := 0",
            "attribute [simp] t",
            "syntax \"probe\" : tactic",
            "notation \"one\" => 1",
            "def init := 0",
            "theorem tactic_free : True := trivial",
        ])
        self.assertEqual(c.findings_of(text), [])

    def test_lines_keep_their_numbers(self):
        text = "/- a\nb\nc -/\n\"x\ny\"\nrun_cmd pure ()\n"
        self.assertEqual([n for n, _, _ in c.findings_of(text)], [6])


ELAB_ONE = "elab \"one%\" : term => do\n  pure (Lean.mkConst ``True)\n"
ELAB_TWO = "elab \"two%\" : term => do\n  pure (Lean.mkConst ``True)\n"
INIT = "initialize\n  pure ()\n"


class Allowlist(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = Path(self.dir.name) / "M.lean"
        self.rel = self.path.as_posix()
        self.write(ELAB_ONE + "-- a comment\n\n" + INIT)

    def tearDown(self):
        self.dir.cleanup()

    def write(self, text: str) -> None:
        self.path.write_text(text, encoding="utf-8")

    def entry(self, code: str, body: str) -> str:
        """An allowlist entry for the construct `body` whose first line has the code `code`."""
        digest = "sha256:" + hashlib.sha256(body.encode("utf-8")).hexdigest()
        return f"{self.rel} | {code} | {digest} | reason\n"

    def entries(self) -> str:
        return self.entry("elab : term => do", ELAB_ONE) + self.entry("initialize", INIT)

    def test_no_entry_fails(self):
        status, out = run([self.rel], "")
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:1: elab", out)
        self.assertIn(f"{self.rel}:5: initialize", out)
        self.assertIn(f"{self.rel}:1-2: construct 'elab : term => do' has the digest sha256:", out)

    def test_the_entries_allow_their_constructs(self):
        status, out = run([self.rel], self.entries())
        self.assertEqual(status, 0, out)

    def test_a_second_elaborator_with_the_same_code_fails(self):
        # Once its string is removed, the second elaborator has the code of the first, but not its digest.
        self.write(ELAB_ONE + ELAB_TWO + "\n" + INIT)
        status, out = run([self.rel], self.entries())
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:3: elab", out)
        self.assertNotIn(f"{self.rel}:1: elab", out)

    def test_a_second_initializer_fails(self):
        self.write(ELAB_ONE + "\n" + INIT + "\ninitialize\n  IO.println \"extra initializer ran\"\n")
        status, out = run([self.rel], self.entries())
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:7: initialize", out)

    def test_a_repeated_construct_fails(self):
        self.write(ELAB_ONE + "\n" + INIT + "\n" + INIT)
        status, out = run([self.rel], self.entries())
        self.assertEqual(status, 1)
        self.assertIn(f"allowlist entry matches 2 constructs, not one: {self.rel} | initialize", out)

    def test_a_changed_construct_fails(self):
        self.write(ELAB_ONE + "\n" + "initialize\n  pure ()\n  Lean.modifyEnv id\n")
        status, out = run([self.rel], self.entries())
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:4: initialize", out)
        self.assertIn(f"{self.rel}:6: Lean.modifyEnv", out)
        self.assertIn(f"allowlist entry unused {self.rel} | initialize", out)

    def test_a_finding_after_the_construct_fails(self):
        self.write(ELAB_ONE + "run_cmd pure ()\n\n" + INIT)
        status, out = run([self.rel], self.entries())
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}:3: run_cmd", out)

    def test_an_unused_entry_fails(self):
        status, out = run([self.rel], self.entries() + self.entry("run_cmd pure ()", "run_cmd pure ()\n"))
        self.assertEqual(status, 1)
        self.assertIn(f"allowlist entry unused {self.rel} | run_cmd pure ()", out)

    def test_a_malformed_entry_fails(self):
        for bad in [f"{self.rel} | initialize | sha256:00 | reason\n",
                    f"{self.rel} | initialize | reason\n",
                    self.entry("initialize", INIT).replace(" | reason", " |")]:
            with self.subTest(entry=bad):
                status, out = run([self.rel], bad)
                self.assertEqual(status, 1)
                self.assertIn("an entry needs a path, a code line, a digest sha256:HEX and a reason", out)


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
