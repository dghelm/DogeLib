#!/usr/bin/env python3
"""
Self-test of `scripts/check_lean_commands.py`.

Each planted command, name and registration attribute fails the check, including an `attribute [...]`
command, an attribute across lines, a macro that expands to `run_cmd` and a `builtin_simproc`. The
same text in a comment, a string or a longer name does not. An allowlist entry pins its whole file:
any edit to the file, such as a second initializer or a continuation of the reviewed one in the first
column, fails, and so does an unused, repeated or malformed entry. The committed libraries pass with
the committed allowlist, and the planted forged module of `scripts/replay-fixtures/` fails.

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
            ("simproc_decl reduceZ (f _) := fun _ => pure .continue", "simproc_decl"),
            ("dsimproc_decl reduceW (f _) := fun _ => pure .continue", "dsimproc_decl"),
            ("simproc_pattern% f _ => reduceZ", "simproc_pattern%"),
            ("builtin_simproc ↓ p (f _) := fun _ => pure .continue", "builtin_simproc"),
            ("builtin_dsimproc p (f _) := fun _ => pure .continue", "builtin_dsimproc"),
            ("builtin_simproc_decl p (f _) := fun _ => pure .continue", "builtin_simproc_decl"),
            ("builtin_dsimproc_decl p (f _) := fun _ => pure .continue", "builtin_dsimproc_decl"),
            ("builtin_simproc_pattern% f _ => p", "builtin_simproc_pattern%"),
            ("builtin_initialize pure ()", "builtin_initialize"),
            ("local builtin_some_future_command x", "builtin_some_future_command"),
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
            ("@[sevalproc] def f := 0", 1),
            ("attribute [command_elab probeCmd] probeHandler", 1),
            ("attribute [local term_elab x] h", 1),
            ("attribute\n  [local init g] f", 2),
            ("@[\n  command_elab probeCmd2\n]\ndef probeHandler2 : CommandElab := fun _ => pure ()", 2),
            ("@[simp,\n  Lean.Elab.Command.command_elab x] def f := 0", 2),
        ]:
            with self.subTest(text=text):
                self.assertIn(line, [n for n, w, _ in c.findings_of(text) if w.startswith("@[")])

    def test_each_builtin_attribute_fails(self):
        for text, line, word in [
            ("@[builtin_command_elab foo] def f := 0", 1, "builtin_command_elab"),
            ("@[local builtin_tactic foo] def f := 0", 1, "builtin_tactic"),
            ("attribute\n  [builtin_init g] f", 2, "builtin_init"),
        ]:
            with self.subTest(text=text):
                self.assertIn((line, word), [(n, w) for n, w, _ in c.findings_of(text)])

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
        # The probe of the re-review: a builtin simplification procedure.
        builtin = "\n".join([
            "import Lean",
            "open Lean Meta Simp",
            "",
            "def probeF (n : Nat) : Nat := Nat.succ n",
            "",
            "builtin_simproc ↓ probeProcedure (probeF _) := fun _ => do",
            "  logInfo \"builtin procedure ran\"",
            "  return .continue",
            "",
            "example (n : Nat) : probeF n ≠ n := by simp [probeF, Nat.succ_ne_self]",
        ])
        self.assertEqual([(n, w) for n, w, _ in c.findings_of(builtin)], [(6, "builtin_simproc")])

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
            "def x := 7 % 2",
            "def builtinValue := 0",
            "theorem t_builtin_free : True := trivial",
            "theorem tactic_free : True := trivial",
        ])
        self.assertEqual(c.findings_of(text), [])

    def test_lines_keep_their_numbers(self):
        text = "/- a\nb\nc -/\n\"x\ny\"\nrun_cmd pure ()\n"
        self.assertEqual([n for n, _, _ in c.findings_of(text)], [6])


TAG = ROOT / "DogeLib/Proofs/TheoremTag.lean"


class Allowlist(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = Path(self.dir.name) / "TheoremTag.lean"
        self.rel = self.path.as_posix()
        self.original = TAG.read_text(encoding="utf-8")
        self.path.write_text(self.original, encoding="utf-8")

    def tearDown(self):
        self.dir.cleanup()

    def entry(self, text: str, count: int = 1) -> str:
        """An allowlist entry for the file `text` at the temporary path."""
        digest = "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()
        return f"{self.rel} | {digest} | {count} | reason\n"

    def test_no_entry_fails(self):
        status, out = run([self.rel], "")
        self.assertEqual(status, 1)
        self.assertIn(": initialize runs code", out)
        self.assertIn(f"{self.rel}: the file has the digest sha256:", out)

    def test_the_entry_allows_its_file(self):
        status, out = run([self.rel], self.entry(self.original))
        self.assertEqual(status, 0, out)

    def test_a_continuation_in_the_first_column_fails(self):
        # The re-review's probe: an operator in the first column continues the reviewed initializer.
        changed = self.original.replace("  }\n", "  }\n*> IO.println \"unreviewed initializer continuation ran\"\n", 1)
        self.assertNotEqual(changed, self.original)
        self.path.write_text(changed, encoding="utf-8")
        status, out = run([self.rel], self.entry(self.original))
        self.assertEqual(status, 1)
        self.assertIn(f"allowlist entry unused: {self.rel}", out)

    def test_a_second_initializer_fails(self):
        self.path.write_text(self.original + "\ninitialize\n  IO.println \"extra initializer ran\"\n", encoding="utf-8")
        status, out = run([self.rel], self.entry(self.original))
        self.assertEqual(status, 1)
        self.assertIn(f"{self.rel}: the file has the digest sha256:", out)
        self.assertIn("and 2 findings", out)

    def test_a_comment_edit_fails(self):
        self.path.write_text(self.original + "-- a comment\n", encoding="utf-8")
        status, _ = run([self.rel], self.entry(self.original))
        self.assertEqual(status, 1)

    def test_a_wrong_count_fails(self):
        status, _ = run([self.rel], self.entry(self.original, 2))
        self.assertEqual(status, 1)

    def test_an_unused_entry_fails(self):
        other = Path(self.dir.name) / "Plain.lean"
        other.write_text("theorem t : True := trivial\n", encoding="utf-8")
        allow = self.entry(self.original) + f"{other.as_posix()} | sha256:{'0' * 64} | 1 | reason\n"
        status, out = run([self.rel, other.as_posix()], allow)
        self.assertEqual(status, 1)
        self.assertIn(f"allowlist entry unused: {other.as_posix()}", out)

    def test_a_second_entry_for_a_file_fails(self):
        status, out = run([self.rel], self.entry(self.original) + self.entry(self.original))
        self.assertEqual(status, 1)
        self.assertIn(f"a second entry for {self.rel}", out)

    def test_a_malformed_entry_fails(self):
        for bad in [f"{self.rel} | sha256:00 | 1 | reason\n",
                    f"{self.rel} | sha256:{'0' * 64} | reason\n",
                    f"{self.rel} | sha256:{'0' * 64} | 0 | reason\n",
                    self.entry(self.original).replace(" | reason", " |")]:
            with self.subTest(entry=bad):
                status, out = run([self.rel], bad)
                self.assertEqual(status, 1)
                self.assertIn("an entry needs a path, a digest sha256:HEX, a number of findings and a reason", out)


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
