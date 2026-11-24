#!/usr/bin/env python3
"""
Check that no library module runs code that could write the environment without the kernel.

A metaprogram can store a constant that the kernel never checked, or a changed copy of one that it did
(Lean issues 16688 and 16730). The kernel replay of `scripts/replay.sh` finds such a constant in a
compiled module. This check is a second defence on the source: it fails on each command that runs code
during elaboration, and on each name that writes the environment or reaches a private part of Lean,
unless an entry of the allowlist names its line.

The modules are the Lean files of the libraries DogeLib and ProposalExamples, and the Refinement
sources: `DogeLib.lean`, `DogeLib/`, `tests/ProposalExamples.lean`, `tests/ProposalExamples/`,
`Refinement/Refinement.lean` and `Refinement/Refinement/`.

The check reads code only: comments, strings and character literals are removed first.
It matches words, so it misses code that reaches the same function under a name it does not list,
for example through an `elab` that calls a function of another module. That is why every `elab` and
every other command that runs code needs an allowlist entry, whatever its body.

The allowlist `scripts/check_lean_commands_allowlist.txt` has one entry per line:

    path | code line | reason

The code line is the line of the file after comments and strings are removed, with each run of
spaces made one space and the spaces at its ends trimmed. An entry allows every finding on that line. Each entry needs a reason, and an entry
that matches no line of its file fails the check, so the list stays exact.

    python3 -I scripts/check_lean_commands.py
    python3 -I scripts/check_lean_commands.py --allowlist FILE PATH...

With paths, the check reads those files or directories instead of the libraries.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

LIBRARIES = [
    "DogeLib.lean",
    "DogeLib",
    "tests/ProposalExamples.lean",
    "tests/ProposalExamples",
    "Refinement/Refinement.lean",
    "Refinement/Refinement",
]

ALLOWLIST = ROOT / "scripts" / "check_lean_commands_allowlist.txt"

# Commands that run code while Lean elaborates the file.
COMMANDS = {
    "run_cmd": "runs a command metaprogram",
    "run_meta": "runs a metaprogram",
    "run_elab": "runs an elaborator",
    "#eval": "runs code",
    "#eval!": "runs code",
    "elab": "defines an elaborator, which runs code",
    "elab_rules": "defines an elaborator, which runs code",
    "initialize": "runs code when the module is loaded",
    "builtin_initialize": "runs code when the module is loaded",
    "simproc": "defines a simplification procedure, which runs code",
    "dsimproc": "defines a simplification procedure, which runs code",
    "simproc_decl": "defines a simplification procedure, which runs code",
    "dsimproc_decl": "defines a simplification procedure, which runs code",
    "unsafe": "marks code that the kernel does not check",
}

# Name components that write the environment, skip the kernel or reach a private part of Lean.
COMPONENTS = {
    "setEnv": "writes the environment",
    "modifyEnv": "writes the environment",
    "addDecl": "adds a declaration from a raw term",
    "addDeclCore": "adds a declaration from a raw term",
    "addAndCompile": "adds a declaration from a raw term",
    "ofKernelEnv": "builds an environment from a kernel environment",
    "toKernelEnv": "reads the kernel environment",
    "skipKernelTC": "skips the kernel check",
    "evalConst": "runs a constant as code",
    "_private": "names a private declaration of another module",
}

# Attributes that make a declaration run as an elaborator, a tactic or an initializer.
ATTRIBUTE = re.compile(
    r"@\[[^\]]*?(?<![\w.])(term_elab|command_elab|tactic|init|builtin_init|builtin_term_elab|"
    r"builtin_command_elab|builtin_tactic|env_extension)(?![\w'!?])"
)

WORD = re.compile(r"#?[A-Za-z_][A-Za-z0-9_'!?]*(?:\.(?:[A-Za-z_][A-Za-z0-9_'!?]*|[0-9]+))*")
CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|.)|[^\\'\n])'")
RAW_STRING = re.compile(r'r(#*)"')


def is_ident(char: str) -> bool:
    """Whether a character can continue a Lean identifier."""
    return char.isalnum() or char in "_'!?»"


def code_of(text: str) -> str:
    """
    The text with comments, strings and character literals replaced by spaces.

    Newlines stay, so each line of the result is the code of the same line of the text.
    Block comments nest. Guillemets of a quoted name `«…»` are dropped, so `«_private»` is `_private`.
    """
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0

    def blank(segment: str) -> str:
        return "".join("\n" if c == "\n" else " " for c in segment)

    while i < n:
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append(blank(text[i]))
                i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            out.append(blank(text[i:end]))
            i = end
            continue
        raw = RAW_STRING.match(text, i)
        if raw and (i == 0 or not is_ident(text[i - 1])):
            close = '"' + raw.group(1)
            end = text.find(close, raw.end())
            end = n if end < 0 else end + len(close)
            out.append(blank(text[i:end]))
            i = end
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            end = min(j + 1, n)
            out.append(blank(text[i:end]))
            i = end
            continue
        if text[i] == "'" and (i == 0 or not is_ident(text[i - 1])):
            char = CHAR_LITERAL.match(text, i)
            if char:
                out.append(blank(char.group(0)))
                i = char.end()
                continue
        if text[i] in "«»":
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def findings_of(text: str) -> list[tuple[int, str, str]]:
    """Each finding of a file's text: its line number, the word found and why it counts."""
    found = []
    for number, line in enumerate(code_of(text).split("\n"), start=1):
        for match in WORD.finditer(line):
            word = match.group(0)
            start = match.start()
            # A word after a dot, as in `(← getEnv).toKernelEnv`, is checked. A word inside another is not.
            if start > 0 and is_ident(line[start - 1]):
                continue
            if word in COMMANDS:
                found.append((number, word, COMMANDS[word]))
                continue
            parts = word.split(".")
            for part in parts:
                if part in COMPONENTS:
                    found.append((number, word, COMPONENTS[part]))
                    break
            else:
                if "Kernel" in parts:
                    found.append((number, word, "reaches the kernel environment"))
        for match in ATTRIBUTE.finditer(line):
            found.append((number, "@[" + match.group(1), "makes a declaration run as code"))
    return found


def read_allowlist(path: Path) -> tuple[list[tuple[str, str, str]], list[str]]:
    """The entries of the allowlist as (path, code line, reason), and its format errors."""
    entries, errors = [], []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = [field.strip() for field in line.split(" | ")]
        if len(fields) != 3 or not all(fields):
            errors.append(f"{path}:{number}: an entry needs a path, a code line and a reason, separated by ' | '")
            continue
        entries.append((fields[0], fields[1], fields[2]))
    return entries, errors


def lean_files(paths: list[str]) -> list[Path]:
    """The Lean files of the given files and directories, relative to the repository root."""
    files = []
    for name in paths:
        path = ROOT / name
        if path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
        elif path.is_file():
            files.append(path)
        else:
            raise SystemExit(f"check_lean_commands: {name} does not exist")
    return files


def check(paths: list[str], allowlist: Path) -> int:
    """Print each finding that no entry allows and each unused entry. Return the exit status."""
    entries, errors = read_allowlist(allowlist)
    for error in errors:
        print(error)
    used = [False] * len(entries)
    fresh = 0
    files = lean_files(paths)
    for path in files:
        rel = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else path.as_posix()
        text = path.read_text(encoding="utf-8")
        lines = code_of(text).split("\n")
        for number, word, why in findings_of(text):
            code = " ".join(lines[number - 1].split())
            allowed = False
            for index, (entry_path, entry_code, _) in enumerate(entries):
                if entry_path == rel and entry_code == code:
                    used[index] = True
                    allowed = True
            if not allowed:
                print(f"{rel}:{number}: {word} {why}")
                fresh += 1
    stale = 0
    for (entry_path, entry_code, _), was_used in zip(entries, used):
        if not was_used:
            print(f"unused allowlist entry: {entry_path} | {entry_code}")
            stale += 1
    print(f"check_lean_commands: {len(files)} files, {fresh} findings not allowed, {stale} unused entries")
    return 0 if fresh == 0 and stale == 0 and not errors else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST)
    parser.add_argument("paths", nargs="*", help="files or directories, relative to the repository root")
    args = parser.parse_args()
    return check(args.paths or LIBRARIES, args.allowlist)


if __name__ == "__main__":
    sys.exit(main())
