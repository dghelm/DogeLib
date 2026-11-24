#!/usr/bin/env python3
"""
List the commands, attributes and names in library modules that can run code or write the environment.

A metaprogram can store a constant that the kernel never checked, or a changed copy of one that it did
(Lean issues 16688 and 16730). The kernel replay of `scripts/replay.sh` finds such a constant in a
compiled module. This check is a review aid on the source, and it runs on pull requests. It is not a
proof that no code runs while Lean builds the libraries.

The modules are the Lean files of the libraries DogeLib and ProposalExamples, and the Refinement
sources: `DogeLib.lean`, `DogeLib/`, `tests/ProposalExamples.lean`, `tests/ProposalExamples/`,
`Refinement/Refinement.lean` and `Refinement/Refinement/`.

It reports three kinds of finding, each from a fixed list:

* A command named in `COMMANDS`, such as `run_cmd`, `#eval`, `elab`, `macro`, `initialize` and the
  procedure commands of `Init/Simproc.lean`, and each word that starts with `builtin_`.
* An attribute named in `REGISTRATIONS`, in `@[...]` or in an `attribute [...]` command, on one line
  or several.
* A name with a component of `COMPONENTS` or the component `Kernel`, such as `setEnv`, `addDecl` and
  `_private`.

The check reads code only: comments, strings and character literals are removed first.
It matches words, so it misses whatever it does not name: a command that an imported module defines,
or a function reached under another name.

The allowlist `scripts/check_lean_commands_allowlist.txt` pins each reviewed file whole:

    path | sha256:DIGEST | N | reason

The digest is the SHA-256 of the file, and N is the number of findings in it. An entry allows the
findings of its file only while the file has that digest and that number of findings, so any edit to
the file needs a renewed entry. The check fails on an entry without a reason, a second entry for one
file, and an entry that allows nothing. A file whose findings no entry allows is printed with its
digest and its number of findings.

    python3 -I scripts/check_lean_commands.py
    python3 -I scripts/check_lean_commands.py --allowlist FILE PATH...

With paths, the check reads those files or directories instead of the libraries.
"""

import argparse
import hashlib
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
    "macro": "defines a macro, which runs code and can expand to any command",
    "macro_rules": "defines a macro, which runs code and can expand to any command",
    "#guard": "runs code",
    "initialize": "runs code when the module is loaded",
    "builtin_initialize": "runs code when the module is loaded",
    "simproc": "defines a simplification procedure, which runs code",
    "dsimproc": "defines a simplification procedure, which runs code",
    "simproc_decl": "defines a simplification procedure, which runs code",
    "dsimproc_decl": "defines a simplification procedure, which runs code",
    "simproc_pattern%": "registers a simplification procedure, which runs code",
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

# Attributes that register a declaration as code that Lean runs: an elaborator, a macro, a tactic,
# an initializer or another handler. A `builtin_` attribute is a finding of the word scan.
REGISTRATIONS = {
    "term_elab", "command_elab", "tactic", "macro", "init", "env_extension",
    "simproc", "dsimproc", "sevalproc", "delab", "app_unexpander",
}

# The start of an attribute list: `@[` or the command `attribute [`.
ATTRIBUTE_START = re.compile(r"@\[|(?<![\w'!?.])attribute\s*\[")

WORD = re.compile(r"#?[A-Za-z_][A-Za-z0-9_'!?]*(?:\.(?:[A-Za-z_][A-Za-z0-9_'!?]*|[0-9]+))*%?")
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


def attribute_findings(code: str) -> list[tuple[int, str, str]]:
    """Each registration attribute in the code of a file, with the line of its name."""
    found = []
    for start in ATTRIBUTE_START.finditer(code):
        depth, i = 1, start.end()
        while i < len(code) and depth > 0:
            depth += {"[": 1, "]": -1}.get(code[i], 0)
            i += 1
        body_start = start.end()
        for match in WORD.finditer(code, body_start, i - 1):
            if match.start() > 0 and is_ident(code[match.start() - 1]):
                continue
            name = match.group(0).split(".")[-1]
            if name in REGISTRATIONS:
                number = code.count("\n", 0, match.start()) + 1
                found.append((number, "@[" + name, "registers a declaration as code that Lean runs"))
    return found


def findings_of(text: str) -> list[tuple[int, str, str]]:
    """Each finding of a file's text: its line number, the word found and why it counts."""
    found = []
    code = code_of(text)
    for number, line in enumerate(code.split("\n"), start=1):
        for match in WORD.finditer(line):
            word = match.group(0)
            start = match.start()
            # A word after a dot, as in `(← getEnv).toKernelEnv`, is checked. A word inside another is not.
            if start > 0 and is_ident(line[start - 1]):
                continue
            if word in COMMANDS:
                found.append((number, word, COMMANDS[word]))
                continue
            if word.startswith("builtin_"):
                found.append((number, word, "is a builtin command or attribute, which registers code"))
                continue
            parts = word.split(".")
            for part in parts:
                if part in COMPONENTS:
                    found.append((number, word, COMPONENTS[part]))
                    break
            else:
                if "Kernel" in parts:
                    found.append((number, word, "reaches the kernel environment"))
    found.extend(attribute_findings(code))
    return sorted(found, key=lambda f: f[0])


def read_allowlist(path: Path) -> tuple[list[tuple[str, str, int, str]], list[str]]:
    """The entries of the allowlist as (path, digest, number of findings, reason), and its format errors."""
    entries, errors, paths = [], [], set()
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = [field.strip() for field in line.split(" | ")]
        if (len(fields) != 4 or not all(fields) or not re.fullmatch(r"sha256:[0-9a-f]{64}", fields[1])
                or not re.fullmatch(r"[1-9][0-9]*", fields[2])):
            errors.append(f"{path}:{number}: an entry needs a path, a digest sha256:HEX, a number of findings "
                          "and a reason, separated by ' | '")
            continue
        if fields[0] in paths:
            errors.append(f"{path}:{number}: a second entry for {fields[0]}")
            continue
        paths.add(fields[0])
        entries.append((fields[0], fields[1], int(fields[2]), fields[3]))
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
    by_path = {entry[0]: entry for entry in entries}
    used: set[str] = set()
    fresh = 0
    files = lean_files(paths)
    for path in files:
        rel = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else path.as_posix()
        data = path.read_bytes()
        found = findings_of(data.decode("utf-8"))
        if not found:
            continue
        digest = "sha256:" + hashlib.sha256(data).hexdigest()
        entry = by_path.get(rel)
        if entry and entry[1] == digest and entry[2] == len(found):
            used.add(rel)
            continue
        for number, word, why in found:
            print(f"{rel}:{number}: {word} {why}")
        print(f"{rel}: the file has the digest {digest} and {len(found)} findings")
        fresh += len(found)
    unused = 0
    for entry_path, digest, count, _ in entries:
        if entry_path not in used:
            print(f"allowlist entry unused: {entry_path} | {digest} | {count}")
            unused += 1
    print(f"check_lean_commands: {len(files)} files, {fresh} findings not allowed, {unused} unused entries")
    return 0 if fresh == 0 and unused == 0 and not errors else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST)
    parser.add_argument("paths", nargs="*", help="files or directories, relative to the repository root")
    args = parser.parse_args()
    return check(args.paths or LIBRARIES, args.allowlist)


if __name__ == "__main__":
    sys.exit(main())
