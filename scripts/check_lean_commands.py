#!/usr/bin/env python3
"""
Check that no library module runs code during elaboration without a reviewed allowlist entry.

A metaprogram can store a constant that the kernel never checked, or a changed copy of one that it did
(Lean issues 16688 and 16730). The kernel replay of `scripts/replay.sh` finds such a constant in a
compiled module. This check is a second defence on the source, and it runs on pull requests.

The modules are the Lean files of the libraries DogeLib and ProposalExamples, and the Refinement
sources: `DogeLib.lean`, `DogeLib/`, `tests/ProposalExamples.lean`, `tests/ProposalExamples/`,
`Refinement/Refinement.lean` and `Refinement/Refinement/`.

The check fails on three kinds of finding:

* A command of Lean core that runs code or defines code that Lean runs later: `run_cmd`, `#eval`,
  `elab`, `elab_rules`, `macro`, `macro_rules`, `initialize`, `simproc` and the others of `COMMANDS`.
  A macro counts, because a macro can expand to any command, `run_cmd` included.
* An attribute that registers a declaration as an elaborator, a macro, a tactic, an initializer or
  another handler, in `@[...]` or in an `attribute [...]` command, on one line or several.
  Each attribute of `REGISTRATIONS` counts, and so does each attribute whose name starts with `builtin_`.
* A name that writes the environment, skips the kernel or reaches a private part of Lean, such as
  `setEnv`, `addDecl`, `_private` and any name with the component `Kernel`.

The check reads code only: comments, strings and character literals are removed first.
It matches words, so it misses a command or a function that the libraries reach under another name,
for example a command that an imported module defines. `notation`, `infix` and `syntax` are not
findings: they declare parsers and term templates, and give a new command meaning only through one
of the findings above.

A finding belongs to the construct that contains its line. A construct starts at a line whose code
starts in the first column, and ends at the last line with code before the next such line.
The allowlist `scripts/check_lean_commands_allowlist.txt` pins each reviewed construct:

    path | code of the first line | sha256:DIGEST | reason

The code of the first line is that line after comments and strings are removed, with each run of
spaces made one space. The digest is the SHA-256 of the construct's source lines, comments and
strings included, each line ending in a newline. An entry allows the findings of one construct only.
The check fails on an entry without a reason, an entry that matches no construct, and an entry
that matches two. When a reviewed construct changes, its digest changes, and the entry must be
reviewed again. A finding that no entry allows is printed with the digest of its construct.

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
# an initializer or another handler. Each attribute whose name starts with `builtin_` counts too.
REGISTRATIONS = {
    "term_elab", "command_elab", "tactic", "macro", "init", "env_extension",
    "simproc", "dsimproc", "delab", "app_unexpander",
}

# The start of an attribute list: `@[` or the command `attribute [`.
ATTRIBUTE_START = re.compile(r"@\[|(?<![\w'!?.])attribute\s*\[")

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
            if name in REGISTRATIONS or name.startswith("builtin_"):
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


def construct_of(code_lines: list[str], number: int) -> tuple[int, int]:
    """
    The first and last line of the construct that contains line `number`, counted from 1.

    It starts at the last line at or before `number` whose code starts in the first column, and ends
    at the last line with code before the next such line.
    """
    first = number
    while first > 1 and not (code_lines[first - 1][:1].strip()):
        first -= 1
    last = first
    for index in range(first + 1, len(code_lines) + 1):
        line = code_lines[index - 1]
        if line[:1].strip():
            break
        if line.strip():
            last = index
    return first, max(last, number)


def digest_of(text_lines: list[str], first: int, last: int) -> str:
    """The SHA-256 of the source lines `first` to `last`, each ending in a newline."""
    body = "".join(line + "\n" for line in text_lines[first - 1:last])
    return "sha256:" + hashlib.sha256(body.encode("utf-8")).hexdigest()


def read_allowlist(path: Path) -> tuple[list[tuple[str, str, str, str]], list[str]]:
    """The entries of the allowlist as (path, code line, digest, reason), and its format errors."""
    entries, errors = [], []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = [field.strip() for field in line.split(" | ")]
        if len(fields) != 4 or not all(fields) or not re.fullmatch(r"sha256:[0-9a-f]{64}", fields[2]):
            errors.append(f"{path}:{number}: an entry needs a path, a code line, a digest sha256:HEX "
                          "and a reason, separated by ' | '")
            continue
        entries.append((fields[0], fields[1], fields[2], fields[3]))
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
    """Print each finding that no entry allows and each unused or repeated entry. Return the exit status."""
    entries, errors = read_allowlist(allowlist)
    for error in errors:
        print(error)
    matches = [0] * len(entries)
    fresh = 0
    files = lean_files(paths)
    for path in files:
        rel = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else path.as_posix()
        text = path.read_text(encoding="utf-8")
        text_lines = text.split("\n")
        code_lines = code_of(text).split("\n")
        constructs: dict[tuple[int, int], list[tuple[int, str, str]]] = {}
        for finding in findings_of(text):
            constructs.setdefault(construct_of(code_lines, finding[0]), []).append(finding)
        for (first, last), found in constructs.items():
            code = " ".join(code_lines[first - 1].split())
            digest = digest_of(text_lines, first, last)
            allowed = False
            for index, (entry_path, entry_code, entry_digest, _) in enumerate(entries):
                if entry_path == rel and entry_code == code and entry_digest == digest:
                    matches[index] += 1
                    allowed = True
            if not allowed:
                for number, word, why in found:
                    print(f"{rel}:{number}: {word} {why}")
                print(f"{rel}:{first}-{last}: construct {code!r} has the digest {digest}")
                fresh += len(found)
    bad = 0
    for (entry_path, entry_code, entry_digest, _), count in zip(entries, matches):
        if count != 1:
            what = "unused" if count == 0 else f"matches {count} constructs, not one:"
            print(f"allowlist entry {what} {entry_path} | {entry_code} | {entry_digest}")
            bad += 1
    print(f"check_lean_commands: {len(files)} files, {fresh} findings not allowed, {bad} allowlist entries not used exactly once")
    return 0 if fresh == 0 and bad == 0 and not errors else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST)
    parser.add_argument("paths", nargs="*", help="files or directories, relative to the repository root")
    args = parser.parse_args()
    return check(args.paths or LIBRARIES, args.allowlist)


if __name__ == "__main__":
    sys.exit(main())
