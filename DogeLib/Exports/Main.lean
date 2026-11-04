module

public import DogeLib.Exports.Oracle

/-!
# `Exports.Main`

The entry point of `dogelib-oracle`.

It reads requests from standard input, one per line, and writes each response as one line of compact JSON to standard output.
It flushes each response before it reads the next line, so a caller can keep the process open and send one request at a time.
It stops at the end of input. A final line without a newline is still answered.
`dogelib-oracle --version` prints the `ok` object of `oracle.version` and exits.
-/

public section

open DogeLib.Exports

/-- Answer each line of standard input, or print the format with `--version`. -/
def main (argv : List String) : IO UInt32 := do
  match argv with
  | ["--version"] =>
    IO.println versionJson.compress
    return 0
  | [] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      if let some response := respond line then
        stdout.putStrLn response.compress
        stdout.flush
    return 0
  | _ =>
    IO.eprintln "usage: dogelib-oracle [--version]"
    return 2
