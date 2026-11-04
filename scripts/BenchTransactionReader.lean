import DogeLib.Transaction.Serialization

open DogeLib DogeLib.Serialization DogeLib.Transaction

/-! Generated workloads measure reader cost, not conformance to independent fixtures. -/

/-- Append a canonical CompactSize count. -/
def countInto (n : Nat) (acc : ByteArray) : ByteArray :=
  CompactSize.encodeInto n.toUInt64 acc

/-- Generate base bytes with empty scripts, or four outputs with scripts of `scriptSize` bytes. -/
def workload (inputs outputs scriptSize : Nat) : ByteArray := Id.run do
  let mut bs := PackedCodec.encodeInto (1 : UInt32) ByteArray.empty
  bs := countInto inputs bs
  for _ in [:inputs] do
    for _ in [:36] do bs := bs.push 0
    bs := bs.push 0
    for _ in [:4] do bs := bs.push 255
  bs := countInto outputs bs
  for _ in [:outputs] do
    bs := PackedCodec.encodeInto (1 : UInt64) bs
    bs := countInto scriptSize bs
    for _ in [:scriptSize] do bs := bs.push 81
  return PackedCodec.encodeInto (0 : UInt32) bs

/-- Parse inside IO so that each measured repetition calls the reader. -/
@[noinline] def parseOnce (bs : List UInt8) : IO Nat := do
  match Transaction.readBase bs with
  | .error _ => throw (IO.userError "generated transaction rejected")
  | .ok (tx, rest) =>
    if !rest.isEmpty then throw (IO.userError "unexpected remainder")
    return tx.inputs.val.length + tx.outputs.val.length

/-- Parse the same workload through the slice reader inside IO. -/
@[noinline] def parseSliceOnce (s : ByteSlice) : IO Nat := do
  match Transaction.readBaseSlice s with
  | .error _ => throw (IO.userError "generated transaction rejected")
  | .ok (tx, rest) =>
    if rest.size != 0 then throw (IO.userError "unexpected remainder")
    return tx.inputs.val.length + tx.outputs.val.length

/-- Report five individual times and their median, without generation or input conversion. -/
def measureReader (shape : String) (n bytes : Nat) (reader : String) (parse : IO Nat) : IO Unit := do
  let _ ← parse
  let mut samples : List Nat := []
  let mut checksum := 0
  for _ in [:5] do
    let start ← IO.monoNanosNow
    checksum := checksum + (← parse)
    samples := ((← IO.monoNanosNow) - start) :: samples
  let sorted := samples.mergeSort (· ≤ ·)
  let median := sorted[2]!
  let times := String.intercalate "," (samples.reverse.map toString)
  IO.println s!"{shape},{n},{bytes},{reader},{times},{median},{checksum}"

/-- Measure each generated workload with both readers on identical bytes. -/
def main (args : List String) : IO Unit := do
  IO.println "shape,size,bytes,reader,ns1,ns2,ns3,ns4,ns5,median_ns,checksum"
  let sliceOnly := args == ["--slice-large"]
  let shapes := if sliceOnly then ["inputs"] else ["inputs", "outputs", "scripts"]
  let sizes := if sliceOnly then [4000, 8000, 16000, 32000] else [500, 1000, 2000, 4000, 8000]
  for shape in shapes do
    for n in sizes do
      let bytes := if shape == "inputs" then workload n 1 0
        else if shape == "outputs" then workload 1 n 0
        else workload 1 4 n
      let bs := bytes.toList
      let slice := ByteSlice.ofByteArray bytes
      unless sliceOnly do measureReader shape n bytes.size "list" (parseOnce bs)
      measureReader shape n bytes.size "slice" (parseSliceOnce slice)
