module

public import DogeLib.Cryptography.Secp256k1.Ecdsa

/-!
# ECDSA known answer

Wycheproof P1363 case 1 at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9` accepts this signature.
The input and expectation come through EthLib `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, under CC0 1.0 for code and Apache 2.0 for vector data.
The vector licence is in `tests/cryptography/secp256k1/LICENSE`.
This file states the vector on coordinates and scalars without a public-key parser.
-/

@[expose] public section

namespace DogeLib.Cryptography.Secp256k1.Ecdsa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Wycheproof P1363 case 1 verifies with the stated coordinates, digest bytes, R and S. -/
theorem wycheproof_p1363_1 :
    verify (.affine 0xb838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6f 0xf0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9)
      ⟨[0xbb, 0x5a, 0x52, 0xf4, 0x2f, 0x9c, 0x92, 0x61, 0xed, 0x43, 0x61, 0xf5, 0x94, 0x22, 0xa1, 0xe3, 0x00, 0x36, 0xe7, 0xc3, 0x2b, 0x27, 0x0c, 0x88, 0x07, 0xa4, 0x19, 0xfe, 0xca, 0x60, 0x50, 0x23], by decide⟩
      0x813ef79ccefa9a56f7ba805f0e478584fe5f0dd5f567bc09b5123ccbc9832365 0x900e75ad233fcc908509dbff5922647db37c21f4afd3203ae8dc4ae7794b0f87 = true := by
  decide +kernel

end DogeLib.Cryptography.Secp256k1.Ecdsa
