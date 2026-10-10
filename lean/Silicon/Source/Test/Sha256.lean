import Silicon.Source.Sha256

/-!
These tests check SHA-256 against the test vectors of FIPS 180-4. They also check the padding
at the block limits, where a message of 55 bytes takes one block and one of 56 bytes takes two.
-/

namespace Silicon.Source.Test.Sha256

open Silicon.Source.Sha256

def digest (s : String) : String := hex (hash s.toUTF8)

#guard digest "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard digest "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard digest "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard digest ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
    "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"

/-! One million bytes `a`. -/
#guard hex (hash (ByteArray.mk (Array.replicate 1000000 97))) ==
  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

/-! The padding at the block limits: 55, 56, and 64 bytes. -/
#guard (pad (ByteArray.mk (Array.replicate 55 0))).size == 64
#guard (pad (ByteArray.mk (Array.replicate 56 0))).size == 128
#guard (pad (ByteArray.mk (Array.replicate 64 0))).size == 128
#guard digest (String.ofList (List.replicate 55 'a')) ==
  "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#guard digest (String.ofList (List.replicate 56 'a')) ==
  "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
#guard digest (String.ofList (List.replicate 64 'a')) ==
  "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"

end Silicon.Source.Test.Sha256
