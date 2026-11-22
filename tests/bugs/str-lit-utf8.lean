-- Non-ASCII string literal reduction: a UTF-8 string literal reduces to
-- `String.ofList` over its Unicode scalar values (`Char.ofNat`), NOT over
-- its raw UTF-8 bytes.
--
-- Covers 2-byte (`é`, U+00E9), 3-byte (`€`, U+20AC), and 4-byte non-BMP
-- (`😀`, U+1F600) UTF-8 sequences.

theorem strLitUtf8 :
    "é€😀" = String.ofList [Char.ofNat 0xE9, Char.ofNat 0x20AC, Char.ofNat 0x1F600] :=
  rfl
