(*  Title:      Pure/General/sha1_polyml.ML
    Author:     Sascha Boehme, TU Muenchen

Digesting strings according to SHA-1 (see RFC 3174) -- based on an
external implementation in C with a fallback to an internal
implementation.
*)

structure SHA1: SHA1 =
struct

fun hex_digit i = if i < 10 then chr (ord "0" + i) else chr (ord "a" + i - 10);

fun hex_string arr i =
  let val c = CInterface.fromCchar (CInterface.offset i CInterface.Cchar arr)
  in (op ^) (pairself hex_digit (Integer.div_mod (Char.ord c) 16)) end

fun digest_external str =
  let
    val digest = CInterface.alloc 20 CInterface.Cchar;
    val _ = CInterface.call3 (CInterface.get_sym "sha1" "sha1_buffer")
      (CInterface.STRING, CInterface.INT, CInterface.POINTER)
      CInterface.POINTER (str, size str, CInterface.address digest);
  in fold (suffix o hex_string digest) (0 upto 19) "" end;

fun digest str = digest_external str
  handle CInterface.Foreign _ => SHA1.digest str;

end;
