(*  Title:      Pure/System/base64.ML
    Author:     Makarius

Support for Base64 data encoding (via Isabelle/Scala).
*)

signature BASE64 =
sig
  val decode: Bytes.T -> Bytes.T
  val encode: Bytes.T -> Bytes.T
end;

structure Base64: BASE64 =
struct

val decode = \<^scala>\<open>Base64.decode\<close>;
val encode = \<^scala>\<open>Base64.encode\<close>;

end;
