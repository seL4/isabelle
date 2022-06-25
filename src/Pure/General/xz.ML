(*  Title:      Pure/System/xz.ML
    Author:     Makarius

Support for XZ compression (via Isabelle/Scala).
*)

signature XZ =
sig
  val compress: Bytes.T -> Bytes.T
  val uncompress: Bytes.T -> Bytes.T
end;

structure XZ: XZ =
struct

val compress = \<^scala>\<open>XZ.compress\<close>;
val uncompress = \<^scala>\<open>XZ.uncompress\<close>;

end;
