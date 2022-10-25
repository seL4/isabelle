(*  Title:      Pure/General/zstd.ML
    Author:     Makarius

Support for Zstd compression (via Isabelle/Scala).
*)

signature Zstd =
sig
  val compress: Bytes.T -> Bytes.T
  val uncompress: Bytes.T -> Bytes.T
end;

structure Zstd: Zstd =
struct

val compress = \<^scala>\<open>Zstd.compress\<close>;
val uncompress = \<^scala>\<open>Zstd.uncompress\<close>;

end;
