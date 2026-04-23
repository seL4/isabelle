(*  Title:      Pure/General/sha1.ML
    Author:     Makarius

Support for SHA1 (via Isabelle/Scala).
*)

signature SHA1 =
sig
  eqtype digest
  val rep: digest -> string
  val fake: string -> digest
  val digest_bytes: Bytes.T -> digest
  val digest: string -> digest
end;

structure SHA1: SHA1 =
struct

datatype digest = Digest of string;

fun rep (Digest s) = s;
val fake = Digest;

val digest_bytes = Digest o Bytes.content o \<^scala>\<open>SHA1.digest\<close>;
val digest = digest_bytes o Bytes.string;

val _ = ML_system_pp (fn _ => fn _ => ML_Pretty.str o quote o rep);

end;
