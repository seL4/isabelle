(*  Title:      Pure/General/message_digest.ML
    Author:     Makarius

Support for message digests: SHA1, SHA256.
*)

signature MESSAGE_DIGEST =
sig
  eqtype T
  val kind: T -> string
  val rep: T -> string
  val rep_short: T -> string
  val fake: {kind: string, rep: string} -> T
end;

signature MESSAGE_DIGEST_OPS =
sig
  eqtype T
  val kind: string
  val fake: string -> T
  val digest_bytes: Bytes.T -> T
  val digest: string -> T
end;


structure Message_Digest: MESSAGE_DIGEST =
struct

datatype T = T of {kind: string, rep: string};

fun kind (T {kind, ...}) = kind;
fun rep (T {rep, ...}) = rep;
fun rep_short t = String.substring (rep t, 0, 12);

val fake = T;

val _ = ML_system_pp (fn _ => fn _ => ML_Pretty.str o quote o rep);

end;


functor Message_Digest_Ops(val kind: string val scala_fun: Bytes.T -> Bytes.T): MESSAGE_DIGEST_OPS =
struct

type T = Message_Digest.T;

val kind = kind;

fun fake rep = Message_Digest.fake {kind = kind, rep = rep};

fun digest_bytes bs =
  Message_Digest.fake {kind = kind, rep = Bytes.content (scala_fun bs)};

val digest = digest_bytes o Bytes.string;

end;

structure SHA1 = Message_Digest_Ops(val kind = "SHA1" val scala_fun = \<^scala>\<open>SHA1.digest\<close>);
structure SHA256 = Message_Digest_Ops(val kind = "SHA256" val scala_fun = \<^scala>\<open>SHA256.digest\<close>);
