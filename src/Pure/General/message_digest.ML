(*  Title:      Pure/General/message_digest.ML
    Author:     Makarius

Support for message digests: SHA1, SHA256.
*)

signature MESSAGE_DIGEST =
sig
  type T
  val ord: T ord
  val eq: T * T -> bool
  structure Table: TABLE
  structure Set: SET
  val prefix: T -> string
  val kind: T -> string
  val rep: T -> string
  val rep_short: T -> string
  val print_prefix: T -> string
  val print_prefix_short: T -> string
  val parse: string -> T
end;

signature MESSAGE_DIGEST_OPS =
sig
  type T
  val prefix: string
  val kind: string
  val parse: string -> T
  val digest_bytes: Bytes.T -> T
  val digest: string -> T
end;


structure Message_Digest: MESSAGE_DIGEST =
struct

(* general operations *)

abstype T = T of {prefix: string, rep: string}
with
  fun dest (T args) = args
  val make = T
end;

val ord = string_ord o apply2 (#rep o dest);
val eq = is_equal o ord;

structure Table = Table(type key = T val ord = ord);
structure Set = Set(Table.Key);

val prefix = #prefix o dest;
val kind = unsuffix ":" o prefix;

val rep = #rep o dest;
fun rep_short t = String.substring (rep t, 0, 12);

fun print_prefix t = prefix t ^ rep t;
fun print_prefix_short t = prefix t ^ rep_short t;

val _ = ML_system_pp (fn _ => fn _ => ML_Pretty.str o quote o print_prefix_short);


(* particular instances *)

val instances = [("SHA1:", 40), ("SHA256:", 64)];

val digits_ok =
  String.forall (fn c => #"0" <= c andalso c <= #"9" orelse #"a" <= c andalso c <= #"f");

fun parse rep =
  if not (digits_ok rep) then error ("Bad message digest content " ^ quote rep)
  else
    let val m = size rep in
      (case instances |> get_first (fn (p, n) => if m = n then SOME p else NONE) of
        NONE =>
          error ("Bad message digest length " ^ Value.print_int m ^
            (instances |> map (fn (p, n) => Value.print_int n ^ " for " ^ unsuffix ":" p)
              |> space_implode " or " |> enclose "\n(expected " ")"))
      | SOME prefix => make {prefix = prefix, rep = rep})
    end;

end;

functor Message_Digest_Ops(val kind: string val scala_fun: Bytes.T -> Bytes.T): MESSAGE_DIGEST_OPS =
struct

type T = Message_Digest.T;

val kind = kind;
val prefix = kind ^ ":";

fun parse rep =
  let val t = Message_Digest.parse rep in
    if Message_Digest.kind t = kind then t
    else error ("Bad message digest " ^ Message_Digest.print_prefix_short t ^
      " (expected " ^ kind ^ ")")
  end;

val digest_bytes = parse o Bytes.content o scala_fun;
val digest = digest_bytes o Bytes.string;

end;

structure SHA1 = Message_Digest_Ops(val kind = "SHA1" val scala_fun = \<^scala>\<open>SHA1.digest\<close>);
structure SHA256 = Message_Digest_Ops(val kind = "SHA256" val scala_fun = \<^scala>\<open>SHA256.digest\<close>);
