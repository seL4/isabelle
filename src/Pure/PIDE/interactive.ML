(*  Title:      Pure/PIDE/interactive.ML
    Author:     Makarius

Interactive mode, with subtle changes of semantics in some situations.
*)

signature INTERACTIVE =
sig
  val enabled: unit -> bool
  val setmp: bool -> ('a -> 'b) -> 'a -> 'b
  val parallel_proofs: unit -> int
end;

structure Interactive: INTERACTIVE =
struct

val system_option = "interactive";

fun enabled () = Options.default_bool system_option;
fun setmp b f x = Options.with_update_default [(system_option, Value.print_bool b)] f x;

fun parallel_proofs () =
  let
    val m = Options.default_int "parallel_proofs";
  in if not (enabled ()) then m else if m > 0 then 3 else 0 end;

end;
