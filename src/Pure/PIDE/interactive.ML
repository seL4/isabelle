(*  Title:      Pure/PIDE/interactive.ML
    Author:     Makarius

Interactive mode, with subtle changes of semantics in some situations.
*)

signature INTERACTIVE =
sig
  val enabled: unit -> bool
  val setmp: bool -> ('a -> 'b) -> 'a -> 'b
  val parallel_proofs: unit -> int
  val setmp_parallel_proofs: int -> ('a -> 'b) -> 'a -> 'b
end;

structure Interactive: INTERACTIVE =
struct

(* interactive mode *)

local val name = "interactive" in

fun enabled () = Options.default_bool name;
fun setmp b f x = Options.with_update_default [(name, Value.print_bool b)] f x;

end;


(* parallel proofs *)

local val name = "parallel_proofs" in

fun parallel_proofs () =
  let val m = Options.default_int name;
  in if not (enabled ()) then m else if m > 0 then 3 else 0 end;

fun setmp_parallel_proofs m f x =
  Options.with_update_default [(name, Value.print_int m)] f x;

end;

end;
