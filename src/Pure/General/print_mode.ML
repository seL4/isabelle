(*  Title:      Pure/General/print_mode.ML
    ID:         $Id$
    Author:     Makarius

Generic print mode as thread-local value derived from global template;
provides implicit configuration for various output mechanisms.
*)

signature BASIC_PRINT_MODE =
sig
  val print_mode: string list ref            (*global template*)
  val print_mode_value: unit -> string list  (*thread-local value*)
  val print_mode_active: string -> bool      (*thread-local value*)
end;

signature PRINT_MODE =
sig
  include BASIC_PRINT_MODE
  val input: string
  val internal: string
  val setmp: string list -> ('a -> 'b) -> 'a -> 'b
  val with_modes: string list -> ('a -> 'b) -> 'a -> 'b
  val closure: ('a -> 'b) -> 'a -> 'b
end;

structure PrintMode: PRINT_MODE =
struct

val input = "input";
val internal = "internal";

val print_mode = ref ([]: string list);
val tag = Universal.tag () : string list option Universal.tag;

fun print_mode_value () =
  let val modes =
    (case Multithreading.get_data tag of
      SOME (SOME modes) => modes
    | _ => NAMED_CRITICAL "print_mode" (fn () => ! print_mode))
  in subtract (op =) [input, internal] modes end;

fun print_mode_active mode = member (op =) (print_mode_value ()) mode;

fun setmp modes f x =
  let
    val orig_data =
      (case Multithreading.get_data tag of
        SOME (SOME orig_modes) => SOME orig_modes
      | _ => NONE);
    val _ = Multithreading.put_data (tag, SOME modes);
    val result = Exn.capture f x;
    val _ = Multithreading.put_data (tag, orig_data);
  in Exn.release result end;

fun with_modes modes f x = setmp (modes @ print_mode_value ()) f x;
fun closure f = with_modes [] f;

end;

structure BasicPrintMode: BASIC_PRINT_MODE = PrintMode;
open BasicPrintMode;
