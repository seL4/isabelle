(*  Title:      Pure/General/print_mode.ML
    ID:         $Id$
    Author:     Makarius

Generic print mode -- implicit configuration for various output
mechanisms.
*)

signature BASIC_PRINT_MODE =
sig
  val print_mode: string list ref
  val print_mode_value: unit -> string list
  val print_mode_active: string -> bool
end;

signature PRINT_MODE =
sig
  include BASIC_PRINT_MODE
  val input: string
  val internal: string
  val setmp: string list -> ('a -> 'b) -> 'a -> 'b
  val with_modes: string list -> ('a -> 'b) -> 'a -> 'b
end;

structure PrintMode: PRINT_MODE =
struct

val input = "input";
val internal = "internal";

val print_mode = ref ([]: string list);
fun get_mode () = subtract (op =) [input, internal] (! print_mode);

fun print_mode_value () = NAMED_CRITICAL "print_mode" get_mode;
fun print_mode_active s = member (op =) (print_mode_value ()) s;

fun setmp modes f x = NAMED_CRITICAL "print_mode" (fn () => Library.setmp print_mode modes f x);
fun with_modes modes f x = NAMED_CRITICAL "print_mode" (fn () => setmp (modes @ ! print_mode) f x);

end;

structure BasicPrintMode: BASIC_PRINT_MODE = PrintMode;
open BasicPrintMode;
