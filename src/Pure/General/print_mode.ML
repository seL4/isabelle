(*  Title:      Pure/General/print_mode.ML
    ID:         $Id$
    Author:     Makarius

Generic print mode -- implicit configuration for various output
mechanisms.
*)

signature BASIC_PRINT_MODE =
sig
  val print_mode: string list ref
  val print_mode_active: string -> bool
end;

signature PRINT_MODE =
sig
  include BASIC_PRINT_MODE
  val with_modes: string list -> ('a -> 'b) -> 'a -> 'b
  val with_default: ('a -> 'b) -> 'a -> 'b
end;

structure PrintMode: PRINT_MODE =
struct

val print_mode = ref ([]: string list);
fun print_mode_active s = member (op =) (! print_mode) s;

fun with_modes [] f x = f x
  | with_modes modes f x = NAMED_CRITICAL "print_mode" (fn () =>
      setmp print_mode (modes @ ! print_mode) f x);

fun with_default f x = NAMED_CRITICAL "print_mode" (fn () =>
  setmp print_mode [] f x);

end;

structure BasicPrintMode: BASIC_PRINT_MODE = PrintMode;
open BasicPrintMode;
