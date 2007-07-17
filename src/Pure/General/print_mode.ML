(*  Title:      Pure/General/print_mode.ML
    ID:         $Id$
    Author:     Makarius

Generic print mode -- implicit configuration for various output
mechanisms.
*)

signature PRINT_MODE =
sig
  val print_mode: string list ref
  val print_mode_active: string -> bool
end;

structure PrintMode: PRINT_MODE =
struct

val print_mode = ref ([]: string list);
fun print_mode_active s = member (op =) (! print_mode) s;

end;

open PrintMode;
