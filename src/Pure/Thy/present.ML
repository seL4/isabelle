(*  Title:      Pure/Thy/present.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory presentation.            (* FIXME fake implementation *)
*)

signature BASIC_PRESENT =
sig
  val section: string -> unit
end;

signature PRESENT =
sig
  include BASIC_PRESENT
  val init: bool -> string list -> string list -> string -> string -> unit
  val finish: unit -> unit
  val theory_file: string -> string -> unit
  val thm: string -> thm -> unit
end;

structure Present: PRESENT =
struct

fun init _ _ _ _ _ = ();
fun finish _ = ();

fun section _ = ();
fun theory_file _ _ = ();
fun thm _ _ = ();

end;

structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
