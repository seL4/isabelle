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
  val thm: string -> thm -> unit
end;

structure Present: PRESENT =
struct

fun section _ = ();
fun thm _ _ = ();

end;

structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
