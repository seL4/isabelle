(*  Title:      Pure/Thy/present.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory presentation abstract interface.
*)

signature BASIC_PRESENT =
sig
  include BASIC_BROWSER_INFO
end;

signature PRESENT =
sig
  include BROWSER_INFO
  val theory_source_presenter:
    (bool -> string -> (string, string list) Source.source * Position.T -> unit) -> unit
end;

structure Present: PRESENT =
struct

(*mostly fall back on BrowserInfo for the time being*)
open BrowserInfo;


(* theory source presenters *)

local
  val presenters =
    ref ([]: (bool -> string -> (string, string list) Source.source  * Position.T -> unit) list);
in
  fun theory_source_presenter f = presenters := f :: ! presenters;
  fun theory_source is_old name src = seq (fn f => f is_old name src) (! presenters);
end;


end;

Present.theory_source_presenter BrowserInfo.theory_source;

structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
