(*  Title:      Pure/Thy/present.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Theory presentation abstract interface.

TODO:
  - presentation_modes: AND (!?);
*)

signature BASIC_PRESENT =
sig
  include BASIC_BROWSER_INFO
end;

signature PRESENT =
sig
  include BROWSER_INFO
end;

structure Present: PRESENT = BrowserInfo;	(* FIXME *)

structure BasicPresent: BASIC_PRESENT = Present;
open BasicPresent;
