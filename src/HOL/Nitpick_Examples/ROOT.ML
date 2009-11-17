(*  Title:      HOL/Nitpick_Examples/ROOT.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Nitpick examples.
*)

Toplevel.debug := true;
if getenv "KODKODI" = "" then
  ()
else
  setmp_noncritical quick_and_dirty true use_thys
                    ["Nitpick_Examples"];
