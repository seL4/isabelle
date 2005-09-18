
(* $Id$ *)

(* code by Sara Kalvala, based on Paulson's LK
                           and Moore's tisl.ML *)

theory washing
imports ILL
begin

consts
  dollar :: o
  quarter :: o
  loaded :: o
  dirty :: o
  wet :: o
  clean :: o

axioms
  change:
  "dollar |- (quarter >< quarter >< quarter >< quarter)"

  load1:
  "quarter , quarter , quarter , quarter , quarter |- loaded"

  load2:
  "dollar , quarter |- loaded"

  wash:
  "loaded , dirty |- wet"

  dry:
  "wet, quarter , quarter , quarter |- clean"

ML {* use_legacy_bindings (the_context ()) *}

end

