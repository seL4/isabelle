
(* $Id$ *)

(* code by Sara Kalvala, based on Paulson's LK
                           and Moore's tisl.ML *)

theory Washing
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


(* "activate" definitions for use in proof *)

ML {* bind_thms ("changeI", [thm "context1"] RL ([thm "change"] RLN (2,[thm "cut"]))) *}
ML {* bind_thms ("load1I", [thm "context1"] RL ([thm "load1"] RLN (2,[thm "cut"]))) *}
ML {* bind_thms ("washI", [thm "context1"] RL ([thm "wash"] RLN (2,[thm "cut"]))) *}
ML {* bind_thms ("dryI", [thm "context1"] RL ([thm "dry"] RLN (2,[thm "cut"]))) *}

(* a load of dirty clothes and two dollars gives you clean clothes *)

lemma "dollar , dollar , dirty |- clean"
  apply (tactic {* best_tac (lazy_cs add_safes (thms "changeI" @ thms "load1I" @ thms "washI" @ thms "dryI")) 1 *})
  done

(* order of premises doesn't matter *)

lemma "dollar , dirty , dollar |- clean"
  apply (tactic {* best_tac (lazy_cs add_safes (thms "changeI" @ thms "load1I" @ thms "washI" @ thms "dryI")) 1 *})
  done

(* alternative formulation *)

lemma "dollar , dollar |- dirty -o clean"
  apply (tactic {* best_tac (lazy_cs add_safes (thms "changeI" @ thms "load1I" @ thms "washI" @ thms "dryI")) 1 *})
  done

end
