(*  Title:      Sequents/Washing.thy
    Author:     Sara Kalvala
*)

theory Washing
imports ILL
begin

axiomatization
  dollar :: o and
  quarter :: o and
  loaded :: o and
  dirty :: o and
  wet :: o and
  clean :: o
where
  change:
  "dollar |- (quarter >< quarter >< quarter >< quarter)" and

  load1:
  "quarter , quarter , quarter , quarter , quarter |- loaded" and

  load2:
  "dollar , quarter |- loaded" and

  wash:
  "loaded , dirty |- wet" and

  dry:
  "wet, quarter , quarter , quarter |- clean"


(* "activate" definitions for use in proof *)

ML {* bind_thms ("changeI", [@{thm context1}] RL ([@{thm change}] RLN (2,[@{thm cut}]))) *}
ML {* bind_thms ("load1I", [@{thm context1}] RL ([@{thm load1}] RLN (2,[@{thm cut}]))) *}
ML {* bind_thms ("washI", [@{thm context1}] RL ([@{thm wash}] RLN (2,[@{thm cut}]))) *}
ML {* bind_thms ("dryI", [@{thm context1}] RL ([@{thm dry}] RLN (2,[@{thm cut}]))) *}

(* a load of dirty clothes and two dollars gives you clean clothes *)

lemma "dollar , dollar , dirty |- clean"
  by (best add!: changeI load1I washI dryI)

(* order of premises doesn't matter *)

lemma "dollar , dirty , dollar |- clean"
  by (best add!: changeI load1I washI dryI)

(* alternative formulation *)

lemma "dollar , dollar |- dirty -o clean"
  by (best add!: changeI load1I washI dryI)

end
