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
  "dollar \<turnstile> (quarter >< quarter >< quarter >< quarter)" and

  load1:
  "quarter , quarter , quarter , quarter , quarter \<turnstile> loaded" and

  load2:
  "dollar , quarter \<turnstile> loaded" and

  wash:
  "loaded , dirty \<turnstile> wet" and

  dry:
  "wet, quarter , quarter , quarter \<turnstile> clean"


(* "activate" definitions for use in proof *)

ML \<open>ML_Thms.bind_thms ("changeI", [@{thm context1}] RL ([@{thm change}] RLN (2,[@{thm cut}])))\<close>
ML \<open>ML_Thms.bind_thms ("load1I", [@{thm context1}] RL ([@{thm load1}] RLN (2,[@{thm cut}])))\<close>
ML \<open>ML_Thms.bind_thms ("washI", [@{thm context1}] RL ([@{thm wash}] RLN (2,[@{thm cut}])))\<close>
ML \<open>ML_Thms.bind_thms ("dryI", [@{thm context1}] RL ([@{thm dry}] RLN (2,[@{thm cut}])))\<close>

(* a load of dirty clothes and two dollars gives you clean clothes *)

lemma "dollar , dollar , dirty \<turnstile> clean"
  by (best add!: changeI load1I washI dryI)

(* order of premises doesn't matter *)

lemma "dollar , dirty , dollar \<turnstile> clean"
  by (best add!: changeI load1I washI dryI)

(* alternative formulation *)

lemma "dollar , dollar \<turnstile> dirty -o clean"
  by (best add!: changeI load1I washI dryI)

end
