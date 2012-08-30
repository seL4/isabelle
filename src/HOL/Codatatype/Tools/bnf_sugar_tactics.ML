(*  Title:      HOL/Codatatype/Tools/bnf_sugar_tactics.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Tactics for sugar on top of a BNF.
*)

signature BNF_SUGAR_TACTICS =
sig
  val mk_nchotomy_tac: int -> thm -> tactic
  val mk_half_disc_disjoint_tac: int -> thm -> thm -> tactic
  val mk_other_half_disc_disjoint_tac: thm -> tactic
end;

structure BNF_Sugar_Tactics : BNF_SUGAR_TACTICS =
struct

open BNF_FP_Util

fun mk_nchotomy_tac n exhaust =
  (rtac allI THEN' rtac exhaust THEN'
   EVERY' (maps (fn k => [rtac (mk_disjIN n k), REPEAT_DETERM o rtac exI, atac]) (1 upto n))) 1;

fun mk_half_disc_disjoint_tac m disc_def disc'_thm =
  (dtac (disc_def RS iffD1) THEN'
   REPEAT_DETERM_N m o etac exE THEN'
   hyp_subst_tac THEN'
   rtac disc'_thm) 1;

fun mk_other_half_disc_disjoint_tac half_thm =
  (etac @{thm contrapos_pn} THEN' etac half_thm) 1;

end;
