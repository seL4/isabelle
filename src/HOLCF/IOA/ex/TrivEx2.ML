(*  Title:      HOLCF/IOA/TrivEx.thy
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1995  TU Muenchen

Trivial Abstraction Example
*)

val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by (fast_tac (claset() addDs prems) 1);
qed "imp_conj_lemma";


Goalw [is_abstraction_def] 
"is_abstraction h_abs C_ioa A_ioa";
by (rtac conjI 1);
(* ------------- start states ------------ *)
by (simp_tac (simpset() addsimps 
    [h_abs_def,starts_of_def,C_ioa_def,A_ioa_def]) 1);
(* -------------- step case ---------------- *)
by (REPEAT (rtac allI 1));
by (rtac imp_conj_lemma 1);
by (simp_tac (simpset() addsimps [trans_of_def,
        C_ioa_def,A_ioa_def,C_trans_def,A_trans_def])1);
by (induct_tac "a" 1);
by (simp_tac (simpset() addsimps [h_abs_def]) 1);
qed"h_abs_is_abstraction";


(*
Goalw [xt2_def,plift,option_lift]
  "(xt2 (plift afun)) (s,a,t) = (afun a)";
(* !!!!!!!!!!!!! Occurs check !!!! *)
by (induct_tac "a" 1);

*)

Goalw [Enabled_def, enabled_def, h_abs_def,A_ioa_def,C_ioa_def,A_trans_def,
           C_trans_def,trans_of_def] 
"!!s. Enabled A_ioa {INC} (h_abs s) ==> Enabled C_ioa {INC} s";
by Auto_tac;
qed"Enabled_implication";


Goalw [is_live_abstraction_def]
"is_live_abstraction h_abs (C_ioa, WF C_ioa {INC}) (A_ioa, WF A_ioa {INC})";
by Auto_tac;
(* is_abstraction *)
by (rtac h_abs_is_abstraction 1);
(* temp_weakening *)
by (abstraction_tac 1);
by (etac Enabled_implication 1);
qed"h_abs_is_liveabstraction";


Goalw [C_live_ioa_def]
"validLIOA C_live_ioa (<>[] <%(n,a,m). n~=0>)";
by (rtac AbsRuleT2 1);
by (rtac h_abs_is_liveabstraction 1);
by (rtac MC_result 1);
by (abstraction_tac 1);
by (asm_full_simp_tac (simpset() addsimps [h_abs_def]) 1);
qed"TrivEx2_abstraction";


(*
Goal "validIOA aut_ioa (Box (Init (%(s,a,t). a= Some(Alarm(APonR)))) 
IMPLIES (Next (Init (%(s,a,t). info_comp(s) = APonR))))";

*)

