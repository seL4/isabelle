(*  Title:      Sequents/ILL.ML
    ID:         $Id$
    Author:     Sara Kalvala and Valeria de Paiva
    Copyright   1992  University of Cambridge

*)

val lazy_cs = empty_pack
 add_safes [tensl, conjr, disjl, promote0,
	    context2,context3]
 add_unsafes [identity, zerol, conjll, conjlr, disjrl, disjrr,
	       impr, tensr, impl, derelict, weaken,
		 promote1, promote2,context1,context4a,context4b];

fun prom_tac n = REPEAT (resolve_tac [promote0,promote1,promote2] n);

fun auto x = prove_goal thy x (fn prems => [best_tac lazy_cs 1]);

Goal "$F, $G |- A ==> $F, !(A -o B), $G |- B";
by (rtac derelict 1);
by (rtac impl 1);
by (rtac identity 2);
by (rtac context1 1);
by (assume_tac 1);
qed "aux_impl";

Goal " $F, !A, !B, $G |- C ==> $F, !(A && B), $G |- C";
by (rtac contract 1);
by (res_inst_tac [("A","(!A) >< (!B)")] cut 1);
by (rtac tensr 2);
by (rtac (auto "! (A && B) |- !A") 3);
by (rtac (auto "! (A && B) |- !B") 3);
by (rtac context1 2);
by (rtac tensl 2);
by (assume_tac 2);
by (rtac context3 1);
by (rtac context3 1);
by (rtac context1 1);
qed "conj_lemma";

Goal "!A, !A, $G |- B ==> $G |- (!A) -o B";
by (rtac impr 1);
by (rtac contract 1);
by (assume_tac 1);
qed "impr_contract";


Goal "A, !A, $G |- B ==> $G |- (!A) -o B";
by (rtac impr 1);
by (rtac contract 1);
by (rtac derelict 1);
by (assume_tac 1);
qed "impr_contr_der";

val _ = goal thy "$F, (!B) -o 0, $G, !B, $H |- A";
by (rtac impl 1);
by (rtac identity 3);
by (rtac context3 1);
by (rtac context1 1);
by (rtac zerol 1);
qed "contrad1";


val _ = goal thy "$F, !B, $G, (!B) -o 0, $H |- A";
by (rtac impl 1);
by (rtac identity 3);
by (rtac context3 1);
by (rtac context1 1);
by (rtac zerol 1);
qed "contrad2";

val _ = goal thy "A -o B, A |- B";
by (rtac impl 1);
by (rtac identity 2);
by (rtac identity 2);
by (rtac context1 1);
qed "ll_mp";

Goal "$F, B, $G, $H |- C ==> $F, A, $G, A -o B, $H |- C";
by (res_inst_tac [("A","B")] cut 1);
by (rtac ll_mp 2);
by (assume_tac 2);
by (rtac context3 1);
by (rtac context3 1);
by (rtac context1 1);
qed "mp_rule1";

Goal "$F, B, $G, $H |- C ==> $F, A -o B, $G, A, $H |- C";
by (res_inst_tac [("A","B")] cut 1);
by (rtac ll_mp 2);
by (assume_tac 2);
by (rtac context3 1);
by (rtac context3 1);
by (rtac context1 1);
qed "mp_rule2";

val _ = goal thy "!((!(A ++ B)) -o 0) |- !( ((!A) -o 0) && ((!B) -o 0))";
by (best_tac lazy_cs 1);
qed "or_to_and";

Goal "$F, !( ((!A) -o 0) && ((!B) -o 0)), $G |- C ==> \
\         $F, !((!(A ++ B)) -o 0), $G |- C";
by (rtac cut 1);
by (rtac or_to_and 2);
by (assume_tac 2);
by (rtac context3 1);
by (rtac context1 1);
qed "o_a_rule";



val _ = goal thy "((!A) -o C) ++ ((!B) -o C) |- (!(A && B)) -o C";
by (rtac impr 1);
by (rtac conj_lemma 1);
by (rtac disjl 1);
by (ALLGOALS (rtac mp_rule1 THEN' best_tac lazy_cs));
qed "conj_imp";


val not_imp = auto "!A, !((!B) -o 0) |- (!((!A) -o B)) -o 0";

Goal "!A -o (!A -o 0) |- !A -o 0";
by (rtac impr 1);
by (rtac contract 1);
by (rtac impl 1);
by (rtac identity 3);
by (rtac context1 1);
by (best_tac lazy_cs 1);
qed "a_not_a";

Goal "$J1, !A -o 0, $J2 |- B ==> $J1, !A -o (!A -o 0), $J2 |- B";
by (res_inst_tac [("A","!A -o 0")] cut 1);
by (rtac a_not_a 2);
by (assume_tac 2);
by (best_tac lazy_cs 1);
qed "a_not_a_rule";

fun thm_to_rule x y =
    prove_goal thy x
      (fn [prem] => [(rtac cut 1), (rtac y 2), (rtac prem 2),
	 	     (best_tac lazy_cs 1)]);

val safe_cs = lazy_cs add_safes [conj_lemma, ll_mp,contrad1,
				 contrad2, mp_rule1, mp_rule2, o_a_rule,
				 a_not_a_rule]
		      add_unsafes [aux_impl];

val power_cs = safe_cs add_unsafes [impr_contr_der];

fun auto1 x = prove_goal thy x (fn prems => [best_tac safe_cs 1]) ;

fun auto2 x = prove_goal thy x (fn prems => [best_tac power_cs 1]) ;


(* some examples from Troelstra and van Dalen

auto1  "!((!A) -o ((!B) -o 0)) |- (!(A && B)) -o 0";

auto1  "!((!(A && B)) -o 0) |- !((!A) -o ((!B) -o 0))";

auto1  "!( (!((! ((!A) -o B) ) -o 0)) -o 0) |- \
\        (!A) -o ( (!  ((!B) -o 0)) -o 0)";


auto2  "!(  (!A) -o ( (!  ((!B) -o 0)) -o 0) ) |- \
\         (!((! ((!A) -o B) ) -o 0)) -o 0";


                                                         *)
