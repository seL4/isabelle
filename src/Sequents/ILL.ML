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

val aux_impl = prove_goal thy "$F, $G |- A ==> $F, !(A -o B), $G |- B"
(fn prems => [rtac derelict 1 THEN rtac impl 1 THEN rtac identity 2
	THEN rtac context1 1 THEN rtac (hd(prems)) 1]);

val conj_lemma =
prove_goal thy " $F, !A, !B, $G |- C ==> $F, !(A && B), $G |- C"
(fn prems => [rtac contract 1,
	res_inst_tac [("A","(!A) >< (!B)")] cut 1,
	rtac tensr 2,
	rtac (auto "! (A && B) |- !A") 3,
	rtac (auto "! (A && B) |- !B") 3,
	rtac context1 2,
	rtac tensl 2,
	rtac (hd(prems)) 2,
	rtac context3 1,
	rtac context3 1,
	rtac context1 1]);

val impr_contract =
prove_goal thy "!A, !A, $G |- B ==> $G |- (!A) -o B"
(fn prems => [rtac impr 1 THEN rtac contract 1
		 THEN rtac (hd(prems)) 1]);


val impr_contr_der =
prove_goal thy "A, !A, $G |- B ==> $G |- (!A) -o B"
(fn prems => [rtac impr 1 THEN rtac contract 1 THEN rtac derelict 1
		 THEN rtac (hd(prems)) 1]);

val contrad1 =
prove_goal thy "$F, (!B) -o 0, $G, !B, $H |- A"
(fn _ => [rtac impl 1,rtac identity 3,rtac context3 1,rtac context1 1,
	  rtac zerol 1]);


val contrad2 =
prove_goal thy "$F, !B, $G, (!B) -o 0, $H |- A"
(fn _ => [rtac impl 1,rtac identity 3,rtac context3 1,rtac context1 1,
	  rtac zerol 1]);

val ll_mp =
prove_goal thy "A -o B, A |- B"
(fn _ => [rtac impl 1 THEN rtac identity 2 THEN rtac identity 2
	 THEN rtac context1 1]);

val mp_rule1 =
prove_goal thy "$F, B, $G, $H |- C ==> $F, A, $G, A -o B, $H |- C"
(fn prems => [res_inst_tac [("A","B")] cut 1, rtac ll_mp 2,
		rtac (hd(prems)) 2, rtac context3 1, rtac context3 1,
		rtac context1 1]);

val mp_rule2 =
prove_goal thy "$F, B, $G, $H |- C ==> $F, A -o B, $G, A, $H |- C"
(fn prems => [res_inst_tac [("A","B")] cut 1, rtac ll_mp 2,
		rtac (hd(prems)) 2, rtac context3 1, rtac context3 1,
		rtac context1 1]);

val or_to_and =
prove_goal thy "!((!(A ++ B)) -o 0) |- !( ((!A) -o 0) && ((!B) -o 0))"
(fn _ => [best_tac lazy_cs 1]);

val o_a_rule =
prove_goal thy "$F, !( ((!A) -o 0) && ((!B) -o 0)), $G |- C ==> \
\         $F, !((!(A ++ B)) -o 0), $G |- C"
(fn prems => [rtac cut 1, rtac or_to_and 2, rtac (hd(prems)) 2,
		rtac context3 1, rtac context1 1]);



val conj_imp =
 prove_goal thy "((!A) -o C) ++ ((!B) -o C) |- (!(A && B)) -o C"
(fn _ => [rtac impr 1,rtac conj_lemma 1, rtac disjl 1,
	  ALLGOALS (rtac mp_rule1 THEN' best_tac lazy_cs)]);


val not_imp = auto "!A, !((!B) -o 0) |- (!((!A) -o B)) -o 0";

val a_not_a =
prove_goal thy "!A -o (!A -o 0) |- !A -o 0"
     (fn _ => [rtac impr 1, rtac contract 1, rtac impl 1,
	  rtac context1 1 THEN rtac identity 2, best_tac lazy_cs 1]);

val a_not_a_rule =
prove_goal thy "$J1, !A -o 0, $J2 |- B ==> $J1, !A -o (!A -o 0), $J2 |- B"
 (fn prems => [res_inst_tac [("A","!A -o 0")] cut 1,
               rtac a_not_a 2 THEN rtac (hd(prems)) 2
		 THEN best_tac lazy_cs 1]);

fun thm_to_rule x y =
prove_goal thy x (fn prems => [rtac cut 1, rtac y 2, rtac (hd(prems)) 2,
				best_tac lazy_cs 1]);

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
