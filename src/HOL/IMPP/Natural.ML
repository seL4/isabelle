(*  Title:      HOL/IMPP/Natural.ML
    ID:         $Id$
    Author:     David von Oheimb, TUM
    Copyright   1999 TUM
*)

open Natural;

AddIs evalc.intrs;
AddIs evaln.intrs;

val evalc_elim_cases = map evalc.mk_cases
   ["<SKIP,s> -c-> t", "<X:==a,s> -c-> t", "<LOCAL Y:=a IN c,s> -c-> t", 
    "<c1;;c2,s> -c-> t","<IF b THEN c1 ELSE c2,s> -c-> t",
    "<BODY P,s> -c-> s1", "<X:=CALL P(a),s> -c-> s1"];
val evaln_elim_cases = map evaln.mk_cases
   ["<SKIP,s> -n-> t", "<X:==a,s> -n-> t", "<LOCAL Y:=a IN c,s> -n-> t",
    "<c1;;c2,s> -n-> t","<IF b THEN c1 ELSE c2,s> -n-> t",
    "<BODY P,s> -n-> s1", "<X:=CALL P(a),s> -n-> s1"];
val evalc_WHILE_case = evalc.mk_cases "<WHILE b DO c,s> -c-> t";
val evaln_WHILE_case = evaln.mk_cases "<WHILE b DO c,s> -n-> t";

AddSEs evalc_elim_cases;
AddSEs evaln_elim_cases;

(* evaluation of com is deterministic *)
Goal "<c,s> -c-> t ==> (!u. <c,s> -c-> u --> u=t)";
be evalc.induct 1;
by (thin_tac "<?c,s1> -c-> s2" 8);
(*blast_tac needs Unify.search_bound := 40*)
by (ALLGOALS (best_tac (claset() addEs [evalc_WHILE_case])));
qed_spec_mp "com_det";

Goal "<c,s> -n-> t ==> <c,s> -c-> t";
be evaln.induct 1;
by (ALLGOALS (resolve_tac evalc.intrs THEN_ALL_NEW atac));
qed "evaln_evalc";

goal Nat.thy "(Suc n <= m') --> (? m. m' = Suc m)";
by (induct_tac "m'" 1);
by  Auto_tac;
qed_spec_mp "Suc_le_D";

Goal "[| Suc n <= m'; (!!m. n <= m ==> P (Suc m)) |] ==> P m'";
by (cut_facts_tac (premises()) 1);
by (ftac Suc_le_D 1);
by (Clarify_tac 1);
by (eresolve_tac (premises()) 1);
qed "Suc_le_D_lemma";

Goal "<c,s> -n-> t ==> !m. n<=m --> <c,s> -m-> t";
be evaln.induct 1;
by (ALLGOALS (EVERY'[strip_tac,TRY o etac Suc_le_D_lemma, REPEAT o smp_tac 1]));
by (ALLGOALS (resolve_tac evaln.intrs THEN_ALL_NEW atac));
qed_spec_mp "evaln_nonstrict";

Goal "<c,s> -n-> s' ==> <c,s> -Suc n-> s'";
be evaln_nonstrict 1;
by Auto_tac;
qed "evaln_Suc";

Goal "[| <c1,s1> -n1-> t1;  <c2,s2> -n2-> t2 |] ==> \
\   ? n. <c1,s1> -n -> t1 & <c2,s2> -n -> t2";
by (cut_facts_tac [read_instantiate [("m","n1"),("n","n2")] nat_le_linear] 1);
by (blast_tac (claset() addDs [evaln_nonstrict]) 1);
qed "evaln_max2";

Goal "<c,s> -c-> t ==> ? n. <c,s> -n-> t";
be evalc.induct 1;
by (ALLGOALS (REPEAT o etac exE));
by (TRYALL(EVERY'[datac evaln_max2 1, REPEAT o eresolve_tac [exE, conjE]]));
by (ALLGOALS (rtac exI THEN' resolve_tac evaln.intrs THEN_ALL_NEW atac));
qed "evalc_evaln";

Goal "<c,s> -c-> t = (? n. <c,s> -n-> t)";
by (fast_tac (claset() addEs [evalc_evaln, evaln_evalc]) 1);
qed "eval_eq";
