(*  Title:      ZF/AC/Hartog.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

  Some proofs on the Hartogs function.
*)

Goal "\\<forall>a. Ord(a) --> a \\<in> X ==> P";
by (res_inst_tac [("X1","{y \\<in> X. Ord(y)}")] (ON_class RS revcut_rl) 1);
by (Fast_tac 1);
qed "Ords_in_set";

Goalw [lepoll_def] "[| Ord(a); a lepoll X |] ==>  \
\               \\<exists>Y. Y \\<subseteq> X & (\\<exists>R. well_ord(Y,R) & ordertype(Y,R)=a)";
by (etac exE 1);
by (REPEAT (resolve_tac [exI, conjI] 1));
by (eresolve_tac [inj_is_fun RS fun_is_rel RS image_subset] 1);
by (rtac exI 1);
by (rtac conjI 1);
by (eresolve_tac [well_ord_Memrel RSN (2, subset_refl RSN (2, 
        restrict_bij RS bij_converse_bij) RS bij_is_inj RS well_ord_rvimage)] 1
        THEN (assume_tac 1));
by (resolve_tac [subset_refl RSN (2, restrict_bij RS bij_converse_bij) RS
        (well_ord_Memrel RSN (2, bij_ordertype_vimage)) RS 
        (ordertype_Memrel RSN (2, trans))] 1
        THEN (REPEAT (assume_tac 1)));
qed "Ord_lepoll_imp_ex_well_ord";

Goal "[| Ord(a); a lepoll X |] ==>  \
\               \\<exists>Y. Y \\<subseteq> X & (\\<exists>R. R \\<subseteq> X*X & ordertype(Y,R)=a)";
by (dtac Ord_lepoll_imp_ex_well_ord 1 THEN (assume_tac 1));
by Safe_tac;
by (REPEAT (ares_tac [exI, conjI] 1));
by (etac ordertype_Int 2);
by (Fast_tac 1);
qed "Ord_lepoll_imp_eq_ordertype";

Goal "\\<forall>a. Ord(a) --> a lepoll X ==>  \
\       \\<forall>a. Ord(a) -->  \
\       a:{a. Z \\<in> Pow(X)*Pow(X*X), \\<exists>Y R. Z=<Y,R> & ordertype(Y,R)=a}";
by (REPEAT (resolve_tac [allI,impI] 1));
by (REPEAT (eresolve_tac [allE, impE] 1));
by (assume_tac 1);
by (dtac Ord_lepoll_imp_eq_ordertype 1 THEN (assume_tac 1));
by (fast_tac (claset() addSIs [ReplaceI] addEs [sym]) 1);
qed "Ords_lepoll_set_lemma";

Goal "\\<forall>a. Ord(a) --> a lepoll X ==> P";
by (eresolve_tac [Ords_lepoll_set_lemma RS Ords_in_set] 1);
qed "Ords_lepoll_set";

Goal "\\<exists>a. Ord(a) & ~a lepoll X";
by (rtac swap 1);
by (Fast_tac 1);
by (rtac Ords_lepoll_set 1);
by (Fast_tac 1);
qed "ex_Ord_not_lepoll";

Goalw [Hartog_def] "~ Hartog(A) lepoll A";
by (resolve_tac [ex_Ord_not_lepoll RS exE] 1);
by (rtac LeastI 1);
by (REPEAT (Fast_tac 1));
qed "HartogI";

val HartogE = HartogI RS notE;

Goalw [Hartog_def] "Ord(Hartog(A))";
by (rtac Ord_Least 1);
qed "Ord_Hartog";

Goalw [Hartog_def] "[| i < Hartog(A); ~ i lepoll A |] ==> P";
by (fast_tac (claset() addEs [less_LeastE]) 1);
qed "less_HartogE1";

Goal "[| i < Hartog(A); i eqpoll Hartog(A) |] ==> P";
by (fast_tac (claset() addEs [less_HartogE1, eqpoll_sym RS eqpoll_imp_lepoll
                RS lepoll_trans RS HartogE]) 1);
qed "less_HartogE";

Goal "Card(Hartog(A))";
by (fast_tac (claset() addSIs [CardI, Ord_Hartog] addEs [less_HartogE]) 1);
qed "Card_Hartog";
