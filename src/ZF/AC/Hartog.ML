(*  Title: 	ZF/AC/Hartog.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

  Some proofs on the Hartogs function.
*)

open Hartog;

goal thy "!!X. ALL a. Ord(a) --> a:X ==> P";
by (res_inst_tac [("X1","{y:X. Ord(y)}")] (ON_class RS revcut_rl) 1);
by (fast_tac AC_cs 1);
val Ords_in_set = result();

goalw thy [lepoll_def] "!!X. [| Ord(a); a lepoll X |] ==>  \
\		EX Y. Y<=X & (EX R. well_ord(Y,R) & ordertype(Y,R)=a)";
by (eresolve_tac [exE] 1);
by (REPEAT (resolve_tac [exI, conjI] 1));
by (eresolve_tac [inj_is_fun RS fun_is_rel RS image_subset] 1);
by (resolve_tac [exI] 1);
by (resolve_tac [conjI] 1);
by (eresolve_tac [well_ord_Memrel RSN (2, subset_refl RSN (2, 
	restrict_bij RS bij_converse_bij) RS bij_is_inj RS well_ord_rvimage)] 1
	THEN (atac 1));
by (resolve_tac [subset_refl RSN (2, restrict_bij RS bij_converse_bij) RS
	(well_ord_Memrel RSN (2, bij_ordertype_vimage)) RS 
	(ordertype_Memrel RSN (2, trans))] 1
	THEN (REPEAT (atac 1)));
val Ord_lepoll_imp_ex_well_ord = result();

goal thy "!!X. [| Ord(a); a lepoll X |] ==>  \
\		EX Y. Y<=X & (EX R. R<=X*X & ordertype(Y,R)=a)";
by (dresolve_tac [Ord_lepoll_imp_ex_well_ord] 1 THEN (atac 1));
by (step_tac AC_cs 1);
by (REPEAT (ares_tac [exI, conjI] 1));
by (eresolve_tac [ordertype_Int] 2);
by (fast_tac AC_cs 1);
val Ord_lepoll_imp_eq_ordertype = result();

goal thy "!!X. ALL a. Ord(a) --> a lepoll X ==>  \
\	ALL a. Ord(a) -->  \
\	a:{a. Z:Pow(X)*Pow(X*X), EX Y R. Z=<Y,R> & ordertype(Y,R)=a}";
by (REPEAT (resolve_tac [allI,impI] 1));
by (REPEAT (eresolve_tac [allE, impE] 1));
by (atac 1);
by (dresolve_tac [Ord_lepoll_imp_eq_ordertype] 1 THEN (atac 1));
by (fast_tac (AC_cs addSIs [ReplaceI] addEs [sym]) 1);
val Ords_lepoll_set_lemma = result();

goal thy "!!X. ALL a. Ord(a) --> a lepoll X ==> P";
by (eresolve_tac [Ords_lepoll_set_lemma RS Ords_in_set] 1);
val Ords_lepoll_set = result();

goal thy "EX a. Ord(a) & ~a lepoll X";
by (resolve_tac [swap] 1);
by (fast_tac AC_cs 1);
by (resolve_tac [Ords_lepoll_set] 1);
by (fast_tac AC_cs 1);
val ex_Ord_not_lepoll = result();

goalw thy [Hartog_def] "~ Hartog(A) lepoll A";
by (resolve_tac [ex_Ord_not_lepoll RS exE] 1);
by (resolve_tac [LeastI] 1);
by (REPEAT (fast_tac AC_cs 1));
val HartogI = result();

val HartogE = HartogI RS notE;

goalw thy [Hartog_def] "Ord(Hartog(A))";
by (resolve_tac [Ord_Least] 1);
val Ord_Hartog = result();

goalw thy [Hartog_def] "!!i. [| i < Hartog(A); ~ i lepoll A |] ==> P";
by (fast_tac (AC_cs addEs [less_LeastE]) 1);
val less_HartogE1 = result();

goal thy "!!i. [| i < Hartog(A); i eqpoll Hartog(A) |] ==> P";
by (fast_tac (AC_cs addEs [less_HartogE1, eqpoll_sym RS eqpoll_imp_lepoll
		RS lepoll_trans RS HartogE]) 1);
val less_HartogE = result();

goal thy "Card(Hartog(A))";
by (fast_tac (AC_cs addSIs [CardI, Ord_Hartog] addEs [less_HartogE]) 1);
val Card_Hartog = result();