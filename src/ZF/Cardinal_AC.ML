(*  Title: 	ZF/Cardinal_AC.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal arithmetic WITH the Axiom of Choice

These results help justify infinite-branching datatypes
*)

open Cardinal_AC;

(*** Strengthened versions of existing theorems about cardinals ***)

goal Cardinal_AC.thy "|A| eqpoll A";
by (resolve_tac [AC_well_ord RS exE] 1);
by (eresolve_tac [well_ord_cardinal_eqpoll] 1);
val cardinal_eqpoll = result();

val cardinal_idem = cardinal_eqpoll RS cardinal_cong;

goal Cardinal_AC.thy "!!X Y. |X| = |Y| ==> X eqpoll Y";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [well_ord_cardinal_eqE] 1);
by (REPEAT_SOME assume_tac);
val cardinal_eqE = result();

goal Cardinal_AC.thy "!!A B. A lepoll B ==> |A| le |B|";
by (resolve_tac [AC_well_ord RS exE] 1);
by (eresolve_tac [well_ord_lepoll_imp_le] 1);
by (assume_tac 1);
val lepoll_imp_le = result();

goal Cardinal_AC.thy "(i |+| j) |+| k = i |+| (j |+| k)";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [well_ord_cadd_assoc] 1);
by (REPEAT_SOME assume_tac);
val cadd_assoc = result();

goal Cardinal_AC.thy "(i |*| j) |*| k = i |*| (j |*| k)";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [well_ord_cmult_assoc] 1);
by (REPEAT_SOME assume_tac);
val cmult_assoc = result();

goal Cardinal_AC.thy "!!A. InfCard(|A|) ==> A*A eqpoll A";
by (resolve_tac [AC_well_ord RS exE] 1);
by (eresolve_tac [well_ord_InfCard_square_eq] 1);
by (assume_tac 1);
val InfCard_square_eq = result();


(*** Other applications of AC ***)

goal Cardinal_AC.thy "!!A B. |A| le |B| ==> A lepoll B";
by (resolve_tac [cardinal_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll RS 
		 lepoll_trans] 1);
by (eresolve_tac [le_imp_subset RS subset_imp_lepoll RS lepoll_trans] 1);
by (resolve_tac [cardinal_eqpoll RS eqpoll_imp_lepoll] 1);
val le_imp_lepoll = result();

goal Cardinal_AC.thy "!!A K. Card(K) ==> |A| le K <-> A lepoll K";
by (eresolve_tac [Card_cardinal_eq RS subst] 1 THEN
    rtac iffI 1 THEN
    DEPTH_SOLVE (eresolve_tac [le_imp_lepoll,lepoll_imp_le] 1));
val le_Card_iff = result();

goalw Cardinal_AC.thy [surj_def] "!!f. f: surj(X,Y) ==> EX g. g: inj(Y,X)";
by (etac CollectE 1);
by (res_inst_tac [("A1", "Y"), ("B1", "%y. f-``{y}")] (AC_Pi RS exE) 1);
by (fast_tac (ZF_cs addSEs [apply_Pair]) 1);
by (resolve_tac [exI] 1);
by (rtac f_imp_injective 1);
by (resolve_tac [Pi_type] 1 THEN assume_tac 1);
by (fast_tac (ZF_cs addDs [apply_type] addEs [memberPiE]) 1);
by (fast_tac (ZF_cs addDs [apply_type] addEs [apply_equality]) 1);
val surj_implies_inj = result();

(*Kunen's Lemma 10.20*)
goal Cardinal_AC.thy "!!f. f: surj(X,Y) ==> |Y| le |X|";
by (resolve_tac [lepoll_imp_le] 1);
by (eresolve_tac [surj_implies_inj RS exE] 1);
by (rewtac lepoll_def);
by (eresolve_tac [exI] 1);
val surj_implies_cardinal_le = result();

(*Kunen's Lemma 10.21*)
goal Cardinal_AC.thy
    "!!K. [| InfCard(K);  ALL i:K. |X(i)| le K |] ==> |UN i:K. X(i)| le K";
by (asm_full_simp_tac (ZF_ss addsimps [InfCard_is_Card, le_Card_iff]) 1);
by (resolve_tac [lepoll_trans] 1);
by (resolve_tac [InfCard_square_eq RS eqpoll_imp_lepoll] 2);
by (asm_simp_tac (ZF_ss addsimps [InfCard_is_Card, Card_cardinal_eq]) 2);
by (rewrite_goals_tac [lepoll_def]);
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (etac (AC_ball_Pi RS exE) 1);
by (resolve_tac [exI] 1);
(*Lemma needed in both subgoals, for a fixed z*)
by (subgoal_tac
    "ALL z: (UN i:K. X(i)). z: X(LEAST i. z:X(i)) & (LEAST i. z:X(i)) : K" 1);
by (fast_tac (ZF_cs addSIs [Least_le RS lt_trans1 RS ltD, ltI]
                    addSEs [LeastI, Ord_in_Ord]) 2);
by (res_inst_tac [("c", "%z. <LEAST i. z:X(i), f ` (LEAST i. z:X(i)) ` z>"),
		  ("d", "split(%i j. converse(f`i) ` j)")] 
	lam_injective 1);
(*Instantiate the lemma proved above*)
by (ALLGOALS ball_tac);
by (fast_tac (ZF_cs addEs [inj_is_fun RS apply_type]
                    addDs [apply_type]) 1);
by (dresolve_tac [apply_type] 1);
by (eresolve_tac [conjunct2] 1);
by (asm_simp_tac (ZF_ss addsimps [left_inverse]) 1);
val cardinal_UN_le = result();

(*The same again, using csucc*)
goal Cardinal_AC.thy
    "!!K. [| InfCard(K);  ALL i:K. |X(i)| < csucc(K) |] ==> \
\         |UN i:K. X(i)| < csucc(K)";
by (asm_full_simp_tac 
    (ZF_ss addsimps [Card_lt_csucc_iff, cardinal_UN_le, 
		     InfCard_is_Card, Card_cardinal]) 1);
val cardinal_UN_lt_csucc = result();

(*The same again, for a union of ordinals*)
goal Cardinal_AC.thy
    "!!K. [| InfCard(K);  ALL i:K. j(i) < csucc(K) |] ==> \
\         (UN i:K. j(i)) < csucc(K)";
by (resolve_tac [cardinal_UN_lt_csucc RS Card_lt_imp_lt] 1);
by (assume_tac 1);
by (fast_tac (ZF_cs addIs [Ord_cardinal_le RS lt_trans1] addEs [ltE]) 1);
by (fast_tac (ZF_cs addSIs [Ord_UN] addEs [ltE]) 1);
by (eresolve_tac [InfCard_is_Card RS Card_is_Ord RS Card_csucc] 1);
val cardinal_UN_Ord_lt_csucc = result();


(*Saves checking Ord(j) below*)
goal Ordinal.thy "!!i j. [| i <= j;  j<k;  Ord(i) |] ==> i<k";
by (resolve_tac [subset_imp_le RS lt_trans1] 1);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
val lt_subset_trans = result();

goal Cardinal_AC.thy
    "!!K. [| InfCard(K);  |W| le K;  ALL w:W. j(w) < csucc(K) |] ==> \
\         (UN w:W. j(w)) < csucc(K)";
by (excluded_middle_tac "W=0" 1);
by (asm_simp_tac
    (ZF_ss addsimps [UN_0, InfCard_is_Card, Card_is_Ord RS Card_csucc, 
		     Card_is_Ord, Ord_0_lt_csucc]) 2);
by (asm_full_simp_tac
    (ZF_ss addsimps [InfCard_is_Card, le_Card_iff, lepoll_def]) 1);
by (safe_tac eq_cs);
by (eresolve_tac [notE] 1);
by (res_inst_tac [("j1", "%i. j(if(i: range(f), converse(f)`i, x))")]
    (cardinal_UN_Ord_lt_csucc RSN (2,lt_subset_trans)) 1);
by (assume_tac 2);
by (resolve_tac [UN_least] 1);
by (res_inst_tac [("x1", "f`xa")] (UN_upper RSN (2,subset_trans)) 1);
by (eresolve_tac [inj_is_fun RS apply_type] 2 THEN assume_tac 2);
by (asm_simp_tac 
    (ZF_ss addsimps [inj_is_fun RS apply_rangeI, left_inverse]) 1);
by (fast_tac (ZF_cs addSIs [Ord_UN] addEs [ltE]) 2);
by (asm_simp_tac (ZF_ss addsimps [inj_converse_fun RS apply_type]
		        setloop split_tac [expand_if]) 1);
val le_UN_Ord_lt_csucc = result();

