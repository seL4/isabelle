(*  Title:      ZF/Cardinal_AC.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal arithmetic WITH the Axiom of Choice

These results help justify infinite-branching datatypes
*)

(*** Strengthened versions of existing theorems about cardinals ***)

Goal "|A| eqpoll A";
by (resolve_tac [AC_well_ord RS exE] 1);
by (etac well_ord_cardinal_eqpoll 1);
qed "cardinal_eqpoll";

val cardinal_idem = cardinal_eqpoll RS cardinal_cong;

Goal "|X| = |Y| ==> X eqpoll Y";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (rtac well_ord_cardinal_eqE 1);
by (REPEAT_SOME assume_tac);
qed "cardinal_eqE";

Goal "|X| = |Y| <-> X eqpoll Y";
by (blast_tac (claset() addIs [cardinal_cong, cardinal_eqE]) 1);
qed "cardinal_eqpoll_iff";

Goal "[| |A|=|B|;  |C|=|D|;  A Int C = 0;  B Int D = 0 |] ==> \
\         |A Un C| = |B Un D|";
by (asm_full_simp_tac (simpset() addsimps [cardinal_eqpoll_iff, 
                                       eqpoll_disjoint_Un]) 1);
qed "cardinal_disjoint_Un";

Goal "A lepoll B ==> |A| le |B|";
by (resolve_tac [AC_well_ord RS exE] 1);
by (etac well_ord_lepoll_imp_Card_le 1);
by (assume_tac 1);
qed "lepoll_imp_Card_le";

Goal "(i |+| j) |+| k = i |+| (j |+| k)";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (rtac well_ord_cadd_assoc 1);
by (REPEAT_SOME assume_tac);
qed "cadd_assoc";

Goal "(i |*| j) |*| k = i |*| (j |*| k)";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (rtac well_ord_cmult_assoc 1);
by (REPEAT_SOME assume_tac);
qed "cmult_assoc";

Goal "(i |+| j) |*| k = (i |*| k) |+| (j |*| k)";
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (resolve_tac [AC_well_ord RS exE] 1);
by (rtac well_ord_cadd_cmult_distrib 1);
by (REPEAT_SOME assume_tac);
qed "cadd_cmult_distrib";

Goal "InfCard(|A|) ==> A*A eqpoll A";
by (resolve_tac [AC_well_ord RS exE] 1);
by (etac well_ord_InfCard_square_eq 1);
by (assume_tac 1);
qed "InfCard_square_eq";


(*** Other applications of AC ***)

Goal "|A| le |B| ==> A lepoll B";
by (resolve_tac [cardinal_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll RS 
                 lepoll_trans] 1);
by (eresolve_tac [le_imp_subset RS subset_imp_lepoll RS lepoll_trans] 1);
by (resolve_tac [cardinal_eqpoll RS eqpoll_imp_lepoll] 1);
qed "Card_le_imp_lepoll";

Goal "Card(K) ==> |A| le K <-> A lepoll K";
by (eresolve_tac [Card_cardinal_eq RS subst] 1 THEN
    rtac iffI 1 THEN
    DEPTH_SOLVE (eresolve_tac [Card_le_imp_lepoll,lepoll_imp_Card_le] 1));
qed "le_Card_iff";

Goalw [surj_def] "f: surj(X,Y) ==> EX g. g: inj(Y,X)";
by (etac CollectE 1);
by (res_inst_tac [("A1", "Y"), ("B1", "%y. f-``{y}")] (AC_Pi RS exE) 1);
by (fast_tac (claset() addSEs [apply_Pair]) 1);
by (blast_tac (claset() addDs [apply_type, Pi_memberD] 
                       addIs [apply_equality, Pi_type, f_imp_injective]) 1);
qed "surj_implies_inj";

(*Kunen's Lemma 10.20*)
Goal "f: surj(X,Y) ==> |Y| le |X|";
by (rtac lepoll_imp_Card_le 1);
by (eresolve_tac [surj_implies_inj RS exE] 1);
by (rewtac lepoll_def);
by (etac exI 1);
qed "surj_implies_cardinal_le";

(*Kunen's Lemma 10.21*)
Goal "[| InfCard(K);  ALL i:K. |X(i)| le K |] ==> |UN i:K. X(i)| le K";
by (asm_full_simp_tac (simpset() addsimps [InfCard_is_Card, le_Card_iff]) 1);
by (rtac lepoll_trans 1);
by (resolve_tac [InfCard_square_eq RS eqpoll_imp_lepoll] 2);
by (asm_simp_tac (simpset() addsimps [InfCard_is_Card, Card_cardinal_eq]) 2);
by (rewtac lepoll_def);
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (etac (AC_ball_Pi RS exE) 1);
by (rtac exI 1);
(*Lemma needed in both subgoals, for a fixed z*)
by (subgoal_tac
    "ALL z: (UN i:K. X(i)). z: X(LEAST i. z:X(i)) & (LEAST i. z:X(i)) : K" 1);
by (fast_tac (claset() addSIs [Least_le RS lt_trans1 RS ltD, ltI]
                       addSEs [LeastI, Ord_in_Ord]) 2);
by (res_inst_tac [("c", "%z. <LEAST i. z:X(i), f ` (LEAST i. z:X(i)) ` z>"),
                  ("d", "%<i,j>. converse(f`i) ` j")] 
        lam_injective 1);
(*Instantiate the lemma proved above*)
by (ALLGOALS ball_tac);
by (blast_tac (claset() addIs [inj_is_fun RS apply_type]
                        addDs [apply_type]) 1);
by (dtac apply_type 1);
by (etac conjunct2 1);
by (asm_simp_tac (simpset() addsimps [left_inverse]) 1);
qed "cardinal_UN_le";



(*The same again, using csucc*)
Goal "[| InfCard(K);  ALL i:K. |X(i)| < csucc(K) |] ==> \
\         |UN i:K. X(i)| < csucc(K)";
by (asm_full_simp_tac 
    (simpset() addsimps [Card_lt_csucc_iff, cardinal_UN_le, 
                     InfCard_is_Card, Card_cardinal]) 1);
qed "cardinal_UN_lt_csucc";

(*The same again, for a union of ordinals.  In use, j(i) is a bit like rank(i),
  the least ordinal j such that i:Vfrom(A,j). *)
Goal "[| InfCard(K);  ALL i:K. j(i) < csucc(K) |] ==> \
\         (UN i:K. j(i)) < csucc(K)";
by (resolve_tac [cardinal_UN_lt_csucc RS Card_lt_imp_lt] 1);
by (assume_tac 1);
by (blast_tac (claset() addIs [Ord_cardinal_le RS lt_trans1] addEs [ltE]) 1);
by (blast_tac (claset() addSIs [Ord_UN] addEs [ltE]) 1);
by (eresolve_tac [InfCard_is_Card RS Card_is_Ord RS Card_csucc] 1);
qed "cardinal_UN_Ord_lt_csucc";


(** Main result for infinite-branching datatypes.  As above, but the index
    set need not be a cardinal.  Surprisingly complicated proof!
**)

(*Saves checking Ord(j) below*)
goal Ordinal.thy "!!i j. [| i <= j;  j<k;  Ord(i) |] ==> i<k";
by (resolve_tac [subset_imp_le RS lt_trans1] 1);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
qed "lt_subset_trans";

(*Work backwards along the injection from W into K, given that W~=0.*)
Goal "[| f: inj(A,B);  a:A |] ==>           \
\     (UN x:A. C(x)) <= (UN y:B. C(if y: range(f) then converse(f)`y else a))";
by (rtac UN_least 1);
by (res_inst_tac [("x1", "f`x")] (UN_upper RSN (2,subset_trans)) 1);
by (eresolve_tac [inj_is_fun RS apply_type] 2 THEN assume_tac 2);
by (asm_simp_tac 
    (simpset() addsimps [inj_is_fun RS apply_rangeI, left_inverse]) 1);
val inj_UN_subset = result();

(*Simpler to require |W|=K; we'd have a bijection; but the theorem would
  be weaker.*)
Goal "[| InfCard(K);  |W| le K;  ALL w:W. j(w) < csucc(K) |] ==> \
\         (UN w:W. j(w)) < csucc(K)";
by (excluded_middle_tac "W=0" 1);
by (asm_simp_tac        (*solve the easy 0 case*)
    (simpset() addsimps [UN_0, InfCard_is_Card, Card_is_Ord RS Card_csucc, 
                     Card_is_Ord, Ord_0_lt_csucc]) 2);
by (asm_full_simp_tac
    (simpset() addsimps [InfCard_is_Card, le_Card_iff, lepoll_def]) 1);
by (safe_tac (claset() addSIs [equalityI]));
by (swap_res_tac [[inj_UN_subset, cardinal_UN_Ord_lt_csucc] 
                  MRS lt_subset_trans] 1);
by (REPEAT (assume_tac 1));
by (blast_tac (claset() addSIs [Ord_UN] addEs [ltE]) 2);
by (asm_simp_tac (simpset() addsimps [inj_converse_fun RS apply_type]) 1);
qed "le_UN_Ord_lt_csucc";

