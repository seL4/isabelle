(*  Title:      ZF/AC/AC18_AC19.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> AC18 ==> AC19 ==> AC1
*)

open AC18_AC19;

(* ********************************************************************** *)
(* AC1 ==> AC18                                                           *)
(* ********************************************************************** *)

goal thy "!!f. [| f: (PROD b:{P(a). a:A}. b); ALL a:A. P(a)<=Q(a) |]  \
\               ==> (lam a:A. f`P(a)):(PROD a:A. Q(a))";
by (rtac lam_type 1);
by (dtac apply_type 1);
by (rtac RepFunI 1 THEN (assume_tac 1));
by (dtac bspec 1 THEN (assume_tac 1));
by (etac subsetD 1 THEN (assume_tac 1));
val PROD_subsets = result();

goal thy "!!X. [| ALL A. 0 ~: A --> (EX f. f : (PROD X:A. X)); A ~= 0 |] ==>  \
\  (INT a:A. UN b:B(a). X(a, b)) <= (UN f:PROD a:A. B(a). INT a:A. X(a, f`a))";
by (rtac subsetI 1);
by (eres_inst_tac [("x","{{b:B(a). x:X(a,b)}. a:A}")] allE 1);
by (etac impE 1);
by (fast_tac (AC_cs addSEs [RepFunE] addSDs [INT_E]
                addEs [UN_E, sym RS equals0D]) 1);
by (etac exE 1);
by (rtac UN_I 1);
by (fast_tac (AC_cs addSEs [PROD_subsets]) 1);
by (simp_tac AC_ss 1);
by (fast_tac (FOL_cs addSEs [not_emptyE] addDs [RepFunI RSN (2, apply_type)]
                addEs [CollectD2] addSIs [INT_I]) 1);
val lemma_AC18 = result();

val [prem] = goalw thy (AC18_def::AC_defs) "AC1 ==> AC18";
by (resolve_tac [prem RS revcut_rl] 1);
by (fast_tac (AC_cs addSEs [lemma_AC18, UN_E, not_emptyE, apply_type]
                addSIs [equalityI, INT_I, UN_I]) 1);
qed "AC1_AC18";

(* ********************************************************************** *)
(* AC18 ==> AC19                                                          *)
(* ********************************************************************** *)

val [prem] = goalw thy [AC18_def, AC19_def] "AC18 ==> AC19";
by (rtac allI 1);
by (res_inst_tac [("B1","%x.x")] (forall_elim_vars 0 prem RS revcut_rl) 1);
by (fast_tac AC_cs 1);
qed "AC18_AC19";

(* ********************************************************************** *)
(* AC19 ==> AC1                                                           *)
(* ********************************************************************** *)

goalw thy [u_def]
        "!!A. [| A ~= 0; 0 ~: A |] ==> {u_(a). a:A} ~= 0 & 0 ~: {u_(a). a:A}";
by (fast_tac (AC_cs addSIs [not_emptyI, RepFunI]
                addSEs [not_emptyE, RepFunE]
                addSDs [sym RS (RepFun_eq_0_iff RS iffD1)]) 1);
val RepRep_conj = result();

goal thy "!!c. [|c : a; x = c Un {0}; x ~: a |] ==> x - {0} : a";
by (hyp_subst_tac 1);
by (rtac subst_elem 1 THEN (assume_tac 1));
by (rtac equalityI 1);
by (fast_tac AC_cs 1);
by (rtac subsetI 1);
by (excluded_middle_tac "x=0" 1);
by (fast_tac AC_cs 1);
by (fast_tac (AC_cs addEs [notE, subst_elem] addSIs [equalityI])  1);
val lemma1_1 = result();

goalw thy [u_def]
        "!!a. [| f`(u_(a)) ~: a; f: (PROD B:{u_(a). a:A}. B); a:A |]  \
\               ==> f`(u_(a))-{0} : a";
by (fast_tac (AC_cs addSEs [RepFunI, RepFunE, lemma1_1]
                addSDs [apply_type]) 1);
val lemma1_2 = result();

goal thy  "!!A. EX f. f: (PROD B:{u_(a). a:A}. B) ==> EX f. f: (PROD B:A. B)";
by (etac exE 1);
by (res_inst_tac
        [("x","lam a:A. if(f`(u_(a)) : a, f`(u_(a)), f`(u_(a))-{0})")] exI 1);
by (rtac lam_type 1);
by (split_tac [expand_if] 1);
by (rtac conjI 1);
by (fast_tac AC_cs 1);
by (fast_tac (AC_cs addSEs [lemma1_2]) 1);
val lemma1 = result();

goalw thy [u_def] "!!a. a~=0 ==> 0: (UN b:u_(a). b)";
by (fast_tac (AC_cs addSEs [not_emptyE] addSIs [UN_I, RepFunI]) 1);
val lemma2_1 = result();

goal thy "!!A C. [| A~=0; 0~:A |] ==> (INT x:{u_(a). a:A}. UN b:x. b) ~= 0";
by (etac not_emptyE 1);
by (res_inst_tac [("a","0")] not_emptyI 1);
by (fast_tac (AC_cs addSIs [INT_I, RepFunI, lemma2_1] addSEs [RepFunE]) 1);
val lemma2 = result();

goal thy "!!F. (UN f:F. P(f)) ~= 0 ==> F ~= 0";
by (fast_tac (AC_cs addSEs [not_emptyE]) 1);
val lemma3 = result();

goalw thy AC_defs "!!Z. AC19 ==> AC1";
by (REPEAT (resolve_tac [allI,impI] 1));
by (excluded_middle_tac "A=0" 1);
by (fast_tac (AC_cs addSIs [empty_fun]) 2);
by (eres_inst_tac [("x","{u_(a). a:A}")] allE 1);
by (etac impE 1);
by (etac RepRep_conj 1 THEN (assume_tac 1));
by (rtac lemma1 1);
by (dtac lemma2 1 THEN (assume_tac 1));
by (dres_inst_tac [("P","%x. x~=0")] subst 1 THEN (assume_tac 1));
by (fast_tac (AC_cs addSEs [lemma3 RS not_emptyE]) 1);
qed "AC19_AC1";


