(*  Title:      ZF/AC/AC18_AC19.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> AC18 ==> AC19 ==> AC1
*)

(* ********************************************************************** *)
(* AC1 ==> AC18                                                           *)
(* ********************************************************************** *)

Goal "[| f: (PROD b:{P(a). a:A}. b);  ALL a:A. P(a)<=Q(a) |]  \
\     ==> (lam a:A. f`P(a)) : (PROD a:A. Q(a))";
by (rtac lam_type 1);
by (dtac apply_type 1);
by Auto_tac;  
qed "PROD_subsets";

Goal "[| ALL A. 0 ~: A --> (EX f. f : (PROD X:A. X)); A ~= 0 |] ==>  \
\  (INT a:A. UN b:B(a). X(a, b)) <= (UN f:PROD a:A. B(a). INT a:A. X(a, f`a))";
by (rtac subsetI 1);
by (eres_inst_tac [("x","{{b:B(a). x:X(a,b)}. a:A}")] allE 1);
by (etac impE 1);
by (Fast_tac 1);
by (etac exE 1);
by (rtac UN_I 1);
by (fast_tac (claset() addSEs [PROD_subsets]) 1);
by (Simp_tac 1);
by (fast_tac (claset() addSEs [not_emptyE] 
                       addDs [RepFunI RSN (2, apply_type)]) 1);
qed "lemma_AC18";

val [prem] = goalw thy (AC18_def::AC_defs) "AC1 ==> AC18";
by (resolve_tac [prem RS revcut_rl] 1);
by (fast_tac (claset() addSEs [lemma_AC18, not_emptyE, apply_type]
                addSIs [equalityI, INT_I, UN_I]) 1);
qed "AC1_AC18";

(* ********************************************************************** *)
(* AC18 ==> AC19                                                          *)
(* ********************************************************************** *)

val [prem] = goalw thy [AC18_def, AC19_def] "AC18 ==> AC19";
by (rtac allI 1);
by (res_inst_tac [("B1","%x. x")] (forall_elim_vars 0 prem RS revcut_rl) 1);
by (Fast_tac 1);
qed "AC18_AC19";

(* ********************************************************************** *)
(* AC19 ==> AC1                                                           *)
(* ********************************************************************** *)

Goalw [u_def]
        "[| A ~= 0; 0 ~: A |] ==> {u_(a). a:A} ~= 0 & 0 ~: {u_(a). a:A}";
by (fast_tac (claset() addSIs [not_emptyI]
                addSEs [not_emptyE]
                addSDs [sym RS (RepFun_eq_0_iff RS iffD1)]) 1);
qed "RepRep_conj";

Goal "[|c : a; x = c Un {0}; x ~: a |] ==> x - {0} : a";
by (hyp_subst_tac 1);
by (rtac subst_elem 1 THEN (assume_tac 1));
by (rtac equalityI 1);
by (Fast_tac 1);
by (rtac subsetI 1);
by (excluded_middle_tac "x=0" 1);
by (Fast_tac 1);
by (fast_tac (claset() addEs [notE, subst_elem])  1);
val lemma1_1 = result();

Goalw [u_def]
        "[| f`(u_(a)) ~: a; f: (PROD B:{u_(a). a:A}. B); a:A |]  \
\               ==> f`(u_(a))-{0} : a";
by (fast_tac (claset() addSEs [lemma1_1] addSDs [apply_type]) 1);
val lemma1_2 = result();

Goal  "EX f. f: (PROD B:{u_(a). a:A}. B) ==> EX f. f: (PROD B:A. B)";
by (etac exE 1);
by (res_inst_tac
        [("x","lam a:A. if(f`(u_(a)) : a, f`(u_(a)), f`(u_(a))-{0})")] exI 1);
by (rtac lam_type 1);
by (split_tac [split_if] 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (fast_tac (claset() addSEs [lemma1_2]) 1);
val lemma1 = result();

Goalw [u_def] "a~=0 ==> 0: (UN b:u_(a). b)";
by (fast_tac (claset() addSEs [not_emptyE] addSIs [UN_I, RepFunI]) 1);
val lemma2_1 = result();

Goal "[| A~=0; 0~:A |] ==> (INT x:{u_(a). a:A}. UN b:x. b) ~= 0";
by (etac not_emptyE 1);
by (res_inst_tac [("a","0")] not_emptyI 1);
by (fast_tac (claset() addSIs [lemma2_1]) 1);
val lemma2 = result();

Goal "(UN f:F. P(f)) ~= 0 ==> F ~= 0";
by (fast_tac (claset() addSEs [not_emptyE]) 1);
val lemma3 = result();

Goalw AC_defs "AC19 ==> AC1";
by (Clarify_tac 1);
by (case_tac "A=0" 1);
by (Force_tac 1);
by (eres_inst_tac [("x","{u_(a). a:A}")] allE 1);
by (etac impE 1);
by (etac RepRep_conj 1 THEN (assume_tac 1));
by (rtac lemma1 1);
by (dtac lemma2 1 THEN (assume_tac 1));
by (dres_inst_tac [("P","%x. x~=0")] subst 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [lemma3 RS not_emptyE]) 1);
qed "AC19_AC1";


