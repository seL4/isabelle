(*  Title:      ZF/AC/AC18_AC19.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> AC18 ==> AC19 ==> AC1
*)

(* ********************************************************************** *)
(* AC1 ==> AC18                                                           *)
(* ********************************************************************** *)

Goal "[| f \\<in> (\\<Pi>b \\<in> {P(a). a \\<in> A}. b);  \\<forall>a \\<in> A. P(a)<=Q(a) |]  \
\     ==> (\\<lambda>a \\<in> A. f`P(a)) \\<in> (\\<Pi>a \\<in> A. Q(a))";
by (rtac lam_type 1);
by (dtac apply_type 1);
by Auto_tac;  
qed "PROD_subsets";

Goal "[| \\<forall>A. 0 \\<notin> A --> (\\<exists>f. f \\<in> (\\<Pi>X \\<in> A. X)); A \\<noteq> 0 |] ==>  \
\  (\\<Inter>a \\<in> A. \\<Union>b \\<in> B(a). X(a, b)) \\<subseteq> (\\<Union>f \\<in> \\<Pi>a \\<in> A. B(a). \\<Inter>a \\<in> A. X(a, f`a))";
by (rtac subsetI 1);
by (eres_inst_tac [("x","{{b \\<in> B(a). x \\<in> X(a,b)}. a \\<in> A}")] allE 1);
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
        "[| A \\<noteq> 0; 0 \\<notin> A |] ==> {u_(a). a \\<in> A} \\<noteq> 0 & 0 \\<notin> {u_(a). a \\<in> A}";
by (fast_tac (claset() addSIs [not_emptyI]
                addSEs [not_emptyE]
                addSDs [sym RS (RepFun_eq_0_iff RS iffD1)]) 1);
qed "RepRep_conj";

Goal "[|c \\<in> a; x = c Un {0}; x \\<notin> a |] ==> x - {0} \\<in> a";
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
        "[| f`(u_(a)) \\<notin> a; f \\<in> (\\<Pi>B \\<in> {u_(a). a \\<in> A}. B); a \\<in> A |]  \
\               ==> f`(u_(a))-{0} \\<in> a";
by (fast_tac (claset() addSEs [lemma1_1] addSDs [apply_type]) 1);
val lemma1_2 = result();

Goal  "\\<exists>f. f \\<in> (\\<Pi>B \\<in> {u_(a). a \\<in> A}. B) ==> \\<exists>f. f \\<in> (\\<Pi>B \\<in> A. B)";
by (etac exE 1);
by (res_inst_tac
        [("x","\\<lambda>a \\<in> A. if(f`(u_(a)) \\<in> a, f`(u_(a)), f`(u_(a))-{0})")] exI 1);
by (rtac lam_type 1);
by (split_tac [split_if] 1);
by (rtac conjI 1);
by (Fast_tac 1);
by (fast_tac (claset() addSEs [lemma1_2]) 1);
val lemma1 = result();

Goalw [u_def] "a\\<noteq>0 ==> 0 \\<in> (\\<Union>b \\<in> u_(a). b)";
by (fast_tac (claset() addSEs [not_emptyE] addSIs [UN_I, RepFunI]) 1);
val lemma2_1 = result();

Goal "[| A\\<noteq>0; 0\\<notin>A |] ==> (\\<Inter>x \\<in> {u_(a). a \\<in> A}. \\<Union>b \\<in> x. b) \\<noteq> 0";
by (etac not_emptyE 1);
by (res_inst_tac [("a","0")] not_emptyI 1);
by (fast_tac (claset() addSIs [lemma2_1]) 1);
val lemma2 = result();

Goal "(\\<Union>f \\<in> F. P(f)) \\<noteq> 0 ==> F \\<noteq> 0";
by (fast_tac (claset() addSEs [not_emptyE]) 1);
val lemma3 = result();

Goalw AC_defs "AC19 ==> AC1";
by (Clarify_tac 1);
by (case_tac "A=0" 1);
by (Force_tac 1);
by (eres_inst_tac [("x","{u_(a). a \\<in> A}")] allE 1);
by (etac impE 1);
by (etac RepRep_conj 1 THEN (assume_tac 1));
by (rtac lemma1 1);
by (dtac lemma2 1 THEN (assume_tac 1));
by (dres_inst_tac [("P","%x. x\\<noteq>0")] subst 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [lemma3 RS not_emptyE]) 1);
qed "AC19_AC1";


