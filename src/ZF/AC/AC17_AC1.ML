(*  Title:      ZF/AC/AC1_AC17.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The equivalence of AC0, AC1 and AC17

Also, the proofs needed to show that each of AC2, AC3, ..., AC6 is equivalent
to AC0 and AC1.
*)


(** AC0 is equivalent to AC1.  
    AC0 comes from Suppes, AC1 from Rubin & Rubin **)

Goal "[| f:(\\<Pi>X \\<in> A. X); D \\<subseteq> A |] ==> \\<exists>g. g:(\\<Pi>X \\<in> D. X)";
by (fast_tac (claset() addSIs [restrict_type, apply_type]) 1);
val lemma1 = result();

Goalw AC_defs "AC0 ==> AC1"; 
by (blast_tac (claset() addIs [lemma1]) 1); 
qed "AC0_AC1";

Goalw AC_defs "AC1 ==> AC0";
by (Blast_tac 1); 
qed "AC1_AC0";


(**** The proof of AC1 ==> AC17 ****)

Goal "f \\<in> (\\<Pi>X \\<in> Pow(A) - {0}. X) ==> f \\<in> (Pow(A) - {0} -> A)";
by (rtac Pi_type 1 THEN (assume_tac 1));
by (dtac apply_type 1 THEN (assume_tac 1));
by (Fast_tac 1);
val lemma1 = result();

Goalw AC_defs "AC1 ==> AC17";
by (rtac allI 1);
by (rtac ballI 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (etac impE 1);
by (Fast_tac 1);
by (etac exE 1);
by (rtac bexI 1);
by (etac lemma1 2);
by (rtac apply_type 1 THEN (assume_tac 1));
by (fast_tac (claset() addSDs [lemma1] addSEs [apply_type]) 1);
qed "AC1_AC17";


(**** The proof of AC17 ==> AC1 ****)

(* *********************************************************************** *)
(* more properties of HH                                                   *)
(* *********************************************************************** *)

Goal "[| x - (\\<Union>j \\<in> LEAST i. HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X}, x, i) = {x}. \
\       HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X}, x, j)) = 0;  \
\       f \\<in> Pow(x)-{0} -> x |]  \
\       ==> \\<exists>r. well_ord(x,r)";
by (rtac exI 1);
by (eresolve_tac [[bij_Least_HH_x RS bij_converse_bij RS bij_is_inj,
                Ord_Least RS well_ord_Memrel] MRS well_ord_rvimage] 1);
by (assume_tac 1);
qed "UN_eq_imp_well_ord";

(* *********************************************************************** *)
(* theorems closer to the proof                                            *)
(* *********************************************************************** *)

Goalw AC_defs "~AC1 ==>  \
\               \\<exists>A. \\<forall>f \\<in> Pow(A)-{0} -> A. \\<exists>u \\<in> Pow(A)-{0}. f`u \\<notin> u";
by (etac swap 1);
by (rtac allI 1);
by (etac swap 1);
by (res_inst_tac [("x","Union(A)")] exI 1);
by (rtac ballI 1);
by (etac swap 1);
by (rtac impI 1);
by (fast_tac (claset() addSIs [restrict_type]) 1);
qed "not_AC1_imp_ex";

Goal "[| \\<forall>f \\<in> Pow(x) - {0} -> x. \\<exists>u \\<in> Pow(x) - {0}. f`u\\<notin>u;  \
\       \\<exists>f \\<in> Pow(x)-{0}->x. \
\       x - (\\<Union>a \\<in> (LEAST i. HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X},x,i)={x}).  \
\       HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X},x,a)) = 0 |] \
\       ==> P";
by (etac bexE 1);
by (eresolve_tac [UN_eq_imp_well_ord RS exE] 1 THEN (assume_tac 1));
by (eresolve_tac [ex_choice_fun_Pow RS exE] 1);
by (etac ballE 1);
by (fast_tac (FOL_cs addEs [bexE, notE, apply_type]) 1);
by (etac notE 1);
by (rtac Pi_type 1 THEN (assume_tac 1));
by (resolve_tac [apply_type RSN (2, subsetD)] 1 THEN TRYALL assume_tac);
by (Fast_tac 1);
val lemma1 = result();

Goal "~ (\\<exists>f \\<in> Pow(x)-{0}->x. x - F(f) = 0)  \
\       ==> (\\<lambda>f \\<in> Pow(x)-{0}->x. x - F(f))  \
\               \\<in> (Pow(x) -{0} -> x) -> Pow(x) - {0}";
by (fast_tac (claset() addSIs [lam_type] addSDs [Diff_eq_0_iff RS iffD1]) 1);
val lemma2 = result();

Goal "[| f`Z \\<in> Z; Z \\<in> Pow(x)-{0} |] ==>  \
\       (\\<lambda>X \\<in> Pow(x)-{0}. {f`X})`Z \\<in> Pow(Z)-{0}";
by Auto_tac;
val lemma3 = result();

Goal "\\<exists>f \\<in> F. f`((\\<lambda>f \\<in> F. Q(f))`f) \\<in> (\\<lambda>f \\<in> F. Q(f))`f  \
\       ==> \\<exists>f \\<in> F. f`Q(f) \\<in> Q(f)";
by (Asm_full_simp_tac 1);
val lemma4 = result();

Goalw [AC17_def] "AC17 ==> AC1";
by (rtac classical 1);
by (eresolve_tac [not_AC1_imp_ex RS exE] 1);
by (excluded_middle_tac
        "\\<exists>f \\<in> Pow(x)-{0}->x. \
\       x - (\\<Union>a \\<in> (LEAST i. HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X},x,i)={x}).  \
\       HH(\\<lambda>X \\<in> Pow(x)-{0}. {f`X},x,a)) = 0" 1);
by (etac lemma1 2 THEN (assume_tac 2));
by (dtac lemma2 1);
by (etac allE 1);
by (dtac bspec 1 THEN (assume_tac 1));
by (dtac lemma4 1);
by (etac bexE 1);
by (dtac apply_type 1 THEN (assume_tac 1));
by (dresolve_tac [beta RS sym RSN (2, subst_elem)] 1);
by (assume_tac 1);
by (dtac lemma3 1 THEN (assume_tac 1));
by (fast_tac (claset() addSDs [HH_Least_eq_x RS sym RSN (2, subst_elem),
                f_subset_imp_HH_subset] addSEs [mem_irrefl]) 1);
qed "AC17_AC1";


(* **********************************************************************
    AC1 ==> AC2 ==> AC1
    AC1 ==> AC4 ==> AC3 ==> AC1
    AC4 ==> AC5 ==> AC4
    AC1 <-> AC6
************************************************************************* *)

(* ********************************************************************** *)
(* AC1 ==> AC2                                                            *)
(* ********************************************************************** *)

Goal "[| f:(\\<Pi>X \\<in> A. X);  B \\<in> A;  0\\<notin>A |] ==> {f`B} \\<subseteq> B Int {f`C. C \\<in> A}";
by (fast_tac (claset() addSEs [apply_type]) 1);
val lemma1 = result();

Goalw [pairwise_disjoint_def]
        "[| pairwise_disjoint(A); B \\<in> A; C \\<in> A; D \\<in> B; D \\<in> C |] ==> f`B = f`C";
by (Fast_tac 1);
val lemma2 = result();

Goalw AC_defs "AC1 ==> AC2"; 
by (rtac allI 1);
by (rtac impI 1);
by (REPEAT (eresolve_tac [asm_rl,conjE,allE,exE,impE] 1));
by (REPEAT (resolve_tac [exI,ballI,equalityI] 1));
by (rtac lemma1 2 THEN (REPEAT (assume_tac 2)));
by (fast_tac (claset() addSEs [lemma2] addEs [apply_type]) 1);
qed "AC1_AC2";


(* ********************************************************************** *)
(* AC2 ==> AC1                                                            *)
(* ********************************************************************** *)

Goal "0\\<notin>A ==> 0 \\<notin> {B*{B}. B \\<in> A}";
by (fast_tac (claset() addSDs [sym RS (Sigma_empty_iff RS iffD1)]) 1);
val lemma1 = result();

Goal "[| X*{X} Int C = {y}; X \\<in> A |]  \
\               ==> (THE y. X*{X} Int C = {y}): X*A";
by (rtac subst_elem 1);
by (fast_tac (claset() addSIs [the_equality]
                addSEs [sym RS trans RS (singleton_eq_iff RS iffD1)]) 2);
by (blast_tac (claset() addSEs [equalityE]) 1);
val lemma2 = result();

Goal "\\<forall>D \\<in> {E*{E}. E \\<in> A}. \\<exists>y. D Int C = {y}  \
\     ==> (\\<lambda>x \\<in> A. fst(THE z. (x*{x} Int C = {z}))) \\<in> (\\<Pi>X \\<in> A. X)";
by (fast_tac (claset() addSEs [lemma2] 
                       addSIs [lam_type, RepFunI, fst_type]) 1);
val lemma3 = result();

Goalw (AC_defs@AC_aux_defs) "AC2 ==> AC1";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [allE, impE] 1));
by (fast_tac (claset() addSEs [lemma3]) 2);
by (fast_tac (claset() addSIs [lemma1, equals0I]) 1);
qed "AC2_AC1";


(* ********************************************************************** *)
(* AC1 ==> AC4                                                            *)
(* ********************************************************************** *)

Goal "0 \\<notin> {R``{x}. x \\<in> domain(R)}";
by (Blast_tac 1);
val lemma = result();

Goalw AC_defs "AC1 ==> AC4";
by (REPEAT (resolve_tac [allI, impI] 1));
by (REPEAT (eresolve_tac [allE, lemma RSN (2, impE), exE] 1));
by (best_tac (claset() addSIs [lam_type] addSEs [apply_type]) 1);
qed "AC1_AC4";


(* ********************************************************************** *)
(* AC4 ==> AC3                                                            *)
(* ********************************************************************** *)

Goal "f \\<in> A->B ==> (\\<Union>z \\<in> A. {z}*f`z) \\<subseteq> A*Union(B)";
by (fast_tac (claset() addSDs [apply_type]) 1);
val lemma1 = result();

Goal "domain(\\<Union>z \\<in> A. {z}*f(z)) = {a \\<in> A. f(a)\\<noteq>0}";
by (Blast_tac 1);
val lemma2 = result();

Goal "x \\<in> A ==> (\\<Union>z \\<in> A. {z}*f(z))``{x} = f(x)";
by (Fast_tac 1);
val lemma3 = result();

Goalw AC_defs "AC4 ==> AC3";
by (REPEAT (resolve_tac [allI,ballI] 1));
by (REPEAT (eresolve_tac [allE,impE] 1));
by (etac lemma1 1);
by (asm_full_simp_tac (simpset() addsimps [lemma2, lemma3]
                                 addcongs [Pi_cong]) 1);
qed "AC4_AC3";

(* ********************************************************************** *)
(* AC3 ==> AC1                                                            *)
(* ********************************************************************** *)

Goal "b\\<notin>A ==> (\\<Pi>x \\<in> {a \\<in> A. id(A)`a\\<noteq>b}. id(A)`x) = (\\<Pi>x \\<in> A. x)";
by (asm_full_simp_tac (simpset() addsimps [id_def] addcongs [Pi_cong]) 1);
by (res_inst_tac [("b","A")] subst_context 1);
by (Fast_tac 1);
val lemma = result();

Goalw AC_defs "AC3 ==> AC1";
by (fast_tac (claset() addSIs [id_type] addEs [lemma RS subst]) 1);
qed "AC3_AC1";

(* ********************************************************************** *)
(* AC4 ==> AC5                                                            *)
(* ********************************************************************** *)

Goalw (range_def::AC_defs) "AC4 ==> AC5";
by (REPEAT (resolve_tac [allI,ballI] 1));
by (REPEAT (eresolve_tac [allE,impE] 1));
by (eresolve_tac [fun_is_rel RS converse_type] 1);
by (etac exE 1);
by (rtac bexI 1);
by (rtac Pi_type 2 THEN (assume_tac 2));
by (fast_tac (claset() addSDs [apply_type]
        addSEs [fun_is_rel RS converse_type RS subsetD RS SigmaD2]) 2);
by (rtac ballI 1);
by (rtac apply_equality 1 THEN (assume_tac 2));
by (etac domainE 1);
by (ftac range_type 1 THEN (assume_tac 1));
by (fast_tac (claset() addDs [apply_equality]) 1);
qed "AC4_AC5";


(* ********************************************************************** *)
(* AC5 ==> AC4, Rubin & Rubin, p. 11                                      *)
(* ********************************************************************** *)

Goal "R \\<subseteq> A*B ==> (\\<lambda>x \\<in> R. fst(x)) \\<in> R -> A";
by (fast_tac (claset() addSIs [lam_type, fst_type]) 1);
val lemma1 = result();

Goalw [range_def] "R \\<subseteq> A*B ==> range(\\<lambda>x \\<in> R. fst(x)) = domain(R)";
by (force_tac (claset() addIs [lamI RS subst_elem] addSEs [lamE], 
	       simpset()) 1);
val lemma2 = result();

Goal "[| \\<exists>f \\<in> A->C. P(f,domain(f)); A=B |] ==>  \\<exists>f \\<in> B->C. P(f,B)";
by (etac bexE 1);
by (ftac domain_of_fun 1);
by (Fast_tac 1);
val lemma3 = result();

Goal "[| R \\<subseteq> A*B; g \\<in> C->R; \\<forall>x \\<in> C. (\\<lambda>z \\<in> R. fst(z))` (g`x) = x |] \
\               ==> (\\<lambda>x \\<in> C. snd(g`x)): (\\<Pi>x \\<in> C. R``{x})";
by (rtac lam_type 1);
by (force_tac (claset() addDs [apply_type], simpset()) 1);
val lemma4 = result();

Goalw AC_defs "AC5 ==> AC4";
by (Clarify_tac 1);
by (REPEAT (eresolve_tac [allE,ballE] 1));
by (eresolve_tac [lemma1 RSN (2, notE)] 2 THEN (assume_tac 2));
by (dresolve_tac [lemma2 RSN (2, lemma3)] 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [lemma4]) 1);
qed "AC5_AC4";


(* ********************************************************************** *)
(* AC1 <-> AC6                                                            *)
(* ********************************************************************** *)

Goalw AC_defs "AC1 <-> AC6";
by (Blast_tac 1);
qed "AC1_iff_AC6";
