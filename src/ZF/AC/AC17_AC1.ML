(*  Title:      ZF/AC/AC17_AC1.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> AC17
*)

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
