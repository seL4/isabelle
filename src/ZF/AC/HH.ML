(*  Title:      ZF/AC/HH.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Some properties of the recursive definition of HH used in the proofs of
  AC17 ==> AC1
  AC1 ==> WO2
  AC15 ==> WO6
*)

(* ********************************************************************** *)
(* Lemmas useful in each of the three proofs                              *)
(* ********************************************************************** *)

Goal "HH(f,x,a) =  \
\       (let z = x - (\\<Union>b \\<in> a. HH(f,x,b))  \
\       in  if(f`z \\<in> Pow(z)-{0}, f`z, {x}))";
by (resolve_tac [HH_def RS def_transrec RS trans] 1);
by (Simp_tac 1);
qed "HH_def_satisfies_eq";

Goal "HH(f,x,a) \\<in> Pow(x)-{0} | HH(f,x,a)={x}";
by (resolve_tac [HH_def_satisfies_eq RS ssubst] 1);
by (simp_tac (simpset() addsimps [Let_def, Diff_subset RS PowI]) 1);
by (Fast_tac 1);
qed "HH_values";

Goal "B \\<subseteq> A ==> X-(\\<Union>a \\<in> A. P(a)) = X-(\\<Union>a \\<in> A-B. P(a))-(\\<Union>b \\<in> B. P(b))";
by (Fast_tac 1);
qed "subset_imp_Diff_eq";

Goal "[| c \\<in> a-b; b<a |] ==> c=b | b<c & c<a";
by (etac ltE 1);
by (dtac Ord_linear 1);
by (fast_tac (claset() addSIs [ltI] addIs [Ord_in_Ord]) 2);
by (fast_tac (claset() addEs [Ord_in_Ord]) 1);
qed "Ord_DiffE";

val prems = goal thy "(!!y. y \\<in> A ==> P(y) = {x}) ==> x - (\\<Union>y \\<in> A. P(y)) = x";
by (asm_full_simp_tac (simpset() addsimps prems) 1);
by (fast_tac (claset() addSDs [prem] addSEs [mem_irrefl]) 1);
qed "Diff_UN_eq_self";

Goal "x - (\\<Union>b \\<in> a. HH(f,x,b)) = x - (\\<Union>b \\<in> a1. HH(f,x,b))  \
\               ==> HH(f,x,a) = HH(f,x,a1)";
by (resolve_tac [HH_def_satisfies_eq RS
                (HH_def_satisfies_eq RS sym RSN (3, trans RS trans))] 1);
by (etac subst_context 1);
qed "HH_eq";

Goal "[| HH(f,x,b)={x}; b<a |] ==> HH(f,x,a)={x}";
by (res_inst_tac [("P","b<a")] impE 1 THEN REPEAT (assume_tac 2));
by (eresolve_tac [lt_Ord2 RS trans_induct] 1);
by (rtac impI 1);
by (resolve_tac [HH_eq RS trans] 1 THEN (assume_tac 2));
by (resolve_tac [leI RS le_imp_subset RS subset_imp_Diff_eq RS ssubst] 1
        THEN (assume_tac 1));
by (res_inst_tac [("t","%z. z-?X")] subst_context 1);
by (rtac Diff_UN_eq_self 1);
by (dtac Ord_DiffE 1 THEN (assume_tac 1));
by (fast_tac (claset() addEs [ltE]) 1);
qed "HH_is_x_gt_too";

Goal "[| HH(f,x,a) \\<in> Pow(x)-{0}; b<a |] ==> HH(f,x,b) \\<in> Pow(x)-{0}";
by (resolve_tac [HH_values RS disjE] 1 THEN (assume_tac 1));
by (dtac HH_is_x_gt_too 1 THEN (assume_tac 1));
by (dtac subst 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [mem_irrefl]) 1);
qed "HH_subset_x_lt_too";

Goal "HH(f,x,a) \\<in> Pow(x)-{0}   \
\               ==> HH(f,x,a) \\<in> Pow(x - (\\<Union>b \\<in> a. HH(f,x,b)))-{0}";
by (dresolve_tac [HH_def_satisfies_eq RS subst] 1);
by (resolve_tac [HH_def_satisfies_eq RS ssubst] 1);
by (asm_full_simp_tac (simpset() addsimps [Let_def, Diff_subset RS PowI]) 1);
by (dresolve_tac [split_if RS iffD1] 1);
by (Simp_tac 1);
by (fast_tac (subset_cs addSEs [mem_irrefl]) 1);
qed "HH_subset_x_imp_subset_Diff_UN";

Goal "[| HH(f,x,v)=HH(f,x,w); HH(f,x,v): Pow(x)-{0}; v \\<in> w |] ==> P";
by (forw_inst_tac [("P","%y. y \\<in> Pow(x)-{0}")] subst 1 THEN (assume_tac 1));
by (dres_inst_tac [("a","w")] HH_subset_x_imp_subset_Diff_UN 1);
by (dtac subst_elem 1 THEN (assume_tac 1));
by (fast_tac (claset() addSIs [singleton_iff RS iffD2, equals0I]) 1);
qed "HH_eq_arg_lt";

Goal "[| HH(f,x,v)=HH(f,x,w); HH(f,x,w): Pow(x)-{0};  \
\               Ord(v); Ord(w) |] ==> v=w";
by (res_inst_tac [("j","w")] Ord_linear_lt 1 THEN TRYALL assume_tac);
by (resolve_tac [sym RS (ltD RSN (3, HH_eq_arg_lt))] 2
        THEN REPEAT (assume_tac 2));
by (dtac subst_elem 1 THEN (assume_tac 1));
by (fast_tac (FOL_cs addDs [ltD] addSEs [HH_eq_arg_lt]) 1);
qed "HH_eq_imp_arg_eq";

Goalw [lepoll_def, inj_def]
        "[| HH(f, x, i) \\<in> Pow(x)-{0}; Ord(i) |] ==> i lepoll Pow(x)-{0}";
by (res_inst_tac [("x","\\<lambda>j \\<in> i. HH(f, x, j)")] exI 1);
by (Asm_simp_tac 1);
by (fast_tac (FOL_cs addSEs [HH_eq_imp_arg_eq, Ord_in_Ord, HH_subset_x_lt_too]
                addSIs [lam_type, ballI, ltI] addIs [bexI]) 1);
qed "HH_subset_x_imp_lepoll";

Goal "HH(f, x, Hartog(Pow(x)-{0})) = {x}";
by (resolve_tac [HH_values RS disjE] 1 THEN (assume_tac 2));
by (fast_tac (FOL_cs addSDs [HH_subset_x_imp_lepoll]
                addSIs [Ord_Hartog] addSEs [HartogE]) 1);
qed "HH_Hartog_is_x";

Goal "HH(f, x, LEAST i. HH(f, x, i) = {x}) = {x}";
by (fast_tac (claset() addSIs [Ord_Hartog, HH_Hartog_is_x, LeastI]) 1);
qed "HH_Least_eq_x";

Goal "a \\<in> (LEAST i. HH(f,x,i)={x}) ==> HH(f,x,a) \\<in> Pow(x)-{0}";
by (resolve_tac [HH_values RS disjE] 1 THEN (assume_tac 1));
by (rtac less_LeastE 1);
by (eresolve_tac [Ord_Least RSN (2, ltI)] 2);
by (assume_tac 1);
qed "less_Least_subset_x";

(* ********************************************************************** *)
(* Lemmas used in the proofs of AC1 ==> WO2 and AC17 ==> AC1              *)
(* ********************************************************************** *)

Goalw [inj_def]
        "(\\<lambda>a \\<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,a))  \
\        \\<in> inj(LEAST i. HH(f,x,i)={x}, Pow(x)-{0})";
by (Asm_full_simp_tac 1);
by (fast_tac (claset()  addSIs [lam_type] addDs [less_Least_subset_x]
                addSEs [HH_eq_imp_arg_eq, Ord_Least RS Ord_in_Ord]) 1);
qed "lam_Least_HH_inj_Pow";

Goal "\\<forall>a \\<in> (LEAST i. HH(f,x,i)={x}). \\<exists>z \\<in> x. HH(f,x,a) = {z}  \
\               ==> (\\<lambda>a \\<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,a))  \
\                       \\<in> inj(LEAST i. HH(f,x,i)={x}, {{y}. y \\<in> x})";
by (resolve_tac [lam_Least_HH_inj_Pow RS inj_strengthen_type] 1);
by (Asm_full_simp_tac 1);
qed "lam_Least_HH_inj";

Goalw [surj_def]
        "[| x - (\\<Union>a \\<in> A. F(a)) = 0;  \
\               \\<forall>a \\<in> A. \\<exists>z \\<in> x. F(a) = {z} |]  \
\               ==> (\\<lambda>a \\<in> A. F(a)) \\<in> surj(A, {{y}. y \\<in> x})";
by (asm_full_simp_tac (simpset() addsimps [lam_type, Diff_eq_0_iff]) 1);
by Safe_tac;
by (set_mp_tac 1);
by (deepen_tac (claset() addSIs [bexI] addSEs [equalityE]) 4 1);
qed "lam_surj_sing";

Goal "y \\<in> Pow(x)-{0} ==> x \\<noteq> 0";
by Auto_tac;
qed "not_emptyI2";

Goal "f`(x - (\\<Union>j \\<in> i. HH(f,x,j))): Pow(x - (\\<Union>j \\<in> i. HH(f,x,j)))-{0}  \
\       ==> HH(f, x, i) \\<in> Pow(x) - {0}";
by (resolve_tac [HH_def_satisfies_eq RS ssubst] 1);
by (asm_full_simp_tac (simpset() addsimps [Let_def, Diff_subset RS PowI,
                not_emptyI2 RS if_P]) 1);
by (Fast_tac 1);
qed "f_subset_imp_HH_subset";

val [prem] = goal thy "(!!z. z \\<in> Pow(x)-{0} ==> f`z \\<in> Pow(z)-{0}) ==>  \
\       x - (\\<Union>j \\<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,j)) = 0";
by (excluded_middle_tac "?P \\<in> {0}" 1);
by (Fast_tac 2);
by (dresolve_tac [Diff_subset RS PowI RS DiffI RS prem RS
                f_subset_imp_HH_subset] 1);
by (fast_tac (claset() addSDs [HH_Least_eq_x RS sym RSN (2, subst_elem)]
                addSEs [mem_irrefl]) 1);
qed "f_subsets_imp_UN_HH_eq_x";

Goal "HH(f,x,i)=f`(x - (\\<Union>j \\<in> i. HH(f,x,j))) | HH(f,x,i)={x}";
by (resolve_tac [HH_def_satisfies_eq RS ssubst] 1);
by (simp_tac (simpset() addsimps [Let_def, Diff_subset RS PowI]) 1);
qed "HH_values2";

Goal "HH(f,x,i): Pow(x)-{0} ==> HH(f,x,i)=f`(x - (\\<Union>j \\<in> i. HH(f,x,j)))";
by (resolve_tac [HH_values2 RS disjE] 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [equalityE, mem_irrefl]
        addSDs [singleton_subsetD]) 1);
qed "HH_subset_imp_eq";

Goal "[| f \\<in> (Pow(x)-{0}) -> {{z}. z \\<in> x};  \
\       a \\<in> (LEAST i. HH(f,x,i)={x}) |] ==> \\<exists>z \\<in> x. HH(f,x,a) = {z}";
by (dtac less_Least_subset_x 1);
by (ftac HH_subset_imp_eq 1);
by (dtac apply_type 1);
by (resolve_tac [Diff_subset RS PowI RS DiffI] 1);
by (fast_tac 
    (claset() addSDs [HH_subset_x_imp_subset_Diff_UN RS not_emptyI2]) 1);
by (fast_tac (claset() addss (simpset())) 1);
qed "f_sing_imp_HH_sing";

Goalw [bij_def] 
        "[| x - (\\<Union>j \\<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,j)) = 0;  \
\       f \\<in> (Pow(x)-{0}) -> {{z}. z \\<in> x} |]  \
\       ==> (\\<lambda>a \\<in> (LEAST i. HH(f,x,i)={x}). HH(f,x,a))  \
\                       \\<in> bij(LEAST i. HH(f,x,i)={x}, {{y}. y \\<in> x})";
by (fast_tac (claset() addSIs [lam_Least_HH_inj, lam_surj_sing,
                              f_sing_imp_HH_sing]) 1);
qed "f_sing_lam_bij";

Goal "f \\<in> (\\<Pi>X \\<in> Pow(x)-{0}. F(X))  \
\       ==> (\\<lambda>X \\<in> Pow(x)-{0}. {f`X}) \\<in> (\\<Pi>X \\<in> Pow(x)-{0}. {{z}. z \\<in> F(X)})";
by (fast_tac (FOL_cs addSIs [lam_type, RepFun_eqI, singleton_eq_iff RS iffD2]
                     addDs [apply_type]) 1);
qed "lam_singI";

val bij_Least_HH_x = 
    (lam_singI RSN (2, [f_sing_lam_bij, lam_sing_bij RS bij_converse_bij]
                    MRS comp_bij)) |> standard;
