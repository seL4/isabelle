(*  Title: 	ZF/AC/AC17_AC1.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

The proof of AC1 ==> AC17
*)

open AC17_AC1;

(* *********************************************************************** *)
(* more properties of HH						   *)
(* *********************************************************************** *)

goal thy "!!f. [| x - (UN j:LEAST i. HH(lam X:Pow(x)-{0}. {f`X}, x, i) = {x}. \
\	HH(lam X:Pow(x)-{0}. {f`X}, x, j)) = 0;  \
\	f : Pow(x)-{0} -> x |]  \
\	==> EX r. well_ord(x,r)";
by (resolve_tac [exI] 1);
by (eresolve_tac [[bij_Least_HH_x RS bij_converse_bij RS bij_is_inj,
		Ord_Least RS well_ord_Memrel] MRS well_ord_rvimage] 1);
by (assume_tac 1);
val UN_eq_imp_well_ord = result();

(* *********************************************************************** *)
(* theorems closer to the proof						   *)
(* *********************************************************************** *)

goalw thy AC_defs "!!Z. ~AC1 ==>  \
\		EX A. ALL f:Pow(A)-{0} -> A. EX u:Pow(A)-{0}. f`u ~: u";
by (eresolve_tac [swap] 1);
by (resolve_tac [allI] 1);
by (eresolve_tac [swap] 1);
by (res_inst_tac [("x","Union(A)")] exI 1);
by (resolve_tac [ballI] 1);
by (eresolve_tac [swap] 1);
by (resolve_tac [impI] 1);
by (fast_tac (AC_cs addSIs [restrict_type]) 1);
val not_AC1_imp_ex = result();

goal thy "!!x. [| ALL f:Pow(x) - {0} -> x. EX u: Pow(x) - {0}. f`u~:u;  \
\	EX f: Pow(x)-{0}->x. \
\	x - (UN a:(LEAST i. HH(lam X:Pow(x)-{0}. {f`X},x,i)={x}).  \
\	HH(lam X:Pow(x)-{0}. {f`X},x,a)) = 0 |] \
\	==> P";
by (eresolve_tac [bexE] 1);
by (eresolve_tac [UN_eq_imp_well_ord RS exE] 1 THEN (assume_tac 1));
by (eresolve_tac [ex_choice_fun_Pow RS exE] 1);
by (eresolve_tac [ballE] 1);
by (fast_tac (FOL_cs addEs [bexE, notE, apply_type]) 1);
by (eresolve_tac [notE] 1);
by (resolve_tac [Pi_type] 1 THEN (assume_tac 1));
by (resolve_tac [apply_type RSN (2, subsetD)] 1 THEN TRYALL assume_tac);
by (fast_tac AC_cs 1);
val lemma1 = result();

goal thy "!!x. ~ (EX f: Pow(x)-{0}->x. x - F(f) = 0)  \
\	==> (lam f: Pow(x)-{0}->x. x - F(f))  \
\		: (Pow(x) -{0} -> x) -> Pow(x) - {0}";
by (fast_tac (AC_cs addSIs [lam_type] addIs [equalityI]
		addSDs [Diff_eq_0_iff RS iffD1]) 1);
val lemma2 = result();

goal thy "!!f. [| f`Z : Z; Z:Pow(x)-{0} |] ==>  \
\	(lam X:Pow(x)-{0}. {f`X})`Z : Pow(Z)-{0}";
by (asm_full_simp_tac AC_ss 1);
by (fast_tac (AC_cs addSDs [equals0D]) 1);
val lemma3 = result();

goal thy "!!z. EX f:F. f`((lam f:F. Q(f))`f) : (lam f:F. Q(f))`f  \
\	==> EX f:F. f`Q(f) : Q(f)";
by (asm_full_simp_tac AC_ss 1);
val lemma4 = result();

goalw thy [AC17_def] "!!Z. AC17 ==> AC1";
by (resolve_tac [classical] 1);
by (eresolve_tac [not_AC1_imp_ex RS exE] 1);
by (excluded_middle_tac
	"EX f: Pow(x)-{0}->x. \
\	x - (UN a:(LEAST i. HH(lam X:Pow(x)-{0}. {f`X},x,i)={x}).  \
\	HH(lam X:Pow(x)-{0}. {f`X},x,a)) = 0" 1);
by (eresolve_tac [lemma1] 2 THEN (assume_tac 2));
by (dresolve_tac [lemma2] 1);
by (eresolve_tac [allE] 1);
by (dresolve_tac [bspec] 1 THEN (assume_tac 1));
by (dresolve_tac [lemma4] 1);
by (eresolve_tac [bexE] 1);
by (dresolve_tac [apply_type] 1 THEN (assume_tac 1));
by (dresolve_tac [beta RS sym RSN (2, subst_elem)] 1);
by (assume_tac 1);
by (dresolve_tac [lemma3] 1 THEN (assume_tac 1));
by (fast_tac (AC_cs addSDs [HH_Least_eq_x RS sym RSN (2, subst_elem),
		f_subset_imp_HH_subset] addSEs [mem_irrefl]) 1);
qed "AC17_AC1";
