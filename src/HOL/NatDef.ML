(*  Title:      HOL/NatDef.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

Goal "mono(%X. {Zero_Rep} Un (Suc_Rep``X))";
by (REPEAT (ares_tac [monoI, subset_refl, image_mono, Un_mono] 1));
qed "Nat_fun_mono";

bind_thm ("Nat_unfold", Nat_fun_mono RS (Nat_def RS def_lfp_unfold));

(* Zero is a natural number -- this also justifies the type definition*)
Goal "Zero_Rep: Nat";
by (stac Nat_unfold 1);
by (rtac (singletonI RS UnI1) 1);
qed "Zero_RepI";

Goal "i: Nat ==> Suc_Rep(i) : Nat";
by (stac Nat_unfold 1);
by (rtac (imageI RS UnI2) 1);
by (assume_tac 1);
qed "Suc_RepI";

(*** Induction ***)

val major::prems = Goal
    "[| i: Nat;  P(Zero_Rep);   \
\       !!j. [| j: Nat; P(j) |] ==> P(Suc_Rep(j)) |]  ==> P(i)";
by (rtac ([Nat_def, Nat_fun_mono, major] MRS def_lfp_induct) 1);
by (blast_tac (claset() addIs prems) 1);
qed "Nat_induct";

val prems = Goalw [Zero_def,Suc_def]
    "[| P(0);   \
\       !!n. P(n) ==> P(Suc(n)) |]  ==> P(n)";
by (rtac (Rep_Nat_inverse RS subst) 1);   (*types force good instantiation*)
by (rtac (Rep_Nat RS Nat_induct) 1);
by (REPEAT (ares_tac prems 1
     ORELSE eresolve_tac [Abs_Nat_inverse RS subst] 1));
qed "nat_induct";

(*Perform induction on n. *)
fun nat_ind_tac a i = 
  res_inst_tac [("n",a)] nat_induct i  THEN  rename_last_tac a [""] (i+1);

(*A special form of induction for reasoning about m<n and m-n*)
val prems = Goal
    "[| !!x. P x 0;  \
\       !!y. P 0 (Suc y);  \
\       !!x y. [| P x y |] ==> P (Suc x) (Suc y)  \
\    |] ==> P m n";
by (res_inst_tac [("x","m")] spec 1);
by (nat_ind_tac "n" 1);
by (rtac allI 2);
by (nat_ind_tac "x" 2);
by (REPEAT (ares_tac (prems@[allI]) 1 ORELSE etac spec 1));
qed "diff_induct";

(*** Isomorphisms: Abs_Nat and Rep_Nat ***)

(*We can't take these properties as axioms, or take Abs_Nat==Inv(Rep_Nat),
  since we assume the isomorphism equations will one day be given by Isabelle*)

Goal "inj(Rep_Nat)";
by (rtac inj_inverseI 1);
by (rtac Rep_Nat_inverse 1);
qed "inj_Rep_Nat";

Goal "inj_on Abs_Nat Nat";
by (rtac inj_on_inverseI 1);
by (etac Abs_Nat_inverse 1);
qed "inj_on_Abs_Nat";

(*** Distinctness of constructors ***)

Goalw [Zero_def,Suc_def] "Suc(m) ~= 0";
by (rtac (inj_on_Abs_Nat RS inj_on_contraD) 1);
by (rtac Suc_Rep_not_Zero_Rep 1);
by (REPEAT (resolve_tac [Rep_Nat, Suc_RepI, Zero_RepI] 1));
qed "Suc_not_Zero";

bind_thm ("Zero_not_Suc", Suc_not_Zero RS not_sym);

AddIffs [Suc_not_Zero,Zero_not_Suc];

bind_thm ("Suc_neq_Zero", (Suc_not_Zero RS notE));
bind_thm ("Zero_neq_Suc", sym RS Suc_neq_Zero);

(** Injectiveness of Suc **)

Goalw [Suc_def] "inj(Suc)";
by (rtac injI 1);
by (dtac (inj_on_Abs_Nat RS inj_onD) 1);
by (REPEAT (resolve_tac [Rep_Nat, Suc_RepI] 1));
by (dtac (inj_Suc_Rep RS injD) 1);
by (etac (inj_Rep_Nat RS injD) 1);
qed "inj_Suc";

bind_thm ("Suc_inject", inj_Suc RS injD);

Goal "(Suc(m)=Suc(n)) = (m=n)";
by (EVERY1 [rtac iffI, etac Suc_inject, etac arg_cong]); 
qed "Suc_Suc_eq";

AddIffs [Suc_Suc_eq];

Goal "n ~= Suc(n)";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "n_not_Suc_n";

bind_thm ("Suc_n_not_n", n_not_Suc_n RS not_sym);

(*** Basic properties of "less than" ***)

Goalw [wf_def, pred_nat_def] "wf(pred_nat)";
by (Clarify_tac 1);
by (nat_ind_tac "x" 1);
by (ALLGOALS Blast_tac);
qed "wf_pred_nat";

(*Used in TFL/post.sml*)
Goalw [less_def] "(m,n) : pred_nat^+ = (m<n)";
by (rtac refl 1);
qed "less_eq";

(** Introduction properties **)

Goalw [less_def] "[| i<j;  j<k |] ==> i<(k::nat)";
by (rtac (trans_trancl RS transD) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "less_trans";

Goalw [less_def, pred_nat_def] "n < Suc(n)";
by (simp_tac (simpset() addsimps [r_into_trancl]) 1);
qed "lessI";
AddIffs [lessI];

(* i<j ==> i<Suc(j) *)
bind_thm("less_SucI", lessI RSN (2, less_trans));

Goal "0 < Suc(n)";
by (nat_ind_tac "n" 1);
by (rtac lessI 1);
by (etac less_trans 1);
by (rtac lessI 1);
qed "zero_less_Suc";
AddIffs [zero_less_Suc];

(** Elimination properties **)

Goalw [less_def] "n<m ==> ~ m<(n::nat)";
by (blast_tac (claset() addIs [wf_pred_nat, wf_trancl RS wf_asym])1);
qed "less_not_sym";

(* [| n<m; ~P ==> m<n |] ==> P *)
bind_thm ("less_asym", less_not_sym RS contrapos_np);

Goalw [less_def] "~ n<(n::nat)";
by (rtac (wf_pred_nat RS wf_trancl RS wf_not_refl) 1);
qed "less_not_refl";

(* n<n ==> R *)
bind_thm ("less_irrefl", less_not_refl RS notE);
AddSEs [less_irrefl];

Goal "n<m ==> m ~= (n::nat)";
by (Blast_tac 1);
qed "less_not_refl2";

(* s < t ==> s ~= t *)
bind_thm ("less_not_refl3", less_not_refl2 RS not_sym);


val major::prems = Goalw [less_def, pred_nat_def]
    "[| i<k;  k=Suc(i) ==> P;  !!j. [| i<j;  k=Suc(j) |] ==> P \
\    |] ==> P";
by (rtac (major RS tranclE) 1);
by (ALLGOALS Full_simp_tac); 
by (REPEAT_FIRST (bound_hyp_subst_tac ORELSE'
                  eresolve_tac (prems@[asm_rl, Pair_inject])));
qed "lessE";

Goal "~ n < (0::nat)";
by (blast_tac (claset() addEs [lessE]) 1);
qed "not_less0";
AddIffs [not_less0];

(* n<0 ==> R *)
bind_thm ("less_zeroE", not_less0 RS notE);

val [major,less,eq] = Goal
    "[| m < Suc(n);  m<n ==> P;  m=n ==> P |] ==> P";
by (rtac (major RS lessE) 1);
by (rtac eq 1);
by (Blast_tac 1);
by (rtac less 1);
by (Blast_tac 1);
qed "less_SucE";

Goal "(m < Suc(n)) = (m < n | m = n)";
by (blast_tac (claset() addSEs [less_SucE] addIs [less_trans]) 1);
qed "less_Suc_eq";

Goal "(n<1) = (n=0)";
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
qed "less_one";
AddIffs [less_one];

Goal "m<n ==> Suc(m) < Suc(n)";
by (etac rev_mp 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS (fast_tac (claset() addEs [less_trans, lessE])));
qed "Suc_mono";

(*"Less than" is a linear ordering*)
Goal "m<n | m=n | n<(m::nat)";
by (nat_ind_tac "m" 1);
by (nat_ind_tac "n" 1);
by (rtac (refl RS disjI1 RS disjI2) 1);
by (rtac (zero_less_Suc RS disjI1) 1);
by (blast_tac (claset() addIs [Suc_mono, less_SucI] addEs [lessE]) 1);
qed "less_linear";

Goal "!!m::nat. (m ~= n) = (m<n | n<m)";
by (cut_facts_tac [less_linear] 1);
by (Blast_tac 1);
qed "nat_neq_iff";

val [major,eqCase,lessCase] = Goal 
   "[| (m::nat)<n ==> P n m; m=n ==> P n m; n<m ==> P n m |] ==> P n m";
by (rtac (less_linear RS disjE) 1);
by (etac disjE 2);
by (etac lessCase 1);
by (etac (sym RS eqCase) 1);
by (etac major 1);
qed "nat_less_cases";


(** Inductive (?) properties **)

Goal "[| m<n; Suc m ~= n |] ==> Suc(m) < n";
by (full_simp_tac (simpset() addsimps [nat_neq_iff]) 1);
by (blast_tac (claset() addSEs [less_irrefl, less_SucE] addEs [less_asym]) 1);
qed "Suc_lessI";

Goal "Suc(m) < n ==> m<n";
by (etac rev_mp 1);
by (nat_ind_tac "n" 1);
by (ALLGOALS (fast_tac (claset() addSIs [lessI RS less_SucI]
                                 addEs  [less_trans, lessE])));
qed "Suc_lessD";

val [major,minor] = Goal 
    "[| Suc(i)<k;  !!j. [| i<j;  k=Suc(j) |] ==> P \
\    |] ==> P";
by (rtac (major RS lessE) 1);
by (etac (lessI RS minor) 1);
by (etac (Suc_lessD RS minor) 1);
by (assume_tac 1);
qed "Suc_lessE";

Goal "Suc(m) < Suc(n) ==> m<n";
by (blast_tac (claset() addEs [lessE, make_elim Suc_lessD]) 1);
qed "Suc_less_SucD";


Goal "(Suc(m) < Suc(n)) = (m<n)";
by (EVERY1 [rtac iffI, etac Suc_less_SucD, etac Suc_mono]);
qed "Suc_less_eq";
AddIffs [Suc_less_eq];

(*Goal "~(Suc(n) < n)";
by (blast_tac (claset() addEs [Suc_lessD RS less_irrefl]) 1);
qed "not_Suc_n_less_n";
Addsimps [not_Suc_n_less_n];*)

Goal "i<j ==> j<k --> Suc i < k";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset())));
by (asm_simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (blast_tac (claset() addDs [Suc_lessD]) 1);
qed_spec_mp "less_trans_Suc";

(*Can be used with less_Suc_eq to get n=m | n<m *)
Goal "(~ m < n) = (n < Suc(m))";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "not_less_eq";

(*Complete induction, aka course-of-values induction*)
val prems = Goalw [less_def]
    "[| !!n. [| ALL m::nat. m<n --> P(m) |] ==> P(n) |]  ==>  P(n)";
by (wf_ind_tac "n" [wf_pred_nat RS wf_trancl] 1);
by (eresolve_tac prems 1);
qed "nat_less_induct";

(*** Properties of <= ***)

(*Was le_eq_less_Suc, but this orientation is more useful*)
Goalw [le_def] "(m < Suc n) = (m <= n)";
by (rtac (not_less_eq RS sym) 1);
qed "less_Suc_eq_le";

(*  m<=n ==> m < Suc n  *)
bind_thm ("le_imp_less_Suc", less_Suc_eq_le RS iffD2);

Goalw [le_def] "(0::nat) <= n";
by (rtac not_less0 1);
qed "le0";
AddIffs [le0];

Goalw [le_def] "~ Suc n <= n";
by (Simp_tac 1);
qed "Suc_n_not_le_n";

Goalw [le_def] "!!i::nat. (i <= 0) = (i = 0)";
by (nat_ind_tac "i" 1);
by (ALLGOALS Asm_simp_tac);
qed "le_0_eq";
AddIffs [le_0_eq];

Goal "(m <= Suc(n)) = (m<=n | m = Suc n)";
by (simp_tac (simpset() delsimps [less_Suc_eq_le]
			addsimps [less_Suc_eq_le RS sym, less_Suc_eq]) 1);
qed "le_Suc_eq";

(* [| m <= Suc n;  m <= n ==> R;  m = Suc n ==> R |] ==> R *)
bind_thm ("le_SucE", le_Suc_eq RS iffD1 RS disjE);

Goalw [le_def] "~n<m ==> m<=(n::nat)";
by (assume_tac 1);
qed "leI";

Goalw [le_def] "m<=n ==> ~ n < (m::nat)";
by (assume_tac 1);
qed "leD";

bind_thm ("leE", make_elim leD);

Goal "(~n<m) = (m<=(n::nat))";
by (blast_tac (claset() addIs [leI] addEs [leE]) 1);
qed "not_less_iff_le";

Goalw [le_def] "~ m <= n ==> n<(m::nat)";
by (Blast_tac 1);
qed "not_leE";

Goalw [le_def] "(~n<=m) = (m<(n::nat))";
by (Simp_tac 1);
qed "not_le_iff_less";

Goalw [le_def] "m < n ==> Suc(m) <= n";
by (simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (blast_tac (claset() addSEs [less_irrefl,less_asym]) 1);
qed "Suc_leI";  (*formerly called lessD*)

Goalw [le_def] "Suc(m) <= n ==> m <= n";
by (asm_full_simp_tac (simpset() addsimps [less_Suc_eq]) 1);
qed "Suc_leD";

(* stronger version of Suc_leD *)
Goalw [le_def] "Suc m <= n ==> m < n";
by (asm_full_simp_tac (simpset() addsimps [less_Suc_eq]) 1);
by (cut_facts_tac [less_linear] 1);
by (Blast_tac 1);
qed "Suc_le_lessD";

Goal "(Suc m <= n) = (m < n)";
by (blast_tac (claset() addIs [Suc_leI, Suc_le_lessD]) 1);
qed "Suc_le_eq";

Goalw [le_def] "m <= n ==> m <= Suc n";
by (blast_tac (claset() addDs [Suc_lessD]) 1);
qed "le_SucI";

(*bind_thm ("le_Suc", not_Suc_n_less_n RS leI);*)

Goalw [le_def] "m < n ==> m <= (n::nat)";
by (blast_tac (claset() addEs [less_asym]) 1);
qed "less_imp_le";

(*For instance, (Suc m < Suc n)  =   (Suc m <= n)  =  (m<n) *)
bind_thms ("le_simps", [less_imp_le, less_Suc_eq_le, Suc_le_eq]);


(** Equivalence of m<=n and  m<n | m=n **)

Goalw [le_def] "m <= n ==> m < n | m=(n::nat)";
by (cut_facts_tac [less_linear] 1);
by (blast_tac (claset() addEs [less_irrefl,less_asym]) 1);
qed "le_imp_less_or_eq";

Goalw [le_def] "m<n | m=n ==> m <=(n::nat)";
by (cut_facts_tac [less_linear] 1);
by (blast_tac (claset() addSEs [less_irrefl] addEs [less_asym]) 1);
qed "less_or_eq_imp_le";

Goal "(m <= (n::nat)) = (m < n | m=n)";
by (REPEAT(ares_tac [iffI,less_or_eq_imp_le,le_imp_less_or_eq] 1));
qed "le_eq_less_or_eq";

(*Useful with Blast_tac.   m=n ==> m<=n *)
bind_thm ("eq_imp_le", disjI2 RS less_or_eq_imp_le);

Goal "n <= (n::nat)";
by (simp_tac (simpset() addsimps [le_eq_less_or_eq]) 1);
qed "le_refl";


Goal "[| i <= j; j < k |] ==> i < (k::nat)";
by (blast_tac (claset() addSDs [le_imp_less_or_eq]
	                addIs [less_trans]) 1);
qed "le_less_trans";

Goal "[| i < j; j <= k |] ==> i < (k::nat)";
by (blast_tac (claset() addSDs [le_imp_less_or_eq]
	                addIs [less_trans]) 1);
qed "less_le_trans";

Goal "[| i <= j; j <= k |] ==> i <= (k::nat)";
by (blast_tac (claset() addSDs [le_imp_less_or_eq]
	                addIs [less_or_eq_imp_le, less_trans]) 1);
qed "le_trans";

Goal "[| m <= n; n <= m |] ==> m = (n::nat)";
(*order_less_irrefl could make this proof fail*)
by (blast_tac (claset() addSDs [le_imp_less_or_eq]
	                addSEs [less_irrefl] addEs [less_asym]) 1);
qed "le_anti_sym";

Goal "(Suc(n) <= Suc(m)) = (n <= m)";
by (simp_tac (simpset() addsimps le_simps) 1);
qed "Suc_le_mono";

AddIffs [Suc_le_mono];

(* Axiom 'order_less_le' of class 'order': *)
Goal "(m::nat) < n = (m <= n & m ~= n)";
by (simp_tac (simpset() addsimps [le_def, nat_neq_iff]) 1);
by (blast_tac (claset() addSEs [less_asym]) 1);
qed "nat_less_le";

(* [| m <= n; m ~= n |] ==> m < n *)
bind_thm ("le_neq_implies_less", [nat_less_le, conjI] MRS iffD2);

(* Axiom 'linorder_linear' of class 'linorder': *)
Goal "(m::nat) <= n | n <= m";
by (simp_tac (simpset() addsimps [le_eq_less_or_eq]) 1);
by (cut_facts_tac [less_linear] 1);
by (Blast_tac 1);
qed "nat_le_linear";

Goal "~ n < m ==> (n < Suc m) = (n = m)";
by (blast_tac (claset() addSEs [less_SucE]) 1);
qed "not_less_less_Suc_eq";


(*Rewrite (n < Suc m) to (n=m) if  ~ n<m or m<=n hold.
  Not suitable as default simprules because they often lead to looping*)
bind_thms ("not_less_simps", [not_less_less_Suc_eq, leD RS not_less_less_Suc_eq]);

(** LEAST -- the least number operator **)

Goal "(ALL m::nat. P m --> n <= m) = (ALL m. m < n --> ~ P m)";
by (blast_tac (claset() addIs [leI] addEs [leE]) 1);
val lemma = result();

(* This is an old def of Least for nat, which is derived for compatibility *)
Goalw [Least_def]
  "(LEAST n::nat. P n) == (@n. P(n) & (ALL m. m < n --> ~P(m)))";
by (simp_tac (simpset() addsimps [lemma]) 1);
qed "Least_nat_def";

val [prem1,prem2] = Goalw [Least_nat_def]
    "[| P(k::nat);  !!x. x<k ==> ~P(x) |] ==> (LEAST x. P(x)) = k";
by (rtac some_equality 1);
by (blast_tac (claset() addSIs [prem1,prem2]) 1);
by (cut_facts_tac [less_linear] 1);
by (blast_tac (claset() addSIs [prem1] addSDs [prem2]) 1);
qed "Least_equality";

Goal "P(k::nat) ==> P(LEAST x. P(x))";
by (etac rev_mp 1);
by (res_inst_tac [("n","k")] nat_less_induct 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","n")] (Least_equality RS ssubst) 1);
by (assume_tac 1);
by (assume_tac 2);
by (Blast_tac 1);
qed "LeastI";

(*Proof is almost identical to the one above!*)
Goal "P(k::nat) ==> (LEAST x. P(x)) <= k";
by (etac rev_mp 1);
by (res_inst_tac [("n","k")] nat_less_induct 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","n")] (Least_equality RS ssubst) 1);
by (assume_tac 1);
by (rtac le_refl 2);
by (blast_tac (claset() addIs [less_imp_le,le_trans]) 1);
qed "Least_le";

Goal "k < (LEAST x. P(x)) ==> ~P(k::nat)";
by (rtac notI 1);
by (etac (rewrite_rule [le_def] Least_le RS notE) 1 THEN assume_tac 1);
qed "not_less_Least";

(* [| m ~= n; m < n ==> P; n < m ==> P |] ==> P *)
bind_thm("nat_neqE", nat_neq_iff RS iffD1 RS disjE);

Goal "(S::nat set) ~= {} ==> EX x:S. ALL y:S. x <= y";
by (cut_facts_tac [wf_pred_nat RS wf_trancl RS (wf_eq_minimal RS iffD1)] 1);
by (dres_inst_tac [("x","S")] spec 1);
by (Asm_full_simp_tac 1);
by (etac impE 1);
by (Force_tac 1);
by (force_tac (claset(), simpset() addsimps [less_eq,not_le_iff_less]) 1);
qed "nonempty_has_least";

(** Re-orientation of the equations 0=x and Suc n = x. *

  The condition "True" is a hack to prevent looping for e.g. Suc m = Suc n.
  Conditional rewrite rules are tried after unconditional ones.
**)

(*Polymorphic, not just for "nat"*)
Goal "True ==> (0 = x) = (x = 0)";
by Auto_tac;  
qed "zero_reorient";
Addsimps [zero_reorient];

Goal "True ==> (1 = x) = (x = 1)";
by Auto_tac;  
qed "one_reorient";
Addsimps [one_reorient];

Goal "True ==> (2 = x) = (x = 2)";
by Auto_tac;  
qed "two_reorient";
Addsimps [two_reorient];
