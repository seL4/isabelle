(*  Title:      HOL/nat
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For nat.thy.  Type nat is defined as a set (Nat) over the type ind.
*)

open Nat;

goal Nat.thy "mono(%X. {Zero_Rep} Un (Suc_Rep``X))";
by (REPEAT (ares_tac [monoI, subset_refl, image_mono, Un_mono] 1));
qed "Nat_fun_mono";

val Nat_unfold = Nat_fun_mono RS (Nat_def RS def_lfp_Tarski);

(* Zero is a natural number -- this also justifies the type definition*)
goal Nat.thy "Zero_Rep: Nat";
by (rtac (Nat_unfold RS ssubst) 1);
by (rtac (singletonI RS UnI1) 1);
qed "Zero_RepI";

val prems = goal Nat.thy "i: Nat ==> Suc_Rep(i) : Nat";
by (rtac (Nat_unfold RS ssubst) 1);
by (rtac (imageI RS UnI2) 1);
by (resolve_tac prems 1);
qed "Suc_RepI";

(*** Induction ***)

val major::prems = goal Nat.thy
    "[| i: Nat;  P(Zero_Rep);   \
\       !!j. [| j: Nat; P(j) |] ==> P(Suc_Rep(j)) |]  ==> P(i)";
by (rtac ([Nat_def, Nat_fun_mono, major] MRS def_induct) 1);
by (fast_tac (!claset addIs prems) 1);
qed "Nat_induct";

val prems = goalw Nat.thy [Zero_def,Suc_def]
    "[| P(0);   \
\       !!k. P(k) ==> P(Suc(k)) |]  ==> P(n)";
by (rtac (Rep_Nat_inverse RS subst) 1);   (*types force good instantiation*)
by (rtac (Rep_Nat RS Nat_induct) 1);
by (REPEAT (ares_tac prems 1
     ORELSE eresolve_tac [Abs_Nat_inverse RS subst] 1));
qed "nat_induct";

(*Perform induction on n. *)
fun nat_ind_tac a i = 
    EVERY [res_inst_tac [("n",a)] nat_induct i,
           rename_last_tac a ["1"] (i+1)];

(*A special form of induction for reasoning about m<n and m-n*)
val prems = goal Nat.thy
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

(*Case analysis on the natural numbers*)
val prems = goal Nat.thy 
    "[| n=0 ==> P;  !!x. n = Suc(x) ==> P |] ==> P";
by (subgoal_tac "n=0 | (EX x. n = Suc(x))" 1);
by (fast_tac (!claset addSEs prems) 1);
by (nat_ind_tac "n" 1);
by (rtac (refl RS disjI1) 1);
by (Fast_tac 1);
qed "natE";

(*** Isomorphisms: Abs_Nat and Rep_Nat ***)

(*We can't take these properties as axioms, or take Abs_Nat==Inv(Rep_Nat),
  since we assume the isomorphism equations will one day be given by Isabelle*)

goal Nat.thy "inj(Rep_Nat)";
by (rtac inj_inverseI 1);
by (rtac Rep_Nat_inverse 1);
qed "inj_Rep_Nat";

goal Nat.thy "inj_onto Abs_Nat Nat";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Nat_inverse 1);
qed "inj_onto_Abs_Nat";

(*** Distinctness of constructors ***)

goalw Nat.thy [Zero_def,Suc_def] "Suc(m) ~= 0";
by (rtac (inj_onto_Abs_Nat RS inj_onto_contraD) 1);
by (rtac Suc_Rep_not_Zero_Rep 1);
by (REPEAT (resolve_tac [Rep_Nat, Suc_RepI, Zero_RepI] 1));
qed "Suc_not_Zero";

bind_thm ("Zero_not_Suc", (Suc_not_Zero RS not_sym));

Addsimps [Suc_not_Zero,Zero_not_Suc];

bind_thm ("Suc_neq_Zero", (Suc_not_Zero RS notE));
val Zero_neq_Suc = sym RS Suc_neq_Zero;

(** Injectiveness of Suc **)

goalw Nat.thy [Suc_def] "inj(Suc)";
by (rtac injI 1);
by (dtac (inj_onto_Abs_Nat RS inj_ontoD) 1);
by (REPEAT (resolve_tac [Rep_Nat, Suc_RepI] 1));
by (dtac (inj_Suc_Rep RS injD) 1);
by (etac (inj_Rep_Nat RS injD) 1);
qed "inj_Suc";

val Suc_inject = inj_Suc RS injD;

goal Nat.thy "(Suc(m)=Suc(n)) = (m=n)";
by (EVERY1 [rtac iffI, etac Suc_inject, etac arg_cong]); 
qed "Suc_Suc_eq";

goal Nat.thy "n ~= Suc(n)";
by (nat_ind_tac "n" 1);
by (ALLGOALS(asm_simp_tac (!simpset addsimps [Suc_Suc_eq])));
qed "n_not_Suc_n";

bind_thm ("Suc_n_not_n", n_not_Suc_n RS not_sym);

(*** nat_case -- the selection operator for nat ***)

goalw Nat.thy [nat_case_def] "nat_case a f 0 = a";
by (fast_tac (!claset addIs [select_equality] addEs [Zero_neq_Suc]) 1);
qed "nat_case_0";

goalw Nat.thy [nat_case_def] "nat_case a f (Suc k) = f(k)";
by (fast_tac (!claset addIs [select_equality] 
                       addEs [make_elim Suc_inject, Suc_neq_Zero]) 1);
qed "nat_case_Suc";

(** Introduction rules for 'pred_nat' **)

goalw Nat.thy [pred_nat_def] "(n, Suc(n)) : pred_nat";
by (Fast_tac 1);
qed "pred_natI";

val major::prems = goalw Nat.thy [pred_nat_def]
    "[| p : pred_nat;  !!x n. [| p = (n, Suc(n)) |] ==> R \
\    |] ==> R";
by (rtac (major RS CollectE) 1);
by (REPEAT (eresolve_tac ([asm_rl,exE]@prems) 1));
qed "pred_natE";

goalw Nat.thy [wf_def] "wf(pred_nat)";
by (strip_tac 1);
by (nat_ind_tac "x" 1);
by (fast_tac (!claset addSEs [mp, pred_natE, Pair_inject, 
                             make_elim Suc_inject]) 2);
by (fast_tac (!claset addSEs [mp, pred_natE, Pair_inject, Zero_neq_Suc]) 1);
qed "wf_pred_nat";


(*** nat_rec -- by wf recursion on pred_nat ***)

(* The unrolling rule for nat_rec *)
goal Nat.thy
   "(%n. nat_rec c d n) = wfrec pred_nat (%f. nat_case ?c (%m. ?d m (f m)))";
  by (simp_tac (HOL_ss addsimps [nat_rec_def]) 1);
bind_thm("nat_rec_unfold", wf_pred_nat RS 
                            ((result() RS eq_reflection) RS def_wfrec));

(*---------------------------------------------------------------------------
 * Old:
 * bind_thm ("nat_rec_unfold", (wf_pred_nat RS (nat_rec_def RS def_wfrec))); 
 *---------------------------------------------------------------------------*)

(** conversion rules **)

goal Nat.thy "nat_rec c h 0 = c";
by (rtac (nat_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [nat_case_0]) 1);
qed "nat_rec_0";

goal Nat.thy "nat_rec c h (Suc n) = h n (nat_rec c h n)";
by (rtac (nat_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [nat_case_Suc, pred_natI, cut_apply]) 1);
qed "nat_rec_Suc";

(*These 2 rules ease the use of primitive recursion.  NOTE USE OF == *)
val [rew] = goal Nat.thy
    "[| !!n. f(n) == nat_rec c h n |] ==> f(0) = c";
by (rewtac rew);
by (rtac nat_rec_0 1);
qed "def_nat_rec_0";

val [rew] = goal Nat.thy
    "[| !!n. f(n) == nat_rec c h n |] ==> f(Suc(n)) = h n (f n)";
by (rewtac rew);
by (rtac nat_rec_Suc 1);
qed "def_nat_rec_Suc";

fun nat_recs def =
      [standard (def RS def_nat_rec_0),
       standard (def RS def_nat_rec_Suc)];


(*** Basic properties of "less than" ***)

(** Introduction properties **)

val prems = goalw Nat.thy [less_def] "[| i<j;  j<k |] ==> i<(k::nat)";
by (rtac (trans_trancl RS transD) 1);
by (resolve_tac prems 1);
by (resolve_tac prems 1);
qed "less_trans";

goalw Nat.thy [less_def] "n < Suc(n)";
by (rtac (pred_natI RS r_into_trancl) 1);
qed "lessI";
Addsimps [lessI];

(* i<j ==> i<Suc(j) *)
val less_SucI = lessI RSN (2, less_trans);

goal Nat.thy "0 < Suc(n)";
by (nat_ind_tac "n" 1);
by (rtac lessI 1);
by (etac less_trans 1);
by (rtac lessI 1);
qed "zero_less_Suc";
Addsimps [zero_less_Suc];

(** Elimination properties **)

val prems = goalw Nat.thy [less_def] "n<m ==> ~ m<(n::nat)";
by (fast_tac (!claset addIs ([wf_pred_nat, wf_trancl RS wf_asym]@prems))1);
qed "less_not_sym";

(* [| n(m; m(n |] ==> R *)
bind_thm ("less_asym", (less_not_sym RS notE));

goalw Nat.thy [less_def] "~ n<(n::nat)";
by (rtac notI 1);
by (etac (wf_pred_nat RS wf_trancl RS wf_irrefl) 1);
qed "less_not_refl";

(* n<n ==> R *)
bind_thm ("less_irrefl", (less_not_refl RS notE));

goal Nat.thy "!!m. n<m ==> m ~= (n::nat)";
by (fast_tac (!claset addEs [less_irrefl]) 1);
qed "less_not_refl2";


val major::prems = goalw Nat.thy [less_def]
    "[| i<k;  k=Suc(i) ==> P;  !!j. [| i<j;  k=Suc(j) |] ==> P \
\    |] ==> P";
by (rtac (major RS tranclE) 1);
by (REPEAT_FIRST (bound_hyp_subst_tac ORELSE'
                  eresolve_tac (prems@[pred_natE, Pair_inject])));
by (rtac refl 1);
qed "lessE";

goal Nat.thy "~ n<0";
by (rtac notI 1);
by (etac lessE 1);
by (etac Zero_neq_Suc 1);
by (etac Zero_neq_Suc 1);
qed "not_less0";
Addsimps [not_less0];

(* n<0 ==> R *)
bind_thm ("less_zeroE", (not_less0 RS notE));
AddSEs [less_zeroE];

val [major,less,eq] = goal Nat.thy
    "[| m < Suc(n);  m<n ==> P;  m=n ==> P |] ==> P";
by (rtac (major RS lessE) 1);
by (rtac eq 1);
by (fast_tac (!claset addSDs [Suc_inject]) 1);
by (rtac less 1);
by (fast_tac (!claset addSDs [Suc_inject]) 1);
qed "less_SucE";

goal Nat.thy "(m < Suc(n)) = (m < n | m = n)";
by (fast_tac (!claset addSIs [lessI]
                      addEs  [less_trans, less_SucE]) 1);
qed "less_Suc_eq";

val prems = goal Nat.thy "m<n ==> n ~= 0";
by (res_inst_tac [("n","n")] natE 1);
by (cut_facts_tac prems 1);
by (ALLGOALS Asm_full_simp_tac);
qed "gr_implies_not0";
Addsimps [gr_implies_not0];

qed_goal "zero_less_eq" Nat.thy "0 < n = (n ~= 0)" (fn _ => [
	rtac iffI 1,
	etac gr_implies_not0 1,
	rtac natE 1,
	contr_tac 1,
	etac ssubst 1,
	rtac zero_less_Suc 1]);

(** Inductive (?) properties **)

val [prem] = goal Nat.thy "Suc(m) < n ==> m<n";
by (rtac (prem RS rev_mp) 1);
by (nat_ind_tac "n" 1);
by (rtac impI 1);
by (etac less_zeroE 1);
by (fast_tac (!claset addSIs [lessI RS less_SucI]
                     addSDs [Suc_inject]
                     addEs  [less_trans, lessE]) 1);
qed "Suc_lessD";

val [major,minor] = goal Nat.thy 
    "[| Suc(i)<k;  !!j. [| i<j;  k=Suc(j) |] ==> P \
\    |] ==> P";
by (rtac (major RS lessE) 1);
by (etac (lessI RS minor) 1);
by (etac (Suc_lessD RS minor) 1);
by (assume_tac 1);
qed "Suc_lessE";

val [major] = goal Nat.thy "Suc(m) < Suc(n) ==> m<n";
by (rtac (major RS lessE) 1);
by (REPEAT (rtac lessI 1
     ORELSE eresolve_tac [make_elim Suc_inject, ssubst, Suc_lessD] 1));
qed "Suc_less_SucD";

val prems = goal Nat.thy "m<n ==> Suc(m) < Suc(n)";
by (subgoal_tac "m<n --> Suc(m) < Suc(n)" 1);
by (fast_tac (!claset addIs prems) 1);
by (nat_ind_tac "n" 1);
by (rtac impI 1);
by (etac less_zeroE 1);
by (fast_tac (!claset addSIs [lessI]
                     addSDs [Suc_inject]
                     addEs  [less_trans, lessE]) 1);
qed "Suc_mono";


goal Nat.thy "(Suc(m) < Suc(n)) = (m<n)";
by (EVERY1 [rtac iffI, etac Suc_less_SucD, etac Suc_mono]);
qed "Suc_less_eq";
Addsimps [Suc_less_eq];

goal Nat.thy "~(Suc(n) < n)";
by (fast_tac (!claset addEs [Suc_lessD RS less_irrefl]) 1);
qed "not_Suc_n_less_n";
Addsimps [not_Suc_n_less_n];

goal Nat.thy "!!i. i<j ==> j<k --> Suc i < k";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac (!simpset)));
by (asm_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (fast_tac (!claset addDs [Suc_lessD]) 1);
qed_spec_mp "less_trans_Suc";

(*"Less than" is a linear ordering*)
goal Nat.thy "m<n | m=n | n<(m::nat)";
by (nat_ind_tac "m" 1);
by (nat_ind_tac "n" 1);
by (rtac (refl RS disjI1 RS disjI2) 1);
by (rtac (zero_less_Suc RS disjI1) 1);
by (fast_tac (!claset addIs [lessI, Suc_mono, less_SucI] addEs [lessE]) 1);
qed "less_linear";

qed_goal "nat_less_cases" Nat.thy 
   "[| (m::nat)<n ==> P n m; m=n ==> P n m; n<m ==> P n m |] ==> P n m"
( fn prems =>
        [
        (res_inst_tac [("m1","n"),("n1","m")] (less_linear RS disjE) 1),
        (etac disjE 2),
        (etac (hd (tl (tl prems))) 1),
        (etac (sym RS hd (tl prems)) 1),
        (etac (hd prems) 1)
        ]);

(*Can be used with less_Suc_eq to get n=m | n<m *)
goal Nat.thy "(~ m < n) = (n < Suc(m))";
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "not_less_eq";

(*Complete induction, aka course-of-values induction*)
val prems = goalw Nat.thy [less_def]
    "[| !!n. [| ! m::nat. m<n --> P(m) |] ==> P(n) |]  ==>  P(n)";
by (wf_ind_tac "n" [wf_pred_nat RS wf_trancl] 1);
by (eresolve_tac prems 1);
qed "less_induct";


(*** Properties of <= ***)

goalw Nat.thy [le_def] "0 <= n";
by (rtac not_less0 1);
qed "le0";

goalw Nat.thy [le_def] "~ Suc n <= n";
by (Simp_tac 1);
qed "Suc_n_not_le_n";

goalw Nat.thy [le_def] "(i <= 0) = (i = 0)";
by (nat_ind_tac "i" 1);
by (ALLGOALS Asm_simp_tac);
qed "le_0_eq";

Addsimps [less_not_refl,
          (*less_Suc_eq, makes simpset non-confluent*) le0, le_0_eq,
          Suc_Suc_eq, Suc_n_not_le_n,
          n_not_Suc_n, Suc_n_not_n,
          nat_case_0, nat_case_Suc, nat_rec_0, nat_rec_Suc];

(*
goal Nat.thy "(Suc m < n | Suc m = n) = (m < n)";
by(stac (less_Suc_eq RS sym) 1);
by(rtac Suc_less_eq 1);
qed "Suc_le_eq";

this could make the simpset (with less_Suc_eq added again) more confluent,
but less_Suc_eq makes additional problems with terms of the form 0 < Suc (...)
*)

(*Prevents simplification of f and g: much faster*)
qed_goal "nat_case_weak_cong" Nat.thy
  "m=n ==> nat_case a f m = nat_case a f n"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

qed_goal "nat_rec_weak_cong" Nat.thy
  "m=n ==> nat_rec a f m = nat_rec a f n"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);

val prems = goalw Nat.thy [le_def] "~n<m ==> m<=(n::nat)";
by (resolve_tac prems 1);
qed "leI";

val prems = goalw Nat.thy [le_def] "m<=n ==> ~ n < (m::nat)";
by (resolve_tac prems 1);
qed "leD";

val leE = make_elim leD;

goal Nat.thy "(~n<m) = (m<=(n::nat))";
by (fast_tac (!claset addIs [leI] addEs [leE]) 1);
qed "not_less_iff_le";

goalw Nat.thy [le_def] "!!m. ~ m <= n ==> n<(m::nat)";
by (Fast_tac 1);
qed "not_leE";

goalw Nat.thy [le_def] "!!m. m < n ==> Suc(m) <= n";
by (simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (fast_tac (!claset addEs [less_irrefl,less_asym]) 1);
qed "lessD";

goalw Nat.thy [le_def] "!!m. Suc(m) <= n ==> m <= n";
by (asm_full_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (Fast_tac 1);
qed "Suc_leD";

(* stronger version of Suc_leD *)
goalw Nat.thy [le_def] 
        "!!m. Suc m <= n ==> m < n";
by (asm_full_simp_tac (!simpset addsimps [less_Suc_eq]) 1);
by (cut_facts_tac [less_linear] 1);
by (Fast_tac 1);
qed "Suc_le_lessD";

goal Nat.thy "(Suc m <= n) = (m < n)";
by (fast_tac (!claset addIs [lessD, Suc_le_lessD]) 1);
qed "Suc_le_eq";

goalw Nat.thy [le_def] "!!m. m <= n ==> m <= Suc n";
by (fast_tac (!claset addDs [Suc_lessD]) 1);
qed "le_SucI";
Addsimps[le_SucI];

goalw Nat.thy [le_def] "!!m. m < n ==> m <= (n::nat)";
by (fast_tac (!claset addEs [less_asym]) 1);
qed "less_imp_le";

goalw Nat.thy [le_def] "!!m. m <= n ==> m < n | m=(n::nat)";
by (cut_facts_tac [less_linear] 1);
by (fast_tac (!claset addEs [less_irrefl,less_asym]) 1);
qed "le_imp_less_or_eq";

goalw Nat.thy [le_def] "!!m. m<n | m=n ==> m <=(n::nat)";
by (cut_facts_tac [less_linear] 1);
by (fast_tac (!claset addEs [less_irrefl,less_asym]) 1);
by (flexflex_tac);
qed "less_or_eq_imp_le";

goal Nat.thy "(x <= (y::nat)) = (x < y | x=y)";
by (REPEAT(ares_tac [iffI,less_or_eq_imp_le,le_imp_less_or_eq] 1));
qed "le_eq_less_or_eq";

goal Nat.thy "n <= (n::nat)";
by (simp_tac (!simpset addsimps [le_eq_less_or_eq]) 1);
qed "le_refl";

val prems = goal Nat.thy "!!i. [| i <= j; j < k |] ==> i < (k::nat)";
by (dtac le_imp_less_or_eq 1);
by (fast_tac (!claset addIs [less_trans]) 1);
qed "le_less_trans";

goal Nat.thy "!!i. [| i < j; j <= k |] ==> i < (k::nat)";
by (dtac le_imp_less_or_eq 1);
by (fast_tac (!claset addIs [less_trans]) 1);
qed "less_le_trans";

goal Nat.thy "!!i. [| i <= j; j <= k |] ==> i <= (k::nat)";
by (EVERY1[dtac le_imp_less_or_eq, dtac le_imp_less_or_eq,
          rtac less_or_eq_imp_le, fast_tac (!claset addIs [less_trans])]);
qed "le_trans";

val prems = goal Nat.thy "!!m. [| m <= n; n <= m |] ==> m = (n::nat)";
by (EVERY1[dtac le_imp_less_or_eq, dtac le_imp_less_or_eq,
          fast_tac (!claset addEs [less_irrefl,less_asym])]);
qed "le_anti_sym";

goal Nat.thy "(Suc(n) <= Suc(m)) = (n <= m)";
by (simp_tac (!simpset addsimps [le_eq_less_or_eq]) 1);
qed "Suc_le_mono";

Addsimps [le_refl,Suc_le_mono];


(** LEAST -- the least number operator **)

val [prem1,prem2] = goalw Nat.thy [Least_def]
    "[| P(k);  !!x. x<k ==> ~P(x) |] ==> (LEAST x.P(x)) = k";
by (rtac select_equality 1);
by (fast_tac (!claset addSIs [prem1,prem2]) 1);
by (cut_facts_tac [less_linear] 1);
by (fast_tac (!claset addSIs [prem1] addSDs [prem2]) 1);
qed "Least_equality";

val [prem] = goal Nat.thy "P(k) ==> P(LEAST x.P(x))";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","n")] (Least_equality RS ssubst) 1);
by (assume_tac 1);
by (assume_tac 2);
by (Fast_tac 1);
qed "LeastI";

(*Proof is almost identical to the one above!*)
val [prem] = goal Nat.thy "P(k) ==> (LEAST x.P(x)) <= k";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("n","k")] less_induct 1);
by (rtac impI 1);
by (rtac classical 1);
by (res_inst_tac [("s","n")] (Least_equality RS ssubst) 1);
by (assume_tac 1);
by (rtac le_refl 2);
by (fast_tac (!claset addIs [less_imp_le,le_trans]) 1);
qed "Least_le";

val [prem] = goal Nat.thy "k < (LEAST x.P(x)) ==> ~P(k)";
by (rtac notI 1);
by (etac (rewrite_rule [le_def] Least_le RS notE) 1);
by (rtac prem 1);
qed "not_less_Least";

qed_goalw "Least_Suc" Nat.thy [Least_def]
 "[| ? n. P (Suc n); ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P (Suc m))"
 (fn prems => [
	cut_facts_tac prems 1,
	rtac select_equality 1,
	fold_goals_tac [Least_def],
	safe_tac (!claset addSEs [LeastI]),
	res_inst_tac [("n","j")] natE 1,
	Fast_tac 1,
	fast_tac (!claset addDs [Suc_less_SucD] addDs [not_less_Least]) 1,	
	res_inst_tac [("n","k")] natE 1,
	Fast_tac 1,
	hyp_subst_tac 1,
	rewtac Least_def,
	rtac (select_equality RS arg_cong RS sym) 1,
	safe_tac (!claset),
	dtac Suc_mono 1,
	Fast_tac 1,
	cut_facts_tac [less_linear] 1,
	safe_tac (!claset),
	atac 2,
	Fast_tac 2,
	dtac Suc_mono 1,
	Fast_tac 1]);
