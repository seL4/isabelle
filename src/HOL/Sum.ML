(*  Title:      HOL/Sum.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

For Sum.thy.  The disjoint sum of two types
*)

open Sum;

(** Inl_Rep and Inr_Rep: Representations of the constructors **)

(*This counts as a non-emptiness result for admitting 'a+'b as a type*)
goalw Sum.thy [Sum_def] "Inl_Rep(a) : Sum";
by (EVERY1 [rtac CollectI, rtac disjI1, rtac exI, rtac refl]);
qed "Inl_RepI";

goalw Sum.thy [Sum_def] "Inr_Rep(b) : Sum";
by (EVERY1 [rtac CollectI, rtac disjI2, rtac exI, rtac refl]);
qed "Inr_RepI";

goal Sum.thy "inj_onto Abs_Sum Sum";
by (rtac inj_onto_inverseI 1);
by (etac Abs_Sum_inverse 1);
qed "inj_onto_Abs_Sum";

(** Distinctness of Inl and Inr **)

goalw Sum.thy [Inl_Rep_def, Inr_Rep_def] "Inl_Rep(a) ~= Inr_Rep(b)";
by (EVERY1 [rtac notI,
            etac (fun_cong RS fun_cong RS fun_cong RS iffE), 
            rtac (notE RS ccontr),  etac (mp RS conjunct2), 
            REPEAT o (ares_tac [refl,conjI]) ]);
qed "Inl_Rep_not_Inr_Rep";

goalw Sum.thy [Inl_def,Inr_def] "Inl(a) ~= Inr(b)";
by (rtac (inj_onto_Abs_Sum RS inj_onto_contraD) 1);
by (rtac Inl_Rep_not_Inr_Rep 1);
by (rtac Inl_RepI 1);
by (rtac Inr_RepI 1);
qed "Inl_not_Inr";

bind_thm ("Inl_neq_Inr", (Inl_not_Inr RS notE));
val Inr_neq_Inl = sym RS Inl_neq_Inr;

goal Sum.thy "(Inl(a)=Inr(b)) = False";
by (simp_tac (!simpset addsimps [Inl_not_Inr]) 1);
qed "Inl_Inr_eq";

goal Sum.thy "(Inr(b)=Inl(a))  =  False";
by (simp_tac (!simpset addsimps [Inl_not_Inr RS not_sym]) 1);
qed "Inr_Inl_eq";


(** Injectiveness of Inl and Inr **)

val [major] = goalw Sum.thy [Inl_Rep_def] "Inl_Rep(a) = Inl_Rep(c) ==> a=c";
by (rtac (major RS fun_cong RS fun_cong RS fun_cong RS iffE) 1);
by (Fast_tac 1);
qed "Inl_Rep_inject";

val [major] = goalw Sum.thy [Inr_Rep_def] "Inr_Rep(b) = Inr_Rep(d) ==> b=d";
by (rtac (major RS fun_cong RS fun_cong RS fun_cong RS iffE) 1);
by (Fast_tac 1);
qed "Inr_Rep_inject";

goalw Sum.thy [Inl_def] "inj(Inl)";
by (rtac injI 1);
by (etac (inj_onto_Abs_Sum RS inj_ontoD RS Inl_Rep_inject) 1);
by (rtac Inl_RepI 1);
by (rtac Inl_RepI 1);
qed "inj_Inl";
val Inl_inject = inj_Inl RS injD;

goalw Sum.thy [Inr_def] "inj(Inr)";
by (rtac injI 1);
by (etac (inj_onto_Abs_Sum RS inj_ontoD RS Inr_Rep_inject) 1);
by (rtac Inr_RepI 1);
by (rtac Inr_RepI 1);
qed "inj_Inr";
val Inr_inject = inj_Inr RS injD;

goal Sum.thy "(Inl(x)=Inl(y)) = (x=y)";
by (fast_tac (!claset addSEs [Inl_inject]) 1);
qed "Inl_eq";

goal Sum.thy "(Inr(x)=Inr(y)) = (x=y)";
by (fast_tac (!claset addSEs [Inr_inject]) 1);
qed "Inr_eq";

(*** Rules for the disjoint sum of two SETS ***)

(** Introduction rules for the injections **)

goalw Sum.thy [sum_def] "!!a A B. a : A ==> Inl(a) : A plus B";
by (REPEAT (ares_tac [UnI1,imageI] 1));
qed "InlI";

goalw Sum.thy [sum_def] "!!b A B. b : B ==> Inr(b) : A plus B";
by (REPEAT (ares_tac [UnI2,imageI] 1));
qed "InrI";

(** Elimination rules **)

val major::prems = goalw Sum.thy [sum_def]
    "[| u: A plus B;  \
\       !!x. [| x:A;  u=Inl(x) |] ==> P; \
\       !!y. [| y:B;  u=Inr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[imageE,ssubst]) 1));
qed "plusE";


val sum_cs = set_cs addSIs [InlI, InrI] 
                    addSEs [plusE, Inl_neq_Inr, Inr_neq_Inl]
                    addSDs [Inl_inject, Inr_inject];

AddSIs [InlI, InrI]; 
AddSEs [plusE, Inl_neq_Inr, Inr_neq_Inl];
AddSDs [Inl_inject, Inr_inject];


(** sum_case -- the selection operator for sums **)

goalw Sum.thy [sum_case_def] "sum_case f g (Inl x) = f(x)";
by (fast_tac (!claset addIs [select_equality]) 1);
qed "sum_case_Inl";

goalw Sum.thy [sum_case_def] "sum_case f g (Inr x) = g(x)";
by (fast_tac (!claset addIs [select_equality]) 1);
qed "sum_case_Inr";

(** Exhaustion rule for sums -- a degenerate form of induction **)

val prems = goalw Sum.thy [Inl_def,Inr_def]
    "[| !!x::'a. s = Inl(x) ==> P;  !!y::'b. s = Inr(y) ==> P \
\    |] ==> P";
by (rtac (rewrite_rule [Sum_def] Rep_Sum RS CollectE) 1);
by (REPEAT (eresolve_tac [disjE,exE] 1
     ORELSE EVERY1 [resolve_tac prems, 
                    etac subst,
                    rtac (Rep_Sum_inverse RS sym)]));
qed "sumE";

goal Sum.thy "sum_case (%x::'a. f(Inl x)) (%y::'b. f(Inr y)) s = f(s)";
by (EVERY1 [res_inst_tac [("s","s")] sumE, 
            etac ssubst, rtac sum_case_Inl,
            etac ssubst, rtac sum_case_Inr]);
qed "surjective_sum";

goal Sum.thy "R(sum_case f g s) = \
\             ((! x. s = Inl(x) --> R(f(x))) & (! y. s = Inr(y) --> R(g(y))))";
by (rtac sumE 1);
by (etac ssubst 1);
by (stac sum_case_Inl 1);
by (fast_tac (!claset addSEs [make_elim Inl_inject, Inl_neq_Inr]) 1);
by (etac ssubst 1);
by (stac sum_case_Inr 1);
by (fast_tac (!claset addSEs [make_elim Inr_inject, Inr_neq_Inl]) 1);
qed "expand_sum_case";

Addsimps [Inl_eq, Inr_eq, Inl_Inr_eq, Inr_Inl_eq,  sum_case_Inl, sum_case_Inr];

(*Prevents simplification of f and g: much faster*)
qed_goal "sum_case_weak_cong" Sum.thy
  "s=t ==> sum_case f g s = sum_case f g t"
  (fn [prem] => [rtac (prem RS arg_cong) 1]);




(** Rules for the Part primitive **)

goalw Sum.thy [Part_def]
    "!!a b A h. [| a : A;  a=h(b) |] ==> a : Part A h";
by (Fast_tac 1);
qed "Part_eqI";

val PartI = refl RSN (2,Part_eqI);

val major::prems = goalw Sum.thy [Part_def]
    "[| a : Part A h;  !!z. [| a : A;  a=h(z) |] ==> P  \
\    |] ==> P";
by (rtac (major RS IntE) 1);
by (etac CollectE 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
qed "PartE";

goalw Sum.thy [Part_def] "Part A h <= A";
by (rtac Int_lower1 1);
qed "Part_subset";

goal Sum.thy "!!A B. A<=B ==> Part A h <= Part B h";
by (fast_tac (!claset addSIs [PartI] addSEs [PartE]) 1);
qed "Part_mono";

val basic_monos = basic_monos @ [Part_mono];

goalw Sum.thy [Part_def] "!!a. a : Part A h ==> a : A";
by (etac IntD1 1);
qed "PartD1";

goal Sum.thy "Part A (%x.x) = A";
by (fast_tac (!claset addIs [PartI] addSEs [PartE]) 1);
qed "Part_id";

goal Sum.thy "Part (A Int B) h = (Part A h) Int (Part B h)";
by (fast_tac (!claset addIs [PartI] addSEs [PartE]) 1);
qed "Part_Int";

(*For inductive definitions*)
goal Sum.thy "Part (A Int {x.P x}) h = (Part A h) Int {x.P x}";
by (fast_tac (!claset addIs [PartI] addSEs [PartE]) 1);
qed "Part_Collect";
