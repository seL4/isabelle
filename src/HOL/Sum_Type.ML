(*  Title:      HOL/Sum_Type.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The disjoint sum of two types
*)

(** Inl_Rep and Inr_Rep: Representations of the constructors **)

(*This counts as a non-emptiness result for admitting 'a+'b as a type*)
Goalw [Sum_def] "Inl_Rep(a) : Sum";
by (EVERY1 [rtac CollectI, rtac disjI1, rtac exI, rtac refl]);
qed "Inl_RepI";

Goalw [Sum_def] "Inr_Rep(b) : Sum";
by (EVERY1 [rtac CollectI, rtac disjI2, rtac exI, rtac refl]);
qed "Inr_RepI";

Goal "inj_on Abs_Sum Sum";
by (rtac inj_on_inverseI 1);
by (etac Abs_Sum_inverse 1);
qed "inj_on_Abs_Sum";

(** Distinctness of Inl and Inr **)

Goalw [Inl_Rep_def, Inr_Rep_def] "Inl_Rep(a) ~= Inr_Rep(b)";
by (EVERY1 [rtac notI,
            etac (fun_cong RS fun_cong RS fun_cong RS iffE), 
            rtac (notE RS ccontr),  etac (mp RS conjunct2), 
            REPEAT o (ares_tac [refl,conjI]) ]);
qed "Inl_Rep_not_Inr_Rep";

Goalw [Inl_def,Inr_def] "Inl(a) ~= Inr(b)";
by (rtac (inj_on_Abs_Sum RS inj_on_contraD) 1);
by (rtac Inl_Rep_not_Inr_Rep 1);
by (rtac Inl_RepI 1);
by (rtac Inr_RepI 1);
qed "Inl_not_Inr";

bind_thm ("Inr_not_Inl", Inl_not_Inr RS not_sym);

AddIffs [Inl_not_Inr, Inr_not_Inl];

bind_thm ("Inl_neq_Inr", Inl_not_Inr RS notE);
bind_thm ("Inr_neq_Inl", sym RS Inl_neq_Inr);


(** Injectiveness of Inl and Inr **)

Goalw [Inl_Rep_def] "Inl_Rep(a) = Inl_Rep(c) ==> a=c";
by (etac (fun_cong RS fun_cong RS fun_cong RS iffE) 1);
by (Blast_tac 1);
qed "Inl_Rep_inject";

Goalw [Inr_Rep_def] "Inr_Rep(b) = Inr_Rep(d) ==> b=d";
by (etac (fun_cong RS fun_cong RS fun_cong RS iffE) 1);
by (Blast_tac 1);
qed "Inr_Rep_inject";

Goalw [Inl_def] "inj(Inl)";
by (rtac injI 1);
by (etac (inj_on_Abs_Sum RS inj_onD RS Inl_Rep_inject) 1);
by (rtac Inl_RepI 1);
by (rtac Inl_RepI 1);
qed "inj_Inl";
bind_thm ("Inl_inject", inj_Inl RS injD);

Goalw [Inr_def] "inj(Inr)";
by (rtac injI 1);
by (etac (inj_on_Abs_Sum RS inj_onD RS Inr_Rep_inject) 1);
by (rtac Inr_RepI 1);
by (rtac Inr_RepI 1);
qed "inj_Inr";
bind_thm ("Inr_inject", inj_Inr RS injD);

Goal "(Inl(x)=Inl(y)) = (x=y)";
by (blast_tac (claset() addSDs [Inl_inject]) 1);
qed "Inl_eq";

Goal "(Inr(x)=Inr(y)) = (x=y)";
by (blast_tac (claset() addSDs [Inr_inject]) 1);
qed "Inr_eq";

AddIffs [Inl_eq, Inr_eq];

(*** Rules for the disjoint sum of two SETS ***)

(** Introduction rules for the injections **)

Goalw [sum_def] "a : A ==> Inl(a) : A <+> B";
by (Blast_tac 1);
qed "InlI";

Goalw [sum_def] "b : B ==> Inr(b) : A <+> B";
by (Blast_tac 1);
qed "InrI";

(** Elimination rules **)

val major::prems = Goalw [sum_def]
    "[| u: A <+> B;  \
\       !!x. [| x:A;  u=Inl(x) |] ==> P; \
\       !!y. [| y:B;  u=Inr(y) |] ==> P \
\    |] ==> P";
by (rtac (major RS UnE) 1);
by (REPEAT (rtac refl 1
     ORELSE eresolve_tac (prems@[imageE,ssubst]) 1));
qed "PlusE";


AddSIs [InlI, InrI]; 
AddSEs [PlusE];


(** Exhaustion rule for sums -- a degenerate form of induction **)

val prems = Goalw [Inl_def,Inr_def]
    "[| !!x::'a. s = Inl(x) ==> P;  !!y::'b. s = Inr(y) ==> P \
\    |] ==> P";
by (rtac (rewrite_rule [Sum_def] Rep_Sum RS CollectE) 1);
by (REPEAT (eresolve_tac [disjE,exE] 1
     ORELSE EVERY1 [resolve_tac prems, 
                    etac subst,
                    rtac (Rep_Sum_inverse RS sym)]));
qed "sumE";

val prems = Goal "[| !!x. P (Inl x); !!x. P (Inr x) |] ==> P x";
by (res_inst_tac [("s","x")] sumE 1);
by (ALLGOALS (hyp_subst_tac THEN' (resolve_tac prems)));
qed "sum_induct";


(** Rules for the Part primitive **)

Goalw [Part_def] "[| a : A;  a=h(b) |] ==> a : Part A h";
by (Blast_tac 1);
qed "Part_eqI";

bind_thm ("PartI", refl RSN (2,Part_eqI));

val major::prems = Goalw [Part_def]
    "[| a : Part A h;  !!z. [| a : A;  a=h(z) |] ==> P  \
\    |] ==> P";
by (rtac (major RS IntE) 1);
by (etac CollectE 1);
by (etac exE 1);
by (REPEAT (ares_tac prems 1));
qed "PartE";

AddIs  [Part_eqI];
AddSEs [PartE];

Goalw [Part_def] "Part A h <= A";
by (rtac Int_lower1 1);
qed "Part_subset";

Goal "A<=B ==> Part A h <= Part B h";
by (Blast_tac 1);
qed "Part_mono";

bind_thms ("basic_monos", basic_monos @ [Part_mono]);

Goalw [Part_def] "a : Part A h ==> a : A";
by (etac IntD1 1);
qed "PartD1";

Goal "Part A (%x. x) = A";
by (Blast_tac 1);
qed "Part_id";

Goal "Part (A Int B) h = (Part A h) Int (Part B h)";
by (Blast_tac 1);
qed "Part_Int";

Goal "Part (A Int {x. P x}) h = (Part A h) Int {x. P x}";
by (Blast_tac 1);
qed "Part_Collect";
