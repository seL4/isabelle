(*  Title:      HOL/Subst/UTerm.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Simple term structure for unifiation.
Binary trees with leaves that are constants or variables.
*)

open UTerm;

val uterm_con_defs = [VAR_def, CONST_def, COMB_def];

goal UTerm.thy "uterm(A) = A <+> A <+> (uterm(A) <*> uterm(A))";
let val rew = rewrite_rule uterm_con_defs in  
by (fast_tac (univ_cs addSIs (equalityI :: map rew uterm.intrs)
                      addEs [rew uterm.elim]) 1)
end;
qed "uterm_unfold";

(** the uterm functional **)

(*This justifies using uterm in other recursive type definitions*)
goalw UTerm.thy uterm.defs "!!A B. A<=B ==> uterm(A) <= uterm(B)";
by (REPEAT (ares_tac (lfp_mono::basic_monos) 1));
qed "uterm_mono";

(** Type checking rules -- uterm creates well-founded sets **)

goalw UTerm.thy (uterm_con_defs @ uterm.defs) "uterm(sexp) <= sexp";
by (rtac lfp_lowerbound 1);
by (fast_tac (univ_cs addIs sexp.intrs@[sexp_In0I,sexp_In1I]) 1);
qed "uterm_sexp";

(* A <= sexp ==> uterm(A) <= sexp *)
bind_thm ("uterm_subset_sexp", ([uterm_mono, uterm_sexp] MRS subset_trans));

(** Induction **)

(*Induction for the type 'a uterm *)
val prems = goalw UTerm.thy [Var_def,Const_def,Comb_def]
    "[| !!x.P(Var(x));  !!x.P(Const(x));  \
\       !!u v. [|  P(u);  P(v) |] ==> P(Comb u v) |]  ==> P(t)";
by (rtac (Rep_uterm_inverse RS subst) 1);   (*types force good instantiation*)
by (rtac (Rep_uterm RS uterm.induct) 1);
by (REPEAT (ares_tac prems 1
     ORELSE eresolve_tac [rangeE, ssubst, Abs_uterm_inverse RS subst] 1));
qed "uterm_induct";

(*Perform induction on xs. *)
fun uterm_ind_tac a M = 
    EVERY [res_inst_tac [("t",a)] uterm_induct M,
           rename_last_tac a ["1"] (M+1)];


(*** Isomorphisms ***)

goal UTerm.thy "inj(Rep_uterm)";
by (rtac inj_inverseI 1);
by (rtac Rep_uterm_inverse 1);
qed "inj_Rep_uterm";

goal UTerm.thy "inj_onto Abs_uterm (uterm (range Leaf))";
by (rtac inj_onto_inverseI 1);
by (etac Abs_uterm_inverse 1);
qed "inj_onto_Abs_uterm";

(** Distinctness of constructors **)

goalw UTerm.thy uterm_con_defs "~ CONST(c) = COMB u v";
by (rtac notI 1);
by (etac (In1_inject RS (In0_not_In1 RS notE)) 1);
qed "CONST_not_COMB";
bind_thm ("COMB_not_CONST", (CONST_not_COMB RS not_sym));
bind_thm ("CONST_neq_COMB", (CONST_not_COMB RS notE));
val COMB_neq_CONST = sym RS CONST_neq_COMB;

goalw UTerm.thy uterm_con_defs "~ COMB u v = VAR(x)";
by (rtac In1_not_In0 1);
qed "COMB_not_VAR";
bind_thm ("VAR_not_COMB", (COMB_not_VAR RS not_sym));
bind_thm ("COMB_neq_VAR", (COMB_not_VAR RS notE));
val VAR_neq_COMB = sym RS COMB_neq_VAR;

goalw UTerm.thy uterm_con_defs "~ VAR(x) = CONST(c)";
by (rtac In0_not_In1 1);
qed "VAR_not_CONST";
bind_thm ("CONST_not_VAR", (VAR_not_CONST RS not_sym));
bind_thm ("VAR_neq_CONST", (VAR_not_CONST RS notE));
val CONST_neq_VAR = sym RS VAR_neq_CONST;


goalw UTerm.thy [Const_def,Comb_def] "~ Const(c) = Comb u v";
by (rtac (CONST_not_COMB RS (inj_onto_Abs_uterm RS inj_onto_contraD)) 1);
by (REPEAT (resolve_tac (uterm.intrs @ [rangeI, Rep_uterm]) 1));
qed "Const_not_Comb";
bind_thm ("Comb_not_Const", (Const_not_Comb RS not_sym));
bind_thm ("Const_neq_Comb", (Const_not_Comb RS notE));
val Comb_neq_Const = sym RS Const_neq_Comb;

goalw UTerm.thy [Comb_def,Var_def] "~ Comb u v = Var(x)";
by (rtac (COMB_not_VAR RS (inj_onto_Abs_uterm RS inj_onto_contraD)) 1);
by (REPEAT (resolve_tac (uterm.intrs @ [rangeI, Rep_uterm]) 1));
qed "Comb_not_Var";
bind_thm ("Var_not_Comb", (Comb_not_Var RS not_sym));
bind_thm ("Comb_neq_Var", (Comb_not_Var RS notE));
val Var_neq_Comb = sym RS Comb_neq_Var;

goalw UTerm.thy [Var_def,Const_def] "~ Var(x) = Const(c)";
by (rtac (VAR_not_CONST RS (inj_onto_Abs_uterm RS inj_onto_contraD)) 1);
by (REPEAT (resolve_tac (uterm.intrs @ [rangeI, Rep_uterm]) 1));
qed "Var_not_Const";
bind_thm ("Const_not_Var", (Var_not_Const RS not_sym));
bind_thm ("Var_neq_Const", (Var_not_Const RS notE));
val Const_neq_Var = sym RS Var_neq_Const;


(** Injectiveness of CONST and Const **)

val inject_cs = HOL_cs addSEs [Scons_inject] 
                       addSDs [In0_inject,In1_inject];

goalw UTerm.thy [VAR_def] "(VAR(M)=VAR(N)) = (M=N)";
by (fast_tac inject_cs 1);
qed "VAR_VAR_eq";

goalw UTerm.thy [CONST_def] "(CONST(M)=CONST(N)) = (M=N)";
by (fast_tac inject_cs 1);
qed "CONST_CONST_eq";

goalw UTerm.thy [COMB_def] "(COMB K L = COMB M N) = (K=M & L=N)";
by (fast_tac inject_cs 1);
qed "COMB_COMB_eq";

bind_thm ("VAR_inject", (VAR_VAR_eq RS iffD1));
bind_thm ("CONST_inject", (CONST_CONST_eq RS iffD1));
bind_thm ("COMB_inject", (COMB_COMB_eq RS iffD1 RS conjE));


(*For reasoning about abstract uterm constructors*)
val uterm_cs = set_cs addIs uterm.intrs @ [Rep_uterm]
                      addSEs [CONST_neq_COMB,COMB_neq_VAR,VAR_neq_CONST,
                              COMB_neq_CONST,VAR_neq_COMB,CONST_neq_VAR,
                              COMB_inject]
                      addSDs [VAR_inject,CONST_inject,
                              inj_onto_Abs_uterm RS inj_ontoD,
                              inj_Rep_uterm RS injD, Leaf_inject];

goalw UTerm.thy [Var_def] "(Var(x)=Var(y)) = (x=y)";
by (fast_tac uterm_cs 1);
qed "Var_Var_eq";
bind_thm ("Var_inject", (Var_Var_eq RS iffD1));

goalw UTerm.thy [Const_def] "(Const(x)=Const(y)) = (x=y)";
by (fast_tac uterm_cs 1);
qed "Const_Const_eq";
bind_thm ("Const_inject", (Const_Const_eq RS iffD1));

goalw UTerm.thy [Comb_def] "(Comb u v =Comb x y) = (u=x & v=y)";
by (fast_tac uterm_cs 1);
qed "Comb_Comb_eq";
bind_thm ("Comb_inject", (Comb_Comb_eq RS iffD1 RS conjE));

val [major] = goal UTerm.thy "VAR(M): uterm(A) ==> M : A";
by (rtac (major RS setup_induction) 1);
by (etac uterm.induct 1);
by (ALLGOALS (fast_tac uterm_cs));
qed "VAR_D";

val [major] = goal UTerm.thy "CONST(M): uterm(A) ==> M : A";
by (rtac (major RS setup_induction) 1);
by (etac uterm.induct 1);
by (ALLGOALS (fast_tac uterm_cs));
qed "CONST_D";

val [major] = goal UTerm.thy
    "COMB M N: uterm(A) ==> M: uterm(A) & N: uterm(A)";
by (rtac (major RS setup_induction) 1);
by (etac uterm.induct 1);
by (ALLGOALS (fast_tac uterm_cs));
qed "COMB_D";

(*Basic ss with constructors and their freeness*)
Addsimps (uterm.intrs @
          [Const_not_Comb,Comb_not_Var,Var_not_Const,
           Comb_not_Const,Var_not_Comb,Const_not_Var,
           Var_Var_eq,Const_Const_eq,Comb_Comb_eq,
           CONST_not_COMB,COMB_not_VAR,VAR_not_CONST,
           COMB_not_CONST,VAR_not_COMB,CONST_not_VAR,
           VAR_VAR_eq,CONST_CONST_eq,COMB_COMB_eq]);

goal UTerm.thy "!u. t~=Comb t u";
by (uterm_ind_tac "t" 1);
by (rtac (Var_not_Comb RS allI) 1);
by (rtac (Const_not_Comb RS allI) 1);
by (Asm_simp_tac 1);
qed "t_not_Comb_t";

goal UTerm.thy "!t. u~=Comb t u";
by (uterm_ind_tac "u" 1);
by (rtac (Var_not_Comb RS allI) 1);
by (rtac (Const_not_Comb RS allI) 1);
by (Asm_simp_tac 1);
qed "u_not_Comb_u";


(*** UTerm_rec -- by wf recursion on pred_sexp ***)

val UTerm_rec_unfold =
    [UTerm_rec_def, wf_pred_sexp RS wf_trancl] MRS def_wfrec;

(** conversion rules **)

goalw UTerm.thy [VAR_def] "UTerm_rec (VAR x) b c d = b(x)";
by (rtac (UTerm_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [Case_In0]) 1);
qed "UTerm_rec_VAR";

goalw UTerm.thy [CONST_def] "UTerm_rec (CONST x) b c d = c(x)";
by (rtac (UTerm_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [Case_In0,Case_In1]) 1);
qed "UTerm_rec_CONST";

goalw UTerm.thy [COMB_def]
    "!!M N. [| M: sexp;  N: sexp |] ==>         \
\           UTerm_rec (COMB M N) b c d = \
\           d M N (UTerm_rec M b c d) (UTerm_rec N b c d)";
by (rtac (UTerm_rec_unfold RS trans) 1);
by (simp_tac (!simpset addsimps [Split,Case_In1]) 1);
by (asm_simp_tac (!simpset addsimps [In1_def]) 1);
qed "UTerm_rec_COMB";

(*** uterm_rec -- by UTerm_rec ***)

val Rep_uterm_in_sexp =
    Rep_uterm RS (range_Leaf_subset_sexp RS uterm_subset_sexp RS subsetD);

Addsimps [UTerm_rec_VAR, UTerm_rec_CONST, UTerm_rec_COMB, 
          Abs_uterm_inverse, Rep_uterm_inverse, 
          Rep_uterm, rangeI, inj_Leaf, Inv_f_f, Rep_uterm_in_sexp];

goalw UTerm.thy [uterm_rec_def, Var_def] "uterm_rec (Var x) b c d = b(x)";
by (Simp_tac 1);
qed "uterm_rec_Var";

goalw UTerm.thy [uterm_rec_def, Const_def] "uterm_rec (Const x) b c d = c(x)";
by (Simp_tac 1);
qed "uterm_rec_Const";

goalw UTerm.thy [uterm_rec_def, Comb_def]
  "uterm_rec (Comb u v) b c d = d u v (uterm_rec u b c d) (uterm_rec v b c d)";
by (Simp_tac 1);
qed "uterm_rec_Comb";

Addsimps [uterm_rec_Var, uterm_rec_Const, uterm_rec_Comb];


(**********)

val uterm_rews = [t_not_Comb_t,u_not_Comb_u];
