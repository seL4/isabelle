(*  Title:      Residuals.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

(* ------------------------------------------------------------------------- *)
(*       Setting up rule lists                                               *)
(* ------------------------------------------------------------------------- *)

AddIs (Sres.intrs @ redexes.intrs @ Sreg.intrs @ [subst_type]); 
AddSEs (map Sres.mk_cases
	     ["residuals(Var(n),Var(n),v)",
	      "residuals(Fun(t),Fun(u),v)",
	      "residuals(App(b, u1, u2), App(0, v1, v2),v)",
	      "residuals(App(b, u1, u2), App(1, Fun(v1), v2),v)",
	      "residuals(Var(n),u,v)",
	      "residuals(Fun(t),u,v)",
	      "residuals(App(b, u1, u2), w,v)",
	      "residuals(u,Var(n),v)",
	      "residuals(u,Fun(t),v)",
	      "residuals(w,App(b, u1, u2),v)"]);

AddSEs (map Ssub.mk_cases
	     ["Var(n) <== u",
	      "Fun(n) <== u",
	      "u <== Fun(n)",
	      "App(1,Fun(t),a) <== u",
	      "App(0,t,a) <== u"]);

AddSEs [redexes.mk_cases "Fun(t):redexes"];

Addsimps Sres.intrs;
val resD1 = Sres.dom_subset RS subsetD RS SigmaD1;
val resD2 = Sres.dom_subset RS subsetD RS SigmaD2 RS SigmaD1;
val resD3 = Sres.dom_subset RS subsetD RS SigmaD2 RS SigmaD2;


(* ------------------------------------------------------------------------- *)
(*       residuals is a  partial function                                    *)
(* ------------------------------------------------------------------------- *)

Goal "residuals(u,v,w) ==> ALL w1. residuals(u,v,w1) --> w1 = w";
by (etac Sres.induct 1);
by (ALLGOALS Force_tac);
qed_spec_mp "residuals_function";

Goal "u~v ==> regular(v) --> (EX w. residuals(u,v,w))";
by (etac Scomp.induct 1);
by (ALLGOALS Fast_tac);
qed "residuals_intro";

Goal "[| u~v;  regular(v) |] ==> residuals(u,v,THE w. residuals(u, v, w))";
by (resolve_tac [residuals_intro RS mp RS exE] 1);
by (stac the_equality 3);
by (ALLGOALS (blast_tac (claset() addIs [residuals_function])));
qed "comp_resfuncD";


(* ------------------------------------------------------------------------- *)
(*               Residual function                                           *)
(* ------------------------------------------------------------------------- *)

Goalw [res_func_def] "n:nat ==> Var(n) |> Var(n) = Var(n)";
by (Blast_tac 1);
qed "res_Var";

Goalw [res_func_def]
    "[|s~t; regular(t)|]==> Fun(s) |> Fun(t) = Fun(s |> t)";
by (blast_tac (claset() addSDs [comp_resfuncD]
			addIs [residuals_function]) 1);
qed "res_Fun";

Goalw [res_func_def]
    "[|s~u; regular(u); t~v; regular(v); b:bool|]==> \
\           App(b,s,t) |> App(0,u,v) = App(b, s |> u, t |> v)";
by (blast_tac (claset() addSDs [comp_resfuncD]
			addIs [residuals_function]) 1);
qed "res_App";

Goalw [res_func_def]
    "[|s~u; regular(u); t~v; regular(v); b:bool|]==> \
\           App(b,Fun(s),t) |> App(1,Fun(u),v) = (t |> v)/ (s |> u)";
by (blast_tac (claset() addSEs redexes.free_SEs
			addSDs [comp_resfuncD]
			addIs [residuals_function]) 1);
qed "res_redex";

Goal "[|s~t; regular(t)|]==> regular(t) --> s |> t:redexes";
by (etac Scomp.induct 1);
by (auto_tac (claset(),
	      simpset() addsimps [res_Var,res_Fun,res_App,res_redex]));
by (dres_inst_tac [("psi", "Fun(?u) |> ?v : redexes")] asm_rl 1);
by (auto_tac (claset(),
	      simpset() addsimps [res_Fun]));
qed "resfunc_type";

Addsimps [res_Var, res_Fun, res_App, res_redex, lift_rec_preserve_comp,
	  lift_rec_preserve_reg, subst_rec_preserve_comp, resfunc_type,
	  subst_rec_preserve_reg];


(* ------------------------------------------------------------------------- *)
(*     Commutation theorem                                                   *)
(* ------------------------------------------------------------------------- *)

Goal "u<==v ==> u~v";
by (etac Ssub.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "sub_comp";

Goal "u<==v  ==> regular(v) --> regular(u)";
by (etac Ssub.induct 1);
by Auto_tac;
qed_spec_mp "sub_preserve_reg";

Goal "[|u~v; k:nat|]==> regular(v)--> (ALL n:nat.  \
\        lift_rec(u,n) |> lift_rec(v,n) = lift_rec(u |> v,n))";
by (etac Scomp.induct 1);
by Safe_tac;
by (ALLGOALS
    (asm_full_simp_tac
     (simpset() addsimps [lift_rec_Var,subst_Var,lift_subst])));
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1);
qed "residuals_lift_rec";

Goal "u1~u2 ==>  ALL v1 v2. v1~v2 --> regular(v2) --> regular(u2) -->\
\   (ALL n:nat. subst_rec(v1,u1,n) |> subst_rec(v2,u2,n) = \
\              subst_rec(v1 |> v2, u1 |> u2,n))";
by (etac Scomp.induct 1);
by Safe_tac;
by (ALLGOALS
    (asm_simp_tac
     (simpset() addsimps [lift_rec_Var,subst_Var,residuals_lift_rec])));
by (dres_inst_tac [("psi", "ALL x.?P(x)")] asm_rl 1);
by (asm_full_simp_tac (simpset() addsimps [substitution]) 1);
qed "residuals_subst_rec";


Goal "[|u1~u2; v1~v2; regular(u2); regular(v2)|]==>\
\       (v1/u1) |> (v2/u2) = (v1 |> v2)/(u1 |> u2)";
by (asm_simp_tac (simpset() addsimps [residuals_subst_rec]) 1);
qed "commutation";

(* ------------------------------------------------------------------------- *)
(*     Residuals are comp and regular                                        *)
(* ------------------------------------------------------------------------- *)

Goal "u~v ==> ALL w. u~w --> v~w --> regular(w) --> (u|>w) ~ (v|>w)";
by (etac Scomp.induct 1);
by (ALLGOALS Force_tac);
qed_spec_mp "residuals_preserve_comp";


Goal "u~v ==> regular(u) --> regular(v) --> regular(u|>v)";
by (etac Scomp.induct 1);
by Safe_tac;
by (TRYALL (dres_inst_tac [("psi", "regular(Fun(?u) |> ?v)")] asm_rl));
by Auto_tac;
qed_spec_mp "residuals_preserve_reg";

(* ------------------------------------------------------------------------- *)
(*     Preservation lemma                                                    *)
(* ------------------------------------------------------------------------- *)

Goal "u~v ==> v ~ (u un v)";
by (etac Scomp.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "union_preserve_comp";

Goal "u ~ v ==> regular(v) --> u|>v = (u un v)|>v";
by (etac Scomp.induct 1);
by Safe_tac;
by (dres_inst_tac [("psi", "Fun(?u) |> ?v = ?w")] asm_rl 3);
by (auto_tac (claset(), 
	      simpset() addsimps [union_preserve_comp,comp_sym_iff]));
by (asm_full_simp_tac (simpset() addsimps 
                       [union_preserve_comp RS comp_sym,
                        comp_sym RS union_preserve_comp RS comp_sym]) 1);
qed_spec_mp "preservation";
