(*  Title:      Subst/Unify
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Unification algorithm
*)

(*---------------------------------------------------------------------------
 * This file defines a nested unification algorithm, then proves that it 
 * terminates, then proves 2 correctness theorems: that when the algorithm
 * succeeds, it 1) returns an MGU; and 2) returns an idempotent substitution.
 * Although the proofs may seem long, they are actually quite direct, in that
 * the correctness and termination properties are not mingled as much as in 
 * previous proofs of this algorithm. 
 *
 * Our approach for nested recursive functions is as follows: 
 *
 *    0. Prove the wellfoundedness of the termination relation.
 *    1. Prove the non-nested termination conditions.
 *    2. Eliminate (0) and (1) from the recursion equations and the 
 *       induction theorem.
 *    3. Prove the nested termination conditions by using the induction 
 *       theorem from (2) and by using the recursion equations from (2). 
 *       These are constrained by the nested termination conditions, but 
 *       things work out magically (by wellfoundedness of the termination 
 *       relation).
 *    4. Eliminate the nested TCs from the results of (2).
 *    5. Prove further correctness properties using the results of (4).
 *
 * Deeper nestings require iteration of steps (3) and (4).
 *---------------------------------------------------------------------------*)

open Unify;



(*---------------------------------------------------------------------------
 * The non-nested TC plus the wellfoundedness of unifyRel.
 *---------------------------------------------------------------------------*)
Tfl.tgoalw Unify.thy [] unify.rules;
(* Wellfoundedness of unifyRel *)
by (simp_tac (!simpset addsimps [unifyRel_def, uterm_less_def,
				 wf_inv_image, wf_lex_prod, wf_finite_psubset,
				 wf_rel_prod, wf_measure]) 1);
(* TC *)
by (Step_tac 1);
by (simp_tac (!simpset addsimps [finite_psubset_def, finite_vars_of,
				 lex_prod_def, measure_def,
				 inv_image_def]) 1);
by (rtac (monotone_vars_of RS (subset_iff_psubset_eq RS iffD1) RS disjE) 1);
by (Blast_tac 1);
by (asm_simp_tac (!simpset addsimps [rprod_def, less_eq, less_add_Suc1]) 1);
qed "tc0";


(*---------------------------------------------------------------------------
 * Eliminate tc0 from the recursion equations and the induction theorem.
 *---------------------------------------------------------------------------*)
val [wfr,tc] = Prim.Rules.CONJUNCTS tc0;
val unifyRules0 = map (normalize_thm [fn th => wfr RS th, fn th => tc RS th]) 
                     unify.rules;

val unifyInduct0 = [wfr,tc] MRS unify.induct 
                  |> read_instantiate [("P","split Q")]
                  |> rewrite_rule [split RS eq_reflection]
                  |> standard;


(*---------------------------------------------------------------------------
 * Termination proof.
 *---------------------------------------------------------------------------*)

goalw Unify.thy [trans_def,inv_image_def]
    "!!r. trans r ==> trans (inv_image r f)";
by (Simp_tac 1);
by (Blast_tac 1);
qed "trans_inv_image";

goalw Unify.thy [finite_psubset_def, trans_def] "trans finite_psubset";
by (simp_tac (!simpset addsimps [psubset_def]) 1);
by (Blast_tac 1);
qed "trans_finite_psubset";

goalw Unify.thy [unifyRel_def,uterm_less_def,measure_def] "trans unifyRel";
by (REPEAT (resolve_tac [trans_inv_image,trans_lex_prod,conjI, 
			 trans_finite_psubset,
			 trans_rprod, trans_inv_image, trans_trancl] 1));
qed "trans_unifyRel";


(*---------------------------------------------------------------------------
 * The following lemma is used in the last step of the termination proof for 
 * the nested call in Unify.  Loosely, it says that unifyRel doesn't care
 * about term structure.
 *---------------------------------------------------------------------------*)
goalw Unify.thy [unifyRel_def,lex_prod_def, inv_image_def]
     "!!x. ((X,Y), (Comb A (Comb B C), Comb D (Comb E F))) : unifyRel  ==> \
    \      ((X,Y), (Comb (Comb A B) C, Comb (Comb D E) F)) : unifyRel";
by (asm_full_simp_tac (!simpset addsimps [uterm_less_def, measure_def, rprod_def,
                          less_eq, inv_image_def,add_assoc]) 1);
by (subgoal_tac "(vars_of A Un vars_of B Un vars_of C Un \
                \  (vars_of D Un vars_of E Un vars_of F)) = \
                \ (vars_of A Un (vars_of B Un vars_of C) Un \
                \  (vars_of D Un (vars_of E Un vars_of F)))" 1);
by (Blast_tac 2);
by (Asm_simp_tac 1);
qed "Rassoc";


(*---------------------------------------------------------------------------
 * This lemma proves the nested termination condition for the base cases 
 * 3, 4, and 6. 
 *---------------------------------------------------------------------------*)
goal Unify.thy
 "!!x. ~(Var x <: M) ==>        \
\   ((N1 <| [(x,M)], N2 <| [(x,M)]), (Comb M N1, Comb(Var x) N2)) : unifyRel \
\ & ((N1 <| [(x,M)], N2 <| [(x,M)]), (Comb(Var x) N1, Comb M N2)) : unifyRel";
by (case_tac "Var x = M" 1);
by (hyp_subst_tac 1);
by (Simp_tac 1);
by (case_tac "x: (vars_of N1 Un vars_of N2)" 1);
(*uterm_less case*)
by (asm_simp_tac
    (!simpset addsimps [less_eq, unifyRel_def, uterm_less_def,
			rprod_def, lex_prod_def,
			measure_def, inv_image_def]) 1);
by (Blast_tac 1);
(*finite_psubset case*)
by (simp_tac
    (!simpset addsimps [unifyRel_def, lex_prod_def,
			measure_def, inv_image_def]) 1);
by (simp_tac (!simpset addsimps [finite_psubset_def, finite_vars_of,
				 psubset_def, set_eq_subset]) 1);
by (Blast_tac 1);
(** LEVEL 9 **)
(*Final case, also finite_psubset*)
by (simp_tac
    (!simpset addsimps [finite_vars_of, unifyRel_def, finite_psubset_def,
			lex_prod_def, measure_def, inv_image_def]) 1);
by (cut_inst_tac [("s","[(x,M)]"), ("v", "x"), ("t","N2")] Var_elim 1);
by (cut_inst_tac [("s","[(x,M)]"), ("v", "x"), ("t","N1")] Var_elim 3);
by (ALLGOALS (asm_simp_tac(!simpset addsimps [srange_iff, vars_iff_occseq])));
by (REPEAT_FIRST (resolve_tac [conjI, disjI1, psubsetI]));
by (ALLGOALS (asm_full_simp_tac 
	      (!simpset addsimps [srange_iff, set_eq_subset]))); 
by (ALLGOALS
    (fast_tac (!claset addEs [Var_intro RS disjE]
	               addss (!simpset addsimps [srange_iff]))));
qed "var_elimR";


val Some{nchotomy = subst_nchotomy,...} = assoc(!datatypes,"subst");

(*---------------------------------------------------------------------------
 * Do a case analysis on something of type 'a subst. 
 *---------------------------------------------------------------------------*)

fun subst_case_tac t =
(cut_inst_tac [("x",t)] (subst_nchotomy RS spec) 1 
  THEN etac disjE 1 
  THEN rotate_tac ~1 1 
  THEN Asm_full_simp_tac 1 
  THEN etac exE 1
  THEN rotate_tac ~1 1 
  THEN Asm_full_simp_tac 1);


(*---------------------------------------------------------------------------
 * The nested TC. Proved by recursion induction.
 *---------------------------------------------------------------------------*)
val [tc1,tc2,tc3] = unify.tcs;
goalw_cterm [] (cterm_of (sign_of Unify.thy) (USyntax.mk_prop tc3));
(*---------------------------------------------------------------------------
 * The extracted TC needs the scope of its quantifiers adjusted, so our 
 * first step is to restrict the scopes of N1 and N2.
 *---------------------------------------------------------------------------*)
by (subgoal_tac "!M1 M2 theta.  \
 \   unify(M1, M2) = Subst theta --> \
 \   (!N1 N2. ((N1<|theta, N2<|theta), Comb M1 N1, Comb M2 N2) : unifyRel)" 1);
by (Blast_tac 1);
by (rtac allI 1); 
by (rtac allI 1);
(* Apply induction *)
by (res_inst_tac [("v","M1"),("v1.0","M2")] unifyInduct0 1);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps (var_elimR::unifyRules0)
			    setloop (split_tac [expand_if]))));
(*Const-Const case*)
by (simp_tac
    (!simpset addsimps [unifyRel_def, lex_prod_def, measure_def,
			inv_image_def, less_eq, uterm_less_def, rprod_def]) 1);
(** LEVEL 7 **)
(*Comb-Comb case*)
by (subst_case_tac "unify(M1a, M2a)");
by (rename_tac "theta" 1);
by (subst_case_tac "unify(N1 <| theta, N2 <| theta)");
by (rename_tac "sigma" 1);
by (REPEAT (rtac allI 1));
by (rename_tac "P Q" 1); 
by (rtac (trans_unifyRel RS transD) 1);
by (Blast_tac 1);
by (simp_tac (HOL_ss addsimps [subst_Comb RS sym]) 1);
by (subgoal_tac "((Comb N1 P <| theta, Comb N2 Q <| theta), \
                \ (Comb M1a (Comb N1 P), Comb M2a (Comb N2 Q))) :unifyRel" 1);
by (asm_simp_tac HOL_ss 2);
by (rtac Rassoc 1);
by (Blast_tac 1);
qed_spec_mp "unify_TC2";


(*---------------------------------------------------------------------------
 * Now for elimination of nested TC from unify.rules and induction. 
 *---------------------------------------------------------------------------*)

(*Desired rule, copied from the theory file.  Could it be made available?*)
goal Unify.thy 
  "unify(Comb M1 N1, Comb M2 N2) =      \
\      (case unify(M1,M2)               \
\        of Fail => Fail                \
\         | Subst theta => (case unify(N1 <| theta, N2 <| theta)        \
\                            of Fail => Fail    \
\                             | Subst sigma => Subst (theta <> sigma)))";
by (asm_simp_tac (!simpset addsimps unifyRules0) 1);
by (subst_case_tac "unify(M1, M2)");
by (asm_simp_tac (!simpset addsimps [unify_TC2]) 1);
qed "unifyCombComb";


val unifyRules = rev (unifyCombComb :: tl (rev unifyRules0));

Addsimps unifyRules;

val prems = goal Unify.thy 
"   [| !!m n. Q (Const m) (Const n);      \
\      !!m M N. Q (Const m) (Comb M N); !!m x. Q (Const m) (Var x);     \
\      !!x M. Q (Var x) M; !!M N x. Q (Comb M N) (Const x);     \
\      !!M N x. Q (Comb M N) (Var x);   \
\      !!M1 N1 M2 N2.   \
\         (! theta.     \
\             unify (M1, M2) = Subst theta -->  \
\             Q (N1 <| theta) (N2 <| theta)) & Q M1 M2   \
\         ==> Q (Comb M1 N1) (Comb M2 N2) |] ==> Q M1 M2";
by (res_inst_tac [("v","M1"),("v1.0","M2")] unifyInduct0 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps (unify_TC2::prems))));
qed "unifyInduct";



(*---------------------------------------------------------------------------
 * Correctness. Notice that idempotence is not needed to prove that the 
 * algorithm terminates and is not needed to prove the algorithm correct, 
 * if you are only interested in an MGU.  This is in contrast to the
 * approach of M&W, who used idempotence and MGU-ness in the termination proof.
 *---------------------------------------------------------------------------*)

goal Unify.thy "!theta. unify(P,Q) = Subst theta --> MGUnifier theta P Q";
by (res_inst_tac [("M1.0","P"),("M2.0","Q")] unifyInduct 1);
by (ALLGOALS (asm_simp_tac (!simpset setloop split_tac [expand_if])));
(*Const-Const case*)
by (simp_tac (!simpset addsimps [MGUnifier_def,Unifier_def]) 1);
(*Const-Var case*)
by (stac mgu_sym 1);
by (simp_tac (!simpset addsimps [MGUnifier_Var]) 1);
(*Var-M case*)
by (simp_tac (!simpset addsimps [MGUnifier_Var]) 1);
(*Comb-Var case*)
by (stac mgu_sym 1);
by (simp_tac (!simpset addsimps [MGUnifier_Var]) 1);
(*Comb-Comb case*)
by (safe_tac (!claset));
by (subst_case_tac "unify(M1, M2)");
by (subst_case_tac "unify(N1<|list, N2<|list)");
by (hyp_subst_tac 1);
by (asm_full_simp_tac (!simpset addsimps [MGUnifier_def, Unifier_def])1);
(** LEVEL 13 **)
by (safe_tac (!claset));
by (rename_tac "theta sigma gamma" 1);
by (rewrite_goals_tac [MoreGeneral_def]);
by (rotate_tac ~3 1);
by (eres_inst_tac [("x","gamma")] allE 1);
by (Asm_full_simp_tac 1);
by (etac exE 1);
by (rename_tac "delta" 1);
by (eres_inst_tac [("x","delta")] allE 1);
by (subgoal_tac "N1 <| theta <| delta = N2 <| theta <| delta" 1);
(*Proving the subgoal*)
by (full_simp_tac (!simpset addsimps [subst_eq_iff]) 2);
by (blast_tac (!claset addIs [trans,sym] delrules [impCE]) 2);
by (blast_tac (!claset addIs [subst_trans, subst_cong, 
			      comp_assoc RS subst_sym]) 1);
qed_spec_mp "unify_gives_MGU";


(*---------------------------------------------------------------------------
 * Unify returns idempotent substitutions, when it succeeds.
 *---------------------------------------------------------------------------*)
goal Unify.thy "!theta. unify(P,Q) = Subst theta --> Idem theta";
by (res_inst_tac [("M1.0","P"),("M2.0","Q")] unifyInduct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Var_Idem] 
			             setloop split_tac[expand_if])));
(*Comb-Comb case*)
by (safe_tac (!claset));
by (subst_case_tac "unify(M1, M2)");
by (subst_case_tac "unify(N1 <| list, N2 <| list)");
by (hyp_subst_tac 1);
by prune_params_tac;
by (rename_tac "theta sigma" 1);
(** LEVEL 8 **)
by (dtac unify_gives_MGU 1);
by (dtac unify_gives_MGU 1);
by (rewrite_tac [MGUnifier_def]);
by (safe_tac (!claset));
by (rtac Idem_comp 1);
by (atac 1);
by (atac 1);

by (eres_inst_tac [("x","q")] allE 1);
by (asm_full_simp_tac (!simpset addsimps [MoreGeneral_def]) 1);
by (safe_tac (!claset));
by (asm_full_simp_tac
    (!simpset addsimps [srange_iff, subst_eq_iff, Idem_def]) 1);
qed_spec_mp "unify_gives_Idem";

