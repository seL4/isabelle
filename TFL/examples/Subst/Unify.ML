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

(* This is just a wrapper for the definition mechanism. *)
local fun cread thy s = read_cterm (sign_of thy) (s, (TVar(("DUMMY",0),[])));
in
fun Rfunc thy R eqs =
   let val read = term_of o cread thy;
    in Tfl.Rfunction thy (read R) (read eqs)
    end
end;

(*---------------------------------------------------------------------------
 * The algorithm.
 *---------------------------------------------------------------------------*)
val {theory,induction,rules,tcs} =
Rfunc Unify.thy "R"
  "(Unify(Const m, Const n)  = (if (m=n) then Subst[] else Fail))    & \
\  (Unify(Const m, Comb M N) = Fail)                                 & \
\  (Unify(Const m, Var v)    = Subst[(v,Const m)])                   & \
\  (Unify(Var v, M) = (if (Var v <: M) then Fail else Subst[(v,M)])) & \
\  (Unify(Comb M N, Const x) = Fail)                                 & \
\  (Unify(Comb M N, Var v) = (if (Var v <: Comb M N) then Fail  \
\                             else Subst[(v,Comb M N)]))             & \
\  (Unify(Comb M1 N1, Comb M2 N2) =  \
\     (case Unify(M1,M2) \
\       of Fail => Fail \
\        | Subst theta => (case Unify(N1 <| theta, N2 <| theta) \
\                           of Fail => Fail \
\                             | Subst sigma => Subst (theta <> sigma))))";

open Unify;

(*---------------------------------------------------------------------------
 * A slightly augmented strip_tac. 
 *---------------------------------------------------------------------------*)
fun my_strip_tac i = 
   CHANGED (strip_tac i 
             THEN REPEAT ((etac exE ORELSE' etac conjE) i)
             THEN TRY (hyp_subst_tac i));

(*---------------------------------------------------------------------------
 * A slightly augmented fast_tac for sets. It handles the case where the 
 * top connective is "=".
 *---------------------------------------------------------------------------*)
fun my_fast_set_tac i = (TRY(rtac set_ext i) THEN fast_tac set_cs i);


(*---------------------------------------------------------------------------
 * Wellfoundedness of proper subset on finite sets.
 *---------------------------------------------------------------------------*)
goalw Unify.thy [R0_def] "wf(R0)";
by (rtac ((wf_subset RS mp) RS mp) 1);
by (rtac wf_measure 1);
by(simp_tac(!simpset addsimps[measure_def,inv_image_def,symmetric less_def])1);
by (my_strip_tac 1);
by (forward_tac[ssubset_card] 1);
by (fast_tac set_cs 1);
val wf_R0 = result();


(*---------------------------------------------------------------------------
 * Tactic for selecting and working on the first projection of R.
 *---------------------------------------------------------------------------*)
fun R0_tac thms i =
  (simp_tac (!simpset addsimps (thms@[R_def,lex_prod_def,
               measure_def,inv_image_def,point_to_prod_def])) i THEN
   REPEAT (rtac exI i) THEN
   REPEAT ((rtac conjI THEN' rtac refl) i) THEN
   rtac disjI1 i THEN
   simp_tac (!simpset addsimps [R0_def,finite_vars_of]) i);



(*---------------------------------------------------------------------------
 * Tactic for selecting and working on the second projection of R.
 *---------------------------------------------------------------------------*)
fun R1_tac thms i = 
   (simp_tac (!simpset addsimps (thms@[R_def,lex_prod_def,
                 measure_def,inv_image_def,point_to_prod_def])) i THEN 
    REPEAT (rtac exI i) THEN 
    REPEAT ((rtac conjI THEN' rtac refl) i) THEN
    rtac disjI2 i THEN
    asm_simp_tac (!simpset addsimps [R1_def,rprod_def]) i);


(*---------------------------------------------------------------------------
 * The non-nested TC plus the wellfoundedness of R.
 *---------------------------------------------------------------------------*)
Tfl.tgoalw Unify.thy [] rules;
by (rtac conjI 1);
(* TC *)
by (my_strip_tac 1);
by (cut_facts_tac [monotone_vars_of] 1); 
by (asm_full_simp_tac(!simpset addsimps [subseteq_iff_subset_eq]) 1);
by (etac disjE 1);
by (R0_tac[] 1);
by (R1_tac[] 1);
by (simp_tac
     (!simpset addsimps [measure_def,inv_image_def,less_eq,less_add_Suc1]) 1);

(* Wellfoundedness of R *)
by (simp_tac (!simpset addsimps [Unify.R_def,Unify.R1_def]) 1);
by (REPEAT (resolve_tac [wf_inv_image,wf_lex_prod,wf_R0,
                         wf_rel_prod, wf_measure] 1));
val tc0 = result();


(*---------------------------------------------------------------------------
 * Eliminate tc0 from the recursion equations and the induction theorem.
 *---------------------------------------------------------------------------*)
val [tc,wfr] = Prim.Rules.CONJUNCTS tc0;
val rules1 = implies_intr_hyps rules;
val rules2 = wfr RS rules1;

val [a,b,c,d,e,f,g] = Prim.Rules.CONJUNCTS rules2;
val g' = tc RS (g RS mp);
val rules4 = standard (Prim.Rules.LIST_CONJ[a,b,c,d,e,f,g']);

val induction1 = implies_intr_hyps induction;
val induction2 = wfr RS induction1;
val induction3 = tc RS induction2;

val induction4 = standard
 (rewrite_rule[fst_conv RS eq_reflection, snd_conv RS eq_reflection]
   (induction3 RS (read_instantiate_sg (sign_of theory)
      [("x","%p. Phi (fst p) (snd p)")] spec)));


(*---------------------------------------------------------------------------
 * Some theorems about transitivity of WF combinators. Only the last
 * (transR) is used, in the proof of termination. The others are generic and
 * should maybe go somewhere.
 *---------------------------------------------------------------------------*)
goalw WF1.thy [trans_def,lex_prod_def,mem_Collect_eq RS eq_reflection]
           "trans R1 & trans R2 --> trans (R1 ** R2)";
by (my_strip_tac 1);
by (res_inst_tac [("x","a")] exI 1);
by (res_inst_tac [("x","a'a")] exI 1);
by (res_inst_tac [("x","b")] exI 1);
by (res_inst_tac [("x","b'a")] exI 1);
by (REPEAT (rewrite_tac [Pair_eq RS eq_reflection] THEN my_strip_tac 1));
by (Simp_tac 1);
by (REPEAT (etac disjE 1));
by (rtac disjI1 1);
by (ALLGOALS (fast_tac set_cs));
val trans_lex_prod = result() RS mp;


goalw WF1.thy [trans_def,rprod_def,mem_Collect_eq RS eq_reflection]
           "trans R1 & trans R2 --> trans (rprod R1  R2)";
by (my_strip_tac 1);
by (res_inst_tac [("x","a")] exI 1);
by (res_inst_tac [("x","a'a")] exI 1);
by (res_inst_tac [("x","b")] exI 1);
by (res_inst_tac [("x","b'a")] exI 1);
by (REPEAT (rewrite_tac [Pair_eq RS eq_reflection] THEN my_strip_tac 1));
by (Simp_tac 1);
by (fast_tac set_cs 1);
val trans_rprod = result() RS mp;


goalw Unify.thy [trans_def,inv_image_def,mem_Collect_eq RS eq_reflection]
 "trans r --> trans (inv_image r f)";
by (rewrite_tac [fst_conv RS eq_reflection, snd_conv RS eq_reflection]);
by (fast_tac set_cs 1);
val trans_inv_image = result() RS mp;

goalw Unify.thy [R0_def, trans_def, mem_Collect_eq RS eq_reflection]
 "trans R0";
by (rewrite_tac [fst_conv RS eq_reflection,snd_conv RS eq_reflection,
                 ssubset_def, set_eq_subset RS eq_reflection]);
by (fast_tac set_cs 1);
val trans_R0 = result();

goalw Unify.thy [R_def,R1_def,measure_def] "trans R";
by (REPEAT (resolve_tac[trans_inv_image,trans_lex_prod,conjI, trans_R0,
                        trans_rprod, trans_inv_image, trans_trancl] 1));
val transR = result();


(*---------------------------------------------------------------------------
 * The following lemma is used in the last step of the termination proof for 
 * the nested call in Unify. Loosely, it says that R doesn't care so much
 * about term structure.
 *---------------------------------------------------------------------------*)
goalw Unify.thy [R_def,lex_prod_def, inv_image_def,point_to_prod_def]
     "((X,Y), (Comb A (Comb B C), Comb D (Comb E F))) : R --> \
    \ ((X,Y), (Comb (Comb A B) C, Comb (Comb D E) F)) : R";
by (Simp_tac 1);
by (rtac conjI 1);
by (strip_tac 1);
by (rtac disjI1 1);
by (subgoal_tac "(vars_of A Un vars_of B Un vars_of C Un \
                \  (vars_of D Un vars_of E Un vars_of F)) = \
                \ (vars_of A Un (vars_of B Un vars_of C) Un \
                \  (vars_of D Un (vars_of E Un vars_of F)))" 1);
by (my_fast_set_tac 2);
by (Asm_simp_tac 1);
by (strip_tac 1);
by (rtac disjI2 1);
by (etac conjE 1);
by (Asm_simp_tac 1);
by (rtac conjI 1);
by (my_fast_set_tac 1);
by (asm_full_simp_tac (!simpset addsimps [R1_def, measure_def, rprod_def,
                          less_eq, inv_image_def,add_assoc]) 1);
val Rassoc = result() RS mp;

(*---------------------------------------------------------------------------
 * Rewriting support.
 *---------------------------------------------------------------------------*)

val termin_ss = (!simpset addsimps (srange_iff::(subst_rews@al_rews)));


(*---------------------------------------------------------------------------
 * This lemma proves the nested termination condition for the base cases 
 * 3, 4, and 6. It's a clumsy formulation (requiring two conjuncts, each with
 * exactly the same proof) of a more general theorem.
 *---------------------------------------------------------------------------*)
goal theory "(~(Var x <: M)) --> [(x, M)] = theta -->       \
\ (! N1 N2. (((N1 <| theta, N2 <| theta), (Comb M N1, Comb (Var x) N2)) : R) \
\       &   (((N1 <| theta, N2 <| theta), (Comb(Var x) N1, Comb M N2)) : R))";
by (my_strip_tac 1);
by (case_tac "Var x = M" 1);
by (hyp_subst_tac 1);
by (case_tac "x:(vars_of N1 Un vars_of N2)" 1);
let val case1 = 
   EVERY1[R1_tac[id_subst_lemma], rtac conjI, my_fast_set_tac,
          REPEAT o (rtac exI), REPEAT o (rtac conjI THEN' rtac refl),
          simp_tac (!simpset addsimps [measure_def,inv_image_def,less_eq])];
in by (rtac conjI 1);
   by case1;
   by case1
end;

let val case2 = 
   EVERY1[R0_tac[id_subst_lemma],
          simp_tac (!simpset addsimps [ssubset_def,set_eq_subset]),
          fast_tac set_cs]
in by (rtac conjI 1);
   by case2;
   by case2
end;

let val case3 =  
 EVERY1 [R0_tac[],
        cut_inst_tac [("s2","[(x, M)]"), ("v2", "x"), ("t2","N1")] Var_elim] 
 THEN ALLGOALS(asm_simp_tac(termin_ss addsimps [vars_iff_occseq]))
 THEN cut_inst_tac [("s2","[(x, M)]"),("v2", "x"), ("t2","N2")] Var_elim 1
 THEN ALLGOALS(asm_simp_tac(termin_ss addsimps [vars_iff_occseq]))
 THEN EVERY1 [simp_tac (HOL_ss addsimps [ssubset_def]),
             rtac conjI, simp_tac (HOL_ss addsimps [subset_iff]),
             my_strip_tac, etac UnE, dtac Var_intro] 
 THEN dtac Var_intro 2
 THEN ALLGOALS (asm_full_simp_tac (termin_ss addsimps [set_eq_subset])) 
 THEN TRYALL (fast_tac set_cs)
in 
  by (rtac conjI 1);
  by case3;
  by case3
end;
val var_elimR = result() RS mp RS mp RS spec RS spec;


val Some{nchotomy = subst_nchotomy,...} = assoc(!datatypes,"subst");

(*---------------------------------------------------------------------------
 * Do a case analysis on something of type 'a subst. 
 *---------------------------------------------------------------------------*)

fun Subst_case_tac theta =
(cut_inst_tac theta (standard (Prim.Rules.SPEC_ALL subst_nchotomy)) 1 
  THEN etac disjE 1 
  THEN rotate_tac ~1 1 
  THEN Asm_full_simp_tac 1 
  THEN etac exE 1
  THEN rotate_tac ~1 1 
  THEN Asm_full_simp_tac 1);


goals_limit := 1;

(*---------------------------------------------------------------------------
 * The nested TC. Proved by recursion induction.
 *---------------------------------------------------------------------------*)
goalw_cterm [] 
     (hd(tl(tl(map (cterm_of (sign_of theory) o USyntax.mk_prop) tcs))));
(*---------------------------------------------------------------------------
 * The extracted TC needs the scope of its quantifiers adjusted, so our 
 * first step is to restrict the scopes of N1 and N2.
 *---------------------------------------------------------------------------*)
by (subgoal_tac "!M1 M2 theta.  \
 \     Unify (M1, M2) = Subst theta --> \
 \    (!N1 N2. ((N1 <| theta, N2 <| theta), Comb M1 N1, Comb M2 N2) : R)" 1);
by (fast_tac HOL_cs 1);
by (rtac allI 1); 
by (rtac allI 1);
(* Apply induction *)
by (res_inst_tac [("xa","M1"),("x","M2")] 
                 (standard (induction4 RS mp RS spec RS spec)) 1);
by (simp_tac (!simpset addsimps (rules4::(subst_rews@al_rews))
                       setloop (split_tac [expand_if])) 1);
(* 1 *)
by (rtac conjI 1);
by (my_strip_tac 1);
by (R1_tac[subst_Nil] 1);
by (REPEAT (rtac exI 1) THEN REPEAT ((rtac conjI THEN' rtac refl) 1));
by (simp_tac (!simpset addsimps [measure_def,inv_image_def,less_eq]) 1);

(* 3 *)
by (rtac conjI 1);
by (my_strip_tac 1);
by (rtac (Prim.Rules.CONJUNCT1 var_elimR) 1);
by (Simp_tac 1);
by (rtac refl 1);

(* 4 *)
by (rtac conjI 1);
by (strip_tac 1);
by (rtac (Prim.Rules.CONJUNCT2 var_elimR) 1);
by (assume_tac 1);
by (rtac refl 1);

(* 6 *)
by (rtac conjI 1);
by (rewrite_tac [symmetric (occs_Comb RS eq_reflection)]);
by (my_strip_tac 1);
by (rtac (Prim.Rules.CONJUNCT1 var_elimR) 1);
by (Asm_simp_tac 1);
by (rtac refl 1);

(* 7 *)
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (etac conjE 1);
by (Subst_case_tac [("v","Unify(M1, M2)")]);
by (rename_tac "theta" 1);

by (Subst_case_tac [("v","Unify(N1 <| theta, N2 <| theta)")]);
by (rename_tac "sigma" 1);
by (REPEAT (rtac allI 1));
by (rename_tac "P Q" 1); 
by (simp_tac (HOL_ss addsimps [subst_comp]) 1);
by(rtac(rewrite_rule[trans_def] transR RS spec RS spec RS spec RS mp RS mp) 1);
by (fast_tac HOL_cs 1);
by (simp_tac (HOL_ss addsimps [symmetric (subst_Comb RS eq_reflection)]) 1);
by (subgoal_tac "((Comb N1 P <| theta, Comb N2 Q <| theta), \
                \ (Comb M1 (Comb N1 P), Comb M2 (Comb N2 Q))) :R" 1);
by (asm_simp_tac HOL_ss 2);

by (rtac Rassoc 1);
by (assume_tac 1);
val Unify_TC2 = result();


(*---------------------------------------------------------------------------
 * Now for elimination of nested TC from rules and induction. This step 
 * would be easier if "rewrite_rule" used context.
 *---------------------------------------------------------------------------*)
goal theory 
 "(Unify (Comb M1 N1, Comb M2 N2) =  \
\   (case Unify (M1, M2) of Fail => Fail \
\    | Subst theta => \
\        (case if ((N1 <| theta, N2 <| theta), Comb M1 N1, Comb M2 N2) : R \
\              then Unify (N1 <| theta, N2 <| theta) else @ z. True of \
\        Fail => Fail | Subst sigma => Subst (theta <> sigma)))) \
\  = \
\ (Unify (Comb M1 N1, Comb M2 N2) = \
\   (case Unify (M1, M2)  \
\      of Fail => Fail \
\      | Subst theta => (case Unify (N1 <| theta, N2 <| theta) \
\                          of Fail => Fail  \
\                           | Subst sigma => Subst (theta <> sigma))))";
by (cut_inst_tac [("v","Unify(M1, M2)")]
                 (standard (Prim.Rules.SPEC_ALL subst_nchotomy)) 1);
by (etac disjE 1);
by (Asm_simp_tac 1);
by (etac exE 1);
by (Asm_simp_tac 1);
by (cut_inst_tac 
     [("x","list"), ("xb","N1"), ("xa","N2"),("xc","M2"), ("xd","M1")]
     (standard(Unify_TC2 RS spec RS spec RS spec RS spec RS spec)) 1);
by (Asm_full_simp_tac 1);
val Unify_rec_simpl = result() RS eq_reflection;

val Unify_rules = rewrite_rule[Unify_rec_simpl] rules4;


goal theory 
 "(! M1 N1 M2 N2.  \
\       (! theta.  \
\           Unify (M1, M2) = Subst theta -->  \
\           ((N1 <| theta, N2 <| theta), Comb M1 N1, Comb M2 N2) : R -->  \
\           ?Phi (N1 <| theta) (N2 <| theta)) & ?Phi M1 M2 -->  \
\       ?Phi (Comb M1 N1) (Comb M2 N2))  \
\    =  \
\ (! M1 N1 M2 N2.  \
\       (! theta.  \
\           Unify (M1, M2) = Subst theta -->  \
\           ?Phi (N1 <| theta) (N2 <| theta)) & ?Phi M1 M2 -->  \
\       ?Phi (Comb M1 N1) (Comb M2 N2))";
by (simp_tac (HOL_ss addsimps [Unify_TC2]) 1);
val Unify_induction = rewrite_rule[result() RS eq_reflection] induction4;



(*---------------------------------------------------------------------------
 * Correctness. Notice that idempotence is not needed to prove that the 
 * algorithm terminates and is not needed to prove the algorithm correct, 
 * if you are only interested in an MGU. This is in contrast to the
 * approach of M&W, who used idempotence and MGU-ness in the termination proof.
 *---------------------------------------------------------------------------*)

goal theory "!theta. Unify (P,Q) = Subst theta --> MGUnifier theta P Q";
by (res_inst_tac [("xa","P"),("x","Q")] 
                 (standard (Unify_induction RS mp RS spec RS spec)) 1);
by (simp_tac (!simpset addsimps [Unify_rules] 
                       setloop (split_tac [expand_if])) 1);
(*1*)
by (rtac conjI 1);
by (REPEAT (rtac allI 1));
by (simp_tac (!simpset addsimps [MGUnifier_def,Unifier_def]) 1);
by (my_strip_tac 1);
by (rtac MoreGen_Nil 1);

(*3*)
by (rtac conjI 1);
by (my_strip_tac 1);
by (rtac (mgu_sym RS iffD1) 1);
by (rtac MGUnifier_Var 1);
by (Simp_tac 1);

(*4*)
by (rtac conjI 1);
by (my_strip_tac 1);
by (rtac MGUnifier_Var 1);
by (assume_tac 1);

(*6*)
by (rtac conjI 1);
by (rewrite_tac NNF_rews);
by (my_strip_tac 1);
by (rtac (mgu_sym RS iffD1) 1);
by (rtac MGUnifier_Var 1);
by (Asm_simp_tac 1);

(*7*) 
by (safe_tac HOL_cs);
by (Subst_case_tac [("v","Unify(M1, M2)")]);
by (Subst_case_tac [("v","Unify(N1 <| list, N2 <| list)")]);
by (hyp_subst_tac 1);
by (asm_full_simp_tac(HOL_ss addsimps [MGUnifier_def,Unifier_def])1);
by (asm_simp_tac (!simpset addsimps [subst_comp]) 1); (* It's a unifier.*)

by (safe_tac HOL_cs);
by (rename_tac "theta sigma gamma" 1);

by (rewrite_tac [MoreGeneral_def]);
by (rotate_tac ~3 1);
by (eres_inst_tac [("x","gamma")] allE 1);
by (Asm_full_simp_tac 1);
by (etac exE 1);
by (rename_tac "delta" 1);
by (eres_inst_tac [("x","delta")] allE 1);
by (subgoal_tac "N1 <| theta <| delta = N2 <| theta <| delta" 1);
by (dtac mp 1);
by (atac 1);
by (etac exE 1);
by (rename_tac "rho" 1);

by (rtac exI 1);
by (rtac subst_trans 1);
by (assume_tac 1);

by (rtac subst_trans 1);
by (rtac (comp_assoc RS subst_sym) 2);
by (rtac subst_cong 1);
by (rtac (refl RS subst_refl) 1);
by (assume_tac 1);

by (asm_full_simp_tac (!simpset addsimps [subst_eq_iff,subst_comp]) 1);
by (forw_inst_tac [("x","N1")] spec 1);
by (dres_inst_tac [("x","N2")] spec 1);
by (Asm_full_simp_tac 1);
val Unify_gives_MGU = standard(result() RS spec RS mp);


(*---------------------------------------------------------------------------
 * Unify returns idempotent substitutions, when it succeeds.
 *---------------------------------------------------------------------------*)
goal theory "!theta. Unify (P,Q) = Subst theta --> Idem theta";
by (res_inst_tac [("xa","P"),("x","Q")] 
                 (standard (Unify_induction RS mp RS spec RS spec)) 1);
(* Blows away all base cases automatically *)
by (simp_tac (!simpset addsimps [Unify_rules,Idem_Nil,Var_Idem] 
                       setloop (split_tac [expand_if])) 1);

(*7*)
by (safe_tac HOL_cs);
by (Subst_case_tac [("v","Unify(M1, M2)")]);
by (Subst_case_tac [("v","Unify(N1 <| list, N2 <| list)")]);
by (hyp_subst_tac 1);
by prune_params_tac;
by (rename_tac "theta sigma" 1);

by (dtac Unify_gives_MGU 1);
by (dtac Unify_gives_MGU 1);
by (rewrite_tac [MGUnifier_def]);
by (my_strip_tac 1);
by (rtac Idem_comp 1);
by (atac 1);
by (atac 1);

by (my_strip_tac 1);
by (eres_inst_tac [("x","q")] allE 1);
by (Asm_full_simp_tac 1);
by (rewrite_tac [MoreGeneral_def]);
by (my_strip_tac 1);
by (asm_full_simp_tac(termin_ss addsimps [subst_eq_iff,subst_comp,Idem_def])1);
val Unify_gives_Idem = result() RS spec RS mp;



(*---------------------------------------------------------------------------
 * Exercise. The given algorithm is a bit inelegant. What about the
 * following "improvement", which adds a few recursive calls in former
 * base cases? It seems that the termination relation needs another
 * case in the lexico. product.

val {theory,induction,rules,tcs,typechecks} =
Rfunc Unify.thy ??
  `(Unify(Const m, Const n)  = (if (m=n) then Subst[] else Fail))    &
   (Unify(Const m, Comb M N) = Fail)                                 &
   (Unify(Const m, Var v)    = Unify(Var v, Const m))                &
   (Unify(Var v, M) = (if (Var v <: M) then Fail else Subst[(v,M)])) &
   (Unify(Comb M N, Const x) = Fail)                                 &
   (Unify(Comb M N, Var v) = Unify(Var v, Comb M N))                 &
   (Unify(Comb M1 N1, Comb M2 N2) = 
      (case Unify(M1,M2)
        of Fail => Fail
         | Subst theta => (case Unify(N1 <| theta, N2 <| theta)
                            of Fail => Fail
                             | Subst sigma => Subst (theta <> sigma))))`;

 *---------------------------------------------------------------------------*)
