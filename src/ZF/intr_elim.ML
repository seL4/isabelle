(*  Title: 	ZF/intr_elim.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Introduction/elimination rule module -- for Inductive/Coinductive Definitions
*)

signature INDUCTIVE_ARG =	(** Description of a (co)inductive def **)
  sig
  val thy        : theory               (*new theory with inductive defs*)
  val monos      : thm list		(*monotonicity of each M operator*)
  val con_defs   : thm list		(*definitions of the constructors*)
  val type_intrs : thm list		(*type-checking intro rules*)
  val type_elims : thm list		(*type-checking elim rules*)
  end;

(*internal items*)
signature INDUCTIVE_I =
  sig
  val rec_tms    : term list		(*the recursive sets*)
  val dom_sum    : term			(*their common domain*)
  val intr_tms   : term list		(*terms for the introduction rules*)
  end;

signature INTR_ELIM =
  sig
  val thy        : theory               (*copy of input theory*)
  val defs	 : thm list		(*definitions made in thy*)
  val bnd_mono   : thm			(*monotonicity for the lfp definition*)
  val unfold     : thm			(*fixed-point equation*)
  val dom_subset : thm			(*inclusion of recursive set in dom*)
  val intrs      : thm list		(*introduction rules*)
  val elim       : thm			(*case analysis theorem*)
  val raw_induct : thm			(*raw induction rule from Fp.induct*)
  val mk_cases : thm list -> string -> thm	(*generates case theorems*)
  val rec_names  : string list		(*names of recursive sets*)
  val sumprod_free_SEs : thm list       (*destruct rules for Su and Pr*)
  end;

(*prove intr/elim rules for a fixedpoint definition*)
functor Intr_elim_Fun
    (structure Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end  
     and Fp: FP and Pr : PR and Su : SU) : INTR_ELIM =
struct
open Logic Inductive Ind_Syntax;

val rec_names = map (#1 o dest_Const o head_of) rec_tms;
val big_rec_name = space_implode "_" rec_names;

val _ = deny (big_rec_name  mem  map ! (stamps_of_thy thy))
             ("Definition " ^ big_rec_name ^ 
	      " would clash with the theory of the same name!");

(*fetch fp definitions from the theory*)
val big_rec_def::part_rec_defs = 
  map (get_def thy)
      (case rec_names of [_] => rec_names | _ => big_rec_name::rec_names);


val sign = sign_of thy;

(********)
val _ = writeln "  Proving monotonicity...";

val Const("==",_) $ _ $ (_ $ dom_sum $ fp_abs) =
    big_rec_def |> rep_thm |> #prop |> Logic.unvarify;

val bnd_mono = 
    prove_goalw_cterm [] 
      (cterm_of sign (mk_tprop (Fp.bnd_mono $ dom_sum $ fp_abs)))
      (fn _ =>
       [rtac (Collect_subset RS bnd_monoI) 1,
	REPEAT (ares_tac (basic_monos @ monos) 1)]);

val dom_subset = standard (big_rec_def RS Fp.subs);

val unfold = standard ([big_rec_def, bnd_mono] MRS Fp.Tarski);

(********)
val _ = writeln "  Proving the introduction rules...";

(*Mutual recursion?  Helps to derive subset rules for the individual sets.*)
val Part_trans =
    case rec_names of
         [_] => asm_rl
       | _   => standard (Part_subset RS subset_trans);

(*To type-check recursive occurrences of the inductive sets, possibly
  enclosed in some monotonic operator M.*)
val rec_typechecks = 
   [dom_subset] RL (asm_rl :: ([Part_trans] RL monos)) RL [subsetD];

(*Type-checking is hardest aspect of proof;
  disjIn selects the correct disjunct after unfolding*)
fun intro_tacsf disjIn prems = 
  [(*insert prems and underlying sets*)
   cut_facts_tac prems 1,
   DETERM (rtac (unfold RS ssubst) 1),
   REPEAT (resolve_tac [Part_eqI,CollectI] 1),
   (*Now 2-3 subgoals: typechecking, the disjunction, perhaps equality.*)
   rtac disjIn 2,
   (*Not ares_tac, since refl must be tried before any equality assumptions;
     backtracking may occur if the premises have extra variables!*)
   DEPTH_SOLVE_1 (resolve_tac [refl,exI,conjI] 2 ORELSE assume_tac 2),
   (*Now solve the equations like Tcons(a,f) = Inl(?b4)*)
   rewrite_goals_tac con_defs,
   REPEAT (rtac refl 2),
   (*Typechecking; this can fail*)
   REPEAT (FIRSTGOAL (        dresolve_tac rec_typechecks
		      ORELSE' eresolve_tac (asm_rl::PartE::SigmaE2::type_elims)
		      ORELSE' hyp_subst_tac)),
   DEPTH_SOLVE (swap_res_tac (SigmaI::type_intrs) 1)];

(*combines disjI1 and disjI2 to access the corresponding nested disjunct...*)
val mk_disj_rls = 
    let fun f rl = rl RS disjI1
	and g rl = rl RS disjI2
    in  accesses_bal(f, g, asm_rl)  end;

val intrs = map (uncurry (prove_goalw_cterm part_rec_defs))
            (map (cterm_of sign) intr_tms ~~ 
	     map intro_tacsf (mk_disj_rls(length intr_tms)));

(********)
val _ = writeln "  Proving the elimination rule...";

(*Includes rules for succ and Pair since they are common constructions*)
val elim_rls = [asm_rl, FalseE, succ_neq_0, sym RS succ_neq_0, 
		Pair_neq_0, sym RS Pair_neq_0, Pair_inject,
		make_elim succ_inject, 
		refl_thin, conjE, exE, disjE];

(*Standard sum/products for datatypes, variant ones for codatatypes;
  We always include Pair_inject above*)
val sumprod_free_SEs = 
    map (gen_make_elim [conjE,FalseE])
	([Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff] 
	 RL [iffD1]);

(*Breaks down logical connectives in the monotonic function*)
val basic_elim_tac =
    REPEAT (SOMEGOAL (eresolve_tac (elim_rls@sumprod_free_SEs)
	      ORELSE' bound_hyp_subst_tac))
    THEN prune_params_tac
        (*Mutual recursion: collapse references to Part(D,h)*)
    THEN fold_tac part_rec_defs;

val elim = rule_by_tactic basic_elim_tac (unfold RS equals_CollectD);

(*Applies freeness of the given constructors, which *must* be unfolded by
  the given defs.  Cannot simply use the local con_defs because con_defs=[] 
  for inference systems. *)
fun con_elim_tac defs =
    rewrite_goals_tac defs THEN basic_elim_tac THEN fold_tac defs;

(*String s should have the form t:Si where Si is an inductive set*)
fun mk_cases defs s = 
    rule_by_tactic (con_elim_tac defs)
      (assume_read thy s  RS  elim);

val defs = big_rec_def :: part_rec_defs;

val raw_induct = standard ([big_rec_def, bnd_mono] MRS Fp.induct);
end;

