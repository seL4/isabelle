(*  Title:      HOL/intr_elim.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Introduction/elimination rule module -- for Inductive/Coinductive Definitions
*)

signature INDUCTIVE_ARG =       (** Description of a (co)inductive def **)
  sig
  val thy        : theory               (*new theory with inductive defs*)
  val monos      : thm list             (*monotonicity of each M operator*)
  val con_defs   : thm list             (*definitions of the constructors*)
  end;


signature INDUCTIVE_I = (** Terms read from the theory section **)
  sig
  val rec_tms    : term list            (*the recursive sets*)
  val intr_tms   : term list            (*terms for the introduction rules*)
  end;

signature INTR_ELIM =
  sig
  val thy        : theory               (*copy of input theory*)
  val defs       : thm list             (*definitions made in thy*)
  val mono       : thm                  (*monotonicity for the lfp definition*)
  val intrs      : thm list             (*introduction rules*)
  val elim       : thm                  (*case analysis theorem*)
  val mk_cases   : thm list -> string -> thm    (*generates case theorems*)
  end;

signature INTR_ELIM_AUX =       (** Used to make induction rules **)
  sig
  val raw_induct : thm                  (*raw induction rule from Fp.induct*)
  val rec_names  : string list          (*names of recursive sets*)
  end;

(*prove intr/elim rules for a fixedpoint definition*)
functor Intr_elim_Fun
    (structure Inductive: sig include INDUCTIVE_ARG INDUCTIVE_I end  
     and Fp: FP) 
    : sig include INTR_ELIM INTR_ELIM_AUX end =
let
val rec_names = map (#1 o dest_Const o head_of) Inductive.rec_tms;
val big_rec_name = space_implode "_" rec_names;

val _ = deny (big_rec_name mem (Sign.stamp_names_of (sign_of Inductive.thy)))
             ("Definition " ^ big_rec_name ^ 
              " would clash with the theory of the same name!");

(*fetch fp definitions from the theory*)
val big_rec_def::part_rec_defs = 
  map (get_def Inductive.thy)
      (case rec_names of [_] => rec_names | _ => big_rec_name::rec_names);


val sign = sign_of Inductive.thy;

(********)
val _ = writeln "  Proving monotonicity...";

val Const("==",_) $ _ $ (Const(_,fpT) $ fp_abs) =
    big_rec_def |> rep_thm |> #prop |> Logic.unvarify;

(*For the type of the argument of mono*)
val [monoT] = binder_types fpT;

val mono = 
    prove_goalw_cterm [] 
      (cterm_of sign (Ind_Syntax.mk_Trueprop 
                      (Const("mono", monoT --> Ind_Syntax.boolT) $ fp_abs)))
      (fn _ =>
       [rtac monoI 1,
        REPEAT (ares_tac (basic_monos @ Inductive.monos) 1)]);

val unfold = standard (mono RS (big_rec_def RS Fp.Tarski));

(********)
val _ = writeln "  Proving the introduction rules...";

fun intro_tacsf disjIn prems = 
  [(*insert prems and underlying sets*)
   cut_facts_tac prems 1,
   stac unfold 1,
   REPEAT (resolve_tac [Part_eqI,CollectI] 1),
   (*Now 1-2 subgoals: the disjunction, perhaps equality.*)
   rtac disjIn 1,
   (*Not ares_tac, since refl must be tried before any equality assumptions;
     backtracking may occur if the premises have extra variables!*)
   DEPTH_SOLVE_1 (resolve_tac [refl,exI,conjI] 1 APPEND assume_tac 1),
   (*Now solve the equations like Inl 0 = Inl ?b2*)
   rewrite_goals_tac Inductive.con_defs,
   REPEAT (rtac refl 1)];


(*combines disjI1 and disjI2 to access the corresponding nested disjunct...*)
val mk_disj_rls = 
    let fun f rl = rl RS disjI1
        and g rl = rl RS disjI2
    in  accesses_bal(f, g, asm_rl)  end;

val intrs = ListPair.map (uncurry (prove_goalw_cterm part_rec_defs))
            (map (cterm_of sign) Inductive.intr_tms,
             map intro_tacsf (mk_disj_rls(length Inductive.intr_tms)));

(********)
val _ = writeln "  Proving the elimination rule...";

(*Breaks down logical connectives in the monotonic function*)
val basic_elim_tac =
    REPEAT (SOMEGOAL (eresolve_tac (Ind_Syntax.elim_rls @ 
                                    Ind_Syntax.sumprod_free_SEs)
              ORELSE' bound_hyp_subst_tac))
    THEN prune_params_tac;

(*Applies freeness of the given constructors, which *must* be unfolded by
  the given defs.  Cannot simply use the local con_defs because con_defs=[] 
  for inference systems.
fun con_elim_tac defs =
    rewrite_goals_tac defs THEN basic_elim_tac THEN fold_tac defs;
 *)
fun con_elim_tac simps =
  let val elim_tac = REPEAT o (eresolve_tac (Ind_Syntax.elim_rls @ 
                                             Ind_Syntax.sumprod_free_SEs))
  in ALLGOALS(EVERY'[elim_tac,
                     asm_full_simp_tac (simpset_of "Nat" addsimps simps),
                     elim_tac,
                     REPEAT o bound_hyp_subst_tac])
     THEN prune_params_tac
  end;


in
  struct
  val thy   = Inductive.thy
  and defs  = big_rec_def :: part_rec_defs
  and mono  = mono
  and intrs = intrs;

  val elim = rule_by_tactic basic_elim_tac 
                  (unfold RS Ind_Syntax.equals_CollectD);

  (*String s should have the form t:Si where Si is an inductive set*)
  fun mk_cases defs s = 
      rule_by_tactic (con_elim_tac defs)
          (assume_read Inductive.thy s  RS  elim) 
      |> standard;

  val raw_induct = standard ([big_rec_def, mono] MRS Fp.induct)
  and rec_names = rec_names
  end
end;

