(*  Title: 	ZF/intr-elim.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Introduction/elimination rule module -- for Inductive/Coinductive Definitions

Features:
* least or greatest fixedpoints
* user-specified product and sum constructions
* mutually recursive definitions
* definitions involving arbitrary monotone operators
* automatically proves introduction and elimination rules

The recursive sets must *already* be declared as constants in parent theory!

  Introduction rules have the form
  [| ti:M(Sj), ..., P(x), ... |] ==> t: Sk |]
  where M is some monotone operator (usually the identity)
  P(x) is any (non-conjunctive) side condition on the free variables
  ti, t are any terms
  Sj, Sk are two of the sets being defined in mutual recursion

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

signature FP =		(** Description of a fixed point operator **)
  sig
  val oper	: term			(*fixed point operator*)
  val bnd_mono	: term			(*monotonicity predicate*)
  val bnd_monoI	: thm			(*intro rule for bnd_mono*)
  val subs	: thm			(*subset theorem for fp*)
  val Tarski	: thm			(*Tarski's fixed point theorem*)
  val induct	: thm			(*induction/coinduction rule*)
  end;

signature PR =			(** Description of a Cartesian product **)
  sig
  val sigma	: term			(*Cartesian product operator*)
  val pair	: term			(*pairing operator*)
  val split_const  : term		(*splitting operator*)
  val fsplit_const : term		(*splitting operator for formulae*)
  val pair_iff	: thm			(*injectivity of pairing, using <->*)
  val split_eq	: thm			(*equality rule for split*)
  val fsplitI	: thm			(*intro rule for fsplit*)
  val fsplitD	: thm			(*destruct rule for fsplit*)
  val fsplitE	: thm			(*elim rule for fsplit*)
  end;

signature SU =			(** Description of a disjoint sum **)
  sig
  val sum	: term			(*disjoint sum operator*)
  val inl	: term			(*left injection*)
  val inr	: term			(*right injection*)
  val elim	: term			(*case operator*)
  val case_inl	: thm			(*inl equality rule for case*)
  val case_inr	: thm			(*inr equality rule for case*)
  val inl_iff	: thm			(*injectivity of inl, using <->*)
  val inr_iff	: thm			(*injectivity of inr, using <->*)
  val distinct	: thm			(*distinctness of inl, inr using <->*)
  val distinct'	: thm			(*distinctness of inr, inl using <->*)
  end;

signature INDUCTIVE =		(** Description of a (co)inductive defn **)
  sig
  val thy        : theory		(*parent theory*)
  val rec_doms   : (string*string) list	(*recursion ops and their domains*)
  val sintrs     : string list		(*desired introduction rules*)
  val monos      : thm list		(*monotonicity of each M operator*)
  val con_defs   : thm list		(*definitions of the constructors*)
  val type_intrs : thm list		(*type-checking intro rules*)
  val type_elims : thm list		(*type-checking elim rules*)
  end;

signature INTR_ELIM =
  sig
  val thy        : theory		(*new theory*)
  val defs	 : thm list		(*definitions made in thy*)
  val bnd_mono   : thm			(*monotonicity for the lfp definition*)
  val unfold     : thm			(*fixed-point equation*)
  val dom_subset : thm			(*inclusion of recursive set in dom*)
  val intrs      : thm list		(*introduction rules*)
  val elim       : thm			(*case analysis theorem*)
  val raw_induct : thm			(*raw induction rule from Fp.induct*)
  val mk_cases : thm list -> string -> thm	(*generates case theorems*)
  (*internal items...*)
  val big_rec_tm : term			(*the lhs of the fixedpoint defn*)
  val rec_tms    : term list		(*the mutually recursive sets*)
  val domts      : term list		(*domains of the recursive sets*)
  val intr_tms   : term list		(*terms for the introduction rules*)
  val rec_params : term list		(*parameters of the recursion*)
  val sumprod_free_SEs : thm list       (*destruct rules for Su and Pr*)
  end;


functor Intr_elim_Fun (structure Ind: INDUCTIVE and 
		       Fp: FP and Pr : PR and Su : SU) : INTR_ELIM =
struct
open Logic Ind;

(*** Extract basic information from arguments ***)

val sign = sign_of Ind.thy;

fun rd T a = 
    read_cterm sign (a,T)
    handle ERROR => error ("The error above occurred for " ^ a);

val rec_names = map #1 rec_doms
and domts     = map (term_of o rd iT o #2) rec_doms;

val dummy = assert_all Syntax.is_identifier rec_names
   (fn a => "Name of recursive set not an identifier: " ^ a);

val dummy = assert_all (is_some o lookup_const sign) rec_names
   (fn a => "Name of recursive set not declared as constant: " ^ a);

val intr_tms = map (term_of o rd propT) sintrs;

local (*Checking the introduction rules*)
  val intr_sets = map (#2 o rule_concl) intr_tms;

  fun intr_ok set =
      case head_of set of Const(a,recT) => a mem rec_names | _ => false;

  val dummy =  assert_all intr_ok intr_sets
     (fn t => "Conclusion of rule does not name a recursive set: " ^ 
	      Sign.string_of_term sign t);
in
val (Const(_,recT),rec_params) = strip_comb (hd intr_sets)
end;

val rec_hds = map (fn a=> Const(a,recT)) rec_names;
val rec_tms = map (fn rec_hd=> list_comb(rec_hd,rec_params)) rec_hds;

val dummy = assert_all is_Free rec_params
    (fn t => "Param in recursion term not a free variable: " ^
             Sign.string_of_term sign t);

(*** Construct the lfp definition ***)

val mk_variant = variant (foldr add_term_names (intr_tms,[]));

val z' = mk_variant"z"
and X' = mk_variant"X"
and w' = mk_variant"w";

(*simple error-checking in the premises*)
fun chk_prem rec_hd (Const("op &",_) $ _ $ _) =
	error"Premises may not be conjuctive"
  | chk_prem rec_hd (Const("op :",_) $ t $ X) = 
	deny (rec_hd occs t) "Recursion term on left of member symbol"
  | chk_prem rec_hd t = 
	deny (rec_hd occs t) "Recursion term in side formula";

(*Makes a disjunct from an introduction rule*)
fun lfp_part intr = (*quantify over rule's free vars except parameters*)
  let val prems = map dest_tprop (strip_imp_prems intr)
      val dummy = seq (fn rec_hd => seq (chk_prem rec_hd) prems) rec_hds
      val exfrees = term_frees intr \\ rec_params
      val zeq = eq_const $ (Free(z',iT)) $ (#1 (rule_concl intr))
  in foldr mk_exists (exfrees, fold_bal (app conj) (zeq::prems)) end;

val dom_sum = fold_bal (app Su.sum) domts;

(*The Part(A,h) terms -- compose injections to make h*)
fun mk_Part (Bound 0) = Free(X',iT)	(*no mutual rec, no Part needed*)
  | mk_Part h         = Part_const $ Free(X',iT) $ Abs(w',iT,h);

(*Access to balanced disjoint sums via injections*)
val parts = 
    map mk_Part (accesses_bal (ap Su.inl, ap Su.inr, Bound 0) 
		              (length rec_doms));

(*replace each set by the corresponding Part(A,h)*)
val part_intrs = map (subst_free (rec_tms ~~ parts) o lfp_part) intr_tms;

val lfp_abs = absfree(X', iT, 
	         mk_Collect(z', dom_sum, fold_bal (app disj) part_intrs));

val lfp_rhs = Fp.oper $ dom_sum $ lfp_abs

val dummy = seq (fn rec_hd => deny (rec_hd occs lfp_rhs) 
			   "Illegal occurrence of recursion operator")
	 rec_hds;

(*** Make the new theory ***)

(*A key definition:
  If no mutual recursion then it equals the one recursive set.
  If mutual recursion then it differs from all the recursive sets. *)
val big_rec_name = space_implode "_" rec_names;

(*Big_rec... is the union of the mutually recursive sets*)
val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

(*The individual sets must already be declared*)
val axpairs = map (mk_defpair sign) 
      ((big_rec_tm, lfp_rhs) ::
       (case parts of 
	   [_] => [] 			(*no mutual recursion*)
	 | _ => rec_tms ~~		(*define the sets as Parts*)
		map (subst_atomic [(Free(X',iT),big_rec_tm)]) parts));

val thy = extend_theory Ind.thy (big_rec_name ^ "_Inductive")
    ([], [], [], [], [], [], None) axpairs;

val defs = map (get_axiom thy o #1) axpairs;

val big_rec_def::part_rec_defs = defs;

val prove = prove_term (sign_of thy);

(********)
val dummy = writeln "Proving monotonocity...";

val bnd_mono = 
    prove [] (mk_tprop (Fp.bnd_mono $ dom_sum $ lfp_abs), 
       fn _ =>
       [rtac (Collect_subset RS bnd_monoI) 1,
	REPEAT (ares_tac (basic_monos @ monos) 1)]);

val dom_subset = standard (big_rec_def RS Fp.subs);

val unfold = standard (bnd_mono RS (big_rec_def RS Fp.Tarski));

(********)
val dummy = writeln "Proving the introduction rules...";

(*Mutual recursion: Needs subset rules for the individual sets???*)
val rec_typechecks = [dom_subset] RL (asm_rl::monos) RL [subsetD];

(*Type-checking is hardest aspect of proof;
  disjIn selects the correct disjunct after unfolding*)
fun intro_tacsf disjIn prems = 
  [(*insert prems and underlying sets*)
   cut_facts_tac prems 1,
   rtac (unfold RS ssubst) 1,
   REPEAT (resolve_tac [Part_eqI,CollectI] 1),
   (*Now 2-3 subgoals: typechecking, the disjunction, perhaps equality.*)
   rtac disjIn 2,
   REPEAT (ares_tac [refl,exI,conjI] 2),
   rewrite_goals_tac con_defs,
   (*Now can solve the trivial equation*)
   REPEAT (rtac refl 2),
   REPEAT (FIRSTGOAL (eresolve_tac (asm_rl::PartE::type_elims)
		      ORELSE' hyp_subst_tac
		      ORELSE' dresolve_tac rec_typechecks)),
   DEPTH_SOLVE (swap_res_tac type_intrs 1)];

(*combines disjI1 and disjI2 to access the corresponding nested disjunct...*)
val mk_disj_rls = 
    let fun f rl = rl RS disjI1
        and g rl = rl RS disjI2
    in  accesses_bal(f, g, asm_rl)  end;

val intrs = map (prove part_rec_defs) 
	       (intr_tms ~~ map intro_tacsf (mk_disj_rls(length intr_tms)));

(********)
val dummy = writeln "Proving the elimination rule...";

(*Includes rules for succ and Pair since they are common constructions*)
val elim_rls = [asm_rl, FalseE, succ_neq_0, sym RS succ_neq_0, 
		Pair_neq_0, sym RS Pair_neq_0, make_elim succ_inject, 
		refl_thin, conjE, exE, disjE];

val sumprod_free_SEs = 
    map (gen_make_elim [conjE,FalseE])
        ([Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff] 
	 RL [iffD1]);

(*Breaks down logical connectives in the monotonic function*)
val basic_elim_tac =
    REPEAT (SOMEGOAL (eresolve_tac (elim_rls@sumprod_free_SEs)
              ORELSE' bound_hyp_subst_tac))
    THEN prune_params_tac;

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

val defs = big_rec_def::part_rec_defs;

val raw_induct = standard ([big_rec_def, bnd_mono] MRS Fp.induct);

end;
