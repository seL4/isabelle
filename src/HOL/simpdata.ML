(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier for HOL.
*)

(* legacy ML bindings *)

val Eq_FalseI = thm "Eq_FalseI";
val Eq_TrueI = thm "Eq_TrueI";
val all_conj_distrib = thm "all_conj_distrib";
val all_simps = thms "all_simps";
val cases_simp = thm "cases_simp";
val conj_assoc = thm "conj_assoc";
val conj_comms = thms "conj_comms";
val conj_commute = thm "conj_commute";
val conj_cong = thm "conj_cong";
val conj_disj_distribL = thm "conj_disj_distribL";
val conj_disj_distribR = thm "conj_disj_distribR";
val conj_left_commute = thm "conj_left_commute";
val de_Morgan_conj = thm "de_Morgan_conj";
val de_Morgan_disj = thm "de_Morgan_disj";
val disj_assoc = thm "disj_assoc";
val disj_comms = thms "disj_comms";
val disj_commute = thm "disj_commute";
val disj_cong = thm "disj_cong";
val disj_conj_distribL = thm "disj_conj_distribL";
val disj_conj_distribR = thm "disj_conj_distribR";
val disj_left_commute = thm "disj_left_commute";
val disj_not1 = thm "disj_not1";
val disj_not2 = thm "disj_not2";
val eq_ac = thms "eq_ac";
val eq_assoc = thm "eq_assoc";
val eq_commute = thm "eq_commute";
val eq_left_commute = thm "eq_left_commute";
val eq_sym_conv = thm "eq_sym_conv";
val eta_contract_eq = thm "eta_contract_eq";
val ex_disj_distrib = thm "ex_disj_distrib";
val ex_simps = thms "ex_simps";
val if_False = thm "if_False";
val if_P = thm "if_P";
val if_True = thm "if_True";
val if_bool_eq_conj = thm "if_bool_eq_conj";
val if_bool_eq_disj = thm "if_bool_eq_disj";
val if_cancel = thm "if_cancel";
val if_def2 = thm "if_def2";
val if_eq_cancel = thm "if_eq_cancel";
val if_not_P = thm "if_not_P";
val if_splits = thms "if_splits";
val iff_conv_conj_imp = thm "iff_conv_conj_imp";
val imp_all = thm "imp_all";
val imp_cong = thm "imp_cong";
val imp_conjL = thm "imp_conjL";
val imp_conjR = thm "imp_conjR";
val imp_conv_disj = thm "imp_conv_disj";
val imp_disj1 = thm "imp_disj1";
val imp_disj2 = thm "imp_disj2";
val imp_disjL = thm "imp_disjL";
val imp_disj_not1 = thm "imp_disj_not1";
val imp_disj_not2 = thm "imp_disj_not2";
val imp_ex = thm "imp_ex";
val meta_eq_to_obj_eq = thm "meta_eq_to_obj_eq";
val neq_commute = thm "neq_commute";
val not_all = thm "not_all";
val not_ex = thm "not_ex";
val not_iff = thm "not_iff";
val not_imp = thm "not_imp";
val not_not = thm "not_not";
val rev_conj_cong = thm "rev_conj_cong";
val simp_thms = thms "simp_thms";
val split_if = thm "split_if";
val split_if_asm = thm "split_if_asm";
val atomize_not = thm"atomize_not";

local
val uncurry = prove_goal (the_context()) "P --> Q --> R ==> P & Q --> R"
              (fn prems => [cut_facts_tac prems 1, Blast_tac 1]);

val iff_allI = allI RS
    prove_goal (the_context()) "!x. P x = Q x ==> (!x. P x) = (!x. Q x)"
               (fn prems => [cut_facts_tac prems 1, Blast_tac 1])
val iff_exI = allI RS
    prove_goal (the_context()) "!x. P x = Q x ==> (? x. P x) = (? x. Q x)"
               (fn prems => [cut_facts_tac prems 1, Blast_tac 1])

val all_comm = prove_goal (the_context()) "(!x y. P x y) = (!y x. P x y)"
               (fn _ => [Blast_tac 1])
val ex_comm = prove_goal (the_context()) "(? x y. P x y) = (? y x. P x y)"
               (fn _ => [Blast_tac 1])
in

(*** make simplification procedures for quantifier elimination ***)

structure Quantifier1 = Quantifier1Fun
(struct
  (*abstract syntax*)
  fun dest_eq((c as Const("op =",_)) $ s $ t) = Some(c,s,t)
    | dest_eq _ = None;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = Some(c,s,t)
    | dest_conj _ = None;
  fun dest_imp((c as Const("op -->",_)) $ s $ t) = Some(c,s,t)
    | dest_imp _ = None;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  (*rules*)
  val iff_reflection = eq_reflection
  val iffI = iffI
  val iff_trans = trans
  val conjI= conjI
  val conjE= conjE
  val impI = impI
  val mp   = mp
  val uncurry = uncurry
  val exI  = exI
  val exE  = exE
  val iff_allI = iff_allI
  val iff_exI = iff_exI
  val all_comm = all_comm
  val ex_comm = ex_comm
end);

end;

val defEX_regroup =
  Simplifier.simproc (Theory.sign_of (the_context ()))
    "defined EX" ["EX x. P x"] Quantifier1.rearrange_ex;

val defALL_regroup =
  Simplifier.simproc (Theory.sign_of (the_context ()))
    "defined ALL" ["ALL x. P x"] Quantifier1.rearrange_all;


(*** Case splitting ***)

(*Make meta-equalities.  The operator below is Trueprop*)

fun mk_meta_eq r = r RS eq_reflection;
fun safe_mk_meta_eq r = mk_meta_eq r handle Thm.THM _ => r;

fun mk_eq th = case concl_of th of
        Const("==",_)$_$_       => th
    |   _$(Const("op =",_)$_$_) => mk_meta_eq th
    |   _$(Const("Not",_)$_)    => th RS Eq_FalseI
    |   _                       => th RS Eq_TrueI;
(* Expects Trueprop(.) if not == *)

fun mk_eq_True r =
  Some (r RS meta_eq_to_obj_eq RS Eq_TrueI) handle Thm.THM _ => None;

(*Congruence rules for = (instead of ==)*)
fun mk_meta_cong rl =
  zero_var_indexes(mk_meta_eq(replicate (nprems_of rl) meta_eq_to_obj_eq MRS rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must be =-equalities");

(* Elimination of True from asumptions: *)

local fun rd s = read_cterm (sign_of (the_context())) (s, propT);
in val True_implies_equals = standard' (equal_intr
  (implies_intr_hyps (implies_elim (assume (rd "True ==> PROP P")) TrueI))
  (implies_intr_hyps (implies_intr (rd "True") (assume (rd "PROP P")))));
end;


structure SplitterData =
  struct
  structure Simplifier = Simplifier
  val mk_eq          = mk_eq
  val meta_eq_to_iff = meta_eq_to_obj_eq
  val iffD           = iffD2
  val disjE          = disjE
  val conjE          = conjE
  val exE            = exE
  val contrapos      = contrapos_nn
  val contrapos2     = contrapos_pp
  val notnotD        = notnotD
  end;

structure Splitter = SplitterFun(SplitterData);

val split_tac        = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;
val split_asm_tac    = Splitter.split_asm_tac;
val op addsplits     = Splitter.addsplits;
val op delsplits     = Splitter.delsplits;
val Addsplits        = Splitter.Addsplits;
val Delsplits        = Splitter.Delsplits;

val mksimps_pairs =
  [("op -->", [mp]), ("op &", [conjunct1,conjunct2]),
   ("All", [spec]), ("True", []), ("False", []),
   ("If", [if_bool_eq_conj RS iffD1])];

(*
val mk_atomize:      (string * thm list) list -> thm -> thm list
looks too specific to move it somewhere else
*)
fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case assoc(pairs,a) of
                     Some(rls) => flat (map atoms ([th] RL rls))
                   | None => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mksimps pairs =
  (mapfilter (try mk_eq) o mk_atomize pairs o gen_all);

fun unsafe_solver_tac prems =
  FIRST'[resolve_tac(reflexive_thm::TrueI::refl::prems), atac, etac FalseE];
val unsafe_solver = mk_solver "HOL unsafe" unsafe_solver_tac;

(*No premature instantiation of variables during simplification*)
fun safe_solver_tac prems =
  FIRST'[match_tac(reflexive_thm::TrueI::refl::prems),
         eq_assume_tac, ematch_tac [FalseE]];
val safe_solver = mk_solver "HOL safe" safe_solver_tac;

val HOL_basic_ss =
  empty_ss setsubgoaler asm_simp_tac
    setSSolver safe_solver
    setSolver unsafe_solver
    setmksimps (mksimps mksimps_pairs)
    setmkeqTrue mk_eq_True
    setmkcong mk_meta_cong;

(*In general it seems wrong to add distributive laws by default: they
  might cause exponential blow-up.  But imp_disjL has been in for a while
  and cannot be removed without affecting existing proofs.  Moreover,
  rewriting by "(P|Q --> R) = ((P-->R)&(Q-->R))" might be justified on the
  grounds that it allows simplification of R in the two cases.*)

val HOL_ss =
    HOL_basic_ss addsimps
     ([triv_forall_equality, (* prunes params *)
       True_implies_equals, (* prune asms `True' *)
       eta_contract_eq, (* prunes eta-expansions *)
       if_True, if_False, if_cancel, if_eq_cancel,
       imp_disjL, conj_assoc, disj_assoc,
       de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2, not_imp,
       disj_not1, not_all, not_ex, cases_simp,
       thm "the_eq_trivial", the_sym_eq_trivial]
     @ ex_simps @ all_simps @ simp_thms)
     addsimprocs [defALL_regroup,defEX_regroup]
     addcongs [imp_cong]
     addsplits [split_if];

fun hol_simplify rews = Simplifier.full_simplify (HOL_basic_ss addsimps rews);


(*Simplifies x assuming c and y assuming ~c*)
val prems = Goalw [if_def]
  "[| b=c; c ==> x=u; ~c ==> y=v |] ==> \
\  (if b then x else y) = (if c then u else v)";
by (asm_simp_tac (HOL_ss addsimps prems) 1);
qed "if_cong";

(*Prevents simplification of x and y: faster and allows the execution
  of functional programs. NOW THE DEFAULT.*)
Goal "b=c ==> (if b then x else y) = (if c then x else y)";
by (etac arg_cong 1);
qed "if_weak_cong";

(*Prevents simplification of t: much faster*)
Goal "a = b ==> (let x=a in t(x)) = (let x=b in t(x))";
by (etac arg_cong 1);
qed "let_weak_cong";

(*To tidy up the result of a simproc.  Only the RHS will be simplified.*)
Goal "u = u' ==> (t==u) == (t==u')";
by (asm_simp_tac HOL_ss 1);
qed "eq_cong2";

Goal "f(if c then x else y) = (if c then f x else f y)";
by (simp_tac (HOL_ss setloop (split_tac [split_if])) 1);
qed "if_distrib";

(*For expand_case_tac*)
val prems = Goal "[| P ==> Q(True); ~P ==> Q(False) |] ==> Q(P)";
by (case_tac "P" 1);
by (ALLGOALS (asm_simp_tac (HOL_ss addsimps prems)));
qed "expand_case";

(*Used in Auth proofs.  Typically P contains Vars that become instantiated
  during unification.*)
fun expand_case_tac P i =
    res_inst_tac [("P",P)] expand_case i THEN
    Simp_tac (i+1) THEN
    Simp_tac i;

(*This lemma restricts the effect of the rewrite rule u=v to the left-hand
  side of an equality.  Used in {Integ,Real}/simproc.ML*)
Goal "x=y ==> (x=z) = (y=z)";
by (asm_simp_tac HOL_ss 1);
qed "restrict_to_left";

(* default simpset *)
val simpsetup =
  [fn thy => (simpset_ref_of thy := HOL_ss addcongs [if_weak_cong]; thy)];


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
  and Classical  = Classical and Blast = Blast
  val iffD1 = iffD1 val iffD2 = iffD2 val notE = notE
  val cla_make_elim = cla_make_elim);
open Clasimp;

val HOL_css = (HOL_cs, HOL_ss);



(*** A general refutation procedure ***)

(* Parameters:

   test: term -> bool
   tests if a term is at all relevant to the refutation proof;
   if not, then it can be discarded. Can improve performance,
   esp. if disjunctions can be discarded (no case distinction needed!).

   prep_tac: int -> tactic
   A preparation tactic to be applied to the goal once all relevant premises
   have been moved to the conclusion.

   ref_tac: int -> tactic
   the actual refutation tactic. Should be able to deal with goals
   [| A1; ...; An |] ==> False
   where the Ai are atomic, i.e. no top-level &, | or EX
*)

fun refute_tac test prep_tac ref_tac =
  let val nnf_simps =
        [imp_conv_disj,iff_conv_conj_imp,de_Morgan_disj,de_Morgan_conj,
         not_all,not_ex,not_not];
      val nnf_simpset =
        empty_ss setmkeqTrue mk_eq_True
                 setmksimps (mksimps mksimps_pairs)
                 addsimps nnf_simps;
      val prem_nnf_tac = full_simp_tac nnf_simpset;

      val refute_prems_tac =
        REPEAT_DETERM
              (eresolve_tac [conjE, exE] 1 ORELSE
               filter_prems_tac test 1 ORELSE
               etac disjE 1) THEN
        ((etac notE 1 THEN eq_assume_tac 1) ORELSE
         ref_tac 1);
  in EVERY'[TRY o filter_prems_tac test,
            REPEAT_DETERM o etac rev_mp, prep_tac, rtac ccontr, prem_nnf_tac,
            SELECT_GOAL (DEPTH_SOLVE refute_prems_tac)]
  end;
