(*  Title:      FOL/simpdata.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Simplification data for FOL.
*)

(*Make meta-equalities.  The operator below is Trueprop*)

fun mk_meta_eq th = case concl_of th of
    _ $ (Const("op =",_)$_$_)   => th RS @{thm eq_reflection}
  | _ $ (Const("op <->",_)$_$_) => th RS @{thm iff_reflection}
  | _                           =>
  error("conclusion must be a =-equality or <->");;

fun mk_eq th = case concl_of th of
    Const("==",_)$_$_           => th
  | _ $ (Const("op =",_)$_$_)   => mk_meta_eq th
  | _ $ (Const("op <->",_)$_$_) => mk_meta_eq th
  | _ $ (Const("Not",_)$_)      => th RS @{thm iff_reflection_F}
  | _                           => th RS @{thm iff_reflection_T};

(*Replace premises x=y, X<->Y by X==Y*)
val mk_meta_prems =
    rule_by_tactic
      (REPEAT_FIRST (resolve_tac [@{thm meta_eq_to_obj_eq}, @{thm def_imp_iff}]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong rl =
  Drule.standard (mk_meta_eq (mk_meta_prems rl))
  handle THM _ =>
  error("Premises and conclusion of congruence rules must use =-equality or <->");

val mksimps_pairs =
  [("op -->", [@{thm mp}]), ("op &", [@{thm conjunct1}, @{thm conjunct2}]),
   ("All", [@{thm spec}]), ("True", []), ("False", [])];

(* ###FIXME: move to simplifier.ML
val mk_atomize:      (string * thm list) list -> thm -> thm list
*)
(* ###FIXME: move to simplifier.ML *)
fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case AList.lookup (op =) pairs a of
                     SOME(rls) => maps atoms ([th] RL rls)
                   | NONE => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mksimps pairs = (map mk_eq o mk_atomize pairs o gen_all);


(** make simplification procedures for quantifier elimination **)
structure Quantifier1 = Quantifier1Fun(
struct
  (*abstract syntax*)
  fun dest_eq((c as Const("op =",_)) $ s $ t) = SOME(c,s,t)
    | dest_eq _ = NONE;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = SOME(c,s,t)
    | dest_conj _ = NONE;
  fun dest_imp((c as Const("op -->",_)) $ s $ t) = SOME(c,s,t)
    | dest_imp _ = NONE;
  val conj = FOLogic.conj
  val imp  = FOLogic.imp
  (*rules*)
  val iff_reflection = @{thm iff_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm iff_trans}
  val conjI= @{thm conjI}
  val conjE= @{thm conjE}
  val impI = @{thm impI}
  val mp   = @{thm mp}
  val uncurry = @{thm uncurry}
  val exI  = @{thm exI}
  val exE  = @{thm exE}
  val iff_allI = @{thm iff_allI}
  val iff_exI = @{thm iff_exI}
  val all_comm = @{thm all_comm}
  val ex_comm = @{thm ex_comm}
end);

val defEX_regroup =
  Simplifier.simproc @{theory}
    "defined EX" ["EX x. P(x)"] Quantifier1.rearrange_ex;

val defALL_regroup =
  Simplifier.simproc @{theory}
    "defined ALL" ["ALL x. P(x)"] Quantifier1.rearrange_all;


(*** Case splitting ***)

structure Splitter = Splitter
(
  val thy = @{theory}
  val mk_eq = mk_eq
  val meta_eq_to_iff = @{thm meta_eq_to_iff}
  val iffD = @{thm iffD2}
  val disjE = @{thm disjE}
  val conjE = @{thm conjE}
  val exE = @{thm exE}
  val contrapos = @{thm contrapos}
  val contrapos2 = @{thm contrapos2}
  val notnotD = @{thm notnotD}
);

val split_tac = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;
val split_asm_tac = Splitter.split_asm_tac;
val op addsplits = Splitter.addsplits;
val op delsplits = Splitter.delsplits;


(*** Standard simpsets ***)

val triv_rls = [@{thm TrueI}, @{thm refl}, reflexive_thm, @{thm iff_refl}, @{thm notFalseI}];

fun unsafe_solver prems = FIRST'[resolve_tac (triv_rls @ prems),
                                 atac, etac @{thm FalseE}];
(*No premature instantiation of variables during simplification*)
fun   safe_solver prems = FIRST'[match_tac (triv_rls @ prems),
                                 eq_assume_tac, ematch_tac [@{thm FalseE}]];

(*No simprules, but basic infastructure for simplification*)
val FOL_basic_ss =
  Simplifier.theory_context @{theory} empty_ss
  setsubgoaler asm_simp_tac
  setSSolver (mk_solver "FOL safe" safe_solver)
  setSolver (mk_solver "FOL unsafe" unsafe_solver)
  setmksimps (mksimps mksimps_pairs)
  setmkcong mk_meta_cong;

fun unfold_tac ths =
  let val ss0 = Simplifier.clear_ss FOL_basic_ss addsimps ths
  in fn ss => ALLGOALS (full_simp_tac (Simplifier.inherit_context ss ss0)) end;


(*intuitionistic simprules only*)
val IFOL_ss =
  FOL_basic_ss
  addsimps (@{thms meta_simps} @ @{thms IFOL_simps} @ @{thms int_ex_simps} @ @{thms int_all_simps})
  addsimprocs [defALL_regroup, defEX_regroup]    
  addcongs [@{thm imp_cong}];

(*classical simprules too*)
val FOL_ss = IFOL_ss addsimps (@{thms cla_simps} @ @{thms cla_ex_simps} @ @{thms cla_all_simps});

val simpsetup = Simplifier.map_simpset (K FOL_ss);


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
  and Classical  = Cla and Blast = Blast
  val iffD1 = @{thm iffD1} val iffD2 = @{thm iffD2} val notE = @{thm notE});
open Clasimp;

ML_Antiquote.value "clasimpset"
  (Scan.succeed "Clasimp.clasimpset_of (ML_Context.the_local_context ())");

val FOL_css = (FOL_cs, FOL_ss);
