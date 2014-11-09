(*  Title:      FOL/simpdata.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Simplification data for FOL.
*)

(*Make meta-equalities.  The operator below is Trueprop*)

fun mk_meta_eq th = case concl_of th of
    _ $ (Const(@{const_name eq},_)$_$_)   => th RS @{thm eq_reflection}
  | _ $ (Const(@{const_name iff},_)$_$_) => th RS @{thm iff_reflection}
  | _                           =>
  error("conclusion must be a =-equality or <->");;

fun mk_eq th = case concl_of th of
    Const(@{const_name Pure.eq},_)$_$_ => th
  | _ $ (Const(@{const_name eq},_)$_$_)   => mk_meta_eq th
  | _ $ (Const(@{const_name iff},_)$_$_) => mk_meta_eq th
  | _ $ (Const(@{const_name Not},_)$_)      => th RS @{thm iff_reflection_F}
  | _                           => th RS @{thm iff_reflection_T};

(*Replace premises x=y, X<->Y by X==Y*)
fun mk_meta_prems ctxt =
    rule_by_tactic ctxt
      (REPEAT_FIRST (resolve_tac [@{thm meta_eq_to_obj_eq}, @{thm def_imp_iff}]));

(*Congruence rules for = or <-> (instead of ==)*)
fun mk_meta_cong ctxt rl =
  Drule.zero_var_indexes (mk_meta_eq (mk_meta_prems ctxt rl))
    handle THM _ =>
      error("Premises and conclusion of congruence rules must use =-equality or <->");

val mksimps_pairs =
  [(@{const_name imp}, [@{thm mp}]), (@{const_name conj}, [@{thm conjunct1}, @{thm conjunct2}]),
   (@{const_name All}, [@{thm spec}]), (@{const_name True}, []), (@{const_name False}, [])];

fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const(@{const_name Trueprop},_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case AList.lookup (op =) pairs a of
                     SOME(rls) => maps atoms ([th] RL rls)
                   | NONE => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mksimps pairs (_: Proof.context) = map mk_eq o mk_atomize pairs o gen_all;


(** make simplification procedures for quantifier elimination **)
structure Quantifier1 = Quantifier1
(
  (*abstract syntax*)
  fun dest_eq (Const (@{const_name eq}, _) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE
  fun dest_conj (Const (@{const_name conj}, _) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE
  fun dest_imp (Const (@{const_name imp}, _) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE
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
);


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


(*** Standard simpsets ***)

val triv_rls = [@{thm TrueI}, @{thm refl}, reflexive_thm, @{thm iff_refl}, @{thm notFalseI}];

fun unsafe_solver ctxt =
  FIRST' [resolve_tac (triv_rls @ Simplifier.prems_of ctxt),
    assume_tac,
    eresolve_tac @{thms FalseE}];

(*No premature instantiation of variables during simplification*)
fun safe_solver ctxt =
  FIRST' [match_tac ctxt (triv_rls @ Simplifier.prems_of ctxt),
    eq_assume_tac, ematch_tac ctxt @{thms FalseE}];

(*No simprules, but basic infastructure for simplification*)
val FOL_basic_ss =
  empty_simpset @{context}
  setSSolver (mk_solver "FOL safe" safe_solver)
  setSolver (mk_solver "FOL unsafe" unsafe_solver)
  |> Simplifier.set_subgoaler asm_simp_tac
  |> Simplifier.set_mksimps (mksimps mksimps_pairs)
  |> Simplifier.set_mkcong mk_meta_cong
  |> simpset_of;

fun unfold_tac ctxt ths =
  ALLGOALS (full_simp_tac (clear_simpset (put_simpset FOL_basic_ss ctxt) addsimps ths));


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = Clasimp
(
  structure Simplifier = Simplifier
    and Splitter = Splitter
    and Classical = Cla
    and Blast = Blast
  val iffD1 = @{thm iffD1}
  val iffD2 = @{thm iffD2}
  val notE = @{thm notE}
);
open Clasimp;

