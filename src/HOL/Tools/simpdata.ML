(*  Title:      HOL/Tools/simpdata.ML
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier for HOL.
*)

(** tools setup **)

structure Quantifier1 = Quantifier1
(
  (*abstract syntax*)
  fun dest_eq (Const(@{const_name HOL.eq},_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(@{const_name HOL.conj},_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(@{const_name HOL.implies},_) $ s $ t) = SOME (s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  (*rules*)
  val iff_reflection = @{thm eq_reflection}
  val iffI = @{thm iffI}
  val iff_trans = @{thm trans}
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

structure Simpdata =
struct

fun mk_meta_eq r = r RS @{thm eq_reflection};
fun safe_mk_meta_eq r = mk_meta_eq r handle Thm.THM _ => r;

fun mk_eq th = case concl_of th
  (*expects Trueprop if not == *)
  of Const (@{const_name "=="},_) $ _ $ _ => th
   | _ $ (Const (@{const_name HOL.eq}, _) $ _ $ _) => mk_meta_eq th
   | _ $ (Const (@{const_name Not}, _) $ _) => th RS @{thm Eq_FalseI}
   | _ => th RS @{thm Eq_TrueI}

fun mk_eq_True (_: simpset) r =
  SOME (r RS @{thm meta_eq_to_obj_eq} RS @{thm Eq_TrueI}) handle Thm.THM _ => NONE;

(* Produce theorems of the form
  (P1 =simp=> ... =simp=> Pn => x == y) ==> (P1 =simp=> ... =simp=> Pn => x = y)
*)

fun lift_meta_eq_to_obj_eq i st =
  let
    fun count_imp (Const (@{const_name HOL.simp_implies}, _) $ P $ Q) = 1 + count_imp Q
      | count_imp _ = 0;
    val j = count_imp (Logic.strip_assums_concl (nth (prems_of st) (i - 1)))
  in
    if j = 0 then @{thm meta_eq_to_obj_eq}
    else
      let
        val Ps = map (fn k => Free ("P" ^ string_of_int k, propT)) (1 upto j);
        fun mk_simp_implies Q = fold_rev (fn R => fn S =>
          Const (@{const_name HOL.simp_implies}, propT --> propT --> propT) $ R $ S) Ps Q
        val aT = TFree ("'a", HOLogic.typeS);
        val x = Free ("x", aT);
        val y = Free ("y", aT)
      in
        Goal.prove_global (Thm.theory_of_thm st) []
          [mk_simp_implies (Logic.mk_equals (x, y))]
          (mk_simp_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (x, y))))
          (fn {prems, ...} => EVERY
           [rewrite_goals_tac @{thms simp_implies_def},
            REPEAT (ares_tac (@{thm meta_eq_to_obj_eq} ::
              map (rewrite_rule @{thms simp_implies_def}) prems) 1)])
      end
  end;

(*Congruence rules for = (instead of ==)*)
fun mk_meta_cong (_: simpset) rl = zero_var_indexes
  (let val rl' = Seq.hd (TRYALL (fn i => fn st =>
     rtac (lift_meta_eq_to_obj_eq i st) i st) rl)
   in mk_meta_eq rl' handle THM _ =>
     if can Logic.dest_equals (concl_of rl') then rl'
     else error "Conclusion of congruence rules must be =-equality"
   end);

fun mk_atomize pairs =
  let
    fun atoms thm =
      let
        fun res th = map (fn rl => th RS rl);   (*exception THM*)
        fun res_fixed rls =
          if Thm.maxidx_of (Thm.adjust_maxidx_thm ~1 thm) = ~1 then res thm rls
          else Variable.trade (K (fn [thm'] => res thm' rls)) (Variable.global_thm_context thm) [thm];
      in
        case concl_of thm
          of Const (@{const_name Trueprop}, _) $ p => (case head_of p
            of Const (a, _) => (case AList.lookup (op =) pairs a
              of SOME rls => (maps atoms (res_fixed rls) handle THM _ => [thm])
              | NONE => [thm])
            | _ => [thm])
          | _ => [thm]
      end;
  in atoms end;

fun mksimps pairs (_: simpset) =
  map_filter (try mk_eq) o mk_atomize pairs o gen_all;

fun unsafe_solver_tac ss =
  (fn i => REPEAT_DETERM (match_tac @{thms simp_impliesI} i)) THEN'
  FIRST' [resolve_tac (reflexive_thm :: @{thm TrueI} :: @{thm refl} :: Simplifier.prems_of ss),
    atac, etac @{thm FalseE}];

val unsafe_solver = mk_solver "HOL unsafe" unsafe_solver_tac;


(*No premature instantiation of variables during simplification*)
fun safe_solver_tac ss =
  (fn i => REPEAT_DETERM (match_tac @{thms simp_impliesI} i)) THEN'
  FIRST' [match_tac (reflexive_thm :: @{thm TrueI} :: @{thm refl} :: Simplifier.prems_of ss),
    eq_assume_tac, ematch_tac @{thms FalseE}];

val safe_solver = mk_solver "HOL safe" safe_solver_tac;

structure Splitter = Splitter
(
  val thy = @{theory}
  val mk_eq = mk_eq
  val meta_eq_to_iff = @{thm meta_eq_to_obj_eq}
  val iffD = @{thm iffD2}
  val disjE = @{thm disjE}
  val conjE = @{thm conjE}
  val exE = @{thm exE}
  val contrapos = @{thm contrapos_nn}
  val contrapos2 = @{thm contrapos_pp}
  val notnotD = @{thm notnotD}
);

val split_tac = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;


(* integration of simplifier with classical reasoner *)

structure Clasimp = Clasimp
(
  structure Simplifier = Simplifier
    and Splitter = Splitter
    and Classical  = Classical
    and Blast = Blast
  val iffD1 = @{thm iffD1}
  val iffD2 = @{thm iffD2}
  val notE = @{thm notE}
);
open Clasimp;

val mksimps_pairs =
 [(@{const_name HOL.implies}, [@{thm mp}]),
  (@{const_name HOL.conj}, [@{thm conjunct1}, @{thm conjunct2}]),
  (@{const_name All}, [@{thm spec}]),
  (@{const_name True}, []),
  (@{const_name False}, []),
  (@{const_name If}, [@{thm if_bool_eq_conj} RS @{thm iffD1}])];

val HOL_basic_ss =
  Simplifier.global_context @{theory} empty_ss
    setsubgoaler asm_simp_tac
    setSSolver safe_solver
    setSolver unsafe_solver
    setmksimps (mksimps mksimps_pairs)
    setmkeqTrue mk_eq_True
    setmkcong mk_meta_cong;

fun hol_simplify rews = Simplifier.full_simplify (HOL_basic_ss addsimps rews);

fun unfold_tac ths =
  let val ss0 = Simplifier.clear_ss HOL_basic_ss addsimps ths
  in fn ss => ALLGOALS (full_simp_tac (Simplifier.inherit_context ss ss0)) end;

end;

structure Splitter = Simpdata.Splitter;
structure Clasimp = Simpdata.Clasimp;
