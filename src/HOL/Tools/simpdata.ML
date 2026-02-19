(*  Title:      HOL/Tools/simpdata.ML
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier for HOL.
*)

(** tools setup **)

structure Quantifier1 = Quantifier1
(
  (*abstract syntax*)
  fun dest_eq (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ s $ t) = SOME (s, t)
    | dest_eq _ = NONE;
  fun dest_conj (Const(\<^const_name>\<open>HOL.conj\<close>,_) $ s $ t) = SOME (s, t)
    | dest_conj _ = NONE;
  fun dest_imp (Const(\<^const_name>\<open>HOL.implies\<close>,_) $ s $ t) = SOME (s, t)
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
  val atomize =
    let val rules = @{thms atomize_all atomize_imp atomize_eq atomize_conj}
    in fn ctxt => Simplifier.rewrite_wrt ctxt true rules end
);

structure Simpdata =
struct

fun mk_meta_eq r = r RS @{thm eq_reflection};
fun safe_mk_meta_eq r = mk_meta_eq r handle Thm.THM _ => r;

fun mk_eq th =
  (case Thm.concl_of th of
  (*expects Trueprop if not == *)
    Const (\<^const_name>\<open>Pure.eq\<close>,_) $ _ $ _ => th
  | _ $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _) => mk_meta_eq th
  | _ $ (Const (\<^const_name>\<open>Not\<close>, _) $ _) => th RS @{thm Eq_FalseI}
  | _ => th RS @{thm Eq_TrueI})

fun mk_eq_True (_: Proof.context) r =
  SOME (HOLogic.mk_obj_eq r RS @{thm Eq_TrueI}) handle Thm.THM _ => NONE;

(* Produce theorems of the form
  (P1 =simp=> ... =simp=> Pn => x == y) ==> (P1 =simp=> ... =simp=> Pn => x = y)
*)

fun lift_meta_eq_to_obj_eq ctxt i st =
  let
    fun count_imp (Const (\<^const_name>\<open>HOL.simp_implies\<close>, _) $ _ $ P) = 1 + count_imp P
      | count_imp _ = 0;
    val j = count_imp (Logic.strip_assums_concl (Thm.term_of (Thm.cprem_of st i)))
  in
    if j = 0 then @{thm meta_eq_to_obj_eq}
    else
      let
        val Ps = map (fn k => Free ("P" ^ string_of_int k, propT)) (1 upto j);
        val mk_simp_implies = fold_rev (fn R => fn S =>
          Const (\<^const_name>\<open>HOL.simp_implies\<close>, propT --> propT --> propT) $ R $ S) Ps;
      in
        Goal.prove_global (Proof_Context.theory_of ctxt) []
          [mk_simp_implies \<^prop>\<open>(x::'a) == y\<close>]
          (mk_simp_implies \<^prop>\<open>(x::'a) = y\<close>)
          (fn {context = ctxt, prems} => EVERY
           [rewrite_goals_tac ctxt @{thms simp_implies_def},
            REPEAT (assume_tac ctxt 1 ORELSE
              resolve_tac ctxt
                (@{thm meta_eq_to_obj_eq} ::
                  map (rewrite_rule ctxt @{thms simp_implies_def}) prems) 1)])
      end
  end;

(*Congruence rules for = (instead of ==)*)
fun mk_meta_cong ctxt rl =
  let
    val rl' = Seq.hd (TRYALL (fn i => fn st =>
      resolve_tac ctxt [lift_meta_eq_to_obj_eq ctxt i st] i st) rl)
  in
    mk_meta_eq rl' handle THM _ =>
      if can Logic.dest_equals (Thm.concl_of rl') then rl'
      else error "Conclusion of congruence rules must be =-equality"
  end |> zero_var_indexes;

fun mk_atomize ctxt pairs =
  let
    fun atoms thm =
      let
        fun res th = map (fn rl => th RS rl);   (*exception THM*)
        val thm_ctxt = Variable.declare_thm thm ctxt;
        fun res_fixed rls =
          if Thm.maxidx_of (Thm.adjust_maxidx_thm ~1 thm) = ~1 then res thm rls
          else Variable.trade (K (fn [thm'] => res thm' rls)) thm_ctxt [thm];
      in
        case Thm.concl_of thm
          of Const (\<^const_name>\<open>Trueprop\<close>, _) $ p => (case head_of p
            of Const (a, _) => (case AList.lookup (op =) pairs a
              of SOME rls => (maps atoms (res_fixed rls) handle THM _ => [thm])
              | NONE => [thm])
            | _ => [thm])
          | _ => [thm]
      end;
  in atoms end;

fun mksimps pairs ctxt = map_filter (try mk_eq) o mk_atomize ctxt pairs o Variable.gen_all ctxt;

fun unsafe_solver_tac ctxt =
  let
    val sol_thms =
      reflexive_thm :: @{thm TrueI} :: @{thm refl} :: Simplifier.prems_of ctxt;
    fun sol_tac i =
      FIRST
       [resolve_tac ctxt sol_thms i,
        assume_tac ctxt i,
        eresolve_tac ctxt @{thms FalseE} i] ORELSE
          (match_tac ctxt [@{thm conjI}]
      THEN_ALL_NEW sol_tac) i
  in
    (fn i => REPEAT_DETERM (match_tac ctxt @{thms simp_impliesI} i)) THEN' sol_tac
  end;

val unsafe_solver = mk_solver "HOL unsafe" unsafe_solver_tac;


(*No premature instantiation of variables during simplification*)
fun safe_solver_tac ctxt =
  (fn i => REPEAT_DETERM (match_tac ctxt @{thms simp_impliesI} i)) THEN'
  FIRST' [match_tac ctxt (reflexive_thm :: @{thm TrueI} :: @{thm refl} :: Simplifier.prems_of ctxt),
    eq_assume_tac, ematch_tac ctxt @{thms FalseE}];

val safe_solver = mk_solver "HOL safe" safe_solver_tac;

structure Splitter = Splitter
(
  val context = \<^context>
  val mk_eq = mk_eq
  val meta_eq_to_iff = @{thm meta_eq_to_obj_eq}
  val iffD = @{thm iffD2}
  val disjE = @{thm disjE}
  val conjE = @{thm conjE}
  val exE = @{thm exE}
  val contrapos = @{thm contrapos_nn}
  val contrapos2 = @{thm contrapos_pp}
  val notnotD = @{thm notnotD}
  val safe_tac = Classical.safe_tac
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
 [(\<^const_name>\<open>HOL.implies\<close>, [@{thm mp}]),
  (\<^const_name>\<open>HOL.conj\<close>, [@{thm conjunct1}, @{thm conjunct2}]),
  (\<^const_name>\<open>All\<close>, [@{thm spec}]),
  (\<^const_name>\<open>True\<close>, []),
  (\<^const_name>\<open>False\<close>, []),
  (\<^const_name>\<open>If\<close>, [@{thm if_bool_eq_conj} RS @{thm iffD1}])];

val HOL_basic_ss =
  empty_ss
  |> Simplifier.simpset_map \<^context> (
    Simplifier.set_safe_solver safe_solver
    #> Simplifier.set_unsafe_solver unsafe_solver
    #> Simplifier.set_subgoaler asm_simp_tac
    #> Simplifier.set_mksimps (mksimps mksimps_pairs)
    #> Simplifier.set_mkeqTrue mk_eq_True
    #> Simplifier.set_mkcong mk_meta_cong);

fun hol_simplify ctxt rews =
  full_simplify (ctxt |> Simplifier.put_simpset HOL_basic_ss |> Simplifier.add_simps rews);

fun unfold_tac ctxt ths =
  ALLGOALS (full_simp_tac
    (ctxt |> Simplifier.put_simpset HOL_basic_ss |> Simplifier.clear_simpset |> Simplifier.add_simps ths));

end;

structure Splitter = Simpdata.Splitter;
structure Clasimp = Simpdata.Clasimp;
