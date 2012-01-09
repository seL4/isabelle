(*  Title:      HOL/HOLCF/Tools/cont_proc.ML
    Author:     Brian Huffman
*)

signature CONT_PROC =
sig
  val is_lcf_term: term -> bool
  val cont_thms: term -> thm list
  val all_cont_thms: term -> thm list
  val cont_tac: int -> tactic
  val cont_proc: theory -> simproc
  val setup: theory -> theory
end

structure ContProc : CONT_PROC =
struct

(** theory context references **)

val cont_K = @{thm cont_const}
val cont_I = @{thm cont_id}
val cont_A = @{thm cont2cont_APP}
val cont_L = @{thm cont2cont_LAM}
val cont_R = @{thm cont_Rep_cfun2}

(* checks whether a term is written entirely in the LCF sublanguage *)
fun is_lcf_term (Const (@{const_name Rep_cfun}, _) $ t $ u) =
      is_lcf_term t andalso is_lcf_term u
  | is_lcf_term (Const (@{const_name Abs_cfun}, _) $ Abs (_, _, t)) =
      is_lcf_term t
  | is_lcf_term (Const (@{const_name Abs_cfun}, _) $ t) =
      is_lcf_term (Term.incr_boundvars 1 t $ Bound 0)
  | is_lcf_term (Bound _) = true
  | is_lcf_term t = not (Term.is_open t)

(*
  efficiently generates a cont thm for every LAM abstraction in a term,
  using forward proof and reusing common subgoals
*)
local
  fun var 0 = [SOME cont_I]
    | var n = NONE :: var (n-1)

  fun k NONE     = cont_K
    | k (SOME x) = x

  fun ap NONE NONE = NONE
    | ap x    y    = SOME (k y RS (k x RS cont_A))

  fun zip []      []      = []
    | zip []      (y::ys) = (ap NONE y   ) :: zip [] ys
    | zip (x::xs) []      = (ap x    NONE) :: zip xs []
    | zip (x::xs) (y::ys) = (ap x    y   ) :: zip xs ys

  fun lam [] = ([], cont_K)
    | lam (x::ys) =
    let
      (* should use "close_derivation" for thms that are used multiple times *)
      (* it seems to allow for sharing in explicit proof objects *)
      val x' = Thm.close_derivation (k x)
      val Lx = x' RS cont_L
    in (map (fn y => SOME (k y RS Lx)) ys, x') end

  (* first list: cont thm for each dangling bound variable *)
  (* second list: cont thm for each LAM in t *)
  (* if b = false, only return cont thm for outermost LAMs *)
  fun cont_thms1 b (Const (@{const_name Rep_cfun}, _) $ f $ t) =
    let
      val (cs1,ls1) = cont_thms1 b f
      val (cs2,ls2) = cont_thms1 b t
    in (zip cs1 cs2, if b then ls1 @ ls2 else []) end
    | cont_thms1 b (Const (@{const_name Abs_cfun}, _) $ Abs (_, _, t)) =
    let
      val (cs, ls) = cont_thms1 b t
      val (cs', l) = lam cs
    in (cs', l::ls) end
    | cont_thms1 b (Const (@{const_name Abs_cfun}, _) $ t) =
    let
      val t' = Term.incr_boundvars 1 t $ Bound 0
      val (cs, ls) = cont_thms1 b t'
      val (cs', l) = lam cs
    in (cs', l::ls) end
    | cont_thms1 _ (Bound n) = (var n, [])
    | cont_thms1 _ _ = ([], [])
in
  (* precondition: is_lcf_term t = true *)
  fun cont_thms t = snd (cont_thms1 false t)
  fun all_cont_thms t = snd (cont_thms1 true t)
end

(*
  Given the term "cont f", the procedure tries to construct the
  theorem "cont f == True". If this theorem cannot be completely
  solved by the introduction rules, then the procedure returns a
  conditional rewrite rule with the unsolved subgoals as premises.
*)

val cont_tac =
  let
    val rules = [cont_K, cont_I, cont_R, cont_A, cont_L]
  
    fun new_cont_tac f' i =
      case all_cont_thms f' of
        [] => no_tac
      | (c::_) => rtac c i

    fun cont_tac_of_term (Const (@{const_name cont}, _) $ f) =
      let
        val f' = Const (@{const_name Abs_cfun}, dummyT) $ f
      in
        if is_lcf_term f'
        then new_cont_tac f'
        else REPEAT_ALL_NEW (resolve_tac rules)
      end
      | cont_tac_of_term _ = K no_tac
  in
    SUBGOAL (fn (t, i) =>
      cont_tac_of_term (HOLogic.dest_Trueprop t) i)
  end

local
  fun solve_cont thy _ t =
    let
      val tr = instantiate' [] [SOME (cterm_of thy t)] @{thm Eq_TrueI}
    in Option.map fst (Seq.pull (cont_tac 1 tr)) end
in
  fun cont_proc thy =
    Simplifier.simproc_global thy "cont_proc" ["cont f"] solve_cont
end

fun setup thy = Simplifier.map_simpset_global (fn ss => ss addsimprocs [cont_proc thy]) thy

end
