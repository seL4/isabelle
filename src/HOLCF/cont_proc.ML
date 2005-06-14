(*  Title:      HOLCF/cont_proc.ML
    ID:         $Id$
    Author:     Brian Huffman
*)

signature CONT_PROC =
sig
  val is_lcf_term: term -> bool
  val cont_thms: term -> thm list
  val cont_proc: theory -> simproc
  val setup: (theory -> theory) list
end;

structure ContProc: CONT_PROC =
struct

(** theory context references **)

val cont_K = thm "cont_const";
val cont_I = thm "cont_id";
val cont_A = thm "cont2cont_Rep_CFun";
val cont_L = thm "cont2cont_LAM";
val cont_R = thm "cont_Rep_CFun2";

(* checks whether a term is written entirely in the LCF sublanguage *)
fun is_lcf_term (Const("Cfun.Rep_CFun",_) $ t $ u) = is_lcf_term t andalso is_lcf_term u
  | is_lcf_term (Const("Cfun.Abs_CFun",_) $ Abs (_,_,t)) = is_lcf_term t
  | is_lcf_term (_ $ _) = false
  | is_lcf_term (Abs _) = false
  | is_lcf_term _ = true; (* Const, Free, Var, and Bound are OK *)

(*
  efficiently generates a cont thm for every LAM abstraction in a term,
  using forward proof and reusing common subgoals
*)
local
  fun var 0 = [SOME cont_I]
    | var n = NONE :: var (n-1);

  fun k NONE     = cont_K
    | k (SOME x) = x;

  fun ap NONE NONE = NONE
    | ap x    y    = SOME (k y RS (k x RS cont_A));

  fun zip []      []      = []
    | zip []      (y::ys) = (ap NONE y   ) :: zip [] ys
    | zip (x::xs) []      = (ap x    NONE) :: zip xs []
    | zip (x::xs) (y::ys) = (ap x    y   ) :: zip xs ys

  fun lam [] = ([], cont_K)
    | lam (x::ys) = let
        (* should use "standard" for thms that are used multiple times *)
        (* it seems to allow for sharing in explicit proof objects *)
        val x' = standard (k x);
        val Lx = x' RS cont_L;
        in (map (fn y => SOME (k y RS Lx)) ys, x') end;

  (* first list: cont thm for each dangling bound variable *)
  (* second list: cont thm for each LAM *)
  fun cont_thms1 (Const _ $ f $ t) = let
        val (cs1,ls1) = cont_thms1 f;
        val (cs2,ls2) = cont_thms1 t;
        in (zip cs1 cs2, ls1 @ ls2) end
    | cont_thms1 (Const _ $ Abs (_,_,t)) = let
        val (cs,ls) = cont_thms1 t;
        val (cs',l) = lam cs;
        in (cs',l::ls) end
    | cont_thms1 (Bound n) = (var n, [])
    | cont_thms1 _ = ([],[]);
in
  (* precondition: is_lcf_term t = true *)
  fun cont_thms t = snd (cont_thms1 t);
end;

(*
  Given the term "cont f", the procedure tries to construct the
  theorem "cont f == True". If this theorem cannot be completely
  solved by the introduction rules, then the procedure returns a
  conditional rewrite rule with the unsolved subgoals as premises.
*)

local
  fun solve_cont sg _ (t as Const("Cont.cont",_) $ f) =
    let
      val rules = [cont_K, cont_I, cont_R, cont_A, cont_L];
      val tr = instantiate' [] [SOME (cterm_of sg t)] Eq_TrueI;
      val f' = Const("Cfun.Abs_CFun",dummyT) $ f;
      val tac = if is_lcf_term f'
        then rtac (hd (cont_thms f')) 1
        else REPEAT_ALL_NEW (resolve_tac rules) 1;
    in Option.map fst (Seq.pull (tac tr)) end
    | solve_cont sg _ _ = NONE;
in
  fun cont_proc thy = Simplifier.simproc (Theory.sign_of thy)
        "cont_proc" ["cont f"] solve_cont;
end;

val setup =
  [fn thy => Simplifier.change_simpset_of (op addsimprocs) [cont_proc thy] thy];

end;
