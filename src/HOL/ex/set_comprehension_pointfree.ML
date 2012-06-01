(*  Title:      HOL/Tools/set_comprehension_pointfree.ML
    Author:     Felix Kuperjans, Lukas Bulwahn, TU Muenchen

Simproc for rewriting set comprehensions to pointfree expressions.
*)

signature SET_COMPREHENSION_POINTFREE =
sig
  val simproc : morphism -> simpset -> cterm -> thm option
end

structure Set_Comprehension_Pointfree : SET_COMPREHENSION_POINTFREE =
struct

(* syntactic operations *)

fun mk_inf (t1, t2) =
  let
    val T = fastype_of t1
  in
    Const (@{const_name Lattices.inf_class.inf}, T --> T --> T) $ t1 $ t2
  end

fun mk_image t1 t2 =
  let
    val T as Type (@{type_name fun}, [_ , R]) = fastype_of t1
  in
    Const (@{const_name image}, T --> fastype_of t2 --> HOLogic.mk_setT R) $ t1 $ t2
  end;

fun mk_sigma (t1, t2) =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val setT = HOLogic.dest_setT T1
    val resultT = HOLogic.mk_setT (HOLogic.mk_prodT (setT, HOLogic.dest_setT T2))
  in
    Const (@{const_name Sigma}, T1 --> (setT --> T2) --> resultT) $ t1 $ absdummy setT t2
  end;

fun dest_Bound (Bound x) = x
  | dest_Bound t = raise TERM("dest_Bound", [t]);

fun dest_Collect (Const (@{const_name Collect}, _) $ Abs (_, _, t)) = t
  | dest_Collect t = raise TERM ("dest_Collect", [t])

(* Copied from predicate_compile_aux.ML *)
fun strip_ex (Const (@{const_name Ex}, _) $ Abs (x, T, t)) =
  let
    val (xTs, t') = strip_ex t
  in
    ((x, T) :: xTs, t')
  end
  | strip_ex t = ([], t)

fun list_tupled_abs [] f = f
  | list_tupled_abs [(n, T)] f = (Abs (n, T, f))
  | list_tupled_abs ((n, T)::v::vs) f = HOLogic.mk_split (Abs (n, T, list_tupled_abs (v::vs) f))
  
fun mk_pointfree_expr t =
  let
    val (vs, t'') = strip_ex (dest_Collect t)
    val (eq::conjs) = HOLogic.dest_conj t''
    val f = if fst (HOLogic.dest_eq eq) = Bound (length vs)
            then snd (HOLogic.dest_eq eq)
            else raise TERM("mk_pointfree_expr", [t]);
    val mems = map (apfst dest_Bound o HOLogic.dest_mem) conjs
    val grouped_mems = AList.group (op =) mems
    fun mk_grouped_unions (i, T) =
      case AList.lookup (op =) grouped_mems i of
        SOME ts => foldr1 mk_inf ts
      | NONE => HOLogic.mk_UNIV T
    val complete_sets = map mk_grouped_unions ((length vs - 1) downto 0 ~~ map snd vs)
  in
    mk_image (list_tupled_abs vs f) (foldr1 mk_sigma complete_sets)
  end;

(* proof tactic *)

(* This tactic is terribly incomplete *) 

val goal1_tac_part2 = REPEAT_ALL_NEW (CHANGED o (atac ORELSE' rtac @{thm SigmaI}))

val goal1_tac = etac @{thm CollectE}
  THEN' REPEAT1 o CHANGED o etac @{thm exE}
  THEN' REPEAT1 o CHANGED o etac @{thm conjE}
  THEN' rtac @{thm image_eqI}
  THEN' RANGE [(REPEAT o CHANGED o stac @{thm split}) THEN' goal1_tac_part2, goal1_tac_part2]

val goal2_tac = etac @{thm imageE}
  THEN' rtac @{thm CollectI}
  THEN' REPEAT o CHANGED o etac @{thm SigmaE}
  THEN' REPEAT o CHANGED o rtac @{thm exI}
  THEN' REPEAT_ALL_NEW (rtac @{thm conjI})
  THEN_ALL_NEW
    (atac ORELSE'
    (asm_full_simp_tac HOL_basic_ss THEN' stac @{thm split} THEN' rtac @{thm refl}))

val tac =
  rtac @{thm set_eqI} 1
  THEN rtac @{thm iffI} 1
  THEN goal1_tac 1
  THEN goal2_tac 1

(* simproc *)

fun simproc _ ss redex =
  let
    val ctxt = Simplifier.the_context ss
    val _ $ set_compr = term_of redex
  in
    case try mk_pointfree_expr set_compr of
      NONE => NONE
    | SOME pointfree_expr =>
        SOME (Goal.prove ctxt [] []
          (HOLogic.mk_Trueprop (HOLogic.mk_eq (set_compr, pointfree_expr))) (K tac)
        RS @{thm arg_cong[of _ _ finite]} RS @{thm eq_reflection})
  end

end;
