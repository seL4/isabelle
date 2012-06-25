(*  Title:      HOL/Tools/set_comprehension_pointfree.ML
    Author:     Felix Kuperjans, Lukas Bulwahn, TU Muenchen
    Author:     Rafal Kolanski, NICTA

Simproc for rewriting set comprehensions to pointfree expressions.
*)

signature SET_COMPREHENSION_POINTFREE =
sig
  val simproc : simpset -> cterm -> thm option
  val rewrite_term : term -> term option
  val conv : Proof.context -> term -> thm option
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
    Const (@{const_name image},
      T --> fastype_of t2 --> HOLogic.mk_setT R) $ t1 $ t2
  end;

fun mk_sigma (t1, t2) =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val setT = HOLogic.dest_setT T1
    val resT = HOLogic.mk_setT (HOLogic.mk_prodT (setT, HOLogic.dest_setT T2))
  in
    Const (@{const_name Sigma},
      T1 --> (setT --> T2) --> resT) $ t1 $ absdummy setT t2
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
  | list_tupled_abs ((n, T)::v::vs) f =
      HOLogic.mk_split (Abs (n, T, list_tupled_abs (v::vs) f))

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

val rewrite_term = try mk_pointfree_expr

(* proof tactic *)

(* Tactic works for arbitrary number of m : S conjuncts *)

val dest_Collect_tac = dtac @{thm iffD1[OF mem_Collect_eq]}
  THEN' (REPEAT_DETERM o (eresolve_tac @{thms exE conjE}))
  THEN' hyp_subst_tac;

val intro_image_Sigma_tac = rtac @{thm image_eqI}
    THEN' (REPEAT_DETERM1 o
      (rtac @{thm refl}
      ORELSE' rtac
        @{thm arg_cong2[OF refl, where f="op =", OF prod.cases, THEN iffD2]}));

val dest_image_Sigma_tac = etac @{thm imageE}
  THEN' (TRY o REPEAT_DETERM1 o Splitter.split_asm_tac @{thms prod.split_asm})
  THEN' hyp_subst_tac
  THEN' (TRY o REPEAT_DETERM1 o
    (etac @{thm conjE} ORELSE' dtac @{thm iffD1[OF mem_Sigma_iff]}));

val intro_Collect_tac = rtac @{thm iffD2[OF mem_Collect_eq]}
  THEN' REPEAT_DETERM1 o resolve_tac @{thms exI}
  THEN' (TRY o (rtac @{thm conjI}))
  THEN' (TRY o hyp_subst_tac)
  THEN' rtac @{thm refl};

val tac =
  let
    val subset_tac1 = rtac @{thm subsetI}
      THEN' dest_Collect_tac
      THEN' intro_image_Sigma_tac
      THEN' (REPEAT_DETERM1 o
        (rtac @{thm SigmaI}
        ORELSE' rtac @{thm UNIV_I}
        ORELSE' rtac @{thm IntI}
        ORELSE' atac));

    val subset_tac2 = rtac @{thm subsetI}
      THEN' dest_image_Sigma_tac
      THEN' intro_Collect_tac
      THEN' REPEAT_DETERM o
        (rtac @{thm conjI}
        ORELSE' eresolve_tac @{thms IntD1 IntD2}
        ORELSE' atac);
  in
    rtac @{thm subset_antisym} THEN' subset_tac1 THEN' subset_tac2
  end;

fun conv ctxt t =
  let
    fun mk_thm t' = Goal.prove ctxt [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t'))) (K (tac 1));
  in
    Option.map mk_thm (rewrite_term t)
  end;

(* simproc *)

fun simproc ss redex =
  let
    val ctxt = Simplifier.the_context ss
    val _ $ set_compr = term_of redex
  in
    conv ctxt set_compr
    |> Option.map (fn thm =>
         thm RS @{thm arg_cong[of _ _ finite]} RS @{thm eq_reflection})
  end;

end;

