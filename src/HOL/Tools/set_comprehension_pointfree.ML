(*  Title:      HOL/Tools/set_comprehension_pointfree.ML
    Author:     Felix Kuperjans, Lukas Bulwahn, TU Muenchen
    Author:     Rafal Kolanski, NICTA

Simproc for rewriting set comprehensions to pointfree expressions.
*)

signature SET_COMPREHENSION_POINTFREE =
sig
  val code_simproc : simpset -> cterm -> thm option
  val simproc : simpset -> cterm -> thm option
  val rewrite_term : term -> term option
  (* FIXME: function conv is not a conversion, i.e. of type cterm -> thm, MAYBE rename *)
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

fun mk_sup (t1, t2) =
  let
    val T = fastype_of t1
  in
    Const (@{const_name Lattices.sup_class.sup}, T --> T --> T) $ t1 $ t2
  end

fun mk_Compl t =
  let
    val T = fastype_of t
  in
    Const (@{const_name "Groups.uminus_class.uminus"}, T --> T) $ t
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
    val conjs = HOLogic.dest_conj t''
    val is_the_eq =
      the_default false o (try (fn eq => fst (HOLogic.dest_eq eq) = Bound (length vs)))
    val SOME eq = find_first is_the_eq conjs
    val f = snd (HOLogic.dest_eq eq)
    val conjs' = filter_out (fn t => eq = t) conjs
    val mems = map (apfst dest_Bound o HOLogic.dest_mem) conjs'
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
  THEN' (TRY o REPEAT_ALL_NEW (rtac @{thm conjI}))
  THEN' (K (ALLGOALS (TRY o ((TRY o hyp_subst_tac) THEN' rtac @{thm refl}))))

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
      THEN' REPEAT_DETERM o (eresolve_tac @{thms IntD1 IntD2} ORELSE' atac);
  in
    rtac @{thm subset_antisym} THEN' subset_tac1 THEN' subset_tac2
  end;

fun conv ctxt t =
  let
    val ct = cterm_of (Proof_Context.theory_of ctxt) t
    val Bex_def = mk_meta_eq @{thm Bex_def}
    val unfold_eq = Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv Bex_def))) ctxt ct
    val t' = term_of (Thm.rhs_of unfold_eq) 
    fun mk_thm t'' = Goal.prove ctxt [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (t', t''))) (K (tac 1))
    fun unfold th = th RS ((unfold_eq RS meta_eq_to_obj_eq) RS @{thm trans})
  in
    Option.map (unfold o mk_thm) (rewrite_term t')
  end;

(* simproc *)

fun base_simproc ss redex =
  let
    val ctxt = Simplifier.the_context ss
    val set_compr = term_of redex
  in
    conv ctxt set_compr
    |> Option.map (fn thm => thm RS @{thm eq_reflection})
  end;

fun instantiate_arg_cong ctxt pred =
  let
    val certify = cterm_of (Proof_Context.theory_of ctxt)
    val arg_cong = @{thm arg_cong}
    val f $ _ = fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (concl_of arg_cong)))
  in
    cterm_instantiate [(certify f, certify pred)] arg_cong
  end;

fun simproc ss redex =
  let
    val ctxt = Simplifier.the_context ss
    val pred $ set_compr = term_of redex
    val arg_cong' = instantiate_arg_cong ctxt pred
  in
    conv ctxt set_compr
    |> Option.map (fn thm => thm RS arg_cong' RS @{thm eq_reflection})
  end;

fun code_simproc ss redex =
  let
    val prep_thm = Raw_Simplifier.rewrite false @{thms eq_equal[symmetric]} redex
  in
    case base_simproc ss (Thm.rhs_of prep_thm) of
      SOME rewr_thm => SOME (transitive_thm OF [transitive_thm OF [prep_thm, rewr_thm],
        Raw_Simplifier.rewrite false @{thms eq_equal} (Thm.rhs_of rewr_thm)])
    | NONE => NONE
  end;

end;

