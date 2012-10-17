(*  Title:      HOL/Tools/set_comprehension_pointfree.ML
    Author:     Felix Kuperjans, Lukas Bulwahn, TU Muenchen
    Author:     Rafal Kolanski, NICTA

Simproc for rewriting set comprehensions to pointfree expressions.
*)

signature SET_COMPREHENSION_POINTFREE =
sig
  val base_simproc : simpset -> cterm -> thm option
  val code_simproc : simpset -> cterm -> thm option
  val simproc : simpset -> cterm -> thm option
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

fun mk_vimage f s =
  let
    val T as Type (@{type_name fun}, [T1, T2]) = fastype_of f
  in
    Const (@{const_name vimage}, T --> HOLogic.mk_setT T2 --> HOLogic.mk_setT T1) $ f $ s
  end; 

fun dest_Collect (Const (@{const_name Collect}, _) $ Abs (x, T, t)) = ((x, T), t)
  | dest_Collect t = raise TERM ("dest_Collect", [t])

(* Copied from predicate_compile_aux.ML *)
fun strip_ex (Const (@{const_name Ex}, _) $ Abs (x, T, t)) =
  let
    val (xTs, t') = strip_ex t
  in
    ((x, T) :: xTs, t')
  end
  | strip_ex t = ([], t)

fun mk_prod1 Ts (t1, t2) =
  let
    val (T1, T2) = pairself (curry fastype_of1 Ts) (t1, t2)
  in
    HOLogic.pair_const T1 T2 $ t1 $ t2
  end;

fun mk_split_abs vs (Bound i) t = let val (x, T) = nth vs i in Abs (x, T, t) end
  | mk_split_abs vs (Const ("Product_Type.Pair", _) $ u $ v) t =
      HOLogic.mk_split (mk_split_abs vs u (mk_split_abs vs v t))
  | mk_split_abs _ t _ = raise TERM ("mk_split_abs: bad term", [t]);


(* patterns *)

datatype pattern = TBound of int | TPair of pattern * pattern;

fun mk_pattern (Bound n) = TBound n
  | mk_pattern (Const (@{const_name "Product_Type.Pair"}, _) $ l $ r) =
      TPair (mk_pattern l, mk_pattern r)
  | mk_pattern t = raise TERM ("mk_pattern: only bound variable tuples currently supported", [t]);

fun type_of_pattern Ts (TBound n) = nth Ts n
  | type_of_pattern Ts (TPair (l, r)) = HOLogic.mk_prodT (type_of_pattern Ts l, type_of_pattern Ts r)

fun term_of_pattern _ (TBound n) = Bound n
  | term_of_pattern Ts (TPair (l, r)) =
    let
      val (lt, rt) = pairself (term_of_pattern Ts) (l, r)
      val (lT, rT) = pairself (curry fastype_of1 Ts) (lt, rt) 
    in
      HOLogic.pair_const lT rT $ lt $ rt
    end;

fun bounds_of_pattern (TBound i) = [i]
  | bounds_of_pattern (TPair (l, r)) = union (op =) (bounds_of_pattern l) (bounds_of_pattern r)


(* formulas *)

datatype formula = Atom of (pattern * term) | Int of formula * formula | Un of formula * formula

fun mk_atom vs (Const (@{const_name "Set.member"}, _) $ x $ s) =
    (case try mk_pattern x of
      SOME pat => (pat, Atom (pat, s))
    | NONE =>
      let
        val bs = loose_bnos x
        val vs' = map (nth (rev vs)) bs
        val x' = subst_atomic (map_index (fn (i, j) => (Bound j, Bound i)) (rev bs)) x
        val tuple = foldr1 TPair (map TBound bs)
        val rT = HOLogic.dest_setT (fastype_of s)
        fun mk_split [(x, T)] t = (T, Abs (x, T, t))
          | mk_split ((x, T) :: vs) t =
              let
                val (T', t') = mk_split vs t
                val t'' = HOLogic.split_const (T, T', rT) $ (Abs (x, T, t'))
              in (domain_type (fastype_of t''), t'') end
        val (_, f) = mk_split vs' x'
      in (tuple, Atom (tuple, mk_vimage f s)) end)
  | mk_atom _ (Const (@{const_name "HOL.Not"}, _) $ (Const (@{const_name "Set.member"}, _) $ x $ s)) =
      (mk_pattern x, Atom (mk_pattern x, mk_Compl s))

fun can_merge (pats1, pats2) =
  let
    fun check pat1 pat2 = (pat1 = pat2)
      orelse (inter (op =) (bounds_of_pattern pat1) (bounds_of_pattern pat2) = [])
  in
    forall (fn pat1 => forall (fn pat2 => check pat1 pat2) pats2) pats1 
  end

fun merge_patterns (pats1, pats2) =
  if can_merge (pats1, pats2) then
    union (op =) pats1 pats2
  else raise Fail "merge_patterns: variable groups overlap"

fun merge oper (pats1, sp1) (pats2, sp2) = (merge_patterns (pats1, pats2), oper (sp1, sp2))

fun mk_formula vs (@{const HOL.conj} $ t1 $ t2) = merge Int (mk_formula vs t1) (mk_formula vs t2)
  | mk_formula vs (@{const HOL.disj} $ t1 $ t2) = merge Un (mk_formula vs t1) (mk_formula vs t2)
  | mk_formula vs t = apfst single (mk_atom vs t)

fun strip_Int (Int (fm1, fm2)) = fm1 :: (strip_Int fm2) 
  | strip_Int fm = [fm]

(* term construction *)

fun reorder_bounds pats t =
  let
    val bounds = maps bounds_of_pattern pats
    val bperm = bounds ~~ ((length bounds - 1) downto 0)
      |> sort (fn (i,j) => int_ord (fst i, fst j)) |> map snd
  in
    subst_bounds (map Bound bperm, t)
  end;

fun mk_pointfree_expr t =
  let
    val ((x, T), (vs, t'')) = apsnd strip_ex (dest_Collect t)
    val Ts = map snd (rev vs)
    fun mk_mem_UNIV n = HOLogic.mk_mem (Bound n, HOLogic.mk_UNIV (nth Ts n))
    fun lookup (pat', t) pat = if pat = pat' then t else HOLogic.mk_UNIV (type_of_pattern Ts pat)
    val conjs = HOLogic.dest_conj t''
    val refl = HOLogic.eq_const T $ Bound (length vs) $ Bound (length vs)
    val is_the_eq =
      the_default false o (try (fn eq => fst (HOLogic.dest_eq eq) = Bound (length vs)))
    val eq = the_default refl (find_first is_the_eq conjs)
    val f = snd (HOLogic.dest_eq eq)
    val conjs' = filter_out (fn t => eq = t) conjs
    val unused_bounds = subtract (op =) (distinct (op =) (maps loose_bnos conjs'))
      (0 upto (length vs - 1))
    val (pats, fm) =
      mk_formula vs (foldr1 HOLogic.mk_conj (conjs' @ map mk_mem_UNIV unused_bounds))
    fun mk_set (Atom pt) = (case map (lookup pt) pats of [t'] => t' | ts => foldr1 mk_sigma ts)
      | mk_set (Un (f1, f2)) = mk_sup (mk_set f1, mk_set f2)
      | mk_set (Int (f1, f2)) = mk_inf (mk_set f1, mk_set f2)
    val pat = foldr1 (mk_prod1 Ts) (map (term_of_pattern Ts) pats)
    val t = mk_split_abs (rev ((x, T) :: vs)) pat (reorder_bounds pats f)
  in
    (fm, mk_image t (mk_set fm))
  end;

val rewrite_term = try mk_pointfree_expr


(* proof tactic *)

val prod_case_distrib = @{lemma "(prod_case g x) z = prod_case (% x y. (g x y) z) x" by (simp add: prod_case_beta)}

(* FIXME: one of many clones *)
fun Trueprop_conv cv ct =
  (case Thm.term_of ct of
    Const (@{const_name Trueprop}, _) $ _ => Conv.arg_conv cv ct
  | _ => raise CTERM ("Trueprop_conv", [ct]))

(* FIXME: another clone *)
fun eq_conv cv1 cv2 ct =
  (case Thm.term_of ct of
    Const (@{const_name HOL.eq}, _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv1) cv2 ct
  | _ => raise CTERM ("eq_conv", [ct]))

val elim_Collect_tac = dtac @{thm iffD1[OF mem_Collect_eq]}
  THEN' (REPEAT_DETERM o (eresolve_tac @{thms exE}))
  THEN' TRY o etac @{thm conjE}
  THEN' TRY o hyp_subst_tac;

fun intro_image_tac ctxt = rtac @{thm image_eqI}
    THEN' (REPEAT_DETERM1 o
      (rtac @{thm refl}
      ORELSE' rtac
        @{thm arg_cong2[OF refl, where f="op =", OF prod.cases, THEN iffD2]}
      ORELSE' CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1
        (Trueprop_conv (eq_conv Conv.all_conv (Conv.rewr_conv (mk_meta_eq prod_case_distrib)))))) ctxt)))

val elim_image_tac = etac @{thm imageE}
  THEN' (TRY o REPEAT_DETERM1 o Splitter.split_asm_tac @{thms prod.split_asm})
  THEN' hyp_subst_tac

fun tac1_of_formula (Int (fm1, fm2)) =
    TRY o etac @{thm conjE}
    THEN' rtac @{thm IntI}
    THEN' (fn i => tac1_of_formula fm2 (i + 1))
    THEN' tac1_of_formula fm1
  | tac1_of_formula (Un (fm1, fm2)) =
    etac @{thm disjE} THEN' rtac @{thm UnI1}
    THEN' tac1_of_formula fm1
    THEN' rtac @{thm UnI2}
    THEN' tac1_of_formula fm2
  | tac1_of_formula (Atom _) =
    REPEAT_DETERM1 o (rtac @{thm SigmaI}
      ORELSE' (rtac @{thm vimageI2} THEN'
        TRY o Simplifier.simp_tac (HOL_basic_ss addsimps [@{thm prod.cases}])) 
      ORELSE' rtac @{thm UNIV_I}
      ORELSE' rtac @{thm iffD2[OF Compl_iff]}
      ORELSE' atac)

fun tac2_of_formula (Int (fm1, fm2)) =
    TRY o etac @{thm IntE}
    THEN' TRY o rtac @{thm conjI}
    THEN' (fn i => tac2_of_formula fm2 (i + 1))
    THEN' tac2_of_formula fm1
  | tac2_of_formula (Un (fm1, fm2)) =
    etac @{thm UnE} THEN' rtac @{thm disjI1}
    THEN' tac2_of_formula fm1
    THEN' rtac @{thm disjI2}
    THEN' tac2_of_formula fm2
  | tac2_of_formula (Atom _) =
    TRY o REPEAT_DETERM1 o
      (dtac @{thm iffD1[OF mem_Sigma_iff]}
       ORELSE' etac @{thm conjE}
       ORELSE' (etac @{thm vimageE}
        THEN' TRY o Simplifier.full_simp_tac (HOL_basic_ss addsimps [@{thm prod.cases}])
        THEN' TRY o hyp_subst_tac)
       ORELSE' etac @{thm ComplE}
       ORELSE' atac)

fun tac ctxt fm =
  let
    val subset_tac1 = rtac @{thm subsetI}
      THEN' elim_Collect_tac
      THEN' (intro_image_tac ctxt)
      THEN' (tac1_of_formula fm)
    val subset_tac2 = rtac @{thm subsetI}
      THEN' elim_image_tac
      THEN' rtac @{thm iffD2[OF mem_Collect_eq]}
      THEN' REPEAT_DETERM o resolve_tac @{thms exI}
      THEN' (TRY o REPEAT_ALL_NEW (rtac @{thm conjI}))
      THEN' (K (TRY (SOMEGOAL ((TRY o hyp_subst_tac) THEN' rtac @{thm refl}))))
      THEN' (fn i => EVERY (rev (map_index (fn (j, f) =>
        REPEAT_DETERM (etac @{thm IntE} (i + j)) THEN tac2_of_formula f (i + j)) (strip_Int fm))))
  in
    rtac @{thm subset_antisym} THEN' subset_tac1 THEN' subset_tac2
  end;


(* preprocessing conversion:
  rewrites {(x1, ..., xn). P x1 ... xn} to {(x1, ..., xn) | x1 ... xn. P x1 ... xn} *)

fun comprehension_conv ctxt ct =
let
  fun dest_Collect (Const (@{const_name Collect}, T) $ t) = (HOLogic.dest_setT (body_type T), t)
    | dest_Collect t = raise TERM ("dest_Collect", [t])
  fun list_ex Ts t = fold_rev (fn T => fn t => HOLogic.exists_const T $ absdummy T t) Ts t
  fun mk_term t =
    let
      val (T, t') = dest_Collect t
      val (t'', Ts, fp) = case HOLogic.strip_psplits t' of
          (_, [_], _) => raise TERM("mk_term", [t'])
        | (t'', Ts, fp) => (t'', Ts, fp)
      val eq = HOLogic.eq_const T $ Bound (length Ts) $
        (HOLogic.mk_ptuple fp (HOLogic.mk_ptupleT fp Ts) (rev (map_index (fn (i, _) => Bound i) Ts)))
    in
      HOLogic.Collect_const T $ absdummy T (list_ex Ts (HOLogic.mk_conj (eq, t'')))
    end;
  val tac = 
    rtac @{thm set_eqI}
    THEN' Simplifier.simp_tac
      (HOL_basic_ss addsimps [@{thm split_paired_all}, @{thm mem_Collect_eq}, @{thm prod.cases}])
    THEN' rtac @{thm iffI}
    THEN' REPEAT_DETERM o rtac @{thm exI}
    THEN' rtac @{thm conjI} THEN' rtac @{thm refl} THEN' atac
    THEN' REPEAT_DETERM o etac @{thm exE}
    THEN' etac @{thm conjE}
    THEN' REPEAT_DETERM o etac @{thm Pair_inject}
    THEN' hyp_subst_tac THEN' atac
in
  case try mk_term (term_of ct) of
    NONE => Thm.reflexive ct
  | SOME t' =>
     Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (term_of ct, t'))) (K (tac 1))
       RS @{thm eq_reflection}
end


(* main simprocs *)

val prep_thms = map mk_meta_eq [@{thm Bex_def}, @{thm Pow_iff[symmetric]}]

val post_thms =
  map mk_meta_eq [@{thm Times_Un_distrib1[symmetric]},
  @{lemma "A \<times> B \<union> A \<times> C = A \<times> (B \<union> C)" by auto},
  @{lemma "(A \<times> B \<inter> C \<times> D) = (A \<inter> C) \<times> (B \<inter> D)" by auto}]

fun conv ctxt t =
  let
    val ct = cterm_of (Proof_Context.theory_of ctxt) t
    val prep_eq = (comprehension_conv ctxt then_conv Raw_Simplifier.rewrite true prep_thms) ct
    val t' = term_of (Thm.rhs_of prep_eq)
    fun mk_thm (fm, t'') = Goal.prove ctxt [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (t', t''))) (fn {context, ...} => tac context fm 1)
    fun unfold th = th RS ((prep_eq RS meta_eq_to_obj_eq) RS @{thm trans})
    fun post th = Conv.fconv_rule (Trueprop_conv (eq_conv Conv.all_conv
      (Raw_Simplifier.rewrite true post_thms))) th
  in
    Option.map (post o unfold o mk_thm) (rewrite_term t')
  end;

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
    val arg_cong = Thm.incr_indexes (maxidx_of_term pred + 1) @{thm arg_cong}
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

