(*  Title:      HOL/Tools/set_comprehension_pointfree.ML
    Author:     Felix Kuperjans, Lukas Bulwahn, TU Muenchen
    Author:     Rafal Kolanski, NICTA

Simproc for rewriting set comprehensions to pointfree expressions.
*)

signature SET_COMPREHENSION_POINTFREE =
sig
  val base_simproc : Proof.context -> cterm -> thm option
  val code_simproc : Proof.context -> cterm -> thm option
  val simproc : Proof.context -> cterm -> thm option
end

structure Set_Comprehension_Pointfree : SET_COMPREHENSION_POINTFREE =
struct

(* syntactic operations *)

fun mk_inf (t1, t2) =
  let
    val T = fastype_of t1
  in
    Const (\<^const_name>\<open>Lattices.inf_class.inf\<close>, T --> T --> T) $ t1 $ t2
  end

fun mk_sup (t1, t2) =
  let
    val T = fastype_of t1
  in
    Const (\<^const_name>\<open>Lattices.sup_class.sup\<close>, T --> T --> T) $ t1 $ t2
  end

fun mk_Compl t =
  let
    val T = fastype_of t
  in
    Const (\<^const_name>\<open>Groups.uminus_class.uminus\<close>, T --> T) $ t
  end

fun mk_image t1 t2 =
  let
    val T as Type (\<^type_name>\<open>fun\<close>, [_ , R]) = fastype_of t1
  in
    Const (\<^const_name>\<open>image\<close>,
      T --> fastype_of t2 --> HOLogic.mk_setT R) $ t1 $ t2
  end;

fun mk_sigma (t1, t2) =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val setT = HOLogic.dest_setT T1
    val resT = HOLogic.mk_setT (HOLogic.mk_prodT (setT, HOLogic.dest_setT T2))
  in
    Const (\<^const_name>\<open>Sigma\<close>,
      T1 --> (setT --> T2) --> resT) $ t1 $ absdummy setT t2
  end;

fun mk_vimage f s =
  let
    val T as Type (\<^type_name>\<open>fun\<close>, [T1, T2]) = fastype_of f
  in
    Const (\<^const_name>\<open>vimage\<close>, T --> HOLogic.mk_setT T2 --> HOLogic.mk_setT T1) $ f $ s
  end; 

fun dest_Collect (Const (\<^const_name>\<open>Collect\<close>, _) $ Abs (x, T, t)) = ((x, T), t)
  | dest_Collect t = raise TERM ("dest_Collect", [t])

(* Copied from predicate_compile_aux.ML *)
fun strip_ex (Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (x, T, t)) =
  let
    val (xTs, t') = strip_ex t
  in
    ((x, T) :: xTs, t')
  end
  | strip_ex t = ([], t)

fun mk_prod1 Ts (t1, t2) =
  let
    val (T1, T2) = apply2 (curry fastype_of1 Ts) (t1, t2)
  in
    HOLogic.pair_const T1 T2 $ t1 $ t2
  end;

fun mk_split_abs vs (Bound i) t = let val (x, T) = nth vs i in Abs (x, T, t) end
  | mk_split_abs vs (Const (\<^const_name>\<open>Product_Type.Pair\<close>, _) $ u $ v) t =
      HOLogic.mk_case_prod (mk_split_abs vs u (mk_split_abs vs v t))
  | mk_split_abs _ t _ = raise TERM ("mk_split_abs: bad term", [t]);

(* a variant of HOLogic.strip_ptupleabs *)
val strip_ptupleabs =
  let
    fun strip [] qs vs t = (t, rev vs, qs)
      | strip (p :: ps) qs vs (Const (\<^const_name>\<open>case_prod\<close>, _) $ t) =
          strip ((1 :: p) :: (2 :: p) :: ps) (p :: qs) vs t
      | strip (_ :: ps) qs vs (Abs (s, T, t)) = strip ps qs ((s, T) :: vs) t
      | strip (_ :: ps) qs vs t = strip ps qs
          ((Name.uu_, hd (binder_types (fastype_of1 (map snd vs, t)))) :: vs)
          (incr_boundvars 1 t $ Bound 0)
  in strip [[]] [] [] end;

(* patterns *)

datatype pattern = Pattern of int list

fun dest_Pattern (Pattern bs) = bs

fun dest_bound (Bound i) = i
  | dest_bound t = raise TERM("dest_bound", [t]);

fun type_of_pattern Ts (Pattern bs) = HOLogic.mk_tupleT (map (nth Ts) bs)

fun term_of_pattern Ts (Pattern bs) =
    let
      fun mk [b] = Bound b
        | mk (b :: bs) = HOLogic.pair_const (nth Ts b) (type_of_pattern Ts (Pattern bs))
           $ Bound b $ mk bs
    in mk bs end;

(* formulas *)

datatype formula = Atom of (pattern * term) | Int of formula * formula | Un of formula * formula

fun map_atom f (Atom a) = Atom (f a)
  | map_atom _ x = x

fun is_collect_atom (Atom (_, Const(\<^const_name>\<open>Collect\<close>, _) $ _)) = true
  | is_collect_atom (Atom (_, Const (\<^const_name>\<open>Groups.uminus_class.uminus\<close>, _) $ (Const(\<^const_name>\<open>Collect\<close>, _) $ _))) = true
  | is_collect_atom _ = false

fun mk_case_prod _ [(x, T)] t = (T, Abs (x, T, t))
  | mk_case_prod rT ((x, T) :: vs) t =
    let
      val (T', t') = mk_case_prod rT vs t
      val t'' = HOLogic.case_prod_const (T, T', rT) $ (Abs (x, T, t'))
    in (domain_type (fastype_of t''), t'') end

fun mk_term vs t =
  let
    val bs = loose_bnos t
    val vs' = map (nth (rev vs)) bs
    val subst = map_index (fn (i, j) => (j, Bound i)) (rev bs)
      |> sort (fn (p1, p2) => int_ord (fst p1, fst p2))
      |> (fn subst' => map (fn i => the_default (Bound i) (AList.lookup (op =) subst' i)) (0 upto (fst (snd (split_last subst')))))
    val t' = subst_bounds (subst, t)
    val tuple = Pattern bs
  in (tuple, (vs', t')) end

fun default_atom vs t =
  let
    val (tuple, (vs', t')) = mk_term vs t
    val T = HOLogic.mk_tupleT (map snd vs')
    val s = HOLogic.Collect_const T $ (snd (mk_case_prod \<^typ>\<open>bool\<close> vs' t'))
  in
    (tuple, Atom (tuple, s))
  end

fun mk_atom vs (t as Const (\<^const_name>\<open>Set.member\<close>, _) $ x $ s) =
    if not (null (loose_bnos s)) then
      default_atom vs t
    else
      (case try ((map dest_bound) o HOLogic.strip_tuple) x of
      SOME pat => (Pattern pat, Atom (Pattern pat, s))
    | NONE =>
        let
          val (tuple, (vs', x')) = mk_term vs x 
          val rT = HOLogic.dest_setT (fastype_of s)
          val s = mk_vimage (snd (mk_case_prod rT vs' x')) s
        in (tuple, Atom (tuple, s)) end)
  | mk_atom vs (Const (\<^const_name>\<open>HOL.Not\<close>, _) $ t) = apsnd (map_atom (apsnd mk_Compl)) (mk_atom vs t)
  | mk_atom vs t = default_atom vs t

fun merge' [] (pats1, pats2) = ([], (pats1, pats2))
  | merge' pat (pats, []) = (pat, (pats, []))
  | merge' pat (pats1, pats) =
  let
    fun disjoint_to_pat p = null (inter (op =) pat p)
    val overlap_pats = filter_out disjoint_to_pat pats
    val rem_pats = filter disjoint_to_pat pats
    val (pat, (pats', pats1')) = merge' (distinct (op =) (flat overlap_pats @ pat)) (rem_pats, pats1)
  in
    (pat, (pats1', pats'))
  end

fun merge ([], pats) = pats
  | merge (pat :: pats', pats) =
  let val (pat', (pats1', pats2')) = merge' pat (pats', pats)
  in pat' :: merge (pats1', pats2') end;

fun restricted_merge ([], pats) = pats
  | restricted_merge (pat :: pats', pats) =
  let
    fun disjoint_to_pat p = null (inter (op =) pat p)
    val overlap_pats = filter_out disjoint_to_pat pats
    val rem_pats = filter disjoint_to_pat pats
  in
    case overlap_pats of
      [] => pat :: restricted_merge (pats', rem_pats)
    | [pat'] => if subset (op =) (pat, pat') then
        pat' :: restricted_merge (pats', rem_pats)
      else if subset (op =) (pat', pat) then
        pat :: restricted_merge (pats', rem_pats)
      else error "restricted merge: two patterns require relational join"
    | _ => error "restricted merge: multiple patterns overlap"
  end;
  
fun map_atoms f (Atom a) = Atom (f a)
  | map_atoms f (Un (fm1, fm2)) = Un (apply2 (map_atoms f) (fm1, fm2))
  | map_atoms f (Int (fm1, fm2)) = Int (apply2 (map_atoms f) (fm1, fm2))

fun extend Ts bs t = foldr1 mk_sigma (t :: map (fn b => HOLogic.mk_UNIV (nth Ts b)) bs)

fun rearrange vs (pat, pat') t =
  let
    val subst = map_index (fn (i, b) => (b, i)) (rev pat)
    val vs' = map (nth (rev vs)) pat
    val Ts' = map snd (rev vs')
    val bs = map (fn b => the (AList.lookup (op =) subst b)) pat'
    val rt = term_of_pattern Ts' (Pattern bs)
    val rT = type_of_pattern Ts' (Pattern bs)
    val (_, f) = mk_case_prod rT vs' rt
  in
    mk_image f t
  end;

fun adjust vs pats (Pattern pat, t) =
  let
    val SOME p = find_first (fn p => not (null (inter (op =) pat p))) pats
    val missing = subtract (op =) pat p
    val Ts = rev (map snd vs)
    val t' = extend Ts missing t
  in (Pattern p, rearrange vs (pat @ missing, p) t') end

fun adjust_atoms vs pats fm = map_atoms (adjust vs pats) fm

fun merge_inter vs (pats1, fm1) (pats2, fm2) =
  let
    val pats = restricted_merge (map dest_Pattern pats1, map dest_Pattern pats2) 
    val (fm1', fm2') = apply2 (adjust_atoms vs pats) (fm1, fm2)
  in
    (map Pattern pats, Int (fm1', fm2'))
  end;

fun merge_union vs (pats1, fm1) (pats2, fm2) = 
  let
    val pats = merge (map dest_Pattern pats1, map dest_Pattern pats2)
    val (fm1', fm2') = apply2 (adjust_atoms vs pats) (fm1, fm2)
  in
    (map Pattern pats, Un (fm1', fm2'))
  end;

fun mk_formula vs \<^Const_>\<open>conj for t1 t2\<close> = merge_inter vs (mk_formula vs t1) (mk_formula vs t2)
  | mk_formula vs \<^Const_>\<open>disj for t1 t2\<close> = merge_union vs (mk_formula vs t1) (mk_formula vs t2)
  | mk_formula vs t = apfst single (mk_atom vs t)

fun strip_Int (Int (fm1, fm2)) = fm1 :: (strip_Int fm2) 
  | strip_Int fm = [fm]

(* term construction *)

fun reorder_bounds pats t =
  let
    val bounds = maps dest_Pattern pats
    val bperm = bounds ~~ ((length bounds - 1) downto 0)
      |> sort (fn (i,j) => int_ord (fst i, fst j)) |> map snd
  in
    subst_bounds (map Bound bperm, t)
  end;

fun is_reordering t =
  let val (t', _, _) = HOLogic.strip_ptupleabs t
  in forall (fn Bound _ => true) (HOLogic.strip_tuple t') end

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
      mk_formula ((x, T) :: vs) (foldr1 HOLogic.mk_conj (conjs' @ map mk_mem_UNIV unused_bounds))
    fun mk_set (Atom pt) = foldr1 mk_sigma (map (lookup pt) pats)
      | mk_set (Un (f1, f2)) = mk_sup (mk_set f1, mk_set f2)
      | mk_set (Int (f1, f2)) = mk_inf (mk_set f1, mk_set f2)
    val pat = foldr1 (mk_prod1 Ts) (map (term_of_pattern Ts) pats)
    val t = mk_split_abs (rev ((x, T) :: vs)) pat (reorder_bounds pats f)
  in
    if the_default false (try is_reordering t) andalso is_collect_atom fm then
      error "mk_pointfree_expr: trivial case" 
    else (fm, mk_image t (mk_set fm))
  end;

val rewrite_term = try mk_pointfree_expr


(* proof tactic *)

val case_prod_beta = @{lemma "case_prod g x z = case_prod (\<lambda>x y. (g x y) z) x" by (simp add: case_prod_beta)}

val vimageI2' = @{lemma "f a \<notin> A ==> a \<notin> f -` A" by simp}
val vimageE' =
  @{lemma "a \<notin> f -` B ==> (\<And> x. f a = x ==> x \<notin> B ==> P) ==> P" by simp}

val collectI' = @{lemma "\<not> P a ==> a \<notin> {x. P x}" by auto}
val collectE' = @{lemma "a \<notin> {x. P x} ==> (\<not> P a ==> Q) ==> Q" by auto}

fun elim_Collect_tac ctxt =
  dresolve_tac ctxt @{thms iffD1 [OF mem_Collect_eq]}
  THEN' (REPEAT_DETERM o (eresolve_tac ctxt @{thms exE}))
  THEN' REPEAT_DETERM o eresolve_tac ctxt @{thms conjE}
  THEN' TRY o hyp_subst_tac ctxt;

fun intro_image_tac ctxt =
  resolve_tac ctxt @{thms image_eqI}
  THEN' (REPEAT_DETERM1 o
      (resolve_tac ctxt @{thms refl}
      ORELSE' resolve_tac ctxt @{thms arg_cong2 [OF refl, where f = "(=)", OF prod.case, THEN iffD2]}
      ORELSE' CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1
        (HOLogic.Trueprop_conv
          (HOLogic.eq_conv Conv.all_conv (Conv.rewr_conv (mk_meta_eq case_prod_beta)))))) ctxt)))

fun elim_image_tac ctxt =
  eresolve_tac ctxt @{thms imageE}
  THEN' REPEAT_DETERM o CHANGED o
    (TRY o full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms split_paired_all prod.case})
    THEN' REPEAT_DETERM o eresolve_tac ctxt @{thms Pair_inject}
    THEN' TRY o hyp_subst_tac ctxt)

fun tac1_of_formula ctxt (Int (fm1, fm2)) =
    TRY o eresolve_tac ctxt @{thms conjE}
    THEN' resolve_tac ctxt @{thms IntI}
    THEN' (fn i => tac1_of_formula ctxt fm2 (i + 1))
    THEN' tac1_of_formula ctxt fm1
  | tac1_of_formula ctxt (Un (fm1, fm2)) =
    eresolve_tac ctxt @{thms disjE} THEN' resolve_tac ctxt @{thms UnI1}
    THEN' tac1_of_formula ctxt fm1
    THEN' resolve_tac ctxt @{thms UnI2}
    THEN' tac1_of_formula ctxt fm2
  | tac1_of_formula ctxt (Atom _) =
    REPEAT_DETERM1 o (assume_tac ctxt
      ORELSE' resolve_tac ctxt @{thms SigmaI}
      ORELSE' ((resolve_tac ctxt @{thms CollectI} ORELSE' resolve_tac ctxt [collectI']) THEN'
        TRY o simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm prod.case}]))
      ORELSE' ((resolve_tac ctxt @{thms vimageI2} ORELSE' resolve_tac ctxt [vimageI2']) THEN'
        TRY o simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm prod.case}]))
      ORELSE' (resolve_tac ctxt @{thms image_eqI} THEN'
    (REPEAT_DETERM o
      (resolve_tac ctxt @{thms refl}
      ORELSE' resolve_tac ctxt @{thms arg_cong2[OF refl, where f = "(=)", OF prod.case, THEN iffD2]})))
      ORELSE' resolve_tac ctxt @{thms UNIV_I}
      ORELSE' resolve_tac ctxt @{thms iffD2[OF Compl_iff]}
      ORELSE' assume_tac ctxt)

fun tac2_of_formula ctxt (Int (fm1, fm2)) =
    TRY o eresolve_tac ctxt @{thms IntE}
    THEN' TRY o resolve_tac ctxt @{thms conjI}
    THEN' (fn i => tac2_of_formula ctxt fm2 (i + 1))
    THEN' tac2_of_formula ctxt fm1
  | tac2_of_formula ctxt (Un (fm1, fm2)) =
    eresolve_tac ctxt @{thms UnE} THEN' resolve_tac ctxt @{thms disjI1}
    THEN' tac2_of_formula ctxt fm1
    THEN' resolve_tac ctxt @{thms disjI2}
    THEN' tac2_of_formula ctxt fm2
  | tac2_of_formula ctxt (Atom _) =
    REPEAT_DETERM o
      (assume_tac ctxt
       ORELSE' dresolve_tac ctxt @{thms iffD1[OF mem_Sigma_iff]}
       ORELSE' eresolve_tac ctxt @{thms conjE}
       ORELSE' ((eresolve_tac ctxt @{thms CollectE} ORELSE' eresolve_tac ctxt [collectE']) THEN'
         TRY o full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm prod.case}]) THEN'
         REPEAT_DETERM o eresolve_tac ctxt @{thms Pair_inject} THEN' TRY o hyp_subst_tac ctxt THEN'
         TRY o resolve_tac ctxt @{thms refl})
       ORELSE' (eresolve_tac ctxt @{thms imageE}
         THEN' (REPEAT_DETERM o CHANGED o
         (TRY o full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms split_paired_all prod.case})
         THEN' REPEAT_DETERM o eresolve_tac ctxt @{thms Pair_inject}
         THEN' TRY o hyp_subst_tac ctxt THEN' TRY o resolve_tac ctxt @{thms refl})))
       ORELSE' eresolve_tac ctxt @{thms ComplE}
       ORELSE' ((eresolve_tac ctxt @{thms vimageE} ORELSE' eresolve_tac ctxt [vimageE'])
        THEN' TRY o full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm prod.case}])
        THEN' TRY o hyp_subst_tac ctxt THEN' TRY o resolve_tac ctxt @{thms refl}))

fun tac ctxt fm =
  let
    val subset_tac1 = resolve_tac ctxt @{thms subsetI}
      THEN' elim_Collect_tac ctxt
      THEN' intro_image_tac ctxt
      THEN' tac1_of_formula ctxt fm
    val subset_tac2 = resolve_tac ctxt @{thms subsetI}
      THEN' elim_image_tac ctxt
      THEN' resolve_tac ctxt @{thms iffD2[OF mem_Collect_eq]}
      THEN' REPEAT_DETERM o resolve_tac ctxt @{thms exI}
      THEN' (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI}))
      THEN' (K (TRY (FIRSTGOAL ((TRY o hyp_subst_tac ctxt) THEN' resolve_tac ctxt @{thms refl}))))
      THEN' (fn i => EVERY (rev (map_index (fn (j, f) =>
        REPEAT_DETERM (eresolve_tac ctxt @{thms IntE} (i + j)) THEN
        tac2_of_formula ctxt f (i + j)) (strip_Int fm))))
  in
    resolve_tac ctxt @{thms subset_antisym} THEN' subset_tac1 THEN' subset_tac2
  end;


(* preprocessing conversion:
  rewrites {(x1, ..., xn). P x1 ... xn} to {(x1, ..., xn) | x1 ... xn. P x1 ... xn} *)

fun comprehension_conv ctxt ct =
  let
    fun dest_Collect (Const (\<^const_name>\<open>Collect\<close>, T) $ t) = (HOLogic.dest_setT (body_type T), t)
      | dest_Collect t = raise TERM ("dest_Collect", [t])
    fun list_ex vs t = fold_rev (fn (x, T) => fn t => HOLogic.exists_const T $ Abs (x, T, t)) vs t
    fun mk_term t =
      let
        val (T, t') = dest_Collect t
        val (t'', vs, fp) = case strip_ptupleabs t' of
            (_, [_], _) => raise TERM("mk_term", [t'])
          | (t'', vs, fp) => (t'', vs, fp)
        val Ts = map snd vs
        val eq = HOLogic.eq_const T $ Bound (length Ts) $
          (HOLogic.mk_ptuple fp (HOLogic.mk_ptupleT fp Ts) (rev (map_index (fn (i, _) => Bound i) Ts)))
      in
        HOLogic.Collect_const T $ absdummy T (list_ex vs (HOLogic.mk_conj (eq, t'')))
      end;
    fun is_eq th = is_some (try (HOLogic.dest_eq o HOLogic.dest_Trueprop) (Thm.prop_of th))
    val unfold_thms = @{thms split_paired_all mem_Collect_eq prod.case}
    fun tac ctxt = 
      resolve_tac ctxt @{thms set_eqI}
      THEN' simp_tac (put_simpset HOL_basic_ss ctxt addsimps unfold_thms)
      THEN' resolve_tac ctxt @{thms iffI}
      THEN' REPEAT_DETERM o resolve_tac ctxt @{thms exI}
      THEN' resolve_tac ctxt @{thms conjI} THEN' resolve_tac ctxt @{thms refl} THEN' assume_tac ctxt
      THEN' REPEAT_DETERM o eresolve_tac ctxt @{thms exE}
      THEN' eresolve_tac ctxt @{thms conjE}
      THEN' REPEAT_DETERM o eresolve_tac ctxt @{thms Pair_inject}
      THEN' Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
        simp_tac (put_simpset HOL_basic_ss ctxt' addsimps (filter is_eq prems)) 1) ctxt
      THEN' TRY o assume_tac ctxt
  in
    case try mk_term (Thm.term_of ct) of
      NONE => Thm.reflexive ct
    | SOME t' =>
      Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (Thm.term_of ct, t')))
          (fn {context, ...} => tac context 1)
        RS @{thm eq_reflection}
  end


(* main simprocs *)

val prep_thms =
  map mk_meta_eq ([@{thm Bex_def}, @{thm Pow_iff[symmetric]}] @ @{thms ex_simps[symmetric]})

val post_thms =
  map mk_meta_eq [@{thm Times_Un_distrib1[symmetric]},
  @{lemma "A \<times> B \<union> A \<times> C = A \<times> (B \<union> C)" by auto},
  @{lemma "(A \<times> B \<inter> C \<times> D) = (A \<inter> C) \<times> (B \<inter> D)" by auto}]

fun conv ctxt t =
  let
    val (t', ctxt') = yield_singleton (Variable.import_terms true) t (Variable.declare_term t ctxt)
    val ct = Thm.cterm_of ctxt' t'
    fun unfold_conv thms =
      Raw_Simplifier.rewrite_cterm (false, false, false) (K (K NONE))
        (empty_simpset ctxt' addsimps thms)
    val prep_eq = (comprehension_conv ctxt' then_conv unfold_conv prep_thms) ct
    val t'' = Thm.term_of (Thm.rhs_of prep_eq)
    fun mk_thm (fm, t''') = Goal.prove ctxt' [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (t'', t'''))) (fn {context, ...} => tac context fm 1)
    fun unfold th = th RS (HOLogic.mk_obj_eq prep_eq RS @{thm trans})
    val post =
      Conv.fconv_rule
        (HOLogic.Trueprop_conv (HOLogic.eq_conv Conv.all_conv (unfold_conv post_thms)))
    val export = singleton (Variable.export ctxt' ctxt)
  in
    Option.map (export o post o unfold o mk_thm) (rewrite_term t'')
  end;

fun base_simproc ctxt redex =
  let
    val set_compr = Thm.term_of redex
  in
    conv ctxt set_compr
    |> Option.map (fn thm => thm RS @{thm eq_reflection})
  end;

fun instantiate_arg_cong ctxt pred =
  let
    val arg_cong = Thm.incr_indexes (maxidx_of_term pred + 1) @{thm arg_cong}
    val (Var (f, _) $ _, _) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.concl_of arg_cong))
  in
    infer_instantiate ctxt [(f, Thm.cterm_of ctxt pred)] arg_cong
  end;

fun simproc ctxt redex =
  let
    val pred $ set_compr = Thm.term_of redex
    val arg_cong' = instantiate_arg_cong ctxt pred
  in
    conv ctxt set_compr
    |> Option.map (fn thm => thm RS arg_cong' RS @{thm eq_reflection})
  end;

fun code_simproc ctxt redex =
  let
    fun unfold_conv thms =
      Raw_Simplifier.rewrite_cterm (false, false, false) (K (K NONE))
        (empty_simpset ctxt addsimps thms)
    val prep_thm = unfold_conv @{thms eq_equal[symmetric]} redex
  in
    case base_simproc ctxt (Thm.rhs_of prep_thm) of
      SOME rewr_thm => SOME (transitive_thm OF [transitive_thm OF [prep_thm, rewr_thm],
        unfold_conv @{thms eq_equal} (Thm.rhs_of rewr_thm)])
    | NONE => NONE
  end;

end;
