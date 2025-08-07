(*  Title:      HOL/Analysis/metric_arith.ML
    Author:     Maximilian Schäffeler (port from HOL Light)

A decision procedure for metric spaces.
*)

signature METRIC_ARITH =
sig
  val trace: bool Config.T
  val argo_timeout: real Config.T
  val metric_arith_tac : Proof.context -> int -> tactic
end

structure Metric_Arith : METRIC_ARITH =
struct

(* apply f to both cterms in ct_pair, merge results *)
fun app_union_ct_pair f ct_pair = uncurry (union (op aconvc)) (apply2 f ct_pair)

val trace = Attrib.setup_config_bool \<^binding>\<open>metric_trace\<close> (K false)

fun trace_tac ctxt msg =
  if Config.get ctxt trace then print_tac ctxt msg else all_tac

val argo_timeout = Attrib.setup_config_real \<^binding>\<open>metric_argo_timeout\<close> (K 20.0)

fun argo_ctxt ctxt =
  let
    val ctxt1 =
      if Config.get ctxt trace
      then Config.map (Argo_Tactic.trace) (K "basic") ctxt
      else ctxt
  in Config.put Argo_Tactic.timeout (Config.get ctxt1 argo_timeout) ctxt1 end

fun free_in v t =
  Term.exists_subterm (fn u => u aconv Thm.term_of v) (Thm.term_of t);

(* build a cterm set with elements cts of type ty *)
fun mk_ct_set ctxt ty =
  map Thm.term_of #>
  HOLogic.mk_set ty #>
  Thm.cterm_of ctxt

fun prenex_tac ctxt =
  let
    val prenex_simps = Proof_Context.get_thms ctxt @{named_theorems metric_prenex}
    val prenex_ctxt = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps prenex_simps
  in
    simp_tac prenex_ctxt THEN'
    K (trace_tac ctxt "Prenex form")
  end

fun nnf_tac ctxt =
  let
    val nnf_simps = Proof_Context.get_thms ctxt @{named_theorems metric_nnf}
    val nnf_ctxt = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps nnf_simps
  in
    simp_tac nnf_ctxt THEN'
    K (trace_tac ctxt "NNF form")
  end

fun unfold_tac ctxt =
  asm_full_simp_tac (put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps (Proof_Context.get_thms ctxt @{named_theorems metric_unfold}))

fun pre_arith_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps (Proof_Context.get_thms ctxt @{named_theorems metric_pre_arith})) THEN'
    K (trace_tac ctxt "Prepared for decision procedure")

fun dist_refl_sym_tac ctxt =
  let
    val refl_sym_simps = @{thms dist_self dist_commute add_0_right add_0_left simp_thms}
    val refl_sym_ctxt = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps refl_sym_simps
  in
    simp_tac refl_sym_ctxt THEN'
    K (trace_tac ctxt ("Simplified using " ^ @{make_string} refl_sym_simps))
  end

fun is_exists \<^Const_>\<open>Ex _ for _\<close> = true
  | is_exists \<^Const_>\<open>Trueprop for t\<close> = is_exists t
  | is_exists _ = false

fun is_forall \<^Const_>\<open>All _ for _\<close> = true
  | is_forall \<^Const_>\<open>Trueprop for t\<close> = is_forall t
  | is_forall _ = false


(* find all free points in ct of type metric_ty *)
fun find_points ctxt metric_ty ct =
  let
    fun find ct =
      (if Thm.typ_of_cterm ct = metric_ty then [ct] else []) @
      (case Thm.term_of ct of
        _ $ _ => app_union_ct_pair find (Thm.dest_comb ct)
      | Abs _ =>
          (*ensure the point doesn't contain the bound variable*)
          let val (x, body) = Thm.dest_abs_global ct
          in filter_out (free_in x) (find body) end
      | _ => [])
  in
    (case find ct of
      [] =>
        (*if no point can be found, invent one*)
        let
          val names = Variable.names_of ctxt |> Term.declare_free_names (Thm.term_of ct)
          val x = Free (#1 (Name.variant "x" names), metric_ty)
        in [Thm.cterm_of ctxt x] end
    | points => points)
  end

(* find all cterms "dist x y" in ct, where x and y have type metric_ty *)
fun find_dist metric_ty =
  let
    fun find ct =
      (case Thm.term_of ct of
        \<^Const_>\<open>dist T for _ _\<close> => if T = metric_ty then [ct] else []
      | _ $ _ => app_union_ct_pair find (Thm.dest_comb ct)
      | Abs _ =>
          let val (x, body) = Thm.dest_abs_global ct
          in filter_out (free_in x) (find body) end
      | _ => [])
  in find end

(* find all "x=y", where x has type metric_ty *)
fun find_eq metric_ty =
  let
    fun find ct =
      (case Thm.term_of ct of
        \<^Const_>\<open>HOL.eq T for _ _\<close> =>
          if T = metric_ty then [ct]
          else app_union_ct_pair find (Thm.dest_binop ct)
      | _ $ _ => app_union_ct_pair find (Thm.dest_comb ct)
      | Abs _ =>
          let val (x, body) = Thm.dest_abs_global ct
          in filter_out (free_in x) (find body) end
      | _ => [])
  in find end

(* rewrite ct of the form "dist x y" using maxdist_thm *)
fun maxdist_conv ctxt fset_ct ct =
  let
    val (x, y) = Thm.dest_binop ct
    val solve_prems =
      rule_by_tactic ctxt (ALLGOALS (simp_tac (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms finite.emptyI finite_insert empty_iff insert_iff})))
    val image_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms image_empty image_insert})
    val dist_refl_sym_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms dist_commute dist_self})
    val algebra_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt |> Simplifier.add_simps
        @{thms diff_self diff_0_right diff_0 abs_zero abs_minus_cancel abs_minus_commute})
    val insert_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms insert_absorb2 insert_commute})
    val sup_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms cSup_singleton Sup_insert_insert})
    val real_abs_dist_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms real_abs_dist})
    val maxdist_thm =
      \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm x\<close> and x and y and s = fset_ct in
        lemma \<open>finite s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> dist x y \<equiv> SUP a\<in>s. \<bar>dist x a - dist a y\<bar>\<close>
          for x y :: \<open>'a::metric_space\<close>
          by (fact maxdist_thm)\<close>
      |> solve_prems
  in
    ((Conv.rewr_conv maxdist_thm) then_conv
    (* SUP to Sup *)
    image_simp then_conv
    dist_refl_sym_simp then_conv
    algebra_simp then_conv
    (* eliminate duplicate terms in set *)
    insert_simp then_conv
    (* Sup to max *)
    sup_simp then_conv
    real_abs_dist_simp) ct
  end

(* rewrite ct of the form "x=y" using metric_eq_thm *)
fun metric_eq_conv ctxt fset_ct ct =
  let
    val (x, y) = Thm.dest_binop ct
    val solve_prems =
      rule_by_tactic ctxt (ALLGOALS (simp_tac (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms empty_iff insert_iff})))
    val ball_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms Set.ball_empty ball_insert})
    val dist_refl_sym_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt
        |> Simplifier.add_simps @{thms dist_commute dist_self})
    val metric_eq_thm =
      \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm x\<close> and x and y and s = fset_ct in
        lemma \<open>x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x = y \<equiv> \<forall>a\<in>s. dist x a = dist y a\<close>
          for x y :: \<open>'a::metric_space\<close>
          by (fact metric_eq_thm)\<close>
      |> solve_prems
  in
    ((Conv.rewr_conv metric_eq_thm) then_conv
    (*convert \<forall>x\<in>{x\<^sub>1,...,x\<^sub>n}. P x to P x\<^sub>1 \<and> ... \<and> P x\<^sub>n*)
    ball_simp then_conv
    dist_refl_sym_simp) ct
  end

(* build list of theorems "0 \<le> dist x y" for all dist terms in ct *)
fun augment_dist_pos metric_ty ct =
  let fun inst dist_ct =
    let val (x, y) = Thm.dest_binop dist_ct in
      \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm x\<close> and x and y
        in lemma \<open>dist x y \<ge> 0\<close> for x y :: \<open>'a::metric_space\<close> by simp\<close>
    end
  in map inst (find_dist metric_ty ct) end

(* apply maxdist_conv and metric_eq_conv to the goal, thereby embedding the goal in (\<real>\<^sup>n,dist\<^sub>\<infinity>) *)
fun embedding_tac ctxt metric_ty = CSUBGOAL (fn (goal, i) =>
  let
    val points = find_points ctxt metric_ty goal
    val fset_ct = mk_ct_set ctxt metric_ty points
    (*embed all subterms of the form "dist x y" in (\<real>\<^sup>n,dist\<^sub>\<infinity>)*)
    val eq1 = map (maxdist_conv ctxt fset_ct) (find_dist metric_ty goal)
    (*replace point equality by equality of components in \<real>\<^sup>n*)
    val eq2 = map (metric_eq_conv ctxt fset_ct) (find_eq metric_ty goal)
  in
    (K (trace_tac ctxt "Embedding into \<real>\<^sup>n") THEN'
      CONVERSION (Conv.top_sweep_rewrs_conv (eq1 @ eq2) ctxt)) i
  end)

(* decision procedure for linear real arithmetic *)
fun lin_real_arith_tac ctxt metric_ty = CSUBGOAL (fn (goal, i) =>
  let val dist_thms = augment_dist_pos metric_ty goal
  in Argo_Tactic.argo_tac (argo_ctxt ctxt) dist_thms i end)

fun basic_metric_arith_tac ctxt metric_ty =
  SELECT_GOAL (
    dist_refl_sym_tac ctxt 1 THEN
    IF_UNSOLVED (embedding_tac ctxt metric_ty 1) THEN
    IF_UNSOLVED (pre_arith_tac ctxt 1) THEN
    IF_UNSOLVED (lin_real_arith_tac ctxt metric_ty 1))

(* tries to infer the metric space from ct from dist terms,
   if no dist terms are present, equality terms will be used *)
fun guess_metric ctxt tm =
  let
    val thy = Proof_Context.theory_of ctxt
    fun find_dist t =
      (case t of
        \<^Const_>\<open>dist T for _ _\<close>  => SOME T
      | t1 $ t2 => (case find_dist t1 of NONE => find_dist t2 | some => some)
      | Abs _ => find_dist (#2 (Term.dest_abs_global t))
      | _ => NONE)
    fun find_eq t =
      (case t of
        \<^Const_>\<open>HOL.eq T for l r\<close> =>
          if Sign.of_sort thy (T, \<^sort>\<open>metric_space\<close>) then SOME T
          else (case find_eq l of NONE => find_eq r | some => some)
      | t1 $ t2 => (case find_eq t1 of NONE => find_eq t2 | some => some)
      | Abs _ => find_eq (#2 (Term.dest_abs_global t))
      | _ => NONE)
    in
      (case find_dist tm of
        SOME ty => ty
      | NONE =>
          case find_eq tm of
            SOME ty => ty
          | NONE => error "No Metric Space was found")
    end

(* solve \<exists> by proving the goal for a single witness from the metric space *)
fun exists_tac ctxt = CSUBGOAL (fn (goal, i) =>
  let
    val _ = \<^assert> (i = 1)
    val metric_ty = guess_metric ctxt (Thm.term_of goal)
    val points = find_points ctxt metric_ty goal

    fun try_point_tac ctxt pt =
      let
        val ex_rule =
          \<^instantiate>\<open>'a = \<open>Thm.ctyp_of_cterm pt\<close> and x = pt in
            lemma (schematic) \<open>P x \<Longrightarrow> \<exists>x::'a. P x\<close> by (rule exI)\<close>
      in
        HEADGOAL (resolve_tac ctxt [ex_rule] ORELSE'
        (*variable doesn't occur in body*)
        resolve_tac ctxt @{thms exI}) THEN
        trace_tac ctxt ("Removed existential quantifier, try " ^ @{make_string} pt) THEN
        HEADGOAL (try_points_tac ctxt)
      end
    and try_points_tac ctxt = SUBGOAL (fn (g, _) =>
      if is_exists g then
        FIRST (map (try_point_tac ctxt) points)
      else if is_forall g then
        resolve_tac ctxt @{thms HOL.allI} 1 THEN
        Subgoal.FOCUS (fn {context = ctxt', ...} =>
          trace_tac ctxt "Removed universal quantifier" THEN
          try_points_tac ctxt' 1) ctxt 1
      else basic_metric_arith_tac ctxt metric_ty 1)
  in try_points_tac ctxt 1 end)

fun metric_arith_tac ctxt =
  SELECT_GOAL (
    (*unfold common definitions to get rid of sets*)
    unfold_tac ctxt 1 THEN
    (*remove all meta-level connectives*)
    IF_UNSOLVED (Object_Logic.full_atomize_tac ctxt 1) THEN
    (*convert goal to prenex form*)
    IF_UNSOLVED (prenex_tac ctxt 1) THEN
    (*and NNF to ?*)
    IF_UNSOLVED (nnf_tac ctxt 1) THEN
    (*turn all universally quantified variables into free variables, by focusing the subgoal*)
    REPEAT (HEADGOAL (resolve_tac ctxt @{thms HOL.allI})) THEN
    IF_UNSOLVED (SUBPROOF (fn {context = ctxt', ...} =>
      trace_tac ctxt' "Focused on subgoal" THEN
      exists_tac ctxt' 1) ctxt 1))

end
