signature METRIC_ARITH = sig
  val metric_arith_tac : Proof.context -> int -> tactic
  val trace: bool Config.T
end

structure MetricArith : METRIC_ARITH = struct

fun default d x = case x of SOME y => SOME y | NONE => d

(* apply f to both cterms in ct_pair, merge results *)
fun app_union_ct_pair f ct_pair = uncurry (union (op aconvc)) (apply2 f ct_pair)

val trace = Attrib.setup_config_bool \<^binding>\<open>metric_trace\<close> (K false)

fun trace_tac ctxt msg =
  if Config.get ctxt trace then print_tac ctxt msg
  else all_tac

fun argo_trace_ctxt ctxt =
  if Config.get ctxt trace
  then Config.map (Argo_Tactic.trace) (K "basic") ctxt
  else ctxt

fun IF_UNSOLVED' tac i = IF_UNSOLVED (tac i)
fun REPEAT' tac i = REPEAT (tac i)

fun free_in v ct = Cterms.defined (Cterms.build (Drule.add_frees_cterm ct)) v

(* build a cterm set with elements cts of type ty *)
fun mk_ct_set ctxt ty =
  map Thm.term_of #>
  HOLogic.mk_set ty #>
  Thm.cterm_of ctxt

fun prenex_tac ctxt =
  let
    val prenex_simps = Proof_Context.get_thms ctxt @{named_theorems metric_prenex}
    val prenex_ctxt = put_simpset HOL_basic_ss ctxt addsimps prenex_simps
  in
    simp_tac prenex_ctxt THEN'
    K (trace_tac ctxt "Prenex form")
  end

fun nnf_tac ctxt =
  let
    val nnf_simps = Proof_Context.get_thms ctxt @{named_theorems metric_nnf}
    val nnf_ctxt = put_simpset HOL_basic_ss ctxt addsimps nnf_simps
  in
    simp_tac nnf_ctxt THEN'
    K (trace_tac ctxt "NNF form")
  end

fun unfold_tac ctxt =
  asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps (
    Proof_Context.get_thms ctxt @{named_theorems metric_unfold}))

fun pre_arith_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps (
    Proof_Context.get_thms ctxt @{named_theorems metric_pre_arith})) THEN'
    K (trace_tac ctxt "Prepared for decision procedure")

fun dist_refl_sym_tac ctxt =
  let
    val refl_sym_simps = @{thms dist_self dist_commute add_0_right add_0_left simp_thms}
    val refl_sym_ctxt = put_simpset HOL_basic_ss ctxt addsimps refl_sym_simps
  in
    simp_tac refl_sym_ctxt THEN'
    K (trace_tac ctxt ("Simplified using " ^ @{make_string} refl_sym_simps))
  end

fun is_exists ct =
  case Thm.term_of ct of
    Const (\<^const_name>\<open>HOL.Ex\<close>,_)$_ => true
  | Const (\<^const_name>\<open>Trueprop\<close>,_)$_ => is_exists (Thm.dest_arg ct)
  | _ => false

fun is_forall ct =
  case Thm.term_of ct of
    Const (\<^const_name>\<open>HOL.All\<close>,_)$_ => true
  | Const (\<^const_name>\<open>Trueprop\<close>,_)$_ => is_forall (Thm.dest_arg ct)
  | _ => false

fun dist_ty mty = mty --> mty --> \<^typ>\<open>real\<close>

(* find all free points in ct of type metric_ty *)
fun find_points ctxt metric_ty ct =
  let
    fun find ct =
      (if Thm.typ_of_cterm ct = metric_ty then [ct] else []) @ (
        case Thm.term_of ct of
          _ $ _ =>
          app_union_ct_pair find (Thm.dest_comb ct)
        | Abs (_, _, _) =>
          (* ensure the point doesn't contain the bound variable *)
          let val (var, bod) = Thm.dest_abs_global ct in
            filter (free_in var #> not) (find bod)
          end
        | _ => [])
    val points = find ct
  in
    case points of
      [] =>
      (* if no point can be found, invent one *)
      let
        val free_name = Term.variant_frees (Thm.term_of ct) [("x", metric_ty)]
      in
        map (Free #> Thm.cterm_of ctxt) free_name
      end
    | _ => points
  end

(* find all cterms "dist x y" in ct, where x and y have type metric_ty *)
fun find_dist metric_ty ct =
  let
    val dty = dist_ty metric_ty
    fun find ct =
      case Thm.term_of ct of
        Const (\<^const_name>\<open>dist\<close>, ty) $ _ $ _ =>
        if ty = dty then [ct] else []
      | _ $ _ =>
        app_union_ct_pair find (Thm.dest_comb ct)
      | Abs (_, _, _) =>
        let val (var, bod) = Thm.dest_abs_global ct in
          filter (free_in var #> not) (find bod)
        end
      | _ => []
  in
    find ct
  end

(* find all "x=y", where x has type metric_ty *)
fun find_eq metric_ty ct =
  let
    fun find ct =
      case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.eq\<close>, ty) $ _ $ _ =>
          if fst (dest_funT ty) = metric_ty
          then [ct]
          else app_union_ct_pair find (Thm.dest_binop ct)
      | _ $ _ => app_union_ct_pair find (Thm.dest_comb ct)
      | Abs (_, _, _) =>
        let val (var, bod) = Thm.dest_abs_global ct in
          filter (free_in var #> not) (find bod)
        end
      | _ => []
  in
    find ct
  end

(* rewrite ct of the form "dist x y" using maxdist_thm *)
fun maxdist_conv ctxt fset_ct ct =
  let
    val (xct, yct) = Thm.dest_binop ct
    val solve_prems =
      rule_by_tactic ctxt (ALLGOALS (simp_tac (put_simpset HOL_ss ctxt
        addsimps @{thms finite.emptyI finite_insert empty_iff insert_iff})))
    val image_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps @{thms image_empty image_insert})
    val dist_refl_sym_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps @{thms dist_commute dist_self})
    val algebra_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps
        @{thms diff_self diff_0_right diff_0 abs_zero abs_minus_cancel abs_minus_commute})
    val insert_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps @{thms insert_absorb2 insert_commute})
    val sup_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps @{thms cSup_singleton Sup_insert_insert})
    val real_abs_dist_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps @{thms real_abs_dist})
    val maxdist_thm =
      @{thm maxdist_thm} |>
      infer_instantiate' ctxt [SOME fset_ct, SOME xct, SOME yct] |>
      solve_prems
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
    val (xct, yct) = Thm.dest_binop ct
    val solve_prems =
      rule_by_tactic ctxt (ALLGOALS (simp_tac (put_simpset HOL_ss ctxt
        addsimps @{thms empty_iff insert_iff})))
    val ball_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps
        @{thms Set.ball_empty ball_insert})
    val dist_refl_sym_simp =
      Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps @{thms dist_commute dist_self})
    val metric_eq_thm =
      @{thm metric_eq_thm} |>
      infer_instantiate' ctxt [SOME xct, SOME fset_ct, SOME yct] |>
      solve_prems
  in
    ((Conv.rewr_conv metric_eq_thm) then_conv
    (* convert \<forall>x\<in>{x\<^sub>1,...,x\<^sub>n}. P x to P x\<^sub>1 \<and> ... \<and> P x\<^sub>n *)
    ball_simp then_conv
    dist_refl_sym_simp) ct
  end

(* build list of theorems "0 \<le> dist x y" for all dist terms in ct *)
fun augment_dist_pos ctxt metric_ty ct =
  let fun inst dist_ct =
    let val (xct, yct) = Thm.dest_binop dist_ct
    in infer_instantiate' ctxt [SOME xct, SOME yct] @{thm zero_le_dist} end
  in map inst (find_dist metric_ty ct) end

fun top_sweep_rewrs_tac ctxt thms =
  CONVERSION (Conv.top_sweep_conv (K (Conv.rewrs_conv thms)) ctxt)

(* apply maxdist_conv and metric_eq_conv to the goal, thereby embedding the goal in (\<real>\<^sup>n,dist\<^sub>\<infinity>) *)
fun embedding_tac ctxt metric_ty i goal =
  let
    val ct = (Thm.cprem_of goal 1)
    val points = find_points ctxt metric_ty ct
    val fset_ct = mk_ct_set ctxt metric_ty points
    (* embed all subterms of the form "dist x y" in (\<real>\<^sup>n,dist\<^sub>\<infinity>) *)
    val eq1 = map (maxdist_conv ctxt fset_ct) (find_dist metric_ty ct)
    (* replace point equality by equality of components in \<real>\<^sup>n *)
    val eq2 = map (metric_eq_conv ctxt fset_ct) (find_eq metric_ty ct)
  in
    ( K (trace_tac ctxt "Embedding into \<real>\<^sup>n") THEN' top_sweep_rewrs_tac ctxt (eq1 @ eq2))i goal
  end

(* decision procedure for linear real arithmetic *)
fun lin_real_arith_tac ctxt metric_ty i goal =
  let
    val dist_thms = augment_dist_pos ctxt metric_ty (Thm.cprem_of goal 1)
    val ctxt' = argo_trace_ctxt ctxt
  in (Argo_Tactic.argo_tac ctxt' dist_thms) i goal end

fun basic_metric_arith_tac ctxt metric_ty =
  HEADGOAL (dist_refl_sym_tac ctxt THEN'
  IF_UNSOLVED' (embedding_tac ctxt metric_ty) THEN'
  IF_UNSOLVED' (pre_arith_tac ctxt) THEN'
  IF_UNSOLVED' (lin_real_arith_tac ctxt metric_ty))

(* tries to infer the metric space from ct from dist terms,
   if no dist terms are present, equality terms will be used *)
fun guess_metric ctxt ct =
let
  fun find_dist ct =
    case Thm.term_of ct of
      Const (\<^const_name>\<open>dist\<close>, ty) $ _ $ _  => SOME (fst (dest_funT ty))
    | _ $ _ =>
      let val (s, t) = Thm.dest_comb ct in
        default (find_dist t) (find_dist s)
      end
    | Abs (_, _, _) => find_dist (snd (Thm.dest_abs_global ct))
    | _ => NONE
  fun find_eq ct =
    case Thm.term_of ct of
      Const (\<^const_name>\<open>HOL.eq\<close>, ty) $ x $ _ =>
      let val (l, r) = Thm.dest_binop ct in
        if Sign.of_sort (Proof_Context.theory_of ctxt) (type_of x, \<^sort>\<open>metric_space\<close>)
        then SOME (fst (dest_funT ty))
        else default (find_dist r) (find_eq l)
      end
    | _ $ _ =>
      let val (s, t) = Thm.dest_comb ct in
        default (find_eq t) (find_eq s)
      end
    | Abs (_, _, _) => find_eq (snd (Thm.dest_abs_global ct))
    | _ => NONE
  in
    case default (find_eq ct) (find_dist ct) of
      SOME ty => ty
    | NONE => error "No Metric Space was found"
  end

(* eliminate \<exists> by proving the goal for a single witness from the metric space *)
fun elim_exists ctxt goal =
  let
    val ct = Thm.cprem_of goal 1
    val metric_ty = guess_metric ctxt ct
    val points = find_points ctxt metric_ty ct

    fun try_point ctxt pt =
      let val ex_rule = infer_instantiate' ctxt [NONE, SOME pt] @{thm exI}
      in
        HEADGOAL (resolve_tac ctxt [ex_rule] ORELSE'
        (* variable doesn't occur in body *)
        resolve_tac ctxt @{thms exI}) THEN
        trace_tac ctxt ("Removed existential quantifier, try " ^ @{make_string} pt) THEN
        try_points ctxt
      end
    and try_points ctxt goal = (
      if is_exists (Thm.cprem_of goal 1) then
        FIRST (map (try_point ctxt) points)
      else if is_forall (Thm.cprem_of goal 1) then
        HEADGOAL (resolve_tac ctxt @{thms HOL.allI} THEN'
        Subgoal.FOCUS (fn {context = ctxt', ...} =>
          trace_tac ctxt "Removed universal quantifier" THEN
          try_points ctxt') ctxt)
      else basic_metric_arith_tac ctxt metric_ty) goal
  in
    try_points ctxt goal
  end

fun metric_arith_tac ctxt =
  (* unfold common definitions to get rid of sets *)
  unfold_tac ctxt THEN'
  (* remove all meta-level connectives *)
  IF_UNSOLVED' (Object_Logic.full_atomize_tac ctxt) THEN'
  (* convert goal to prenex form *)
  IF_UNSOLVED' (prenex_tac ctxt) THEN'
  (* and NNF to ? *)
  IF_UNSOLVED' (nnf_tac ctxt) THEN'
  (* turn all universally quantified variables into free variables, by focusing the subgoal *)
  REPEAT' (resolve_tac ctxt @{thms HOL.allI}) THEN'
  IF_UNSOLVED' (SUBPROOF (fn {context=ctxt', ...} =>
    trace_tac ctxt' "Focused on subgoal" THEN
    elim_exists ctxt') ctxt)
end
