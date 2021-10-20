(*  Title:    HOL/Library/conditional_parametricity.ML
    Author:   Jan Gilcher, Andreas Lochbihler, Dmitriy Traytel, ETH Zürich

A conditional parametricity prover
*)

signature CONDITIONAL_PARAMETRICITY =
sig
  exception WARNING of string
  type settings =
    {suppress_print_theorem: bool,
    suppress_warnings: bool,
    warnings_as_errors: bool,
    use_equality_heuristic: bool}
  val default_settings: settings
  val quiet_settings: settings

  val parametric_constant: settings -> Attrib.binding * thm -> Proof.context ->
    (thm * Proof.context)
  val get_parametricity_theorems: Proof.context -> thm list

  val prove_goal: settings -> Proof.context -> thm option -> term -> thm
  val prove_find_goal_cond: settings -> Proof.context -> thm list -> thm option -> term -> thm

  val mk_goal: Proof.context -> term -> term
  val mk_cond_goal: Proof.context -> thm -> term * thm
  val mk_param_goal_from_eq_def: Proof.context -> thm -> term
  val step_tac: settings -> Proof.context -> thm list -> int -> tactic
end

structure Conditional_Parametricity: CONDITIONAL_PARAMETRICITY =
struct

type settings =
  {suppress_print_theorem: bool,
  suppress_warnings: bool,
  warnings_as_errors: bool (* overrides suppress_warnings!  *),
  use_equality_heuristic: bool};

val quiet_settings =
  {suppress_print_theorem = true,
  suppress_warnings = true,
  warnings_as_errors = false,
  use_equality_heuristic = false};

val default_settings =
  {suppress_print_theorem = false,
  suppress_warnings = false,
  warnings_as_errors = false,
  use_equality_heuristic = false};

(* helper functions *)

fun strip_imp_prems_concl (Const("Pure.imp", _) $ A $ B) = A :: strip_imp_prems_concl B
  | strip_imp_prems_concl C = [C];

fun strip_prop_safe t = Logic.unprotect t handle TERM _ => t;

fun get_class_of ctxt t =
  Axclass.class_of_param (Proof_Context.theory_of ctxt) (fst (dest_Const t));

fun is_class_op ctxt t =
  let
    val t' = t |> Envir.eta_contract;
  in
    Term.is_Const t' andalso is_some (get_class_of ctxt t')
  end;

fun apply_Var_to_bounds t =
  let
    val (t, ts) = strip_comb t;
  in
    (case t of
      Var (xi, _) =>
        let
          val (bounds, tail) = chop_prefix is_Bound ts;
        in
          list_comb (Var (xi, fastype_of (betapplys (t, bounds))), map apply_Var_to_bounds tail)
        end
    | _ => list_comb (t, map apply_Var_to_bounds ts))
  end;

fun theorem_format_error ctxt thm =
  let
    val msg = Pretty.string_of (Pretty.chunks [(Pretty.para
      "Unexpected format of definition. Must be an unconditional equation."), Thm.pretty_thm ctxt thm]);
  in error msg end;

(* Tacticals and Tactics *)

exception FINISH of thm;

(* Tacticals *)
fun REPEAT_TRY_ELSE_DEFER tac st =
  let
    fun COMB' tac count st = (
      let
        val n = Thm.nprems_of st;
      in
        (if n = 0 then all_tac st else
          (case Seq.pull ((tac THEN COMB' tac 0) st) of
            NONE =>
              if count+1 = n
              then raise FINISH st
              else (defer_tac 1 THEN (COMB' tac (count+1))) st
          | some => Seq.make (fn () => some)))
      end)
  in COMB' tac 0 st end;

(* Tactics  *)
(* helper tactics for printing *)
fun error_tac ctxt msg st =
  (error(msg ^ "\n" ^ Pretty.string_of (Pretty.chunks (Goal_Display.pretty_goals ctxt st)));
  Seq.single st);

fun error_tac' ctxt msg = SELECT_GOAL (error_tac ctxt msg);

(*  finds assumption of the form "Rel ?B Bound x Bound y", rotates it in front,
    applies rel_app arity times and uses ams_rl *)
fun rel_app_tac ctxt t x y arity =
  let
    val rel_app = [@{thm Rel_app}];
    val assume = [asm_rl];
    fun find_and_rotate_tac t i =
      let
        fun is_correct_rule t =
          (case t of
            Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Transfer.Rel\<close>, _) $
              _ $ Bound x' $ Bound y') => x = x' andalso y = y'
          | _ => false);
        val idx = find_index is_correct_rule (t |> Logic.strip_assums_hyp);
      in
        if idx < 0 then no_tac else rotate_tac idx i
      end;
    fun rotate_and_dresolve_tac ctxt arity i = REPEAT_DETERM_N (arity - 1)
      (EVERY' [rotate_tac ~1, dresolve_tac ctxt rel_app, defer_tac] i);
  in
    SELECT_GOAL (EVERY' [find_and_rotate_tac t, forward_tac ctxt rel_app, defer_tac,
      rotate_and_dresolve_tac ctxt arity, rotate_tac ~1, eresolve_tac ctxt assume] 1)
  end;

exception WARNING of string;

fun transform_rules 0 thms = thms
  | transform_rules n thms = transform_rules (n - 1) (curry (Drule.RL o swap)
      @{thms Rel_app Rel_match_app} thms);

fun assume_equality_tac settings ctxt t arity i st =
  let
    val quiet = #suppress_warnings settings;
    val errors = #warnings_as_errors settings;
    val T = fastype_of t;
    val is_eq_lemma = @{thm is_equality_Rel} |> Thm.incr_indexes ((Term.maxidx_of_term t) + 1) |>
      Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt t)];
    val msg = Pretty.string_of (Pretty.chunks [Pretty.paragraph ((Pretty.text
      "No rule found for constant \"") @ [Syntax.pretty_term ctxt t, Pretty.str " :: " ,
      Syntax.pretty_typ ctxt T] @ (Pretty.text "\". Using is_eq_lemma:")), Pretty.quote
      (Thm.pretty_thm ctxt is_eq_lemma)]);
    fun msg_tac st = (if errors then raise WARNING msg else if quiet then () else warning msg;
      Seq.single st)
    val tac = resolve_tac ctxt (transform_rules arity [is_eq_lemma]) i;
  in
    (if fold_atyps (K (K true)) T false then msg_tac THEN tac else tac) st
  end;

fun mark_class_as_match_tac ctxt const const' arity =
  let
    val rules = transform_rules arity [@{thm Rel_match_Rel} |> Thm.incr_indexes ((Int.max o
      apply2 Term.maxidx_of_term) (const, const') + 1) |> Drule.infer_instantiate' ctxt [NONE,
      SOME (Thm.cterm_of ctxt const), SOME (Thm.cterm_of ctxt const')]];
  in resolve_tac ctxt rules end;

(* transforms the parametricity theorems to fit a given arity and uses them for resolution *)
fun parametricity_thm_tac settings ctxt parametricity_thms const arity =
  let
    val rules = transform_rules arity parametricity_thms;
  in resolve_tac ctxt rules ORELSE' assume_equality_tac settings ctxt const arity end;

(* variant of parametricity_thm_tac to use matching *)
fun parametricity_thm_match_tac ctxt parametricity_thms arity =
   let
    val rules = transform_rules arity parametricity_thms;
  in match_tac ctxt rules end;

fun rel_abs_tac ctxt = resolve_tac ctxt [@{thm Rel_abs}];

fun step_tac' settings ctxt parametricity_thms (tm, i) =
  (case tm |> Logic.strip_assums_concl of
    Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (rel, _) $ _ $ t $ u) =>
    let
      val (arity_of_t, arity_of_u) = apply2 (strip_comb #> snd #> length) (t, u);
    in
      (case rel of
        \<^const_name>\<open>Transfer.Rel\<close> =>
          (case (head_of t, head_of u) of
            (Abs _, _) => rel_abs_tac ctxt
          | (_, Abs _) => rel_abs_tac ctxt
          | (const as (Const _), const' as (Const _)) =>
            if #use_equality_heuristic settings andalso t aconv u
              then
                assume_equality_tac quiet_settings ctxt t 0
              else if arity_of_t = arity_of_u
                then if is_class_op ctxt const orelse is_class_op ctxt const'
                  then mark_class_as_match_tac ctxt const const' arity_of_t
                  else parametricity_thm_tac settings ctxt parametricity_thms const arity_of_t
                else error_tac' ctxt "Malformed term. Arities of t and u don't match."
          | (Bound x, Bound y) =>
            if arity_of_t = arity_of_u then if arity_of_t > 0 then rel_app_tac ctxt tm x y arity_of_t
               else assume_tac ctxt
            else  error_tac' ctxt "Malformed term. Arities of t and u don't match."
          | _ => error_tac' ctxt
            "Unexpected format. Expected  (Abs _, _), (_, Abs _), (Const _, Const _) or (Bound _, Bound _).")
         | \<^const_name>\<open>Conditional_Parametricity.Rel_match\<close> =>
             parametricity_thm_match_tac ctxt parametricity_thms arity_of_t
      | _ => error_tac' ctxt "Unexpected format. Expected Transfer.Rel or Rel_match marker." ) i
    end
    | Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Transfer.is_equality\<close>, _) $ _) =>
        Transfer.eq_tac ctxt i
    | _ => error_tac' ctxt "Unexpected format. Not of form Const (HOL.Trueprop, _) $ _" i);

fun step_tac settings = SUBGOAL oo step_tac' settings;

fun apply_theorem_tac ctxt thm =
  HEADGOAL (resolve_tac ctxt [Local_Defs.unfold ctxt @{thms Pure.prop_def} thm] THEN_ALL_NEW
    assume_tac ctxt);

(* Goal Generation  *)
fun strip_boundvars_from_rel_match t =
  (case t of
    (Tp as Const (\<^const_name>\<open>HOL.Trueprop\<close>, _)) $
      ((Rm as Const (\<^const_name>\<open>Conditional_Parametricity.Rel_match\<close>, _)) $ R $ t $ t') =>
        Tp $ (Rm $ apply_Var_to_bounds R $ t $ t')
  | _ => t);

val extract_conditions =
  let
    val filter_bounds = filter_out Term.is_open;
    val prem_to_conditions =
      map (map strip_boundvars_from_rel_match o strip_imp_prems_concl o strip_all_body);
    val remove_duplicates = distinct Term.aconv;
  in remove_duplicates o filter_bounds o flat o prem_to_conditions end;

fun mk_goal ctxt t =
  let
    val ctxt = fold (Variable.declare_typ o snd) (Term.add_frees t []) ctxt;
    val t = singleton (Variable.polymorphic ctxt) t;
    val i = maxidx_of_term t + 1;
    fun tvar_to_tfree ((name, _), sort) = (name, sort);
    val tvars = Term.add_tvars t [];
    val new_frees = map TFree (Term.variant_frees t (map tvar_to_tfree tvars));
    val u = subst_atomic_types ((map TVar tvars) ~~ new_frees) t;
    val T = fastype_of t;
    val U = fastype_of u;
    val R = [T,U] ---> \<^typ>\<open>bool\<close>
    val r = Var (("R", 2 * i), R);
    val transfer_rel = Const (\<^const_name>\<open>Transfer.Rel\<close>, [R,T,U] ---> \<^typ>\<open>bool\<close>);
  in HOLogic.mk_Trueprop (transfer_rel $ r $ t $ u) end;

fun mk_abs_helper T t =
  let
    val U = fastype_of t;
    fun mk_abs_helper' T U =
      if T = U then t else
        let
          val (T2, T1) = Term.dest_funT T;
        in
          Term.absdummy T2 (mk_abs_helper' T1 U)
        end;
  in mk_abs_helper' T U end;

fun compare_ixs ((name, i):indexname, (name', i'):indexname) = if name < name' then LESS
  else if name > name' then GREATER
  else if i < i' then LESS
  else if i > i' then GREATER
  else EQUAL;

fun mk_cond_goal ctxt thm =
  let
    val conclusion = (hd o strip_imp_prems_concl o strip_prop_safe o Thm.concl_of) thm;
    val conditions = (extract_conditions o Thm.prems_of) thm;
    val goal = Logic.list_implies (conditions, conclusion);
    fun compare ((ix, _), (ix', _)) = compare_ixs (ix, ix');
    val goal_vars = Term.add_vars goal [] |> Ord_List.make compare;
    val (ixs, Ts) = split_list goal_vars;
    val (_, Ts') = Term.add_vars (Thm.prop_of thm) [] |> Ord_List.make compare
      |> Ord_List.inter compare goal_vars |> split_list;
    val (As, _) = Ctr_Sugar_Util.mk_Frees "A" Ts ctxt;
    val goal_subst = ixs ~~ As;
    val thm_subst = ixs ~~ (map2 mk_abs_helper Ts' As);
    val thm' = thm |> Drule.infer_instantiate ctxt (map (apsnd (Thm.cterm_of ctxt)) thm_subst);
  in (goal |> Term.subst_Vars goal_subst, thm') end;

fun mk_param_goal_from_eq_def ctxt thm =
  let
    val t =
      (case Thm.full_prop_of thm of
        (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ t' $ _) => t'
      | _ => theorem_format_error ctxt thm);
  in mk_goal ctxt t end;

(* Transformations and parametricity theorems *)
fun transform_class_rule ctxt thm =
  (case Thm.concl_of thm of
    Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_name>\<open>Transfer.Rel\<close>, _) $ _ $ t $ u ) =>
      (if curry Term.aconv_untyped t u andalso is_class_op ctxt t then
        thm RS @{thm Rel_Rel_match}
      else thm)
  | _ => thm);

fun is_parametricity_theorem thm =
  (case Thm.concl_of thm of
    Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ (Const (rel, _) $ _ $ t $ u ) =>
      if rel = \<^const_name>\<open>Transfer.Rel\<close> orelse
        rel = \<^const_name>\<open>Conditional_Parametricity.Rel_match\<close>
      then curry Term.aconv_untyped t u
      else false
  | _ => false);

(* Pre- and postprocessing of theorems *)
fun mk_Domainp_assm (T, R) =
  HOLogic.mk_eq ((Const (\<^const_name>\<open>Domainp\<close>, Term.fastype_of T --> Term.fastype_of R) $ T), R);

val Domainp_lemma =
  @{lemma "(!!R. Domainp T = R ==> PROP (P R)) == PROP (P (Domainp T))"
    by (rule, drule meta_spec,
      erule meta_mp, rule HOL.refl, simp)};

fun fold_Domainp f (t as Const (\<^const_name>\<open>Domainp\<close>,_) $ (Var (_,_))) = f t
  | fold_Domainp f (t $ u) = fold_Domainp f t #> fold_Domainp f u
  | fold_Domainp f (Abs (_, _, t)) = fold_Domainp f t
  | fold_Domainp _ _ = I;

fun subst_terms tab t =
  let
    val t' = Termtab.lookup tab t
  in
    (case t' of
      SOME t' => t'
    | NONE =>
      (case t of
          u $ v => (subst_terms tab u) $ (subst_terms tab v)
        | Abs (a, T, t) => Abs (a, T, subst_terms tab t)
        | t => t))
  end;

fun gen_abstract_domains ctxt (dest : term -> term * (term -> term)) thm =
  let
    val prop = Thm.prop_of thm
    val (t, mk_prop') = dest prop
    val Domainp_ts = rev (fold_Domainp (fn t => insert op= t) t [])
    val Domainp_Ts = map (snd o dest_funT o snd o dest_Const o fst o dest_comb) Domainp_ts
    val used = Term.add_free_names t []
    val rels = map (snd o dest_comb) Domainp_ts
    val rel_names = map (fst o fst o dest_Var) rels
    val names = map (fn name => ("D" ^ name)) rel_names |> Name.variant_list used
    val frees = map Free (names ~~ Domainp_Ts)
    val prems = map (HOLogic.mk_Trueprop o mk_Domainp_assm) (rels ~~ frees);
    val t' = subst_terms (fold Termtab.update (Domainp_ts ~~ frees) Termtab.empty) t
    val prop1 = fold Logic.all frees (Logic.list_implies (prems, mk_prop' t'))
    val prop2 = Logic.list_rename_params (rev names) prop1
    val cprop = Thm.cterm_of ctxt prop2
    val equal_thm = Raw_Simplifier.rewrite ctxt false [Domainp_lemma] cprop
    fun forall_elim thm = Thm.forall_elim_vars (Thm.maxidx_of thm + 1) thm;
  in
    forall_elim (thm COMP (equal_thm COMP @{thm equal_elim_rule2}))
  end
    handle TERM _ => thm;

fun abstract_domains_transfer ctxt thm =
  let
    fun dest prop =
      let
        val prems = Logic.strip_imp_prems prop
        val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)
        val ((rel, x), y) = apfst Term.dest_comb (Term.dest_comb concl)
      in
        (x, fn x' =>
          Logic.list_implies (prems, HOLogic.mk_Trueprop (rel $ x' $ y)))
      end
  in
    gen_abstract_domains ctxt dest thm
  end;

fun transfer_rel_conv conv =
  Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.fun2_conv (Conv.arg_conv conv)));

fun fold_relator_eqs_conv ctxt =
  Conv.bottom_rewrs_conv (Transfer.get_relator_eq ctxt) ctxt;

fun mk_is_equality t =
  Const (\<^const_name>\<open>is_equality\<close>, Term.fastype_of t --> HOLogic.boolT) $ t;

val is_equality_lemma =
  @{lemma "(!!R. is_equality R ==> PROP (P R)) == PROP (P (=))"
    by (unfold is_equality_def, rule, drule meta_spec,
      erule meta_mp, rule HOL.refl, simp)};

fun gen_abstract_equalities ctxt (dest : term -> term * (term -> term)) thm =
  let
    val prop = Thm.prop_of thm
    val (t, mk_prop') = dest prop
    (* Only consider "(=)" at non-base types *)
    fun is_eq (Const (\<^const_name>\<open>HOL.eq\<close>, Type ("fun", [T, _]))) =
        (case T of Type (_, []) => false | _ => true)
      | is_eq _ = false
    val add_eqs = Term.fold_aterms (fn t => if is_eq t then insert (op =) t else I)
    val eq_consts = rev (add_eqs t [])
    val eqTs = map (snd o dest_Const) eq_consts
    val used = Term.add_free_names prop []
    val names = map (K "") eqTs |> Name.variant_list used
    val frees = map Free (names ~~ eqTs)
    val prems = map (HOLogic.mk_Trueprop o mk_is_equality) frees
    val prop1 = mk_prop' (Term.subst_atomic (eq_consts ~~ frees) t)
    val prop2 = fold Logic.all frees (Logic.list_implies (prems, prop1))
    val cprop = Thm.cterm_of ctxt prop2
    val equal_thm = Raw_Simplifier.rewrite ctxt false [is_equality_lemma] cprop
    fun forall_elim thm = Thm.forall_elim_vars (Thm.maxidx_of thm + 1) thm
  in
    forall_elim (thm COMP (equal_thm COMP @{thm equal_elim_rule2}))
  end
    handle TERM _ => thm;

fun abstract_equalities_transfer ctxt thm =
  let
    fun dest prop =
      let
        val prems = Logic.strip_imp_prems prop
        val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)
        val ((rel, x), y) = apfst Term.dest_comb (Term.dest_comb concl)
      in
        (rel, fn rel' =>
          Logic.list_implies (prems, HOLogic.mk_Trueprop (rel' $ x $ y)))
      end
    val contracted_eq_thm =
      Conv.fconv_rule (transfer_rel_conv (fold_relator_eqs_conv ctxt)) thm
      handle CTERM _ => thm
  in
    gen_abstract_equalities ctxt dest contracted_eq_thm
  end;

fun prep_rule ctxt = abstract_equalities_transfer ctxt #> abstract_domains_transfer ctxt;

fun get_preprocess_theorems ctxt =
  Named_Theorems.get ctxt \<^named_theorems>\<open>parametricity_preprocess\<close>;

fun preprocess_theorem ctxt =
  Local_Defs.unfold0 ctxt (get_preprocess_theorems ctxt)
  #> transform_class_rule ctxt;

fun postprocess_theorem ctxt =
  Local_Defs.fold ctxt (@{thm Rel_Rel_match_eq} :: get_preprocess_theorems ctxt)
  #> prep_rule ctxt
  #>  Local_Defs.unfold ctxt @{thms Rel_def};

fun get_parametricity_theorems ctxt =
  let
    val parametricity_thm_map_filter =
      Option.filter (is_parametricity_theorem andf (not o curry Term.could_unify
        (Thm.full_prop_of @{thm is_equality_Rel})) o Thm.full_prop_of) o preprocess_theorem ctxt;
  in
    map_filter (parametricity_thm_map_filter o Thm.transfer' ctxt)
      (Transfer.get_transfer_raw ctxt)
  end;

(* Provers *)
(* Tries to prove a parametricity theorem without conditions, returns the last goal_state as thm *)
fun prove_find_goal_cond settings ctxt rules def_thm t =
  let
    fun find_conditions_tac {context = ctxt, prems = _} = unfold_tac ctxt (the_list def_thm) THEN
      (REPEAT_TRY_ELSE_DEFER o HEADGOAL) (step_tac settings ctxt rules);
  in
    Goal.prove ctxt [] [] t find_conditions_tac handle FINISH st => st
  end;

(* Simplifies and proves thm *)
fun prove_cond_goal ctxt thm =
  let
    val (goal, thm') = mk_cond_goal ctxt thm;
    val vars = Variable.add_free_names ctxt goal [];
    fun prove_conditions_tac {context = ctxt, prems = _} = apply_theorem_tac ctxt thm';
    val vars = Variable.add_free_names ctxt (Thm.prop_of thm') vars;
  in
    Goal.prove ctxt vars [] goal prove_conditions_tac
  end;

(* Finds necessary conditions for t and proofs conditional parametricity of t under those conditions *)
fun prove_goal settings ctxt def_thm t =
  let
    val parametricity_thms = get_parametricity_theorems ctxt;
    val found_thm = prove_find_goal_cond settings ctxt parametricity_thms def_thm t;
    val thm = prove_cond_goal ctxt found_thm;
  in
    postprocess_theorem ctxt thm
  end;

(* Commands  *)
fun gen_parametric_constant settings prep_att prep_thm (raw_b : Attrib.binding, raw_eq) lthy =
  let
    val b = apsnd (map (prep_att lthy)) raw_b;
    val def_thm = (prep_thm lthy raw_eq);
    val eq = Ctr_Sugar_Util.mk_abs_def def_thm handle TERM _ => theorem_format_error lthy def_thm;
    val goal= mk_param_goal_from_eq_def lthy eq;
    val thm = prove_goal settings lthy (SOME eq) goal;
    val (res, lthy') = Local_Theory.note (b, [thm]) lthy;
    val _ = if #suppress_print_theorem settings then () else
      Proof_Display.print_results true (Position.thread_data ()) lthy' (("theorem",""), [res]);
  in
    (the_single (snd res), lthy')
  end;

fun parametric_constant settings = gen_parametric_constant settings (K I) (K I);

val parametric_constant_cmd = snd oo gen_parametric_constant default_settings (Attrib.check_src)
  (singleton o Attrib.eval_thms);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>parametric_constant\<close> "proves parametricity"
    ((Parse_Spec.opt_thm_name ":" -- Parse.thm) >> parametric_constant_cmd);

end;
