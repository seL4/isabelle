(*  Title:      HOL/Eisbach/match_method.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Setup for "match" proof method. It provides basic fact/term matching in
addition to premise/conclusion matching through Subgoal.focus, and binds
fact names from matches as well as term patterns within matches.
*)

signature MATCH_METHOD =
sig
  val focus_schematics: Proof.context -> Envir.tenv
  val focus_params: Proof.context -> term list
  (* FIXME proper ML interface for the main thing *)
end

structure Match_Method : MATCH_METHOD =
struct

(* Filter premises by predicate, with premise order; recovers premise order afterwards.*)
fun filter_prems_tac' ctxt prem =
  let
    fun Then NONE tac = SOME tac
      | Then (SOME tac) tac' = SOME (tac THEN' tac');
    fun thins idxH (tac, n, i) =
       if prem idxH then (tac, n + 1 , i)
       else (Then tac (rotate_tac n THEN' eresolve_tac ctxt [thin_rl]), 0, i + n);
  in
    SUBGOAL (fn (goal, i) =>
      let val idxHs = tag_list 0 (Logic.strip_assums_hyp goal) in
        (case fold thins idxHs (NONE, 0, 0) of
          (NONE, _, _) => no_tac
        | (SOME tac, _, n) => tac i THEN rotate_tac (~ n) i)
      end)
  end;


datatype match_kind =
    Match_Term of term Item_Net.T
  | Match_Fact of thm Item_Net.T
  | Match_Concl
  | Match_Prems of bool;


val aconv_net = Item_Net.init (op aconv) single;

val parse_match_kind =
  Scan.lift \<^keyword>\<open>conclusion\<close> >> K Match_Concl ||
  Scan.lift (\<^keyword>\<open>premises\<close> |-- Args.mode "local") >> Match_Prems ||
  Scan.lift (\<^keyword>\<open>(\<close>) |-- Args.term --| Scan.lift (\<^keyword>\<open>)\<close>) >>
    (fn t => Match_Term (Item_Net.update t aconv_net)) ||
  Attrib.thms >> (fn thms => Match_Fact (fold Item_Net.update thms Thm.item_net));


fun nameable_match m = (case m of Match_Fact _ => true | Match_Prems _ => true | _ => false);
fun prop_match m = (case m of Match_Term _ => false | _ => true);

val bound_thm : (thm, binding) Parse_Tools.parse_val parser =
  Parse_Tools.parse_thm_val Parse.binding;

val bound_term : (term, binding) Parse_Tools.parse_val parser =
  Parse_Tools.parse_term_val Parse.binding;

val fixes =
  Parse.and_list1 (Scan.repeat1 (Parse.position bound_term) --
    Scan.option (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.typ)
    >> (fn (xs, T) => map (fn (x, pos) => ((x, T), pos)) xs)) >> flat;

val for_fixes = Scan.optional (\<^keyword>\<open>for\<close> |-- fixes) [];

fun pos_of dyn = Parse_Tools.the_parse_val dyn |> Binding.pos_of;

(*FIXME: Dynamic facts modify the background theory, so we have to resort
  to token replacement for matched facts. *)
val dynamic_fact =
  Scan.lift bound_thm -- Attrib.opt_attribs;

type match_args = {multi : bool, cut : int};

val parse_match_args =
  Scan.optional
    (Args.parens
      (Parse.enum1 ","
        (Args.$$$ "multi" >> (fn _ => fn {cut, ...} => {multi = true, cut = cut}) ||
         Args.$$$ "cut" |-- Scan.optional Parse.nat 1
          >> (fn n => fn {multi, ...} => {multi = multi, cut = n})))) []
  >> (fn fs => fold I fs {multi = false, cut = ~1});

fun parse_named_pats match_kind =
  Args.context --
  Parse.and_list1'
    (Scan.option (dynamic_fact --| Scan.lift Args.colon) :--
      (fn opt_dyn =>
        if is_none opt_dyn orelse nameable_match match_kind
        then Scan.lift (Parse_Tools.name_term -- parse_match_args)
        else
          let val b = #1 (the opt_dyn)
          in error ("Cannot bind fact name in term match" ^ Position.here (pos_of b)) end)) --
  Scan.lift (for_fixes -- (\<^keyword>\<open>\<Rightarrow>\<close> |-- Parse.token Parse.text))
  >> (fn ((ctxt, ts), (fixes, body)) =>
    (case Token.get_value body of
      SOME (Token.Source src) =>
        let
          val text = Method.read ctxt src;
          val ts' =
            map
              (fn (b, (Parse_Tools.Real_Val v, match_args)) =>
                ((Option.map (fn (b, att) =>
                  (Parse_Tools.the_real_val b, att)) b, match_args), v)
                | _ => raise Fail "Expected closed term") ts
          val fixes' = map (fn ((p, _), _) => Parse_Tools.the_real_val p) fixes
        in (ts', fixes', text) end
    | _ =>
        let
          val (fix_names, ctxt3) = ctxt
            |> Proof_Context.add_fixes_cmd
              (map (fn ((pb, otyp), _) => (Parse_Tools.the_parse_val pb, otyp, NoSyn)) fixes)
            ||> Proof_Context.set_mode Proof_Context.mode_schematic;

          fun parse_term term =
            if prop_match match_kind
            then Syntax.parse_prop ctxt3 term
            else Syntax.parse_term ctxt3 term;

          fun drop_judgment_dummy t =
            (case t of
              Const (judgment, _) $
                (Const (\<^syntax_const>\<open>_type_constraint_\<close>, T) $
                  Const (\<^const_name>\<open>Pure.dummy_pattern\<close>, _)) =>
                if judgment = Object_Logic.judgment_name ctxt then
                    Const (\<^syntax_const>\<open>_type_constraint_\<close>, T) $
                      Const (\<^const_name>\<open>Pure.dummy_pattern\<close>, propT)
                else t
            | t1 $ t2 => drop_judgment_dummy t1 $ drop_judgment_dummy t2
            | Abs (a, T, b) => Abs (a, T, drop_judgment_dummy b)
            | _ => t);

          val pats =
            map (fn (_, (term, _)) => parse_term (Parse_Tools.the_parse_val term)) ts
            |> map drop_judgment_dummy
            |> (fn ts => fold_map Term.replace_dummy_patterns ts (Variable.maxidx_of ctxt3 + 1))
            |> fst
            |> Syntax.check_terms ctxt3;

          val pat_fixes = fold (Term.add_frees) pats [] |> map fst;

          val _ =
            map2 (fn nm => fn (_, pos) =>
                member (op =) pat_fixes nm orelse
                error ("For-fixed variable must be bound in some pattern" ^ Position.here pos))
              fix_names fixes;

          val _ = map (Term.map_types Type.no_tvars) pats;

          val ctxt4 = fold Variable.declare_term pats ctxt3;

          val (real_fixes, ctxt5) = ctxt4
            |> fold_map Proof_Context.inferred_param fix_names |>> map Free;

          fun reject_extra_free (Free (x, _)) () =
                if Variable.is_fixed ctxt5 x then ()
                else error ("Illegal use of free (unfixed) variable " ^ quote x)
            | reject_extra_free _ () = ();
          val _ = (fold o fold_aterms) reject_extra_free pats ();

          val binds =
            map (fn (b, _) => Option.map (fn (b, att) => (Parse_Tools.the_parse_val b, att)) b) ts;

          fun upd_ctxt (SOME (b, att)) pat (tms, ctxt) =
                let
                  val ([nm], ctxt') =
                    Variable.variant_fixes [Name.internal (Binding.name_of b)] ctxt;
                  val abs_nms = Term.strip_all_vars pat;

                  val param_thm = map (Drule.mk_term o Thm.cterm_of ctxt' o Free) abs_nms
                    |> Conjunction.intr_balanced
                    |> Drule.generalize (Symtab.empty, Symtab.make_set (map fst abs_nms))
                    |> Thm.tag_free_dummy;

                  val atts = map (Attrib.attribute ctxt') att;
                  val (param_thm', ctxt'') = Thm.proof_attributes atts param_thm ctxt';

                  fun label_thm thm =
                    Thm.cterm_of ctxt'' (Free (nm, propT))
                    |> Drule.mk_term
                    |> not (null abs_nms) ? Conjunction.intr thm

                  val [head_thm, body_thm] =
                    Drule.zero_var_indexes_list (map label_thm [param_thm, param_thm'])
                    |> map Thm.tag_free_dummy;

                  val ctxt''' =
                    Attrib.local_notes "" [((b, []), [([body_thm], [])])] ctxt''
                    |> snd
                    |> Variable.declare_maxidx (Thm.maxidx_of head_thm);
                in
                  (SOME (head_thm, att) :: tms, ctxt''')
                end
            | upd_ctxt NONE _ (tms, ctxt) = (NONE :: tms, ctxt);

          val (binds, ctxt6) = ctxt5
            |> (fn ctxt => fold2 upd_ctxt binds pats ([], ctxt) |> apfst rev)
            ||> Proof_Context.restore_mode ctxt;

          val (text, src) = Method.read_closure_input ctxt6 (Token.input_of body);

          val morphism =
            Variable.export_morphism ctxt6
              (ctxt
                |> fold Token.declare_maxidx src
                |> Variable.declare_maxidx (Variable.maxidx_of ctxt6));

          val pats' = map (Term.map_types Type_Infer.paramify_vars #> Morphism.term morphism) pats;
          val _ = ListPair.app (fn ((_, (v, _)), t) => Parse_Tools.the_parse_fun v t) (ts, pats');

          fun close_src src =
            let
              val src' = src |> map (Token.closure #> Token.transform morphism);
              val _ =
                (Token.args_of_src src ~~ Token.args_of_src src')
                |> List.app (fn (tok, tok') =>
                  (case Token.get_value tok' of
                    SOME value => ignore (Token.assign (SOME value) tok)
                  | NONE => ()));
            in src' end;

          val binds' =
            map (Option.map (fn (t, atts) => (Morphism.thm morphism t, map close_src atts))) binds;

          val _ =
            ListPair.app
              (fn ((SOME ((v, _)), _), SOME (t, _)) => Parse_Tools.the_parse_fun v t
                | ((NONE, _), NONE) => ()
                | _ => error "Mismatch between real and parsed bound variables")
              (ts, binds');

          val real_fixes' = map (Morphism.term morphism) real_fixes;
          val _ =
            ListPair.app (fn (((v, _) , _), t) => Parse_Tools.the_parse_fun v t)
              (fixes, real_fixes');

          val match_args = map (fn (_, (_, match_args)) => match_args) ts;
          val binds'' = (binds' ~~ match_args) ~~ pats';

          val src' = map (Token.transform morphism) src;
          val _ = Token.assign (SOME (Token.Source src')) body;
        in
          (binds'', real_fixes', text)
        end));


fun dest_internal_term t =
  (case try Logic.dest_conjunction t of
    SOME (params, head) =>
     (params |> Logic.dest_conjunctions |> map Logic.dest_term,
      head |> Logic.dest_term)
  | NONE => ([], t |> Logic.dest_term));

fun dest_internal_fact thm = dest_internal_term (Thm.prop_of thm);

fun inst_thm ctxt env ts params thm =
  let
    val ts' = map (Envir.norm_term env) ts;
    val insts = map (#1 o dest_Var) ts' ~~ map (Thm.cterm_of ctxt) params;
  in infer_instantiate ctxt insts thm end;

fun do_inst fact_insts' env text ctxt =
  let
    val fact_insts =
      map_filter
        (fn ((((SOME ((_, head), att), _), _), _), thms) => SOME (head, (thms, att))
          | _ => NONE) fact_insts';

    fun try_dest_term thm = \<^try>\<open>#2 (dest_internal_fact thm)\<close>;

    fun expand_fact fact_insts thm =
      the_default [thm]
        (case try_dest_term thm of
          SOME t_ident => AList.lookup (op aconv) fact_insts t_ident
        | NONE => NONE);

    fun fact_morphism fact_insts =
      Morphism.term_morphism "do_inst.term" (Envir.norm_term env) $>
      Morphism.typ_morphism "do_inst.type" (Envir.norm_type (Envir.type_env env)) $>
      Morphism.fact_morphism "do_inst.fact" (maps (expand_fact fact_insts));

    fun apply_attribute (head, (fact, atts)) (fact_insts, ctxt) =
      let
        val morphism = fact_morphism fact_insts;
        val atts' = map (Attrib.attribute ctxt o map (Token.transform morphism)) atts;
        val (fact'', ctxt') = fold_map (Thm.proof_attributes atts') fact ctxt;
      in ((head, fact'') :: fact_insts, ctxt') end;

     (*TODO: What to do about attributes that raise errors?*)
    val (fact_insts', ctxt') = fold_rev (apply_attribute) fact_insts ([], ctxt);

    val text' = (Method.map_source o map) (Token.transform (fact_morphism fact_insts')) text;
  in
    (text', ctxt')
  end;

fun prep_fact_pat ((x, args), pat) ctxt =
  let
    val ((params, pat'), ctxt') = Variable.focus NONE pat ctxt;
    val params' = map (Free o snd) params;

    val morphism =
      Variable.export_morphism ctxt'
        (ctxt |> Variable.declare_maxidx (Variable.maxidx_of ctxt'));
    val pat'' :: params'' = map (Morphism.term morphism) (pat' :: params');

    fun prep_head (t, att) = (dest_internal_fact t, att);
  in
    ((((Option.map prep_head x, args), params''), pat''), ctxt')
  end;

fun morphism_env morphism env =
  let
    val tenv = Envir.term_env env
      |> Vartab.map (K (fn (T, t) => (Morphism.typ morphism T, Morphism.term morphism t)));
    val tyenv = Envir.type_env env
      |> Vartab.map (K (fn (S, T) => (S, Morphism.typ morphism T)));
   in Envir.Envir {maxidx = Envir.maxidx_of env, tenv = tenv, tyenv = tyenv} end;

fun export_with_params ctxt morphism (SOME ts, params) thm env =
      let
        val outer_env = morphism_env morphism env;
        val thm' = Morphism.thm morphism thm;
      in inst_thm ctxt outer_env params ts thm' end
  | export_with_params _ morphism (NONE, _) thm _ = Morphism.thm morphism thm;

fun match_filter_env is_newly_fixed pat_vars fixes params env =
  let
    val param_vars = map Term.dest_Var params;

    val tenv = Envir.term_env env;
    val params' = map (fn (xi, _) => Vartab.lookup tenv xi) param_vars;

    val fixes_vars = map Term.dest_Var fixes;

    val all_vars = Vartab.keys tenv;
    val extra_vars = subtract (fn ((xi, _), xi') => xi = xi') fixes_vars all_vars;

    val tenv' = tenv |> fold (Vartab.delete_safe) extra_vars;
    val env' =
      Envir.Envir {maxidx = Envir.maxidx_of env, tenv = tenv', tyenv = Envir.type_env env};

    val all_params_bound = forall (fn SOME (_, Free (x, _)) => is_newly_fixed x | _ => false) params';
    val all_params_distinct = not (has_duplicates (eq_option (eq_pair (op =) (op aconv))) params');

    val pat_fixes = inter (eq_fst (op =)) fixes_vars pat_vars;
    val all_pat_fixes_bound = forall (fn (xi, _) => is_some (Vartab.lookup tenv' xi)) pat_fixes;
  in
    if all_params_bound andalso all_pat_fixes_bound andalso all_params_distinct
    then SOME env'
    else NONE
  end;


(* Slightly hacky way of uniquely identifying focus premises *)
val prem_idN = "premise_id";

fun prem_id_eq ((id, _ : thm), (id', _ : thm)) = id = id';

val prem_rules : (int * thm) Item_Net.T =
  Item_Net.init prem_id_eq (single o Thm.full_prop_of o snd);

fun raw_thm_to_id thm =
  (case Properties.get (Thm.get_tags thm) prem_idN of NONE => NONE | SOME id => Int.fromString id)
  |> the_default ~1;

structure Focus_Data = Proof_Data
(
  type T =
    (int * (int * thm) Item_Net.T) *  (*prems*)
    Envir.tenv *  (*schematics*)
    term list  (*params*)
  fun init _ : T = ((0, prem_rules), Vartab.empty, [])
);


(* focus prems *)

val focus_prems = #1 o Focus_Data.get;

fun transfer_focus_prems from_ctxt =
  Focus_Data.map (@{apply 3(1)} (K (focus_prems from_ctxt)))


fun add_focus_prem prem =
  `(Focus_Data.get #> #1 #> #1) ##>
  (Focus_Data.map o @{apply 3(1)}) (fn (next, net) =>
    (next + 1, Item_Net.update (next, Thm.tag_rule (prem_idN, string_of_int next) prem) net));

fun remove_focus_prem' (ident, thm) =
  (Focus_Data.map o @{apply 3(1)} o apsnd)
    (Item_Net.remove (ident, thm));

fun remove_focus_prem thm = remove_focus_prem' (raw_thm_to_id thm, thm);

(*TODO: Preliminary analysis to see if we're trying to clear in a non-focus match?*)
val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>thin\<close>
      (Scan.succeed
        (Thm.declaration_attribute (fn th => Context.mapping I (remove_focus_prem th))))
        "clear premise inside match method");


(* focus schematics *)

val focus_schematics = #2 o Focus_Data.get;

fun add_focus_schematics schematics =
  (Focus_Data.map o @{apply 3(2)})
    (fold (fn ((xi, T), ct) => Vartab.update_new (xi, (T, Thm.term_of ct))) schematics);


(* focus params *)

val focus_params = #3 o Focus_Data.get;

fun add_focus_params params =
  (Focus_Data.map o @{apply 3(3)})
    (append (map (fn (_, ct) => Thm.term_of ct) params));


(* Add focus elements as proof data *)
fun augment_focus (focus: Subgoal.focus) : (int list * Subgoal.focus) =
  let
    val {context, params, prems, asms, concl, schematics} = focus;

    val (prem_ids, ctxt') = context
      |> add_focus_params params
      |> add_focus_schematics (snd schematics)
      |> fold_map add_focus_prem (rev prems)

  in
    (prem_ids,
      {context = ctxt',
       params = params,
       prems = prems,
       concl = concl,
       schematics = schematics,
       asms = asms})
  end;


(* Fix schematics in the goal *)
fun focus_concl ctxt i bindings goal =
  let
    val ({context = ctxt', concl, params, prems, asms, schematics}, goal') =
      Subgoal.focus_params ctxt i bindings goal;

    val (inst, ctxt'') = Variable.import_inst true [Thm.term_of concl] ctxt';
    val schematic_terms = map (apsnd (Thm.cterm_of ctxt'')) (#2 inst);

    val goal'' = Thm.instantiate ([], schematic_terms) goal';
    val concl' = Thm.instantiate_cterm ([], schematic_terms) concl;
    val (schematic_types, schematic_terms') = schematics;
    val schematics' = (schematic_types, schematic_terms @ schematic_terms');
  in
    ({context = ctxt'', concl = concl', params = params, prems = prems,
      schematics = schematics', asms = asms} : Subgoal.focus, goal'')
  end;


fun deduplicate eq prev seq =
  Seq.make (fn () =>
    (case Seq.pull seq of
      SOME (x, seq') =>
        if member eq prev x
        then Seq.pull (deduplicate eq prev seq')
        else SOME (x, deduplicate eq (x :: prev) seq')
    | NONE => NONE));


fun consistent_env env =
  let
    val tenv = Envir.term_env env;
    val tyenv = Envir.type_env env;
  in
    forall (fn (_, (T, t)) => Envir.norm_type tyenv T = fastype_of t) (Vartab.dest tenv)
  end;

fun term_eq_wrt (env1, env2) (t1, t2) =
  Envir.eta_contract (Envir.norm_term env1 t1) aconv
  Envir.eta_contract (Envir.norm_term env2 t2);

fun type_eq_wrt (env1, env2) (T1, T2) =
  Envir.norm_type (Envir.type_env env1) T1 = Envir.norm_type (Envir.type_env env2) T2;


fun eq_env (env1, env2) =
    Envir.maxidx_of env1 = Envir.maxidx_of env1 andalso
    ListPair.allEq (fn ((var, (_, t)), (var', (_, t'))) =>
        (var = var' andalso term_eq_wrt (env1, env2) (t, t')))
      (apply2 Vartab.dest (Envir.term_env env1, Envir.term_env env2))
    andalso
    ListPair.allEq (fn ((var, (_, T)), (var', (_, T'))) =>
        var = var' andalso type_eq_wrt (env1, env2) (T, T'))
      (apply2 Vartab.dest (Envir.type_env env1, Envir.type_env env2));


fun merge_env (env1, env2) =
  let
    val tenv =
      Vartab.merge (eq_snd (term_eq_wrt (env1, env2))) (Envir.term_env env1, Envir.term_env env2);
    val tyenv =
      Vartab.merge (eq_snd (type_eq_wrt (env1, env2)) andf eq_fst (op =))
        (Envir.type_env env1, Envir.type_env env2);
    val maxidx = Int.max (Envir.maxidx_of env1, Envir.maxidx_of env2);
  in Envir.Envir {maxidx = maxidx, tenv = tenv, tyenv = tyenv} end;


fun import_with_tags thms ctxt =
  let
    val ((_, thms'), ctxt') = Variable.import false thms ctxt;
    val thms'' = map2 (fn thm => Thm.map_tags (K (Thm.get_tags thm))) thms thms';
  in (thms'', ctxt') end;


fun try_merge (env, env') = SOME (merge_env (env, env')) handle Vartab.DUP _ => NONE


fun Seq_retrieve seq f =
  let
    fun retrieve' (list, seq) f =
      (case Seq.pull seq of
        SOME (x, seq') =>
          if f x then (SOME x, (list, seq'))
          else retrieve' (list @ [x], seq') f
      | NONE => (NONE, (list, seq)));

    val (result, (list, seq)) = retrieve' ([], seq) f;
  in (result, Seq.append (Seq.of_list list) seq) end;

fun match_facts ctxt fixes prop_pats get =
  let
    fun is_multi (((_, x : match_args), _), _) = #multi x;
    fun get_cut (((_, x : match_args), _), _) = #cut x;
    fun do_cut n = if n = ~1 then I else Seq.take n;

    val raw_thmss = map (get o snd) prop_pats;
    val (thmss, ctxt') = fold_burrow import_with_tags raw_thmss ctxt;

    val newly_fixed = Variable.is_newly_fixed ctxt' ctxt;

    val morphism = Variable.export_morphism ctxt' ctxt;

    fun match_thm (((x, params), pat), thm)  =
      let
        val pat_vars = Term.add_vars pat [];

        val ts = Option.map (fst o fst) (fst x);

        val item' = Thm.prop_of thm;

        val matches =
          (Unify.matchers (Context.Proof ctxt) [(pat, item')])
          |> Seq.filter consistent_env
          |> Seq.map_filter (fn env' =>
              (case match_filter_env newly_fixed pat_vars fixes params env' of
                SOME env'' => SOME (export_with_params ctxt morphism (ts, params) thm env', env'')
              | NONE => NONE))
          |> Seq.map (apfst (Thm.map_tags (K (Thm.get_tags thm))))
          |> deduplicate (eq_pair Thm.eq_thm_prop eq_env) []
      in matches end;

    val all_matches =
      map2 pair prop_pats thmss
      |> map (fn (pat, matches) => (pat, map (fn thm => match_thm (pat, thm)) matches));

    fun proc_multi_match (pat, thmenvs) (pats, env) =
      do_cut (get_cut pat)
        (if is_multi pat then
          let
            fun maximal_set tail seq envthms =
              Seq.make (fn () =>
                (case Seq.pull seq of
                  SOME ((thm, env'), seq') =>
                    let
                      val (result, envthms') =
                        Seq_retrieve envthms (fn (env, _) => eq_env (env, env'));
                    in        
                      (case result of
                        SOME (_, thms) => SOME ((env', thm :: thms), maximal_set tail seq' envthms')
                      | NONE => Seq.pull (maximal_set (tail @ [(env', [thm])]) seq' envthms'))
                    end
                 | NONE => Seq.pull (Seq.append envthms (Seq.of_list tail))));

            val maximal_sets = fold (maximal_set []) thmenvs Seq.empty;
          in
            maximal_sets
            |> Seq.map swap
            |> Seq.filter (fn (thms, _) => not (null thms))
            |> Seq.map_filter (fn (thms, env') =>
              (case try_merge (env, env') of
                SOME env'' => SOME ((pat, thms) :: pats, env'')
              | NONE => NONE))
          end
        else
          let
            fun just_one (thm, env') =
              (case try_merge (env, env') of
                SOME env'' => SOME ((pat, [thm]) :: pats, env'')
              | NONE => NONE);
          in fold (fn seq => Seq.append (Seq.map_filter just_one seq)) thmenvs Seq.empty end);

    val all_matches =
      Seq.EVERY (map proc_multi_match all_matches) ([], Envir.init);
  in
    all_matches
    |> Seq.map (apsnd (morphism_env morphism))
  end;

fun real_match using outer_ctxt fixes m text pats st =
  let              
    val goal_ctxt =
      fold Variable.declare_term fixes outer_ctxt
      (*FIXME Is this a good idea? We really only care about the maxidx*)
      |> fold (fn (_, t) => Variable.declare_term t) pats;

    fun make_fact_matches ctxt get =
      let
        val (pats', ctxt') = fold_map prep_fact_pat pats ctxt;
      in
        match_facts ctxt' fixes pats' get
        |> Seq.map (fn (fact_insts, env) => do_inst fact_insts env text ctxt')
      end;

    fun make_term_matches ctxt get =
      let
        val pats' = map
          (fn ((SOME _, _), _) => error "Cannot name term match"
            | ((_, x), t) => (((NONE, x), []), Logic.mk_term t)) pats;

        val thm_of = Drule.mk_term o Thm.cterm_of ctxt;
        fun get' t = get (Logic.dest_term t) |> map thm_of;
      in
        match_facts ctxt fixes pats' get'
        |> Seq.map (fn (fact_insts, env) => do_inst fact_insts env text ctxt)
      end;
  in
    (case m of
      Match_Fact net =>
        make_fact_matches goal_ctxt (Item_Net.retrieve net)
        |> Seq.map (fn (text, ctxt') =>
          Method.evaluate_runtime text ctxt' using (ctxt', st)
          |> Seq.filter_results |> Seq.map (fn (_, thm) => (outer_ctxt, thm)))
    | Match_Term net =>
        make_term_matches goal_ctxt (Item_Net.retrieve net)
        |> Seq.map (fn (text, ctxt') =>
          Method.evaluate_runtime text ctxt' using (ctxt', st)
          |> Seq.filter_results |> Seq.map (fn (_, thm) => (outer_ctxt, thm)))
    | match_kind =>
        if Thm.no_prems st then Seq.empty
        else
          let
            fun focus_cases f g =
              (case match_kind of
                Match_Prems b => f b
              | Match_Concl => g
              | _ => raise Fail "Match kind fell through");

            val ((local_premids, {context = focus_ctxt, params, asms, concl, prems, ...}), focused_goal) =
              focus_cases (K Subgoal.focus_prems) focus_concl goal_ctxt 1 NONE st
              |>> augment_focus;
            
            val texts =
              focus_cases
                (fn is_local => fn _ =>
                  make_fact_matches focus_ctxt
                    (Item_Net.retrieve (focus_prems focus_ctxt |> snd)
                     #> is_local ? filter (fn (p, _) => exists (fn id' => id' = p) local_premids)
                     #> order_list))
                (fn _ =>
                  make_term_matches focus_ctxt
                    (fn _ => [Logic.strip_imp_concl (Thm.term_of concl)]))
                ();

            (*TODO: How to handle cases? *)

            fun do_retrofit (inner_ctxt, st1) =
              let
                val (_, before_prems) = focus_prems focus_ctxt;
                val (_, after_prems) = focus_prems inner_ctxt;

                val removed_prems =
                  Item_Net.filter (null o Item_Net.lookup after_prems) before_prems

                val removed_local_prems = Item_Net.content removed_prems
                  |> filter (fn (id, _) => member (op =) local_premids id)
                  |> map (fn (_, prem) => Thm.prop_of prem)

                fun filter_removed_prems prems =
                  Item_Net.filter (null o Item_Net.lookup removed_prems) prems;
                                     
                val outer_ctxt' = outer_ctxt 
                  |> Focus_Data.map (@{apply 3(1)} (apsnd filter_removed_prems));

                val n_subgoals = Thm.nprems_of st1;

                val removed_prem_idxs = 
                  prems
                  |> tag_list 0
                  |> filter (member (op aconv) removed_local_prems o Thm.prop_of o snd)
                  |> map fst

                fun filter_prem (i, _) = not (member (op =) removed_prem_idxs i); 

              in
                Subgoal.retrofit inner_ctxt goal_ctxt params asms 1 st1 st
                |> focus_cases 
                   (fn _ => (n_subgoals > 0 andalso length removed_local_prems > 0) ?
                    (Seq.map (Goal.restrict 1 n_subgoals)
                      #> Seq.maps (ALLGOALS (fn i =>
                          DETERM (filter_prems_tac' goal_ctxt filter_prem i)))
                      #> Seq.map (Goal.unrestrict 1)))
                   I
                |> Seq.map (pair outer_ctxt')
              end;

            fun apply_text (text, ctxt') =
                Method.evaluate_runtime text ctxt' using (ctxt', focused_goal)
              |> Seq.filter_results
              |> Seq.maps (Seq.DETERM do_retrofit)             

          in Seq.map apply_text texts end)
  end;

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>match\<close>
      (parse_match_kind :--
        (fn kind => Scan.lift \<^keyword>\<open>in\<close> |-- Parse.enum1' "\<bar>" (parse_named_pats kind)) >>
        (fn (matches, bodies) => fn ctxt =>
          CONTEXT_METHOD (fn using => Method.RUNTIME (fn (goal_ctxt, st) =>
            let
              val ctxt' = transfer_focus_prems goal_ctxt ctxt;
              fun exec (pats, fixes, text) st' =
                real_match using ctxt' fixes matches text pats st';
            in
              Seq.flat (Seq.FIRST (map exec bodies) st)
              |> Seq.map (apfst (fn ctxt' => transfer_focus_prems ctxt' goal_ctxt))
              |> Seq.make_results
            end))))
      "structural analysis/matching on goals");

end;
