(*  Title:      match_method.ML
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

(*Variant of filter_prems_tac with auxiliary configuration;
  recovers premise order afterwards.*)
fun filter_prems_tac' ctxt prep pred a =
  let
    fun Then NONE tac = SOME tac
      | Then (SOME tac) tac' = SOME (tac THEN' tac');
    fun thins H (tac, n, a, i) =
      (case pred a H of
        NONE => (tac, n + 1, a, i)
      | SOME a' => (Then tac (rotate_tac n THEN' eresolve_tac ctxt [thin_rl]), 0, a', i + n));
  in
    SUBGOAL (fn (goal, i) =>
      let val Hs = Logic.strip_assums_hyp (prep goal) in
        (case fold thins Hs (NONE, 0, a, 0) of
          (NONE, _, _, _) => no_tac
        | (SOME tac, _, _, n) => tac i THEN rotate_tac (~ n) i)
      end)
  end;


datatype match_kind =
    Match_Term of term Item_Net.T
  | Match_Fact of thm Item_Net.T
  | Match_Concl
  | Match_Prems;


val aconv_net = Item_Net.init (op aconv) single;

val parse_match_kind =
  Scan.lift @{keyword "conclusion"} >> K Match_Concl ||
  Scan.lift @{keyword "premises"} >> K Match_Prems ||
  Scan.lift (@{keyword "("}) |-- Args.term --| Scan.lift (@{keyword ")"}) >>
    (fn t => Match_Term (Item_Net.update t aconv_net)) ||
  Attrib.thms >> (fn thms => Match_Fact (fold Item_Net.update thms Thm.full_rules));


fun nameable_match m = (case m of Match_Fact _ => true | Match_Prems => true | _ => false);
fun prop_match m = (case m of Match_Term _ => false | _ => true);

val bound_term : (term, binding) Parse_Tools.parse_val parser =
  Parse_Tools.parse_term_val Parse.binding;

val fixes =
  Parse.and_list1 (Scan.repeat1  (Parse.position bound_term) --
    Scan.option (@{keyword "::"} |-- Parse.!!! Parse.typ) >> (fn (xs, T) => map (fn (nm,pos) => ((nm,T),pos)) xs))
  >> flat;

val for_fixes = Scan.optional (@{keyword "for"} |-- fixes) [];

fun pos_of dyn =
  (case dyn of
    Parse_Tools.Parse_Val (b, _) => Binding.pos_of b
  | _ => raise Fail "Not a parse value");


(*FIXME: Dynamic facts modify the background theory, so we have to resort
  to token replacement for matched facts. *)
fun dynamic_fact ctxt =
  bound_term -- Args.opt_attribs (Attrib.check_name ctxt);

type match_args = {multi : bool, cut : bool};

val parse_match_args =
  Scan.optional (Args.parens (Parse.enum1 ","
    (Args.$$$ "multi" || Args.$$$ "cut"))) [] >>
    (fn ss =>
      fold (fn s => fn {multi, cut} =>
        (case s of
         "multi" => {multi = true, cut = cut}
        | "cut" => {multi = multi, cut = true}))
      ss {multi = false, cut = false});

(*TODO: Shape holes in thms *)
fun parse_named_pats match_kind =
  Args.context :|-- (fn ctxt =>
    Scan.lift (Parse.and_list1 (Scan.option (dynamic_fact ctxt --| Args.colon) :--
      (fn opt_dyn =>
        if is_none opt_dyn orelse nameable_match match_kind
        then Parse_Tools.name_term -- parse_match_args
        else
          let val b = #1 (the opt_dyn)
          in error ("Cannot bind fact name in term match" ^ Position.here (pos_of b)) end))
    -- for_fixes -- (@{keyword "\<Rightarrow>"} |-- Parse.token Parse.cartouche))
  >> (fn ((ts, fixes), cartouche) =>
    (case Token.get_value cartouche of
      SOME (Token.Source src) =>
        let
          val text = Method_Closure.read_inner_method ctxt src
          (*TODO: Correct parse context for attributes?*)
          val ts' =
            map
              (fn (b, (Parse_Tools.Real_Val v, match_args)) =>
                ((Option.map (fn (b, att) =>
                  (Parse_Tools.the_real_val b,
                    map (Attrib.attribute ctxt) att)) b, match_args), v)
                | _ => raise Fail "Expected closed term") ts
          val fixes' = map (fn ((p, _),_) => Parse_Tools.the_real_val p) fixes
        in (ts', fixes', text) end
    | SOME _ => error "Unexpected token value in match cartouche"
    | NONE =>
        let
          val fixes' = map (fn ((pb, otyp),_) => (Parse_Tools.the_parse_val pb, otyp, NoSyn)) fixes;
          val (fixes'', ctxt1) = Proof_Context.read_vars fixes' ctxt;
          val (fix_nms, ctxt2) = Proof_Context.add_fixes fixes'' ctxt1;

          val ctxt3 = Proof_Context.set_mode Proof_Context.mode_schematic ctxt2;

          fun parse_term term =
            if prop_match match_kind
            then Syntax.parse_prop ctxt3 term
            else Syntax.parse_term ctxt3 term;

          val pats =
            map (fn (_, (term, _)) => parse_term (Parse_Tools.the_parse_val term)) ts
            |> Syntax.check_terms ctxt3;

          val pat_fixes = fold (Term.add_frees) pats [] |> map fst;

          val _ = map2 (fn nm => fn (_,pos) => member (op =) pat_fixes nm orelse
            error ("For-fixed variable must be bound in some pattern." ^ Position.here pos))
            fix_nms fixes;

          val _ = map (Term.map_types Type.no_tvars) pats

          val ctxt4 = fold Variable.declare_term pats ctxt3;

          val (Ts, ctxt5) = ctxt4 |> fold_map Proof_Context.inferred_param fix_nms;

          val real_fixes = map Free (fix_nms ~~ Ts);

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
                    |> Drule.generalize ([], map fst abs_nms);

                  val thm =
                    Thm.cterm_of ctxt' (Free (nm, propT))
                    |> Drule.mk_term
                    |> not (null abs_nms) ? Conjunction.intr param_thm
                    |> Drule.zero_var_indexes
                    |> Method_Closure.tag_free_thm;

                  (*TODO: Preprocess attributes here?*)

                  val (_, ctxt'') = Proof_Context.note_thmss "" [((b, []), [([thm], [])])] ctxt';
                in
                  (SOME (Thm.prop_of thm, map (Attrib.attribute ctxt) att) :: tms, ctxt'')
                end
            | upd_ctxt NONE _ (tms, ctxt) = (NONE :: tms, ctxt);

          val (binds, ctxt6) = ctxt5
            |> (fn ctxt => fold2 upd_ctxt binds pats ([], ctxt) |> apfst rev)
            ||> Proof_Context.restore_mode ctxt;

          val (src, text) = Method_Closure.read_inner_text_closure ctxt6 (Token.input_of cartouche);

          val morphism =
            Variable.export_morphism ctxt6
              (ctxt
                |> Token.declare_maxidx_src src
                |> Variable.declare_maxidx (Variable.maxidx_of ctxt6));

          val pats' = map (Term.map_types Type_Infer.paramify_vars #> Morphism.term morphism) pats;
          val _ = ListPair.app (fn ((_, (Parse_Tools.Parse_Val (_, f), _)), t) => f t) (ts, pats');

          val binds' = map (Option.map (fn (t, atts) => (Morphism.term morphism t, atts))) binds;

          val _ =
            ListPair.app
              (fn ((SOME ((Parse_Tools.Parse_Val (_, f), _)), _), SOME (t, _)) => f t
                | ((NONE, _), NONE) => ()
                | _ => error "Mismatch between real and parsed bound variables")
              (ts, binds');

          val real_fixes' = map (Morphism.term morphism) real_fixes;
          val _ =
            ListPair.app (fn (( (Parse_Tools.Parse_Val (_, f),_) , _), t) => f t) (fixes, real_fixes');

          val match_args = map (fn (_, (_, match_args)) => match_args) ts;
          val binds'' = (binds' ~~ match_args) ~~ pats';

          val src' = Token.transform_src morphism src;
          val _ = Token.assign (SOME (Token.Source src')) cartouche;
        in
          (binds'', real_fixes', text)
        end)));


fun parse_match_bodies match_kind =
  Parse.enum1' "\<bar>" (parse_named_pats match_kind);


fun dest_internal_fact t =
  (case try Logic.dest_conjunction t of
    SOME (params, head) =>
     (params |> Logic.dest_conjunctions |> map Logic.dest_term,
      head |> Logic.dest_term)
  | NONE => ([], t |> Logic.dest_term));


fun inst_thm ctxt env ts params thm =
  let
    val ts' = map (Envir.norm_term env) ts;
    val insts = map (Thm.cterm_of ctxt) ts' ~~ map (Thm.cterm_of ctxt) params;

  in
    Drule.cterm_instantiate insts thm
  end;

fun do_inst fact_insts' env text ctxt =
  let
    val fact_insts =
      map_filter
        (fn ((((SOME ((_, head), att), _), _), _), thms) => SOME (head, (thms, att))
          | _ => NONE) fact_insts';

    fun apply_attribute thm att ctxt =
      let
        val (opt_context', thm') = att (Context.Proof ctxt, thm)
      in
        (case thm' of
          SOME _ => error "Rule attributes cannot be applied here"
        | _ => the_default ctxt (Option.map Context.proof_of opt_context'))
      end;

    fun apply_attributes atts thm = fold (apply_attribute thm) atts;

     (*TODO: What to do about attributes that raise errors?*)
    val (fact_insts, ctxt') =
      fold_map (fn (head, (thms, atts : attribute list)) => fn ctxt =>
        ((head, thms), fold (apply_attributes atts) thms ctxt)) fact_insts ctxt;

    fun try_dest_term thm = try (Thm.prop_of #> dest_internal_fact #> snd) thm;

    fun expand_fact thm =
      the_default [thm]
        (case try_dest_term thm of
          SOME t_ident => AList.lookup (op aconv) fact_insts t_ident
        | NONE => NONE);

    val morphism =
      Morphism.term_morphism "do_inst.term" (Envir.norm_term env) $>
      Morphism.typ_morphism "do_inst.type" (Envir.norm_type (Envir.type_env env)) $>
      Morphism.fact_morphism "do_inst.fact" (maps expand_fact);

    val text' = Method.map_source (Token.transform_src morphism) text;
  in
    (text', ctxt')
  end;

fun DROP_CASES (tac: cases_tactic) : tactic =
  tac #> Seq.map (fn (_, st) => st);

fun prep_fact_pat ((x, args), pat) ctxt =
  let
    val ((params, pat'), ctxt') = Variable.focus pat ctxt;
    val params' = map (Free o snd) params;

    val morphism =
      Variable.export_morphism ctxt'
        (ctxt |> Variable.declare_maxidx (Variable.maxidx_of ctxt'));
    val pat'' :: params'' = map (Morphism.term morphism) (pat' :: params');

    fun prep_head (t, att) = (dest_internal_fact t, att);

  in
    ((((Option.map prep_head x, args), params''), pat''), ctxt')
  end;

fun recalculate_maxidx env =
  let
    val tenv = Envir.term_env env;
    val tyenv = Envir.type_env env;
    val max_tidx = Vartab.fold (fn (_,(_,t)) => curry Int.max (maxidx_of_term t)) tenv ~1;
    val max_Tidx = Vartab.fold (fn (_,(_,T)) => curry Int.max (maxidx_of_typ T)) tyenv ~1;
  in
    Envir.Envir
      {maxidx = Int.max (Int.max (max_tidx,max_Tidx),Envir.maxidx_of env),
        tenv = tenv, tyenv = tyenv}
  end

fun match_filter_env inner_ctxt morphism pat_vars fixes (ts, params) thm inner_env =
  let
    val tenv = Envir.term_env inner_env
      |> Vartab.map (K (fn (T,t) => (Morphism.typ morphism T,Morphism.term morphism t)));

    val tyenv = Envir.type_env inner_env
      |> Vartab.map (K (fn (S,T) => (S,Morphism.typ morphism T)));

    val outer_env = Envir.Envir {maxidx = Envir.maxidx_of inner_env, tenv = tenv, tyenv = tyenv};

    val param_vars = map Term.dest_Var params;

    val params' = map (fn (xi,_) => Vartab.lookup (Envir.term_env outer_env) xi) param_vars;

    val fixes_vars = map Term.dest_Var fixes;

    val all_vars = Vartab.keys tenv;

    val extra_vars = subtract (fn ((xi, _), xi') => xi = xi') fixes_vars all_vars;

    val tenv' = tenv
      |> fold (Vartab.delete_safe) extra_vars;

    val env' =
      Envir.Envir {maxidx = Envir.maxidx_of outer_env, tenv = tenv', tyenv = tyenv}
      |> recalculate_maxidx;

    val all_params_bound = forall (fn SOME (_,(Var _)) => true | _ => false) params';

    val pat_fixes = inter (eq_fst (op =)) fixes_vars pat_vars;

    val all_pat_fixes_bound = forall (fn (xi,_) => is_some (Vartab.lookup tenv' xi)) pat_fixes;

    val thm' = Morphism.thm morphism thm;

  in
    if all_params_bound andalso all_pat_fixes_bound then
      SOME (case ts of SOME ts => inst_thm inner_ctxt outer_env params ts thm' | _ => thm', env')
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

fun add_focus_prem prem =
  (Focus_Data.map o @{apply 3(1)}) (fn (next, net) =>
    (next + 1, Item_Net.update (next, Thm.tag_rule (prem_idN, string_of_int next) prem) net));

fun remove_focus_prem thm =
  (Focus_Data.map o @{apply 3(1)} o apsnd)
    (Item_Net.remove (raw_thm_to_id thm, thm));

(*TODO: Preliminary analysis to see if we're trying to clear in a non-focus match?*)
val _ =
  Theory.setup
    (Attrib.setup @{binding "thin"}
      (Scan.succeed
        (Thm.declaration_attribute (fn th => Context.mapping I (remove_focus_prem th))))
        "clear premise inside match method");


(* focus schematics *)

val focus_schematics = #2 o Focus_Data.get;

fun add_focus_schematics cterms =
  (Focus_Data.map o @{apply 3(2)})
    (fold (fn (Var (xi, T), t) => Vartab.update_new (xi, (T, t)))
      (map (apply2 Thm.term_of) cterms));


(* focus params *)

val focus_params = #3 o Focus_Data.get;

fun add_focus_params params =
  (Focus_Data.map o @{apply 3(3)})
    (append (map (fn (_, ct) => Thm.term_of ct) params));


(* Add focus elements as proof data *)
fun augment_focus
    ({context, params, prems, asms, concl, schematics} : Subgoal.focus) : Subgoal.focus =
  let
    val context' = context
      |> add_focus_params params
      |> add_focus_schematics (snd schematics)
      |> fold add_focus_prem (rev prems);
  in
    {context = context',
     params = params,
     prems = prems,
     concl = concl,
     schematics = schematics,
     asms = asms}
  end;


(* Fix schematics in the goal *)
fun focus_concl ctxt i goal =
  let
    val ({context, concl, params, prems, asms, schematics}, goal') =
      Subgoal.focus_params ctxt i goal;

    val ((_, schematic_terms), context') =
      Variable.import_inst true [Thm.term_of concl] context
      |>> Thm.certify_inst (Thm.theory_of_thm goal');

    val goal'' = Thm.instantiate ([], schematic_terms) goal';
    val concl' = Thm.instantiate_cterm ([], schematic_terms) concl;
    val (schematic_types, schematic_terms') = schematics;
    val schematics' = (schematic_types, schematic_terms @ schematic_terms');
  in
    ({context = context', concl = concl', params = params, prems = prems,
      schematics = schematics', asms = asms} : Subgoal.focus, goal'')
  end;

exception MATCH_CUT;

val raise_match : (thm * Envir.env) Seq.seq = Seq.make (fn () => raise MATCH_CUT);

fun map_handle seq =
  Seq.make (fn () =>
    (case (Seq.pull seq handle MATCH_CUT => NONE) of
      SOME (x, seq') => SOME (x, map_handle seq')
    | NONE => NONE));

fun deduplicate eq prev seq =
  Seq.make (fn () =>
    (case (Seq.pull seq) of
      SOME (x, seq') =>
        if member eq prev x
        then Seq.pull (deduplicate eq prev seq')
        else SOME (x,deduplicate eq (x :: prev) seq')
    | NONE => NONE));

fun consistent_env env =
  let
    val tenv = Envir.term_env env;
    val tyenv = Envir.type_env env;
  in
    forall (fn (_, (T, t)) => Envir.norm_type tyenv T = fastype_of t) (Vartab.dest tenv)
  end;

fun eq_env (env1,env2) =
  let
    val tyenv1 = Envir.type_env env1;
    val tyenv2 = Envir.type_env env2;
  in
    Envir.maxidx_of env1 = Envir.maxidx_of env1 andalso
    ListPair.allEq (fn ((var, (_, t)), (var', (_, t'))) =>
        (var = var' andalso
          Envir.eta_contract (Envir.norm_term env1 t) aconv
          Envir.eta_contract (Envir.norm_term env2 t')))
      (apply2 Vartab.dest (Envir.term_env env1, Envir.term_env env2))
    andalso
    ListPair.allEq (fn ((var, (_, T)), (var', (_,T'))) =>
        var = var' andalso Envir.norm_type tyenv1 T = Envir.norm_type tyenv2 T')
      (apply2 Vartab.dest (Envir.type_env env1, Envir.type_env env2))
  end;


fun match_facts ctxt fixes prop_pats get =
  let
    fun is_multi (((_, x : match_args), _), _) = #multi x;
    fun is_cut (_, x : match_args) = #cut x;

    fun match_thm (((x, params), pat), thm) env  =
      let
        fun try_dest_term term = the_default term (try Logic.dest_term term);

        val pat_vars = Term.add_vars pat [];

        val pat' = pat |> Envir.norm_term env |> try_dest_term;

        val (((Tinsts', insts),[thm']), inner_ctxt) = Variable.import false [thm] ctxt

        val item' = Thm.prop_of thm' |> try_dest_term;

        val ts = Option.map (fst o fst) (fst x);

        val outer_ctxt = ctxt |> Variable.declare_maxidx (Envir.maxidx_of env);

        val morphism = Variable.export_morphism inner_ctxt outer_ctxt;

        val matches =
          (Unify.matchers (Context.Proof ctxt) [(pat', item')])
          |> Seq.filter consistent_env
          |> Seq.map_filter (fn env' =>
              match_filter_env inner_ctxt morphism pat_vars fixes
                (ts, params) thm' (Envir.merge (env, env')))
          |> Seq.map (apfst (Thm.map_tags (K (Thm.get_tags thm))))
          |> deduplicate (eq_snd eq_env) []
          |> is_cut x ? (fn t => Seq.make (fn () =>
            Option.map (fn (x, _) => (x, raise_match)) (Seq.pull t)));
      in
        matches
      end;

    val all_matches =
      map (fn pat => (pat, get (snd pat))) prop_pats
      |> map (fn (pat, matches) => (pat, map (fn thm => match_thm (pat, thm)) matches));

    fun proc_multi_match (pat, thmenvs) (pats, env) =
      if is_multi pat then
        let
          val empty = ([], Envir.empty ~1);

          val thmenvs' =
            Seq.EVERY (map (fn e => fn (thms, env) =>
              Seq.append (Seq.map (fn (thm, env') => (thm :: thms, env')) (e env))
                (Seq.single (thms, env))) thmenvs) empty;
        in
          Seq.map_filter (fn (fact, env') =>
            if not (null fact) then SOME ((pat, fact) :: pats, env') else NONE) thmenvs'
        end
      else
        fold (fn e => Seq.append (Seq.map (fn (thm, env') =>
          ((pat, [thm]) :: pats, env')) (e env))) thmenvs Seq.empty;

    val all_matches =
      Seq.EVERY (map proc_multi_match all_matches) ([], Envir.empty ~1)
  in
    map_handle all_matches
  end;

fun real_match using ctxt fixes m text pats goal =
  let
    fun make_fact_matches ctxt get =
      let
        val (pats', ctxt') = fold_map prep_fact_pat pats ctxt;
      in
        match_facts ctxt' fixes pats' get
        |> Seq.map (fn (fact_insts, env) => do_inst fact_insts env text ctxt')
      end;

    (*TODO: Slightly hacky re-use of fact match implementation in plain term matching *)
    fun make_term_matches ctxt get =
      let
        val pats' =
          map
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
        Seq.map (fn (text, ctxt') => Method_Closure.method_evaluate text ctxt' using goal)
          (make_fact_matches ctxt (Item_Net.retrieve net))
    | Match_Term net =>
        Seq.map (fn (text, ctxt') => Method_Closure.method_evaluate text ctxt' using goal)
          (make_term_matches ctxt (Item_Net.retrieve net))
    | match_kind =>
        if Thm.no_prems goal then Seq.empty
        else
          let
            fun focus_cases f g =
              (case match_kind of
                Match_Prems => f
              | Match_Concl => g
              | _ => raise Fail "Match kind fell through");

            val ({context = focus_ctxt, params, asms, concl, ...}, focused_goal) =
              focus_cases (Subgoal.focus_prems) (focus_concl) ctxt 1 goal
              |>> augment_focus;

            val texts =
              focus_cases
                (fn _ =>
                  make_fact_matches focus_ctxt
                    (Item_Net.retrieve (focus_prems focus_ctxt |> snd) #>
                  order_list))
                (fn _ =>
                  make_term_matches focus_ctxt (fn _ => [Logic.strip_imp_concl (Thm.term_of concl)]))
                ();

            (*TODO: How to handle cases? *)

            fun do_retrofit inner_ctxt goal' =
              let
                val cleared_prems =
                  subtract (eq_fst (op =))
                    (focus_prems inner_ctxt |> snd |> Item_Net.content)
                    (focus_prems focus_ctxt |> snd |> Item_Net.content)
                  |> map (fn (_, thm) =>
                    Thm.hyps_of thm
                    |> (fn [hyp] => hyp | _ => error "Prem should have only one hyp"));

                val n_subgoals = Thm.nprems_of goal';
                fun prep_filter t =
                  Term.subst_bounds (map (Thm.term_of o snd) params |> rev, Term.strip_all_body t);
                fun filter_test prems t =
                  if member (op =) prems t then SOME (remove1 (op aconv) t prems) else NONE;
              in
                Subgoal.retrofit inner_ctxt ctxt params asms 1 goal' goal |>
                (if n_subgoals = 0 orelse null cleared_prems then I
                 else
                  Seq.map (Goal.restrict 1 n_subgoals)
                  #> Seq.maps (ALLGOALS (fn i =>
                      DETERM (filter_prems_tac' ctxt prep_filter filter_test cleared_prems i)))
                  #> Seq.map (Goal.unrestrict 1))
              end;

            fun apply_text (text, ctxt') =
              let
                val goal' =
                  DROP_CASES (Method_Closure.method_evaluate text ctxt' using) focused_goal
                  |> Seq.maps (DETERM (do_retrofit ctxt'))
                  |> Seq.map (fn goal => ([]: cases, goal))
              in goal' end;
          in
            Seq.map apply_text texts
          end)
  end;

val match_parser =
  parse_match_kind :-- (fn kind => Scan.lift @{keyword "in"} |-- parse_match_bodies kind) >>
    (fn (matches, bodies) => fn ctxt => fn using => fn goal =>
      if Method_Closure.is_dummy goal then Seq.empty
      else
        let
          fun exec (pats, fixes, text) goal =
            let
              val ctxt' = fold Variable.declare_term fixes ctxt
              |> fold (fn (_, t) => Variable.declare_term t) pats; (*Is this a good idea? We really only care about the maxidx*)
            in
              real_match using ctxt' fixes matches text pats goal
            end;
        in
          Seq.FIRST (map exec bodies) goal
          |> Seq.flat
        end);

val _ =
  Theory.setup
    (Method.setup @{binding match}
      (match_parser >> (fn m => fn ctxt => METHOD_CASES (m ctxt)))
      "structural analysis/matching on goals");

end;
