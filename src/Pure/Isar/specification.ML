(*  Title:      Pure/Isar/specification.ML
    Author:     Makarius

Derived local theory specifications --- with type-inference and
toplevel polymorphism.
*)

signature SPECIFICATION =
sig
  val read_props: string list -> (binding * string option * mixfix) list -> Proof.context ->
    term list * Proof.context
  val read_prop: string -> (binding * string option * mixfix) list -> Proof.context ->
    term * Proof.context
  val check_free_spec:
    (binding * typ option * mixfix) list -> (Attrib.binding * term) list -> Proof.context ->
    ((((binding * typ) * mixfix) list * (Attrib.binding * term) list) * (string -> Position.T))
      * Proof.context
  val read_free_spec:
    (binding * string option * mixfix) list -> (Attrib.binding * string) list -> Proof.context ->
    ((((binding * typ) * mixfix) list * (Attrib.binding * term) list) * (string -> Position.T))
      * Proof.context
  val check_spec:
    (binding * typ option * mixfix) list -> (Attrib.binding * term) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term) list) * Proof.context
  val read_spec:
    (binding * string option * mixfix) list -> (Attrib.binding * string) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term) list) * Proof.context
  val check_specification: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val read_specification: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val axiomatization: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list -> theory ->
    (term list * thm list list) * theory
  val axiomatization_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list -> theory ->
    (term list * thm list list) * theory
  val axiom: Attrib.binding * term -> theory -> thm * theory
  val definition:
    (binding * typ option * mixfix) option * (Attrib.binding * term) ->
    local_theory -> (term * (string * thm)) * local_theory
  val definition':
    (binding * typ option * mixfix) option * (Attrib.binding * term) ->
    bool -> local_theory -> (term * (string * thm)) * local_theory
  val definition_cmd:
    (binding * string option * mixfix) option * (Attrib.binding * string) ->
    bool -> local_theory -> (term * (string * thm)) * local_theory
  val abbreviation: Syntax.mode -> (binding * typ option * mixfix) option * term ->
    bool -> local_theory -> local_theory
  val abbreviation_cmd: Syntax.mode -> (binding * string option * mixfix) option * string ->
    bool -> local_theory -> local_theory
  val type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> local_theory -> local_theory
  val type_notation_cmd: bool -> Syntax.mode -> (string * mixfix) list ->
    local_theory -> local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val notation_cmd: bool -> Syntax.mode -> (string * mixfix) list -> local_theory -> local_theory
  val theorems: string ->
    (Attrib.binding * (thm list * Token.src list) list) list ->
    (binding * typ option * mixfix) list ->
    bool -> local_theory -> (string * thm list) list * local_theory
  val theorems_cmd: string ->
    (Attrib.binding * (Facts.ref * Token.src list) list) list ->
    (binding * string option * mixfix) list ->
    bool -> local_theory -> (string * thm list) list * local_theory
  val theorem: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    string list -> Element.context_i list -> Element.statement_i ->
    bool -> local_theory -> Proof.state
  val theorem_cmd: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    (xstring * Position.T) list -> Element.context list -> Element.statement ->
    bool -> local_theory -> Proof.state
  val schematic_theorem: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    string list -> Element.context_i list -> Element.statement_i ->
    bool -> local_theory -> Proof.state
  val schematic_theorem_cmd: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    (xstring * Position.T) list -> Element.context list -> Element.statement ->
    bool -> local_theory -> Proof.state
end;

structure Specification: SPECIFICATION =
struct

(* prepare propositions *)

fun read_props raw_props raw_fixes ctxt =
  let
    val (_, ctxt1) = ctxt |> Proof_Context.add_fixes_cmd raw_fixes;
    val props1 = map (Syntax.parse_prop ctxt1) raw_props;
    val (props2, ctxt2) = ctxt1 |> fold_map Variable.fix_dummy_patterns props1;
    val props3 = Syntax.check_props ctxt2 props2;
    val ctxt3 = ctxt2 |> fold Variable.declare_term props3;
  in (props3, ctxt3) end;

fun read_prop raw_prop raw_fixes ctxt =
  let val ([prop], ctxt') = read_props [raw_prop] raw_fixes ctxt
  in (prop, ctxt') end;


(* prepare specification *)

local

fun close_forms ctxt i As =
  let
    val xs = rev (fold (Variable.add_free_names ctxt) As []);
    val types =
      map (Type_Infer.param i o rpair []) (Name.invent Name.context Name.aT (length xs));
    val uniform_typing = AList.lookup (op =) (xs ~~ types);
    val close = fold_rev (Logic.dependent_all_constraint uniform_typing) (xs ~~ xs);
  in map close As end;

fun get_positions ctxt x =
  let
    fun get Cs (Const ("_type_constraint_", C) $ t) = get (C :: Cs) t
      | get _ (t $ u) = get [] t @ get [] u
      | get _ (Abs (_, _, t)) = get [] t
      | get Cs (Free (y, T)) =
          if x = y then
            map_filter Term_Position.decode_positionT
              (T :: map (Type.constraint_type ctxt) Cs)
          else []
      | get _ _ = [];
  in get [] end;

fun prepare prep_var parse_prop prep_att do_close raw_vars raw_specss ctxt =
  let
    val (vars, vars_ctxt) = ctxt |> fold_map prep_var raw_vars;
    val (xs, params_ctxt) = vars_ctxt
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible vars_ctxt;
    val _ =
      Context_Position.reports params_ctxt
        (map (Binding.pos_of o #1) vars ~~
          map (Variable.markup_entity_def params_ctxt ##> Properties.remove Markup.kindN) xs);

    val Asss =
      (map o map) snd raw_specss
      |> (burrow o burrow) (grouped 10 Par_List.map_independent (parse_prop params_ctxt));
    val names = Variable.names_of (params_ctxt |> (fold o fold o fold) Variable.declare_term Asss)
      |> fold Name.declare xs;
    val Asss' = #1 ((fold_map o fold_map o fold_map) Term.free_dummy_patterns Asss names);
    val idx = (fold o fold o fold) Term.maxidx_term Asss' ~1 + 1;

    val specs =
      (if do_close then
        #1 (fold_map
            (fn Ass => fn i => (burrow (close_forms params_ctxt i) Ass, i + 1)) Asss' idx)
      else Asss')
      |> flat |> burrow (Syntax.check_props params_ctxt);
    val specs_ctxt = params_ctxt |> (fold o fold) Variable.declare_term specs;

    val ps = specs_ctxt |> fold_map Proof_Context.inferred_param xs |> fst;
    val params = map2 (fn (b, _, mx) => fn (_, T) => ((b, T), mx)) vars ps;
    val name_atts: Attrib.binding list =
      map (fn ((name, atts), _) => (name, map (prep_att ctxt) atts)) (flat raw_specss);

    fun get_pos x =
      if do_close then Position.none
      else
        (case (maps o maps o maps) (get_positions specs_ctxt x) Asss' of
          [] => Position.none
        | pos :: _ => pos);
  in (((params, name_atts ~~ specs), get_pos), specs_ctxt) end;


fun single_spec (a, prop) = [(a, [prop])];
fun the_spec (a, [prop]) = (a, prop);

fun prep_spec prep_var parse_prop prep_att do_close vars specs =
  prepare prep_var parse_prop prep_att do_close
    vars (map single_spec specs) #>> (apfst o apsnd) (map the_spec);

in

fun check_free_spec vars specs =
  prep_spec Proof_Context.cert_var (K I) (K I) false vars specs;

fun read_free_spec vars specs =
  prep_spec Proof_Context.read_var Syntax.parse_prop Attrib.check_src false vars specs;

fun check_spec vars specs =
  prep_spec Proof_Context.cert_var (K I) (K I) true vars specs #> apfst fst;

fun read_spec vars specs =
  prep_spec Proof_Context.read_var Syntax.parse_prop Attrib.check_src true vars specs #> apfst fst;

fun check_specification vars specs =
  prepare Proof_Context.cert_var (K I) (K I) true vars [specs] #> apfst fst

fun read_specification vars specs =
  prepare Proof_Context.read_var Syntax.parse_prop Attrib.check_src true vars [specs] #> apfst fst;

end;


(* axiomatization -- within global theory *)

fun gen_axioms prep raw_vars raw_specs thy =
  let
    val ((vars, specs), _) = prep raw_vars raw_specs (Proof_Context.init_global thy);
    val xs = map (fn ((b, T), _) => (Variable.check_name b, T)) vars;

    (*consts*)
    val (consts, consts_thy) = thy |> fold_map Theory.specify_const vars;
    val subst = Term.subst_atomic (map Free xs ~~ consts);

    (*axioms*)
    val (axioms, axioms_thy) = (specs, consts_thy) |-> fold_map (fn ((b, atts), props) =>
        fold_map Thm.add_axiom_global
          (map (apfst (fn a => Binding.map_name (K a) b))
            (Global_Theory.name_multi (Binding.name_of b) (map subst props)))
        #>> (fn ths => ((b, atts), [(map #2 ths, [])])));

    (*facts*)
    val (facts, facts_lthy) = axioms_thy
      |> Named_Target.theory_init
      |> Spec_Rules.add Spec_Rules.Unknown (consts, maps (maps #1 o #2) axioms)
      |> Local_Theory.notes axioms;

  in ((consts, map #2 facts), Local_Theory.exit_global facts_lthy) end;

val axiomatization = gen_axioms check_specification;
val axiomatization_cmd = gen_axioms read_specification;

fun axiom (b, ax) = axiomatization [] [(b, [ax])] #>> (hd o hd o snd);


(* definition *)

fun gen_def prep (raw_var, raw_spec) int lthy =
  let
    val ((vars, [((raw_name, atts), prop)]), get_pos) =
      fst (prep (the_list raw_var) [raw_spec] lthy);
    val (((x, T), rhs), prove) = Local_Defs.derived_def lthy true prop;
    val _ = Name.reject_internal (x, []);
    val (b, mx) =
      (case vars of
        [] => (Binding.make (x, get_pos x), NoSyn)
      | [((b, _), mx)] =>
          let
            val y = Variable.check_name b;
            val _ = x = y orelse
              error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote y ^
                Position.here (Binding.pos_of b));
          in (b, mx) end);
    val name = Binding.reset_pos (Thm.def_binding_optional b raw_name);
    val ((lhs, (_, raw_th)), lthy2) = lthy
      |> Local_Theory.define_internal ((b, mx), ((Binding.suffix_name "_raw" name, []), rhs));

    val th = prove lthy2 raw_th;
    val lthy3 = lthy2 |> Spec_Rules.add Spec_Rules.Equational ([lhs], [th]);

    val ([(def_name, [th'])], lthy4) = lthy3
      |> Local_Theory.notes [((name, Code.add_default_eqn_attrib :: atts), [([th], [])])];

    val lhs' = Morphism.term (Local_Theory.target_morphism lthy4) lhs;

    val _ =
      Proof_Display.print_consts int (Position.thread_data ()) lthy4
        (member (op =) (Term.add_frees lhs' [])) [(x, T)];
  in ((lhs, (def_name, th')), lthy4) end;

val definition' = gen_def check_free_spec;
fun definition spec = definition' spec false;
val definition_cmd = gen_def read_free_spec;


(* abbreviation *)

fun gen_abbrev prep mode (raw_var, raw_prop) int lthy =
  let
    val lthy1 = lthy
      |> Proof_Context.set_syntax_mode mode;
    val (((vars, [(_, prop)]), get_pos), _) =
      prep (the_list raw_var) [(Attrib.empty_binding, raw_prop)]
        (lthy1 |> Proof_Context.set_mode Proof_Context.mode_abbrev);
    val ((x, T), rhs) = Local_Defs.abs_def (#2 (Local_Defs.cert_def lthy1 prop));
    val _ = Name.reject_internal (x, []);
    val (b, mx) =
      (case vars of
        [] => (Binding.make (x, get_pos x), NoSyn)
      | [((b, _), mx)] =>
          let
            val y = Variable.check_name b;
            val _ = x = y orelse
              error ("Head of abbreviation " ^ quote x ^ " differs from declaration " ^ quote y ^
                Position.here (Binding.pos_of b));
          in (b, mx) end);
    val lthy2 = lthy1
      |> Local_Theory.abbrev mode ((b, mx), rhs) |> snd
      |> Proof_Context.restore_syntax_mode lthy;

    val _ = Proof_Display.print_consts int (Position.thread_data ()) lthy2 (K false) [(x, T)];
  in lthy2 end;

val abbreviation = gen_abbrev check_free_spec;
val abbreviation_cmd = gen_abbrev read_free_spec;


(* notation *)

local

fun gen_type_notation prep_type add mode args lthy =
  lthy |> Local_Theory.type_notation add mode (map (apfst (prep_type lthy)) args);

fun gen_notation prep_const add mode args lthy =
  lthy |> Local_Theory.notation add mode (map (apfst (prep_const lthy)) args);

in

val type_notation = gen_type_notation (K I);
val type_notation_cmd =
  gen_type_notation (Proof_Context.read_type_name {proper = true, strict = false});

val notation = gen_notation (K I);
val notation_cmd = gen_notation (Proof_Context.read_const {proper = false, strict = false});

end;


(* fact statements *)

local

fun gen_theorems prep_fact prep_att add_fixes
    kind raw_facts raw_fixes int lthy =
  let
    val facts = raw_facts |> map (fn ((name, atts), bs) =>
      ((name, map (prep_att lthy) atts),
        bs |> map (fn (b, more_atts) => (prep_fact lthy b, map (prep_att lthy) more_atts))));
    val (_, ctxt') = add_fixes raw_fixes lthy;

    val facts' = facts
      |> Attrib.partial_evaluation ctxt'
      |> Attrib.transform_facts (Proof_Context.export_morphism ctxt' lthy);
    val (res, lthy') = lthy |> Local_Theory.notes_kind kind facts';
    val _ = Proof_Display.print_results int (Position.thread_data ()) lthy' ((kind, ""), res);
  in (res, lthy') end;

in

val theorems = gen_theorems (K I) (K I) Proof_Context.add_fixes;
val theorems_cmd = gen_theorems Proof_Context.get_fact Attrib.check_src Proof_Context.add_fixes_cmd;

end;


(* complex goal statements *)

local

fun prep_statement prep_att prep_stmt raw_elems raw_stmt ctxt =
  let
    val (stmt, elems_ctxt) = prep_stmt raw_elems raw_stmt ctxt;
    val prems = Assumption.local_prems_of elems_ctxt ctxt;
    val stmt_ctxt = fold (fold (Variable.auto_fixes o fst) o snd) stmt elems_ctxt;
  in
    (case raw_stmt of
      Element.Shows _ =>
        let val stmt' = Attrib.map_specs (map prep_att) stmt
        in (([], prems, stmt', NONE), stmt_ctxt) end
    | Element.Obtains raw_obtains =>
        let
          val asms_ctxt = stmt_ctxt
            |> fold (fn ((name, _), asm) =>
                snd o Proof_Context.add_assms Assumption.assume_export
                  [((name, [Context_Rules.intro_query NONE]), asm)]) stmt;
          val that = Assumption.local_prems_of asms_ctxt stmt_ctxt;
          val ([(_, that')], that_ctxt) = asms_ctxt
            |> Proof_Context.note_thmss "" [((Binding.name Auto_Bind.thatN, []), [(that, [])])];

          val more_atts = map (Attrib.internal o K) (Obtain.obtains_attributes raw_obtains);
          val stmt' = [((Binding.empty, []), [(#2 (#1 (Obtain.obtain_thesis ctxt)), [])])];
        in ((more_atts, prems, stmt', SOME that'), that_ctxt) end)
  end;

fun gen_theorem schematic bundle_includes prep_att prep_stmt
    kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl int lthy =
  let
    val _ = Local_Theory.assert lthy;

    val elems = raw_elems |> map (Element.map_ctxt_attrib (prep_att lthy));
    val ((more_atts, prems, stmt, facts), goal_ctxt) = lthy
      |> bundle_includes raw_includes
      |> prep_statement (prep_att lthy) prep_stmt elems raw_concl;
    val atts = more_atts @ map (prep_att lthy) raw_atts;

    val pos = Position.thread_data ();
    fun after_qed' results goal_ctxt' =
      let
        val results' =
          burrow (map (Goal.norm_result lthy) o Proof_Context.export goal_ctxt' lthy) results;
        val (res, lthy') =
          if forall (Attrib.is_empty_binding o fst) stmt then (map (pair "") results', lthy)
          else
            Local_Theory.notes_kind kind
              (map2 (fn (b, _) => fn ths => (b, [(ths, [])])) stmt results') lthy;
        val lthy'' =
          if Attrib.is_empty_binding (name, atts) then
            (Proof_Display.print_results int pos lthy' ((kind, ""), res); lthy')
          else
            let
              val ([(res_name, _)], lthy'') =
                Local_Theory.notes_kind kind [((name, atts), [(maps #2 res, [])])] lthy';
              val _ = Proof_Display.print_results int pos lthy' ((kind, res_name), res);
            in lthy'' end;
      in after_qed results' lthy'' end;
  in
    goal_ctxt
    |> Proof_Context.note_thmss "" [((Binding.name Auto_Bind.assmsN, []), [(prems, [])])]
    |> snd
    |> Proof.theorem before_qed after_qed' (map snd stmt)
    |> (case facts of NONE => I | SOME ths => Proof.refine_insert ths)
    |> tap (fn state => not schematic andalso Proof.schematic_goal state andalso
        error "Illegal schematic goal statement")
  end;

in

val theorem =
  gen_theorem false Bundle.includes (K I) Expression.cert_statement;
val theorem_cmd =
  gen_theorem false Bundle.includes_cmd Attrib.check_src Expression.read_statement;

val schematic_theorem =
  gen_theorem true Bundle.includes (K I) Expression.cert_statement;
val schematic_theorem_cmd =
  gen_theorem true Bundle.includes_cmd Attrib.check_src Expression.read_statement;

end;

end;
