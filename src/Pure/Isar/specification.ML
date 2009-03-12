(*  Title:      Pure/Isar/specification.ML
    Author:     Makarius

Derived local theory specifications --- with type-inference and
toplevel polymorphism.
*)

signature SPECIFICATION =
sig
  val print_consts: local_theory -> (string * typ -> bool) -> (string * typ) list -> unit
  val check_specification: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val read_specification: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val check_free_specification: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val read_free_specification: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val axiomatization: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list -> theory ->
    (term list * (string * thm list) list) * theory
  val axiomatization_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list -> theory ->
    (term list * (string * thm list) list) * theory
  val definition:
    (binding * typ option * mixfix) option * (Attrib.binding * term) ->
    local_theory -> (term * (string * thm)) * local_theory
  val definition_cmd:
    (binding * string option * mixfix) option * (Attrib.binding * string) ->
    local_theory -> (term * (string * thm)) * local_theory
  val abbreviation: Syntax.mode -> (binding * typ option * mixfix) option * term ->
    local_theory -> local_theory
  val abbreviation_cmd: Syntax.mode -> (binding * string option * mixfix) option * string ->
    local_theory -> local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val notation_cmd: bool -> Syntax.mode -> (string * mixfix) list -> local_theory -> local_theory
  val theorems: string ->
    (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val theorems_cmd: string ->
    (Attrib.binding * (Facts.ref * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val theorem: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    Element.context_i list -> Element.statement_i ->
    bool -> local_theory -> Proof.state
  val theorem_cmd: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    Element.context list -> Element.statement ->
    bool -> local_theory -> Proof.state
  val add_theorem_hook: (bool -> Proof.state -> Proof.state) -> Context.generic -> Context.generic
end;

structure Specification: SPECIFICATION =
struct

(* diagnostics *)

fun print_consts _ _ [] = ()
  | print_consts ctxt pred cs = Pretty.writeln (ProofDisplay.pretty_consts ctxt pred cs);


(* prepare specification *)

local

fun close_forms ctxt i xs As =
  let
    fun add_free (Free (x, _)) = if Variable.is_fixed ctxt x then I else insert (op =) x
      | add_free _ = I;

    val commons = map #1 xs;
    val _ =
      (case duplicates (op =) commons of [] => ()
      | dups => error ("Duplicate local variables " ^ commas_quote dups));
    val frees = rev ((fold o fold_aterms) add_free As (rev commons));
    val types = map (TypeInfer.param i o rpair []) (Name.invents Name.context Name.aT (length frees));
    val uniform_typing = the o AList.lookup (op =) (frees ~~ types);

    fun abs_body lev y (Abs (x, T, b)) = Abs (x, T, abs_body (lev + 1) y b)
      | abs_body lev y (t $ u) = abs_body lev y t $ abs_body lev y u
      | abs_body lev y (t as Free (x, T)) =
          if x = y then TypeInfer.constrain (uniform_typing x) (TypeInfer.constrain T (Bound lev))
          else t
      | abs_body _ _ a = a;
    fun close (y, U) B =
      let val B' = abs_body 0 y (Term.incr_boundvars 1 B)
      in if Term.loose_bvar1 (B', 0) then Term.all dummyT $ Abs (y, U, B') else B end;
    fun close_form A =
      let
        val occ_frees = rev (fold_aterms add_free A []);
        val bounds = xs @ map (rpair dummyT) (subtract (op =) commons occ_frees);
      in fold_rev close bounds A end;
  in map close_form As end;

fun prep_spec prep_vars parse_prop prep_att do_close raw_vars raw_specss ctxt =
  let
    val thy = ProofContext.theory_of ctxt;

    val (vars, vars_ctxt) = ctxt |> prep_vars raw_vars;
    val (xs, params_ctxt) = vars_ctxt |> ProofContext.add_fixes_i vars;

    val Asss = (map o map) (map (parse_prop params_ctxt) o snd) raw_specss;
    val names = Variable.names_of (params_ctxt |> (fold o fold o fold) Variable.declare_term Asss)
      |> fold Name.declare xs;
    val Asss' = #1 ((fold_map o fold_map o fold_map) Term.free_dummy_patterns Asss names);
    val idx = (fold o fold o fold) Term.maxidx_term Asss' ~1 + 1;
    val specs =
      (if do_close then
        #1 (fold_map
            (fn Ass => fn i => (burrow (close_forms params_ctxt i []) Ass, i + 1)) Asss' idx)
      else Asss')
      |> flat |> burrow (Syntax.check_props params_ctxt);
    val specs_ctxt = params_ctxt |> (fold o fold) Variable.declare_term specs;

    val Ts = specs_ctxt |> fold_map ProofContext.inferred_param xs |> fst;
    val params = map2 (fn (b, _, mx) => fn T => ((b, T), mx)) vars Ts;
    val name_atts = map (fn ((name, atts), _) => (name, map (prep_att thy) atts)) (flat raw_specss);
  in ((params, name_atts ~~ specs), specs_ctxt) end;

fun read_spec x = prep_spec ProofContext.read_vars Syntax.parse_prop Attrib.intern_src x;
fun check_spec x = prep_spec ProofContext.cert_vars (K I) (K I) x;

in

fun read_specification x = read_spec true x;
fun check_specification x = check_spec true x;
fun read_free_specification vars specs = read_spec false vars [specs];
fun check_free_specification vars specs = check_spec false vars [specs];

end;


(* axiomatization -- within global theory *)

fun gen_axioms do_print prep raw_vars raw_specs thy =
  let
    val ((vars, specs), _) = prep raw_vars [raw_specs] (ProofContext.init thy);
    val xs = map (fn ((b, T), _) => (Binding.name_of b, T)) vars;

    (*consts*)
    val (consts, consts_thy) = thy |> fold_map (Theory.specify_const []) vars;
    val subst = Term.subst_atomic (map Free xs ~~ consts);

    (*axioms*)
    val (axioms, axioms_thy) = (specs, consts_thy) |-> fold_map (fn ((b, atts), props) =>
        fold_map Thm.add_axiom
          (map (apfst (fn a => Binding.map_name (K a) b))
            (PureThy.name_multi (Binding.name_of b) (map subst props)))
        #>> (fn ths => ((b, atts), [(map Drule.standard' ths, [])])));

    (*facts*)
    val (facts, thy') = axioms_thy |> PureThy.note_thmss Thm.axiomK
      (Attrib.map_facts (Attrib.attribute_i axioms_thy) axioms);

    val _ =
      if not do_print then ()
      else print_consts (ProofContext.init thy') (K false) xs;
  in ((consts, facts), thy') end;

val axiomatization = gen_axioms false check_specification;
val axiomatization_cmd = gen_axioms true read_specification;


(* definition *)

fun gen_def do_print prep (raw_var, (raw_a, raw_prop)) lthy =
  let
    val (vars, [((raw_name, atts), [prop])]) =
      fst (prep (the_list raw_var) [(raw_a, [raw_prop])] lthy);
    val (((x, T), rhs), prove) = LocalDefs.derived_def lthy true prop;
    val var as (b, _) =
      (case vars of
        [] => (Binding.name x, NoSyn)
      | [((b, _), mx)] =>
          let
            val y = Binding.name_of b;
            val _ = x = y orelse
              error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote y ^
                Position.str_of (Binding.pos_of b));
          in (b, mx) end);
    val name = Thm.def_binding_optional b raw_name;
    val ((lhs, (_, th)), lthy2) = lthy
      |> LocalTheory.define Thm.definitionK
        (var, ((Binding.suffix_name "_raw" name, []), rhs));
    val ((def_name, [th']), lthy3) = lthy2
      |> LocalTheory.note Thm.definitionK
        ((name, Code.add_default_eqn_attrib :: atts), [prove lthy2 th]);

    val lhs' = Morphism.term (LocalTheory.target_morphism lthy3) lhs;
    val _ =
      if not do_print then ()
      else print_consts lthy3 (member (op =) (Term.add_frees lhs' [])) [(x, T)];
  in ((lhs, (def_name, th')), lthy3) end;

val definition = gen_def false check_free_specification;
val definition_cmd = gen_def true read_free_specification;


(* abbreviation *)

fun gen_abbrev do_print prep mode (raw_var, raw_prop) lthy =
  let
    val ((vars, [(_, [prop])]), _) =
      prep (the_list raw_var) [(("", []), [raw_prop])]
        (lthy |> ProofContext.set_mode ProofContext.mode_abbrev);
    val ((x, T), rhs) = LocalDefs.abs_def (#2 (LocalDefs.cert_def lthy prop));
    val var =
      (case vars of
        [] => (Binding.name x, NoSyn)
      | [((b, _), mx)] =>
          let
            val y = Binding.name_of b;
            val _ = x = y orelse
              error ("Head of abbreviation " ^ quote x ^ " differs from declaration " ^ quote y ^
                Position.str_of (Binding.pos_of b));
          in (b, mx) end);
    val lthy' = lthy
      |> ProofContext.set_syntax_mode mode    (* FIXME ?!? *)
      |> LocalTheory.abbrev mode (var, rhs) |> snd
      |> ProofContext.restore_syntax_mode lthy;

    val _ = if not do_print then () else print_consts lthy' (K false) [(x, T)];
  in lthy' end;

val abbreviation = gen_abbrev false check_free_specification;
val abbreviation_cmd = gen_abbrev true read_free_specification;


(* notation *)

fun gen_notation prep_const add mode args lthy =
  lthy |> LocalTheory.notation add mode (map (apfst (prep_const lthy)) args);

val notation = gen_notation (K I);
val notation_cmd = gen_notation ProofContext.read_const;


(* fact statements *)

fun gen_theorems prep_fact prep_att kind raw_facts lthy =
  let
    val attrib = prep_att (ProofContext.theory_of lthy);
    val facts = raw_facts |> map (fn ((name, atts), bs) =>
      ((name, map attrib atts),
        bs |> map (fn (b, more_atts) => (prep_fact lthy b, map attrib more_atts))));
    val (res, lthy') = lthy |> LocalTheory.notes kind facts;
    val _ = ProofDisplay.print_results true lthy' ((kind, ""), res);
  in (res, lthy') end;

val theorems = gen_theorems (K I) (K I);
val theorems_cmd = gen_theorems ProofContext.get_fact Attrib.intern_src;


(* complex goal statements *)

local

fun subtract_prems ctxt1 ctxt2 =
  Library.drop (length (Assumption.prems_of ctxt1), Assumption.prems_of ctxt2);

fun prep_statement prep_att prep_stmt elems concl ctxt =
  (case concl of
    Element.Shows shows =>
      let
        val (propp, elems_ctxt) = prep_stmt elems (map snd shows) ctxt;
        val prems = subtract_prems ctxt elems_ctxt;
        val stmt = Attrib.map_specs prep_att (map fst shows ~~ propp);
        val goal_ctxt = fold (fold (Variable.auto_fixes o fst)) propp elems_ctxt;
      in ((prems, stmt, []), goal_ctxt) end
  | Element.Obtains obtains =>
      let
        val case_names = obtains |> map_index (fn (i, (b, _)) =>
          if Binding.is_empty b then string_of_int (i + 1) else Binding.name_of b);
        val constraints = obtains |> map (fn (_, (vars, _)) =>
          Element.Constrains
            (vars |> map_filter (fn (x, SOME T) => SOME (Binding.name_of x, T) | _ => NONE)));

        val raw_propp = obtains |> map (fn (_, (_, props)) => map (rpair []) props);
        val (propp, elems_ctxt) = prep_stmt (elems @ constraints) raw_propp ctxt;

        val thesis = ObjectLogic.fixed_judgment (ProofContext.theory_of ctxt) AutoBind.thesisN;

        fun assume_case ((name, (vars, _)), asms) ctxt' =
          let
            val bs = map fst vars;
            val xs = map Binding.name_of bs;
            val props = map fst asms;
            val (Ts, _) = ctxt'
              |> fold Variable.declare_term props
              |> fold_map ProofContext.inferred_param xs;
            val asm = Term.list_all_free (xs ~~ Ts, Logic.list_implies (props, thesis));
          in
            ctxt' |> (snd o ProofContext.add_fixes_i (map (fn b => (b, NONE, NoSyn)) bs));
            ctxt' |> Variable.auto_fixes asm
            |> ProofContext.add_assms_i Assumption.assume_export
              [((name, [ContextRules.intro_query NONE]), [(asm, [])])]
            |>> (fn [(_, [th])] => th)
          end;

        val atts = map (Attrib.internal o K)
          [RuleCases.consumes (~ (length obtains)), RuleCases.case_names case_names];
        val prems = subtract_prems ctxt elems_ctxt;
        val stmt = [((Binding.empty, atts), [(thesis, [])])];

        val (facts, goal_ctxt) = elems_ctxt
          |> (snd o ProofContext.add_fixes_i [(Binding.name AutoBind.thesisN, NONE, NoSyn)])
          |> fold_map assume_case (obtains ~~ propp)
          |-> (fn ths => ProofContext.note_thmss_i Thm.assumptionK
                [((Binding.name Obtain.thatN, []), [(ths, [])])] #> #2 #> pair ths);
      in ((prems, stmt, facts), goal_ctxt) end);

structure TheoremHook = GenericDataFun
(
  type T = ((bool -> Proof.state -> Proof.state) * stamp) list;
  val empty = [];
  val extend = I;
  fun merge _ hooks : T = Library.merge (eq_snd op =) hooks;
);

fun gen_theorem prep_att prep_stmt
    kind before_qed after_qed (name, raw_atts) raw_elems raw_concl int lthy =
  let
    val _ = LocalTheory.affirm lthy;
    val thy = ProofContext.theory_of lthy;

    val attrib = prep_att thy;
    val atts = map attrib raw_atts;
    val elems = raw_elems |> map (Element.map_ctxt_attrib attrib);
    val ((prems, stmt, facts), goal_ctxt) =
      prep_statement attrib prep_stmt elems raw_concl lthy;

    fun after_qed' results goal_ctxt' =
      let val results' =
        burrow (map Goal.norm_result o ProofContext.export goal_ctxt' lthy) results
      in
        lthy
        |> LocalTheory.notes kind (map2 (fn (a, _) => fn ths => (a, [(ths, [])])) stmt results')
        |> (fn (res, lthy') =>
          if Binding.is_empty name andalso null atts then
            (ProofDisplay.print_results true lthy' ((kind, ""), res); lthy')
          else
            let
              val ([(res_name, _)], lthy'') = lthy'
                |> LocalTheory.notes kind [((name, atts), [(maps #2 res, [])])];
              val _ = ProofDisplay.print_results true lthy' ((kind, res_name), res);
            in lthy'' end)
        |> after_qed results'
      end;
  in
    goal_ctxt
    |> ProofContext.note_thmss_i Thm.assumptionK
      [((Binding.name AutoBind.assmsN, []), [(prems, [])])]
    |> snd
    |> Proof.theorem_i before_qed after_qed' (map snd stmt)
    |> Proof.refine_insert facts
    |> Library.apply (map (fn (f, _) => f int) (rev (TheoremHook.get (Context.Proof goal_ctxt))))
  end;

in

val theorem = gen_theorem (K I) Expression.cert_statement;
val theorem_cmd = gen_theorem Attrib.intern_src Expression.read_statement;

fun add_theorem_hook f = TheoremHook.map (cons (f, stamp ()));

end;

end;
