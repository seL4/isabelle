(*  Title:      Pure/Isar/specification.ML
    ID:         $Id$
    Author:     Makarius

Derived local theory specifications --- with type-inference and
toplevel polymorphism.
*)

signature SPECIFICATION =
sig
  val quiet_mode: bool ref
  val print_consts: local_theory -> (string * typ -> bool) -> (string * typ) list -> unit
  val read_specification: (string * string option * mixfix) list ->
    ((string * Attrib.src list) * string list) list -> local_theory ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    local_theory
  val cert_specification: (string * typ option * mixfix) list ->
    ((string * Attrib.src list) * term list) list -> local_theory ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    local_theory
  val axiomatization: (string * string option * mixfix) list ->
    ((bstring * Attrib.src list) * string list) list -> local_theory ->
    (term list * (bstring * thm list) list) * local_theory
  val axiomatization_i: (string * typ option * mixfix) list ->
    ((bstring * Attrib.src list) * term list) list -> local_theory ->
    (term list * (bstring * thm list) list) * local_theory
  val definition:
    ((string * string option * mixfix) option * ((string * Attrib.src list) * string)) list ->
    local_theory -> (term * (bstring * thm)) list * local_theory
  val definition_i:
    ((string * typ option * mixfix) option * ((string * Attrib.src list) * term)) list ->
    local_theory -> (term * (bstring * thm)) list * local_theory
  val abbreviation: Syntax.mode -> ((string * string option * mixfix) option * string) list ->
    local_theory -> (term * term) list * local_theory
  val abbreviation_i: Syntax.mode -> ((string * typ option * mixfix) option * term) list ->
    local_theory -> (term * term) list * local_theory
  val notation: Syntax.mode -> (string * mixfix) list -> local_theory -> local_theory
  val notation_i: Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val theorems: string -> ((bstring * Attrib.src list) * (thmref * Attrib.src list) list) list
    -> local_theory -> (bstring * thm list) list * local_theory
  val theorems_i: string -> ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list
    -> local_theory -> (bstring * thm list) list * local_theory
  val theorem: string -> Method.text option -> (thm list list -> local_theory -> local_theory) ->
    string * Attrib.src list -> Element.context Locale.element list -> Element.statement ->
    local_theory -> Proof.state
  val theorem_i: string -> Method.text option -> (thm list list -> local_theory -> local_theory) ->
    string * Attrib.src list -> Element.context_i Locale.element list -> Element.statement_i ->
    local_theory -> Proof.state
end;

structure Specification: SPECIFICATION =
struct


(* diagnostics *)

val quiet_mode = ref false;

fun print_consts _ _ [] = ()
  | print_consts ctxt pred cs =
      if ! quiet_mode then () else Pretty.writeln (ProofDisplay.pretty_consts ctxt pred cs);

fun present_results ctxt res =
  if ! quiet_mode then () else ProofDisplay.present_results ctxt res;

fun present_results' ctxt kind res = present_results ctxt ((kind, ""), res);


(* prepare specification *)

fun prep_specification prep_vars prep_propp prep_att raw_vars raw_specs ctxt =
  let
    val thy = ProofContext.theory_of ctxt;

    val (vars, vars_ctxt) = ctxt |> prep_vars raw_vars;
    val (xs, params_ctxt) = vars_ctxt |> ProofContext.add_fixes_i vars;
    val ((specs, vs), specs_ctxt) =
      prep_propp (params_ctxt, map (map (rpair []) o snd) raw_specs)
      |> swap |>> map (map fst)
      ||>> fold_map ProofContext.inferred_param xs;

    val params = vs ~~ map #3 vars;
    val names = map (fst o fst) raw_specs;
    val atts = map (map (prep_att thy) o snd o fst) raw_specs;
  in ((params, (names ~~ atts) ~~ specs), specs_ctxt) end;

fun read_specification x =
  prep_specification ProofContext.read_vars ProofContext.read_propp Attrib.intern_src x;

fun cert_specification x =
  prep_specification ProofContext.cert_vars ProofContext.cert_propp (K I) x;


(* axiomatization *)

fun gen_axioms prep raw_vars raw_specs lthy =
  let
    val (vars, specs) = fst (prep raw_vars raw_specs lthy);
    val cs = map fst vars;
    val spec_frees = member (op =) (fold (fold Term.add_frees o snd) specs []);

    val ((consts, axioms), lthy') = lthy
      |> LocalTheory.consts spec_frees vars
      ||> fold (fold Variable.auto_fixes o snd) specs   (* FIXME !? *)
      ||>> LocalTheory.axioms specs;

    (* FIXME generic target!? *)
    val hs = map (Term.head_of o #2 o Logic.dest_equals o Thm.prop_of o #2) consts;
    val lthy'' = lthy' |> LocalTheory.theory (Theory.add_finals_i false hs);

    val _ = print_consts lthy' spec_frees cs;
  in ((map #1 consts, axioms), lthy'') end;

val axiomatization = gen_axioms read_specification;
val axiomatization_i = gen_axioms cert_specification;


(* definition *)

fun gen_defs prep args lthy =
  let
    fun define (raw_var, (raw_a, raw_prop)) lthy1 =
      let
        val (vars, [((raw_name, atts), [prop])]) =
          fst (prep (the_list raw_var) [(raw_a, [raw_prop])] lthy1);
        val (((x, T), rhs), prove) = LocalDefs.derived_def lthy1 true prop;
        val name = Thm.def_name_optional x raw_name;
        val mx = (case vars of [] => NoSyn | [((x', _), mx)] =>
          if x = x' then mx
          else error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote x'));
        val ((lhs, (_, th)), lthy2) = lthy1
(*          |> LocalTheory.def ((x, mx), ((name ^ "_raw", []), rhs));  FIXME *)
          |> LocalTheory.def ((x, mx), ((name, []), rhs));
        val ((b, [th']), lthy3) = lthy2
          |> LocalTheory.note ((name, atts), [prove lthy2 th]);
      in (((x, T), (lhs, (b, th'))), LocalTheory.restore lthy3) end;

    val ((cs, defs), lthy') = lthy |> fold_map define args |>> split_list;
    val def_frees = member (op =) (fold (Term.add_frees o fst) defs []);
    val _ = print_consts lthy' def_frees cs;
  in (defs, lthy') end;

val definition = gen_defs read_specification;
val definition_i = gen_defs cert_specification;


(* abbreviation *)

fun gen_abbrevs prep mode args lthy =
  let
    fun abbrev (raw_var, raw_prop) lthy1 =
      let
        val ((vars, [(_, [prop])]), _) =
          prep (the_list raw_var) [(("", []), [raw_prop])]
            (lthy1 |> ProofContext.expand_abbrevs false);
        val ((x, T), rhs) = LocalDefs.abs_def (#2 (LocalDefs.cert_def lthy1 prop));
        val mx = (case vars of [] => NoSyn | [((y, _), mx)] =>
          if x = y then mx
          else error ("Head of abbreviation " ^ quote x ^ " differs from declaration " ^ quote y));
        val ([abbr], lthy2) = lthy1
          |> LocalTheory.abbrevs mode [((x, mx), rhs)];
      in (((x, T), abbr), LocalTheory.restore lthy2) end;

    val (abbrs, lthy1) = lthy
      |> ProofContext.set_syntax_mode mode
      |> fold_map abbrev args
      ||> ProofContext.restore_syntax_mode lthy;
    val _ = print_consts lthy1 (K false) (map fst abbrs);
  in (map snd abbrs, lthy1) end;

val abbreviation = gen_abbrevs read_specification;
val abbreviation_i = gen_abbrevs cert_specification;


(* notation *)

fun gen_notation prep_const mode args lthy =
  lthy |> LocalTheory.notation mode (map (apfst (prep_const lthy)) args);

val notation = gen_notation ProofContext.read_const;
val notation_i = gen_notation (K I);


(* fact statements *)

fun gen_theorems prep_thms prep_att kind raw_facts lthy =
  let
    val k = if kind = "" then [] else [Attrib.kind kind];
    val attrib = prep_att (ProofContext.theory_of lthy);
    val facts = raw_facts |> map (fn ((name, atts), bs) =>
      ((name, map attrib atts),
        bs |> map (fn (b, more_atts) => (prep_thms lthy b, map attrib more_atts @ k))));
    val (res, lthy') = lthy |> LocalTheory.notes facts;
    val _ = present_results' lthy' kind res;
  in (res, lthy') end;

val theorems = gen_theorems ProofContext.get_thms Attrib.intern_src;
val theorems_i = gen_theorems (K I) (K I);


(* complex goal statements *)

local

fun prep_statement prep_att prep_stmt elems concl ctxt =
  (case concl of
    Element.Shows shows =>
      let
        val (_, _, elems_ctxt, propp) = prep_stmt elems (map snd shows) ctxt;
        val goal_ctxt = fold (fold (Variable.auto_fixes o fst)) propp elems_ctxt;
        val stmt = Attrib.map_specs prep_att (map fst shows ~~ propp);
      in ((stmt, []), goal_ctxt) end
  | Element.Obtains obtains =>
      let
        val case_names = obtains |> map_index
          (fn (i, ("", _)) => string_of_int (i + 1) | (_, (name, _)) => name);
        val constraints = obtains |> map (fn (_, (vars, _)) =>
          Locale.Elem (Element.Constrains
            (vars |> map_filter (fn (x, SOME T) => SOME (x, T) | _ => NONE))));

        val raw_propp = obtains |> map (fn (_, (_, props)) => map (rpair []) props);
        val (_, _, elems_ctxt, propp) = prep_stmt (elems @ constraints) raw_propp ctxt;

        val thesis = ObjectLogic.fixed_judgment (ProofContext.theory_of ctxt) AutoBind.thesisN;

        fun assume_case ((name, (vars, _)), asms) ctxt' =
          let
            val xs = map fst vars;
            val props = map fst asms;
            val (parms, _) = ctxt'
              |> fold Variable.declare_term props
              |> fold_map ProofContext.inferred_param xs;
            val asm = Term.list_all_free (parms, Logic.list_implies (props, thesis));
          in
            ctxt' |> (snd o ProofContext.add_fixes_i (map (fn x => (x, NONE, NoSyn)) xs));
            ctxt' |> Variable.auto_fixes asm
            |> ProofContext.add_assms_i Assumption.assume_export
              [((name, [ContextRules.intro_query NONE]), [(asm, [])])]
            |>> (fn [(_, [th])] => th)
          end;

        val atts = map Attrib.internal
          [RuleCases.consumes (~ (length obtains)), RuleCases.case_names case_names];
        val stmt = [(("", atts), [(thesis, [])])];

        val (facts, goal_ctxt) = elems_ctxt
          |> (snd o ProofContext.add_fixes_i [(AutoBind.thesisN, NONE, NoSyn)])
          |> fold_map assume_case (obtains ~~ propp)
          |-> (fn ths =>
            ProofContext.note_thmss_i [((Obtain.thatN, []), [(ths, [])])] #> #2 #> pair ths);
      in ((stmt, facts), goal_ctxt) end);

fun gen_theorem prep_att prep_stmt
    kind before_qed after_qed (name, raw_atts) raw_elems raw_concl lthy0 =
  let
    val _ = LocalTheory.assert lthy0;
    val thy = ProofContext.theory_of lthy0;
    val attrib = prep_att thy;

    val (loc, ctxt, lthy) =
      (case (TheoryTarget.peek lthy0, exists (fn Locale.Expr _ => true | _ => false) raw_elems) of
        (SOME loc, true) => (* workaround non-modularity of in/includes *)  (* FIXME *)
          (SOME loc, ProofContext.init thy, LocalTheory.restore lthy0)
      | _ => (NONE, lthy0, lthy0));

    val elems = raw_elems |> (map o Locale.map_elem)
      (Element.map_ctxt {name = I, var = I, typ = I, term = I, fact = I, attrib = attrib});
    val ((stmt, facts), goal_ctxt) = prep_statement attrib (prep_stmt loc) elems raw_concl ctxt;

    val k = if kind = "" then [] else [Attrib.kind kind];
    val names = map (fst o fst) stmt;
    val attss = map (fn ((_, atts), _) => atts @ k) stmt;
    val atts = map attrib raw_atts @ k;

    fun after_qed' results goal_ctxt' =
      let val results' = burrow (ProofContext.export_standard goal_ctxt' lthy) results in
        lthy
        |> LocalTheory.notes ((names ~~ attss) ~~ map (fn ths => [(ths, [])]) results')
        |> (fn (res, lthy') =>
          (present_results lthy' ((kind, name), res);
            if name = "" andalso null raw_atts then lthy'
            else #2 (LocalTheory.notes [((name, atts), [(maps #2 res, [])])] lthy')))
        |> after_qed results'
      end;
  in
    goal_ctxt
    |> Proof.theorem_i kind before_qed after_qed' (map snd stmt)
    |> Proof.refine_insert facts
  end;

in

val theorem = gen_theorem Attrib.intern_src Locale.read_context_statement_i;
val theorem_i = gen_theorem (K I) Locale.cert_context_statement;

end;

end;
