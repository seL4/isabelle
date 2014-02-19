(*  Title:   Tools/permanent_interpretation.ML
    Author:  Florian Haftmann, TU Muenchen

Permanent interpretation accompanied with mixin definitions.
*)

signature PERMANENT_INTERPRETATION =
sig
  val permanent_interpretation: Expression.expression_i ->
    (Attrib.binding * ((binding * mixfix) * term)) list -> (Attrib.binding * term) list ->
    local_theory -> Proof.state
  val permanent_interpretation_cmd: Expression.expression ->
    (Attrib.binding * ((binding * mixfix) * string)) list -> (Attrib.binding * string) list ->
    local_theory -> Proof.state
end;

structure Permanent_Interpretation : PERMANENT_INTERPRETATION =
struct

local

(* reading *)

fun prep_interpretation prep_expr prep_term prep_prop prep_attr expression raw_defs raw_eqns initial_ctxt =
  let
    (*reading*)
    val ((_, deps, _), proto_deps_ctxt) = prep_expr expression initial_ctxt;
    val deps_ctxt = fold Locale.activate_declarations deps proto_deps_ctxt;
    val prep = Syntax.check_terms deps_ctxt #> Variable.export_terms deps_ctxt deps_ctxt;
    val rhss = (prep o map (prep_term deps_ctxt o snd o snd)) raw_defs;
    val eqns = (prep o map (prep_prop deps_ctxt o snd)) raw_eqns;

    (*defining*)
    val pre_defs = map2 (fn ((name, atts), ((b, mx), _)) => fn rhs =>
      ((b, mx), ((Thm.def_binding_optional b name, atts), rhs))) raw_defs rhss;
    val (defs, defs_ctxt) = fold_map Local_Theory.define pre_defs initial_ctxt;
    val def_eqns = map (Thm.symmetric o Morphism.thm (Local_Theory.standard_morphism defs_ctxt initial_ctxt) o snd o snd) defs;
    val base_ctxt = if null def_eqns then defs_ctxt else Local_Theory.restore defs_ctxt;
      (*the "if" prevents restoring a proof context which is no local theory*)

    (*setting up*)
    val ((propss, deps, export), expr_ctxt) = prep_expr expression base_ctxt;
      (*FIXME: only re-prepare if defs are given*)
    val attrss = map (apsnd (map (prep_attr (Proof_Context.theory_of expr_ctxt))) o fst) raw_eqns;
    val goal_ctxt = fold Variable.auto_fixes eqns expr_ctxt;
    val export' = Variable.export_morphism goal_ctxt expr_ctxt;
  in (((propss, deps, export, export'), (def_eqns, eqns, attrss)), goal_ctxt) end;

val cert_interpretation = prep_interpretation Expression.cert_goal_expression (K I) (K I) (K I);
val read_interpretation = prep_interpretation Expression.read_goal_expression Syntax.parse_term Syntax.parse_prop Attrib.intern_src;


(* generic interpretation machinery *)

fun meta_rewrite eqns ctxt = (map (Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def) (maps snd eqns), ctxt);

fun note_eqns_register note activate deps witss def_eqns eqns attrss export export' ctxt =
  let
    val facts = (Attrib.empty_binding, [(map (Morphism.thm (export' $> export)) def_eqns, [])])
      :: map2 (fn attrs => fn eqn => (attrs, [([Morphism.thm (export' $> export) eqn], [])])) attrss eqns;
    val (eqns', ctxt') = ctxt
      |> note Thm.lemmaK facts
      |-> meta_rewrite;
    val dep_morphs = map2 (fn (dep, morph) => fn wits =>
      (dep, morph $> Element.satisfy_morphism (map (Element.transform_witness export') wits))) deps witss;
    fun activate' dep_morph ctxt = activate dep_morph
      (Option.map (rpair true) (Element.eq_morphism (Proof_Context.theory_of ctxt) eqns')) export ctxt;
  in
    ctxt'
    |> fold activate' dep_morphs
  end;

fun generic_interpretation prep_interpretation setup_proof note add_registration
    expression raw_defs raw_eqns initial_ctxt = 
  let
    val (((propss, deps, export, export'), (def_eqns, eqns, attrss)), goal_ctxt) = 
      prep_interpretation expression raw_defs raw_eqns initial_ctxt;
    fun after_qed witss eqns =
      note_eqns_register note add_registration deps witss def_eqns eqns attrss export export';
  in setup_proof after_qed propss eqns goal_ctxt end;


(* interpretation with permanent registration *)

fun subscribe lthy =
  if Named_Target.is_theory lthy
  then Generic_Target.theory_registration
  else Generic_Target.locale_dependency (Named_Target.the_name lthy);

fun gen_permanent_interpretation prep_interpretation expression raw_defs raw_eqns lthy =
  generic_interpretation prep_interpretation Element.witness_proof_eqs Local_Theory.notes_kind (subscribe lthy)
    expression raw_defs raw_eqns lthy

in

fun permanent_interpretation x = gen_permanent_interpretation cert_interpretation x;
fun permanent_interpretation_cmd x = gen_permanent_interpretation read_interpretation x;

end;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "permanent_interpretation"}
    "prove interpretation of locale expression into named theory"
    (Parse.!!! (Parse_Spec.locale_expression true) --
      Scan.optional (@{keyword "defining"} |-- Parse.and_list1 (Parse_Spec.opt_thm_name ":"
        -- ((Parse.binding -- Parse.opt_mixfix') --| @{keyword "="} -- Parse.term))) [] --
      Scan.optional (Parse.where_ |-- Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)) []
      >> (fn ((expr, defs), eqns) => permanent_interpretation_cmd expr defs eqns));

end;
