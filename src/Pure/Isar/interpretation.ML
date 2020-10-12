(*  Title:      Pure/Isar/interpretation.ML
    Author:     Clemens Ballarin, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen

Locale interpretation.
*)

signature INTERPRETATION =
sig
  type 'a defines = (Attrib.binding * ((binding * mixfix) * 'a)) list

  (*interpretation in proofs*)
  val interpret: Expression.expression_i -> Proof.state -> Proof.state
  val interpret_cmd: Expression.expression -> Proof.state -> Proof.state

  (*interpretation in local theories*)
  val interpretation: Expression.expression_i -> local_theory -> Proof.state
  val interpretation_cmd: Expression.expression -> local_theory -> Proof.state

  (*interpretation into global theories*)
  val global_interpretation: Expression.expression_i ->
    term defines -> local_theory -> Proof.state
  val global_interpretation_cmd: Expression.expression ->
    string defines -> local_theory -> Proof.state

  (*interpretation between locales*)
  val sublocale: Expression.expression_i ->
    term defines -> local_theory -> Proof.state
  val sublocale_cmd: Expression.expression ->
    string defines -> local_theory -> Proof.state
  val global_sublocale: string -> Expression.expression_i ->
    term defines -> theory -> Proof.state
  val global_sublocale_cmd: xstring * Position.T -> Expression.expression ->
    string defines -> theory -> Proof.state

  (*mixed Isar interface*)
  val isar_interpretation: Expression.expression_i -> local_theory -> Proof.state
  val isar_interpretation_cmd: Expression.expression -> local_theory -> Proof.state
end;

structure Interpretation : INTERPRETATION =
struct

(** common interpretation machinery **)

type 'a defines = (Attrib.binding * ((binding * mixfix) * 'a)) list

(* reading of locale expressions with rewrite morphisms *)

local

fun augment_with_def prep_term ((name, atts), ((b, mx), raw_rhs)) lthy =
  let
    val rhs = prep_term lthy raw_rhs;
    val lthy' = Variable.declare_term rhs lthy;
    val ((_, (_, def)), lthy'') =
      Local_Theory.define ((b, mx), ((Thm.def_binding_optional b name, atts), rhs)) lthy';
  in (Thm.symmetric def, lthy'') end;

fun augment_with_defs _ [] _ = pair []
      (*quasi-inhomogeneous type: definitions demand local theory rather than bare proof context*)
  | augment_with_defs prep_term raw_defs deps =
      Local_Theory.begin_nested
      #> snd
      #> fold Locale.activate_declarations deps
      #> fold_map (augment_with_def prep_term) raw_defs
      #> Local_Theory.end_nested_result Morphism.fact;

fun prep_interpretation prep_expr prep_term
  expression raw_defs initial_ctxt =
  let
    val ((propss, eq_propss, deps, eqnss, export), expr_ctxt) = prep_expr expression initial_ctxt;
    val (def_eqns, def_ctxt) =
      augment_with_defs prep_term raw_defs deps expr_ctxt;
    val export' = Proof_Context.export_morphism def_ctxt expr_ctxt;
  in (((propss, eq_propss, deps, eqnss, export, export'), def_eqns), def_ctxt) end;

in

fun cert_interpretation expression =
  prep_interpretation Expression.cert_goal_expression Syntax.check_term expression;

fun read_interpretation expression =
  prep_interpretation Expression.read_goal_expression Syntax.read_term expression;

end;


(* interpretation machinery *)

local

fun abs_def_rule eqns ctxt =
  (map (Local_Defs.abs_def_rule ctxt) (maps snd eqns), ctxt);

fun note_eqns_register note add_registration
    deps eqnss witss def_eqns thms export export' ctxt =
  let
    val factss = thms
      |> unflat ((map o map) #1 eqnss)
      |> map2 (map2 (fn b => fn eq => (b, [([Morphism.thm export eq], [])]))) ((map o map) #1 eqnss);
    val (eqnss', ctxt') =
      fold_map (fn facts => note Thm.theoremK facts #-> abs_def_rule) factss ctxt;
    val defs = (Binding.empty_atts, [(map (Morphism.thm (export' $> export)) def_eqns, [])]);
    val (eqns', ctxt'') = ctxt' |> note Thm.theoremK [defs] |-> abs_def_rule;
    val deps' =
      (deps ~~ witss) |> map (fn ((dep, morph), wits) =>
        (dep, morph $> Element.satisfy_morphism (map (Element.transform_witness export') wits)));
    fun register (dep, eqns) ctxt =
      ctxt |> add_registration
        {inst = dep,
          mixin =
            Option.map (rpair true)
              (Element.eq_morphism (Proof_Context.theory_of ctxt) (eqns @ eqns')),
          export = export};
  in ctxt'' |> fold register (deps' ~~ eqnss') end;

in

fun generic_interpretation prep_interpretation setup_proof note add_registration
    expression raw_defs initial_ctxt =
  let
    val (((propss, eq_propss, deps, eqnss, export, export'), def_eqns), goal_ctxt) =
      prep_interpretation expression raw_defs initial_ctxt;
    fun after_qed witss eqns =
      note_eqns_register note add_registration deps eqnss witss def_eqns eqns export export';
  in setup_proof after_qed propss (flat eq_propss) goal_ctxt end;

end;


(** interfaces **)

(* interpretation in proofs *)

local

fun setup_proof state after_qed propss eqns goal_ctxt =
  Element.witness_local_proof_eqs
    (fn witss => fn eqns => Proof.map_context (after_qed witss eqns) #> Proof.reset_facts)
    "interpret" propss eqns goal_ctxt state;

fun gen_interpret prep_interpretation expression state =
  Proof.assert_forward_or_chain state
  |> Proof.context_of
  |> generic_interpretation prep_interpretation (setup_proof state)
    Attrib.local_notes Locale.add_registration_proof expression [];

in

val interpret = gen_interpret cert_interpretation;
val interpret_cmd = gen_interpret read_interpretation;

end;


(* interpretation in local theories *)

fun activate_fragment registration =
  Local_Theory.mark_brittle #> Locale.add_registration_local_theory registration;

fun interpretation expression =
  generic_interpretation cert_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind activate_fragment expression [];

fun interpretation_cmd expression =
  generic_interpretation read_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind activate_fragment expression [];


(* interpretation into global theories *)

fun global_interpretation expression =
  generic_interpretation cert_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Local_Theory.theory_registration expression;

fun global_interpretation_cmd expression =
  generic_interpretation read_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Local_Theory.theory_registration expression;


(* interpretation between locales *)

fun sublocale expression =
  generic_interpretation cert_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Local_Theory.locale_dependency expression;

fun sublocale_cmd expression =
  generic_interpretation read_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Local_Theory.locale_dependency expression;

local

fun gen_global_sublocale prep_loc prep_interpretation
    raw_locale expression raw_defs thy =
  let
    val lthy = Named_Target.init (prep_loc thy raw_locale) thy;
    fun setup_proof after_qed =
      Element.witness_proof_eqs
        (fn wits => fn eqs => after_qed wits eqs #> Local_Theory.exit);
  in
    lthy |>
      generic_interpretation prep_interpretation setup_proof
        Local_Theory.notes_kind Local_Theory.locale_dependency expression raw_defs
  end;

in

fun global_sublocale expression =
  gen_global_sublocale (K I) cert_interpretation expression;

fun global_sublocale_cmd raw_expression =
  gen_global_sublocale Locale.check read_interpretation raw_expression;

end;


(* mixed Isar interface *)

local

fun register_or_activate lthy =
  if Named_Target.is_theory lthy
  then Local_Theory.theory_registration
  else activate_fragment;

fun gen_isar_interpretation prep_interpretation expression lthy =
  generic_interpretation prep_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind (register_or_activate lthy) expression [] lthy;

in

fun isar_interpretation expression =
  gen_isar_interpretation cert_interpretation expression;
fun isar_interpretation_cmd raw_expression =
  gen_isar_interpretation read_interpretation raw_expression;

end;

end;
