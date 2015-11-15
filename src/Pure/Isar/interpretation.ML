(*  Title:      Pure/Isar/interpretation.ML
    Author:     Clemens Ballarin, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen

Locale interpretation.
*)

signature INTERPRETATION =
sig
  type 'a defines = (Attrib.binding * ((binding * mixfix) * 'a)) list
  type 'a rewrites = (Attrib.binding * 'a) list

  (*interpretation in proofs*)
  val interpret: Expression.expression_i -> term rewrites -> bool -> Proof.state -> Proof.state
  val interpret_cmd: Expression.expression -> string rewrites -> bool -> Proof.state -> Proof.state

  (*algebraic-view*)
  val global_interpretation: Expression.expression_i ->
    term defines -> term rewrites -> theory -> Proof.state
  val global_sublocale: string -> Expression.expression_i ->
    term defines -> term rewrites -> theory -> Proof.state
  val global_sublocale_cmd: xstring * Position.T -> Expression.expression ->
    string defines -> string rewrites -> theory -> Proof.state
  val sublocale: Expression.expression_i ->
    term defines -> term rewrites -> local_theory -> Proof.state
  val sublocale_cmd: Expression.expression ->
    string defines -> string rewrites -> local_theory -> Proof.state

  (*local-theory-based view*)
  val ephemeral_interpretation: Expression.expression_i ->
    term rewrites -> local_theory -> Proof.state
  val permanent_interpretation: Expression.expression_i ->
    term defines -> term rewrites -> local_theory -> Proof.state
  val permanent_interpretation_cmd: Expression.expression ->
    string defines -> string rewrites -> local_theory -> Proof.state

  (*mixed Isar interface*)
  val interpretation: Expression.expression_i -> term rewrites -> local_theory -> Proof.state
  val interpretation_cmd: Expression.expression -> string rewrites ->
    local_theory -> Proof.state
end;

structure Interpretation : INTERPRETATION =
struct

(** common interpretation machinery **)

type 'a defines = (Attrib.binding * ((binding * mixfix) * 'a)) list
type 'a rewrites = (Attrib.binding * 'a) list

(* reading of locale expressions with rewrite morphisms *)

local

fun prep_interpretation prep_expr prep_term prep_prop prep_attr expression raw_defs raw_eqns initial_ctxt =
  let
    (*reading*)
    val ((propss, deps, export), expr_ctxt) = prep_expr expression initial_ctxt;
    val deps_ctxt = fold Locale.activate_declarations deps expr_ctxt;
    val prep = Syntax.check_terms deps_ctxt #> Variable.export_terms deps_ctxt deps_ctxt;
    val rhss = (prep o map (prep_term deps_ctxt o snd o snd)) raw_defs;
    val eqns = (prep o map (prep_prop deps_ctxt o snd)) raw_eqns;

    (*defining*)
    val pre_defs = map2 (fn ((name, atts), ((b, mx), _)) => fn rhs =>
      ((b, mx), ((Thm.def_binding_optional b name, atts), rhs))) raw_defs rhss;
    val (defs, forked_ctxt) = fold_map Local_Theory.define pre_defs expr_ctxt;
    val def_ctxt = Proof_Context.transfer (Proof_Context.theory_of forked_ctxt) expr_ctxt;
    val def_eqns = defs
      |> map (Thm.symmetric o
        Morphism.thm (Local_Theory.standard_morphism forked_ctxt def_ctxt) o snd o snd);

    (*setting up proof*)
    val attrss = map (apsnd (map (prep_attr def_ctxt)) o fst) raw_eqns;
    val goal_ctxt = fold Variable.auto_fixes eqns def_ctxt;
    val export' = Variable.export_morphism goal_ctxt def_ctxt;
  in (((propss, deps, export, export'), (def_eqns, eqns, attrss)), goal_ctxt) end;

in

val cert_interpretation =
  prep_interpretation Expression.cert_goal_expression (K I) (K I) (K I);

val read_interpretation =
  prep_interpretation Expression.read_goal_expression Syntax.parse_term Syntax.parse_prop Attrib.check_src;

end;


(* interpretation machinery *)

local

fun meta_rewrite eqns ctxt =
  (map (Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def) (maps snd eqns), ctxt);

fun note_eqns_register note activate deps witss def_eqns eqns attrss export export' ctxt =
  let
    val facts = (Attrib.empty_binding, [(map (Morphism.thm (export' $> export)) def_eqns, [])])
      :: map2 (fn attrs => fn eqn => (attrs, [([Morphism.thm (export' $> export) eqn], [])])) attrss eqns;
    val (eqns', ctxt') = ctxt
      |> note Thm.theoremK facts
      |-> meta_rewrite;
    val dep_morphs = map2 (fn (dep, morph) => fn wits =>
      (dep, morph $> Element.satisfy_morphism (map (Element.transform_witness export') wits))) deps witss;
    fun activate' dep_morph ctxt = activate dep_morph
      (Option.map (rpair true) (Element.eq_morphism (Proof_Context.theory_of ctxt) eqns')) export ctxt;
  in
    ctxt'
    |> fold activate' dep_morphs
  end;

in

fun generic_interpretation_with_defs prep_interpretation setup_proof note add_registration
    expression raw_defs raw_eqns initial_ctxt =
  let
    val (((propss, deps, export, export'), (def_eqns, eqns, attrss)), goal_ctxt) =
      prep_interpretation expression raw_defs raw_eqns initial_ctxt;
    fun after_qed witss eqns =
      note_eqns_register note add_registration deps witss def_eqns eqns attrss export export';
  in setup_proof after_qed propss eqns goal_ctxt end;

fun generic_interpretation prep_interpretation setup_proof note add_registration expression =
  generic_interpretation_with_defs prep_interpretation setup_proof note add_registration expression [];

end;


(** interfaces **)

(* interpretation in proofs *)

local

fun gen_interpret prep_interpretation expression raw_eqns int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;
    fun lift_after_qed after_qed witss eqns =
      Proof.map_context (after_qed witss eqns) #> Proof.reset_facts;
    fun setup_proof after_qed propss eqns goal_ctxt =
      Element.witness_local_proof_eqs (lift_after_qed after_qed) "interpret"
        propss eqns goal_ctxt int state;
  in
    generic_interpretation prep_interpretation setup_proof
      Attrib.local_notes (Context.proof_map ooo Locale.add_registration) expression raw_eqns ctxt
  end;

in

fun interpret expression = gen_interpret cert_interpretation expression;
fun interpret_cmd raw_expression = gen_interpret read_interpretation raw_expression;

end;


(* algebraic-view *)

local

fun gen_global_interpretation prep_interpretation expression
    raw_defs raw_eqns thy = 
  let
    val lthy = Named_Target.theory_init thy;
    fun setup_proof after_qed =
      Element.witness_proof_eqs
        (fn wits => fn eqs => after_qed wits eqs #> Local_Theory.exit);
  in
    lthy |>
      generic_interpretation_with_defs prep_interpretation setup_proof
        Local_Theory.notes_kind Local_Theory.subscription expression raw_defs raw_eqns
  end;

fun gen_global_sublocale prep_loc prep_interpretation
    raw_locale expression raw_defs raw_eqns thy =
  let
    val lthy = Named_Target.init (prep_loc thy raw_locale) thy;
    fun setup_proof after_qed =
      Element.witness_proof_eqs
        (fn wits => fn eqs => after_qed wits eqs #> Local_Theory.exit);
  in
    lthy |>
      generic_interpretation_with_defs prep_interpretation setup_proof
        Local_Theory.notes_kind Local_Theory.subscription expression raw_defs raw_eqns
  end;

fun subscribe_locale_only lthy =
  let
    val _ =
      if Named_Target.is_theory lthy
      then error "Not possible on level of global theory"
      else ();
  in Local_Theory.subscription end;

fun gen_sublocale prep_interpretation expression raw_defs raw_eqns lthy =
  generic_interpretation_with_defs prep_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind (subscribe_locale_only lthy) expression raw_defs raw_eqns lthy;

in

fun global_interpretation expression =
  gen_global_interpretation cert_interpretation expression;
fun global_sublocale expression =
  gen_global_sublocale (K I) cert_interpretation expression;
fun global_sublocale_cmd raw_expression =
  gen_global_sublocale Locale.check read_interpretation raw_expression;
fun sublocale expression =
  gen_sublocale cert_interpretation expression;
fun sublocale_cmd raw_expression =
  gen_sublocale read_interpretation raw_expression;

end;


(* local-theory-based view *)

local

fun gen_permanent_interpretation prep_interpretation expression raw_defs raw_eqns =
  Local_Theory.assert_bottom true
  #> generic_interpretation_with_defs prep_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Local_Theory.subscription expression raw_defs raw_eqns

in

fun ephemeral_interpretation expression =
  generic_interpretation cert_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Locale.activate_fragment expression;

fun permanent_interpretation expression =
  gen_permanent_interpretation cert_interpretation expression;
fun permanent_interpretation_cmd raw_expression =
  gen_permanent_interpretation read_interpretation raw_expression;

end;


(* mixed Isar interface *)

local

fun subscribe_or_activate lthy =
  if Named_Target.is_theory lthy
  then Local_Theory.subscription
  else Locale.activate_fragment;

fun gen_local_theory_interpretation prep_interpretation expression raw_eqns lthy =
  generic_interpretation prep_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind (subscribe_or_activate lthy) expression raw_eqns lthy;

in

fun interpretation expression =
  gen_local_theory_interpretation cert_interpretation expression;
fun interpretation_cmd raw_expression =
  gen_local_theory_interpretation read_interpretation raw_expression;

end;

end;
