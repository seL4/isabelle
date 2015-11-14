(*  Title:      Pure/Isar/interpretation.ML
    Author:     Clemens Ballarin, TU Muenchen
    Author:     Florian Haftmann, TU Muenchen

Locale interpretation.
*)

signature INTERPRETATION =
sig
  val interpret: Expression.expression_i -> (Attrib.binding * term) list -> bool -> Proof.state -> Proof.state
  val interpret_cmd: Expression.expression -> (Attrib.binding * string) list ->
    bool -> Proof.state -> Proof.state
  val ephemeral_interpretation: Expression.expression_i -> (Attrib.binding * term) list ->
    local_theory -> Proof.state
  val permanent_interpretation: Expression.expression_i ->
    (Attrib.binding * ((binding * mixfix) * term)) list -> (Attrib.binding * term) list ->
    local_theory -> Proof.state
  val permanent_interpretation_cmd: Expression.expression ->
    (Attrib.binding * ((binding * mixfix) * string)) list -> (Attrib.binding * string) list ->
    local_theory -> Proof.state

  val interpretation: Expression.expression_i -> (Attrib.binding * term) list -> local_theory -> Proof.state
  val interpretation_cmd: Expression.expression -> (Attrib.binding * string) list ->
    local_theory -> Proof.state
  val sublocale: Expression.expression_i -> (Attrib.binding * term) list -> local_theory -> Proof.state
  val sublocale_cmd: Expression.expression -> (Attrib.binding * string) list -> local_theory -> Proof.state
  val sublocale_global: string -> Expression.expression_i ->
    (Attrib.binding * term) list -> theory -> Proof.state
  val sublocale_global_cmd: xstring * Position.T -> Expression.expression ->
    (Attrib.binding * string) list -> theory -> Proof.state
end;

structure Interpretation : INTERPRETATION =
struct

local

(** reading **)

(* without mixin definitions *)

fun prep_with_extended_syntax prep_prop deps ctxt props =
  let
    val deps_ctxt = fold Locale.activate_declarations deps ctxt;
  in
    map (prep_prop deps_ctxt o snd) props |> Syntax.check_terms deps_ctxt
      |> Variable.export_terms deps_ctxt ctxt
  end;

fun prep_interpretation prep_expr prep_prop prep_attr expression raw_eqns initial_ctxt =
  let
    val ((propss, deps, export), expr_ctxt) = prep_expr expression initial_ctxt;
    val eqns = prep_with_extended_syntax prep_prop deps expr_ctxt raw_eqns;
    val attrss = map (apsnd (map (prep_attr initial_ctxt)) o fst) raw_eqns;
    val goal_ctxt = fold Variable.auto_fixes eqns expr_ctxt;
    val export' = Variable.export_morphism goal_ctxt expr_ctxt;
  in (((propss, deps, export, export'), (eqns, attrss)), goal_ctxt) end;

val cert_interpretation =
  prep_interpretation Expression.cert_goal_expression (K I) (K I);

val read_interpretation =
  prep_interpretation Expression.read_goal_expression Syntax.parse_prop Attrib.check_src;


(* with mixin definitions *)

fun prep_interpretation_with_defs prep_expr prep_term prep_prop prep_attr expression raw_defs raw_eqns initial_ctxt =
  let
    (*reading*)
    val ((propss, deps, export), expr_ctxt1) = prep_expr expression initial_ctxt;
    val deps_ctxt = fold Locale.activate_declarations deps expr_ctxt1;
    val prep = Syntax.check_terms deps_ctxt #> Variable.export_terms deps_ctxt deps_ctxt;
    val rhss = (prep o map (prep_term deps_ctxt o snd o snd)) raw_defs;
    val eqns = (prep o map (prep_prop deps_ctxt o snd)) raw_eqns;

    (*defining*)
    val pre_defs = map2 (fn ((name, atts), ((b, mx), _)) => fn rhs =>
      ((b, mx), ((Thm.def_binding_optional b name, atts), rhs))) raw_defs rhss;
    val (defs, defs_ctxt) = fold_map Local_Theory.define pre_defs expr_ctxt1;
    val expr_ctxt2 = Proof_Context.transfer (Proof_Context.theory_of defs_ctxt) expr_ctxt1;
    val def_eqns = defs
      |> map (Thm.symmetric o
        Morphism.thm (Local_Theory.standard_morphism defs_ctxt expr_ctxt2) o snd o snd);

    (*setting up*)
    val attrss = map (apsnd (map (prep_attr expr_ctxt2)) o fst) raw_eqns;
    val goal_ctxt = fold Variable.auto_fixes eqns expr_ctxt2;
    val export' = Variable.export_morphism goal_ctxt expr_ctxt2;
  in (((propss, deps, export, export'), (def_eqns, eqns, attrss)), goal_ctxt) end;

val cert_interpretation_with_defs =
  prep_interpretation_with_defs Expression.cert_goal_expression (K I) (K I) (K I);

val read_interpretation_with_defs =
  prep_interpretation_with_defs Expression.read_goal_expression Syntax.parse_term Syntax.parse_prop Attrib.check_src;


(** generic interpretation machinery **)

(* without mixin definitions *)

local

fun meta_rewrite ctxt eqns =
  map (Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def) (maps snd eqns);

fun note_eqns_register note activate deps witss eqns attrss export export' ctxt =
  let
    val facts = map2 (fn attrs => fn eqn =>
      (attrs, [([Morphism.thm (export' $> export) eqn], [])])) attrss eqns;
    val (eqns', ctxt') = ctxt
      |> note Thm.theoremK facts
      |> (fn (eqns, ctxt') => (meta_rewrite ctxt' eqns, ctxt'));
    val dep_morphs =
      map2 (fn (dep, morph) => fn wits =>
          (dep, morph $> Element.satisfy_morphism (map (Element.transform_witness export') wits)))
        deps witss;
    fun activate' dep_morph ctxt =
      activate dep_morph
        (Option.map (rpair true) (Element.eq_morphism (Proof_Context.theory_of ctxt) eqns'))
        export ctxt;
  in
    ctxt'
    |> fold activate' dep_morphs
  end;

in

fun generic_interpretation prep_interpretation setup_proof note activate
    expression raw_eqns initial_ctxt =
  let
    val (((propss, deps, export, export'), (eqns, attrss)), goal_ctxt) =
      prep_interpretation expression raw_eqns initial_ctxt;
    fun after_qed witss eqns =
      note_eqns_register note activate deps witss eqns attrss export export';
  in setup_proof after_qed propss eqns goal_ctxt end;

end;


(* without mixin definitions *)

local

fun meta_rewrite eqns ctxt = (map (Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def) (maps snd eqns), ctxt);

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

end;


(** first dimension: proof vs. local theory **)

(* proof *)

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


(* local theory *)

fun gen_local_theory_interpretation prep_interpretation activate expression raw_eqns lthy =
  generic_interpretation prep_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind (activate lthy) expression raw_eqns lthy;


(* local theory with mixin definitions *)

fun gen_interpretation_with_defs prep_interpretation expression raw_defs raw_eqns =
  Local_Theory.assert_bottom true
  #> generic_interpretation_with_defs prep_interpretation Element.witness_proof_eqs
    Local_Theory.notes_kind Local_Theory.subscription expression raw_defs raw_eqns


(** second dimension: relation to underlying target **)

fun subscribe_or_activate lthy =
  if Named_Target.is_theory lthy
  then Local_Theory.subscription
  else Locale.activate_fragment;

fun subscribe_locale_only lthy =
  let
    val _ =
      if Named_Target.is_theory lthy
      then error "Not possible on level of global theory"
      else ();
  in Local_Theory.subscription end;


(** special case: global sublocale command **)

fun gen_sublocale_global prep_loc prep_interpretation
    raw_locale expression raw_eqns thy =
  let
    val lthy = Named_Target.init (prep_loc thy raw_locale) thy;
    fun setup_proof after_qed =
      Element.witness_proof_eqs
        (fn wits => fn eqs => after_qed wits eqs #> Local_Theory.exit);
  in
    lthy |>
      generic_interpretation prep_interpretation setup_proof
        Local_Theory.notes_kind (subscribe_locale_only lthy) expression raw_eqns
  end;

in


(** interfaces **)

fun interpret x = gen_interpret cert_interpretation x;
fun interpret_cmd x = gen_interpret read_interpretation x;

fun ephemeral_interpretation x =
  gen_local_theory_interpretation cert_interpretation (K Locale.activate_fragment) x;

fun permanent_interpretation x = gen_interpretation_with_defs cert_interpretation_with_defs x;
fun permanent_interpretation_cmd x = gen_interpretation_with_defs read_interpretation_with_defs x;

fun interpretation x =
  gen_local_theory_interpretation cert_interpretation subscribe_or_activate x;
fun interpretation_cmd x =
  gen_local_theory_interpretation read_interpretation subscribe_or_activate x;

fun sublocale x =
  gen_local_theory_interpretation cert_interpretation subscribe_locale_only x;
fun sublocale_cmd x =
  gen_local_theory_interpretation read_interpretation subscribe_locale_only x;

fun sublocale_global x = gen_sublocale_global (K I) cert_interpretation x;
fun sublocale_global_cmd x = gen_sublocale_global Locale.check read_interpretation x;

end;

end;
