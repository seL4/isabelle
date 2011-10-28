(*  Title:      Tools/interpretation_with_defs.ML
    Author:     Florian Haftmann, TU Muenchen

Interpretation accompanied with mixin definitions.  EXPERIMENTAL.
*)

signature INTERPRETATION_WITH_DEFS =
sig
  val interpretation: Expression.expression_i ->
    (Attrib.binding * ((binding * mixfix) * term)) list -> (Attrib.binding * term) list ->
    theory -> Proof.state
  val interpretation_cmd: Expression.expression ->
    (Attrib.binding * ((binding * mixfix) * string)) list -> (Attrib.binding * string) list ->
    theory -> Proof.state
end;

structure Interpretation_With_Defs : INTERPRETATION_WITH_DEFS =
struct

fun note_eqns_register deps witss def_eqns attrss eqns export export' context =
  let
    fun meta_rewrite context =
      map (Local_Defs.meta_rewrite_rule (Context.proof_of context) #> Drule.abs_def) o
        maps snd;
  in
    context
    |> Element.generic_note_thmss Thm.lemmaK
      (attrss ~~ map (fn eqn => [([Morphism.thm (export' $> export) eqn], [])]) eqns)
    |-> (fn facts => `(fn context => meta_rewrite context facts))
    |-> (fn eqns => fold (fn ((dep, morph), wits) =>
      fn context =>
        Locale.add_registration (dep, morph $> Element.satisfy_morphism
            (map (Element.transform_witness export') wits))
          (Element.eq_morphism (Context.theory_of context) (def_eqns @ eqns) |>
            Option.map (rpair true))
          export context) (deps ~~ witss))
  end;

local

fun gen_interpretation prep_expr prep_decl parse_term parse_prop prep_attr
    expression raw_defs raw_eqns theory =
  let
    val (_, (_, defs_ctxt)) =
      prep_decl expression I [] (Proof_Context.init_global theory);

    val rhss = map (parse_term defs_ctxt o snd o snd) raw_defs
      |> Syntax.check_terms defs_ctxt;
    val defs = map2 (fn (binding_thm, (binding_syn, _)) => fn rhs =>
      (binding_syn, (binding_thm, rhs))) raw_defs rhss;

    val (def_eqns, theory') = theory
      |> Named_Target.theory_init
      |> fold_map (Local_Theory.define) defs
      |>> map (Thm.symmetric o snd o snd)
      |> Local_Theory.exit_result_global (map o Morphism.thm);

    val ((propss, deps, export), expr_ctxt) = theory'
      |> Proof_Context.init_global
      |> prep_expr expression;

    val eqns = map (parse_prop expr_ctxt o snd) raw_eqns
      |> Syntax.check_terms expr_ctxt;
    val attrss = map ((apsnd o map) (prep_attr theory) o fst) raw_eqns;
    val goal_ctxt = fold Variable.auto_fixes eqns expr_ctxt;
    val export' = Variable.export_morphism goal_ctxt expr_ctxt;

    fun after_qed witss eqns =
      (Proof_Context.background_theory o Context.theory_map)
        (note_eqns_register deps witss def_eqns attrss eqns export export');

  in Element.witness_proof_eqs after_qed propss eqns goal_ctxt end;

in

fun interpretation x = gen_interpretation Expression.cert_goal_expression
  Expression.cert_declaration (K I) (K I) (K I) x;
fun interpretation_cmd x = gen_interpretation Expression.read_goal_expression
  Expression.read_declaration Syntax.parse_term Syntax.parse_prop Attrib.intern_src x;

end;

val definesK = "defines";
val _ = Keyword.keyword definesK;

val _ =
  Outer_Syntax.command "interpretation"
    "prove interpretation of locale expression in theory" Keyword.thy_goal
    (Parse.!!! (Parse_Spec.locale_expression true) --
      Scan.optional (Parse.$$$ definesK |-- Parse.and_list1 (Parse_Spec.opt_thm_name ":"
        -- ((Parse.binding -- Parse.opt_mixfix') --| Parse.$$$ "is" -- Parse.term))) [] --
      Scan.optional (Parse.where_ |-- Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)) []
      >> (fn ((expr, defs), equations) => Toplevel.print o
          Toplevel.theory_to_proof (interpretation_cmd expr defs equations)));

end;
