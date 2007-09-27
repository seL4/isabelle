(*  Title:      Pure/Tools/invoke.ML
    ID:         $Id$
    Author:     Makarius

Schematic invocation of locale expression in proof context.
*)

signature INVOKE =
sig
  val invoke: string * Attrib.src list -> Locale.expr -> string option list ->
    (string * string option * mixfix) list -> bool -> Proof.state -> Proof.state
  val invoke_i: string * attribute list -> Locale.expr -> term option list ->
    (string * typ option * mixfix) list -> bool -> Proof.state -> Proof.state
end;

structure Invoke: INVOKE =
struct


(* invoke *)

local

fun gen_invoke prep_att prep_expr parse_term add_fixes
    (prfx, raw_atts) raw_expr raw_insts fixes int state =
  let
    val thy = Proof.theory_of state;
    val _ = Proof.assert_forward_or_chain state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    val more_atts = map (prep_att thy) raw_atts;
    val (elems, _) = prep_expr raw_expr [] (ProofContext.init thy);

    val prems = maps Element.prems_of elems;
    val params = maps Element.params_of elems;
    val types = rev (fold Term.add_tfrees prems (fold (Term.add_tfreesT o #2) params []));

    val prems' = map Logic.varify prems;
    val params' = map (Logic.varify o Free) params;
    val types' = map (Logic.varifyT o TFree) types;

    val state' = state
      |> Proof.enter_forward
      |> Proof.begin_block
      |> Proof.map_context (snd o add_fixes fixes);
    val ctxt' = Proof.context_of state';

    val raw_insts' = zip_options params' raw_insts
      handle Library.UnequalLengths => error "Too many instantiations";

    fun prep_inst (t, u) =
      TypeInfer.constrain (TypeInfer.paramify_vars (Term.fastype_of t)) (parse_term ctxt' u);
    val insts = map #1 raw_insts' ~~
      Variable.polymorphic ctxt' (Syntax.check_terms ctxt' (map prep_inst raw_insts'));
    val inst_rules =
      replicate (length types') Drule.termI @
      map (fn t =>
        (case AList.lookup (op =) insts t of
          SOME u => Drule.mk_term (Thm.cterm_of thy u)
        | NONE => Drule.termI)) params';

    val propp =
      [(("", []), map (rpair [] o Logic.mk_term o Logic.mk_type) types'),
       (("", []), map (rpair [] o Logic.mk_term) params'),
       (("", []), map (rpair [] o Element.mark_witness) prems')];
    fun after_qed results =
      Proof.end_block #>
      Proof.map_context (fn ctxt =>
        let
          val ([res_types, res_params, res_prems], ctxt'') =
            fold_burrow (apfst snd oo Variable.import_thms false) results ctxt';

          val types'' = map (Logic.dest_type o Thm.term_of o Drule.dest_term) res_types;
          val params'' = map (Thm.term_of o Drule.dest_term) res_params;
          val inst = Element.morph_ctxt (Element.inst_morphism thy
            (Symtab.make (map #1 types ~~ types''), Symtab.make (map #1 params ~~ params'')));
          val elems' = map inst elems;
          val prems'' = map2 Element.make_witness (maps Element.prems_of elems') res_prems;
          val notes =
            maps (Element.facts_of thy) elems'
            |> Element.satisfy_facts prems''
            |> Element.generalize_facts ctxt'' ctxt
            |> Attrib.map_facts (Attrib.attribute_i thy)
            |> map (fn ((a, atts), bs) => ((a, atts @ more_atts), bs));
        in
          ctxt
          |> ProofContext.sticky_prefix prfx
          |> ProofContext.qualified_names
          |> (snd o ProofContext.note_thmss_i "" notes)
          |> ProofContext.restore_naming ctxt
        end) #>
      Proof.put_facts NONE #> Seq.single;
  in
    state'
    |> Proof.chain_facts chain_facts
    |> Proof.local_goal (K (K ())) (K I) ProofContext.bind_propp_schematic_i
      "invoke" NONE after_qed propp
    |> Element.refine_witness
    |> Seq.hd
    |> Proof.refine (Method.Basic (K (Method.METHOD (K (HEADGOAL (RANGE (map rtac inst_rules))))),
      Position.none))
    |> Seq.hd
  end;

in

fun invoke x =
  gen_invoke Attrib.attribute Locale.read_expr Syntax.parse_term ProofContext.add_fixes x;
fun invoke_i x = gen_invoke (K I) Locale.cert_expr (K I) ProofContext.add_fixes_i x;

end;


(* concrete syntax *)

local structure P = OuterParse and K = OuterKeyword in

val invokeP =
  OuterSyntax.command "invoke"
    "schematic invocation of locale expression in proof context"
    (K.tag_proof K.prf_goal)
    (SpecParse.opt_thm_name ":" -- SpecParse.locale_expr -- SpecParse.locale_insts -- P.for_fixes
      >> (fn (((name, expr), (insts, _)), fixes) =>
          Toplevel.print o Toplevel.proof' (invoke name expr insts fixes)));

val _ = OuterSyntax.add_parsers [invokeP];

end;

end;
