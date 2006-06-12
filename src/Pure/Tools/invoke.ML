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

fun gen_invoke prep_att prep_expr prep_terms add_fixes
    (prfx, raw_atts) raw_expr raw_insts fixes int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;

    val more_atts = map (prep_att thy) raw_atts;
    val (elems, _) = prep_expr raw_expr [] (ProofContext.init thy);

    val prems = maps Element.prems_of elems;
    val params = maps Element.params_of elems;
    val types = rev (fold Term.add_tfrees prems (fold (Term.add_tfreesT o #2) params []));

    val prems' = map Logic.varify prems;
    val params' = map (Logic.varify o Free) params;
    val types' = map (Logic.varifyT o TFree) types;

    val state' = state
      |> Proof.begin_block
      |> Proof.map_context (snd o add_fixes fixes);
    val ctxt' = Proof.context_of state';

    val raw_insts' = zip_options params' raw_insts
      handle Library.UnequalLengths => error "Too many instantiations";
    val insts = map #1 raw_insts' ~~
      prep_terms ctxt' (map (fn (t, u) => (u, Term.fastype_of t)) raw_insts');
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
      Seq.map (Proof.map_context (fn ctxt =>
        let
          val ([res_types, res_params, res_prems], ctxt'') =
            fold_burrow (ProofContext.import false) results ctxt';

          val types'' = map (Logic.dest_type o Thm.term_of o Drule.dest_term) res_types;
          val params'' = map (Thm.term_of o Drule.dest_term) res_params;
          val elems' = elems |> map (Element.inst_ctxt thy
            (Symtab.make (map #1 types ~~ types''), Symtab.make (map #1 params ~~ params'')));
          val prems'' = map2 Element.make_witness (maps Element.prems_of elems') res_prems;

          val Element.Notes notes = 
            Element.Notes (maps (Element.facts_of thy) elems')
            |> Element.satisfy_ctxt prems''
            |> Element.map_ctxt_values I I (ProofContext.export ctxt'' ctxt);
            (* FIXME export typs/terms *)
          val notes' = notes
            |> Attrib.map_facts (Attrib.attribute_i thy)
            |> map (fn ((a, atts), facts) => ((a, atts @ more_atts), facts));
        in
          ctxt
          |> ProofContext.sticky_prefix prfx
          |> ProofContext.qualified_names
          |> (snd o ProofContext.note_thmss_i notes')
          |> ProofContext.restore_naming ctxt
        end) #> Proof.put_facts NONE);
  in
    state'
    |> Proof.local_goal (K (K ())) (K I) ProofContext.bind_propp_schematic_i
      "invoke" NONE after_qed propp
    |> Element.refine_witness
    |> Seq.hd
    |> Proof.refine (Method.Basic (K (Method.METHOD (K (HEADGOAL (RANGE (map rtac inst_rules)))))))
    |> Seq.hd
  end;

(* FIXME *)
fun read_terms ctxt args =
  #1 (ProofContext.read_termTs ctxt (K false) (K NONE) (K NONE) [] args)
  |> ProofContext.polymorphic ctxt;

(* FIXME *)
fun cert_terms ctxt args = map fst args;

in

fun invoke x = gen_invoke Attrib.attribute Locale.read_expr read_terms ProofContext.add_fixes x;
fun invoke_i x = gen_invoke (K I) Locale.cert_expr cert_terms ProofContext.add_fixes_i x;

end;


(* concrete syntax *)

local structure P = OuterParse and K = OuterKeyword in

val invokeP =
  OuterSyntax.command "invoke"
    "schematic invocation of locale expression in proof context"
    (K.tag_proof K.prf_goal)
    (P.opt_thm_name ":" -- P.locale_expr -- P.locale_insts -- P.for_fixes
      >> (fn (((name, expr), insts), fixes) =>
          Toplevel.print o Toplevel.proof' (invoke name expr insts fixes)));

val _ = OuterSyntax.add_parsers [invokeP];

end;

end;
