(*  Title:      Pure/Tools/invoke.ML
    ID:         $Id$
    Author:     Makarius

Schematic invocation of locale expression in proof context.
*)

signature INVOKE =
sig
  val invoke: string * Attrib.src list -> Locale.expr -> string option list -> bool ->
    Proof.state -> Proof.state
  val invoke_i: string * attribute list -> Locale.expr -> term option list -> bool ->
    Proof.state -> Proof.state
end;

structure Invoke: INVOKE =
struct

(* invoke *)

local

fun gen_invoke prep_att prep_expr prep_terms
    (prfx, raw_atts) raw_expr raw_insts int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val thy = Proof.theory_of state;
    val ctxt = Proof.context_of state;

    val atts = map (prep_att thy) raw_atts;
    val (elems, _) = prep_expr raw_expr [] (ProofContext.init thy);
    val xs = maps Element.params_of elems;
    val As = maps Element.prems_of elems;
    val xs' = map (Logic.varify o Free) xs;
    val As' = map Logic.varify As;

    val raw_insts' = zip_options xs' raw_insts
      handle Library.UnequalLengths => error "Too many instantiations";
    val insts = map #1 raw_insts' ~~
      prep_terms ctxt (map (fn (t, u) => (u, Term.fastype_of t)) raw_insts');
    val inst_rules = xs' |> map (fn t =>
      (case AList.lookup (op =) insts t of
        SOME u => Drule.mk_term (Thm.cterm_of thy u)
      | NONE => Drule.termI));

    val propp =
      [(("", []), map (rpair [] o Logic.mk_term) xs'),
       (("", []), map (rpair [] o Element.mark_witness) As')];

    fun after_qed [insts, results] =
      Proof.put_facts NONE
      #> Seq.single;
  in
    state
    |> Proof.local_goal (ProofDisplay.print_results int) (K I) ProofContext.bind_propp_schematic_i
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

fun invoke x = gen_invoke Attrib.attribute Locale.read_expr read_terms x;
fun invoke_i x = gen_invoke (K I) Locale.cert_expr cert_terms x;

end;


(* concrete syntax *)

local structure P = OuterParse and K = OuterKeyword in

val invokeP =
  OuterSyntax.command "invoke"
    "schematic invocation of locale expression in proof context"
    (K.tag_proof K.prf_goal)
    (P.opt_thm_name ":" -- P.locale_expr -- P.locale_insts >> (fn ((x, y), z) =>
      Toplevel.print o Toplevel.proof' (invoke x y z)));

val _ = OuterSyntax.add_parsers [invokeP];

end;

end;
