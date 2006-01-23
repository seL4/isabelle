(*  Title:      Pure/Isar/specification.ML
    ID:         $Id$
    Author:     Makarius

Common theory/locale specifications --- with type-inference, but
without internal polymorphism.
*)

signature SPECIFICATION =
sig
  val read_specification: (string * string option * mixfix) list ->
    ((string * Attrib.src list) * string list) list -> Proof.context ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    Proof.context
  val cert_specification: (string * typ option * mixfix) list ->
    ((string * Attrib.src list) * term list) list -> Proof.context ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    Proof.context
  val axiomatization: xstring option -> (string * string option * mixfix) list ->
    ((bstring * Attrib.src list) * string list) list -> theory ->
    (term list * (bstring * thm list) list) * (theory * Proof.context)
  val axiomatization_i: string option -> (string * typ option * mixfix) list ->
    ((bstring * Attrib.src list) * term list) list -> theory ->
    (term list * (bstring * thm list) list) * (theory * Proof.context)
end;

structure Specification: SPECIFICATION =
struct

(* prepare specification *)

fun prep_specification prep_vars prep_propp prep_att
    raw_vars raw_specs ctxt =
  let
    val thy = ProofContext.theory_of ctxt;

    val (vars, vars_ctxt) = ctxt |> prep_vars raw_vars;
    val (xs, params_ctxt) = vars_ctxt |> ProofContext.add_fixes_i vars;
    val ((specs, vs), specs_ctxt) =
      prep_propp (params_ctxt, map (map (rpair ([], [])) o snd) raw_specs)
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

fun gen_axiomatization prep init locale raw_vars raw_specs thy =
  let
    val ((vars, specs), ctxt) = init locale thy |> prep raw_vars raw_specs;
    val (consts, consts_ctxt) = ctxt |> LocalTheory.consts vars;
    val subst = Term.subst_atomic (map (Free o fst) vars ~~ consts);
    val (axioms, axioms_ctxt) =
      consts_ctxt
      |> LocalTheory.axioms (specs |> map (fn (a, props) => (a, map subst props)))
      ||> LocalTheory.map_theory (Theory.add_finals_i false (map Term.head_of consts));
    val _ = Pretty.writeln (LocalTheory.pretty_consts ctxt (map fst vars));
  in ((consts, axioms), `LocalTheory.exit axioms_ctxt) end;

val axiomatization = gen_axiomatization read_specification LocalTheory.init;
val axiomatization_i = gen_axiomatization cert_specification LocalTheory.init_i;

end;
