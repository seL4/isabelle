(*  Title:      Pure/Isar/specification.ML
    ID:         $Id$
    Author:     Makarius

Common theory/locale specifications --- with type-inference and
toplevel polymorphism.
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
    (term list * (bstring * thm list) list) * (Proof.context * theory)
  val axiomatization_i: string option -> (string * typ option * mixfix) list ->
    ((bstring * Attrib.src list) * term list) list -> theory ->
    (term list * (bstring * thm list) list) * (Proof.context * theory)
  val axiomatization_loc: (string * typ option * mixfix) list ->
    ((bstring * Attrib.src list) * term list) list -> Proof.context ->
    (term list * (bstring * thm list) list) * Proof.context
  val definition: xstring option ->
    ((string * string option * mixfix) option * ((string * Attrib.src list) * string)) list ->
    theory -> (term * (bstring * thm)) list * (Proof.context * theory)
  val definition_i: string option ->
    ((string * typ option * mixfix) option * ((string * Attrib.src list) * term)) list ->
    theory -> (term * (bstring * thm)) list * (Proof.context * theory)
  val definition_loc:
    ((string * typ option * mixfix) option * ((string * Attrib.src list) * term)) list ->
    Proof.context -> (term * (bstring * thm)) list * Proof.context
end;

structure Specification: SPECIFICATION =
struct

(* prepare specification *)

fun prep_specification prep_vars prep_propp prep_att raw_vars raw_specs ctxt =
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

fun gen_axioms prep init exit print raw_vars raw_specs context =
  let
    val ctxt = init context;
    val (vars, specs) = fst (prep raw_vars raw_specs ctxt);
    val cs = map fst vars;
    val spec_frees = member (op =) (fold (fold Term.add_frees o snd) specs []);

    val (consts, consts_ctxt) = ctxt |> LocalTheory.consts_restricted spec_frees vars;
    val subst = Term.subst_atomic (map Free cs ~~ consts);

    val (axioms, axioms_ctxt) =
      consts_ctxt
      |> LocalTheory.axioms (specs |> map (fn (a, props) => (a, map subst props)))
      ||> LocalTheory.theory (Theory.add_finals_i false (map Term.head_of consts));
    val _ = print ctxt spec_frees cs;
  in ((consts, axioms), exit axioms_ctxt) end;

fun axiomatization loc =
  gen_axioms read_specification (LocalTheory.init loc) LocalTheory.exit LocalTheory.print_consts;
fun axiomatization_i loc =
  gen_axioms cert_specification (LocalTheory.init_i loc) LocalTheory.exit LocalTheory.print_consts;
val axiomatization_loc = gen_axioms cert_specification I I (K (K (K ())));


(* definition *)

fun gen_defs prep init exit print args context =
  let
    fun define (raw_var, (raw_a, raw_prop)) ctxt =
      let
        val (vars, [(a, [prop])]) = fst (prep (the_list raw_var) [(raw_a, [raw_prop])] ctxt);
        val (((x, T), rhs), prove) = LocalDefs.derived_def ctxt prop;
        val mx = (case vars of [] => NoSyn | [((x', _), mx)] =>
          if x = x' then mx
          else error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote x'));
      in
        ctxt
        |> LocalTheory.def_finish prove ((x, mx), (a, rhs))
        |>> pair (x, T)
      end;

    val ctxt = init context;
    val ((cs, defs), defs_ctxt) = ctxt |> fold_map define args |>> split_list;
    val def_frees = member (op =) (fold (Term.add_frees o fst) defs []);
    val _ = print ctxt def_frees cs;
  in (defs, exit defs_ctxt) end;

fun definition loc =
  gen_defs read_specification (LocalTheory.init loc) LocalTheory.exit LocalTheory.print_consts;
fun definition_i loc =
  gen_defs cert_specification (LocalTheory.init_i loc) LocalTheory.exit LocalTheory.print_consts;
val definition_loc = gen_defs cert_specification I I (K (K (K ())));

end;
