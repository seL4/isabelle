(*  Title:      Pure/Isar/specification.ML
    ID:         $Id$
    Author:     Makarius

Common theory/locale specifications --- with type-inference and
toplevel polymorphism.
*)

signature SPECIFICATION =
sig
  val read_specification: (string * string option * mixfix) list ->
    ((string * Attrib.src list) * string list) list -> local_theory ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    local_theory
  val cert_specification: (string * typ option * mixfix) list ->
    ((string * Attrib.src list) * term list) list -> local_theory ->
    (((string * typ) * mixfix) list * ((string * Attrib.src list) * term list) list) *
    local_theory
  val axiomatization: (string * string option * mixfix) list ->
    ((bstring * Attrib.src list) * string list) list -> local_theory ->
    (term list * (bstring * thm list) list) * local_theory
  val axiomatization_i: (string * typ option * mixfix) list ->
    ((bstring * Attrib.src list) * term list) list -> local_theory ->
    (term list * (bstring * thm list) list) * local_theory
  val definition:
    ((string * string option * mixfix) option * ((string * Attrib.src list) * string)) list ->
    local_theory -> (term * (bstring * thm)) list * local_theory
  val definition_i:
    ((string * typ option * mixfix) option * ((string * Attrib.src list) * term)) list ->
    local_theory -> (term * (bstring * thm)) list * local_theory
  val abbreviation: string * bool -> ((string * string option * mixfix) option * string) list ->
    local_theory -> local_theory
  val abbreviation_i: string * bool -> ((string * typ option * mixfix) option * term) list ->
    local_theory -> local_theory
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

fun gen_axioms prep raw_vars raw_specs ctxt =
  let
    val (vars, specs) = fst (prep raw_vars raw_specs ctxt);
    val cs = map fst vars;
    val spec_frees = member (op =) (fold (fold Term.add_frees o snd) specs []);

    val (consts, consts_ctxt) = ctxt |> LocalTheory.consts_restricted spec_frees vars;
    val subst = Term.subst_atomic (map Free cs ~~ consts);

    val (axioms, axioms_ctxt) =
      consts_ctxt
      |> LocalTheory.axioms (specs |> map (fn (a, props) => (a, map subst props)))
      ||> LocalTheory.theory (Theory.add_finals_i false (map Term.head_of consts));
    val _ = LocalTheory.print_consts ctxt spec_frees cs;
  in ((consts, axioms), axioms_ctxt) end;

val axiomatization = gen_axioms read_specification;
val axiomatization_i = gen_axioms cert_specification;


(* definition *)

fun gen_defs prep args ctxt =
  let
    fun define (raw_var, (raw_a, raw_prop)) ctxt' =
      let
        val (vars, [(a, [prop])]) = fst (prep (the_list raw_var) [(raw_a, [raw_prop])] ctxt');
        val (((x, T), rhs), prove) = LocalDefs.derived_def ctxt' true prop;
        val mx = (case vars of [] => NoSyn | [((x', _), mx)] =>
          if x = x' then mx
          else error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote x'));
      in
        ctxt'
        |> LocalTheory.def_finish prove ((x, mx), (a, rhs))
        |>> pair (x, T)
      end;

    val ((cs, defs), defs_ctxt) = ctxt |> fold_map define args |>> split_list;
    val def_frees = member (op =) (fold (Term.add_frees o fst) defs []);
    val _ = LocalTheory.print_consts ctxt def_frees cs;
  in (defs, defs_ctxt) end;

val definition = gen_defs read_specification;
val definition_i = gen_defs cert_specification;


(* abbreviation *)

fun gen_abbrevs prep mode args ctxt =
  let
    fun abbrev (raw_var, raw_prop) ctxt' =
      let
        val ((vars, [(_, [prop])]), _) =
          prep (the_list raw_var) [(("", []), [raw_prop])]
            (ctxt' |> ProofContext.expand_abbrevs false);
        val ((x, T), rhs) = LocalDefs.abs_def (#2 (LocalDefs.cert_def ctxt' prop));
        val mx = (case vars of [] => NoSyn | [((x', _), mx)] =>
          if x = x' then mx
          else error ("Head of abbreviation " ^ quote x ^ " differs from declaration " ^ quote x'));
      in
        ctxt'
        |> LocalTheory.abbrev mode ((x, mx), rhs)
        |> pair (x, T)
      end;

    val (cs, abbrs_ctxt) = ctxt
      |> ProofContext.set_syntax_mode mode
      |> fold_map abbrev args
      ||> ProofContext.restore_syntax_mode ctxt;
    val _ = LocalTheory.print_consts ctxt (K false) cs;
  in abbrs_ctxt end;

val abbreviation = gen_abbrevs read_specification;
val abbreviation_i = gen_abbrevs cert_specification;

end;
