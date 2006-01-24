(*  Title:      Pure/Isar/constdefs.ML
    ID:         $Id$
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)

Old-style constant definitions, with type-inference and optional
structure context; specifications need to observe strictly sequential
dependencies; no support for overloading.
*)

signature CONSTDEFS =
sig
  val add_constdefs: (string * string option) list *
    ((bstring * string option * mixfix) option * ((bstring * Attrib.src list) * string)) list ->
    theory -> theory
  val add_constdefs_i: (string * typ option) list *
    ((bstring * typ option * mixfix) option * ((bstring * attribute list) * term)) list ->
    theory -> theory
end;

structure Constdefs: CONSTDEFS =
struct

(** add_constdefs(_i) **)

fun gen_constdef prep_vars prep_term prep_att
    structs (raw_decl, ((raw_name, raw_atts), raw_prop)) thy =
  let
    fun err msg ts =
      error (cat_lines (msg :: map (Sign.string_of_term thy) ts));

    val (_, ctxt) = thy |> ProofContext.init |> ProofContext.add_fixes_i structs;
    val ((d, mx), ctxt') =
      (case raw_decl of
        NONE => ((NONE, NoSyn), ctxt)
      | SOME raw_var =>
          ctxt |> prep_vars [raw_var] |-> (fn [(x, T, mx)] =>
            ProofContext.add_fixes_legacy [(x, T, mx)] #> snd #> pair (SOME x, mx)));

    val prop = prep_term ctxt' raw_prop;
    val concl = Logic.strip_imp_concl prop;
    val (lhs, _) = Logic.dest_equals concl handle TERM _ =>
      err "Not a meta-equality (==):" [concl];
    val head = Term.head_of lhs;
    val (c, T) = Term.dest_Free head handle TERM _ =>
      err "Locally fixed variable required as head of definition:" [head];
    val _ = (case d of NONE => () | SOME c' =>
      if c <> c' then
        err ("Head of definition " ^ quote c ^ " differs from declaration " ^ quote c') []
      else ());

    val def = Term.subst_atomic [(Free (c, T), Const (Sign.full_name thy c, T))] prop;
    val name = if raw_name = "" then Thm.def_name c else raw_name;
    val atts = map (prep_att thy) raw_atts;

    val thy' =
      thy
      |> Theory.add_consts_i [(c, T, mx)]
      |> PureThy.add_defs_i false [((name, def), atts)] |> snd;
  in ((c, T), thy') end;

fun gen_constdefs prep_vars prep_term prep_att (raw_structs, specs) thy =
  let
    val ctxt = ProofContext.init thy;
    val (structs, _) = prep_vars (map (fn (x, T) => (x, T, Structure)) raw_structs) ctxt;
    val (decls, thy') = fold_map (gen_constdef prep_vars prep_term prep_att structs) specs thy;
  in Pretty.writeln (LocalTheory.pretty_consts ctxt decls); thy' end;

val add_constdefs = gen_constdefs ProofContext.read_vars_legacy
  ProofContext.read_term_legacy Attrib.attribute;
val add_constdefs_i = gen_constdefs ProofContext.cert_vars_legacy ProofContext.cert_term (K I);

end;
