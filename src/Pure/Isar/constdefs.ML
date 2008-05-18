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

fun gen_constdef prep_vars prep_prop prep_att
    structs (raw_decl, ((raw_name, raw_atts), raw_prop)) thy =
  let
    fun err msg ts = error (cat_lines (msg :: map (Syntax.string_of_term_global thy) ts));

    val thy_ctxt = ProofContext.init thy;
    val struct_ctxt = #2 (ProofContext.add_fixes_i structs thy_ctxt);
    val ((d, mx), var_ctxt) =
      (case raw_decl of
        NONE => ((NONE, NoSyn), struct_ctxt)
      | SOME raw_var =>
          struct_ctxt |> prep_vars [raw_var] |-> (fn [(x, T, mx)] =>
            ProofContext.add_fixes_i [(x, T, mx)] #> snd #> pair (SOME x, mx)));

    val prop = prep_prop var_ctxt raw_prop;
    val (c, T) = #1 (LocalDefs.cert_def thy_ctxt (Logic.strip_imp_concl prop));
    val _ = (case d of NONE => () | SOME c' =>
      if c <> c' then
        err ("Head of definition " ^ quote c ^ " differs from declaration " ^ quote c') []
      else ());

    val def = Term.subst_atomic [(Free (c, T), Const (Sign.full_name thy c, T))] prop;
    val name = Thm.def_name_optional c raw_name;
    val atts = map (prep_att thy) raw_atts;

    val thy' =
      thy
      |> Sign.add_consts_i [(c, T, mx)]
      |> PureThy.add_defs_i false [((name, def), atts)]
      |-> (fn [thm] => Code.add_default_func thm);
  in ((c, T), thy') end;

fun gen_constdefs prep_vars prep_prop prep_att (raw_structs, specs) thy =
  let
    val ctxt = ProofContext.init thy;
    val (structs, _) = prep_vars (map (fn (x, T) => (x, T, Structure)) raw_structs) ctxt;
    val (decls, thy') = fold_map (gen_constdef prep_vars prep_prop prep_att structs) specs thy;
  in Pretty.writeln (ProofDisplay.pretty_consts ctxt (K true) decls); thy' end;

val add_constdefs = gen_constdefs ProofContext.read_vars Syntax.read_prop Attrib.attribute;
val add_constdefs_i = gen_constdefs ProofContext.cert_vars ProofContext.cert_prop (K I);

end;
