(*  Title:      Pure/Isar/constdefs.ML
    ID:         $Id$
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Standard constant definitions, with type-inference and optional
structure context; specifications need to observe strictly sequential
dependencies; no support for overloading.
*)

signature CONSTDEFS =
sig
  val add_constdefs: (string list * string option) list *
    ((bstring * string option * Syntax.mixfix) option *
      ((bstring * Args.src list) * string)) list
    -> theory -> theory
  val add_constdefs_i: (string list * typ option) list *
    ((bstring * typ option * Syntax.mixfix) option *
      ((bstring * theory attribute list) * term)) list
    -> theory -> theory
end;

structure Constdefs: CONSTDEFS =
struct

(** add_constdefs(_i) **)

fun gen_constdef prep_typ prep_term prep_att
    structs (thy, (decl, ((raw_name, raw_atts), raw_prop))) =
  let
    val ctxt =
      ProofContext.init thy |> ProofContext.add_fixes
        (flat (map (fn (As, T) => map (fn A => (A, T, None)) As) structs));
    val (ctxt', mx) =
      (case decl of None => (ctxt, Syntax.NoSyn) | Some (x, raw_T, mx) =>
        (ProofContext.add_fixes [(x, apsome (prep_typ ctxt) raw_T, Some mx)] ctxt, mx));

    val prop = prep_term ctxt' raw_prop;
    fun err msg = raise TERM (msg, [prop]);

    val (lhs, _) = Logic.dest_equals (Logic.strip_imp_concl prop)
      handle TERM _ => err "Not a meta-equality (==)";
    val (c, T) = Term.dest_Free (Term.head_of lhs)
      handle TERM _ => err "Head of definition needs to turn out as fixed variable";
    val _ = (case decl of None => () | Some (d, _, _) =>
      if c = d then ()
      else err ("Head of definition " ^ quote c ^ " differs from declaration " ^ quote d));

    val full = Sign.full_name (Theory.sign_of thy);
    val def = Term.subst_atomic [(Free (c, T), Const (full c, T))] prop;
    val name = if raw_name = "" then Thm.def_name c else raw_name;
    val atts = map (prep_att thy) raw_atts;
  in
    thy
    |> Theory.add_consts_i [(c, T, mx)]
    |> PureThy.add_defs_i false [((name, def), atts)] |> #1
  end;

fun gen_constdefs prep_vars prep_typ prep_term prep_att (raw_structs, specs) thy =
  let val structs = #2 (foldl_map prep_vars (ProofContext.init thy, raw_structs))
  in foldl (gen_constdef prep_typ prep_term prep_att structs) (thy, specs) end;

val add_constdefs = gen_constdefs ProofContext.read_vars
  ProofContext.read_typ ProofContext.read_term Attrib.global_attribute;
val add_constdefs_i = gen_constdefs ProofContext.cert_vars
  ProofContext.cert_typ ProofContext.cert_term (K I);

end;
