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

fun pretty_const sg (c, T) =
  Pretty.block [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (Sign.pretty_typ sg T)];

fun pretty_constdefs sg decls =
  Pretty.big_list "constants" (map (pretty_const sg) decls);

fun gen_constdef prep_typ prep_term prep_att
    structs (thy, (decl, ((raw_name, raw_atts), raw_prop))) =
  let
    val sign = Theory.sign_of thy;
    fun err msg ts =
      error (cat_lines (msg :: map (Sign.string_of_term sign) ts));

    val ctxt =
      ProofContext.init thy |> ProofContext.add_fixes
        (flat (map (fn (As, T) => map (fn A => (A, T, None)) As) structs));
    val (ctxt', d, mx) =
      (case decl of None => (ctxt, None, Syntax.NoSyn) | Some (x, raw_T, mx) =>
        let
          val x' = Syntax.const_name x mx and mx' = Syntax.fix_mixfix x mx;
          val T = apsome (prep_typ ctxt) raw_T;
        in (ProofContext.add_fixes_liberal [(x', T, Some mx')] ctxt, Some x', mx') end);

    val prop = prep_term ctxt' raw_prop;
    val concl = Logic.strip_imp_concl prop;
    val (lhs, _) = Logic.dest_equals concl handle TERM _ =>
      err "Not a meta-equality (==):" [concl];
    val head = Term.head_of lhs;
    val (c, T) = Term.dest_Free head handle TERM _ =>
      err "Locally fixed variable required as head of definition:" [head];
    val _ = (case d of None => () | Some c' =>
      if c <> c' then
        err ("Head of definition " ^ quote c ^ " differs from declaration " ^ quote c') []
      else ());

    val def = Term.subst_atomic [(Free (c, T), Const (Sign.full_name sign c, T))] prop;
    val name = if raw_name = "" then Thm.def_name c else raw_name;
    val atts = map (prep_att thy) raw_atts;

    val thy' =
      thy
      |> Theory.add_consts_i [(c, T, mx)]
      |> PureThy.add_defs_i false [((name, def), atts)] |> #1;
  in (thy', (c, T)) end;

fun gen_constdefs prep_vars prep_typ prep_term prep_att (raw_structs, specs) thy =
  let
    val structs = #2 (foldl_map prep_vars (ProofContext.init thy, raw_structs));
    val (thy', decls) = (thy, specs)
      |> foldl_map (gen_constdef prep_typ prep_term prep_att structs);
  in Pretty.writeln (pretty_constdefs (Theory.sign_of thy') decls); thy' end;

val add_constdefs = gen_constdefs ProofContext.read_vars_liberal
  ProofContext.read_typ ProofContext.read_term_liberal Attrib.global_attribute;
val add_constdefs_i = gen_constdefs ProofContext.cert_vars_liberal
  ProofContext.cert_typ ProofContext.cert_term (K I);

end;
