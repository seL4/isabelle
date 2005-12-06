(*  Title:      Pure/Isar/constdefs.ML
    ID:         $Id$
    Author:     Makarius, Hagia Maria Sion Abbey (Jerusalem)

Standard constant definitions, with type-inference and optional
structure context; specifications need to observe strictly sequential
dependencies; no support for overloading.
*)

signature CONSTDEFS =
sig
  val add_constdefs: (string list * string option) list *
    ((bstring * string option * Syntax.mixfix) option *
      ((bstring * Attrib.src list) * string)) list
    -> theory -> theory
  val add_constdefs_i: (string list * typ option) list *
    ((bstring * typ option * Syntax.mixfix) option *
      ((bstring * theory attribute list) * term)) list
    -> theory -> theory
end;

structure Constdefs: CONSTDEFS =
struct

(** add_constdefs(_i) **)

fun pretty_const thy (c, T) =
  Pretty.block [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (Sign.pretty_typ thy T)];

fun pretty_constdefs thy decls =
  Pretty.big_list "constants" (map (pretty_const thy) decls);

fun gen_constdef prep_typ prep_term prep_att
    structs (decl, ((raw_name, raw_atts), raw_prop)) thy =
  let
    fun err msg ts =
      error (cat_lines (msg :: map (Sign.string_of_term thy) ts));

    val ctxt =
      ProofContext.init thy |> ProofContext.add_fixes
        (List.concat (map (fn (As, T) => map (fn A => (A, T, NONE)) As) structs));
    val (ctxt', d, mx) =
      (case decl of NONE => (ctxt, NONE, Syntax.NoSyn) | SOME (x, raw_T, mx) =>
        let
          val x' = Syntax.const_name x mx and mx' = Syntax.fix_mixfix x mx;
          val T = Option.map (prep_typ ctxt) raw_T;
        in (ProofContext.add_fixes_liberal [(x', T, SOME mx')] ctxt, SOME x', mx') end);

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
      |> PureThy.add_defs_i false [((name, def), atts)]
      |> snd;
  in ((c, T), thy') end;

fun gen_constdefs prep_vars prep_typ prep_term prep_att (raw_structs, specs) thy =
  let
    val structs = #1 (fold_map prep_vars raw_structs (ProofContext.init thy));
    val (decls, thy') = fold_map (gen_constdef prep_typ prep_term prep_att structs) specs thy
  in Pretty.writeln (pretty_constdefs thy' decls); thy' end;

val add_constdefs = gen_constdefs ProofContext.read_vars_liberal
  ProofContext.read_typ ProofContext.read_term_liberal Attrib.global_attribute;
val add_constdefs_i = gen_constdefs ProofContext.cert_vars_liberal
  ProofContext.cert_typ ProofContext.cert_term (K I);

end;
