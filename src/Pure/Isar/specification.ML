(*  Title:      Pure/Isar/specification.ML
    ID:         $Id$
    Author:     Makarius

Theory specifications --- with type-inference, but no internal
polymorphism.
*)

signature SPECIFICATION =
sig
  val pretty_consts: Proof.context -> (string * typ) list -> Pretty.T
  val read_specification:
    (string * string option * mixfix) list *
      ((string * Attrib.src list) * string list) list -> Proof.context ->
    ((string * typ * mixfix) list *
      ((string * Context.generic attribute list) * term list) list) * Proof.context
  val cert_specification:
    (string * typ option * mixfix) list *
      ((string * Context.generic attribute list) * term list) list -> Proof.context ->
    ((string * typ * mixfix) list *
      ((string * Context.generic attribute list) * term list) list) * Proof.context
  val axiomatize:
    (string * string option * mixfix) list *
      ((bstring * Attrib.src list) * string list) list -> theory -> thm list list * theory
  val axiomatize_i:
    (string * typ option * mixfix) list *
      ((bstring * Context.generic attribute list) * term list) list -> theory ->
    thm list list * theory
end;

structure Specification: SPECIFICATION =
struct

(* pretty_consts *)

fun pretty_const ctxt (c, T) =
  Pretty.block [Pretty.str c, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (ProofContext.pretty_typ ctxt T)];

fun pretty_consts ctxt decls =
  Pretty.big_list "constants" (map (pretty_const ctxt) decls);


(* prepare specification *)

fun prep_specification prep_vars prep_propp prep_att
    (raw_vars, raw_specs) ctxt =
  let
    val thy = ProofContext.theory_of ctxt;

    val (vars, vars_ctxt) = ctxt |> prep_vars raw_vars;
    val (xs, params_ctxt) = vars_ctxt |> ProofContext.add_fixes_i vars;
    val ((specs, vs), specs_ctxt) =
      prep_propp (params_ctxt, map (map (rpair ([], [])) o snd) raw_specs)
      |> swap |>> map (map fst)
      ||>> fold_map ProofContext.inferred_type xs;

    val params = map2 (fn (x, T) => fn (_, _, mx) => (x, T, mx)) vs vars;
    val names = map (fst o fst) raw_specs;
    val atts = map (map (prep_att thy) o snd o fst) raw_specs;
  in ((params, (names ~~ atts) ~~ specs), specs_ctxt) end;

fun read_specification x =
  prep_specification ProofContext.read_vars ProofContext.read_propp Attrib.generic_attribute x;
fun cert_specification x =
  prep_specification ProofContext.cert_vars ProofContext.cert_propp (K I) x;


(* axiomatize *)

fun gen_axiomatize prep args thy =
  let
    val ((consts, specs), ctxt) = prep args (ProofContext.init thy);
    val subst = consts |> map (fn (x, T, _) => (Free (x, T), Const (Sign.full_name thy x, T)));
    val axioms = specs |> map (fn ((name, att), ts) =>
      ((name, map (Term.subst_atomic subst) ts), map Attrib.theory att));
    val (thms, thy') =
      thy
      |> Theory.add_consts_i consts
      |> PureThy.add_axiomss_i axioms
      ||> Theory.add_finals_i false (map snd subst);
  in Pretty.writeln (pretty_consts ctxt (map (dest_Free o fst) subst)); (thms, thy') end;

val axiomatize = gen_axiomatize read_specification;
val axiomatize_i = gen_axiomatize cert_specification;

end;
