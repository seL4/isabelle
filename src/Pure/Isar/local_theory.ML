(*  Title:      Pure/Isar/local_theory.ML
    ID:         $Id$
    Author:     Makarius

Local theory operations, with optional target locale.
*)

type local_theory = Proof.context;

signature LOCAL_THEORY =
sig
  val params_of: local_theory -> (string * typ) list
  val hyps_of: local_theory -> term list
  val standard: local_theory -> thm -> thm
  val pretty_consts: local_theory -> (string * typ -> bool) -> (string * typ) list -> Pretty.T
  val quiet_mode: bool ref
  val print_consts: local_theory -> (string * typ -> bool) -> (string * typ) list -> unit
  val theory: (theory -> theory) -> local_theory -> local_theory
  val theory_result: (theory -> 'a * theory) -> local_theory -> 'a * local_theory
  val init: xstring option -> theory -> local_theory
  val init_i: string option -> theory -> local_theory
  val restore: local_theory -> local_theory
  val exit: local_theory -> local_theory * theory
  val restore_naming: local_theory -> local_theory
  val naming: local_theory -> local_theory
  val mapping: xstring option -> (local_theory -> local_theory) -> theory -> local_theory * theory
  val consts: ((bstring * typ) * mixfix) list -> local_theory -> term list * local_theory
  val consts_restricted: (string * typ -> bool) ->
    ((bstring * typ) * mixfix) list -> local_theory -> term list * local_theory
  val axioms: ((bstring * Attrib.src list) * term list) list -> local_theory ->
    (bstring * thm list) list * local_theory
  val axioms_finish: (local_theory -> thm -> thm) ->
    ((bstring * Attrib.src list) * term list) list -> local_theory ->
    (bstring * thm list) list * local_theory
  val notes: string -> ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    local_theory -> (bstring * thm list) list * local_theory
  val note: (bstring * Attrib.src list) * thm list -> local_theory ->
    (bstring * thm list) * local_theory
  val def: (bstring * mixfix) * ((bstring * Attrib.src list) * term) ->
    local_theory -> (term * (bstring * thm)) * local_theory
  val def_finish: (local_theory -> term -> thm -> thm) ->
    (bstring * mixfix) * ((bstring * Attrib.src list) * term) ->
    local_theory -> (term * (bstring * thm)) * local_theory
end;

structure LocalTheory: LOCAL_THEORY =
struct


(** local context data **)

structure Data = ProofDataFun
(
  val name = "Pure/local_theory";
  type T =
   {locale: (string * (cterm list * Proof.context)) option,
    params: (string * typ) list,
    hyps: term list,
    restore_naming: theory -> theory};
  fun init thy = {locale = NONE, params = [], hyps = [], restore_naming = I};
  fun print _ _ = ();
);
val _ = Context.add_setup Data.init;

fun map_locale f = Data.map (fn {locale, params, hyps, restore_naming} =>
  {locale = Option.map (fn (loc, (view, ctxt)) => (loc, (view, f ctxt))) locale,
    params = params, hyps = hyps, restore_naming = restore_naming});

val locale_of = #locale o Data.get;
val params_of = #params o Data.get;
val hyps_of = #hyps o Data.get;

fun standard ctxt =
  (case #locale (Data.get ctxt) of
    NONE => Drule.standard
  | SOME (_, (_, loc_ctxt)) => ProofContext.export_standard ctxt loc_ctxt);


(* print consts *)

val quiet_mode = ref false;

local

fun pretty_var ctxt (x, T) =
  Pretty.block [Pretty.str x, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (ProofContext.pretty_typ ctxt T)];

fun pretty_vars ctxt kind vs = Pretty.big_list kind (map (pretty_var ctxt) vs);

in

fun pretty_consts ctxt pred cs =
  (case filter pred (params_of ctxt) of
    [] => pretty_vars ctxt "constants" cs
  | ps => Pretty.chunks [pretty_vars ctxt "parameters" ps, pretty_vars ctxt "constants" cs]);

fun print_consts _ _ [] = ()
  | print_consts ctxt pred cs =
      if ! quiet_mode then () else Pretty.writeln (pretty_consts ctxt pred cs);

end;


(* theory/locale substructures *)

fun theory_result f ctxt =
  let val (res, thy') = f (ProofContext.theory_of ctxt)
  in (res, ctxt |> map_locale (ProofContext.transfer thy') |> ProofContext.transfer thy') end;

fun theory f ctxt = #2 (theory_result (f #> pair ()) ctxt);

fun locale_result f ctxt =
  (case locale_of ctxt of
    NONE => error "Local theory: no locale context"
  | SOME (_, view_ctxt) =>
      let
        val (res, loc_ctxt') = f view_ctxt;
        val thy' = ProofContext.theory_of loc_ctxt';
      in (res, ctxt |> map_locale (K loc_ctxt') |> ProofContext.transfer thy') end);

fun locale f ctxt =
  if is_none (locale_of ctxt) then ctxt
  else #2 (locale_result (f #> pair ()) ctxt);


(* init -- restore -- exit *)

fun init_i NONE thy = ProofContext.init thy
  | init_i (SOME loc) thy =
      thy
      |> Locale.init loc
      ||>> ProofContext.inferred_fixes
      |> (fn ((view, params), ctxt) => Data.put
          {locale = SOME (loc, (view, ctxt)),
           params = params,
           hyps = ProofContext.assms_of ctxt,
           restore_naming = Sign.restore_naming thy} ctxt);

fun init loc thy = init_i (Option.map (Locale.intern thy) loc) thy;

fun restore ctxt =
  (case locale_of ctxt of
    NONE => ctxt
  | SOME (_, (_, loc_ctxt)) => loc_ctxt |> Data.put (Data.get ctxt));

fun exit ctxt = (ctxt, ProofContext.theory_of ctxt);


(* local naming *)

fun naming ctxt =
  (case locale_of ctxt of
    NONE => ctxt
  | SOME (loc, _) => ctxt |> theory (Sign.sticky_prefix (Sign.base_name loc)));

fun restore_naming ctxt = theory (#restore_naming (Data.get ctxt)) ctxt;

fun mapping loc f =
  init loc #> naming #> f #> restore_naming #> exit;



(** local theory **)

(* consts *)

fun consts_restricted pred decls ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val params = filter pred (params_of ctxt);
    val ps = map Free params;
    val Ps = map #2 params;
    val abbrevs = decls |> map (fn ((c, T), mx) =>
      let val t = Term.list_comb (Const (Sign.full_name thy c, Ps ---> T), ps)
      in (c, t, mx) end);
  in
    ctxt |>
    (case locale_of ctxt of
      NONE => theory (Sign.add_consts_i (map (fn ((c, T), mx) => (c, T, mx)) decls))
    | SOME (loc, _) =>
        theory (Sign.add_consts_i (map (fn ((c, T), _) => (c, Ps ---> T, NoSyn)) decls)) #>
        locale (Locale.add_abbrevs loc true abbrevs) #>
        ProofContext.add_abbrevs_i true abbrevs)
    |> pair (map #2 abbrevs)
  end;

val consts = consts_restricted (K true);


(* fact definitions *)

fun notes kind facts ctxt =
  let
    val attrib = Attrib.attribute_i (ProofContext.theory_of ctxt);
    val facts' = map (apsnd (map (apfst (map (standard ctxt))))) facts;
  in
    ctxt |>
    (case locale_of ctxt of
      NONE => theory_result (PureThy.note_thmss_i kind (Attrib.map_facts attrib facts'))
    | SOME (loc, _) =>
        locale_result (apfst #1 o Locale.add_thmss kind loc facts'))
    ||> (#2 o ProofContext.note_thmss_i (Attrib.map_facts attrib facts))
  end;

fun note (a, ths) ctxt =
  ctxt |> notes PureThy.theoremK [(a, [(ths, [])])] |>> hd;


(* axioms *)

local

fun add_axiom hyps (name, prop) thy =
  let
    val name' = if name = "" then "axiom_" ^ string_of_int (serial ()) else name;
    val frees = rev ([] |> Term.add_frees prop |> fold Term.add_frees hyps);
    val prop' = Term.list_all_free (frees, Logic.list_implies (hyps, prop));
    val thy' = thy |> Theory.add_axioms_i [(name', prop')];

    val cert = Thm.cterm_of thy';
    fun all_polymorphic (x, T) th =
      let val var = cert (Var ((x, 0), #1 (Logic.dest_all (Thm.prop_of th))))
      in ((var, cert (Free (x, T))), Thm.forall_elim var th) end;
    fun implies_polymorphic hyp th = Thm.assume (cert hyp) COMP th;
    val th =
      Thm.get_axiom_i thy' (Sign.full_name thy' name')
      |> fold_map all_polymorphic frees |-> Drule.cterm_instantiate
      |> fold implies_polymorphic hyps
  in (th, thy') end;

in

fun axioms_finish finish = fold_map (fn ((name, atts), props) =>
  fold ProofContext.fix_frees props
  #> (fn ctxt => ctxt
    |> theory_result (fold_map (add_axiom (hyps_of ctxt)) (PureThy.name_multi name props))
    |-> (fn ths => note ((name, atts), map (finish ctxt) ths))));

val axioms = axioms_finish (K I);

end;


(* constant definitions *)

local

fun add_def (name, prop) =
  Theory.add_defs_i false [(name, prop)] #> (fn thy =>
    let
      val th = Thm.get_axiom_i thy (Sign.full_name thy name);
      val cert = Thm.cterm_of thy;
      val subst = map2 (fn var => fn free => (cert (Var var), cert (Free free)))
        (Term.add_vars (Thm.prop_of th) []) (Term.add_frees prop []);
    in (Drule.cterm_instantiate subst th, thy) end);

in

fun def_finish finish (var, spec) ctxt =
  let
    val (x, mx) = var;
    val ((name, atts), rhs) = spec;
    val name' = if name = "" then Thm.def_name x else name;
    val rhs_frees = Term.add_frees rhs [];
  in
    ctxt
    |> consts_restricted (member (op =) rhs_frees) [((x, Term.fastype_of rhs), mx)]
    |-> (fn [lhs] =>
      theory_result (add_def (name', Logic.mk_equals (lhs, rhs)))
      #-> (fn th => fn ctxt' => note ((name', atts), [finish ctxt' lhs th]) ctxt')
      #> apfst (fn (b, [th]) => (lhs, (b, th))))
  end;

val def = def_finish (K (K I));

end;

end;
