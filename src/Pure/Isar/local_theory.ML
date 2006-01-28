(*  Title:      Pure/Isar/local_theory.ML
    ID:         $Id$
    Author:     Makarius

Local theory operations, with optional target locale.
*)

signature LOCAL_THEORY =
sig
  val params_of: Proof.context -> (string * typ) list
  val hyps_of: Proof.context -> term list
  val standard: Proof.context -> thm -> thm
  val pretty_consts: Proof.context -> (string * typ) list -> Pretty.T
  val print_consts: Proof.context -> (string * typ) list -> unit
  val theory: (theory -> theory) -> Proof.context -> Proof.context
  val theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val init: xstring option -> theory -> Proof.context
  val init_i: string option -> theory -> Proof.context
  val exit: Proof.context -> Proof.context * theory
  val consts: ((bstring * typ) * mixfix) list -> Proof.context -> term list * Proof.context
  val axioms: ((bstring * Attrib.src list) * term list) list -> Proof.context ->
    (bstring * thm list) list * Proof.context
  val axioms_finish: (Proof.context -> thm -> thm) ->
    ((bstring * Attrib.src list) * term list) list -> Proof.context ->
    (bstring * thm list) list * Proof.context
  val notes: string -> ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    Proof.context -> (bstring * thm list) list * Proof.context
  val note: (bstring * Attrib.src list) * thm list -> Proof.context ->
    (bstring * thm list) * Proof.context
  val def: (bstring * mixfix) * ((bstring * Attrib.src list) * term) ->
    Proof.context -> (term * (bstring * thm)) * Proof.context
  val def_finish: (Proof.context -> term -> thm -> thm) ->
    (bstring * mixfix) * ((bstring * Attrib.src list) * term) ->
    Proof.context -> (term * (bstring * thm)) * Proof.context
end;

structure LocalTheory: LOCAL_THEORY =
struct

(** local context data **)

structure Data = ProofDataFun
(
  val name = "Isar/local_theory";
  type T =
   {locale: (string * (cterm list * Proof.context)) option,
    params: (string * typ) list,
    hyps: term list,
    exit: theory -> theory};
  fun init thy = {locale = NONE, params = [], hyps = [], exit = I};
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;

fun map_locale f = Data.map (fn {locale, params, hyps, exit} =>
  {locale = Option.map (fn (loc, (view, ctxt)) => (loc, (view, f ctxt))) locale,
    params = params, hyps = hyps, exit = exit});

val locale_of = #locale o Data.get;
val params_of = #params o Data.get;
val hyps_of = #hyps o Data.get;

fun standard ctxt =
  (case #locale (Data.get ctxt) of
    NONE => Drule.standard
  | SOME (_, (_, loc_ctxt)) => ProofContext.export_standard ctxt loc_ctxt);


(* print consts *)

local

fun pretty_var ctxt (x, T) =
  Pretty.block [Pretty.str x, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (ProofContext.pretty_typ ctxt T)];

fun pretty_vars ctxt kind vs = Pretty.big_list kind (map (pretty_var ctxt) vs);

in

fun pretty_consts ctxt cs =
  (case params_of ctxt of
    [] => pretty_vars ctxt "constants" cs
  | ps => Pretty.chunks [pretty_vars ctxt "parameters" ps, pretty_vars ctxt "constants" cs]);

fun print_consts _ [] = ()
  | print_consts ctxt cs = Pretty.writeln (pretty_consts ctxt cs);

end;


(* theory/locale substructures *)

fun transfer thy =
  ProofContext.transfer thy #> map_locale (ProofContext.transfer thy);

fun theory f ctxt = transfer (f (ProofContext.theory_of ctxt)) ctxt;

fun theory_result f ctxt =
  let val (res, thy') = f (ProofContext.theory_of ctxt)
  in (res, transfer thy' ctxt) end;

fun locale_result f ctxt =
  (case locale_of ctxt of
    NONE => error "Local theory: no locale context"
  | SOME (loc, (view, loc_ctxt)) =>
      let
        val (res, loc_ctxt') = f loc_ctxt;
        val thy' = ProofContext.theory_of loc_ctxt';
      in (res, ctxt |> map_locale (K loc_ctxt') |> transfer thy') end);


(* init -- exit *)

fun init_i NONE thy = ProofContext.init thy
  | init_i (SOME loc) thy =
      thy
      |> Locale.init loc
      ||>> ProofContext.inferred_fixes
      |> (fn ((view, params), ctxt) => Data.put
          {locale = SOME (loc, (view, ctxt)),
           params = params,
           hyps = ProofContext.assms_of ctxt,
           exit = Sign.restore_naming thy} ctxt)
      |> theory (Sign.add_path (Sign.base_name loc) #> Sign.no_base_names);

fun init loc thy = init_i (Option.map (Locale.intern thy) loc) thy;

fun exit ctxt = (ctxt, #exit (Data.get ctxt) (ProofContext.theory_of ctxt));



(** local theory **)

(* consts *)

fun consts decls ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val params = params_of ctxt;
    val ps = map Free params;
    val Ps = map #2 params;
  in
    ctxt
    |> theory (Sign.add_consts_i (decls |> map (fn ((c, T), mx) => (c, Ps ---> T, mx))))
    |> pair (decls |> map (fn ((c, T), _) =>
      Term.list_comb (Const (Sign.full_name thy c, Ps ---> T), ps)))
  end;


(* fact definitions *)

fun notes kind facts ctxt =
  let
    val attrib = Attrib.attribute_i (ProofContext.theory_of ctxt);
    val facts' = map (apsnd (map (apfst (map (standard ctxt))))) facts;
  in
    ctxt |>
    (case locale_of ctxt of
      NONE => theory_result (PureThy.note_thmss_i kind (Attrib.map_facts attrib facts'))
    | SOME (loc, view_ctxt) =>
        locale_result (K (apfst #1 (Locale.add_thmss kind loc facts' view_ctxt))))
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
  in
    ctxt
    |> consts [((x, Term.fastype_of rhs), mx)]
    |-> (fn [lhs] =>
      theory_result (add_def (name', Logic.mk_equals (lhs, rhs)))
      #-> (fn th => fn ctxt' => note ((name', atts), [finish ctxt' lhs th]) ctxt')
      #> apfst (fn (b, [th]) => (lhs, (b, th))))
  end;

val def = def_finish (K (K I));

end;

end;
