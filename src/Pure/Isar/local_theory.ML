(*  Title:      Pure/Isar/local_theory.ML
    ID:         $Id$
    Author:     Makarius

Local theory operations, with optional target locale.
*)

signature LOCAL_THEORY =
sig
  val map_theory: (theory -> theory) -> Proof.context -> Proof.context
  val map_theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val init: xstring option -> theory -> Proof.context
  val init_i: string option -> theory -> Proof.context
  val exit: Proof.context -> theory
  val locale_of: Proof.context -> string option
  val params_of: Proof.context -> (string * typ) list
  val hyps_of: Proof.context -> term list
  val pretty_consts: Proof.context -> (string * typ) list -> Pretty.T
  val consts: ((string * typ) * mixfix) list -> Proof.context -> term list * Proof.context
  val notes: string -> ((bstring * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    Proof.context -> (bstring * thm list) list * Proof.context
  val note: (bstring * Attrib.src list) -> thm list -> Proof.context ->
    (bstring * thm list) * Proof.context
  val axioms: ((string * Attrib.src list) * term list) list -> Proof.context ->
    (bstring * thm list) list * Proof.context
end;

structure LocalTheory: LOCAL_THEORY =
struct


(** local context data **)

structure Data = ProofDataFun
(
  val name = "Isar/local_theory";
  type T =
   {locale: string option,
    params: (string * typ) list,
    hyps: term list,
    exit: theory -> theory};
  fun init _ = {locale = NONE, params = [], hyps = [], exit = I};
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;

val locale_of = #locale o Data.get;
val params_of = #params o Data.get;
val hyps_of = #hyps o Data.get;



(** theory **)

fun map_theory f ctxt =
  ProofContext.transfer (f (ProofContext.theory_of ctxt)) ctxt;

fun map_theory_result f ctxt =
  let val (res, thy') = f (ProofContext.theory_of ctxt)
  in (res, ProofContext.transfer thy' ctxt) end;

fun init_i NONE thy = ProofContext.init thy
  | init_i (SOME loc) thy =
      thy
      |> Locale.init loc
      |> ProofContext.inferred_fixes
      ||>> `ProofContext.assms_of
      |-> (fn (params, hyps) => Data.put
          {locale = SOME loc,
           params = params,
           hyps = hyps,
           exit = Sign.restore_naming thy})
      |> map_theory (Sign.add_path (Sign.base_name loc) #> Sign.no_base_names);

fun init target thy = init_i (Option.map (Locale.intern thy) target) thy;

fun exit ctxt = #exit (Data.get ctxt) (ProofContext.theory_of ctxt);



(** local theory **)

(* pretty_consts *)

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

end;


(* consts *)

fun consts decls ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val params = params_of ctxt;
    val ps = map Free params;
    val Ps = map snd params;
  in
    ctxt
    |> map_theory (Sign.add_consts_i (decls |> map (fn ((c, T), mx) => (c, Ps ---> T, mx))))
    |> pair (decls |> map (fn ((c, T), _) =>
      Term.list_comb (Const (Sign.full_name thy c, Ps ---> T), ps)))
  end;


(* notes *)

fun notes kind facts ctxt =
  (case locale_of ctxt of
    NONE => ctxt |> map_theory_result
      (PureThy.note_thmss_i (Drule.kind kind)
        (Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of ctxt)) facts))
  | SOME loc => ctxt |> map_theory_result (Locale.note_thmss_i kind loc facts #> apsnd #1));

fun note a ths ctxt =
  ctxt |> notes Drule.theoremK [(a, [(ths, [])])] |>> hd;


(* axioms *)

fun forall_elim frees =
  let
    fun elim (x, T) th =
      let
        val cert = Thm.cterm_of (Thm.theory_of_thm th);
        val var = cert (Var ((x, 0), #1 (Logic.dest_all (Thm.prop_of th))));
      in ((var, cert (Free (x, T))), Thm.forall_elim var th) end;
  in fold_map elim frees #-> Drule.cterm_instantiate end;

fun implies_elim hyps rule =
  let val cert = Thm.cterm_of (Thm.theory_of_thm rule)
  in fold (fn hyp => fn th => Thm.assume (cert hyp) COMP th) hyps rule end;

fun add_axiom name hyps prop thy =
  let
    val name' = (if name = "" then "axiom" else name) ^ "_" ^ string_of_int (serial ());
    val frees = rev ([] |> Term.add_frees prop |> fold Term.add_frees hyps);
    val prop' = Term.list_all_free (frees, Logic.list_implies (hyps, prop));
    val thy' = thy |> Theory.add_axioms_i [(name', prop')];
    val th =
      Thm.get_axiom_i thy' (Sign.full_name thy' name')
      |> forall_elim frees |> implies_elim hyps
      |> Goal.norm_hhf;
  in (th, thy') end;

fun axioms specs ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val hyps = hyps_of ctxt;
  in
    ctxt |> fold_map (fn ((name, atts), props) =>
      map_theory_result (fold_map (add_axiom name hyps) props) #-> note (name, atts)) specs
  end;

end;
