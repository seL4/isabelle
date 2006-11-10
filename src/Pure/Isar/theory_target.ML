(*  Title:      Pure/Isar/theory_target.ML
    ID:         $Id$
    Author:     Makarius

Common theory targets.
*)

signature THEORY_TARGET =
sig
  val peek: local_theory -> string option
  val begin: bstring -> Proof.context -> local_theory
  val init: xstring option -> theory -> local_theory
  val init_i: string option -> theory -> local_theory
end;

structure TheoryTarget: THEORY_TARGET =
struct

(** locale targets **)

(* context data *)

structure Data = ProofDataFun
(
  val name = "Isar/theory_target";
  type T = string option;
  fun init _ = NONE;
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;
val peek = Data.get;


(* pretty *)

fun pretty loc ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val fixes = map (fn (x, T) => (x, SOME T, NoSyn)) (#1 (ProofContext.inferred_fixes ctxt));
    val assumes = map (fn A => (("", []), [(A, [])])) (Assumption.assms_of ctxt);
    val elems =
      (if null fixes then [] else [Element.Fixes fixes]) @
      (if null assumes then [] else [Element.Assumes assumes]);
  in
    if loc = "" then
      [Pretty.block
        [Pretty.str "theory", Pretty.brk 1, Pretty.str (Context.theory_name thy),
          Pretty.str " =", Pretty.brk 1, ThyInfo.pretty_theory thy]]
    else if null elems then [Pretty.str ("locale " ^ Locale.extern thy loc)]
    else
      [Pretty.big_list ("locale " ^ Locale.extern thy loc ^ " =")
        (map (Pretty.chunks o Element.pretty_ctxt ctxt) elems)]
  end;


(* consts *)

fun consts loc depends decls lthy =
  let
    val xs = filter depends (#1 (ProofContext.inferred_fixes lthy));
    val ys = filter (Variable.newly_fixed lthy (LocalTheory.target_of lthy) o #1) xs;

    fun const ((c, T), mx) thy =
      let
        val U = map #2 xs ---> T;
        val mx' = if null ys then mx else NoSyn;
        val mx'' = Syntax.unlocalize_mixfix (loc <> "") mx';

        val t = Term.list_comb (Const (Sign.full_name thy c, U), map Free xs);
        val defn = ((c, if loc <> "" then mx else NoSyn (* FIXME !? *)), (("", []), t));
        val abbr = ((c, mx'), fold_rev (lambda o Free) ys t);
        val thy' = Sign.add_consts_authentic [(c, U, mx'')] thy;
      in ((defn, abbr), thy') end;

    val ((defns, abbrs), lthy') = lthy
      |> LocalTheory.theory_result (fold_map const decls) |>> split_list;
  in
    lthy'
    |> K (loc <> "") ? (snd o LocalTheory.abbrevs Syntax.default_mode abbrs)
    |> LocalDefs.add_defs defns |>> map (apsnd snd)
  end;


(* axioms *)

local

fun add_axiom hyps (name, prop) thy =
  let
    val name' = if name = "" then "axiom_" ^ serial_string () else name;
    val prop' = Logic.list_implies (hyps, prop);
    val thy' = thy |> Theory.add_axioms_i [(name', prop')];
    val axm = Drule.unvarify (Thm.get_axiom_i thy' (Sign.full_name thy' name'));
    val prems = map (Thm.assume o Thm.cterm_of thy') hyps;
  in (Drule.implies_elim_list axm prems, thy') end;

in

fun axioms specs lthy =
  let
    val hyps = Assumption.assms_of lthy;
    fun axiom ((name, atts), props) thy = thy
      |> fold_map (add_axiom hyps) (PureThy.name_multi name props)
      |-> (fn ths => pair ((name, atts), [(ths, [])]));
  in
    lthy
    |> fold (fold Variable.declare_term o snd) specs
    |> LocalTheory.theory_result (fold_map axiom specs)
    |-> LocalTheory.notes
  end;

end;


(* defs *)

local

fun add_def (name, prop) =
  Theory.add_defs_i false false [(name, prop)] #>
  (fn thy => (Drule.unvarify (Thm.get_axiom_i thy (Sign.full_name thy name)), thy));

fun expand_defs lthy =
  Drule.term_rule (ProofContext.theory_of lthy)
    (Assumption.export false lthy (LocalTheory.target_of lthy));

in

fun defs args lthy =
  let
    fun def ((x, mx), ((name, atts), rhs)) lthy1 =
      let
        val name' = Thm.def_name_optional x name;
        val T = Term.fastype_of rhs;
        val rhs' = expand_defs lthy1 rhs;
        val depends = member (op =) (Term.add_frees rhs' []);
        val defined = filter_out depends (Term.add_frees rhs []);

        val rhs_conv = rhs
          |> Thm.cterm_of (ProofContext.theory_of lthy1)
          |> Tactic.rewrite true (map_filter (LocalDefs.find_def lthy1 o #1) defined);

        val ([(lhs, local_def)], lthy2) = lthy1
          |> LocalTheory.consts depends [((x, T), mx)];
        val lhs' = #2 (Logic.dest_equals (Thm.prop_of local_def));

        val (global_def, lthy3) = lthy2
          |> LocalTheory.theory_result (add_def (name', Logic.mk_equals (lhs', rhs')));

        val eq = Thm.transitive (Thm.transitive local_def global_def) (Thm.symmetric rhs_conv);
      in ((lhs, ((name', atts), [([eq], [])])), lthy3) end;

    val ((lhss, facts), lthy') = lthy |> fold_map def args |>> split_list;
    val (res, lthy'') = lthy' |> LocalTheory.notes facts;
  in (lhss ~~ map (apsnd the_single) res, lthy'') end;

end;


(* notes *)

fun context_notes facts lthy =
  let
    val facts' = facts
      |> Element.export_standard_facts lthy lthy
      |> Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of lthy));
  in
    lthy
    |> ProofContext.qualified_names
    |> ProofContext.note_thmss_i facts'
    ||> ProofContext.restore_naming lthy
  end;

fun theory_notes keep_atts facts lthy = lthy |> LocalTheory.theory (fn thy =>
  let
    val facts' = facts
      |> Element.export_standard_facts lthy (ProofContext.init thy)
      |> Attrib.map_facts (if keep_atts then Attrib.attribute_i thy else K I);
  in
    thy
    |> Sign.qualified_names
    |> PureThy.note_thmss_i "" facts' |> #2
    |> Sign.restore_naming thy
  end);

fun locale_notes loc facts lthy = lthy |> LocalTheory.target (fn ctxt =>
  #2 (Locale.add_thmss "" loc (Element.export_standard_facts lthy ctxt facts) ctxt));

fun notes "" facts = theory_notes true facts #> context_notes facts
  | notes loc facts = theory_notes false facts #> locale_notes loc facts #> context_notes facts;


(* declarations *)

fun term_syntax "" f = LocalTheory.theory (Context.theory_map f)
  | term_syntax loc f = LocalTheory.target (Locale.add_term_syntax loc (Context.proof_map f));

fun declaration "" f = LocalTheory.theory (Context.theory_map f)
  | declaration loc f = I;    (* FIXME *)


(* init and exit *)

fun begin loc =
  Data.put (if loc = "" then NONE else SOME loc) #>
  LocalTheory.init (SOME (NameSpace.base loc))
   {pretty = pretty loc,
    consts = consts loc,
    axioms = axioms,
    defs = defs,
    notes = notes loc,
    term_syntax = term_syntax loc,
    declaration = declaration loc,
    reinit = fn _ => begin loc o (if loc = "" then ProofContext.init else Locale.init loc),
    exit = LocalTheory.target_of}

fun init_i NONE thy = begin "" (ProofContext.init thy)
  | init_i (SOME loc) thy = begin loc (Locale.init loc thy);

fun init (SOME "-") thy = init_i NONE thy
  | init loc thy = init_i (Option.map (Locale.intern thy) loc) thy;

end;
