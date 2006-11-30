(*  Title:      Pure/Isar/theory_target.ML
    ID:         $Id$
    Author:     Makarius

Common theory/locale targets.
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
    val assumes = map (fn A => (("", []), [(A, [])])) (map Thm.term_of (Assumption.assms_of ctxt));
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

fun consts is_loc depends decls lthy =
  let
    val xs = filter depends (#1 (ProofContext.inferred_fixes (LocalTheory.target_of lthy)));

    fun const ((c, T), mx) thy =
      let
        val U = map #2 xs ---> T;
        val t = Term.list_comb (Const (Sign.full_name thy c, U), map Free xs);
        val thy' = Sign.add_consts_authentic [(c, U, Syntax.unlocalize_mixfix is_loc mx)] thy;
      in (((c, mx), t), thy') end;

    val (abbrs, lthy') = lthy |> LocalTheory.theory_result (fold_map const decls);
    val defs = abbrs |> map (fn (x, t) => (x, (("", []), t)));
  in
    lthy'
    |> is_loc ? LocalTheory.abbrevs Syntax.default_mode abbrs
    |> LocalDefs.add_defs defs |>> map (apsnd snd)
  end;


(* defs *)

local

infix also;

fun eq1 also eq2 =
  eq2 COMP (eq1 COMP (Drule.incr_indexes2 eq1 eq2 transitive_thm));

fun expand_term ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val thy_ctxt = ProofContext.init thy;
    val ct = Thm.cterm_of thy t;
    val (defs, ct') = LocalDefs.export ctxt thy_ctxt (Drule.mk_term ct) ||> Drule.dest_term;
  in (Thm.term_of ct', Tactic.rewrite true defs ct) end;

fun add_def (name, prop) =
  Theory.add_defs_i false false [(name, prop)] #>
  (fn thy => (Drule.unvarify (Thm.get_axiom_i thy (Sign.full_name thy name)), thy));

in

fun defs kind args lthy0 =
  let
    fun def ((c, mx), ((name, atts), rhs)) lthy1 =
      let
        val (rhs', rhs_conv) = expand_term lthy0 rhs;
        val xs = Variable.add_fixed (LocalTheory.target_of lthy0) rhs' [];

        val ([(lhs, lhs_def)], lthy2) = lthy1
          |> LocalTheory.consts (member (op =) xs) [((c, Term.fastype_of rhs), mx)];
        val lhs' = #2 (Logic.dest_equals (Thm.prop_of lhs_def));

        val name' = Thm.def_name_optional c name;
        val (def, lthy3) = lthy2
          |> LocalTheory.theory_result (add_def (name', Logic.mk_equals (lhs', rhs')));

        val eq =
          (*c == loc.c xs*) lhs_def
          (*lhs' == rhs'*)  also def
          (*rhs' == rhs*)   also Thm.symmetric rhs_conv;
      in ((lhs, ((name', atts), [([eq], [])])), lthy3) end;

    val ((lhss, facts), lthy') = lthy0 |> fold_map def args |>> split_list;
    val (res, lthy'') = lthy' |> LocalTheory.notes kind facts;
  in (lhss ~~ map (apsnd the_single) res, lthy'') end;

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

fun axioms kind specs lthy =
  let
    val hyps = map Thm.term_of (Assumption.assms_of lthy);
    fun axiom ((name, atts), props) thy = thy
      |> fold_map (add_axiom hyps) (PureThy.name_multi name props)
      |-> (fn ths => pair ((name, atts), [(ths, [])]));
  in
    lthy
    |> fold (fold Variable.declare_term o snd) specs
    |> LocalTheory.theory_result (fold_map axiom specs)
    |-> LocalTheory.notes kind
  end;

end;


(* notes *)

fun import_export_proof ctxt (name, raw_th) =
  let
    val thy = ProofContext.theory_of ctxt;
    val thy_ctxt = ProofContext.init thy;
    val certT = Thm.ctyp_of thy;
    val cert = Thm.cterm_of thy;

    (*export assumes/defines*)
    val th = Goal.norm_result raw_th;
    val (defs, th') = LocalDefs.export ctxt thy_ctxt th;
    val concl_conv = Tactic.rewrite true defs (Thm.cprop_of th);
    val assms = map (Tactic.rewrite_rule defs o Thm.assume) (Assumption.assms_of ctxt);
    val nprems = Thm.nprems_of th' - Thm.nprems_of th;

    (*export fixes*)
    val tfrees = map TFree (Drule.fold_terms Term.add_tfrees th' []);
    val frees = map Free (Drule.fold_terms Term.add_frees th' []);
    val (th'' :: vs) = (th' :: map (Drule.mk_term o cert) (map Logic.mk_type tfrees @ frees))
      |> Variable.export ctxt thy_ctxt
      |> Drule.zero_var_indexes_list;

    (*thm definition*)
    val result = PureThy.name_thm true (name, Goal.close_result th'');

    (*import fixes*)
    val (tvars, vars) =
      chop (length tfrees) (map (Thm.term_of o Drule.dest_term) vs)
      |>> map Logic.dest_type;

    val instT = map_filter (fn (TVar v, T) => SOME (v, T) | _ => NONE) (tvars ~~ tfrees);
    val inst = filter (is_Var o fst) (vars ~~ frees);
    val cinstT = map (pairself certT o apfst TVar) instT;
    val cinst = map (pairself (cert o Term.map_types (TermSubst.instantiateT instT))) inst;
    val result' = Thm.instantiate (cinstT, cinst) result;

    (*import assumes/defines*)
    val assm_tac = FIRST' (map (fn assm => Tactic.compose_tac (false, assm, 0)) assms);
    val result'' =
      (case SINGLE (Seq.INTERVAL assm_tac 1 nprems) result' of
        NONE => raise THM ("Failed to re-import result", 0, [result'])
      | SOME res => res) COMP (concl_conv COMP_INCR Drule.equal_elim_rule2)
      |> Goal.norm_result;

  in (result'', result) end;

fun import_export ctxt (_, raw_th) =
  let
    val thy_ctxt = ProofContext.init (ProofContext.theory_of ctxt);
    val result'' = Goal.norm_result raw_th;
    val result = Goal.norm_result (singleton (ProofContext.export ctxt thy_ctxt) result'');
  in (result'', result) end;

fun notes loc kind facts lthy =
  let
    val is_loc = loc <> "";
    val thy = ProofContext.theory_of lthy;

    val facts' = facts
      |> map (fn (a, bs) => (a, PureThy.burrow_fact (PureThy.name_multi (fst a)) bs))
      |> PureThy.map_facts (import_export lthy);   (* FIXME import_export_proof *)
    val local_facts = PureThy.map_facts #1 facts'
      |> Attrib.map_facts (Attrib.attribute_i thy);
    val target_facts = PureThy.map_facts #1 facts'
      |> is_loc ? Element.facts_map (Element.morph_ctxt (LocalTheory.target_morphism lthy));
    val global_facts = PureThy.map_facts #2 facts'
      |> Attrib.map_facts (if is_loc then K I else Attrib.attribute_i thy);
  in
    lthy |> LocalTheory.theory
      (Sign.qualified_names
        #> PureThy.note_thmss_i kind global_facts #> snd
        #> Sign.restore_naming thy)

    |> is_loc ? LocalTheory.target (Locale.add_thmss loc kind target_facts)

    |> ProofContext.set_stmt true
    |> ProofContext.qualified_names
    |> ProofContext.note_thmss_i kind local_facts
    ||> ProofContext.restore_naming lthy
    ||> ProofContext.restore_stmt lthy
  end;


(* target declarations *)

fun target_decl _ "" f =
      LocalTheory.theory (Context.theory_map (f Morphism.identity)) #>
      LocalTheory.target (Context.proof_map (f Morphism.identity))
  | target_decl add loc f =
      LocalTheory.target (add loc (Context.proof_map o f));

val type_syntax = target_decl Locale.add_type_syntax;
val term_syntax = target_decl Locale.add_term_syntax;
val declaration = target_decl Locale.add_declaration;

fun target_morphism loc lthy =
  ProofContext.export_morphism lthy (LocalTheory.target_of lthy) $>
  Morphism.thm_morphism Goal.norm_result;

fun target_name "" lthy = Sign.full_name (ProofContext.theory_of lthy)
  | target_name _ lthy = ProofContext.full_name (LocalTheory.target_of lthy);


(* init and exit *)

fun begin loc =
  Data.put (if loc = "" then NONE else SOME loc) #>
  LocalTheory.init (NameSpace.base loc)
   {pretty = pretty loc,
    consts = consts (loc <> ""),
    axioms = axioms,
    defs = defs,
    notes = notes loc,
    type_syntax = type_syntax loc,
    term_syntax = term_syntax loc,
    declaration = declaration loc,
    target_morphism = target_morphism loc,
    target_name = target_name loc,
    reinit = fn _ => begin loc o (if loc = "" then ProofContext.init else Locale.init loc),
    exit = LocalTheory.target_of};

fun init_i NONE thy = begin "" (ProofContext.init thy)
  | init_i (SOME loc) thy = begin loc (Locale.init loc thy);

fun init (SOME "-") thy = init_i NONE thy
  | init loc thy = init_i (Option.map (Locale.intern thy) loc) thy;

end;
