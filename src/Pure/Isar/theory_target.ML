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
  type T = string option;
  fun init _ = NONE;
);

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

fun target_abbrev prmode ((c, mx), rhs) phi =
  let
    val c' = Morphism.name phi c;
    val rhs' = Morphism.term phi rhs;
    val arg' = (c', rhs');
    val eq_heads =
      (case pairself Term.head_of (rhs, rhs') of
        (Const (a, _), Const (a', _)) => a = a'
      | _ => false);
  in
    eq_heads ? (Context.mapping_result
      (Sign.add_abbrev Syntax.internalM arg') (ProofContext.add_abbrev Syntax.internalM arg')
    #-> (fn (lhs, _) =>
      Term.equiv_types (rhs, rhs') ?
        Morphism.form (ProofContext.target_notation prmode [(lhs, mx)])))
  end;

fun internal_abbrev prmode ((c, mx), t) =
  (* FIXME really permissive *)
  LocalTheory.term_syntax (perhaps o try o target_abbrev prmode ((c, mx), t))
  #> ProofContext.add_abbrev Syntax.internalM (c, t) #> snd;

fun consts is_loc some_class depends decls lthy =
  let
    val xs = filter depends (#1 (ProofContext.inferred_fixes (LocalTheory.target_of lthy)));

    fun const ((c, T), mx) thy =
      let
        val U = map #2 xs ---> T;
        val t = Term.list_comb (Const (Sign.full_name thy c, U), map Free xs);
        val (mx1, mx2) = Class.fork_mixfix is_loc some_class mx;
        val thy' = Sign.add_consts_authentic [(c, U, mx1)] thy;
      in (((c, mx2), t), thy') end;

    fun const_class (SOME class) ((c, _), mx) (_, t) =
          Class.add_const_in_class class ((c, t), mx)
      | const_class NONE _ _ = I;

    val (abbrs, lthy') = lthy
      |> LocalTheory.theory_result (fold_map const decls)
    val defs = map (apsnd (pair ("", []))) abbrs;
  in
    lthy'
    |> is_loc ? fold (internal_abbrev Syntax.default_mode) abbrs
    |> LocalTheory.raw_theory (fold2 (const_class some_class) decls abbrs)
    |> LocalDefs.add_defs defs
    |>> map (apsnd snd)
  end;


(* abbrev *)

fun occ_params ctxt ts =
  #1 (ProofContext.inferred_fixes ctxt)
  |> filter (member (op =) (fold (Variable.add_fixed ctxt) ts []));

fun local_abbrev (x, rhs) =
  Variable.add_fixes [x] #-> (fn [x'] =>
    let
      val T = Term.fastype_of rhs;
      val lhs = Free (x', T);
    in
      Variable.declare_term lhs #>
      Variable.declare_term rhs #>
      Assumption.add_assms (K (K (I, Envir.expand_term_frees [((x', T), rhs)]))) [] #> snd #>
      pair (lhs, rhs)
    end);

fun abbrev is_loc some_class prmode ((raw_c, mx), raw_t) lthy =
  let
    val thy_ctxt = ProofContext.init (ProofContext.theory_of lthy);
    val target = LocalTheory.target_of lthy;
    val target_morphism = LocalTheory.target_morphism lthy;

    val c = Morphism.name target_morphism raw_c;
    val t = Morphism.term target_morphism raw_t;
    val xs = map Free (occ_params target [t]);
    val u = fold_rev Term.lambda xs t;
    val U = Term.fastype_of u;
    val u' = singleton (Variable.export_terms (Variable.declare_term u target) thy_ctxt) u;

    val ((lhs as Const (full_c, _), rhs), lthy1) = lthy
      |> LocalTheory.theory_result (Sign.add_abbrev (#1 prmode) (c, u'));
    val (mx1, mx2) = Class.fork_mixfix is_loc some_class mx;
  in
    lthy1
    |> LocalTheory.theory (Sign.add_notation prmode [(lhs, mx1)])
    |> is_loc ? internal_abbrev prmode ((c, mx2), Term.list_comb (Const (full_c, U), xs))
    |> local_abbrev (c, rhs)
  end;


(* defs *)

local

fun expand_term ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val thy_ctxt = ProofContext.init thy;
    val ct = Thm.cterm_of thy t;
    val (defs, ct') = LocalDefs.export ctxt thy_ctxt (Drule.mk_term ct) ||> Drule.dest_term;
  in (Thm.term_of ct', MetaSimplifier.rewrite true defs ct) end;

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
        val T = Term.fastype_of rhs;

        val ([(lhs, lhs_def)], lthy2) = lthy1
          |> LocalTheory.consts (member (op =) xs) [((c, T), mx)];
        val lhs' = #2 (Logic.dest_equals (Thm.prop_of lhs_def));

        val name' = Thm.def_name_optional c name;
        val (def, lthy3) = lthy2
          |> LocalTheory.theory_result (add_def (name', Logic.mk_equals (lhs', rhs')));
        val eq = LocalDefs.trans_terms lthy3
          [(*c == loc.c xs*) lhs_def,
           (*lhs' == rhs'*)  def,
           (*rhs' == rhs*)   Thm.symmetric rhs_conv];
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
    val concl_conv = MetaSimplifier.rewrite true defs (Thm.cprop_of th);
    val assms = map (MetaSimplifier.rewrite_rule defs o Thm.assume) (Assumption.assms_of ctxt);
    val nprems = Thm.nprems_of th' - Thm.nprems_of th;

    (*export fixes*)
    val tfrees = map TFree (Thm.fold_terms Term.add_tfrees th' []);
    val frees = map Free (Thm.fold_terms Term.add_frees th' []);
    val (th'' :: vs) = (th' :: map (Drule.mk_term o cert) (map Logic.mk_type tfrees @ frees))
      |> Variable.export ctxt thy_ctxt
      |> Drule.zero_var_indexes_list;

    (*thm definition*)
    val result = th''
      |> PureThy.name_thm true true ""
      |> Goal.close_result
      |> PureThy.name_thm true true name;

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
      | SOME res => LocalDefs.trans_props ctxt [res, Thm.symmetric concl_conv])
      |> Goal.norm_result
      |> PureThy.name_thm false false name;

  in (result'', result) end;

fun notes loc kind facts lthy =
  let
    val is_loc = loc <> "";
    val thy = ProofContext.theory_of lthy;
    val full = LocalTheory.full_name lthy;

    val facts' = facts
      |> map (fn (a, bs) => (a, PureThy.burrow_fact (PureThy.name_multi (full (fst a))) bs))
      |> PureThy.map_facts (import_export_proof lthy);
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

fun target_decl add loc d lthy =
  let
    val d' = Morphism.transform (LocalTheory.target_morphism lthy) d;
    val d0 = Morphism.form d';
  in
    if loc = "" then
      lthy
      |> LocalTheory.theory (Context.theory_map d0)
      |> LocalTheory.target (Context.proof_map d0)
    else
      lthy
      |> LocalTheory.target (add loc d')
  end;

val type_syntax = target_decl Locale.add_type_syntax;
val term_syntax = target_decl Locale.add_term_syntax;
val declaration = target_decl Locale.add_declaration;

fun target_morphism loc lthy =
  ProofContext.export_morphism lthy (LocalTheory.target_of lthy) $>
  Morphism.thm_morphism Goal.norm_result;

fun target_naming loc lthy =
  (if loc = "" then Sign.naming_of (ProofContext.theory_of lthy)
   else ProofContext.naming_of (LocalTheory.target_of lthy))
  |> NameSpace.qualified_names;


(* init and exit *)

fun begin loc ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val is_loc = loc <> "";
    val some_class = Class.class_of_locale thy loc;
  in
    ctxt
    |> Data.put (if is_loc then SOME loc else NONE)
    |> LocalTheory.init (NameSpace.base loc)
     {pretty = pretty loc,
      consts = consts is_loc some_class,
      axioms = axioms,
      abbrev = abbrev is_loc some_class,
      defs = defs,
      notes = notes loc,
      type_syntax = type_syntax loc,
      term_syntax = term_syntax loc,
      declaration = declaration loc,
      target_morphism = target_morphism loc,
      target_naming = target_naming loc,
      reinit = fn _ =>
        begin loc o (if is_loc then Locale.init loc else ProofContext.init),
      exit = LocalTheory.target_of}
  end;

fun init_i NONE thy = begin "" (ProofContext.init thy)
  | init_i (SOME loc) thy = begin loc (Locale.init loc thy);

fun init (SOME "-") thy = init_i NONE thy
  | init loc thy = init_i (Option.map (Locale.intern thy) loc) thy;

end;
