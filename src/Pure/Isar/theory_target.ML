(*  Title:      Pure/Isar/theory_target.ML
    ID:         $Id$
    Author:     Makarius

Common theory/locale/class targets.
*)

signature THEORY_TARGET =
sig
  val peek: local_theory -> {target: string, is_locale: bool, is_class: bool}
  val begin: string -> Proof.context -> local_theory
  val init: string option -> theory -> local_theory
  val init_cmd: xstring option -> theory -> local_theory
end;

structure TheoryTarget: THEORY_TARGET =
struct

(* context data *)

datatype target = Target of {target: string, is_locale: bool, is_class: bool};

fun make_target target is_locale is_class =
  Target {target = target, is_locale = is_locale, is_class = is_class};

structure Data = ProofDataFun
(
  type T = target;
  fun init _ = make_target "" false false;
);

val peek = (fn Target args => args) o Data.get;


(* pretty *)

fun pretty (Target {target, is_locale, is_class}) ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val target_name = (if is_class then "class " else "locale ") ^ Locale.extern thy target;

    val fixes = map (fn (x, T) => (x, SOME T, NoSyn)) (#1 (ProofContext.inferred_fixes ctxt));
    val assumes = map (fn A => (("", []), [(A, [])])) (map Thm.term_of (Assumption.assms_of ctxt));
    val elems =
      (if null fixes then [] else [Element.Fixes fixes]) @
      (if null assumes then [] else [Element.Assumes assumes]);
  in
    Pretty.block [Pretty.str "theory", Pretty.brk 1, Pretty.str (Context.theory_name thy)] ::
     (if target = "" then []
      else if null elems then [Pretty.str target_name]
      else [Pretty.big_list (target_name ^ " =")
        (map (Pretty.chunks o Element.pretty_ctxt ctxt) elems)])
  end;


(* target declarations *)

fun target_decl add (Target {target, ...}) d lthy =
  let
    val d' = Morphism.transform (LocalTheory.target_morphism lthy) d;
    val d0 = Morphism.form d';
  in
    if target = "" then
      lthy
      |> LocalTheory.theory (Context.theory_map d0)
      |> LocalTheory.target (Context.proof_map d0)
    else
      lthy
      |> LocalTheory.target (add target d')
  end;

val type_syntax = target_decl Locale.add_type_syntax;
val term_syntax = target_decl Locale.add_term_syntax;
val declaration = target_decl Locale.add_declaration;

fun target_naming (Target {target, ...}) lthy =
  (if target = "" then Sign.naming_of (ProofContext.theory_of lthy)
   else ProofContext.naming_of (LocalTheory.target_of lthy))
  |> NameSpace.qualified_names;



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
      |> fold PureThy.tag_rule (ContextPosition.properties_of ctxt)
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

fun notes (Target {target, is_locale, ...}) kind facts lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val full = LocalTheory.full_name lthy;

    val facts' = facts
      |> map (fn (a, bs) => (a, PureThy.burrow_fact (PureThy.name_multi (full (fst a))) bs))
      |> PureThy.map_facts (import_export_proof lthy);
    val local_facts = PureThy.map_facts #1 facts'
      |> Attrib.map_facts (Attrib.attribute_i thy);
    val target_facts = PureThy.map_facts #1 facts'
      |> is_locale ? Element.facts_map (Element.morph_ctxt (LocalTheory.target_morphism lthy));
    val global_facts = PureThy.map_facts #2 facts'
      |> Attrib.map_facts (if is_locale then K I else Attrib.attribute_i thy);
  in
    lthy |> LocalTheory.theory
      (Sign.qualified_names
        #> PureThy.note_thmss_i kind global_facts #> snd
        #> Sign.restore_naming thy)

    |> is_locale ? LocalTheory.target (Locale.add_thmss target kind target_facts)

    |> ProofContext.qualified_names
    |> ProofContext.note_thmss_i kind local_facts
    ||> ProofContext.restore_naming lthy
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
        (Sign.add_abbrev Syntax.internalM [] arg')
        (ProofContext.add_abbrev Syntax.internalM [] arg')
      #-> (fn (lhs, _) =>
        Type.similar_types (rhs, rhs') ?
          Morphism.form (ProofContext.target_notation true prmode [(lhs, mx)])))
  end;

fun internal_abbrev ta prmode ((c, mx), t) lthy = lthy
  (* FIXME really permissive *)
  |> term_syntax ta (perhaps o try o target_abbrev prmode ((c, mx), t))
  |> ProofContext.add_abbrev Syntax.internalM (ContextPosition.properties_of lthy) (c, t)
  |> snd;

fun declare_consts (ta as Target {target, is_locale, is_class}) depends decls lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val xs = filter depends (#1 (ProofContext.inferred_fixes (LocalTheory.target_of lthy)));

    fun const ((c, T), mx) thy =
      let
        val U = map #2 xs ---> T;
        val (mx1, mx2) = Class.fork_mixfix is_locale is_class mx;
        val mx3 = if is_locale then NoSyn else mx1;
        val (const, thy') = Sign.declare_const (ContextPosition.properties_of lthy) (c, U, mx3) thy;
        val t = Term.list_comb (const, map Free xs);
      in (((c, mx2), t), thy') end;
    fun const_class ((c, _), mx) (_, t) =
      LocalTheory.raw_theory_result (Class.add_const_in_class target ((c, mx), t))
      #-> Class.remove_constraint target;

    val (abbrs, lthy') = lthy
      |> LocalTheory.theory_result (fold_map const decls)
  in
    lthy'
    |> is_class ? fold2 const_class decls abbrs
    |> is_locale ? fold (internal_abbrev ta Syntax.mode_default) abbrs
    |> fold_map (apfst (apsnd snd) oo LocalDefs.add_def) abbrs
  end;


(* abbrev *)

fun abbrev (ta as Target {target, is_locale, is_class}) prmode ((raw_c, mx), raw_t) lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val thy_ctxt = ProofContext.init thy;
    val target_ctxt = LocalTheory.target_of lthy;
    val target_morphism = LocalTheory.target_morphism lthy;

    val c = Morphism.name target_morphism raw_c;
    val t = Morphism.term target_morphism raw_t;
    val xs = map Free (Variable.add_fixed target_ctxt t []);
    val u = fold_rev lambda xs t;
    val U = Term.fastype_of u;

    val u' = singleton (Variable.export_terms (Variable.declare_term u target_ctxt) thy_ctxt) u;
    val (mx1, mx2) = Class.fork_mixfix is_locale is_class mx;
    val mx3 = if is_locale then NoSyn else mx1;
    fun add_abbrev_in_class abbr =
      LocalTheory.raw_theory_result (Class.add_abbrev_in_class target prmode abbr)
      #-> Class.remove_constraint target;
  in
    lthy
    |> LocalTheory.theory_result
        (Sign.add_abbrev (#1 prmode) (ContextPosition.properties_of lthy) (c, u'))
    |-> (fn (lhs, rhs) =>
          LocalTheory.theory (Sign.notation true prmode [(lhs, mx3)])
          #> is_locale ? internal_abbrev ta prmode ((c, mx2), Term.list_comb (lhs, xs))
          #> is_class ? add_abbrev_in_class ((c, mx1), Term.list_comb (lhs, xs)))
    |> LocalDefs.add_def ((c, NoSyn), raw_t)
  end;


(* define *)

fun define (ta as Target {target, is_locale, is_class})
    kind ((c, mx), ((name, atts), rhs)) lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val thy_ctxt = ProofContext.init thy;

    val name' = Thm.def_name_optional c name;
    val (rhs', rhs_conv) =
      LocalDefs.export_cterm lthy thy_ctxt (Thm.cterm_of thy rhs) |>> Thm.term_of;
    val xs = Variable.add_fixed (LocalTheory.target_of lthy) rhs' [];
    val T = Term.fastype_of rhs;

    (*consts*)
    val ([(lhs, local_def)], lthy2) = lthy
      |> declare_consts ta (member (op =) xs) [((c, T), mx)];
    val (_, lhs') = Logic.dest_equals (Thm.prop_of local_def);

    (*def*)
    val (global_def, lthy3) = lthy2
      |> LocalTheory.theory_result (Thm.add_def false (name', Logic.mk_equals (lhs', rhs')));
    val def = LocalDefs.trans_terms lthy3
      [(*c == global.c xs*)     local_def,
       (*global.c xs == rhs'*)  global_def,
       (*rhs' == rhs*)          Thm.symmetric rhs_conv];

    (*notes*)
    val ([(res_name, [res])], lthy4) = lthy3
      |> notes ta kind [((name', atts), [([def], [])])];
  in ((lhs, (res_name, res)), lthy4) end;


(* axioms *)

fun axioms ta kind (vars, specs) lthy =
  let
    val thy_ctxt = ProofContext.init (ProofContext.theory_of lthy);
    val expanded_props = map (Assumption.export_term lthy thy_ctxt) (maps snd specs);
    val xs = fold Term.add_frees expanded_props [];

    (*consts*)
    val (consts, lthy') = declare_consts ta (member (op =) xs) vars lthy;
    val global_consts = map (Term.dest_Const o Term.head_of o Thm.term_of o Thm.rhs_of o #2) consts;

    (*axioms*)
    val hyps = map Thm.term_of (Assumption.assms_of lthy');
    fun axiom ((name, atts), props) thy = thy
      |> fold_map (Thm.add_axiom hyps) (PureThy.name_multi name props)
      |-> (fn ths => pair ((name, atts), [(ths, [])]));
  in
    lthy'
    |> fold Variable.declare_term expanded_props
    |> LocalTheory.theory (fold (fn c => Theory.add_deps "" c []) global_consts)
    |> LocalTheory.theory_result (fold_map axiom specs)
    |-> notes ta kind
    |>> pair (map #1 consts)
  end;


(* init and exit *)

fun begin target ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val is_locale = target <> "";
    val is_class = Class.is_class thy target;
    val ta = Target {target = target, is_locale = is_locale, is_class = is_class};
  in
    ctxt
    |> Data.put ta
    |> is_class ? Class.init target
    |> LocalTheory.init (NameSpace.base target)
     {pretty = pretty ta,
      axioms = axioms ta,
      abbrev = abbrev ta,
      define = define ta,
      notes = notes ta,
      type_syntax = type_syntax ta,
      term_syntax = term_syntax ta,
      declaration = declaration ta,
      target_naming = target_naming ta,
      reinit = fn _ =>
        begin target o (if is_locale then Locale.init target else ProofContext.init),
      exit = LocalTheory.target_of}
  end;

fun init NONE thy = begin "" (ProofContext.init thy)
  | init (SOME target) thy = begin target (Locale.init target thy);

fun init_cmd (SOME "-") thy = init NONE thy
  | init_cmd target thy = init (Option.map (Locale.intern thy) target) thy;

end;
