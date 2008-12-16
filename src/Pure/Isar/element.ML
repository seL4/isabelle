(*  Title:      Pure/Isar/element.ML
    Author:     Makarius

Explicit data structures for some Isar language elements, with derived
logical operations.
*)

signature ELEMENT =
sig
  datatype ('typ, 'term) stmt =
    Shows of (Attrib.binding * ('term * 'term list) list) list |
    Obtains of (Binding.T * ((Binding.T * 'typ option) list * 'term list)) list
  type statement = (string, string) stmt
  type statement_i = (typ, term) stmt
  datatype ('typ, 'term, 'fact) ctxt =
    Fixes of (Binding.T * 'typ option * mixfix) list |
    Constrains of (string * 'typ) list |
    Assumes of (Attrib.binding * ('term * 'term list) list) list |
    Defines of (Attrib.binding * ('term * 'term list)) list |
    Notes of string * (Attrib.binding * ('fact * Attrib.src list) list) list
  type context = (string, string, Facts.ref) ctxt
  type context_i = (typ, term, thm list) ctxt
  val facts_map: (('typ, 'term, 'fact) ctxt -> ('a, 'b, 'c) ctxt) ->
   (Attrib.binding * ('fact * Attrib.src list) list) list ->
   (Attrib.binding * ('c * Attrib.src list) list) list
  val map_ctxt': {binding: Binding.T -> Binding.T,
    var: Binding.T * mixfix -> Binding.T * mixfix,
    typ: 'typ -> 'a, term: 'term -> 'b, pat: 'term -> 'b, fact: 'fact -> 'c,
    attrib: Attrib.src -> Attrib.src} -> ('typ, 'term, 'fact) ctxt -> ('a, 'b, 'c) ctxt
  val map_ctxt: {binding: Binding.T -> Binding.T,
    var: Binding.T * mixfix -> Binding.T * mixfix,
    typ: 'typ -> 'a, term: 'term -> 'b, fact: 'fact -> 'c,
    attrib: Attrib.src -> Attrib.src} -> ('typ, 'term, 'fact) ctxt -> ('a, 'b, 'c) ctxt
  val map_ctxt_attrib: (Attrib.src -> Attrib.src) ->
    ('typ, 'term, 'fact) ctxt -> ('typ, 'term, 'fact) ctxt
  val morph_ctxt: morphism -> context_i -> context_i
  val params_of: context_i -> (string * typ) list
  val prems_of: context_i -> term list
  val facts_of: theory -> context_i -> (Attrib.binding * (thm list * Attrib.src list) list) list
  val pretty_stmt: Proof.context -> statement_i -> Pretty.T list
  val pretty_ctxt: Proof.context -> context_i -> Pretty.T list
  val pretty_statement: Proof.context -> string -> thm -> Pretty.T
  type witness
  val map_witness: (term * thm -> term * thm) -> witness -> witness
  val morph_witness: morphism -> witness -> witness
  val witness_prop: witness -> term
  val witness_hyps: witness -> term list
  val assume_witness: theory -> term -> witness
  val prove_witness: Proof.context -> term -> tactic -> witness
  val close_witness: witness -> witness
  val conclude_witness: witness -> thm
  val mark_witness: term -> term
  val make_witness: term -> thm -> witness
  val dest_witness: witness -> term * thm
  val transfer_witness: theory -> witness -> witness
  val refine_witness: Proof.state -> Proof.state Seq.seq
  val pretty_witness: Proof.context -> witness -> Pretty.T
  val rename: (string * (string * mixfix option)) list -> string -> string
  val rename_var_name: (string * (string * mixfix option)) list ->
    string * mixfix -> string * mixfix
  val rename_var: (string * (string * mixfix option)) list ->
    Binding.T * mixfix -> Binding.T * mixfix
  val rename_term: (string * (string * mixfix option)) list -> term -> term
  val rename_thm: (string * (string * mixfix option)) list -> thm -> thm
  val rename_morphism: (string * (string * mixfix option)) list -> morphism
  val instT_type: typ Symtab.table -> typ -> typ
  val instT_term: typ Symtab.table -> term -> term
  val instT_thm: theory -> typ Symtab.table -> thm -> thm
  val instT_morphism: theory -> typ Symtab.table -> morphism
  val inst_term: typ Symtab.table * term Symtab.table -> term -> term
  val inst_thm: theory -> typ Symtab.table * term Symtab.table -> thm -> thm
  val inst_morphism: theory -> typ Symtab.table * term Symtab.table -> morphism
  val satisfy_thm: witness list -> thm -> thm
  val satisfy_morphism: witness list -> morphism
  val satisfy_facts: witness list ->
    (Attrib.binding * (thm list * Attrib.src list) list) list ->
    (Attrib.binding * (thm list * Attrib.src list) list) list
  val generalize_facts: Proof.context -> Proof.context ->
    (Attrib.binding * (thm list * Attrib.src list) list) list ->
    (Attrib.binding * (thm list * Attrib.src list) list) list
  val activate: (typ, term, Facts.ref) ctxt list -> Proof.context ->
    (context_i list * (Binding.T * Thm.thm list) list) * Proof.context
  val activate_i: context_i list -> Proof.context ->
    (context_i list * (Binding.T * Thm.thm list) list) * Proof.context
end;

structure Element: ELEMENT =
struct

(** language elements **)

(* statement *)

datatype ('typ, 'term) stmt =
  Shows of (Attrib.binding * ('term * 'term list) list) list |
  Obtains of (Binding.T * ((Binding.T * 'typ option) list * 'term list)) list;

type statement = (string, string) stmt;
type statement_i = (typ, term) stmt;


(* context *)

datatype ('typ, 'term, 'fact) ctxt =
  Fixes of (Binding.T * 'typ option * mixfix) list |
  Constrains of (string * 'typ) list |
  Assumes of (Attrib.binding * ('term * 'term list) list) list |
  Defines of (Attrib.binding * ('term * 'term list)) list |
  Notes of string * (Attrib.binding * ('fact * Attrib.src list) list) list;

type context = (string, string, Facts.ref) ctxt;
type context_i = (typ, term, thm list) ctxt;

fun facts_map f facts = Notes ("", facts) |> f |> (fn Notes (_, facts') => facts');

fun map_ctxt' {binding, var, typ, term, pat, fact, attrib} =
  fn Fixes fixes => Fixes (fixes |> map (fn (x, T, mx) =>
       let val (x', mx') = var (x, mx) in (x', Option.map typ T, mx') end))
   | Constrains xs => Constrains (xs |> map (fn (x, T) =>
       let val x' = Binding.base_name (#1 (var (Binding.name x, NoSyn))) in (x', typ T) end))
   | Assumes asms => Assumes (asms |> map (fn ((a, atts), propps) =>
      ((binding a, map attrib atts), propps |> map (fn (t, ps) => (term t, map pat ps)))))
   | Defines defs => Defines (defs |> map (fn ((a, atts), (t, ps)) =>
      ((binding a, map attrib atts), (term t, map pat ps))))
   | Notes (kind, facts) => Notes (kind, facts |> map (fn ((a, atts), bs) =>
      ((binding a, map attrib atts), bs |> map (fn (ths, btts) => (fact ths, map attrib btts)))));

fun map_ctxt {binding, var, typ, term, fact, attrib} =
  map_ctxt' {binding = binding, var = var, typ = typ, term = term, pat = term,
    fact = fact, attrib = attrib}

fun map_ctxt_attrib attrib =
  map_ctxt {binding = I, var = I, typ = I, term = I, fact = I, attrib = attrib};

fun morph_ctxt phi = map_ctxt
 {binding = Morphism.binding phi,
  var = Morphism.var phi,
  typ = Morphism.typ phi,
  term = Morphism.term phi,
  fact = Morphism.fact phi,
  attrib = Args.morph_values phi};


(* logical content *)

fun params_of (Fixes fixes) = fixes |> map
    (fn (x, SOME T, _) => (Binding.base_name x, T)
      | (x, _, _) => raise TERM ("Untyped context element parameter " ^ quote (Binding.display x), []))
  | params_of _ = [];

fun prems_of (Assumes asms) = maps (map fst o snd) asms
  | prems_of (Defines defs) = map (fst o snd) defs
  | prems_of _ = [];

fun assume thy t = Assumption.assume (Thm.cterm_of thy t);

fun facts_of thy (Assumes asms) = map (apsnd (map (fn (t, _) => ([assume thy t], [])))) asms
  | facts_of thy (Defines defs) = map (apsnd (fn (t, _) => [([assume thy t], [])])) defs
  | facts_of _ (Notes (_, facts)) = facts
  | facts_of _ _ = [];



(** pretty printing **)

fun pretty_items _ _ [] = []
  | pretty_items keyword sep (x :: ys) =
      Pretty.block [Pretty.keyword keyword, Pretty.brk 1, x] ::
        map (fn y => Pretty.block [Pretty.str "  ", Pretty.keyword sep, Pretty.brk 1, y]) ys;

fun pretty_name_atts ctxt (b, atts) sep =
  let
    val name = Binding.display b;
  in if name = "" andalso null atts then []
    else [Pretty.block
      (Pretty.breaks (Pretty.str name :: Attrib.pretty_attribs ctxt atts @ [Pretty.str sep]))]
  end;


(* pretty_stmt *)

fun pretty_stmt ctxt =
  let
    val prt_typ = Pretty.quote o Syntax.pretty_typ ctxt;
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    val prt_terms = separate (Pretty.keyword "and") o map prt_term;
    val prt_name_atts = pretty_name_atts ctxt;

    fun prt_show (a, ts) =
      Pretty.block (Pretty.breaks (prt_name_atts a ":" @ prt_terms (map fst ts)));

    fun prt_var (x, SOME T) = Pretty.block
          [Pretty.str (Binding.base_name x ^ " ::"), Pretty.brk 1, prt_typ T]
      | prt_var (x, NONE) = Pretty.str (Binding.base_name x);
    val prt_vars = separate (Pretty.keyword "and") o map prt_var;

    fun prt_obtain (_, ([], ts)) = Pretty.block (Pretty.breaks (prt_terms ts))
      | prt_obtain (_, (xs, ts)) = Pretty.block (Pretty.breaks
          (prt_vars xs @ [Pretty.keyword "where"] @ prt_terms ts));
  in
    fn Shows shows => pretty_items "shows" "and" (map prt_show shows)
     | Obtains obtains => pretty_items "obtains" "|" (map prt_obtain obtains)
  end;


(* pretty_ctxt *)

fun pretty_ctxt ctxt =
  let
    val prt_typ = Pretty.quote o Syntax.pretty_typ ctxt;
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    val prt_thm = Pretty.backquote o ProofContext.pretty_thm ctxt;
    val prt_name_atts = pretty_name_atts ctxt;

    fun prt_mixfix NoSyn = []
      | prt_mixfix mx = [Pretty.brk 2, Syntax.pretty_mixfix mx];

    fun prt_fix (x, SOME T, mx) = Pretty.block (Pretty.str (Binding.base_name x ^ " ::") ::
          Pretty.brk 1 :: prt_typ T :: Pretty.brk 1 :: prt_mixfix mx)
      | prt_fix (x, NONE, mx) = Pretty.block (Pretty.str (Binding.base_name x) ::
          Pretty.brk 1 :: prt_mixfix mx);
    fun prt_constrain (x, T) = prt_fix (Binding.name x, SOME T, NoSyn);

    fun prt_asm (a, ts) =
      Pretty.block (Pretty.breaks (prt_name_atts a ":" @ map (prt_term o fst) ts));
    fun prt_def (a, (t, _)) =
      Pretty.block (Pretty.breaks (prt_name_atts a ":" @ [prt_term t]));

    fun prt_fact (ths, []) = map prt_thm ths
      | prt_fact (ths, atts) = Pretty.enclose "(" ")"
          (Pretty.breaks (map prt_thm ths)) :: Attrib.pretty_attribs ctxt atts;
    fun prt_note (a, ths) =
      Pretty.block (Pretty.breaks (flat (prt_name_atts a "=" :: map prt_fact ths)));
  in
    fn Fixes fixes => pretty_items "fixes" "and" (map prt_fix fixes)
     | Constrains xs => pretty_items "constrains" "and" (map prt_constrain xs)
     | Assumes asms => pretty_items "assumes" "and" (map prt_asm asms)
     | Defines defs => pretty_items "defines" "and" (map prt_def defs)
     | Notes ("", facts) => pretty_items "notes" "and" (map prt_note facts)
     | Notes (kind, facts) => pretty_items ("notes " ^ kind) "and" (map prt_note facts)
  end;


(* pretty_statement *)

local

fun thm_name kind th prts =
  let val head =
    if Thm.has_name_hint th then
      Pretty.block [Pretty.command kind,
        Pretty.brk 1, Pretty.str (Sign.base_name (Thm.get_name_hint th) ^ ":")]
    else Pretty.command kind
  in Pretty.block (Pretty.fbreaks (head :: prts)) end;

fun fix (x, T) = (Binding.name x, SOME T);

fun obtain prop ctxt =
  let
    val ((xs, prop'), ctxt') = Variable.focus prop ctxt;
    val As = Logic.strip_imp_prems (Thm.term_of prop');
  in ((Binding.empty, (map (fix o Term.dest_Free o Thm.term_of) xs, As)), ctxt') end;

in

fun pretty_statement ctxt kind raw_th =
  let
    val thy = ProofContext.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val th = MetaSimplifier.norm_hhf raw_th;
    val is_elim = ObjectLogic.is_elim th;

    val ((_, [th']), ctxt') = Variable.import_thms true [th] (Variable.set_body false ctxt);
    val prop = Thm.prop_of th';
    val (prems, concl) = Logic.strip_horn prop;
    val concl_term = ObjectLogic.drop_judgment thy concl;

    val fixes = fold_aterms (fn v as Free (x, T) =>
        if Variable.newly_fixed ctxt' ctxt x andalso not (v aconv concl_term)
        then insert (op =) (x, T) else I | _ => I) prop [] |> rev;
    val (assumes, cases) = take_suffix (fn prem =>
      is_elim andalso concl aconv Logic.strip_assums_concl prem) prems;
  in
    pretty_ctxt ctxt' (Fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) fixes)) @
    pretty_ctxt ctxt' (Assumes (map (fn t => (Attrib.empty_binding, [(t, [])])) assumes)) @
     (if null cases then pretty_stmt ctxt' (Shows [(Attrib.empty_binding, [(concl, [])])])
      else
        let val (clauses, ctxt'') = fold_map (obtain o cert) cases ctxt'
        in pretty_stmt ctxt'' (Obtains clauses) end)
  end |> thm_name kind raw_th;

end;



(** logical operations **)

(* witnesses -- hypotheses as protected facts *)

datatype witness = Witness of term * thm;

fun map_witness f (Witness witn) = Witness (f witn);

fun morph_witness phi = map_witness (fn (t, th) => (Morphism.term phi t, Morphism.thm phi th));

fun witness_prop (Witness (t, _)) = t;
fun witness_hyps (Witness (_, th)) = #hyps (Thm.rep_thm th);

fun assume_witness thy t =
  Witness (t, Goal.protect (Thm.assume (Thm.cterm_of thy t)));

fun prove_witness ctxt t tac =
  Witness (t, Thm.close_derivation (Goal.prove ctxt [] [] (Logic.protect t) (fn _ =>
    Tactic.rtac Drule.protectI 1 THEN tac)));

val close_witness = map_witness (fn (t, th) => (t, Thm.close_derivation th));

fun conclude_witness (Witness (_, th)) =
  Thm.close_derivation (MetaSimplifier.norm_hhf_protect (Goal.conclude th));

fun compose_witness (Witness (_, th)) r =
  let
    val th' = Goal.conclude th;
    val A = Thm.cprem_of r 1;
  in
    Thm.implies_elim
      (Conv.gconv_rule Drule.beta_eta_conversion 1 r)
      (Conv.fconv_rule Drule.beta_eta_conversion
        (Thm.instantiate (Thm.match (Thm.cprop_of th', A)) th'))
  end;

val mark_witness = Logic.protect;

fun make_witness t th = Witness (t, th);
fun dest_witness (Witness w) = w;

fun transfer_witness thy (Witness (t, th)) = Witness (t, Thm.transfer thy th);

val refine_witness =
  Proof.refine (Method.Basic (K (Method.RAW_METHOD
    (K (ALLGOALS
      (CONJUNCTS (ALLGOALS
        (CONJUNCTS (TRYALL (Tactic.rtac Drule.protectI)))))))), Position.none));

fun pretty_witness ctxt witn =
  let val prt_term = Pretty.quote o Syntax.pretty_term ctxt in
    Pretty.block (prt_term (witness_prop witn) ::
      (if ! show_hyps then [Pretty.brk 2, Pretty.list "[" "]"
         (map prt_term (witness_hyps witn))] else []))
  end;


(* derived rules *)

fun instantiate_tfrees thy subst th =
  let
    val certT = Thm.ctyp_of thy;
    val idx = Thm.maxidx_of th + 1;
    fun cert_inst (a, (S, T)) = (certT (TVar ((a, idx), S)), certT T);

    fun add_inst (a, S) insts =
      if AList.defined (op =) insts a then insts
      else (case AList.lookup (op =) subst a of NONE => insts | SOME T => (a, (S, T)) :: insts);
    val insts =
      Term.fold_types (Term.fold_atyps (fn TFree v => add_inst v | _ => I))
        (Thm.full_prop_of th) [];
  in
    th
    |> Thm.generalize (map fst insts, []) idx
    |> Thm.instantiate (map cert_inst insts, [])
  end;

fun instantiate_frees thy subst =
  let val cert = Thm.cterm_of thy in
    Drule.forall_intr_list (map (cert o Free o fst) subst) #>
    Drule.forall_elim_list (map (cert o snd) subst)
  end;

fun hyps_rule rule th =
  let val {hyps, ...} = Thm.crep_thm th in
    Drule.implies_elim_list
      (rule (Drule.implies_intr_list hyps th))
      (map (Thm.assume o Drule.cterm_rule rule) hyps)
  end;


(* rename *)

fun rename ren x =
  (case AList.lookup (op =) ren (x: string) of
    NONE => x
  | SOME (x', _) => x');

fun rename_var_name ren (x, mx) =
  (case (AList.lookup (op =) ren x, mx) of
    (NONE, _) => (x, mx)
  | (SOME (x', NONE), Structure) => (x', mx)
  | (SOME (x', SOME _), Structure) =>
      error ("Attempt to change syntax of structure parameter " ^ quote x)
  | (SOME (x', NONE), _) => (x', NoSyn)
  | (SOME (x', SOME mx'), _) => (x', mx'));

fun rename_var ren (b, mx) =
  let
    val x = Binding.base_name b;
    val (x', mx') = rename_var_name ren (x, mx);
  in (Binding.name x', mx') end;

fun rename_term ren (Free (x, T)) = Free (rename ren x, T)
  | rename_term ren (t $ u) = rename_term ren t $ rename_term ren u
  | rename_term ren (Abs (x, T, t)) = Abs (x, T, rename_term ren t)
  | rename_term _ a = a;

fun rename_thm ren th =
  let
    val thy = Thm.theory_of_thm th;
    val subst = (Thm.fold_terms o Term.fold_aterms)
      (fn Free (x, T) =>
        let val x' = rename ren x
        in if x = x' then I else insert (eq_fst (op =)) ((x, T), Free (x', T)) end
      | _ => I) th [];
  in
    if null subst then th
    else th |> hyps_rule (instantiate_frees thy subst)
  end;

fun rename_morphism ren = Morphism.morphism
  {binding = I, var = rename_var ren, typ = I, term = rename_term ren, fact = map (rename_thm ren)};


(* instantiate types *)

fun instT_type env =
  if Symtab.is_empty env then I
  else Term.map_type_tfree (fn (x, S) => the_default (TFree (x, S)) (Symtab.lookup env x));

fun instT_term env =
  if Symtab.is_empty env then I
  else Term.map_types (instT_type env);

fun instT_subst env th = (Thm.fold_terms o Term.fold_types o Term.fold_atyps)
  (fn T as TFree (a, _) =>
    let val T' = the_default T (Symtab.lookup env a)
    in if T = T' then I else insert (op =) (a, T') end
  | _ => I) th [];

fun instT_thm thy env th =
  if Symtab.is_empty env then th
  else
    let val subst = instT_subst env th
    in if null subst then th else th |> hyps_rule (instantiate_tfrees thy subst) end;

fun instT_morphism thy env =
  let val thy_ref = Theory.check_thy thy in
    Morphism.morphism
     {binding = I, var = I,
      typ = instT_type env,
      term = instT_term env,
      fact = map (fn th => instT_thm (Theory.deref thy_ref) env th)}
  end;


(* instantiate types and terms *)

fun inst_term (envT, env) =
  if Symtab.is_empty env then instT_term envT
  else
    let
      val instT = instT_type envT;
      fun inst (Const (x, T)) = Const (x, instT T)
        | inst (Free (x, T)) =
            (case Symtab.lookup env x of
              NONE => Free (x, instT T)
            | SOME t => t)
        | inst (Var (xi, T)) = Var (xi, instT T)
        | inst (b as Bound _) = b
        | inst (Abs (x, T, t)) = Abs (x, instT T, inst t)
        | inst (t $ u) = inst t $ inst u;
    in Envir.beta_norm o inst end;

fun inst_thm thy (envT, env) th =
  if Symtab.is_empty env then instT_thm thy envT th
  else
    let
      val substT = instT_subst envT th;
      val subst = (Thm.fold_terms o Term.fold_aterms)
       (fn Free (x, T) =>
          let
            val T' = instT_type envT T;
            val t = Free (x, T');
            val t' = the_default t (Symtab.lookup env x);
          in if t aconv t' then I else insert (eq_fst (op =)) ((x, T'), t') end
       | _ => I) th [];
    in
      if null substT andalso null subst then th
      else th |> hyps_rule
       (instantiate_tfrees thy substT #>
        instantiate_frees thy subst #>
        Conv.fconv_rule (Thm.beta_conversion true))
    end;

fun inst_morphism thy envs =
  let val thy_ref = Theory.check_thy thy in
    Morphism.morphism
     {binding = I, var = I,
      typ = instT_type (#1 envs),
      term = inst_term envs,
      fact = map (fn th => inst_thm (Theory.deref thy_ref) envs th)}
  end;


(* satisfy hypotheses *)

fun satisfy_thm witns thm = thm |> fold (fn hyp =>
    (case find_first (fn Witness (t, _) => Thm.term_of hyp aconv t) witns of
      NONE => I
    | SOME w => Thm.implies_intr hyp #> compose_witness w)) (#hyps (Thm.crep_thm thm));

fun satisfy_morphism witns = Morphism.thm_morphism (satisfy_thm witns);

fun satisfy_facts witns = facts_map (morph_ctxt (satisfy_morphism witns));


(* generalize type/term parameters *)

val maxidx_atts = fold Args.maxidx_values;

fun generalize_facts inner outer facts =
  let
    val thy = ProofContext.theory_of inner;
    val maxidx =
      fold (fn ((_, atts), bs) => maxidx_atts atts #> fold (maxidx_atts o #2) bs) facts ~1;
    val exp_fact = map (Thm.adjust_maxidx_thm maxidx) #> Variable.export inner outer;
    val exp_term = Drule.term_rule thy (singleton exp_fact);
    val exp_typ = Logic.type_map exp_term;
    val morphism =
      Morphism.morphism {binding = I, var = I, typ = exp_typ, term = exp_term, fact = exp_fact};
  in facts_map (morph_ctxt morphism) facts end;


(** activate in context, return elements and facts **)

local

fun activate_elem (Fixes fixes) ctxt =
      ([], ctxt |> ProofContext.add_fixes_i fixes |> snd)
  | activate_elem (Constrains _) ctxt =
      ([], ctxt)
  | activate_elem (Assumes asms) ctxt =
      let
        val asms' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) asms;
        val ts = maps (map #1 o #2) asms';
        val (_, ctxt') =
          ctxt |> fold Variable.auto_fixes ts
          |> ProofContext.add_assms_i Assumption.presume_export asms';
      in ([], ctxt') end
  | activate_elem (Defines defs) ctxt =
      let
        val defs' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) defs;
        val asms = defs' |> map (fn ((name, atts), (t, ps)) =>
            let val ((c, _), t') = LocalDefs.cert_def ctxt t
            in (t', ((Binding.map_base (Thm.def_name_optional c) name, atts), [(t', ps)])) end);
        val (_, ctxt') =
          ctxt |> fold (Variable.auto_fixes o #1) asms
          |> ProofContext.add_assms_i LocalDefs.def_export (map #2 asms);
      in ([], ctxt') end
  | activate_elem (Notes (kind, facts)) ctxt =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of ctxt)) facts;
        val (res, ctxt') = ctxt |> ProofContext.note_thmss_i kind facts';
      in ((map (#1 o #1) facts' ~~ map #2 res), ctxt') end;

fun gen_activate prep_facts raw_elems ctxt =
  let
    val elems = map (map_ctxt_attrib Args.assignable o prep_facts ctxt) raw_elems;
    val (res, ctxt') = fold_map activate_elem elems (ProofContext.qualified_names ctxt);
    val elems' = elems |> map (map_ctxt_attrib Args.closure);
  in ((elems', flat res), ProofContext.restore_naming ctxt ctxt') end;

fun check_name name =
  if NameSpace.is_qualified name then error ("Illegal qualified name: " ^ quote name)
  else name;

fun prep_facts prep_name get intern ctxt elem = elem |> map_ctxt
     {var = I, typ = I, term = I,
      binding = Binding.map_base prep_name,
      fact = get ctxt,
      attrib = intern (ProofContext.theory_of ctxt)};

in

fun activate x = gen_activate (prep_facts check_name ProofContext.get_fact Attrib.intern_src) x;
fun activate_i x = gen_activate (K I) x;

end;

end;
