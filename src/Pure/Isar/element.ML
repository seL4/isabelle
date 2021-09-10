(*  Title:      Pure/Isar/element.ML
    Author:     Makarius

Explicit data structures for some Isar language elements, with derived
logical operations.
*)

signature ELEMENT =
sig
  type ('typ, 'term) obtain = binding * ((binding * 'typ option * mixfix) list * 'term list)
  type obtains = (string, string) obtain list
  type obtains_i = (typ, term) obtain list
  datatype ('typ, 'term) stmt =
    Shows of (Attrib.binding * ('term * 'term list) list) list |
    Obtains of ('typ, 'term) obtain list
  type statement = (string, string) stmt
  type statement_i = (typ, term) stmt
  datatype ('typ, 'term, 'fact) ctxt =
    Fixes of (binding * 'typ option * mixfix) list |
    Constrains of (string * 'typ) list |
    Assumes of (Attrib.binding * ('term * 'term list) list) list |
    Defines of (Attrib.binding * ('term * 'term list)) list |
    Notes of string * (Attrib.binding * ('fact * Token.src list) list) list |
    Lazy_Notes of string * (binding * 'fact lazy)
  type context = (string, string, Facts.ref) ctxt
  type context_i = (typ, term, thm list) ctxt
  val map_ctxt: {binding: binding -> binding, typ: 'typ -> 'a, term: 'term -> 'b,
    pattern: 'term -> 'b, fact: 'fact -> 'c, attrib: Token.src -> Token.src} ->
    ('typ, 'term, 'fact) ctxt -> ('a, 'b, 'c) ctxt
  val map_ctxt_attrib: (Token.src -> Token.src) ->
    ('typ, 'term, 'fact) ctxt -> ('typ, 'term, 'fact) ctxt
  val transform_ctxt: morphism -> context_i -> context_i
  val pretty_stmt: Proof.context -> statement_i -> Pretty.T list
  val pretty_ctxt: Proof.context -> context_i -> Pretty.T list
  val pretty_ctxt_no_attribs: Proof.context -> context_i -> Pretty.T list
  val pretty_statement: Proof.context -> string -> thm -> Pretty.T
  type witness
  val prove_witness: Proof.context -> term -> tactic -> witness
  val witness_proof: (witness list list -> Proof.context -> Proof.context) ->
    term list list -> Proof.context -> Proof.state
  val witness_proof_eqs: (witness list list -> thm list -> Proof.context -> Proof.context) ->
    term list list -> term list -> Proof.context -> Proof.state
  val witness_local_proof: (witness list list -> Proof.state -> Proof.state) ->
    string -> term list list -> Proof.context -> Proof.state -> Proof.state
  val witness_local_proof_eqs: (witness list list -> thm list -> Proof.state -> Proof.state) ->
    string -> term list list -> term list -> Proof.context -> Proof.state -> Proof.state
  val transform_witness: morphism -> witness -> witness
  val conclude_witness: Proof.context -> witness -> thm
  val pretty_witness: Proof.context -> witness -> Pretty.T
  val instantiate_normalize_morphism: ctyp TFrees.table * cterm Frees.table -> morphism
  val satisfy_morphism: witness list -> morphism
  val eq_term_morphism: theory -> term list -> morphism option
  val eq_morphism: theory -> thm list -> morphism option
  val init: context_i -> Context.generic -> Context.generic
  val activate_i: context_i -> Proof.context -> context_i * Proof.context
  val activate: (typ, term, Facts.ref) ctxt -> Proof.context -> context_i * Proof.context
end;

structure Element: ELEMENT =
struct

(** language elements **)

(* statement *)

type ('typ, 'term) obtain = binding * ((binding * 'typ option * mixfix) list * 'term list);
type obtains = (string, string) obtain list;
type obtains_i = (typ, term) obtain list;

datatype ('typ, 'term) stmt =
  Shows of (Attrib.binding * ('term * 'term list) list) list |
  Obtains of ('typ, 'term) obtain list;

type statement = (string, string) stmt;
type statement_i = (typ, term) stmt;


(* context *)

datatype ('typ, 'term, 'fact) ctxt =
  Fixes of (binding * 'typ option * mixfix) list |
  Constrains of (string * 'typ) list |
  Assumes of (Attrib.binding * ('term * 'term list) list) list |
  Defines of (Attrib.binding * ('term * 'term list)) list |
  Notes of string * (Attrib.binding * ('fact * Token.src list) list) list |
  Lazy_Notes of string * (binding * 'fact lazy);

type context = (string, string, Facts.ref) ctxt;
type context_i = (typ, term, thm list) ctxt;

fun map_ctxt {binding, typ, term, pattern, fact, attrib} =
  fn Fixes fixes => Fixes (fixes |> map (fn (x, T, mx) => (binding x, Option.map typ T, mx)))
   | Constrains xs => Constrains (xs |> map (fn (x, T) =>
      (Variable.check_name (binding (Binding.name x)), typ T)))
   | Assumes asms => Assumes (asms |> map (fn ((a, atts), propps) =>
      ((binding a, map attrib atts), propps |> map (fn (t, ps) => (term t, map pattern ps)))))
   | Defines defs => Defines (defs |> map (fn ((a, atts), (t, ps)) =>
      ((binding a, map attrib atts), (term t, map pattern ps))))
   | Notes (kind, facts) => Notes (kind, facts |> map (fn ((a, atts), bs) =>
      ((binding a, map attrib atts), bs |> map (fn (ths, btts) => (fact ths, map attrib btts)))))
   | Lazy_Notes (kind, (a, ths)) => Lazy_Notes (kind, (binding a, Lazy.map fact ths));

fun map_ctxt_attrib attrib =
  map_ctxt {binding = I, typ = I, term = I, pattern = I, fact = I, attrib = attrib};

fun transform_ctxt phi = map_ctxt
 {binding = Morphism.binding phi,
  typ = Morphism.typ phi,
  term = Morphism.term phi,
  pattern = Morphism.term phi,
  fact = Morphism.fact phi,
  attrib = map (Token.transform phi)};



(** pretty printing **)

fun pretty_items _ _ [] = []
  | pretty_items keyword sep (x :: ys) =
      Pretty.block [Pretty.keyword2 keyword, Pretty.brk 1, x] ::
        map (fn y => Pretty.block [Pretty.str "  ", Pretty.keyword2 sep, Pretty.brk 1, y]) ys;


(* pretty_stmt *)

fun pretty_stmt ctxt =
  let
    val prt_typ = Pretty.quote o Syntax.pretty_typ ctxt;
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    val prt_terms = separate (Pretty.keyword2 "and") o map prt_term;
    val prt_binding = Attrib.pretty_binding ctxt;
    val prt_name = Proof_Context.pretty_name ctxt;

    fun prt_show (a, ts) =
      Pretty.block (Pretty.breaks (prt_binding a ":" @ prt_terms (map fst ts)));

    fun prt_var (x, SOME T, _) = Pretty.block
          [prt_name (Binding.name_of x), Pretty.str " ::", Pretty.brk 1, prt_typ T]
      | prt_var (x, NONE, _) = prt_name (Binding.name_of x);
    val prt_vars = separate (Pretty.keyword2 "and") o map prt_var;

    fun prt_obtain (_, ([], props)) = Pretty.block (Pretty.breaks (prt_terms props))
      | prt_obtain (_, (vars, props)) = Pretty.block (Pretty.breaks
          (prt_vars vars @ [Pretty.keyword2 "where"] @ prt_terms props));
  in
    fn Shows shows => pretty_items "shows" "and" (map prt_show shows)
     | Obtains obtains => pretty_items "obtains" "|" (map prt_obtain obtains)
  end;


(* pretty_ctxt *)

fun gen_pretty_ctxt show_attribs ctxt =
  let
    val prt_typ = Pretty.quote o Syntax.pretty_typ ctxt;
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    val prt_thm = Pretty.cartouche o Thm.pretty_thm ctxt;
    val prt_name = Proof_Context.pretty_name ctxt;

    fun prt_binding (b, atts) =
      Attrib.pretty_binding ctxt (b, if show_attribs then atts else []);

    fun prt_fact (ths, atts) =
      if not show_attribs orelse null atts then map prt_thm ths
      else
        Pretty.enclose "(" ")" (Pretty.breaks (map prt_thm ths)) ::
          Attrib.pretty_attribs ctxt atts;

    fun prt_mixfix NoSyn = []
      | prt_mixfix mx = [Pretty.brk 2, Mixfix.pretty_mixfix mx];

    fun prt_fix (x, SOME T, mx) = Pretty.block (prt_name (Binding.name_of x) :: Pretty.str " ::" ::
          Pretty.brk 1 :: prt_typ T :: prt_mixfix mx)
      | prt_fix (x, NONE, mx) = Pretty.block (prt_name (Binding.name_of x) :: prt_mixfix mx);
    fun prt_constrain (x, T) = prt_fix (Binding.name x, SOME T, NoSyn);

    fun prt_asm (a, ts) =
      Pretty.block (Pretty.breaks (prt_binding a ":" @ map (prt_term o fst) ts));
    fun prt_def (a, (t, _)) =
      Pretty.block (Pretty.breaks (prt_binding a ":" @ [prt_term t]));

    fun prt_note (a, ths) =
      Pretty.block (Pretty.breaks (flat (prt_binding a " =" :: map prt_fact ths)));

    fun notes_kind "" = "notes"
      | notes_kind kind = "notes " ^ kind;
  in
    fn Fixes fixes => pretty_items "fixes" "and" (map prt_fix fixes)
     | Constrains xs => pretty_items "constrains" "and" (map prt_constrain xs)
     | Assumes asms => pretty_items "assumes" "and" (map prt_asm asms)
     | Defines defs => pretty_items "defines" "and" (map prt_def defs)
     | Notes (kind, facts) => pretty_items (notes_kind kind) "and" (map prt_note facts)
     | Lazy_Notes (kind, (a, ths)) =>
        pretty_items (notes_kind kind) "and" [prt_note ((a, []), [(Lazy.force ths, [])])]
  end;

val pretty_ctxt = gen_pretty_ctxt true;
val pretty_ctxt_no_attribs = gen_pretty_ctxt false;


(* pretty_statement *)

local

fun standard_elim ctxt th =
  (case Object_Logic.elim_concl ctxt th of
    SOME C =>
      let
        val thesis = Var ((Auto_Bind.thesisN, Thm.maxidx_of th + 1), fastype_of C);
        val insts = (TVars.empty, Vars.make [(Term.dest_Var C, Thm.cterm_of ctxt thesis)]);
        val th' = Thm.instantiate insts th;
      in (th', true) end
  | NONE => (th, false));

fun thm_name ctxt kind th prts =
  let val head =
    if Thm.has_name_hint th then
      Pretty.block [Pretty.keyword1 kind, Pretty.brk 1,
        Proof_Context.pretty_name ctxt (Long_Name.base_name (Thm.get_name_hint th)), Pretty.str ":"]
    else Pretty.keyword1 kind
  in Pretty.block (Pretty.fbreaks (head :: prts)) end;

fun obtain prop ctxt =
  let
    val ((ps, prop'), ctxt') = Variable.focus NONE prop ctxt;
    fun fix (x, T) = (Binding.name (Variable.revert_fixed ctxt' x), SOME T, NoSyn);
    val xs = map (fix o #2) ps;
    val As = Logic.strip_imp_prems prop';
  in ((Binding.empty, (xs, As)), ctxt') end;

in

fun pretty_statement ctxt kind raw_th =
  let
    val (th, is_elim) = standard_elim ctxt (Raw_Simplifier.norm_hhf ctxt raw_th);
    val ((_, [th']), ctxt') = Variable.import true [th] (Variable.set_body true ctxt);
    val prop = Thm.prop_of th';
    val (prems, concl) = Logic.strip_horn prop;
    val concl_term = Object_Logic.drop_judgment ctxt concl;

    val (assumes, cases) =
      chop_suffix (fn prem => is_elim andalso concl aconv Logic.strip_assums_concl prem) prems;
    val is_thesis = if null cases then K false else fn v => v aconv concl_term;
    val fixes =
      rev (fold_aterms (fn v as Free (x, T) =>
        if Variable.is_newly_fixed ctxt' ctxt x andalso not (is_thesis v)
        then insert (op =) (Variable.revert_fixed ctxt' x, T) else I | _ => I) prop []);
  in
    pretty_ctxt ctxt' (Fixes (map (fn (x, T) => (Binding.name x, SOME T, NoSyn)) fixes)) @
    pretty_ctxt ctxt' (Assumes (map (fn t => (Binding.empty_atts, [(t, [])])) assumes)) @
     (if null cases then pretty_stmt ctxt' (Shows [(Binding.empty_atts, [(concl, [])])])
      else
        let val (clauses, ctxt'') = fold_map obtain cases ctxt'
        in pretty_stmt ctxt'' (Obtains clauses) end)
  end |> thm_name ctxt kind raw_th;

end;



(** logical operations **)

(* witnesses -- hypotheses as protected facts *)

datatype witness = Witness of term * thm;

val mark_witness = Logic.protect;
fun witness_prop (Witness (t, _)) = t;
fun witness_hyps (Witness (_, th)) = Thm.hyps_of th;
fun map_witness f (Witness witn) = Witness (f witn);

fun transform_witness phi = map_witness (fn (t, th) => (Morphism.term phi t, Morphism.thm phi th));

fun prove_witness ctxt t tac =
  Witness (t,
    Goal.prove ctxt [] [] (mark_witness t)
      (fn _ => resolve_tac ctxt [Drule.protectI] 1 THEN tac)
    |> Thm.close_derivation \<^here>);


local

val refine_witness =
  Proof.refine_singleton (Method.Basic (fn ctxt => CONTEXT_TACTIC o
    K (ALLGOALS (CONJUNCTS (ALLGOALS (CONJUNCTS (TRYALL (resolve_tac ctxt [Drule.protectI]))))))));

fun gen_witness_proof proof after_qed wit_propss eq_props =
  let
    val propss =
      (map o map) (fn prop => (mark_witness prop, [])) wit_propss @
        [map (rpair []) eq_props];
    fun after_qed' thmss =
      let val (wits, eqs) = split_last ((map o map) (Thm.close_derivation \<^here>) thmss);
      in after_qed ((map2 o map2) (curry Witness) wit_propss wits) eqs end;
  in proof after_qed' propss #> refine_witness end;

fun proof_local cmd goal_ctxt after_qed propp =
  let
    fun after_qed' (result_ctxt, results) state' =
      after_qed (burrow (Proof_Context.export result_ctxt (Proof.context_of state')) results) state';
  in
    Proof.map_context (K goal_ctxt) #>
    Proof.internal_goal (K (K ())) (Proof_Context.get_mode goal_ctxt) true cmd
      NONE after_qed' [] [] (map (pair Binding.empty_atts) propp) #> snd
  end;

in

fun witness_proof after_qed wit_propss =
  gen_witness_proof (Proof.theorem NONE) (fn wits => fn _ => after_qed wits)
    wit_propss [];

val witness_proof_eqs = gen_witness_proof (Proof.theorem NONE);

fun witness_local_proof after_qed cmd wit_propss goal_ctxt =
  gen_witness_proof (proof_local cmd goal_ctxt)
    (fn wits => fn _ => after_qed wits) wit_propss [];

fun witness_local_proof_eqs after_qed cmd wit_propss eq_props goal_ctxt =
  gen_witness_proof (proof_local cmd goal_ctxt) after_qed wit_propss eq_props;

end;

fun conclude_witness ctxt (Witness (_, th)) =
  Goal.conclude th
  |> Raw_Simplifier.norm_hhf_protect ctxt
  |> Thm.close_derivation \<^here>;

fun pretty_witness ctxt witn =
  let val prt_term = Pretty.quote o Syntax.pretty_term ctxt in
    Pretty.block (prt_term (witness_prop witn) ::
      (if Config.get ctxt show_hyps then [Pretty.brk 2, Pretty.list "[" "]"
         (map prt_term (witness_hyps witn))] else []))
  end;


(* instantiate frees, with beta normalization *)

fun instantiate_normalize_morphism insts =
  Morphism.instantiate_frees_morphism insts $>
  Morphism.term_morphism "beta_norm" Envir.beta_norm $>
  Morphism.thm_morphism "beta_conversion" (Conv.fconv_rule (Thm.beta_conversion true));


(* satisfy hypotheses *)

local

val norm_term = Envir.beta_eta_contract;
val norm_conv = Drule.beta_eta_conversion;
val norm_cterm = Thm.rhs_of o norm_conv;

fun find_witness witns hyp =
  (case find_first (fn Witness (t, _) => hyp aconv t) witns of
    NONE =>
      let val hyp' = norm_term hyp
      in find_first (fn Witness (t, _) => hyp' aconv norm_term t) witns end
  | some => some);

fun compose_witness (Witness (_, th)) r =
  let
    val th' = Goal.conclude th;
    val A = Thm.cprem_of r 1;
  in
    Thm.implies_elim
      (Conv.gconv_rule norm_conv 1 r)
      (Conv.fconv_rule norm_conv
        (Thm.instantiate (Thm.match (apply2 norm_cterm (Thm.cprop_of th', A))) th'))
  end;

in

fun satisfy_thm witns thm =
  (Thm.chyps_of thm, thm) |-> fold (fn hyp =>
    (case find_witness witns (Thm.term_of hyp) of
      NONE => I
    | SOME w => Thm.implies_intr hyp #> compose_witness w));

val satisfy_morphism = Morphism.thm_morphism "Element.satisfy" o satisfy_thm;

end;


(* rewriting with equalities *)

(* for activating declarations only *)
fun eq_term_morphism _ [] = NONE
  | eq_term_morphism thy props =
      let
        fun decomp_simp prop =
          let
            val ctxt = Proof_Context.init_global thy;
            val _ = Logic.count_prems prop = 0 orelse
              error ("Bad conditional rewrite rule " ^ Syntax.string_of_term ctxt prop);
            val lhsrhs = Logic.dest_equals prop
              handle TERM _ => error ("Rewrite rule not a meta-equality " ^ Syntax.string_of_term ctxt prop);
          in lhsrhs end;
        val phi =
          Morphism.morphism "Element.eq_term_morphism"
           {binding = [],
            typ = [],
            term = [Pattern.rewrite_term thy (map decomp_simp props) []],
            fact = [fn _ => error "Illegal application of Element.eq_term_morphism"]};
      in SOME phi end;

fun eq_morphism _ [] = NONE
  | eq_morphism thy thms =
      let
        (* FIXME proper context!? *)
        fun rewrite th = rewrite_rule (Proof_Context.init_global (Thm.theory_of_thm th)) thms th;
        val phi =
          Morphism.morphism "Element.eq_morphism"
           {binding = [],
            typ = [],
            term = [Raw_Simplifier.rewrite_term thy thms []],
            fact = [map rewrite]};
      in SOME phi end;



(** activate in context **)

(* init *)

fun init (Fixes fixes) = Context.map_proof (Proof_Context.add_fixes fixes #> #2)
  | init (Constrains _) = I
  | init (Assumes asms) = Context.map_proof (fn ctxt =>
      let
        val asms' = Attrib.map_specs (map (Attrib.attribute ctxt)) asms;
        val (_, ctxt') = ctxt
          |> fold Proof_Context.augment (maps (map #1 o #2) asms')
          |> Proof_Context.add_assms Assumption.assume_export asms';
      in ctxt' end)
  | init (Defines defs) = Context.map_proof (fn ctxt =>
      let
        val defs' = Attrib.map_specs (map (Attrib.attribute ctxt)) defs;
        val asms = defs' |> map (fn (b, (t, ps)) =>
            let val (_, t') = Local_Defs.cert_def ctxt (K []) t  (* FIXME adapt ps? *)
            in (t', (b, [(t', ps)])) end);
        val (_, ctxt') = ctxt
          |> fold Proof_Context.augment (map #1 asms)
          |> Proof_Context.add_assms Local_Defs.def_export (map #2 asms);
      in ctxt' end)
  | init (Notes (kind, facts)) = Attrib.generic_notes kind facts #> #2
  | init (Lazy_Notes (kind, ths)) = Attrib.lazy_notes kind ths;


(* activate *)

fun activate_i elem ctxt =
  let
    val elem' =
      (case (map_ctxt_attrib o map) Token.init_assignable elem of
        Defines defs =>
          Defines (defs |> map (fn ((a, atts), (t, ps)) =>
            ((Thm.def_binding_optional
              (Binding.name (#1 (#1 (Local_Defs.cert_def ctxt (K []) t)))) a, atts),
              (t, ps))))
      | e => e);
    val ctxt' = Context.proof_map (init elem') ctxt;
  in ((map_ctxt_attrib o map) Token.closure elem', ctxt') end;

fun activate raw_elem ctxt =
  let val elem = raw_elem |> map_ctxt
   {binding = I,
    typ = I,
    term = I,
    pattern = I,
    fact = Proof_Context.get_fact ctxt,
    attrib = Attrib.check_src ctxt}
  in activate_i elem ctxt end;

end;
