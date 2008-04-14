(*  Title:      Pure/Isar/locale.ML
    ID:         $Id$
    Author:     Clemens Ballarin, TU Muenchen; Markus Wenzel, LMU/TU Muenchen

Locales -- Isar proof contexts as meta-level predicates, with local
syntax and implicit structures.

Draws basic ideas from Florian Kammueller's original version of
locales, but uses the richer infrastructure of Isar instead of the raw
meta-logic.  Furthermore, structured import of contexts (with merge
and rename operations) are provided, as well as type-inference of the
signature parts, and predicate definitions of the specification text.

Interpretation enables the reuse of theorems of locales in other
contexts, namely those defined by theories, structured proofs and
locales themselves.

See also:

[1] Clemens Ballarin. Locales and Locale Expressions in Isabelle/Isar.
    In Stefano Berardi et al., Types for Proofs and Programs: International
    Workshop, TYPES 2003, Torino, Italy, LNCS 3085, pages 34-50, 2004.
[2] Clemens Ballarin. Interpretation of Locales in Isabelle: Managing
    Dependencies between Locales. Technical Report TUM-I0607, Technische
    Universitaet Muenchen, 2006.
[3] Clemens Ballarin. Interpretation of Locales in Isabelle: Theories and
    Proof Contexts. In J.M. Borwein and W.M. Farmer, MKM 2006, LNAI 4108,
    pages 31-43, 2006.
*)

(* TODO:
- beta-eta normalisation of interpretation parameters
- dangling type frees in locales
- test subsumption of interpretations when merging theories
*)

signature LOCALE =
sig
  datatype expr =
    Locale of string |
    Rename of expr * (string * mixfix option) option list |
    Merge of expr list
  val empty: expr
  datatype 'a element = Elem of 'a | Expr of expr
  val map_elem: ('a -> 'b) -> 'a element -> 'b element

  val intern: theory -> xstring -> string
  val intern_expr: theory -> expr -> expr
  val extern: theory -> string -> xstring
  val init: string -> theory -> Proof.context

  (* The specification of a locale *)
  val parameters_of: theory -> string ->
    ((string * typ) * mixfix) list
  val parameters_of_expr: theory -> expr ->
    ((string * typ) * mixfix) list
  val local_asms_of: theory -> string ->
    ((string * Attrib.src list) * term list) list
  val global_asms_of: theory -> string ->
    ((string * Attrib.src list) * term list) list
  val intros: theory -> string -> thm list * thm list
  val dests: theory -> string -> thm list

  (* Processing of locale statements *)
  val read_context_statement: xstring option -> Element.context element list ->
    (string * string list) list list -> Proof.context ->
    string option * Proof.context * Proof.context * (term * term list) list list
  val read_context_statement_i: string option -> Element.context element list ->
    (string * string list) list list -> Proof.context ->
    string option * Proof.context * Proof.context * (term * term list) list list
  val cert_context_statement: string option -> Element.context_i element list ->
    (term * term list) list list -> Proof.context ->
    string option * Proof.context * Proof.context * (term * term list) list list
  val read_expr: expr -> Element.context list -> Proof.context ->
    Element.context_i list * Proof.context
  val cert_expr: expr -> Element.context_i list -> Proof.context ->
    Element.context_i list * Proof.context

  (* Diagnostic functions *)
  val print_locales: theory -> unit
  val print_locale: theory -> bool -> expr -> Element.context list -> unit
  val print_registrations: bool -> string -> Proof.context -> unit

  val add_locale: string option -> bstring -> expr -> Element.context list -> theory
    -> string * Proof.context
  val add_locale_i: string option -> bstring -> expr -> Element.context_i list -> theory
    -> string * Proof.context

  (* Tactics *)
  val intro_locales_tac: bool -> Proof.context -> thm list -> tactic

  (* Storing results *)
  val add_thmss: string -> string ->
    ((string * Attrib.src list) * (thm list * Attrib.src list) list) list ->
    Proof.context -> Proof.context
  val add_type_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_term_syntax: string -> declaration -> Proof.context -> Proof.context
  val add_declaration: string -> declaration -> Proof.context -> Proof.context

  val interpretation_i: (Proof.context -> Proof.context) ->
    (bool * string) * Attrib.src list -> expr ->
    term option list * ((bstring * Attrib.src list) * term) list ->
    theory -> Proof.state
  val interpretation: (Proof.context -> Proof.context) ->
    (bool * string) * Attrib.src list -> expr ->
    string option list * ((bstring * Attrib.src list) * string) list ->
    theory -> Proof.state
  val interpretation_in_locale: (Proof.context -> Proof.context) ->
    xstring * expr -> theory -> Proof.state
  val interpret_i: (Proof.state -> Proof.state Seq.seq) ->
    (bool * string) * Attrib.src list -> expr ->
    term option list * ((bstring * Attrib.src list) * term) list ->
    bool -> Proof.state -> Proof.state
  val interpret: (Proof.state -> Proof.state Seq.seq) ->
    (bool * string) * Attrib.src list -> expr ->
    string option list * ((bstring * Attrib.src list) * string) list ->
    bool -> Proof.state -> Proof.state
end;

structure Locale: LOCALE =
struct

(* legacy operations *)

fun gen_merge_lists _ xs [] = xs
  | gen_merge_lists _ [] ys = ys
  | gen_merge_lists eq xs ys = xs @ filter_out (member eq xs) ys;

fun merge_lists xs ys = gen_merge_lists (op =) xs ys;
fun merge_alists xs = gen_merge_lists (eq_fst (op =)) xs;

fun legacy_unvarifyT thm =
  let
    val cT = Thm.ctyp_of (Thm.theory_of_thm thm);
    val tvars = rev (Thm.fold_terms Term.add_tvars thm []);
    val tfrees = map (fn ((x, _), S) => SOME (cT (TFree (x, S)))) tvars;
  in Drule.instantiate' tfrees [] thm end;

fun legacy_unvarify raw_thm =
  let
    val thm = legacy_unvarifyT raw_thm;
    val ct = Thm.cterm_of (Thm.theory_of_thm thm);
    val vars = rev (Thm.fold_terms Term.add_vars thm []);
    val frees = map (fn ((x, _), T) => SOME (ct (Free (x, T)))) vars;
  in Drule.instantiate' [] frees thm end;


(** locale elements and expressions **)

datatype ctxt = datatype Element.ctxt;

datatype expr =
  Locale of string |
  Rename of expr * (string * mixfix option) option list |
  Merge of expr list;

val empty = Merge [];

datatype 'a element =
  Elem of 'a | Expr of expr;

fun map_elem f (Elem e) = Elem (f e)
  | map_elem _ (Expr e) = Expr e;

type decl = declaration * stamp;

type locale =
 {axiom: Element.witness list,
    (* For locales that define predicates this is [A [A]], where A is the locale
       specification.  Otherwise [].
       Only required to generate the right witnesses for locales with predicates. *)
  imports: expr,                                                     (*dynamic imports*)
  elems: (Element.context_i * stamp) list,
    (* Static content, neither Fixes nor Constrains elements *)
  params: ((string * typ) * mixfix) list,                             (*all params*)
  lparams: string list,                                             (*local params*)
  decls: decl list * decl list,                    (*type/term_syntax declarations*)
  regs: ((string * string list) * Element.witness list) list,
    (* Registrations: indentifiers and witnesses of locales interpreted in the locale. *)
  intros: thm list * thm list,
    (* Introduction rules: of delta predicate and locale predicate. *)
  dests: thm list}
    (* Destruction rules relative to canonical order in locale context. *)

(* CB: an internal (Int) locale element was either imported or included,
   an external (Ext) element appears directly in the locale text. *)

datatype ('a, 'b) int_ext = Int of 'a | Ext of 'b;



(** substitutions on Frees and Vars -- clone from element.ML **)

(* instantiate types *)

fun var_instT_type env =
  if Vartab.is_empty env then I
  else Term.map_type_tvar (fn (x, S) => the_default (TVar (x, S)) (Vartab.lookup env x));

fun var_instT_term env =
  if Vartab.is_empty env then I
  else Term.map_types (var_instT_type env);

fun var_inst_term (envT, env) =
  if Vartab.is_empty env then var_instT_term envT
  else
    let
      val instT = var_instT_type envT;
      fun inst (Const (x, T)) = Const (x, instT T)
        | inst (Free (x, T)) = Free(x, instT T)
        | inst (Var (xi, T)) =
            (case Vartab.lookup env xi of
              NONE => Var (xi, instT T)
            | SOME t => t)
        | inst (b as Bound _) = b
        | inst (Abs (x, T, t)) = Abs (x, instT T, inst t)
        | inst (t $ u) = inst t $ inst u;
    in Envir.beta_norm o inst end;


(** management of registrations in theories and proof contexts **)

structure Registrations :
  sig
    type T
    val empty: T
    val join: T * T -> T
    val dest: theory -> T ->
      (term list *
        (((bool * string) * Attrib.src list) *
         (Morphism.morphism * ((typ Vartab.table * typ list) * (term Vartab.table * term list))) *
         Element.witness list *
         thm Termtab.table)) list
    val test: theory -> T * term list -> bool
    val lookup: theory ->
      T * (term list * ((typ Vartab.table * typ list) * (term Vartab.table * term list))) ->
      (((bool * string) * Attrib.src list) *
        Element.witness list *
        thm Termtab.table) option
    val insert: theory -> term list -> ((bool * string) * Attrib.src list) ->
        (Morphism.morphism * ((typ Vartab.table * typ list) * (term Vartab.table * term list))) -> T ->
      T * (term list * (((bool * string) * Attrib.src list) * Element.witness list)) list
    val add_witness: term list -> Element.witness -> T -> T
    val add_equation: term list -> thm -> T -> T
  end =
struct
  (* A registration is indexed by parameter instantiation.  Its components are:
     - parameters and prefix
       (if the Boolean flag is set, only accesses containing the prefix are generated,
        otherwise the prefix may be omitted when accessing theorems etc.)
     - pair of export and import morphisms, export maps content to its originating
       context, import is its inverse
     - theorems (actually witnesses) instantiating locale assumptions
     - theorems (equations) interpreting derived concepts and indexed by lhs.
     NB: index is exported while content is internalised.
  *)
  type T = (((bool * string) * Attrib.src list) *
            (Morphism.morphism * ((typ Vartab.table * typ list) * (term Vartab.table * term list))) *
            Element.witness list *
            thm Termtab.table) Termtab.table;

  val empty = Termtab.empty;

  (* term list represented as single term, for simultaneous matching *)
  fun termify ts =
    Term.list_comb (Const ("", map fastype_of ts ---> propT), ts);
  fun untermify t =
    let fun ut (Const _) ts = ts
          | ut (s $ t) ts = ut s (t::ts)
    in ut t [] end;

  (* joining of registrations:
     - prefix, attributes and morphisms of right theory;
     - witnesses are equal, no attempt to subsumption testing;
     - union of equalities, if conflicting (i.e. two eqns with equal lhs)
       eqn of right theory takes precedence *)
  fun join (r1, r2) = Termtab.join (fn _ => fn ((_, _, _, e1), (n, m, w, e2)) =>
      (n, m, w, Termtab.join (fn _ => fn (_, e) => e) (e1, e2))) (r1, r2);

  fun dest_transfer thy regs =
    Termtab.dest regs |> map (apsnd (fn (n, m, ws, es) =>
      (n, m, map (Element.transfer_witness thy) ws, Termtab.map (transfer thy) es)));

  fun dest thy regs = dest_transfer thy regs |> map (apfst untermify);

  (* registrations that subsume t *)
  fun subsumers thy t regs =
    filter (fn (t', _) => Pattern.matches thy (t', t)) (dest_transfer thy regs);

  (* test if registration that subsumes the query is present *)
  fun test thy (regs, ts) =
    not (null (subsumers thy (termify ts) regs));
      
  (* look up registration, pick one that subsumes the query *)
  fun lookup thy (regs, (ts, ((impT, _), (imp, _)))) =
    let
      val t = termify ts;
      val subs = subsumers thy t regs;
    in
      (case subs of
        [] => NONE
      | ((t', ((prfx, atts), (exp', ((impT', domT'), (imp', dom'))), thms, eqns)) :: _) =>
          let
            val (tinst, inst) = Pattern.match thy (t', t) (Vartab.empty, Vartab.empty);
            val tinst' = domT' |> map (fn (T as TFree (x, _)) =>
                (x, T |> Morphism.typ exp' |> Envir.typ_subst_TVars tinst
                      |> var_instT_type impT)) |> Symtab.make;
            val inst' = dom' |> map (fn (t as Free (x, _)) =>
                (x, t |> Morphism.term exp' |> Envir.subst_vars (tinst, inst)
                      |> var_inst_term (impT, imp))) |> Symtab.make;
            val inst'_morph = Element.inst_morphism thy (tinst', inst');
          in SOME ((prfx, map (Args.morph_values inst'_morph) atts),
            map (Element.morph_witness inst'_morph) thms,
            Termtab.map (Morphism.thm inst'_morph) eqns)
          end)
    end;

  (* add registration if not subsumed by ones already present,
     additionally returns registrations that are strictly subsumed *)
  fun insert thy ts attn m regs =
    let
      val t = termify ts;
      val subs = subsumers thy t regs ;
    in (case subs of
        [] => let
                val sups =
                  filter (fn (t', _) => Pattern.matches thy (t, t')) (dest_transfer thy regs);
                val sups' = map (apfst untermify) sups |> map (fn (ts, (n, _, w, _)) => (ts, (n, w)))
              in (Termtab.update (t, (attn, m, [], Termtab.empty)) regs, sups') end
      | _ => (regs, []))
    end;

  fun gen_add f ts regs =
    let
      val t = termify ts;
    in
      Termtab.update (t, f (the (Termtab.lookup regs t))) regs
    end;

  (* add witness theorem to registration,
     only if instantiation is exact, otherwise exception Option raised *)
  fun add_witness ts wit regs =
    gen_add (fn (x, m, wits, eqns) => (x, m, Element.close_witness wit :: wits, eqns))
      ts regs;

  (* add equation to registration, replaces previous equation with same lhs;
     only if instantiation is exact, otherwise exception Option raised;
     exception TERM raised if not a meta equality *)
  fun add_equation ts thm regs =
    gen_add (fn (x, m, thms, eqns) =>
      (x, m, thms, Termtab.update (thm |> prop_of |> Logic.dest_equals |> fst, Thm.close_derivation thm) eqns))
      ts regs;
end;


(** theory data : locales **)

structure LocalesData = TheoryDataFun
(
  type T = NameSpace.T * locale Symtab.table;
    (* 1st entry: locale namespace,
       2nd entry: locales of the theory *)

  val empty = (NameSpace.empty, Symtab.empty);
  val copy = I;
  val extend = I;

  fun join_locales _
    ({axiom, imports, elems, params, lparams, decls = (decls1, decls2), regs, intros, dests}: locale,
      {elems = elems', decls = (decls1', decls2'), regs = regs', ...}: locale) =
     {axiom = axiom,
      imports = imports,
      elems = gen_merge_lists (eq_snd (op =)) elems elems',
      params = params,
      lparams = lparams,
      decls =
       (Library.merge (eq_snd (op =)) (decls1, decls1'),
        Library.merge (eq_snd (op =)) (decls2, decls2')),
      regs = merge_alists regs regs',
      intros = intros,
      dests = dests};
  fun merge _ ((space1, locs1), (space2, locs2)) =
    (NameSpace.merge (space1, space2), Symtab.join join_locales (locs1, locs2));
);



(** context data : registrations **)

structure RegistrationsData = GenericDataFun
(
  type T = Registrations.T Symtab.table;  (*registrations, indexed by locale name*)
  val empty = Symtab.empty;
  val extend = I;
  fun merge _ = Symtab.join (K Registrations.join);
);


(** access locales **)

fun print_locales thy =
  let val (space, locs) = LocalesData.get thy in
    Pretty.strs ("locales:" :: map #1 (NameSpace.extern_table (space, locs)))
    |> Pretty.writeln
  end;

val intern = NameSpace.intern o #1 o LocalesData.get;
val extern = NameSpace.extern o #1 o LocalesData.get;

fun declare_locale name thy =
  thy |> LocalesData.map (fn (space, locs) =>
    (Sign.declare_name thy name space, locs));

fun put_locale name loc =
  LocalesData.map (fn (space, locs) =>
    (space, Symtab.update (name, loc) locs));

fun get_locale thy name = Symtab.lookup (#2 (LocalesData.get thy)) name;

fun the_locale thy name =
  (case get_locale thy name of
    SOME loc => loc
  | NONE => error ("Unknown locale " ^ quote name));

fun change_locale name f thy =
  let
    val {axiom, imports, elems, params, lparams, decls, regs, intros, dests} =
        the_locale thy name;
    val (axiom', imports', elems', params', lparams', decls', regs', intros', dests') =
      f (axiom, imports, elems, params, lparams, decls, regs, intros, dests);
  in
    put_locale name {axiom = axiom', imports = imports', elems = elems',
      params = params', lparams = lparams', decls = decls', regs = regs',
      intros = intros', dests = dests'} thy
  end;


(* access registrations *)

(* retrieve registration from theory or context *)

fun get_registrations ctxt name =
  case Symtab.lookup (RegistrationsData.get ctxt) name of
      NONE => []
    | SOME reg => Registrations.dest (Context.theory_of ctxt) reg;

fun get_global_registrations thy = get_registrations (Context.Theory thy);
fun get_local_registrations ctxt = get_registrations (Context.Proof ctxt);


fun get_registration ctxt imprt (name, ps) =
  case Symtab.lookup (RegistrationsData.get ctxt) name of
      NONE => NONE
    | SOME reg => Registrations.lookup (Context.theory_of ctxt) (reg, (ps, imprt));

fun get_global_registration thy = get_registration (Context.Theory thy);
fun get_local_registration ctxt = get_registration (Context.Proof ctxt);


fun test_registration ctxt (name, ps) =
  case Symtab.lookup (RegistrationsData.get ctxt) name of
      NONE => false
    | SOME reg => Registrations.test (Context.theory_of ctxt) (reg, ps);

fun test_global_registration thy = test_registration (Context.Theory thy);
fun test_local_registration ctxt = test_registration (Context.Proof ctxt);


(* add registration to theory or context, ignored if subsumed *)

fun put_registration (name, ps) attn morphs ctxt =
  RegistrationsData.map (fn regs =>
    let
      val thy = Context.theory_of ctxt;
      val reg = the_default Registrations.empty (Symtab.lookup regs name);
      val (reg', sups) = Registrations.insert thy ps attn morphs reg;
      val _ = if not (null sups) then warning
                ("Subsumed interpretation(s) of locale " ^
                 quote (extern thy name) ^
                 "\nwith the following prefix(es):" ^
                  commas_quote (map (fn (_, (((_, s), _), _)) => s) sups))
              else ();
    in Symtab.update (name, reg') regs end) ctxt;

fun put_global_registration id attn morphs =
  Context.theory_map (put_registration id attn morphs);
fun put_local_registration id attn morphs =
  Context.proof_map (put_registration id attn morphs);


fun put_registration_in_locale name id =
  change_locale name (fn (axiom, imports, elems, params, lparams, decls, regs, intros, dests) =>
    (axiom, imports, elems, params, lparams, decls, regs @ [(id, [])], intros, dests));


(* add witness theorem to registration, ignored if registration not present *)

fun add_witness (name, ps) thm =
  RegistrationsData.map (Symtab.map_entry name (Registrations.add_witness ps thm));

fun add_global_witness id thm = Context.theory_map (add_witness id thm);
fun add_local_witness id thm = Context.proof_map (add_witness id thm);


fun add_witness_in_locale name id thm =
  change_locale name (fn (axiom, imports, elems, params, lparams, decls, regs, intros, dests) =>
    let
      fun add (id', thms) =
        if id = id' then (id', thm :: thms) else (id', thms);
    in (axiom, imports, elems, params, lparams, decls, map add regs, intros, dests) end);


(* add equation to registration, ignored if registration not present *)

fun add_equation (name, ps) thm =
  RegistrationsData.map (Symtab.map_entry name (Registrations.add_equation ps thm));

fun add_global_equation id thm = Context.theory_map (add_equation id thm);
fun add_local_equation id thm = Context.proof_map (add_equation id thm);


(* printing of registrations *)

fun print_registrations show_wits loc ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    fun prt_term' t = if !show_types
          then Pretty.block [prt_term t, Pretty.brk 1, Pretty.str "::",
            Pretty.brk 1, (Pretty.quote o Syntax.pretty_typ ctxt) (type_of t)]
          else prt_term t;
    val prt_thm = prt_term o prop_of;
    fun prt_inst ts =
        Pretty.enclose "(" ")" (Pretty.breaks (map prt_term' ts));
    fun prt_attn ((false, prfx), atts) =
        Pretty.breaks (Pretty.str prfx :: Pretty.str "(optional)" ::
          Attrib.pretty_attribs ctxt atts)
      | prt_attn ((true, prfx), atts) =
        Pretty.breaks (Pretty.str prfx :: Attrib.pretty_attribs ctxt atts);
    fun prt_eqns [] = Pretty.str "no equations."
      | prt_eqns eqns = Pretty.block (Pretty.str "equations:" :: Pretty.brk 1 ::
          Pretty.breaks (map prt_thm eqns));
    fun prt_core ts eqns =
          [prt_inst ts, Pretty.fbrk, prt_eqns (Termtab.dest eqns |> map snd)];
    fun prt_witns [] = Pretty.str "no witnesses."
      | prt_witns witns = Pretty.block (Pretty.str "witnesses:" :: Pretty.brk 1 ::
          Pretty.breaks (map (Element.pretty_witness ctxt) witns))
    fun prt_reg (ts, (((_, ""), []), _, witns, eqns)) =
        if show_wits
          then Pretty.block (prt_core ts eqns @ [Pretty.fbrk, prt_witns witns])
          else Pretty.block (prt_core ts eqns)
      | prt_reg (ts, (attn, _, witns, eqns)) =
        if show_wits
          then Pretty.block ((prt_attn attn @ [Pretty.str ":", Pretty.brk 1] @
            prt_core ts eqns @ [Pretty.fbrk, prt_witns witns]))
          else Pretty.block ((prt_attn attn @
            [Pretty.str ":", Pretty.brk 1] @ prt_core ts eqns));

    val loc_int = intern thy loc;
    val regs = RegistrationsData.get (Context.Proof ctxt);
    val loc_regs = Symtab.lookup regs loc_int;
  in
    (case loc_regs of
        NONE => Pretty.str ("no interpretations")
      | SOME r => let
            val r' = Registrations.dest thy r;
            val r'' = Library.sort_wrt (fn (_, (((_, prfx), _), _, _, _)) => prfx) r';
          in Pretty.big_list ("interpretations:") (map prt_reg r'') end)
    |> Pretty.writeln
  end;


(* diagnostics *)

fun err_in_locale ctxt msg ids =
  let
    val thy = ProofContext.theory_of ctxt;
    fun prt_id (name, parms) =
      [Pretty.block (Pretty.breaks (map Pretty.str (extern thy name :: parms)))];
    val prt_ids = flat (separate [Pretty.str " +", Pretty.brk 1] (map prt_id ids));
    val err_msg =
      if forall (equal "" o #1) ids then msg
      else msg ^ "\n" ^ Pretty.string_of (Pretty.block
        (Pretty.str "The error(s) above occurred in locale:" :: Pretty.brk 1 :: prt_ids));
  in error err_msg end;

fun err_in_locale' ctxt msg ids' = err_in_locale ctxt msg (map fst ids');


fun pretty_ren NONE = Pretty.str "_"
  | pretty_ren (SOME (x, NONE)) = Pretty.str x
  | pretty_ren (SOME (x, SOME syn)) =
      Pretty.block [Pretty.str x, Pretty.brk 1, Syntax.pretty_mixfix syn];

fun pretty_expr thy (Locale name) = Pretty.str (extern thy name)
  | pretty_expr thy (Rename (expr, xs)) =
      Pretty.block [pretty_expr thy expr, Pretty.brk 1, Pretty.block (map pretty_ren xs |> Pretty.breaks)]
  | pretty_expr thy (Merge es) =
      Pretty.separate "+" (map (pretty_expr thy) es) |> Pretty.block;

fun err_in_expr _ msg (Merge []) = error msg
  | err_in_expr ctxt msg expr =
    error (msg ^ "\n" ^ Pretty.string_of (Pretty.block
      [Pretty.str "The error(s) above occured in locale expression:", Pretty.brk 1,
       pretty_expr (ProofContext.theory_of ctxt) expr]));


(** structured contexts: rename + merge + implicit type instantiation **)

(* parameter types *)

fun frozen_tvars ctxt Ts =
  #1 (Variable.importT_inst (map Logic.mk_type Ts) ctxt)
  |> map (fn ((xi, S), T) => (xi, (S, T)));

fun unify_frozen ctxt maxidx Ts Us =
  let
    fun paramify NONE i = (NONE, i)
      | paramify (SOME T) i = apfst SOME (TypeInfer.paramify_dummies T i);

    val (Ts', maxidx') = fold_map paramify Ts maxidx;
    val (Us', maxidx'') = fold_map paramify Us maxidx';
    val thy = ProofContext.theory_of ctxt;

    fun unify (SOME T, SOME U) env = (Sign.typ_unify thy (U, T) env
          handle Type.TUNIFY => raise TYPE ("unify_frozen: failed to unify types", [U, T], []))
      | unify _ env = env;
    val (unifier, _) = fold unify (Ts' ~~ Us') (Vartab.empty, maxidx'');
    val Vs = map (Option.map (Envir.norm_type unifier)) Us';
    val unifier' = Vartab.extend (unifier, frozen_tvars ctxt (map_filter I Vs));
  in map (Option.map (Envir.norm_type unifier')) Vs end;

fun params_of elemss =
  distinct (eq_fst (op = : string * string -> bool)) (maps (snd o fst) elemss);

fun params_of' elemss =
  distinct (eq_fst (op = : string * string -> bool)) (maps (snd o fst o fst) elemss);


fun params_qualified params name =
  NameSpace.qualified (space_implode "_" params) name;


(* CB: param_types has the following type:
  ('a * 'b option) list -> ('a * 'b) list *)
fun param_types ps = map_filter (fn (_, NONE) => NONE | (x, SOME T) => SOME (x, T)) ps;


fun merge_syntax ctxt ids ss = Symtab.merge (op = : mixfix * mixfix -> bool) ss
  handle Symtab.DUP x => err_in_locale ctxt
    ("Conflicting syntax for parameter: " ^ quote x) (map fst ids);


(* Distinction of assumed vs. derived identifiers.
   The former may have axioms relating assumptions of the context to
   assumptions of the specification fragment (for locales with
   predicates).  The latter have witnesses relating assumptions of the
   specification fragment to assumptions of other (assumed) specification
   fragments. *)

datatype 'a mode = Assumed of 'a | Derived of 'a;

fun map_mode f (Assumed x) = Assumed (f x)
  | map_mode f (Derived x) = Derived (f x);


(* flatten expressions *)

local

fun unify_parms ctxt fixed_parms raw_parmss =
  let
    val thy = ProofContext.theory_of ctxt;
    val maxidx = length raw_parmss;
    val idx_parmss = (0 upto maxidx - 1) ~~ raw_parmss;

    fun varify i = Term.map_type_tfree (fn (a, S) => TVar ((a, i), S));
    fun varify_parms (i, ps) = map (apsnd (varify i)) (param_types ps);
    val parms = fixed_parms @ maps varify_parms idx_parmss;

    fun unify T U envir = Sign.typ_unify thy (U, T) envir
      handle Type.TUNIFY =>
        let
          val T' = Envir.norm_type (fst envir) T;
          val U' = Envir.norm_type (fst envir) U;
          val prt = Sign.string_of_typ thy;
        in
          raise TYPE ("unify_parms: failed to unify types " ^
            prt U' ^ " and " ^ prt T', [U', T'], [])
        end;
    fun unify_list (T :: Us) = fold (unify T) Us
      | unify_list [] = I;
    val (unifier, _) = fold unify_list (map #2 (Symtab.dest (Symtab.make_list parms)))
      (Vartab.empty, maxidx);

    val parms' = map (apsnd (Envir.norm_type unifier)) (distinct (eq_fst (op =)) parms);
    val unifier' = Vartab.extend (unifier, frozen_tvars ctxt (map #2 parms'));

    fun inst_parms (i, ps) =
      List.foldr Term.add_typ_tfrees [] (map_filter snd ps)
      |> map_filter (fn (a, S) =>
          let val T = Envir.norm_type unifier' (TVar ((a, i), S))
          in if T = TFree (a, S) then NONE else SOME (a, T) end)
      |> Symtab.make;
  in map inst_parms idx_parmss end;

in

fun unify_elemss _ _ [] = []
  | unify_elemss _ [] [elems] = [elems]
  | unify_elemss ctxt fixed_parms elemss =
      let
        val thy = ProofContext.theory_of ctxt;
        val phis = unify_parms ctxt fixed_parms (map (snd o fst o fst) elemss)
          |> map (Element.instT_morphism thy);
        fun inst ((((name, ps), mode), elems), phi) =
          (((name, map (apsnd (Option.map (Morphism.typ phi))) ps),
              map_mode (map (Element.morph_witness phi)) mode),
            map (Element.morph_ctxt phi) elems);
      in map inst (elemss ~~ phis) end;


fun renaming xs parms = zip_options parms xs
  handle Library.UnequalLengths =>
    error ("Too many arguments in renaming: " ^
      commas (map (fn NONE => "_" | SOME x => quote (fst x)) xs));


(* params_of_expr:
   Compute parameters (with types and syntax) of locale expression.
*)

fun params_of_expr ctxt fixed_params expr (prev_parms, prev_types, prev_syn) =
  let
    val thy = ProofContext.theory_of ctxt;

    fun merge_tenvs fixed tenv1 tenv2 =
        let
          val [env1, env2] = unify_parms ctxt fixed
                [tenv1 |> Symtab.dest |> map (apsnd SOME),
                 tenv2 |> Symtab.dest |> map (apsnd SOME)]
        in
          Symtab.merge (op =) (Symtab.map (Element.instT_type env1) tenv1,
            Symtab.map (Element.instT_type env2) tenv2)
        end;

    fun merge_syn expr syn1 syn2 =
        Symtab.merge (op = : mixfix * mixfix -> bool) (syn1, syn2)
        handle Symtab.DUP x => err_in_expr ctxt
          ("Conflicting syntax for parameter: " ^ quote x) expr;

    fun params_of (expr as Locale name) =
          let
            val {imports, params, ...} = the_locale thy name;
            val parms = map (fst o fst) params;
            val (parms', types', syn') = params_of imports;
            val all_parms = merge_lists parms' parms;
            val all_types = merge_tenvs [] types' (params |> map fst |> Symtab.make);
            val all_syn = merge_syn expr syn' (params |> map (apfst fst) |> Symtab.make);
          in (all_parms, all_types, all_syn) end
      | params_of (expr as Rename (e, xs)) =
          let
            val (parms', types', syn') = params_of e;
            val ren = renaming xs parms';
            (* renaming may reduce number of parameters *)
            val new_parms = map (Element.rename ren) parms' |> distinct (op =);
            val ren_syn = syn' |> Symtab.dest |> map (Element.rename_var ren);
            val new_syn = fold (Symtab.insert (op =)) ren_syn Symtab.empty
                handle Symtab.DUP x =>
                  err_in_expr ctxt ("Conflicting syntax for parameter: " ^ quote x) expr;
            val syn_types = map (apsnd (fn mx =>
                SOME (Type.freeze_type (#1 (TypeInfer.paramify_dummies (Syntax.mixfixT mx) 0)))))
              (Symtab.dest new_syn);
            val ren_types = types' |> Symtab.dest |> map (apfst (Element.rename ren));
            val (env :: _) = unify_parms ctxt []
                ((ren_types |> map (apsnd SOME)) :: map single syn_types);
            val new_types = fold (Symtab.insert (op =))
                (map (apsnd (Element.instT_type env)) ren_types) Symtab.empty;
          in (new_parms, new_types, new_syn) end
      | params_of (Merge es) =
          fold (fn e => fn (parms, types, syn) =>
                   let
                     val (parms', types', syn') = params_of e
                   in
                     (merge_lists parms parms', merge_tenvs [] types types',
                      merge_syn e syn syn')
                   end)
            es ([], Symtab.empty, Symtab.empty)

      val (parms, types, syn) = params_of expr;
    in
      (merge_lists prev_parms parms, merge_tenvs fixed_params prev_types types,
       merge_syn expr prev_syn syn)
    end;

fun make_params_ids params = [(("", params), ([], Assumed []))];
fun make_raw_params_elemss (params, tenv, syn) =
    [((("", map (fn p => (p, Symtab.lookup tenv p)) params), Assumed []),
      Int [Fixes (map (fn p =>
        (p, Symtab.lookup tenv p, Symtab.lookup syn p |> the)) params)])];


(* flatten_expr:
   Extend list of identifiers by those new in locale expression expr.
   Compute corresponding list of lists of locale elements (one entry per
   identifier).

   Identifiers represent locale fragments and are in an extended form:
     ((name, ps), (ax_ps, axs))
   (name, ps) is the locale name with all its parameters.
   (ax_ps, axs) is the locale axioms with its parameters;
     axs are always taken from the top level of the locale hierarchy,
     hence axioms may contain additional parameters from later fragments:
     ps subset of ax_ps.  axs is either singleton or empty.

   Elements are enriched by identifier-like information:
     (((name, ax_ps), axs), elems)
   The parameters in ax_ps are the axiom parameters, but enriched by type
   info: now each entry is a pair of string and typ option.  Axioms are
   type-instantiated.

*)

fun flatten_expr ctxt ((prev_idents, prev_syntax), expr) =
  let
    val thy = ProofContext.theory_of ctxt;

    fun rename_parms top ren ((name, ps), (parms, mode)) =
        ((name, map (Element.rename ren) ps),
         if top
         then (map (Element.rename ren) parms,
               map_mode (map (Element.morph_witness (Element.rename_morphism ren))) mode)
         else (parms, mode));

    (* add (name, ps) and its registrations, recursively; adjust hyps of witnesses *)

    fun add_with_regs ((name, pTs), mode) (wits, ids, visited) =
        if member (fn (a, (b, _)) => a = b) visited (name, map #1 pTs)
        then (wits, ids, visited)
        else
          let
            val {params, regs, ...} = the_locale thy name;
            val pTs' = map #1 params;
            val ren = map #1 pTs' ~~ map (fn (x, _) => (x, NONE)) pTs;
              (* dummy syntax, since required by rename *)
            val pTs'' = map (fn ((p, _), (_, T)) => (p, T)) (pTs ~~ pTs');
            val [env] = unify_parms ctxt pTs [map (apsnd SOME) pTs''];
              (* propagate parameter types, to keep them consistent *)
            val regs' = map (fn ((name, ps), wits) =>
                ((name, map (Element.rename ren) ps),
                 map (Element.transfer_witness thy) wits)) regs;
            val new_regs = regs';
            val new_ids = map fst new_regs;
            val new_idTs =
              map (apsnd (map (fn p => (p, (the o AList.lookup (op =) pTs) p)))) new_ids;

            val new_wits = new_regs |> map (#2 #> map
              (Element.morph_witness
                (Element.instT_morphism thy env $>
                  Element.rename_morphism ren $>
                  Element.satisfy_morphism wits)
                #> Element.close_witness));
            val new_ids' = map (fn (id, wits) =>
                (id, ([], Derived wits))) (new_ids ~~ new_wits);
            val new_idTs' = map (fn ((n, pTs), (_, ([], mode))) =>
                ((n, pTs), mode)) (new_idTs ~~ new_ids');
            val new_id = ((name, map #1 pTs), ([], mode));
            val (wits', ids', visited') = fold add_with_regs new_idTs'
              (wits @ flat new_wits, ids, visited @ [new_id]);
          in
            (wits', ids' @ [new_id], visited')
          end;

    (* distribute top-level axioms over assumed ids *)

    fun axiomify all_ps ((name, parms), (_, Assumed _)) axioms =
        let
          val {elems, ...} = the_locale thy name;
          val ts = maps
            (fn (Assumes asms, _) => maps (map #1 o #2) asms
              | _ => [])
            elems;
          val (axs1, axs2) = chop (length ts) axioms;
        in (((name, parms), (all_ps, Assumed axs1)), axs2) end
      | axiomify all_ps (id, (_, Derived ths)) axioms =
          ((id, (all_ps, Derived ths)), axioms);

    (* identifiers of an expression *)

    fun identify top (Locale name) =
    (* CB: ids_ax is a list of tuples of the form ((name, ps), axs),
       where name is a locale name, ps a list of parameter names and axs
       a list of axioms relating to the identifier, axs is empty unless
       identify at top level (top = true);
       parms is accumulated list of parameters *)
          let
            val {axiom, imports, params, ...} = the_locale thy name;
            val ps = map (#1 o #1) params;
            val (ids', parms') = identify false imports;
                (* acyclic import dependencies *)

            val (_, ids'', _) = add_with_regs ((name, map #1 params), Assumed []) ([], ids', ids');
            val ids_ax = if top then fst (fold_map (axiomify ps) ids'' axiom) else ids'';
            in (ids_ax, merge_lists parms' ps) end
      | identify top (Rename (e, xs)) =
          let
            val (ids', parms') = identify top e;
            val ren = renaming xs parms'
              handle ERROR msg => err_in_locale' ctxt msg ids';

            val ids'' = distinct (eq_fst (op =)) (map (rename_parms top ren) ids');
            val parms'' = distinct (op =) (maps (#2 o #1) ids'');
          in (ids'', parms'') end
      | identify top (Merge es) =
          fold (fn e => fn (ids, parms) =>
                   let
                     val (ids', parms') = identify top e
                   in
                     (merge_alists ids ids', merge_lists parms parms')
                   end)
            es ([], []);

    fun inst_wit all_params (t, th) = let
         val {hyps, prop, ...} = Thm.rep_thm th;
         val ps = map (apsnd SOME) (fold Term.add_frees (prop :: hyps) []);
         val [env] = unify_parms ctxt all_params [ps];
         val t' = Element.instT_term env t;
         val th' = Element.instT_thm thy env th;
       in (t', th') end;

    fun eval all_params tenv syn ((name, params), (locale_params, mode)) =
      let
        val {params = ps_mx, elems = elems_stamped, ...} = the_locale thy name;
        val elems = map fst elems_stamped;
        val ps = map fst ps_mx;
        fun lookup_syn x = (case Symtab.lookup syn x of SOME Structure => NONE | opt => opt);
        val locale_params' = map (fn p => (p, Symtab.lookup tenv p |> the)) locale_params;
        val mode' = map_mode (map (Element.map_witness (inst_wit all_params))) mode;
        val ren = map fst ps ~~ map (fn p => (p, lookup_syn p)) params;
        val [env] = unify_parms ctxt all_params [map (apfst (Element.rename ren) o apsnd SOME) ps];
        val elem_morphism =
          Element.rename_morphism ren $>
          Morphism.name_morphism (params_qualified params) $>
          Element.instT_morphism thy env;
        val elems' = map (Element.morph_ctxt elem_morphism) elems;
      in (((name, map (apsnd SOME) locale_params'), mode'), elems') end;

    (* parameters, their types and syntax *)
    val (all_params', tenv, syn) = params_of_expr ctxt [] expr ([], Symtab.empty, Symtab.empty);
    val all_params = map (fn p => (p, Symtab.lookup tenv p |> the)) all_params';
    (* compute identifiers and syntax, merge with previous ones *)
    val (ids, _) = identify true expr;
    val idents = subtract (eq_fst (op =)) prev_idents ids;
    val syntax = merge_syntax ctxt ids (syn, prev_syntax);
    (* type-instantiate elements *)
    val final_elemss = map (eval all_params tenv syntax) idents;
  in ((prev_idents @ idents, syntax), final_elemss) end;

end;


(* activate elements *)

local

fun axioms_export axs _ As =
  (Element.satisfy_thm axs #> Drule.implies_intr_list (Library.drop (length axs, As)), fn t => t);


(* NB: derived ids contain only facts at this stage *)

fun activate_elem _ _ ((ctxt, mode), Fixes fixes) =
      ((ctxt |> ProofContext.add_fixes_i fixes |> snd, mode), [])
  | activate_elem _ _ ((ctxt, mode), Constrains _) =
      ((ctxt, mode), [])
  | activate_elem ax_in_ctxt _ ((ctxt, Assumed axs), Assumes asms) =
      let
        val asms' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) asms;
        val ts = maps (map #1 o #2) asms';
        val (ps, qs) = chop (length ts) axs;
        val (_, ctxt') =
          ctxt |> fold Variable.auto_fixes ts
          |> ProofContext.add_assms_i (axioms_export (if ax_in_ctxt then ps else [])) asms';
      in ((ctxt', Assumed qs), []) end
  | activate_elem _ _ ((ctxt, Derived ths), Assumes asms) =
      ((ctxt, Derived ths), [])
  | activate_elem _ _ ((ctxt, Assumed axs), Defines defs) =
      let
        val defs' = Attrib.map_specs (Attrib.attribute_i (ProofContext.theory_of ctxt)) defs;
        val asms = defs' |> map (fn ((name, atts), (t, ps)) =>
            let val ((c, _), t') = LocalDefs.cert_def ctxt t
            in (t', ((Thm.def_name_optional c name, atts), [(t', ps)])) end);
        val (_, ctxt') =
          ctxt |> fold (Variable.auto_fixes o #1) asms
          |> ProofContext.add_assms_i LocalDefs.def_export (map #2 asms);
      in ((ctxt', Assumed axs), []) end
  | activate_elem _ _ ((ctxt, Derived ths), Defines defs) =
      ((ctxt, Derived ths), [])
  | activate_elem _ is_ext ((ctxt, mode), Notes (kind, facts)) =
      let
        val facts' = Attrib.map_facts (Attrib.attribute_i (ProofContext.theory_of ctxt)) facts;
        val (res, ctxt') = ctxt |> ProofContext.note_thmss_i kind facts';
      in ((ctxt', mode), if is_ext then res else []) end;

fun activate_elems ax_in_ctxt (((name, ps), mode), elems) ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val ((ctxt', _), res) =
      foldl_map (activate_elem ax_in_ctxt (name = ""))
        ((ProofContext.qualified_names ctxt, mode), elems)
      handle ERROR msg => err_in_locale ctxt msg [(name, map fst ps)];
    val ctxt'' = if name = "" then ctxt'
          else let
              val ps' = map (fn (n, SOME T) => Free (n, T)) ps;
            in if test_local_registration ctxt' (name, ps') then ctxt'
              else let
                  val ctxt'' = put_local_registration (name, ps') ((true, ""), [])
                    (Morphism.identity, ((Vartab.empty, []), (Vartab.empty, []) )) ctxt'
                in case mode of
                    Assumed axs =>
                      fold (add_local_witness (name, ps') o
                        Element.assume_witness thy o Element.witness_prop) axs ctxt''
                  | Derived ths =>
                     fold (add_local_witness (name, ps')) ths ctxt''
                end
            end
  in (ProofContext.restore_naming ctxt ctxt'', res) end;

fun activate_elemss ax_in_ctxt prep_facts =
    fold_map (fn (((name, ps), mode), raw_elems) => fn ctxt =>
      let
        val elems = map (prep_facts ctxt) raw_elems;
        val (ctxt', res) = apsnd flat
            (activate_elems ax_in_ctxt (((name, ps), mode), elems) ctxt);
        val elems' = elems |> map (Element.map_ctxt_attrib Args.closure);
      in (((((name, ps), mode), elems'), res), ctxt') end);

in

(* CB: activate_facts prep_facts (ctxt, elemss),
   where elemss is a list of pairs consisting of identifiers and
   context elements, extends ctxt by the context elements yielding
   ctxt' and returns (ctxt', (elemss', facts)).
   Identifiers in the argument are of the form ((name, ps), axs) and
   assumptions use the axioms in the identifiers to set up exporters
   in ctxt'.  elemss' does not contain identifiers and is obtained
   from elemss and the intermediate context with prep_facts.
   If read_facts or cert_facts is used for prep_facts, these also remove
   the internal/external markers from elemss. *)

fun activate_facts ax_in_ctxt prep_facts (ctxt, args) =
  let val ((elemss, factss), ctxt') = activate_elemss ax_in_ctxt prep_facts args ctxt |>> split_list
  in (ctxt', (elemss, flat factss)) end;

end;



(** prepare locale elements **)

(* expressions *)

fun intern_expr thy (Locale xname) = Locale (intern thy xname)
  | intern_expr thy (Merge exprs) = Merge (map (intern_expr thy) exprs)
  | intern_expr thy (Rename (expr, xs)) = Rename (intern_expr thy expr, xs);


(* propositions and bindings *)

(* flatten (ctxt, prep_expr) ((ids, syn), expr)
   normalises expr (which is either a locale
   expression or a single context element) wrt.
   to the list ids of already accumulated identifiers.
   It returns ((ids', syn'), elemss) where ids' is an extension of ids
   with identifiers generated for expr, and elemss is the list of
   context elements generated from expr.
   syn and syn' are symtabs mapping parameter names to their syntax.  syn'
   is an extension of syn.
   For details, see flatten_expr.

   Additionally, for a locale expression, the elems are grouped into a single
   Int; individual context elements are marked Ext.  In this case, the
   identifier-like information of the element is as follows:
   - for Fixes: (("", ps), []) where the ps have type info NONE
   - for other elements: (("", []), []).
   The implementation of activate_facts relies on identifier names being
   empty strings for external elements.
*)

fun flatten (ctxt, _) ((ids, syn), Elem (Fixes fixes)) = let
        val ids' = ids @ [(("", map #1 fixes), ([], Assumed []))]
      in
        ((ids',
         merge_syntax ctxt ids'
           (syn, Symtab.make (map (fn fx => (#1 fx, #3 fx)) fixes))
           handle Symtab.DUP x => err_in_locale ctxt
             ("Conflicting syntax for parameter: " ^ quote x)
             (map #1 ids')),
         [((("", map (rpair NONE o #1) fixes), Assumed []), Ext (Fixes fixes))])
      end
  | flatten _ ((ids, syn), Elem elem) =
      ((ids @ [(("", []), ([], Assumed []))], syn), [((("", []), Assumed []), Ext elem)])
  | flatten (ctxt, prep_expr) ((ids, syn), Expr expr) =
      apsnd (map (apsnd Int)) (flatten_expr ctxt ((ids, syn), prep_expr expr));

local

local

fun declare_int_elem (ctxt, Fixes fixes) =
      (ctxt |> ProofContext.add_fixes_i (map (fn (x, T, mx) =>
        (x, Option.map (Term.map_type_tfree (TypeInfer.param 0)) T, mx)) fixes) |> snd, [])
  | declare_int_elem (ctxt, _) = (ctxt, []);

fun declare_ext_elem prep_vars (ctxt, Fixes fixes) =
      let val (vars, _) = prep_vars fixes ctxt
      in (ctxt |> ProofContext.add_fixes_i vars |> snd, []) end
  | declare_ext_elem prep_vars (ctxt, Constrains csts) =
      let val (_, ctxt') = prep_vars (map (fn (x, T) => (x, SOME T, NoSyn)) csts) ctxt
      in (ctxt', []) end
  | declare_ext_elem _ (ctxt, Assumes asms) = (ctxt, map #2 asms)
  | declare_ext_elem _ (ctxt, Defines defs) = (ctxt, map (fn (_, (t, ps)) => [(t, ps)]) defs)
  | declare_ext_elem _ (ctxt, Notes _) = (ctxt, []);

fun declare_elems prep_vars (ctxt, (((name, ps), Assumed _), elems)) =
    let val (ctxt', propps) =
      (case elems of
        Int es => foldl_map declare_int_elem (ctxt, es)
      | Ext e => foldl_map (declare_ext_elem prep_vars) (ctxt, [e]))
      handle ERROR msg => err_in_locale ctxt msg [(name, map fst ps)]
    in (ctxt', propps) end
  | declare_elems _ (ctxt, ((_, Derived _), elems)) = (ctxt, []);

in

fun declare_elemss prep_vars fixed_params raw_elemss ctxt =
  let
    (* CB: fix of type bug of goal in target with context elements.
       Parameters new in context elements must receive types that are
       distinct from types of parameters in target (fixed_params).  *)
    val ctxt_with_fixed =
      fold Variable.declare_term (map Free fixed_params) ctxt;
    val int_elemss =
      raw_elemss
      |> map_filter (fn (id, Int es) => SOME (id, es) | _ => NONE)
      |> unify_elemss ctxt_with_fixed fixed_params;
    val (_, raw_elemss') =
      foldl_map (fn ((_, es) :: elemss, (id, Int _)) => (elemss, (id, Int es)) | x => x)
        (int_elemss, raw_elemss);
  in foldl_map (declare_elems prep_vars) (ctxt, raw_elemss') end;

end;

local

val norm_term = Envir.beta_norm oo Term.subst_atomic;

fun abstract_thm thy eq =
  Thm.assume (Thm.cterm_of thy eq) |> Drule.gen_all |> Drule.abs_def;

fun bind_def ctxt (name, ps) eq (xs, env, ths) =
  let
    val ((y, T), b) = LocalDefs.abs_def eq;
    val b' = norm_term env b;
    val th = abstract_thm (ProofContext.theory_of ctxt) eq;
    fun err msg = err_in_locale ctxt (msg ^ ": " ^ quote y) [(name, map fst ps)];
  in
    exists (equal y o #1) xs andalso
      err "Attempt to define previously specified variable";
    exists (fn (Free (y', _), _) => y = y' | _ => false) env andalso
      err "Attempt to redefine variable";
    (Term.add_frees b' xs, (Free (y, T), b') :: env, th :: ths)
  end;


(* CB: for finish_elems (Int and Ext),
   extracts specification, only of assumed elements *)

fun eval_text _ _ _ (Fixes _) text = text
  | eval_text _ _ _ (Constrains _) text = text
  | eval_text _ (_, Assumed _) is_ext (Assumes asms)
        (((exts, exts'), (ints, ints')), (xs, env, defs)) =
      let
        val ts = maps (map #1 o #2) asms;
        val ts' = map (norm_term env) ts;
        val spec' =
          if is_ext then ((exts @ ts, exts' @ ts'), (ints, ints'))
          else ((exts, exts'), (ints @ ts, ints' @ ts'));
      in (spec', (fold Term.add_frees ts' xs, env, defs)) end
  | eval_text _ (_, Derived _) _ (Assumes _) text = text
  | eval_text ctxt (id, Assumed _) _ (Defines defs) (spec, binds) =
      (spec, fold (bind_def ctxt id o #1 o #2) defs binds)
  | eval_text _ (_, Derived _) _ (Defines _) text = text
  | eval_text _ _ _ (Notes _) text = text;


(* for finish_elems (Int),
   remove redundant elements of derived identifiers,
   turn assumptions and definitions into facts,
   satisfy hypotheses of facts *)

fun finish_derived _ _ (Assumed _) (Fixes fixes) = SOME (Fixes fixes)
  | finish_derived _ _ (Assumed _) (Constrains csts) = SOME (Constrains csts)
  | finish_derived _ _ (Assumed _) (Assumes asms) = SOME (Assumes asms)
  | finish_derived _ _ (Assumed _) (Defines defs) = SOME (Defines defs)

  | finish_derived _ _ (Derived _) (Fixes _) = NONE
  | finish_derived _ _ (Derived _) (Constrains _) = NONE
  | finish_derived sign satisfy (Derived _) (Assumes asms) = asms
      |> map (apsnd (map (fn (a, _) => ([Thm.assume (cterm_of sign a)], []))))
      |> pair Thm.assumptionK |> Notes
      |> Element.morph_ctxt satisfy |> SOME
  | finish_derived sign satisfy (Derived _) (Defines defs) = defs
      |> map (apsnd (fn (d, _) => [([Thm.assume (cterm_of sign d)], [])]))
      |> pair Thm.definitionK |> Notes
      |> Element.morph_ctxt satisfy |> SOME

  | finish_derived _ satisfy _ (Notes facts) = Notes facts
      |> Element.morph_ctxt satisfy |> SOME;

(* CB: for finish_elems (Ext) *)

fun closeup _ false elem = elem
  | closeup ctxt true elem =
      let
        fun close_frees t =
          let
            val rev_frees =
              Term.fold_aterms (fn Free (x, T) =>
                if Variable.is_fixed ctxt x then I else insert (op =) (x, T) | _ => I) t [];
          in Term.list_all_free (rev rev_frees, t) end;

        fun no_binds [] = []
          | no_binds _ = error "Illegal term bindings in locale element";
      in
        (case elem of
          Assumes asms => Assumes (asms |> map (fn (a, propps) =>
            (a, map (fn (t, ps) => (close_frees t, no_binds ps)) propps)))
        | Defines defs => Defines (defs |> map (fn (a, (t, ps)) =>
            (a, (close_frees (#2 (LocalDefs.cert_def ctxt t)), no_binds ps))))
        | e => e)
      end;


fun finish_ext_elem parms _ (Fixes fixes, _) = Fixes (map (fn (x, _, mx) =>
      (x, AList.lookup (op =) parms x, mx)) fixes)
  | finish_ext_elem parms _ (Constrains _, _) = Constrains []
  | finish_ext_elem _ close (Assumes asms, propp) =
      close (Assumes (map #1 asms ~~ propp))
  | finish_ext_elem _ close (Defines defs, propp) =
      close (Defines (map #1 defs ~~ map (fn [(t, ps)] => (t, ps)) propp))
  | finish_ext_elem _ _ (Notes facts, _) = Notes facts;


(* CB: finish_parms introduces type info from parms to identifiers *)
(* CB: only needed for types that have been NONE so far???
   If so, which are these??? *)

fun finish_parms parms (((name, ps), mode), elems) =
  (((name, map (fn (x, _) => (x, AList.lookup (op = : string * string -> bool) parms x)) ps), mode), elems);

fun finish_elems ctxt parms _ ((text, wits), ((id, Int e), _)) =
      let
        val [(id' as (_, mode), es)] = unify_elemss ctxt parms [(id, e)];
        val wits' = case mode of Assumed _ => wits | Derived ths => wits @ ths;
        val text' = fold (eval_text ctxt id' false) es text;
        val es' = map_filter
          (finish_derived (ProofContext.theory_of ctxt) (Element.satisfy_morphism wits') mode) es;
      in ((text', wits'), (id', map Int es')) end
  | finish_elems ctxt parms do_close ((text, wits), ((id, Ext e), [propp])) =
      let
        val e' = finish_ext_elem parms (closeup ctxt do_close) (e, propp);
        val text' = eval_text ctxt id true e' text;
      in ((text', wits), (id, [Ext e'])) end

in

(* CB: only called by prep_elemss *)

fun finish_elemss ctxt parms do_close =
  foldl_map (apsnd (finish_parms parms) o finish_elems ctxt parms do_close);

end;


(* Remove duplicate Defines elements: temporary workaround to fix Afp/Category. *)

fun defs_ord (defs1, defs2) =
    list_ord (fn ((_, (d1, _)), (_, (d2, _))) =>
      Term.fast_term_ord (d1, d2)) (defs1, defs2);
structure Defstab =
    TableFun(type key = ((string * Attrib.src list) * (term * term list)) list
        val ord = defs_ord);

fun rem_dup_defs es ds =
    fold_map (fn e as (Defines defs) => (fn ds =>
                 if Defstab.defined ds defs
                 then (Defines [], ds)
                 else (e, Defstab.update (defs, ()) ds))
               | e => (fn ds => (e, ds))) es ds;
fun rem_dup_elemss (Int es) ds = apfst Int (rem_dup_defs es ds)
  | rem_dup_elemss (Ext e) ds = (Ext e, ds);
fun rem_dup_defines raw_elemss =
    fold_map (fn (id as (_, (Assumed _)), es) => (fn ds =>
                     apfst (pair id) (rem_dup_elemss es ds))
               | (id as (_, (Derived _)), es) => (fn ds =>
                     ((id, es), ds))) raw_elemss Defstab.empty |> #1;

(* CB: type inference and consistency checks for locales.

   Works by building a context (through declare_elemss), extracting the
   required information and adjusting the context elements (finish_elemss).
   Can also universally close free vars in assms and defs.  This is only
   needed for Ext elements and controlled by parameter do_close.

   Only elements of assumed identifiers are considered.
*)

fun prep_elemss prep_vars prepp do_close context fixed_params raw_elemss raw_concl =
  let
    (* CB: contexts computed in the course of this function are discarded.
       They are used for type inference and consistency checks only. *)
    (* CB: fixed_params are the parameters (with types) of the target locale,
       empty list if there is no target. *)
    (* CB: raw_elemss are list of pairs consisting of identifiers and
       context elements, the latter marked as internal or external. *)
    val raw_elemss = rem_dup_defines raw_elemss;
    val (raw_ctxt, raw_proppss) = declare_elemss prep_vars fixed_params raw_elemss context;
    (* CB: raw_ctxt is context with additional fixed variables derived from
       the fixes elements in raw_elemss,
       raw_proppss contains assumptions and definitions from the
       external elements in raw_elemss. *)
    fun prep_prop raw_propp (raw_ctxt, raw_concl)  =
      let
        (* CB: add type information from fixed_params to context (declare_term) *)
        (* CB: process patterns (conclusion and external elements only) *)
        val (ctxt, all_propp) =
          prepp (fold Variable.declare_term (map Free fixed_params) raw_ctxt, raw_concl @ raw_propp);
        (* CB: add type information from conclusion and external elements to context *)
        val ctxt = fold Variable.declare_term (maps (map fst) all_propp) ctxt;
        (* CB: resolve schematic variables (patterns) in conclusion and external elements. *)
        val all_propp' = map2 (curry (op ~~))
          (#1 (#2 (ProofContext.bind_propp_schematic_i (ctxt, all_propp)))) (map (map snd) all_propp);
        val (concl, propp) = chop (length raw_concl) all_propp';
      in (propp, (ctxt, concl)) end

    val (proppss, (ctxt, concl)) =
      (fold_burrow o fold_burrow) prep_prop raw_proppss (raw_ctxt, raw_concl);

    (* CB: obtain all parameters from identifier part of raw_elemss *)
    val xs = map #1 (params_of' raw_elemss);
    val typing = unify_frozen ctxt 0
      (map (Variable.default_type raw_ctxt) xs)
      (map (Variable.default_type ctxt) xs);
    val parms = param_types (xs ~~ typing);
    (* CB: parms are the parameters from raw_elemss, with correct typing. *)

    (* CB: extract information from assumes and defines elements
       (fixes, constrains and notes in raw_elemss don't have an effect on
       text and elemss), compute final form of context elements. *)
    val ((text, _), elemss) = finish_elemss ctxt parms do_close
      ((((([], []), ([], [])), ([], [], [])), []), raw_elemss ~~ proppss);
    (* CB: text has the following structure:
           (((exts, exts'), (ints, ints')), (xs, env, defs))
       where
         exts: external assumptions (terms in external assumes elements)
         exts': dito, normalised wrt. env
         ints: internal assumptions (terms in internal assumes elements)
         ints': dito, normalised wrt. env
         xs: the free variables in exts' and ints' and rhss of definitions,
           this includes parameters except defined parameters
         env: list of term pairs encoding substitutions, where the first term
           is a free variable; substitutions represent defines elements and
           the rhs is normalised wrt. the previous env
         defs: theorems representing the substitutions from defines elements
           (thms are normalised wrt. env).
       elemss is an updated version of raw_elemss:
         - type info added to Fixes and modified in Constrains
         - axiom and definition statement replaced by corresponding one
           from proppss in Assumes and Defines
         - Facts unchanged
       *)
  in ((parms, elemss, concl), text) end;

in

fun read_elemss x = prep_elemss ProofContext.read_vars ProofContext.read_propp_schematic x;
fun cert_elemss x = prep_elemss ProofContext.cert_vars ProofContext.cert_propp_schematic x;

end;


(* facts and attributes *)

local

fun check_name name =
  if NameSpace.is_qualified name then error ("Illegal qualified name: " ^ quote name)
  else name;

fun prep_facts _ _ _ ctxt (Int elem) = elem
      |> Element.morph_ctxt (Morphism.thm_morphism (Thm.transfer (ProofContext.theory_of ctxt)))
  | prep_facts prep_name get intern ctxt (Ext elem) = elem |> Element.map_ctxt
     {var = I, typ = I, term = I,
      name = prep_name,
      fact = get ctxt,
      attrib = Args.assignable o intern (ProofContext.theory_of ctxt)};

in

fun read_facts x = prep_facts check_name ProofContext.get_fact Attrib.intern_src x;
fun cert_facts x = prep_facts I (K I) (K I) x;

end;


(* Get the specification of a locale *)

(*The global specification is made from the parameters and global
  assumptions, the local specification from the parameters and the
  local assumptions.*)

local

fun gen_asms_of get thy name =
  let
    val ctxt = ProofContext.init thy;
    val (_, raw_elemss) = flatten (ctxt, I) (([], Symtab.empty), Expr (Locale name));
    val ((_, elemss, _), _) = read_elemss false ctxt [] raw_elemss [];
  in
    elemss |> get
      |> maps (fn (_, es) => map (fn Int e => e) es)
      |> maps (fn Assumes asms => asms | _ => [])
      |> map (apsnd (map fst))
  end;

in

fun parameters_of thy = #params o the_locale thy;

fun intros thy = #intros o the_locale thy;
  (*returns introduction rule for delta predicate and locale predicate
    as a pair of singleton lists*)

fun dests thy = #dests o the_locale thy;


fun parameters_of_expr thy expr =
  let
    val ctxt = ProofContext.init thy;
    val pts = params_of_expr ctxt [] (intern_expr thy expr)
        ([], Symtab.empty, Symtab.empty);
    val raw_params_elemss = make_raw_params_elemss pts;
    val ((_, syn), raw_elemss) = flatten (ctxt, intern_expr thy)
        (([], Symtab.empty), Expr expr);
    val ((parms, _, _), _) =
        read_elemss false ctxt [] (raw_params_elemss @ raw_elemss) [];
  in map (fn p as (n, _) => (p, Symtab.lookup syn n |> the)) parms end;

fun local_asms_of thy name =
  gen_asms_of (single o Library.last_elem) thy name;

fun global_asms_of thy name =
  gen_asms_of I thy name;

end;


(* full context statements: imports + elements + conclusion *)

local

fun prep_context_statement prep_expr prep_elemss prep_facts
    do_close fixed_params imports elements raw_concl context =
  let
    val thy = ProofContext.theory_of context;

    val (import_params, import_tenv, import_syn) =
      params_of_expr context fixed_params (prep_expr thy imports)
        ([], Symtab.empty, Symtab.empty);
    val includes = map_filter (fn Expr e => SOME e | Elem _ => NONE) elements;
    val (incl_params, incl_tenv, incl_syn) = fold (params_of_expr context fixed_params)
      (map (prep_expr thy) includes) (import_params, import_tenv, import_syn);

    val ((import_ids, _), raw_import_elemss) =
      flatten (context, prep_expr thy) (([], Symtab.empty), Expr imports);
    (* CB: normalise "includes" among elements *)
    val ((ids, syn), raw_elemsss) = foldl_map (flatten (context, prep_expr thy))
      ((import_ids, incl_syn), elements);

    val raw_elemss = flat raw_elemsss;
    (* CB: raw_import_elemss @ raw_elemss is the normalised list of
       context elements obtained from import and elements. *)
    (* Now additional elements for parameters are inserted. *)
    val import_params_ids = make_params_ids import_params;
    val incl_params_ids =
        make_params_ids (incl_params \\ import_params);
    val raw_import_params_elemss =
        make_raw_params_elemss (import_params, incl_tenv, incl_syn);
    val raw_incl_params_elemss =
        make_raw_params_elemss (incl_params \\ import_params, incl_tenv, incl_syn);
    val ((parms, all_elemss, concl), (spec, (_, _, defs))) = prep_elemss do_close
      context fixed_params
      (raw_import_params_elemss @ raw_import_elemss @ raw_incl_params_elemss @ raw_elemss) raw_concl;

    (* replace extended ids (for axioms) by ids *)
    val (import_ids', incl_ids) = chop (length import_ids) ids;
    val all_ids = import_params_ids @ import_ids' @ incl_params_ids @ incl_ids;
    val all_elemss' = map (fn (((_, ps), _), (((n, ps'), mode), elems)) =>
        (((n, map (fn p => (p, (the o AList.lookup (op =) ps') p)) ps), mode), elems))
      (all_ids ~~ all_elemss);
    (* CB: all_elemss and parms contain the correct parameter types *)

    val (ps, qs) = chop (length raw_import_params_elemss + length raw_import_elemss) all_elemss';
    val (import_ctxt, (import_elemss, _)) =
      activate_facts false prep_facts (context, ps);

    val (ctxt, (elemss, _)) =
      activate_facts false prep_facts (ProofContext.set_stmt true import_ctxt, qs);
  in
    ((((import_ctxt, import_elemss), (ctxt, elemss, syn)),
      (parms, spec, defs)), concl)
  end;

fun prep_statement prep_locale prep_ctxt raw_locale elems concl ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val locale = Option.map (prep_locale thy) raw_locale;
    val (fixed_params, imports) =
      (case locale of
        NONE => ([], empty)
      | SOME name =>
          let val {params = ps, ...} = the_locale thy name
          in (map fst ps, Locale name) end);
    val ((((locale_ctxt, _), (elems_ctxt, _, _)), _), concl') =
      prep_ctxt false fixed_params imports elems concl ctxt;
  in (locale, locale_ctxt, elems_ctxt, concl') end;

fun prep_expr prep imports body ctxt =
  let
    val (((_, import_elemss), (ctxt', elemss, _)), _) = prep imports body ctxt;
    val all_elems = maps snd (import_elemss @ elemss);
  in (all_elems, ctxt') end;

in

val read_ctxt = prep_context_statement intern_expr read_elemss read_facts;
val cert_ctxt = prep_context_statement (K I) cert_elemss cert_facts;

fun read_context imports body ctxt = #1 (read_ctxt true [] imports (map Elem body) [] ctxt);
fun cert_context imports body ctxt = #1 (cert_ctxt true [] imports (map Elem body) [] ctxt);

val read_expr = prep_expr read_context;
val cert_expr = prep_expr cert_context;

fun read_context_statement loc = prep_statement intern read_ctxt loc;
fun read_context_statement_i loc = prep_statement (K I) read_ctxt loc;
fun cert_context_statement loc = prep_statement (K I) cert_ctxt loc;

end;


(* init *)

fun init loc =
  ProofContext.init
  #> #2 o cert_context_statement (SOME loc) [] [];


(* print locale *)

fun print_locale thy show_facts imports body =
  let val (all_elems, ctxt) = read_expr imports body (ProofContext.init thy) in
    Pretty.big_list "locale elements:" (all_elems
      |> (if show_facts then I else filter (fn Notes _ => false | _ => true))
      |> map (Element.pretty_ctxt ctxt) |> filter_out null
      |> map Pretty.chunks)
    |> Pretty.writeln
  end;



(** store results **)

(* naming of interpreted theorems *)

fun global_note_prefix_i kind loc (fully_qualified, prfx) args thy =
  thy
  |> Sign.qualified_names
  |> Sign.add_path (NameSpace.base loc ^ "_locale")
  |> (if fully_qualified then Sign.sticky_prefix prfx else Sign.add_path prfx)
  |> PureThy.note_thmss_i kind args
  ||> Sign.restore_naming thy;

fun local_note_prefix_i kind loc (fully_qualified, prfx) args ctxt =
  ctxt
  |> ProofContext.qualified_names
  |> ProofContext.add_path (NameSpace.base loc ^ "_locale")
  |> (if fully_qualified then ProofContext.sticky_prefix prfx else ProofContext.add_path prfx)
  |> ProofContext.note_thmss_i kind args
  ||> ProofContext.restore_naming ctxt;


(* join equations of an id with already accumulated ones *)

fun join_eqns get_reg prep_id ctxt id eqns =
  let
    val id' = prep_id id
    val eqns' = case get_reg id'
      of NONE => eqns
	| SOME (_, _, eqns') => Termtab.join (fn t => fn (_, e) => e) (eqns, eqns')
            handle Termtab.DUP t =>
	      error ("Conflicting interpreting equations for term " ^
		quote (Syntax.string_of_term ctxt t))
  in ((id', eqns'), eqns') end;


(* collect witnesses and equations up to a particular target for global
   registration; requires parameters and flattened list of identifiers
   instead of recomputing it from the target *)

fun collect_global_witnesses thy imprt parms ids vts = let
    val ts = map Logic.unvarify vts;
    val (parms, parmTs) = split_list parms;
    val parmvTs = map Logic.varifyT parmTs;
    val vtinst = fold (Sign.typ_match thy) (parmvTs ~~ map Term.fastype_of ts) Vartab.empty;
    val tinst = Vartab.dest vtinst |> map (fn ((x, 0), (_, T)) => (x, T))
        |> Symtab.make;
    (* replace parameter names in ids by instantiations *)
    val vinst = Symtab.make (parms ~~ vts);
    fun vinst_names ps = map (the o Symtab.lookup vinst) ps;
    val inst = Symtab.make (parms ~~ ts);
    val inst_ids = map (apfst (apsnd vinst_names)) ids;
    val assumed_ids' = map_filter (fn (id, (_, Assumed _)) => SOME id | _ => NONE) inst_ids;
    val wits = maps (#2 o the o get_global_registration thy imprt) assumed_ids';

    val ids' = map fst inst_ids;
    val eqns =
      fold_map (join_eqns (get_global_registration thy imprt) I (ProofContext.init thy))
        ids' Termtab.empty |> snd |> Termtab.dest |> map snd;
  in ((tinst, inst), wits, eqns) end;


(* standardise export morphism *)

(* clone from Element.generalize_facts *)
fun standardize thy export facts =
  let
    val exp_fact = Drule.zero_var_indexes_list o map Thm.strip_shyps o Morphism.fact export;
    val exp_term = TermSubst.zero_var_indexes o Morphism.term export;
      (* FIXME sync with exp_fact *)
    val exp_typ = Logic.type_map exp_term;
    val morphism =
      Morphism.morphism {name = I, var = I, typ = exp_typ, term = exp_term, fact = exp_fact};
  in Element.facts_map (Element.morph_ctxt morphism) facts end;


(* suppress application of name morphism: workaroud for class package *) (* FIXME *)

fun morph_ctxt' phi = Element.map_ctxt
  {name = I,
   var = Morphism.var phi,
   typ = Morphism.typ phi,
   term = Morphism.term phi,
   fact = Morphism.fact phi,
   attrib = Args.morph_values phi};


(* compute morphism and apply to args *)

fun interpret_args thy prfx insts prems eqns atts2 exp attrib args =
  let
    val inst = Morphism.name_morphism (NameSpace.qualified prfx) $>
      Element.inst_morphism thy insts $> Element.satisfy_morphism prems $>
      Morphism.term_morphism (MetaSimplifier.rewrite_term thy eqns []) $>
      Morphism.thm_morphism (MetaSimplifier.rewrite_rule eqns)
  in
    args |> Element.facts_map (morph_ctxt' inst) |>
      map (fn (attn, bs) => (attn,
        bs |> map (fn (ths, atts) => (ths, (atts @ atts2))))) |>
      standardize thy exp |> Attrib.map_facts attrib
  end;


(* store instantiations of args for all registered interpretations
   of the theory *)

fun note_thmss_registrations target (kind, args) thy =
  let
    val parms = the_locale thy target |> #params |> map fst;
    val ids = flatten (ProofContext.init thy, intern_expr thy)
      (([], Symtab.empty), Expr (Locale target)) |> fst |> fst;

    val regs = get_global_registrations thy target;
    (* add args to thy for all registrations *)

    fun activate (vts, (((fully_qualified, prfx), atts2), (exp, imp), _, _)) thy =
      let
        val (insts, prems, eqns) = collect_global_witnesses thy imp parms ids vts;
        val attrib = Attrib.attribute_i thy;
        val args' = interpret_args thy prfx insts prems eqns atts2 exp attrib args;
      in global_note_prefix_i kind target (fully_qualified, prfx) args' thy |> snd end;
  in fold activate regs thy end;


(* locale results *)

fun add_thmss loc kind args ctxt =
  let
    val (ctxt', ([(_, [Notes args'])], _)) =
      activate_facts true cert_facts
        (ctxt, [((("", []), Assumed []), [Ext (Notes (kind, args))])]);
    val ctxt'' = ctxt' |> ProofContext.theory
      (change_locale loc
        (fn (axiom, imports, elems, params, lparams, decls, regs, intros, dests) =>
          (axiom, imports, elems @ [(Notes args', stamp ())],
            params, lparams, decls, regs, intros, dests))
      #> note_thmss_registrations loc args');
  in ctxt'' end;


(* declarations *)

local

fun decl_attrib decl phi = Thm.declaration_attribute (K (decl phi));

fun add_decls add loc decl =
  ProofContext.theory (change_locale loc
    (fn (axiom, imports, elems, params, lparams, decls, regs, intros, dests) =>
      (axiom, imports, elems, params, lparams, add (decl, stamp ()) decls, regs, intros, dests))) #>
  add_thmss loc Thm.internalK
    [(("", [Attrib.internal (decl_attrib decl)]), [([Drule.dummy_thm], [])])];

in

val add_type_syntax = add_decls (apfst o cons);
val add_term_syntax = add_decls (apsnd o cons);
val add_declaration = add_decls (K I);

end;



(** define locales **)

(* predicate text *)
(* CB: generate locale predicates and delta predicates *)

local

(* introN: name of theorems for introduction rules of locale and
     delta predicates;
   axiomsN: name of theorem set with destruct rules for locale predicates,
     also name suffix of delta predicates. *)

val introN = "intro";
val axiomsN = "axioms";

fun atomize_spec thy ts =
  let
    val t = Logic.mk_conjunction_balanced ts;
    val body = ObjectLogic.atomize_term thy t;
    val bodyT = Term.fastype_of body;
  in
    if bodyT = propT then (t, propT, Thm.reflexive (Thm.cterm_of thy t))
    else (body, bodyT, ObjectLogic.atomize (Thm.cterm_of thy t))
  end;

fun aprop_tr' n c = (Syntax.constN ^ c, fn ctxt => fn args =>
  if length args = n then
    Syntax.const "_aprop" $
      Term.list_comb (Syntax.free (Consts.extern (ProofContext.consts_of ctxt) c), args)
  else raise Match);

(* CB: define one predicate including its intro rule and axioms
   - bname: predicate name
   - parms: locale parameters
   - defs: thms representing substitutions from defines elements
   - ts: terms representing locale assumptions (not normalised wrt. defs)
   - norm_ts: terms representing locale assumptions (normalised wrt. defs)
   - thy: the theory
*)

fun def_pred bname parms defs ts norm_ts thy =
  let
    val name = Sign.full_name thy bname;

    val (body, bodyT, body_eq) = atomize_spec thy norm_ts;
    val env = Term.add_term_free_names (body, []);
    val xs = filter (member (op =) env o #1) parms;
    val Ts = map #2 xs;
    val extraTs = (Term.term_tfrees body \\ List.foldr Term.add_typ_tfrees [] Ts)
      |> Library.sort_wrt #1 |> map TFree;
    val predT = map Term.itselfT extraTs ---> Ts ---> bodyT;

    val args = map Logic.mk_type extraTs @ map Free xs;
    val head = Term.list_comb (Const (name, predT), args);
    val statement = ObjectLogic.ensure_propT thy head;

    val ([pred_def], defs_thy) =
      thy
      |> bodyT = propT ? Sign.add_advanced_trfuns ([], [], [aprop_tr' (length args) name], [])
      |> Sign.declare_const [] (bname, predT, NoSyn) |> snd
      |> PureThy.add_defs_i false
        [((Thm.def_name bname, Logic.mk_equals (head, body)), [PureThy.kind_internal])];
    val defs_ctxt = ProofContext.init defs_thy |> Variable.declare_term head;

    val cert = Thm.cterm_of defs_thy;

    val intro = Goal.prove_global defs_thy [] norm_ts statement (fn _ =>
      MetaSimplifier.rewrite_goals_tac [pred_def] THEN
      Tactic.compose_tac (false, body_eq RS Drule.equal_elim_rule1, 1) 1 THEN
      Tactic.compose_tac (false,
        Conjunction.intr_balanced (map (Thm.assume o cert) norm_ts), 0) 1);

    val conjuncts =
      (Drule.equal_elim_rule2 OF [body_eq,
        MetaSimplifier.rewrite_rule [pred_def] (Thm.assume (cert statement))])
      |> Conjunction.elim_balanced (length ts);
    val axioms = ts ~~ conjuncts |> map (fn (t, ax) =>
      Element.prove_witness defs_ctxt t
       (MetaSimplifier.rewrite_goals_tac defs THEN
        Tactic.compose_tac (false, ax, 0) 1));
  in ((statement, intro, axioms), defs_thy) end;

fun assumes_to_notes (Assumes asms) axms =
      fold_map (fn (a, spec) => fn axs =>
          let val (ps, qs) = chop (length spec) axs
          in ((a, [(ps, [])]), qs) end) asms axms
      |> apfst (curry Notes Thm.assumptionK)
  | assumes_to_notes e axms = (e, axms);

(* CB: the following two change only "new" elems, these have identifier ("", _). *)

(* turn Assumes into Notes elements *)

fun change_assumes_elemss axioms elemss =
  let
    val satisfy = Element.morph_ctxt (Element.satisfy_morphism axioms);
    fun change (id as ("", _), es) =
          fold_map assumes_to_notes (map satisfy es)
          #-> (fn es' => pair (id, es'))
      | change e = pair e;
  in
    fst (fold_map change elemss (map Element.conclude_witness axioms))
  end;

(* adjust hyps of Notes elements *)

fun change_elemss_hyps axioms elemss =
  let
    val satisfy = Element.morph_ctxt (Element.satisfy_morphism axioms);
    fun change (id as ("", _), es) = (id, map (fn e as Notes _ => satisfy e | e => e) es)
      | change e = e;
  in map change elemss end;

in

(* CB: main predicate definition function *)

fun define_preds pname (parms, ((exts, exts'), (ints, ints')), defs) elemss thy =
  let
    val ((elemss', more_ts), a_elem, a_intro, thy'') =
      if null exts then ((elemss, []), [], [], thy)
      else
        let
          val aname = if null ints then pname else pname ^ "_" ^ axiomsN;
          val ((statement, intro, axioms), thy') =
            thy
            |> def_pred aname parms defs exts exts';
          val elemss' = change_assumes_elemss axioms elemss;
          val a_elem = [(("", []), [Assumes [((pname ^ "_" ^ axiomsN, []), [(statement, [])])]])];
          val (_, thy'') =
            thy'
            |> PureThy.note_thmss_qualified Thm.internalK aname [((introN, []), [([intro], [])])];
        in ((elemss', [statement]), a_elem, [intro], thy'') end;
    val (predicate, stmt', elemss'', b_intro, thy'''') =
      if null ints then (([], []), more_ts, elemss' @ a_elem, [], thy'')
      else
        let
          val ((statement, intro, axioms), thy''') =
            thy''
            |> def_pred pname parms defs (ints @ more_ts) (ints' @ more_ts);
          val cstatement = Thm.cterm_of thy''' statement;
          val elemss'' = change_elemss_hyps axioms elemss';
          val b_elem = [(("", []),
               [Assumes [((pname ^ "_" ^ axiomsN, []), [(statement, [])])]])];
          val (_, thy'''') =
            thy'''
            |> PureThy.note_thmss_qualified Thm.internalK pname
                 [((introN, []), [([intro], [])]),
                  ((axiomsN, []), [(map (Drule.standard o Element.conclude_witness) axioms, [])])];
        in (([cstatement], axioms), [statement], elemss'' @ b_elem, [intro], thy'''') end;
  in (((elemss'', predicate, stmt'), (a_intro, b_intro)), thy'''') end;

end;


(* add_locale(_i) *)

local

(* turn Defines into Notes elements, accumulate definition terms *)

fun defines_to_notes is_ext thy (Defines defs) defns =
    let
      val defs' = map (fn (_, (def, _)) => (("", []), (def, []))) defs
      val notes = map (fn (a, (def, _)) =>
        (a, [([assume (cterm_of thy def)], [])])) defs
    in
      (if is_ext then SOME (Notes (Thm.definitionK, notes)) else NONE, defns @ [Defines defs'])
    end
  | defines_to_notes _ _ e defns = (SOME e, defns);

fun change_defines_elemss thy elemss defns =
  let
    fun change (id as (n, _), es) defns =
        let
          val (es', defns') = fold_map (defines_to_notes (n="") thy) es defns
        in ((id, map_filter I es'), defns') end
  in fold_map change elemss defns end;

fun gen_add_locale prep_ctxt prep_expr
    predicate_name bname raw_imports raw_body thy =
    (* predicate_name: NONE - open locale without predicate
        SOME "" - locale with predicate named as locale
        SOME "name" - locale with predicate named "name" *)
  let
    val name = Sign.full_name thy bname;
    val _ = is_some (get_locale thy name) andalso
      error ("Duplicate definition of locale " ^ quote name);

    val thy_ctxt = ProofContext.init thy;
    val (((import_ctxt, import_elemss), (body_ctxt, body_elemss, syn)),
      text as (parms, ((_, exts'), _), defs)) =
      prep_ctxt raw_imports raw_body thy_ctxt;
    val elemss = import_elemss @ body_elemss |>
        map_filter (fn ((id, Assumed axs), elems) => SOME (id, elems) | _ => NONE);
    val imports = prep_expr thy raw_imports;

    val extraTs = List.foldr Term.add_term_tfrees [] exts' \\
      List.foldr Term.add_typ_tfrees [] (map snd parms);
    val _ = if null extraTs then ()
      else warning ("Additional type variable(s) in locale specification " ^ quote bname);

    val ((((elemss', predicate as (predicate_statement, predicate_axioms), stmt'), intros),
          pred_thy), (imports, regs)) =
      case predicate_name
       of SOME predicate_name =>
            let
              val predicate_name' = case predicate_name of "" => bname | _ => predicate_name;
              val (elemss', defns) = change_defines_elemss thy elemss [];
              val elemss'' = elemss' @ [(("", []), defns)];
              val (((elemss''', predicate as (_, axioms), stmt'), intros), thy') =
                define_preds predicate_name' text elemss'' thy;
              fun mk_regs elemss wits =
                fold_map (fn (id, elems) => fn wts => let
                    val ts = List.concat (List.mapPartial (fn (Assumes asms) =>
                      SOME (List.concat (map (map #1 o #2) asms)) | _ => NONE) elems);
                    val (wts1, wts2) = chop (length ts) wts
                  in ((apsnd (map fst) id, wts1), wts2) end) elemss wits |> fst;
              val regs = mk_regs elemss''' axioms |>
                    map_filter (fn (("", _), _) => NONE | e => SOME e);
            in ((((elemss''', predicate, stmt'), intros), thy'), (empty, regs)) end
        | NONE => ((((elemss, ([], []), []), ([], [])), thy), (imports, []));

    fun axiomify axioms elemss =
      (axioms, elemss) |> foldl_map (fn (axs, (id, elems)) => let
                   val ts = flat (map_filter (fn (Assumes asms) =>
                     SOME (maps (map #1 o #2) asms) | _ => NONE) elems);
                   val (axs1, axs2) = chop (length ts) axs;
                 in (axs2, ((id, Assumed axs1), elems)) end)
        |> snd;
    val (ctxt, (_, facts)) = activate_facts true (K I)
      (ProofContext.init pred_thy, axiomify predicate_axioms elemss');
    val view_ctxt = Assumption.add_view thy_ctxt predicate_statement ctxt;
    val export = Thm.close_derivation o Goal.norm_result o
      singleton (ProofContext.export view_ctxt thy_ctxt);
    val facts' = facts |> map (fn (a, ths) => ((a, []), [(map export ths, [])]));
    val elems' = maps #2 (filter (equal "" o #1 o #1) elemss');
    val elems'' = map_filter (fn (Fixes _) => NONE | e => SOME e) elems';
    val axs' = map (Element.assume_witness pred_thy) stmt';
    val loc_ctxt = pred_thy
      |> PureThy.note_thmss_qualified Thm.assumptionK bname facts' |> snd
      |> declare_locale name
      |> put_locale name
       {axiom = axs',
        imports = imports,
        elems = map (fn e => (e, stamp ())) elems'',
        params = params_of elemss' |> map (fn (x, SOME T) => ((x, T), the (Symtab.lookup syn x))),
        lparams = map #1 (params_of' body_elemss),
        decls = ([], []),
        regs = regs,
        intros = intros,
        dests = map Element.conclude_witness predicate_axioms}
      |> init name;
  in (name, loc_ctxt) end;

in

val add_locale = gen_add_locale read_context intern_expr;
val add_locale_i = gen_add_locale cert_context (K I);

end;

val _ = Context.>> (Context.map_theory
 (add_locale_i (SOME "") "var" empty [Fixes [(Name.internal "x", NONE, NoSyn)]] #>
  snd #> ProofContext.theory_of #>
  add_locale_i (SOME "") "struct" empty [Fixes [(Name.internal "S", NONE, Structure)]] #>
  snd #> ProofContext.theory_of));




(** Normalisation of locale statements ---
    discharges goals implied by interpretations **)

local

fun locale_assm_intros thy =
  Symtab.fold (fn (_, {intros = (a, _), ...}) => fn intros => (a @ intros))
    (#2 (LocalesData.get thy)) [];
fun locale_base_intros thy =
  Symtab.fold (fn (_, {intros = (_, b), ...}) => fn intros => (b @ intros))
    (#2 (LocalesData.get thy)) [];

fun all_witnesses ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    fun get registrations = Symtab.fold (fn (_, regs) => fn thms =>
        (Registrations.dest thy regs |> map (fn (_, (_, (exp, _), wits, _)) =>
          map (Element.conclude_witness #> Morphism.thm exp) wits) |> flat) @ thms)
      registrations [];
  in get (RegistrationsData.get (Context.Proof ctxt)) end;

in

fun intro_locales_tac eager ctxt facts st =
  let
    val wits = all_witnesses ctxt;
    val thy = ProofContext.theory_of ctxt;
    val intros = locale_base_intros thy @ (if eager then locale_assm_intros thy else []);
  in
    Method.intros_tac (wits @ intros) facts st
  end;

val _ = Context.>> (Context.map_theory
  (Method.add_methods
    [("intro_locales",
      Method.ctxt_args (fn ctxt => Method.METHOD (intro_locales_tac false ctxt)),
      "back-chain introduction rules of locales without unfolding predicates"),
     ("unfold_locales",
      Method.ctxt_args (fn ctxt => Method.METHOD (intro_locales_tac true ctxt)),
      "back-chain all introduction rules of locales")]));

end;


(** Interpretation commands **)

local

(* extract proof obligations (assms and defs) from elements *)

fun extract_asms_elems ((id, Assumed _), elems) = (id, maps Element.prems_of elems)
  | extract_asms_elems ((id, Derived _), _) = (id, []);


(* activate instantiated facts in theory or context *)

structure Idtab =
  TableFun(type key = string * term list
    val ord = prod_ord string_ord (list_ord Term.fast_term_ord));

fun gen_activate_facts_elemss mk_ctxt get_reg note note_interp attrib put_reg add_wit add_eqn
        attn all_elemss new_elemss propss eq_attns (exp, imp) thmss thy_ctxt =
  let
    val ctxt = mk_ctxt thy_ctxt;
    val (propss, eq_props) = chop (length new_elemss) propss;
    val (thmss, eq_thms) = chop (length new_elemss) thmss;

    fun activate_elem prems eqns exp loc ((fully_qualified, prfx), atts) (Notes (kind, facts)) thy_ctxt =
        let
          val ctxt = mk_ctxt thy_ctxt;
          val facts' = interpret_args (ProofContext.theory_of ctxt) prfx
              (Symtab.empty, Symtab.empty) prems eqns atts
              exp (attrib thy_ctxt) facts;
        in snd (note_interp kind loc (fully_qualified, prfx) facts' thy_ctxt) end
      | activate_elem _ _ _ _ _ _ thy_ctxt = thy_ctxt;

    fun activate_elems prems eqns exp ((id, _), elems) thy_ctxt =
      let
        val (prfx_atts, _, _) = case get_reg thy_ctxt imp id
         of SOME x => x
          | NONE => sys_error ("Unknown registration of " ^ quote (fst id)
              ^ " while activating facts.");
      in fold (activate_elem prems (the (Idtab.lookup eqns id)) exp (fst id) prfx_atts) elems thy_ctxt end;

    val thy_ctxt' = thy_ctxt
      (* add registrations *)
      |> fold (fn ((id, _), _) => put_reg id attn (exp, imp)) new_elemss
      (* add witnesses of Assumed elements (only those generate proof obligations) *)
      |> fold (fn (id, thms) => fold (add_wit id) thms) (map fst propss ~~ thmss)
      (* add equations *)
      |> fold (fn (id, thms) => fold (add_eqn id) thms) (map fst eq_props ~~
          (map o map) (Drule.abs_def o LocalDefs.meta_rewrite_rule ctxt o
            Element.conclude_witness) eq_thms);

    val prems = flat (map_filter
          (fn ((id, Assumed _), _) => Option.map #2 (get_reg thy_ctxt' imp id)
            | ((_, Derived _), _) => NONE) all_elemss);
    val thy_ctxt'' = thy_ctxt'
      (* add witnesses of Derived elements *)
      |> fold (fn (id, thms) => fold (add_wit id o Element.morph_witness (Element.satisfy_morphism prems)) thms)
         (map_filter (fn ((_, Assumed _), _) => NONE
            | ((id, Derived thms), _) => SOME (id, thms)) new_elemss)

    (* Accumulate equations *)
    val all_eqns =
      fold_map (join_eqns (get_reg thy_ctxt'' imp) (fst o fst) ctxt) all_elemss Termtab.empty
      |> fst
      |> map (apsnd (map snd o Termtab.dest))
      |> (fn xs => fold Idtab.update xs Idtab.empty)
      (* Idtab.make wouldn't work here: can have conflicting duplicates,
         because instantiation may equate ids and equations are accumulated! *)
  in
    thy_ctxt''
    (* add equations *)
    |> fold (fn (attns, thms) =>
         fold (fn (attn, thm) => note "lemma"
           [(apsnd (map (attrib thy_ctxt'')) attn,
             [([Element.conclude_witness thm], [])])] #> snd)
           (attns ~~ thms)) (unflat eq_thms eq_attns ~~ eq_thms)
    (* add facts *)
    |> fold (activate_elems prems all_eqns exp) new_elemss
  end;

fun global_activate_facts_elemss x = gen_activate_facts_elemss
      ProofContext.init
      get_global_registration
      PureThy.note_thmss_i
      global_note_prefix_i
      Attrib.attribute_i
      put_global_registration add_global_witness add_global_equation
      x;

fun local_activate_facts_elemss x = gen_activate_facts_elemss
      I
      get_local_registration
      ProofContext.note_thmss_i
      local_note_prefix_i
      (Attrib.attribute_i o ProofContext.theory_of)
      put_local_registration
      add_local_witness
      add_local_equation
      x;

fun prep_instantiations parse_term parse_prop ctxt parms (insts, eqns) =
  let
    (* parameters *)
    val (parm_names, parm_types) = parms |> split_list
      ||> map (TypeInfer.paramify_vars o Logic.varifyT);
    val type_parms = fold Term.add_tvarsT parm_types [] |> map (Logic.mk_type o TVar);
    val type_parm_names = fold Term.add_tfreesT (map snd parms) [] |> map fst;

    (* parameter instantiations *)
    val d = length parms - length insts;
    val insts =
      if d < 0 then error "More arguments than parameters in instantiation."
      else insts @ replicate d NONE;
    val (given_ps, given_insts) =
      ((parm_names ~~ parm_types) ~~ insts) |> map_filter
          (fn (_, NONE) => NONE
            | ((n, T), SOME inst) => SOME ((n, T), inst))
        |> split_list;
    val (given_parm_names, given_parm_types) = given_ps |> split_list;

    (* parse insts / eqns *)
    val given_insts' = map (parse_term ctxt) given_insts;
    val eqns' = map (parse_prop ctxt) eqns;

    (* type inference and contexts *)
    val arg = type_parms @ map2 TypeInfer.constrain given_parm_types given_insts' @ eqns';
    val res = Syntax.check_terms ctxt arg;
    val ctxt' = ctxt |> fold Variable.auto_fixes res;

    (* instantiation *)
    val (type_parms'', res') = chop (length type_parms) res;
    val (given_insts'', eqns'') = chop (length given_insts) res';
    val instT = Symtab.make (type_parm_names ~~ map Logic.dest_type type_parms'');
    val inst = Symtab.make (given_parm_names ~~ given_insts'');

    (* export from eigencontext *)
    val export = Variable.export_morphism ctxt' ctxt;

    (* import, its inverse *)
    val domT = fold Term.add_tfrees res [] |> map TFree;
    val importT = domT |> map (fn x => (Morphism.typ export x, x))
      |> map_filter (fn (TFree _, _) => NONE  (* fixed point of export *)
               | (TVar y, x) => SOME (fst y, x)
               | _ => error "internal: illegal export in interpretation")
      |> Vartab.make;
    val dom = fold Term.add_frees res [] |> map Free;
    val imprt = dom |> map (fn x => (Morphism.term export x, x))
      |> map_filter (fn (Free _, _) => NONE  (* fixed point of export *)
               | (Var y, x) => SOME (fst y, x)
               | _ => error "internal: illegal export in interpretation")
      |> Vartab.make;
  in (((instT, inst), eqns''), (export, ((importT, domT), (imprt, dom)))) end;

val read_instantiations = prep_instantiations Syntax.parse_term Syntax.parse_prop;
val check_instantiations = prep_instantiations (K I) (K I);

fun gen_prep_registration mk_ctxt test_reg activate
    prep_attr prep_expr prep_insts
    thy_ctxt raw_attn raw_expr raw_insts =
  let
    val ctxt = mk_ctxt thy_ctxt;
    val thy = ProofContext.theory_of ctxt;
    val ctxt' = ProofContext.init thy;
    fun prep_attn attn = (apsnd o map)
      (Attrib.crude_closure ctxt o Args.assignable o prep_attr thy) attn;

    val attn = prep_attn raw_attn;
    val expr = prep_expr thy raw_expr;

    val pts = params_of_expr ctxt' [] expr ([], Symtab.empty, Symtab.empty);
    val params_ids = make_params_ids (#1 pts);
    val raw_params_elemss = make_raw_params_elemss pts;
    val ((ids, _), raw_elemss) = flatten (ctxt', I) (([], Symtab.empty), Expr expr);
    val ((parms, all_elemss, _), (_, (_, defs, _))) =
      read_elemss false ctxt' [] (raw_params_elemss @ raw_elemss) [];

    (** compute instantiation **)

    (* consistency check: equations need to be stored in a particular locale,
       therefore if equations are present locale expression must be a name *)

    val _ = case (expr, snd raw_insts) of
        (Locale _, _) => () | (_, []) => ()
      | (_, _) => error "Interpretations with `where' only permitted if locale expression is a name.";

    (* read or certify instantiation *)
    val (raw_insts', raw_eqns) = raw_insts;
    val (raw_eq_attns, raw_eqns') = split_list raw_eqns;
    val (((instT, inst1), eqns), morphs) = prep_insts ctxt parms (raw_insts', raw_eqns');
    val eq_attns = map prep_attn raw_eq_attns;

    (* defined params without given instantiation *)
    val not_given = filter_out (Symtab.defined inst1 o fst) parms;
    fun add_def (p, pT) inst =
      let
        val (t, T) = case find_first (fn (Free (a, _), _) => a = p) defs of
               NONE => error ("Instance missing for parameter " ^ quote p)
             | SOME (Free (_, T), t) => (t, T);
        val d = Element.inst_term (instT, inst) t;
      in Symtab.update_new (p, d) inst end;
    val inst2 = fold add_def not_given inst1;
    val inst_morphism = Element.inst_morphism thy (instT, inst2);
    (* Note: insts contain no vars. *)

    (** compute proof obligations **)

    (* restore "small" ids *)
    val ids' = map (fn ((n, ps), (_, mode)) =>
          ((n, map (fn p => Free (p, (the o AList.lookup (op =) parms) p)) ps), mode))
        ids;
    val (_, all_elemss') = chop (length raw_params_elemss) all_elemss
    (* instantiate ids and elements *)
    val inst_elemss = (ids' ~~ all_elemss') |> map (fn (((n, ps), _), ((_, mode), elems)) =>
      ((n, map (Morphism.term (inst_morphism $> fst morphs)) ps),
        map (fn Int e => Element.morph_ctxt inst_morphism e) elems)
      |> apfst (fn id => (id, map_mode (map (Element.morph_witness inst_morphism)) mode)));

    (* remove fragments already registered with theory or context *)
    val new_inst_elemss = filter_out (fn ((id, _), _) =>
          test_reg thy_ctxt id) inst_elemss;

    (* equations *)
    val eqn_elems = if null eqns then []
      else [(Library.last_elem inst_elemss |> fst |> fst, eqns)];

    val propss = map extract_asms_elems new_inst_elemss @ eqn_elems;

  in (propss, activate attn inst_elemss new_inst_elemss propss eq_attns morphs) end;

fun gen_prep_global_registration mk_ctxt = gen_prep_registration ProofContext.init
  test_global_registration
  global_activate_facts_elemss mk_ctxt;

fun gen_prep_local_registration mk_ctxt = gen_prep_registration I
  test_local_registration
  local_activate_facts_elemss mk_ctxt;

val prep_global_registration = gen_prep_global_registration
  Attrib.intern_src intern_expr read_instantiations;
val prep_global_registration_i = gen_prep_global_registration
  (K I) (K I) check_instantiations;

val prep_local_registration = gen_prep_local_registration
  Attrib.intern_src intern_expr read_instantiations;
val prep_local_registration_i = gen_prep_local_registration
  (K I) (K I) check_instantiations;

fun prep_registration_in_locale target expr thy =
  (* target already in internal form *)
  let
    val ctxt = ProofContext.init thy;
    val ((raw_target_ids, target_syn), _) = flatten (ctxt, I)
        (([], Symtab.empty), Expr (Locale target));
    val fixed = the_locale thy target |> #params |> map #1;
    val ((all_ids, syn), raw_elemss) = flatten (ctxt, intern_expr thy)
        ((raw_target_ids, target_syn), Expr expr);
    val (target_ids, ids) = chop (length raw_target_ids) all_ids;
    val ((parms, elemss, _), _) = read_elemss false ctxt fixed raw_elemss [];

    (** compute proof obligations **)

    (* restore "small" ids, with mode *)
    val ids' = map (apsnd snd) ids;
    (* remove Int markers *)
    val elemss' = map (fn (_, es) =>
        map (fn Int e => e) es) elemss
    (* extract assumptions and defs *)
    val ids_elemss = ids' ~~ elemss';
    val propss = map extract_asms_elems ids_elemss;

    (** activation function:
        - add registrations to the target locale
        - add induced registrations for all global registrations of
          the target, unless already present
        - add facts of induced registrations to theory **)

    fun activate thmss thy = let
        val satisfy = Element.satisfy_thm (flat thmss);
        val ids_elemss_thmss = ids_elemss ~~ thmss;
        val regs = get_global_registrations thy target;

        fun activate_id (((id, Assumed _), _), thms) thy =
            thy |> put_registration_in_locale target id
                |> fold (add_witness_in_locale target id) thms
          | activate_id _ thy = thy;

        fun activate_reg (vts, (((fully_qualified, prfx), atts2), (exp, imp), _, _)) thy =
          let
            val (insts, wits, _) = collect_global_witnesses thy imp fixed target_ids vts;
            fun inst_parms ps = map
                  (the o AList.lookup (op =) (map #1 fixed ~~ vts)) ps;
            val disch = Element.satisfy_thm wits;
            val new_elemss = filter (fn (((name, ps), _), _) =>
                not (test_global_registration thy (name, inst_parms ps))) (ids_elemss);
            fun activate_assumed_id (((_, Derived _), _), _) thy = thy
              | activate_assumed_id ((((name, ps), Assumed _), _), thms) thy = let
                val ps' = inst_parms ps;
              in
                if test_global_registration thy (name, ps')
                then thy
                else thy
                  |> put_global_registration (name, ps') ((fully_qualified, prfx), atts2) (exp, imp)
                  |> fold (fn witn => fn thy => add_global_witness (name, ps')
                     (Element.morph_witness (Element.inst_morphism thy insts) witn) thy) thms
              end;

            fun activate_derived_id ((_, Assumed _), _) thy = thy
              | activate_derived_id (((name, ps), Derived ths), _) thy = let
                val ps' = inst_parms ps;
              in
                if test_global_registration thy (name, ps')
                then thy
                else thy
                  |> put_global_registration (name, ps') ((fully_qualified, prfx), atts2) (exp, imp)
                  |> fold (fn witn => fn thy => add_global_witness (name, ps')
                       (witn |> Element.map_witness (fn (t, th) =>  (* FIXME *)
                       (Element.inst_term insts t,
                        disch (Element.inst_thm thy insts (satisfy th))))) thy) ths
              end;

            fun activate_elem (loc, ps) (Notes (kind, facts)) thy =
                let
                  val att_morphism =
                    Morphism.name_morphism (NameSpace.qualified prfx) $>
                    Morphism.thm_morphism satisfy $>
                    Element.inst_morphism thy insts $>
                    Morphism.thm_morphism disch;
                  val facts' = facts
                    |> Attrib.map_facts (Attrib.attribute_i thy o Args.morph_values att_morphism)
                    |> map (apfst (apsnd (fn a => a @ map (Attrib.attribute thy) atts2)))
                    |> map (apsnd (map (apfst (map (disch o Element.inst_thm thy insts o satisfy)))))
                in
                  thy
                  |> global_note_prefix_i kind loc (fully_qualified, prfx) facts'
                  |> snd
                end
              | activate_elem _ _ thy = thy;

            fun activate_elems ((id, _), elems) thy = fold (activate_elem id) elems thy;

          in thy |> fold activate_assumed_id ids_elemss_thmss
                 |> fold activate_derived_id ids_elemss
                 |> fold activate_elems new_elemss end;
      in
        thy |> fold activate_id ids_elemss_thmss
            |> fold activate_reg regs
      end;

  in (propss, activate) end;

fun prep_propp propss = propss |> map (fn (_, props) =>
  map (rpair [] o Element.mark_witness) props);

fun prep_result propps thmss =
  ListPair.map (fn ((_, props), thms) => map2 Element.make_witness props thms) (propps, thmss);

fun gen_interpretation prep_registration after_qed (prfx, raw_atts) raw_expr raw_insts thy =
  (* prfx = (flag indicating full qualification, name prefix) *)
  let
    val (propss, activate) = prep_registration thy (prfx, raw_atts) raw_expr raw_insts;
    fun after_qed' results =
      ProofContext.theory (activate (prep_result propss results))
      #> after_qed;
  in
    thy
    |> ProofContext.init
    |> Proof.theorem_i NONE after_qed' (prep_propp propss)
    |> Element.refine_witness
    |> Seq.hd
  end;

fun gen_interpret prep_registration after_qed (prfx, atts) expr insts int state =
  (* prfx = (flag indicating full qualification, name prefix) *)
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;
    val (propss, activate) = prep_registration ctxt (prfx, atts) expr insts;
    fun after_qed' results =
      Proof.map_context (K (ctxt |> activate (prep_result propss results)))
      #> Proof.put_facts NONE
      #> after_qed;
  in
    state
    |> Proof.local_goal (ProofDisplay.print_results int) (K I) ProofContext.bind_propp_i
      "interpret" NONE after_qed' (map (pair ("", [])) (prep_propp propss))
    |> Element.refine_witness |> Seq.hd
  end;

in

val interpretation_i = gen_interpretation prep_global_registration_i;
val interpretation = gen_interpretation prep_global_registration;


fun interpretation_in_locale after_qed (raw_target, expr) thy =
  let
    val target = intern thy raw_target;
    val (propss, activate) = prep_registration_in_locale target expr thy;
    val raw_propp = prep_propp propss;

    val (_, _, goal_ctxt, propp) = thy
      |> ProofContext.init
      |> cert_context_statement (SOME target) [] raw_propp;

    fun after_qed' results =
      ProofContext.theory (activate (prep_result propss results))
      #> after_qed;
  in
    goal_ctxt
    |> Proof.theorem_i NONE after_qed' propp
    |> Element.refine_witness |> Seq.hd
  end;

val interpret_i = gen_interpret prep_local_registration_i;
val interpret = gen_interpret prep_local_registration;

end;

end;
