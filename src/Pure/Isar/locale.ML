(*  Title:      Pure/Isar/locale.ML
    Author:     Clemens Ballarin, TU Muenchen

Locales -- managed Isar proof contexts, based on Pure predicates.

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

signature LOCALE =
sig
  (* Locale specification *)
  val register_locale: binding ->
    (string * sort) list * ((string * typ) * mixfix) list ->
    term option * term list ->
    thm option * thm option -> thm list ->
    declaration list ->
    (string * (Attrib.binding * (thm list * Attrib.src list) list) list) list ->
    (string * morphism) list -> theory -> theory
  val intern: theory -> xstring -> string
  val extern: theory -> string -> xstring
  val defined: theory -> string -> bool
  val params_of: theory -> string -> ((string * typ) * mixfix) list
  val intros_of: theory -> string -> thm option * thm option
  val axioms_of: theory -> string -> thm list
  val instance_of: theory -> string -> morphism -> term list
  val specification_of: theory -> string -> term option * term list

  (* Storing results *)
  val add_thmss: string -> string -> (Attrib.binding * (thm list * Attrib.src list) list) list ->
    Proof.context -> Proof.context
  val add_declaration: string -> declaration -> Proof.context -> Proof.context
  val add_syntax_declaration: string -> declaration -> Proof.context -> Proof.context

  (* Activation *)
  val activate_declarations: string * morphism -> Proof.context -> Proof.context
  val activate_facts: string * morphism -> Context.generic -> Context.generic
  val init: string -> theory -> Proof.context

  (* Reasoning about locales *)
  val get_witnesses: Proof.context -> thm list
  val get_intros: Proof.context -> thm list
  val get_unfolds: Proof.context -> thm list
  val witness_add: attribute
  val intro_add: attribute
  val unfold_add: attribute
  val intro_locales_tac: bool -> Proof.context -> thm list -> tactic

  (* Registrations and dependencies *)
  val add_registration: string * morphism -> (morphism * bool) option ->
    morphism -> theory -> theory
  val amend_registration: string * morphism -> morphism * bool ->
    morphism -> theory -> theory
  val add_dependency: string -> string * morphism -> morphism -> theory -> theory

  (* Diagnostic *)
  val print_locales: theory -> unit
  val print_locale: theory -> bool -> xstring -> unit
  val print_registrations: theory -> string -> unit
end;

structure Locale: LOCALE =
struct

datatype ctxt = datatype Element.ctxt;


(*** Theory data ***)

datatype locale = Loc of {
  (** static part **)
  parameters: (string * sort) list * ((string * typ) * mixfix) list,
    (* type and term parameters *)
  spec: term option * term list,
    (* assumptions (as a single predicate expression) and defines *)
  intros: thm option * thm option,
  axioms: thm list,
  (** dynamic part **)
  syntax_decls: (declaration * serial) list,
    (* syntax declarations *)
  notes: ((string * (Attrib.binding * (thm list * Attrib.src list) list) list) * serial) list,
    (* theorem declarations *)
  dependencies: ((string * (morphism * morphism)) * serial) list
    (* locale dependencies (sublocale relation) *)
};

fun mk_locale ((parameters, spec, intros, axioms), ((syntax_decls, notes), dependencies)) =
  Loc {parameters = parameters, intros = intros, axioms = axioms, spec = spec,
    syntax_decls = syntax_decls, notes = notes, dependencies = dependencies};

fun map_locale f (Loc {parameters, spec, intros, axioms, syntax_decls, notes, dependencies}) =
  mk_locale (f ((parameters, spec, intros, axioms), ((syntax_decls, notes), dependencies)));

fun merge_locale
 (Loc {parameters, spec, intros, axioms, syntax_decls, notes, dependencies},
  Loc {syntax_decls = syntax_decls', notes = notes', dependencies = dependencies', ...}) =
    mk_locale
      ((parameters, spec, intros, axioms),
        ((merge (eq_snd op =) (syntax_decls, syntax_decls'),
          merge (eq_snd op =) (notes, notes')),
            merge (eq_snd op =) (dependencies, dependencies')));

structure Locales = Theory_Data
(
  type T = locale Name_Space.table;
  val empty : T = Name_Space.empty_table "locale";
  val extend = I;
  val merge = Name_Space.join_tables (K merge_locale);
);

val intern = Name_Space.intern o #1 o Locales.get;
val extern = Name_Space.extern o #1 o Locales.get;

val get_locale = Symtab.lookup o #2 o Locales.get;
val defined = Symtab.defined o #2 o Locales.get;

fun the_locale thy name =
  (case get_locale thy name of
    SOME (Loc loc) => loc
  | NONE => error ("Unknown locale " ^ quote name));

fun register_locale binding parameters spec intros axioms syntax_decls notes dependencies thy =
  thy |> Locales.map (Name_Space.define true (Sign.naming_of thy)
    (binding,
      mk_locale ((parameters, spec, intros, axioms),
        ((map (fn decl => (decl, serial ())) syntax_decls, map (fn n => (n, serial ())) notes),
          map (fn d => (d |> apsnd (rpair Morphism.identity), serial ())) dependencies))) #> snd);
          (* FIXME *)

fun change_locale name =
  Locales.map o apsnd o Symtab.map_entry name o map_locale o apsnd;

fun print_locales thy =
  Pretty.strs ("locales:" :: map #1 (Name_Space.extern_table (Locales.get thy)))
  |> Pretty.writeln;


(*** Primitive operations ***)

fun params_of thy = snd o #parameters o the_locale thy;

fun intros_of thy = #intros o the_locale thy;

fun axioms_of thy = #axioms o the_locale thy;

fun instance_of thy name morph = params_of thy name |>
  map (Morphism.term morph o Free o #1);

fun specification_of thy = #spec o the_locale thy;

fun dependencies_of thy name = the_locale thy name |>
  #dependencies |> map fst;

(* Print instance and qualifiers *)

fun pretty_reg thy (name, morph) =
  let
    val name' = extern thy name;
    val ctxt = ProofContext.init_global thy;
    fun prt_qual (qual, mand) = Pretty.str (qual ^ (if mand then "!" else "?"));
    fun prt_quals qs = Pretty.separate "." (map prt_qual qs) |> Pretty.block;
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    fun prt_term' t = if !show_types
      then Pretty.block [prt_term t, Pretty.brk 1, Pretty.str "::",
        Pretty.brk 1, (Pretty.quote o Syntax.pretty_typ ctxt) (type_of t)]
      else prt_term t;
    fun prt_inst ts =
      Pretty.block (Pretty.breaks (Pretty.str name' :: map prt_term' ts));

    val qs = Binding.name "x" |> Morphism.binding morph |> Binding.prefix_of;
    val ts = instance_of thy name morph;
  in
    case qs of
       [] => prt_inst ts
     | qs => Pretty.block [prt_quals qs, Pretty.brk 1, Pretty.str ":",
         Pretty.brk 1, prt_inst ts]
  end;


(*** Activate context elements of locale ***)

(** Identifiers: activated locales in theory or proof context **)

(* subsumption *)
fun ident_le thy ((n: string, ts), (m, ss)) = (m = n) andalso Pattern.matchess thy (ss, ts);
  (* smaller term is more general *)

(* total order *)
fun ident_ord ((n: string, ts), (m, ss)) =
  case fast_string_ord (m, n) of
      EQUAL => list_ord Term_Ord.fast_term_ord (ts, ss)
    | ord => ord;

local

datatype 'a delayed = Ready of 'a | ToDo of 'a delayed * 'a delayed;

structure Identifiers = Generic_Data
(
  type T = (string * term list) list delayed;
  val empty = Ready [];
  val extend = I;
  val merge = ToDo;
);

fun finish thy (ToDo (i1, i2)) = merge (ident_le thy) (finish thy i1, finish thy i2)
  | finish _ (Ready ids) = ids;

val _ = Context.>> (Context.map_theory (Theory.at_begin (fn thy =>
  (case Identifiers.get (Context.Theory thy) of
    Ready _ => NONE
  | ids => SOME (Context.theory_map (Identifiers.put (Ready (finish thy ids))) thy)))));

in

val get_idents = (fn Ready ids => ids) o Identifiers.get;
val put_idents = Identifiers.put o Ready;

end;


(** Resolve locale dependencies in a depth-first fashion **)

local

val roundup_bound = 120;

fun add thy depth export (name, morph) (deps, marked) =
  if depth > roundup_bound
  then error "Roundup bound exceeded (sublocale relation probably not terminating)."
  else
    let
      val dependencies = dependencies_of thy name;
      val instance = instance_of thy name (morph $> export);
    in
      if member (ident_le thy) marked (name, instance)
      then (deps, marked)
      else
        let
          val dependencies' = map (fn (name, (morph', export')) => (name, morph' $> export' $> morph)) dependencies;
          val marked' = (name, instance) :: marked;
          val (deps', marked'') = fold_rev (add thy (depth + 1) export) dependencies' ([], marked');
        in
          ((name, morph) :: deps' @ deps, marked'')
        end
    end;

in

(* Note that while identifiers always have the external (exported) view, activate_dep
  is presented with the internal view. *)

fun roundup thy activate_dep export (name, morph) (marked, input) =
  let
    (* Find all dependencies incuding new ones (which are dependencies enriching
      existing registrations). *)
    val (dependencies, marked') = add thy 0 export (name, morph) ([], []);
    (* Filter out fragments from marked; these won't be activated. *)
    val dependencies' = filter_out (fn (name, morph) =>
      member (ident_le thy) marked (name, instance_of thy name (morph $> export))) dependencies;
  in
    (merge (ident_le thy) (marked, marked'), input |> fold_rev activate_dep dependencies')
  end;

end;


(* Declarations, facts and entire locale content *)

fun activate_syntax_decls (name, morph) context =
  let
    val thy = Context.theory_of context;
    val {syntax_decls, ...} = the_locale thy name;
  in
    context
    |> fold_rev (fn (decl, _) => decl morph) syntax_decls
  end;

fun activate_notes activ_elem transfer thy (name, morph) input =
  let
    val {notes, ...} = the_locale thy name;
    fun activate ((kind, facts), _) input =
      let
        val facts' = facts |> Element.facts_map (Element.morph_ctxt (transfer input $> morph))
      in activ_elem (Notes (kind, facts')) input end;
  in
    fold_rev activate notes input
  end;

fun activate_all name thy activ_elem transfer (marked, input) =
  let
    val {parameters = (_, params), spec = (asm, defs), ...} = the_locale thy name;
    val input' = input |>
      (not (null params) ?
        activ_elem (Fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params))) |>
      (* FIXME type parameters *)
      (case asm of SOME A => activ_elem (Assumes [(Attrib.empty_binding, [(A, [])])]) | _ => I) |>
      (if not (null defs)
        then activ_elem (Defines (map (fn def => (Attrib.empty_binding, (def, []))) defs))
        else I);
    val activate = activate_notes activ_elem transfer thy;
  in
    roundup thy activate Morphism.identity (name, Morphism.identity) (marked, input')
  end;


(** Public activation functions **)

fun activate_declarations dep = Context.proof_map (fn context =>
  let
    val thy = Context.theory_of context;
  in
    roundup thy activate_syntax_decls Morphism.identity dep (get_idents context, context)
    |-> put_idents
  end);

fun activate_facts dep context =
  let
    val thy = Context.theory_of context;
    val activate = activate_notes Element.init (Element.transfer_morphism o Context.theory_of) thy;
  in roundup thy activate Morphism.identity dep (get_idents context, context) |-> put_idents end;

fun init name thy =
  activate_all name thy Element.init (Element.transfer_morphism o Context.theory_of)
    ([], Context.Proof (ProofContext.init_global thy)) |-> put_idents |> Context.proof_of;

fun print_locale thy show_facts raw_name =
  let
    val name = intern thy raw_name;
    val ctxt = init name thy;
    fun cons_elem (elem as Notes _) = show_facts ? cons elem
      | cons_elem elem = cons elem;
    val elems =
      activate_all name thy cons_elem (K (Element.transfer_morphism thy)) ([], [])
      |> snd |> rev;
  in
    Pretty.big_list "locale elements:" (map (Pretty.chunks o Element.pretty_ctxt ctxt) elems)
    |> Pretty.writeln
  end;


(*** Registrations: interpretations in theories ***)

structure Idtab = Table(type key = string * term list val ord = ident_ord);

structure Registrations = Theory_Data
(
  type T = ((morphism * morphism) * serial) Idtab.table *
    (* registrations, indexed by locale name and instance;
       serial points to mixin list *)
    (((morphism * bool) * serial) list) Inttab.table;
    (* table of mixin lists, per list mixins in reverse order of declaration;
       lists indexed by registration serial,
       entries for empty lists may be omitted *)
  val empty = (Idtab.empty, Inttab.empty);
  val extend = I;
  fun merge ((reg1, mix1), (reg2, mix2)) : T =
    (Idtab.join (fn id => fn (r1 as (_, s1), r2 as (_, s2)) =>
        if s1 = s2 then raise Idtab.SAME else raise Idtab.DUP id) (reg1, reg2),
      Inttab.join (K (Library.merge (eq_snd op =))) (mix1, mix2))
    handle Idtab.DUP id =>
      (* distinct interpretations with same base: merge their mixins *)
      let
        val (_, s1) = Idtab.lookup reg1 id |> the;
        val (morph2, s2) = Idtab.lookup reg2 id |> the;
        val reg2' = Idtab.update (id, (morph2, s1)) reg2;
        val mix2' = case Inttab.lookup mix2 s2 of
              NONE => mix2 |
              SOME mxs => Inttab.delete s2 mix2 |> Inttab.update_new (s1, mxs);
        val _ = warning "Removed duplicate interpretation after retrieving its mixins.";
        (* FIXME print interpretations,
           which is not straightforward without theory context *)
      in merge ((reg1, mix1), (reg2', mix2')) end;
    (* FIXME consolidate with dependencies, consider one data slot only *)
);


(* Primitive operations *)

fun add_reg thy export (name, morph) =
  Registrations.map (apfst (Idtab.insert (K false)
    ((name, instance_of thy name (morph $> export)), ((morph, export), serial ()))));

fun add_mixin serial' mixin =
  (* registration to be amended identified by its serial id *)
  Registrations.map (apsnd (Inttab.map_default (serial', []) (cons (mixin, serial ()))));

fun get_mixins thy (name, morph) =
  let
    val (regs, mixins) = Registrations.get thy;
  in
    case Idtab.lookup regs (name, instance_of thy name morph) of
      NONE => []
    | SOME (_, serial) => the_default [] (Inttab.lookup mixins serial)
  end;

fun collect_mixins thy (name, morph) =
  roundup thy (fn dep => fn mixins =>
    merge (eq_snd op =) (mixins, get_mixins thy dep)) Morphism.identity (name, morph) ([], [])
  |> snd |> filter (snd o fst);  (* only inheritable mixins *) (* FIXME *)
  (* FIXME refactor usage *)

fun compose_mixins mixins =
  fold_rev Morphism.compose (map (fst o fst) mixins) Morphism.identity;

fun reg_morph mixins ((name, (base, export)), serial) =
  let val mix = the_default [] (AList.lookup (op =) mixins serial) |> compose_mixins;
  in (name, base $> mix $> export) end;

fun these_registrations thy name = Registrations.get thy
  |>> Idtab.dest
  |>> filter (curry (op =) name o fst o fst)
  (* with inherited mixins *)
  |-> (fn regs => fn _ => map (fn ((name, _), ((base, export) ,_)) =>
    (name, base $> (collect_mixins thy (name, base $> export) |> compose_mixins) $> export)) regs);

fun all_registrations thy = Registrations.get thy (* FIXME clone *)
  |>> Idtab.dest
  (* with inherited mixins *)
  |-> (fn regs => fn _ => map (fn ((name, _), ((base, export) ,_)) =>
    (name, base $> (collect_mixins thy (name, base $> export) |> compose_mixins) $> export)) regs);

fun activate_notes' activ_elem transfer thy export (name, morph) input =
  let
    val {notes, ...} = the_locale thy name;
    fun activate ((kind, facts), _) input =
      let
        val mixin = collect_mixins thy (name, morph $> export) |> compose_mixins;
        val facts' = facts |> Element.facts_map (Element.morph_ctxt (transfer input $> morph $> mixin $> export))
      in activ_elem (Notes (kind, facts')) input end;
  in
    fold_rev activate notes input
  end;

fun activate_facts' export dep context =
  let
    val thy = Context.theory_of context;
    val activate = activate_notes' Element.init (Element.transfer_morphism o Context.theory_of) thy export;
  in roundup thy activate export dep (get_idents context, context) |-> put_idents end;


(* Diagnostic *)

fun print_registrations thy raw_name =
  (case these_registrations thy (intern thy raw_name) of
      [] => Pretty.str ("no interpretations")
    | regs => Pretty.big_list "interpretations:" (map (pretty_reg thy) (rev regs)))
  |> Pretty.writeln;


(* Add and extend registrations *)

fun amend_registration (name, morph) mixin export thy =
  let
    val regs = Registrations.get thy |> fst;
    val base = instance_of thy name (morph $> export);
  in
    case Idtab.lookup regs (name, base) of
        NONE => error ("No interpretation of locale " ^
          quote (extern thy name) ^ " and\nparameter instantiation " ^
          space_implode " " (map (quote o Syntax.string_of_term_global thy) base) ^
          " available")
      | SOME (_, serial') => add_mixin serial' mixin thy
  end;

(* Note that a registration that would be subsumed by an existing one will not be
   generated, and it will not be possible to amend it. *)

fun add_registration (name, base_morph) mixin export thy =
  let
    val mix = case mixin of NONE => Morphism.identity
          | SOME (mix, _) => mix;
    val morph = base_morph $> mix;
    val inst = instance_of thy name morph;
  in
    if member (ident_le thy) (get_idents (Context.Theory thy)) (name, inst)
    then thy
    else
      (get_idents (Context.Theory thy), thy)
      (* add new registrations with inherited mixins *)
      |> roundup thy (add_reg thy export) export (name, morph)
      |> snd
      (* add mixin *)
      |> (case mixin of NONE => I
           | SOME mixin => amend_registration (name, morph) mixin export)
      (* activate import hierarchy as far as not already active *)
      |> Context.theory_map (activate_facts' export (name, morph))
  end;


(*** Dependencies ***)

fun add_dependency loc (name, morph) export thy =
  let
    val thy' = (change_locale loc o apsnd) (cons ((name, (morph, export)), serial ())) thy;
    val (_, regs) = fold_rev (roundup thy' cons export)
      (all_registrations thy') (get_idents (Context.Theory thy'), []);
  in
    thy'
    |> fold_rev (fn dep => add_registration dep NONE export) regs
  end;


(*** Storing results ***)

(* Theorems *)

fun add_thmss loc kind args ctxt =
  let
    val (Notes args', ctxt') = Element.activate_i (Notes (kind, args)) ctxt;
    val ctxt'' = ctxt' |> ProofContext.theory (
      (change_locale loc o apfst o apsnd) (cons (args', serial ()))
        #>
      (* Registrations *)
      (fn thy => fold_rev (fn (_, morph) =>
            let
              val args'' = snd args' |> Element.facts_map (Element.morph_ctxt morph) |>
                Attrib.map_facts (Attrib.attribute_i thy)
            in PureThy.note_thmss kind args'' #> snd end)
        (these_registrations thy loc) thy))
  in ctxt'' end;


(* Declarations *)

fun add_declaration loc decl =
  add_thmss loc ""
    [((Binding.conceal Binding.empty,
        [Attrib.internal (fn phi => Thm.declaration_attribute (K (decl phi)))]),
      [([Drule.dummy_thm], [])])];

fun add_syntax_declaration loc decl =
  ProofContext.theory ((change_locale loc o apfst o apfst) (cons (decl, serial ())))
  #> add_declaration loc decl;


(*** Reasoning about locales ***)

(* Storage for witnesses, intro and unfold rules *)

structure Thms = Generic_Data
(
  type T = thm list * thm list * thm list;
  val empty = ([], [], []);
  val extend = I;
  fun merge ((witnesses1, intros1, unfolds1), (witnesses2, intros2, unfolds2)) =
   (Thm.merge_thms (witnesses1, witnesses2),
    Thm.merge_thms (intros1, intros2),
    Thm.merge_thms (unfolds1, unfolds2));
);

val get_witnesses = #1 o Thms.get o Context.Proof;
val get_intros = #2 o Thms.get o Context.Proof;
val get_unfolds = #3 o Thms.get o Context.Proof;

val witness_add =
  Thm.declaration_attribute (fn th => Thms.map (fn (x, y, z) => (Thm.add_thm th x, y, z)));
val intro_add =
  Thm.declaration_attribute (fn th => Thms.map (fn (x, y, z) => (x, Thm.add_thm th y, z)));
val unfold_add =
  Thm.declaration_attribute (fn th => Thms.map (fn (x, y, z) => (x, y, Thm.add_thm th z)));


(* Tactic *)

fun gen_intro_locales_tac intros_tac eager ctxt =
  intros_tac
    (get_witnesses ctxt @ get_intros ctxt @ (if eager then get_unfolds ctxt else []));

val intro_locales_tac = gen_intro_locales_tac Method.intros_tac;
val try_intro_locales_tac= gen_intro_locales_tac Method.try_intros_tac;

val _ = Context.>> (Context.map_theory
 (Method.setup (Binding.name "intro_locales") (Scan.succeed (METHOD o try_intro_locales_tac false))
    "back-chain introduction rules of locales without unfolding predicates" #>
  Method.setup (Binding.name "unfold_locales") (Scan.succeed (METHOD o try_intro_locales_tac true))
    "back-chain all introduction rules of locales"));

end;
