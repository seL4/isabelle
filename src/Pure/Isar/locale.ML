(*  Title:      Pure/Isar/locale.ML
    Author:     Clemens Ballarin, TU Muenchen

Locales -- managed Isar proof contexts, based on Pure predicates.

Draws basic ideas from Florian Kammueller's original version of
locales, but uses the richer infrastructure of Isar instead of the raw
meta-logic.  Furthermore, structured composition of contexts (with merge
and instantiation) is provided, as well as type-inference of the
signature parts and predicate definitions of the specification text.

Interpretation enables the transfer of declarations and theorems to other
contexts, namely those defined by theories, structured proofs and locales
themselves.

A comprehensive account of locales is available:

[1] Clemens Ballarin. Locales: a module system for mathematical theories.
    Journal of Automated Reasoning, 52(2):123-153, 2014.

See also:

[2] Clemens Ballarin. Locales and Locale Expressions in Isabelle/Isar.
    In Stefano Berardi et al., Types for Proofs and Programs: International
    Workshop, TYPES 2003, Torino, Italy, LNCS 3085, pages 34-50, 2004.
[3] Clemens Ballarin. Interpretation of Locales in Isabelle: Managing
    Dependencies between Locales. Technical Report TUM-I0607, Technische
    Universitaet Muenchen, 2006.
[4] Clemens Ballarin. Interpretation of Locales in Isabelle: Theories and
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
    Element.context_i list ->
    declaration list ->
    (string * Attrib.fact list) list ->
    (string * morphism) list -> theory -> theory
  val locale_space: theory -> Name_Space.T
  val intern: theory -> xstring -> string
  val check: theory -> xstring * Position.T -> string
  val extern: theory -> string -> xstring
  val markup_name: Proof.context -> string -> string
  val pretty_name: Proof.context -> string -> Pretty.T
  val defined: theory -> string -> bool
  val parameters_of: theory -> string -> (string * sort) list * ((string * typ) * mixfix) list
  val params_of: theory -> string -> ((string * typ) * mixfix) list
  val intros_of: theory -> string -> thm option * thm option
  val axioms_of: theory -> string -> thm list
  val instance_of: theory -> string -> morphism -> term list
  val specification_of: theory -> string -> term option * term list
  val hyp_spec_of: theory -> string -> Element.context_i list

  (* Storing results *)
  val add_facts: string -> string -> Attrib.fact list -> Proof.context -> Proof.context
  val add_declaration: string -> bool -> declaration -> Proof.context -> Proof.context

  (* Activation *)
  val activate_facts: morphism option -> string * morphism -> Context.generic -> Context.generic
  val activate_declarations: string * morphism -> Proof.context -> Proof.context
  val init: string -> theory -> Proof.context

  (* Reasoning about locales *)
  val get_witnesses: Proof.context -> thm list
  val get_intros: Proof.context -> thm list
  val get_unfolds: Proof.context -> thm list
  val witness_add: attribute
  val intro_add: attribute
  val unfold_add: attribute
  val intro_locales_tac: {strict: bool, eager: bool} -> Proof.context -> thm list -> tactic

  (* Registrations and dependencies *)
  type registration = {inst: string * morphism, mixin: (morphism * bool) option, export: morphism}
  val amend_registration: registration -> Context.generic -> Context.generic
  val add_registration: registration -> Context.generic -> Context.generic
  val add_registration_theory': registration -> theory -> theory
  val add_registration_theory: registration -> local_theory -> local_theory
  val add_registration_local_theory: registration -> local_theory -> local_theory
  val add_registration_proof: registration -> Proof.context -> Proof.context
  val registrations_of: Context.generic -> string -> (string * morphism) list
  val add_dependency': string -> registration -> theory -> theory
  val add_dependency: string -> registration -> local_theory -> local_theory

  (* Diagnostic *)
  val get_locales: theory -> string list
  val pretty_locales: theory -> bool -> Pretty.T
  val pretty_locale: theory -> bool -> string -> Pretty.T
  val pretty_registrations: Proof.context -> string -> Pretty.T
  val pretty_locale_deps: theory -> {name: string, parents: string list, body: Pretty.T} list
  type locale_dependency =
    {source: string, target: string, prefix: (string * bool) list, morphism: morphism,
      pos: Position.T, serial: serial}
  val dest_dependencies: theory list -> theory -> locale_dependency list
  val tracing : Proof.context -> string -> unit
end;

structure Locale: LOCALE =
struct

datatype ctxt = datatype Element.ctxt;


(*** Locales ***)

type dep = {name: string, morphisms: morphism * morphism, pos: Position.T, serial: serial};
fun eq_dep (dep1: dep, dep2: dep) = #serial dep1 = #serial dep2;

fun make_dep (name, morphisms) : dep =
  {name = name, morphisms = morphisms, pos = Position.thread_data (), serial = serial ()};

(*table of mixin lists, per list mixins in reverse order of declaration;
  lists indexed by registration/dependency serial,
  entries for empty lists may be omitted*)
type mixin = (morphism * bool) * serial;
type mixins = mixin list Inttab.table;

fun lookup_mixins (mixins: mixins) serial' = Inttab.lookup_list mixins serial';

val merge_mixins: mixins * mixins -> mixins = Inttab.merge_list (eq_snd op =);

fun insert_mixin serial' mixin : mixins -> mixins = Inttab.cons_list (serial', (mixin, serial ()));

fun rename_mixin (old, new) (mixins: mixins) =
  (case Inttab.lookup mixins old of
    NONE => mixins
  | SOME mixin => Inttab.delete old mixins |> Inttab.update_new (new, mixin));

fun compose_mixins (mixins: mixin list) =
  fold_rev Morphism.compose (map (fst o fst) mixins) Morphism.identity;

datatype locale = Loc of {
  (* static part *)

  (*type and term parameters*)
  parameters: (string * sort) list * ((string * typ) * mixfix) list,
  (*assumptions (as a single predicate expression) and defines*)
  spec: term option * term list,
  intros: thm option * thm option,
  axioms: thm list,
  (*diagnostic device: theorem part of hypothetical body as specified by the user*)
  hyp_spec: Element.context_i list,

  (* dynamic part *)

  (*syntax declarations*)
  syntax_decls: (declaration * serial) list,
  (*theorem declarations*)
  notes: ((string * Attrib.fact list) * serial) list,
  (*locale dependencies (sublocale relation) in reverse order*)
  dependencies: dep list,
  (*mixin part of dependencies*)
  mixins: mixins
};

fun mk_locale ((parameters, spec, intros, axioms, hyp_spec),
    ((syntax_decls, notes), (dependencies, mixins))) =
  Loc {parameters = parameters, spec = spec, intros = intros, axioms = axioms, hyp_spec = hyp_spec,
    syntax_decls = syntax_decls, notes = notes, dependencies = dependencies, mixins = mixins};

fun map_locale f (Loc {parameters, spec, intros, axioms, hyp_spec,
    syntax_decls, notes, dependencies, mixins}) =
  mk_locale (f ((parameters, spec, intros, axioms, hyp_spec),
    ((syntax_decls, notes), (dependencies, mixins))));

fun merge_locale
 (Loc {parameters, spec, intros, axioms, hyp_spec, syntax_decls, notes, dependencies, mixins},
  Loc {syntax_decls = syntax_decls', notes = notes',
      dependencies = dependencies', mixins = mixins', ...}) =
    mk_locale
      ((parameters, spec, intros, axioms, hyp_spec),
        ((merge (eq_snd op =) (syntax_decls, syntax_decls'),
          merge (eq_snd op =) (notes, notes')),
            (merge eq_dep (dependencies, dependencies'),
              (merge_mixins (mixins, mixins')))));

structure Locales = Theory_Data
(
  type T = locale Name_Space.table;
  val empty : T = Name_Space.empty_table "locale";
  val extend = I;
  val merge = Name_Space.join_tables (K merge_locale);
);

val locale_space = Name_Space.space_of_table o Locales.get;
val intern = Name_Space.intern o locale_space;
fun check thy = #1 o Name_Space.check (Context.Theory thy) (Locales.get thy);

fun extern thy = Name_Space.extern (Proof_Context.init_global thy) (locale_space thy);

fun markup_extern ctxt =
  Name_Space.markup_extern ctxt (locale_space (Proof_Context.theory_of ctxt));

fun markup_name ctxt name = markup_extern ctxt name |-> Markup.markup;
fun pretty_name ctxt name = markup_extern ctxt name |> Pretty.mark_str;

val get_locale = Name_Space.lookup o Locales.get;
val defined = is_some oo get_locale;

fun the_locale thy name =
  (case get_locale thy name of
    SOME (Loc loc) => loc
  | NONE => error ("Unknown locale " ^ quote name));

fun register_locale
    binding parameters spec intros axioms hyp_spec syntax_decls notes dependencies thy =
  thy |> Locales.map (Name_Space.define (Context.Theory thy) true
    (binding,
      mk_locale ((parameters, spec, (apply2 o Option.map) Thm.trim_context intros,
          map Thm.trim_context axioms, hyp_spec),
        ((map (fn decl => (decl, serial ())) syntax_decls, map (fn n => (n, serial ())) notes),
          (map (fn (name, morph) => make_dep (name, (morph, Morphism.identity))) dependencies,
            Inttab.empty)))) #> snd);
          (* FIXME Morphism.identity *)

fun change_locale name =
  Locales.map o Name_Space.map_table_entry name o map_locale o apsnd;



(** Primitive operations **)

fun parameters_of thy = #parameters o the_locale thy;
val params_of = #2 oo parameters_of;

fun intros_of thy = (apply2 o Option.map) (Thm.transfer thy) o #intros o the_locale thy;

fun axioms_of thy = map (Thm.transfer thy) o #axioms o the_locale thy;

fun instance_of thy name morph = params_of thy name |>
  map (Morphism.term morph o Free o #1);

fun specification_of thy = #spec o the_locale thy;

fun hyp_spec_of thy = #hyp_spec o the_locale thy;

fun dependencies_of thy = #dependencies o the_locale thy;

fun mixins_of thy name serial = lookup_mixins (#mixins (the_locale thy name)) serial;


(* Print instance and qualifiers *)

fun pretty_reg_inst ctxt qs (name, ts) =
  let
    fun print_qual (qual, mandatory) = qual ^ (if mandatory then "" else "?");
    fun prt_quals qs = Pretty.str (space_implode "." (map print_qual qs));
    val prt_term = Pretty.quote o Syntax.pretty_term ctxt;
    fun prt_term' t =
      if Config.get ctxt show_types
      then Pretty.block [prt_term t, Pretty.brk 1, Pretty.str "::",
        Pretty.brk 1, (Pretty.quote o Syntax.pretty_typ ctxt) (type_of t)]
      else prt_term t;
    fun prt_inst ts =
      Pretty.block (Pretty.breaks (pretty_name ctxt name :: map prt_term' ts));
  in
    (case qs of
      [] => prt_inst ts
    | qs => Pretty.block [prt_quals qs, Pretty.brk 1, Pretty.str ":", Pretty.brk 1, prt_inst ts])
  end;

fun pretty_reg ctxt export (name, morph) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val morph' = morph $> export;
    val qs = Morphism.binding_prefix morph';
    val ts = instance_of thy name morph';
  in pretty_reg_inst ctxt qs (name, ts) end;


(*** Identifiers: activated locales in theory or proof context ***)

type idents = term list list Symtab.table;  (* name ~> instance (grouped by name) *)

val empty_idents : idents = Symtab.empty;
val insert_idents = Symtab.insert_list (eq_list (op aconv));
val merge_idents = Symtab.merge_list (eq_list (op aconv));

fun redundant_ident thy idents (name, instance) =
  exists (fn pat => Pattern.matchess thy (pat, instance)) (Symtab.lookup_list idents name);

structure Idents = Generic_Data
(
  type T = idents;
  val empty = empty_idents;
  val extend = I;
  val merge = merge_idents;
);


(** Resolve locale dependencies in a depth-first fashion **)

local

val roundup_bound = 120;

fun add thy depth stem export (name, morph) (deps, marked) =
  if depth > roundup_bound
  then error "Roundup bound exceeded (sublocale relation probably not terminating)."
  else
    let
      val instance = instance_of thy name (morph $> stem $> export);
    in
      if redundant_ident thy marked (name, instance) then (deps, marked)
      else
        let
          (*no inheritance of mixins, regardless of requests by clients*)
          val dependencies =
            dependencies_of thy name |> map (fn dep as {morphisms = (morph', export'), ...} =>
              (#name dep, morph' $> export' $> compose_mixins (mixins_of thy name (#serial dep))));
          val marked' = insert_idents (name, instance) marked;
          val (deps', marked'') =
            fold_rev (add thy (depth + 1) (morph $> stem) export) dependencies
              ([], marked');
        in ((name, morph $> stem) :: deps' @ deps, marked'') end
    end;

in

(* Note that while identifiers always have the external (exported) view, activate_dep
   is presented with the internal view. *)

fun roundup thy activate_dep export (name, morph) (marked, input) =
  let
    (* Find all dependencies including new ones (which are dependencies enriching
      existing registrations). *)
    val (dependencies, marked') =
      add thy 0 Morphism.identity export (name, morph) ([], empty_idents);
    (* Filter out fragments from marked; these won't be activated. *)
    val dependencies' = filter_out (fn (name, morph) =>
      redundant_ident thy marked (name, instance_of thy name (morph $> export))) dependencies;
  in
    (merge_idents (marked, marked'), input |> fold_rev activate_dep dependencies')
  end;

end;


(*** Registrations: interpretations in theories or proof contexts ***)

val total_ident_ord = prod_ord fast_string_ord (list_ord Term_Ord.fast_term_ord);
structure Idtab = Table(type key = string * term list val ord = total_ident_ord);

type reg = {morphisms: morphism * morphism, pos: Position.T, serial: serial};
type regs = reg Idtab.table;

val join_regs : regs * regs -> regs =
  Idtab.join (fn id => fn (reg1, reg2) =>
    if #serial reg1 = #serial reg2 then raise Idtab.SAME else raise Idtab.DUP id);

(* FIXME consolidate with locale dependencies, consider one data slot only *)
structure Global_Registrations = Theory_Data'
(
  (*registrations, indexed by locale name and instance;
    unique registration serial points to mixin list*)
  type T = regs * mixins;
  val empty: T = (Idtab.empty, Inttab.empty);
  val extend = I;
  fun merge old_thys =
    let
      fun recursive_merge ((regs1, mixins1), (regs2, mixins2)) : T =
        (join_regs (regs1, regs2), merge_mixins (mixins1, mixins2))
        handle Idtab.DUP id =>
          (*distinct interpretations with same base: merge their mixins*)
          let
            val reg1 = Idtab.lookup regs1 id |> the;
            val reg2 = Idtab.lookup regs2 id |> the;
            val reg2' =
             {morphisms = #morphisms reg2,
              pos = Position.thread_data (),
              serial = #serial reg1};
            val regs2' = Idtab.update (id, reg2') regs2;
            val mixins2' = rename_mixin (#serial reg2, #serial reg1) mixins2;
            val _ =
              warning ("Removed duplicate interpretation after retrieving its mixins" ^
                Position.here_list [#pos reg1, #pos reg2] ^ ":\n  " ^
                Pretty.string_of (pretty_reg_inst (Syntax.init_pretty_global (#1 old_thys)) [] id));
          in recursive_merge ((regs1, mixins1), (regs2', mixins2')) end;
    in recursive_merge end;
);

structure Local_Registrations = Proof_Data
(
  type T = Global_Registrations.T;
  val init = Global_Registrations.get;
);

val get_registrations = Context.cases Global_Registrations.get Local_Registrations.get;

fun map_registrations f (Context.Theory thy) = Context.Theory (Global_Registrations.map f thy)
  | map_registrations f (Context.Proof ctxt) = Context.Proof (Local_Registrations.map f ctxt);


(* Primitive operations *)

fun add_reg thy export (name, morph) =
  let
    val reg = {morphisms = (morph, export), pos = Position.thread_data (), serial = serial ()};
    val id = (name, instance_of thy name (morph $> export));
  in (map_registrations o apfst) (Idtab.insert (K false) (id, reg)) end;

fun add_mixin serial' mixin =
  (* registration to be amended identified by its serial id *)
  (map_registrations o apsnd) (insert_mixin serial' mixin);

val get_regs = #1 o get_registrations;

fun get_mixins context (name, morph) =
  let
    val thy = Context.theory_of context;
    val (regs, mixins) = get_registrations context;
  in
    (case Idtab.lookup regs (name, instance_of thy name morph) of
      NONE => []
    | SOME {serial, ...} => lookup_mixins mixins serial)
  end;

fun collect_mixins context (name, morph) =
  let
    val thy = Context.theory_of context;
  in
    roundup thy (fn dep => fn mixins => merge (eq_snd op =) (mixins, get_mixins context dep))
      Morphism.identity (name, morph)
      (insert_idents (name, instance_of thy name morph) empty_idents, [])
    |> snd |> filter (snd o fst)  (* only inheritable mixins *)
    |> (fn x => merge (eq_snd op =) (x, get_mixins context (name, morph)))
    |> compose_mixins
  end;


(*** Activate context elements of locale ***)

fun activate_err msg kind (name, morph) context =
  cat_error msg ("The above error(s) occurred while activating " ^ kind ^ " of locale instance\n" ^
    (pretty_reg (Context.proof_of context) Morphism.identity (name, morph) |>
      Pretty.string_of));

fun init_element elem context =
  context
  |> Context.mapping I (Thm.unchecked_hyps #> Context_Position.not_really)
  |> Element.init elem
  |> Context.mapping I (fn ctxt =>
      let val ctxt0 = Context.proof_of context
      in ctxt |> Context_Position.restore_visible ctxt0 |> Thm.restore_hyps ctxt0 end);


(* Potentially lazy notes *)

fun make_notes kind = map (fn ((b, atts), facts) =>
  if null atts andalso forall (null o #2) facts
  then Lazy_Notes (kind, (b, Lazy.value (maps #1 facts)))
  else Notes (kind, [((b, atts), facts)]));

fun lazy_notes thy loc =
  rev (#notes (the_locale thy loc))
  |> maps (fn ((kind, notes), _) => make_notes kind notes);

fun consolidate_notes elems =
  elems
  |> map_filter (fn Lazy_Notes (_, (_, ths)) => SOME ths | _ => NONE)
  |> Lazy.consolidate
  |> ignore;

fun force_notes (Lazy_Notes (kind, (b, ths))) = Notes (kind, [((b, []), [(Lazy.force ths, [])])])
  | force_notes elem = elem;


(* Declarations, facts and entire locale content *)

val trace_locales =
  Attrib.setup_config_bool (Binding.make ("trace_locales", \<^here>)) (K false);

fun tracing context msg =
  if Config.get context trace_locales then Output.tracing msg else ();
  
fun trace kind (name, morph) context =
  tracing (Context.proof_of context) ("Activating " ^ kind ^ " of " ^
    (pretty_reg (Context.proof_of context) Morphism.identity (name, morph) |> Pretty.string_of));

fun activate_syntax_decls (name, morph) context =
  let
    val _ = trace "syntax" (name, morph) context;
    val thy = Context.theory_of context;
    val {syntax_decls, ...} = the_locale thy name;
  in
    context
    |> fold_rev (fn (decl, _) => decl morph) syntax_decls
      handle ERROR msg => activate_err msg "syntax" (name, morph) context
  end;

fun activate_notes activ_elem transfer context export' (name, morph) input =
  let
    val thy = Context.theory_of context;
    val mixin =
      (case export' of
        NONE => Morphism.identity
      | SOME export => collect_mixins context (name, morph $> export) $> export);
    val morph' = transfer input $> morph $> mixin;
    val notes' = map (Element.transform_ctxt morph') (lazy_notes thy name);
  in
    (notes', input) |-> fold (fn elem => fn res =>
      activ_elem (Element.transform_ctxt (transfer res) elem) res)
  end handle ERROR msg => activate_err msg "facts" (name, morph) context;

fun activate_notes_trace activ_elem transfer context export' (name, morph) context' =
  let
    val _ = trace "facts" (name, morph) context';
  in
    activate_notes activ_elem transfer context export' (name, morph) context'
  end;

fun activate_all name thy activ_elem transfer (marked, input) =
  let
    val {parameters = (_, params), spec = (asm, defs), ...} = the_locale thy name;
    val input' = input |>
      (not (null params) ?
        activ_elem (Fixes (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) params))) |>
      (* FIXME type parameters *)
      (case asm of SOME A => activ_elem (Assumes [(Binding.empty_atts, [(A, [])])]) | _ => I) |>
      (not (null defs) ?
        activ_elem (Defines (map (fn def => (Binding.empty_atts, (def, []))) defs)));
    val activate = activate_notes activ_elem transfer (Context.Theory thy) NONE;
  in
    roundup thy activate Morphism.identity (name, Morphism.identity) (marked, input')
  end;


(** Public activation functions **)

fun activate_facts export dep context =
  context
  |> Context_Position.set_visible_generic false
  |> pair (Idents.get context)
  |> roundup (Context.theory_of context)
      (activate_notes_trace init_element Morphism.transfer_morphism'' context export)
      (the_default Morphism.identity export) dep
  |-> Idents.put
  |> Context_Position.restore_visible_generic context;

fun activate_declarations dep = Context.proof_map (fn context =>
  context
  |> Context_Position.set_visible_generic false
  |> pair (Idents.get context)
  |> roundup (Context.theory_of context) activate_syntax_decls Morphism.identity dep
  |-> Idents.put
  |> Context_Position.restore_visible_generic context);

fun init name thy =
  let
    val context = Context.Proof (Proof_Context.init_global thy);
    val marked = Idents.get context;
  in
    context
    |> Context_Position.set_visible_generic false
    |> pair empty_idents
    |> activate_all name thy init_element Morphism.transfer_morphism''
    |-> (fn marked' => Idents.put (merge_idents (marked, marked')))
    |> Context_Position.restore_visible_generic context
    |> Context.proof_of
  end;


(*** Add and extend registrations ***)

type registration = Locale.registration;

fun amend_registration {mixin = NONE, ...} context = context
  | amend_registration {inst = (name, morph), mixin = SOME mixin, export} context =
      let
        val thy = Context.theory_of context;
        val ctxt = Context.proof_of context;

        val regs = get_regs context;
        val base = instance_of thy name (morph $> export);
        val serial' =
          (case Idtab.lookup regs (name, base) of
            NONE =>
              error ("No interpretation of locale " ^ quote (markup_name ctxt name) ^
                " with\nparameter instantiation " ^
                space_implode " " (map (quote o Syntax.string_of_term_global thy) base) ^
                " available")
          | SOME {serial = serial', ...} => serial');
      in
        add_mixin serial' mixin context
      end;

(* Note that a registration that would be subsumed by an existing one will not be
   generated, and it will not be possible to amend it. *)

fun add_registration {inst = (name, base_morph), mixin, export} context =
  let
    val thy = Context.theory_of context;
    val pos_morph = Morphism.binding_morphism "position" (Binding.set_pos (Position.thread_data ()));
    val mix_morph = (case mixin of NONE => base_morph | SOME (mix, _) => base_morph $> mix);
    val inst = instance_of thy name mix_morph;
    val idents = Idents.get context;
  in
    if redundant_ident thy idents (name, inst) then context  (* FIXME amend mixins? *)
    else
      (idents, context)
      (* add new registrations with inherited mixins *)
      |> roundup thy (add_reg thy export) export (name, mix_morph) |> #2
      (* add mixin *)
      |> amend_registration {inst = (name, mix_morph), mixin = mixin, export = export}
      (* activate import hierarchy as far as not already active *)
      |> activate_facts (SOME export) (name, mix_morph $> pos_morph)
  end;

val add_registration_theory' = Context.theory_map o add_registration;

val add_registration_theory = Local_Theory.raw_theory o add_registration_theory';

fun add_registration_local_theory' registration lthy =
  let val n = Local_Theory.level lthy in
    lthy
    |> Local_Theory.map_contexts (fn level =>
      level = n - 1 ? Context.proof_map (add_registration registration))
  end;

fun add_registration_local_theory registration =
  Local_Theory.mark_brittle #> add_registration_local_theory' registration

fun add_registration_proof registration ctxt = ctxt
  |> Proof_Context.set_stmt false
  |> Context.proof_map (add_registration registration)
  |> Proof_Context.restore_stmt ctxt;


(*** Dependencies ***)

fun registrations_of context loc =
  Idtab.fold_rev (fn ((name, _), {morphisms, ...}) =>
    name = loc ? cons (name, morphisms)) (get_regs context) []
  (*with inherited mixins*)
  |> map (fn (name, (base, export)) =>
      (name, base $> (collect_mixins context (name, base $> export)) $> export));

fun add_dependency' loc {inst = (name, morph), mixin, export} thy =
  let
    val dep = make_dep (name, (morph, export));
    val add_dep =
      apfst (cons dep) #>
      apsnd (case mixin of NONE => I | SOME mixin => insert_mixin (#serial dep) mixin);
    val thy' = change_locale loc (apsnd add_dep) thy;
    val context' = Context.Theory thy';
    val (_, regs) =
      fold_rev (roundup thy' cons export)
        (registrations_of context' loc) (Idents.get context', []);
  in
    fold_rev (fn inst => add_registration_theory' {inst = inst, mixin = NONE, export = export})
      regs thy'
  end;

fun add_dependency loc registration =
  Local_Theory.raw_theory (add_dependency' loc registration)
  #> add_registration_local_theory' registration;


(*** Storing results ***)

fun add_facts loc kind facts ctxt =
  if null facts then ctxt
  else
    let
      val stored_notes = ((kind, map Attrib.trim_context_fact facts), serial ());
      val applied_notes = make_notes kind facts;

      fun apply_notes morph = applied_notes |> fold (fn elem => fn context =>
        let val elem' = Element.transform_ctxt (Morphism.transfer_morphism'' context $> morph) elem
        in Element.init elem' context end);
      val apply_registrations = Context.theory_map (fn context =>
        fold_rev (apply_notes o #2) (registrations_of context loc) context);
    in
      ctxt
      |> Attrib.local_notes kind facts |> #2
      |> Proof_Context.background_theory
        ((change_locale loc o apfst o apsnd) (cons stored_notes) #> apply_registrations)
    end;

fun add_declaration loc syntax decl =
  syntax ?
    Proof_Context.background_theory ((change_locale loc o apfst o apfst) (cons (decl, serial ())))
  #> add_facts loc "" [(Binding.empty_atts, Attrib.internal_declaration decl)];


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

fun get_thms which ctxt =
  map (Thm.transfer' ctxt) (which (Thms.get (Context.Proof ctxt)));

val get_witnesses = get_thms #1;
val get_intros = get_thms #2;
val get_unfolds = get_thms #3;

val witness_add =
  Thm.declaration_attribute (fn th =>
    Thms.map (fn (x, y, z) => (Thm.add_thm (Thm.trim_context th) x, y, z)));

val intro_add =
  Thm.declaration_attribute (fn th =>
    Thms.map (fn (x, y, z) => (x, Thm.add_thm (Thm.trim_context th) y, z)));

val unfold_add =
  Thm.declaration_attribute (fn th =>
    Thms.map (fn (x, y, z) => (x, y, Thm.add_thm (Thm.trim_context th) z)));


(* Tactics *)

fun intro_locales_tac {strict, eager} ctxt =
  (if strict then Method.intros_tac else Method.try_intros_tac) ctxt
    (get_witnesses ctxt @ get_intros ctxt @ (if eager then get_unfolds ctxt else []));

val _ = Theory.setup
 (Method.setup \<^binding>\<open>intro_locales\<close>
    (Scan.succeed (METHOD o intro_locales_tac {strict = false, eager = false}))
    "back-chain introduction rules of locales without unfolding predicates" #>
  Method.setup \<^binding>\<open>unfold_locales\<close>
    (Scan.succeed (METHOD o intro_locales_tac {strict = false, eager = true}))
    "back-chain all introduction rules of locales");


(*** diagnostic commands and interfaces ***)

fun get_locales thy = map #1 (Name_Space.dest_table (Locales.get thy));

fun pretty_locales thy verbose =
  Pretty.block
    (Pretty.breaks
      (Pretty.str "locales:" ::
        map (Pretty.mark_str o #1)
          (Name_Space.markup_table verbose (Proof_Context.init_global thy) (Locales.get thy))));

fun pretty_locale thy show_facts name =
  let
    val locale_ctxt = init name thy;
    fun cons_elem (elem as Notes _) = show_facts ? cons elem
      | cons_elem (elem as Lazy_Notes _) = show_facts ? cons elem
      | cons_elem elem = cons elem;
    val elems =
      activate_all name thy cons_elem (K (Morphism.transfer_morphism thy)) (empty_idents, [])
      |> snd |> rev
      |> tap consolidate_notes
      |> map force_notes;
  in
    Pretty.block (Pretty.keyword1 "locale" :: Pretty.brk 1 :: pretty_name locale_ctxt name ::
      maps (fn elem => [Pretty.fbrk, Pretty.chunks (Element.pretty_ctxt locale_ctxt elem)]) elems)
  end;

fun pretty_registrations ctxt name =
  (case registrations_of (Context.Proof ctxt) name of
    [] => Pretty.str "no interpretations"
  | regs => Pretty.big_list "interpretations:" (map (pretty_reg ctxt Morphism.identity) (rev regs)));

fun pretty_locale_deps thy =
  let
    fun make_node name =
     {name = name,
      parents = map #name (dependencies_of thy name),
      body = pretty_locale thy false name};
    val names = sort_strings (Name_Space.fold_table (cons o #1) (Locales.get thy) []);
  in map make_node names end;

type locale_dependency =
  {source: string, target: string, prefix: (string * bool) list, morphism: morphism,
    pos: Position.T, serial: serial};

fun dest_dependencies prev_thys thy =
  let
    fun remove_prev loc prev_thy deps =
      (case get_locale prev_thy loc of
        NONE => deps
      | SOME (Loc {dependencies = prev_deps, ...}) =>
          if eq_list eq_dep (prev_deps, deps) then []
          else subtract eq_dep prev_deps deps);
    fun result loc (dep: dep) =
      let val morphism = op $> (#morphisms dep) in
       {source = #name dep,
        target = loc,
        prefix = Morphism.binding_prefix morphism,
        morphism = morphism,
        pos = #pos dep,
        serial = #serial dep}
      end;
    fun add (loc, Loc {dependencies = deps, ...}) =
      fold (cons o result loc) (fold (remove_prev loc) prev_thys deps);
  in
    Name_Space.fold_table add (Locales.get thy) []
    |> sort (int_ord o apply2 #serial)
  end;

end;
