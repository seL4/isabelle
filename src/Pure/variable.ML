(*  Title:      Pure/variable.ML
    Author:     Makarius

Fixed type/term variables and polymorphic term abbreviations.
*)

signature VARIABLE =
sig
  val names_of: Proof.context -> Name.context
  val binds_of: Proof.context -> (typ * term) Vartab.table
  val maxidx_of: Proof.context -> int
  val constraints_of: Proof.context -> typ Vartab.table * sort Vartab.table
  val is_declared: Proof.context -> string -> bool
  val check_name: binding -> string
  val default_type: Proof.context -> string -> typ option
  val def_type: Proof.context -> bool -> indexname -> typ option
  val def_sort: Proof.context -> indexname -> sort option
  val declare_maxidx: int -> Proof.context -> Proof.context
  val declare_names: term -> Proof.context -> Proof.context
  val variant_names: Proof.context -> (string * 'a) list -> (string * 'a) list
  val declare_constraints: term -> Proof.context -> Proof.context
  val declare_internal: term -> Proof.context -> Proof.context
  val declare_term: term -> Proof.context -> Proof.context
  val declare_typ: typ -> Proof.context -> Proof.context
  val declare_prf: Proofterm.proof -> Proof.context -> Proof.context
  val declare_thm: thm -> Proof.context -> Proof.context
  val bind_term: indexname * term -> Proof.context -> Proof.context
  val unbind_term: indexname -> Proof.context -> Proof.context
  val maybe_bind_term: indexname * term option -> Proof.context -> Proof.context
  val expand_binds: Proof.context -> term -> term
  val lookup_const: Proof.context -> string -> string option
  val is_const: Proof.context -> string -> bool
  val declare_const: string * string -> Proof.context -> Proof.context
  val next_bound: string * typ -> Proof.context -> term * Proof.context
  val revert_bounds: Proof.context -> term -> term
  val is_body: Proof.context -> bool
  val set_body: bool -> Proof.context -> Proof.context
  val restore_body: Proof.context -> Proof.context -> Proof.context
  val improper_fixes: Proof.context -> Proof.context
  val restore_proper_fixes: Proof.context -> Proof.context -> Proof.context
  val is_improper: Proof.context -> string -> bool
  val is_fixed: Proof.context -> string -> bool
  val is_newly_fixed: Proof.context -> Proof.context -> string -> bool
  val fixed_ord: Proof.context -> string ord
  val intern_fixed: Proof.context -> string -> string
  val lookup_fixed: Proof.context -> string -> string option
  val revert_fixed: Proof.context -> string -> string
  val markup_fixed: Proof.context -> string -> Markup.T
  val markup: Proof.context -> string -> Markup.T
  val markup_entity_def: Proof.context -> string -> Markup.T
  val dest_fixes: Proof.context -> (string * string) list
  val add_fixed_names: Proof.context -> term -> string list -> string list
  val add_fixed: Proof.context -> term -> (string * typ) list -> (string * typ) list
  val add_newly_fixed: Proof.context -> Proof.context ->
    term -> (string * typ) list -> (string * typ) list
  val add_free_names: Proof.context -> term -> string list -> string list
  val add_frees: Proof.context -> term -> (string * typ) list -> (string * typ) list
  val add_fixes_binding: binding list -> Proof.context -> string list * Proof.context
  val add_fixes: string list -> Proof.context -> string list * Proof.context
  val add_fixes_direct: string list -> Proof.context -> Proof.context
  val add_fixes_implicit: term -> Proof.context -> Proof.context
  val fix_dummy_patterns: term -> Proof.context -> term * Proof.context
  val variant_fixes: string list -> Proof.context -> string list * Proof.context
  val gen_all: Proof.context -> thm -> thm
  val export_terms: Proof.context -> Proof.context -> term list -> term list
  val exportT_terms: Proof.context -> Proof.context -> term list -> term list
  val exportT: Proof.context -> Proof.context -> thm list -> thm list
  val export_prf: Proof.context -> Proof.context -> Proofterm.proof -> Proofterm.proof
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val export_morphism: Proof.context -> Proof.context -> morphism
  val invent_types: sort list -> Proof.context -> (string * sort) list * Proof.context
  val importT_inst: term list -> Proof.context -> typ TVars.table * Proof.context
  val import_inst: bool -> term list -> Proof.context ->
    (typ TVars.table * term Vars.table) * Proof.context
  val import_inst_revert: typ TVars.table * term Vars.table -> typ TFrees.table * term Frees.table
  val importT_terms: term list -> Proof.context -> term list * Proof.context
  val import_terms: bool -> term list -> Proof.context -> term list * Proof.context
  val importT: thm list -> Proof.context -> (ctyp TVars.table * thm list) * Proof.context
  val import_prf: bool -> Proofterm.proof -> Proof.context -> Proofterm.proof * Proof.context
  val import: bool -> thm list -> Proof.context ->
    ((ctyp TVars.table * cterm Vars.table) * thm list) * Proof.context
  val import_vars: Proof.context -> thm -> thm
  val tradeT: (Proof.context -> thm list -> thm list) -> Proof.context -> thm list -> thm list
  val trade: (Proof.context -> thm list -> thm list) -> Proof.context -> thm list -> thm list
  val dest_abs: term -> Proof.context -> ((string * typ) * term) * Proof.context
  val dest_abs_cterm: cterm -> Proof.context -> (cterm * cterm) * Proof.context
  val dest_all: term -> Proof.context -> ((string * typ) * term) * Proof.context
  val dest_all_cterm: cterm -> Proof.context -> (cterm * cterm) * Proof.context
  val is_bound_focus: Proof.context -> bool
  val set_bound_focus: bool -> Proof.context -> Proof.context
  val restore_bound_focus: Proof.context -> Proof.context -> Proof.context
  val focus_params: binding list option -> term -> Proof.context ->
    (string list * (string * typ) list) * Proof.context
  val focus: binding list option -> term -> Proof.context ->
    ((string * (string * typ)) list * term) * Proof.context
  val focus_cterm: binding list option -> cterm -> Proof.context ->
    ((string * cterm) list * cterm) * Proof.context
  val focus_subgoal: binding list option -> int -> thm -> Proof.context ->
    ((string * cterm) list * cterm) * Proof.context
  val warn_extra_tfrees: Proof.context -> Proof.context -> unit
  val polymorphic_types: Proof.context -> term list -> (indexname * sort) list * term list
  val polymorphic: Proof.context -> term list -> term list
end;

structure Variable: VARIABLE =
struct

(** local context data **)

type fixes = (string * bool) Name_Space.table;
val empty_fixes: fixes = Name_Space.empty_table Markup.fixedN;

datatype data = Data of
 {names: Name.context,                  (*type/term variable names*)
  consts: string Symtab.table,          (*consts within the local scope*)
  bounds: int * ((string * typ) * string) list,  (*next index, internal name, type, external name*)
  fixes: fixes,                         (*term fixes -- global name space, intern ~> extern*)
  binds: (typ * term) Vartab.table,     (*term bindings*)
  type_occs: string list Symtab.table,  (*type variables -- possibly within term variables*)
  maxidx: int,                          (*maximum var index*)
  constraints:
    typ Vartab.table *                  (*type constraints*)
    sort Vartab.table};                 (*default sorts*)

fun make_data (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =
  Data {names = names, consts = consts, bounds = bounds, fixes = fixes, binds = binds,
    type_occs = type_occs, maxidx = maxidx, constraints = constraints};

val empty_data =
  make_data (Name.context, Symtab.empty, (0, []), empty_fixes, Vartab.empty,
    Symtab.empty, ~1, (Vartab.empty, Vartab.empty));

structure Data = Proof_Data
(
  type T = data;
  fun init _ = empty_data;
);

fun map_data f =
  Data.map (fn Data {names, consts, bounds, fixes, binds, type_occs, maxidx, constraints} =>
    make_data (f (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints)));

fun map_names f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (f names, consts, bounds, fixes, binds, type_occs, maxidx, constraints));

fun map_consts f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, f consts, bounds, fixes, binds, type_occs, maxidx, constraints));

fun map_bounds f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, consts, f bounds, fixes, binds, type_occs, maxidx, constraints));

fun map_fixes f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, consts, bounds, f fixes, binds, type_occs, maxidx, constraints));

fun map_binds f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, consts, bounds, fixes, f binds, type_occs, maxidx, constraints));

fun map_type_occs f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, consts, bounds, fixes, binds, f type_occs, maxidx, constraints));

fun map_maxidx f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, consts, bounds, fixes, binds, type_occs, f maxidx, constraints));

fun map_constraints f =
  map_data (fn (names, consts, bounds, fixes, binds, type_occs, maxidx, constraints) =>
    (names, consts, bounds, fixes, binds, type_occs, maxidx, f constraints));

fun rep_data ctxt = Data.get ctxt |> (fn Data rep => rep);

val names_of = #names o rep_data;
val fixes_of = #fixes o rep_data;
val fixes_space = Name_Space.space_of_table o fixes_of;
val binds_of = #binds o rep_data;
val type_occs_of = #type_occs o rep_data;
val maxidx_of = #maxidx o rep_data;
val constraints_of = #constraints o rep_data;

val is_declared = Name.is_declared o names_of;

val check_name = Name_Space.base_name o tap Binding.check;



(** declarations **)

(* default sorts and types *)

fun default_type ctxt x = Vartab.lookup (#1 (constraints_of ctxt)) (x, ~1);

fun def_type ctxt pattern xi =
  let val {binds, constraints = (types, _), ...} = rep_data ctxt in
    (case Vartab.lookup types xi of
      NONE =>
        if pattern then NONE
        else Vartab.lookup binds xi |> Option.map (Type.mark_polymorphic o #1)
    | some => some)
  end;

val def_sort = Vartab.lookup o #2 o constraints_of;


(* maxidx *)

val declare_maxidx = map_maxidx o Integer.max;


(* type/term names *)

fun declare_type_names t =
  map_names (Term.declare_tfree_names t) #>
  map_maxidx (fold_types Term.maxidx_typ t);

fun declare_names t =
  declare_type_names t #>
  map_names (Term.declare_free_names t) #>
  map_maxidx (Term.maxidx_term t);

fun variant_names ctxt xs = Name.variant_names (names_of ctxt) xs;


(* type occurrences *)

fun decl_type_occsT T = fold_atyps (fn TFree (a, _) => Symtab.default (a, []) | _ => I) T;

val decl_type_occs = fold_term_types
  (fn Free (x, _) => fold_atyps (fn TFree (a, _) => Symtab.insert_list (op =) (a, x) | _ => I)
    | _ => decl_type_occsT);

val declare_type_occsT = map_type_occs o fold_types decl_type_occsT;
val declare_type_occs = map_type_occs o decl_type_occs;


(* constraints *)

fun constrain_tvar (xi, raw_S) =
  let val S = #2 (Term_Position.decode_positionS raw_S)
  in if S = dummyS then Vartab.delete_safe xi else Vartab.update (xi, S) end;

fun declare_constraints t = map_constraints (fn (types, sorts) =>
  let
    val types' = fold_aterms
      (fn Free (x, T) => Vartab.update ((x, ~1), T)
        | Var v => Vartab.update v
        | _ => I) t types;
    val sorts' = (fold_types o fold_atyps)
      (fn TFree (x, S) => constrain_tvar ((x, ~1), S)
        | TVar v => constrain_tvar v
        | _ => I) t sorts;
  in (types', sorts') end)
  #> declare_type_occsT t
  #> declare_type_names t;


(* common declarations *)

fun declare_internal t =
  declare_names t #>
  declare_type_occs t #>
  Thm.declare_term_sorts t;

fun declare_term t =
  declare_internal t #>
  declare_constraints t;

val declare_typ = declare_term o Logic.mk_type;

val declare_prf =
  Proofterm.fold_proof_terms_types declare_internal (declare_internal o Logic.mk_type);

val declare_thm = Thm.fold_terms {hyps = true} declare_internal;



(** term bindings **)

fun bind_term ((x, i), t) =
  let
    val u = Term.close_schematic_term t;
    val U = Term.fastype_of u;
  in declare_term u #> map_binds (Vartab.update ((x, i), (U, u))) end;

val unbind_term = map_binds o Vartab.delete_safe;

fun maybe_bind_term (xi, SOME t) = bind_term (xi, t)
  | maybe_bind_term (xi, NONE) = unbind_term xi;

fun expand_binds ctxt =
  let
    val binds = binds_of ctxt;
    val get = fn Var (xi, _) => Vartab.lookup binds xi | _ => NONE;
  in Envir.beta_norm o Envir.expand_term get end;



(** consts **)

val lookup_const = Symtab.lookup o #consts o rep_data;
val is_const = is_some oo lookup_const;

val declare_fixed = map_consts o Symtab.delete_safe;
val declare_const = map_consts o Symtab.update;



(** bounds **)

fun inc_bound (a, T) ctxt =
  let
    val b = Name.bound (#1 (#bounds (rep_data ctxt)));
    val ctxt' = ctxt |> map_bounds (fn (next, bounds) => (next + 1, ((b, T), a) :: bounds));
  in (Free (b, T), ctxt') end;

fun next_bound a ctxt =
  let val (x as Free (b, _), ctxt') = inc_bound a ctxt
  in if Name.is_declared (names_of ctxt') b then inc_bound a ctxt' else (x, ctxt') end;

fun revert_bounds ctxt t =
  (case #2 (#bounds (rep_data ctxt)) of
    [] => t
  | bounds =>
      let
        val names = Term.declare_free_names t (names_of ctxt);
        val xs = rev (Name.variants names (rev (map #2 bounds)));
        fun substs (((b, T), _), x') =
          let fun subst U = (Free (b, U), Syntax_Trans.mark_bound_abs (x', U))
          in [subst T, subst (Type_Annotation.ignore_type T)] end;
      in Term.subst_atomic (maps substs (bounds ~~ xs)) t end);



(** fixes **)

(* inner body mode *)

val inner_body = Config.declare_bool ("inner_body", \<^here>) (K false);
val is_body = Config.apply inner_body;
val set_body = Config.put inner_body;
val restore_body = set_body o is_body;


(* proper mode *)

val proper_fixes = Config.declare_bool ("proper_fixes", \<^here>) (K true);
val improper_fixes = Config.put proper_fixes false;
val restore_proper_fixes = Config.put proper_fixes o Config.apply proper_fixes;

fun is_improper ctxt x =
  (case Name_Space.lookup (fixes_of ctxt) x of
    SOME (_, proper) => not proper
  | NONE => false);


(* specialized name space *)

val is_fixed = Name_Space.defined o fixes_of;
fun is_newly_fixed inner outer = is_fixed inner andf (not o is_fixed outer);

val fixed_ord = Name_Space.entry_ord o fixes_space;
val intern_fixed = Name_Space.intern o fixes_space;

fun lookup_fixed ctxt x =
  let val x' = intern_fixed ctxt x
  in if is_fixed ctxt x' then SOME x' else NONE end;

fun revert_fixed ctxt x =
  (case Name_Space.lookup (fixes_of ctxt) x of
    SOME (x', _) => if intern_fixed ctxt x' = x then x' else x
  | NONE => x);

fun markup_fixed ctxt x =
  Name_Space.markup (fixes_space ctxt) x
  |> Markup.name (revert_fixed ctxt x);

fun markup ctxt x =
  if is_improper ctxt x then Markup.improper
  else if Name.is_skolem x then Markup.skolem
  else Markup.free;

val markup_entity_def = Name_Space.markup_def o fixes_space;

fun dest_fixes ctxt =
  Name_Space.fold_table (fn (x, (y, _)) => cons (y, x)) (fixes_of ctxt) []
  |> sort (Name_Space.entry_ord (fixes_space ctxt) o apply2 #2);


(* collect variables *)

fun add_free_names ctxt =
  fold_aterms (fn Free (x, _) => not (is_fixed ctxt x) ? insert (op =) x | _ => I);

fun add_frees ctxt =
  fold_aterms (fn Free (x, T) => not (is_fixed ctxt x) ? insert (op =) (x, T) | _ => I);

fun add_fixed_names ctxt =
  fold_aterms (fn Free (x, _) => is_fixed ctxt x ? insert (op =) x | _ => I);

fun add_fixed ctxt =
  fold_aterms (fn Free (x, T) => is_fixed ctxt x ? insert (op =) (x, T) | _ => I);

fun add_newly_fixed ctxt' ctxt =
  fold_aterms (fn Free (x, T) => is_newly_fixed ctxt' ctxt x ? insert (op =) (x, T) | _ => I);


(* declarations *)

local

fun err_dups dups =
  error ("Duplicate fixed variable(s): " ^ commas (map Binding.print dups));

fun new_fixed ((x, x'), pos) ctxt =
  if is_some (lookup_fixed ctxt x') then err_dups [Binding.make (x, pos)]
  else
    let
      val proper = Config.get ctxt proper_fixes;
      val context = Context.Proof ctxt
        |> Name_Space.map_naming (K Name_Space.global_naming)
        |> Context_Position.set_visible_generic false;
    in
      ctxt
      |> map_fixes
        (Name_Space.define context true (Binding.make (x', pos), (x, proper)) #> snd #>
          x <> "" ? Name_Space.alias_table Name_Space.global_naming (Binding.make (x, pos)) x')
      |> declare_fixed x
      |> declare_constraints (Syntax.free x')
  end;

fun new_fixes names' args =
  map_names (K names') #>
  fold new_fixed args #>
  pair (map (#2 o #1) args);

fun variant ctxt raw_xs =
  let
    val names = names_of ctxt;
    val xs = map (fn x => Name.clean x |> Name.is_internal x ? Name.internal) raw_xs;
    val (xs', names') = fold_map Name.variant xs names |>> (is_body ctxt ? map Name.skolem);
  in (names', xs ~~ xs') end;

in

fun add_fixes_binding bs ctxt =
  let
    val _ =
      (case filter (Name.is_skolem o Binding.name_of) bs of
        [] => ()
      | bads => error ("Illegal internal Skolem constant(s): " ^ commas (map Binding.print bads)));
    val _ =
      (case duplicates (op = o apply2 Binding.name_of) bs of
        [] => ()
      | dups => err_dups dups);

    val xs = map check_name bs;
    val names = names_of ctxt;
    val (xs', names') =
      if is_body ctxt then fold_map Name.variant xs names |>> map Name.skolem
      else (xs, fold Name.declare xs names);
  in ctxt |> new_fixes names' ((xs ~~ xs') ~~ map Binding.pos_of bs) end;

fun variant_fixes xs ctxt =
  let val (names', vs) = variant ctxt xs;
  in ctxt |> new_fixes names' (map (rpair Position.none) vs) end;

fun bound_fixes xs ctxt =
  let
    val (names', vs) = variant ctxt (map #1 xs);
    val (ys, ctxt') = fold_map next_bound (map2 (fn (x', _) => fn (_, T) => (x', T)) vs xs) ctxt;
    val fixes = map2 (fn (x, _) => fn Free (y, _) => ((x, y), Position.none)) vs ys;
  in ctxt' |> new_fixes names' fixes end;

end;

val add_fixes = add_fixes_binding o map Binding.name;

fun add_fixes_direct xs ctxt = ctxt
  |> set_body false
  |> (snd o add_fixes xs)
  |> restore_body ctxt;

fun add_fixes_implicit t ctxt = ctxt
  |> not (is_body ctxt) ? add_fixes_direct (rev (add_free_names ctxt t []));


(* dummy patterns *)

fun fix_dummy_patterns (Const ("Pure.dummy_pattern", T)) ctxt =
      let val ([x], ctxt') = ctxt |> set_body true |> add_fixes [Name.uu_] ||> restore_body ctxt
      in (Free (x, T), ctxt') end
  | fix_dummy_patterns (Abs (x, T, b)) ctxt =
      let val (b', ctxt') = fix_dummy_patterns b ctxt
      in (Abs (x, T, b'), ctxt') end
  | fix_dummy_patterns (t $ u) ctxt =
      let
        val (t', ctxt') = fix_dummy_patterns t ctxt;
        val (u', ctxt'') = fix_dummy_patterns u ctxt';
      in (t' $ u', ctxt'') end
  | fix_dummy_patterns a ctxt = (a, ctxt);



(** export -- generalize type/term variables (beware of closure sizes) **)

fun gen_all ctxt th =
  let
    val i = Thm.maxidx_thm th (maxidx_of ctxt) + 1;
    fun gen (x, T) = Thm.forall_elim (Thm.cterm_of ctxt (Var ((x, i), T)));
  in fold gen (Drule.outer_params (Thm.prop_of th)) th end;

fun export_inst inner outer =
  let
    val declared_outer = is_declared outer;
    val still_fixed = not o is_newly_fixed inner outer;

    val gen_fixes =
      Names.build (fixes_of inner |> Name_Space.fold_table (fn (y, _) =>
        not (is_fixed outer y) ? Names.add_set y));

    val type_occs_inner = type_occs_of inner;
    fun gen_fixesT ts =
      Names.build (fold decl_type_occs ts type_occs_inner |> Symtab.fold (fn (a, xs) =>
        if declared_outer a orelse exists still_fixed xs
        then I else Names.add_set a));
  in (gen_fixesT, gen_fixes) end;

fun exportT_inst inner outer = #1 (export_inst inner outer);

fun exportT_terms inner outer =
  let
    val mk_tfrees = exportT_inst inner outer;
    val maxidx = maxidx_of outer;
  in
    fn ts => ts |> map
      (Term_Subst.generalize (mk_tfrees ts, Names.empty)
        (fold (Term.fold_types Term.maxidx_typ) ts maxidx + 1))
  end;

fun export_terms inner outer =
  let
    val (mk_tfrees, tfrees) = export_inst inner outer;
    val maxidx = maxidx_of outer;
  in
    fn ts => ts |> map
      (Term_Subst.generalize (mk_tfrees ts, tfrees)
        (fold Term.maxidx_term ts maxidx + 1))
  end;

fun export_prf inner outer prf =
  let
    val (mk_tfrees, frees) = export_inst (declare_prf prf inner) outer;
    val tfrees = mk_tfrees [];
    val maxidx = maxidx_of outer;
    val idx = Proofterm.maxidx_proof prf maxidx + 1;
    val gen_term = Term_Subst.generalize_same (tfrees, frees) idx;
    val gen_typ = Term_Subst.generalizeT_same tfrees idx;
  in Same.commit (Proofterm.map_proof_terms_same gen_term gen_typ) prf end;


fun gen_export (mk_tfrees, frees) maxidx ths =
  let
    val tfrees = mk_tfrees (map Thm.full_prop_of ths);
    val idx = fold Thm.maxidx_thm ths maxidx + 1;
  in map (Thm.generalize (tfrees, frees) idx) ths end;

fun exportT inner outer = gen_export (exportT_inst inner outer, Names.empty) (maxidx_of outer);
fun export inner outer = gen_export (export_inst inner outer) (maxidx_of outer);

fun export_morphism inner outer =
  let
    val fact = export inner outer;
    val term = singleton (export_terms inner outer);
    val typ = Logic.type_map term;
  in
    Morphism.morphism "Variable.export"
      {binding = [], typ = [K typ], term = [K term], fact = [K fact]}
  end;



(** import -- fix schematic type/term variables **)

fun invent_types Ss ctxt =
  let
    val tfrees = Name.invent_types (names_of ctxt) Ss;
    val ctxt' = fold (declare_constraints o Logic.mk_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;

fun importT_inst ts ctxt =
  let
    val tvars = TVars.build (fold TVars.add_tvars ts) |> TVars.list_set;
    val (tfrees, ctxt') = invent_types (map #2 tvars) ctxt;
    val instT = TVars.build (fold2 (fn a => fn b => TVars.add (a, TFree b)) tvars tfrees);
  in (instT, ctxt') end;

fun import_inst is_open ts ctxt =
  let
    val ren = Name.clean #> (if is_open then I else Name.internal);
    val (instT, ctxt') = importT_inst ts ctxt;
    val vars =
      Vars.build (fold Vars.add_vars ts) |> Vars.list_set
      |> map (apsnd (Term_Subst.instantiateT instT));
    val (ys, ctxt'') = variant_fixes (map (ren o #1 o #1) vars) ctxt';
    val inst = Vars.build (fold2 (fn (x, T) => fn y => Vars.add ((x, T), Free (y, T))) vars ys);
  in ((instT, inst), ctxt'') end;

fun import_inst_revert (instT, inst) =
  let
    val instT' = TFrees.build (instT |> TVars.fold (fn (v, TFree w) => TFrees.add (w, TVar v)));
    val instantiateT' = Term_Subst.instantiateT_frees instT';
    val inst' =
      Frees.build (inst |> Vars.fold (fn ((xi, T), Free (y, U)) =>
        Frees.add ((y, instantiateT' U), Var (xi, instantiateT' T))));
  in (instT', inst') end;

fun importT_terms ts ctxt =
  let val (instT, ctxt') = importT_inst ts ctxt
  in (map (Term_Subst.instantiate (instT, Vars.empty)) ts, ctxt') end;

fun import_terms is_open ts ctxt =
  let val (inst, ctxt') = import_inst is_open ts ctxt
  in (map (Term_Subst.instantiate inst) ts, ctxt') end;

fun importT ths ctxt =
  let
    val (instT, ctxt') = importT_inst (map Thm.full_prop_of ths) ctxt;
    val instT' = TVars.map (K (Thm.ctyp_of ctxt')) instT;
    val ths' = map (Thm.instantiate (instT', Vars.empty)) ths;
  in ((instT', ths'), ctxt') end;

fun import_prf is_open prf ctxt =
  let
    val ts = rev (Proofterm.fold_proof_terms_types cons (cons o Logic.mk_type) prf []);
    val (insts, ctxt') = import_inst is_open ts ctxt;
  in (Proofterm.instantiate insts prf, ctxt') end;

fun import is_open ths ctxt =
  let
    val ((instT, inst), ctxt') = import_inst is_open (map Thm.full_prop_of ths) ctxt;
    val instT' = TVars.map (K (Thm.ctyp_of ctxt')) instT;
    val inst' = Vars.map (K (Thm.cterm_of ctxt')) inst;
    val ths' = map (Thm.instantiate (instT', inst')) ths;
  in (((instT', inst'), ths'), ctxt') end;

fun import_vars ctxt th =
  let val ((_, [th']), _) = ctxt |> set_body false |> import true [th];
  in th' end;


(* import/export *)

fun gen_trade imp exp f ctxt ths =
  let val ((_, ths'), ctxt') = imp ths ctxt
  in exp ctxt' ctxt (f ctxt' ths') end;

val tradeT = gen_trade importT exportT;
val trade = gen_trade (import true) export;


(* destruct binders *)

local

fun gen_dest_abs exn dest term_of arg ctxt =
  (case term_of arg of
    Abs (a, T, _) =>
      let
        val (x, ctxt') = yield_singleton bound_fixes (a, T) ctxt;
        val res = dest x arg handle Term.USED_FREE _ =>
          raise Fail ("Bad context: clash of fresh free for bound: " ^
            Syntax.string_of_term ctxt (Free (x, T)) ^ " vs. " ^
            Syntax.string_of_term ctxt' (Free (x, T)));
      in (res, ctxt') end
  | _ => raise exn ("dest_abs", [arg]));

in

val dest_abs = gen_dest_abs TERM Term.dest_abs_fresh I;
val dest_abs_cterm = gen_dest_abs CTERM Thm.dest_abs_fresh Thm.term_of;

fun dest_all t ctxt =
  (case t of
    Const ("Pure.all", _) $ u => dest_abs u ctxt
  | _ => raise TERM ("dest_all", [t]));

fun dest_all_cterm ct ctxt =
  (case Thm.term_of ct of
    Const ("Pure.all", _) $ _ => dest_abs_cterm (Thm.dest_arg ct) ctxt
  | _ => raise CTERM ("dest_all", [ct]));

end;


(* focus on outermost parameters: \<And>x y z. B *)

val bound_focus = Config.declare_bool ("bound_focus", \<^here>) (K false);
val is_bound_focus = Config.apply bound_focus;
val set_bound_focus = Config.put bound_focus;
val restore_bound_focus = set_bound_focus o is_bound_focus;

fun focus_params bindings t ctxt =
  let
    val ps = Syntax_Trans.variant_bounds ctxt t (Term.strip_all_vars t);
    val (xs, Ts) = split_list ps;
    val (xs', ctxt') =
      (case bindings of
        SOME bs => ctxt |> set_body true |> add_fixes_binding bs ||> restore_body ctxt
      | NONE => if is_bound_focus ctxt then bound_fixes ps ctxt else variant_fixes xs ctxt);
    val ps' = xs' ~~ Ts;
    val ctxt'' = ctxt' |> fold (declare_constraints o Free) ps';
  in ((xs, ps'), ctxt'') end;

fun focus bindings t ctxt =
  let
    val ((xs, ps), ctxt') = focus_params bindings t ctxt;
    val t' = Term.subst_bounds (rev (map Free ps), Term.strip_all_body t);
  in (((xs ~~ ps), t'), ctxt') end;

fun forall_elim_prop t prop =
  Thm.beta_conversion false (Thm.apply (Thm.dest_arg prop) t)
  |> Thm.cprop_of |> Thm.dest_arg;

fun focus_cterm bindings goal ctxt =
  let
    val ((xs, ps), ctxt') = focus_params bindings (Thm.term_of goal) ctxt;
    val ps' = map (Thm.cterm_of ctxt' o Free) ps;
    val goal' = fold forall_elim_prop ps' goal;
  in ((xs ~~ ps', goal'), ctxt') end;

fun focus_subgoal bindings i st =
  let
    val all_vars = Vars.build (Thm.fold_terms {hyps = false} Vars.add_vars st);
  in
    Vars.fold (unbind_term o #1 o #1) all_vars #>
    Vars.fold (declare_constraints o Var o #1) all_vars #>
    focus_cterm bindings (Thm.cprem_of st i)
  end;



(** implicit polymorphism **)

(* warn_extra_tfrees *)

fun warn_extra_tfrees ctxt1 ctxt2 =
  let
    fun occs_typ a = Term.exists_subtype (fn TFree (b, _) => a = b | _ => false);
    fun occs_free a x =
      (case def_type ctxt1 false (x, ~1) of
        SOME T => if occs_typ a T then I else cons (a, x)
      | NONE => cons (a, x));

    val occs1 = type_occs_of ctxt1;
    val occs2 = type_occs_of ctxt2;
    val extras = Symtab.fold (fn (a, xs) =>
      if Symtab.defined occs1 a then I else fold (occs_free a) xs) occs2 [];
    val tfrees = map #1 extras |> sort_distinct string_ord;
    val frees = map #2 extras |> sort_distinct string_ord;
  in
    if null extras orelse not (Context_Position.is_visible ctxt2) then ()
    else warning ("Introduced fixed type variable(s): " ^ commas tfrees ^ " in " ^
      space_implode " or " (map quote frees))
  end;


(* polymorphic terms *)

fun polymorphic_types ctxt ts =
  let
    val ctxt' = fold declare_term ts ctxt;
    val occs = type_occs_of ctxt;
    val occs' = type_occs_of ctxt';
    val types =
      Names.build (occs' |> Symtab.fold (fn (a, _) =>
        if Symtab.defined occs a then I else Names.add_set a));
    val idx = maxidx_of ctxt' + 1;
    val Ts' = (fold o fold_types o fold_atyps)
      (fn T as TFree _ =>
          (case Term_Subst.generalizeT types idx T of TVar v => insert (op =) v | _ => I)
        | _ => I) ts [];
    val ts' = map (Term_Subst.generalize (types, Names.empty) idx) ts;
  in (rev Ts', ts') end;

fun polymorphic ctxt ts = snd (polymorphic_types ctxt ts);

end;
