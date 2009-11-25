(*  Title:      Pure/variable.ML
    Author:     Makarius

Fixed type/term variables and polymorphic term abbreviations.
*)

signature VARIABLE =
sig
  val is_body: Proof.context -> bool
  val set_body: bool -> Proof.context -> Proof.context
  val restore_body: Proof.context -> Proof.context -> Proof.context
  val names_of: Proof.context -> Name.context
  val fixes_of: Proof.context -> (string * string) list
  val binds_of: Proof.context -> (typ * term) Vartab.table
  val maxidx_of: Proof.context -> int
  val sorts_of: Proof.context -> sort list
  val constraints_of: Proof.context -> typ Vartab.table * sort Vartab.table
  val is_declared: Proof.context -> string -> bool
  val is_fixed: Proof.context -> string -> bool
  val newly_fixed: Proof.context -> Proof.context -> string -> bool
  val add_fixed: Proof.context -> term -> (string * typ) list -> (string * typ) list
  val default_type: Proof.context -> string -> typ option
  val def_type: Proof.context -> bool -> indexname -> typ option
  val def_sort: Proof.context -> indexname -> sort option
  val declare_names: term -> Proof.context -> Proof.context
  val declare_constraints: term -> Proof.context -> Proof.context
  val declare_term: term -> Proof.context -> Proof.context
  val declare_typ: typ -> Proof.context -> Proof.context
  val declare_prf: Proofterm.proof -> Proof.context -> Proof.context
  val declare_thm: thm -> Proof.context -> Proof.context
  val thm_context: thm -> Proof.context
  val variant_frees: Proof.context -> term list -> (string * 'a) list -> (string * 'a) list
  val bind_term: indexname * term option -> Proof.context -> Proof.context
  val expand_binds: Proof.context -> term -> term
  val lookup_const: Proof.context -> string -> string option
  val is_const: Proof.context -> string -> bool
  val declare_const: string * string -> Proof.context -> Proof.context
  val add_fixes: string list -> Proof.context -> string list * Proof.context
  val add_fixes_direct: string list -> Proof.context -> Proof.context
  val auto_fixes: term -> Proof.context -> Proof.context
  val variant_fixes: string list -> Proof.context -> string list * Proof.context
  val invent_types: sort list -> Proof.context -> (string * sort) list * Proof.context
  val export_terms: Proof.context -> Proof.context -> term list -> term list
  val exportT_terms: Proof.context -> Proof.context -> term list -> term list
  val exportT: Proof.context -> Proof.context -> thm list -> thm list
  val export_prf: Proof.context -> Proof.context -> Proofterm.proof -> Proofterm.proof
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val export_morphism: Proof.context -> Proof.context -> morphism
  val importT_inst: term list -> Proof.context -> ((indexname * sort) * typ) list * Proof.context
  val import_inst: bool -> term list -> Proof.context ->
    (((indexname * sort) * typ) list * ((indexname * typ) * term) list) * Proof.context
  val importT_terms: term list -> Proof.context -> term list * Proof.context
  val import_terms: bool -> term list -> Proof.context -> term list * Proof.context
  val importT: thm list -> Proof.context -> ((ctyp * ctyp) list * thm list) * Proof.context
  val import_prf: bool -> Proofterm.proof -> Proof.context -> Proofterm.proof * Proof.context
  val import: bool -> thm list -> Proof.context ->
    (((ctyp * ctyp) list * (cterm * cterm) list) * thm list) * Proof.context
  val tradeT: (Proof.context -> thm list -> thm list) -> Proof.context -> thm list -> thm list
  val trade: (Proof.context -> thm list -> thm list) -> Proof.context -> thm list -> thm list
  val focus: cterm -> Proof.context -> ((string * cterm) list * cterm) * Proof.context
  val focus_subgoal: int -> thm -> Proof.context -> ((string * cterm) list * cterm) * Proof.context
  val warn_extra_tfrees: Proof.context -> Proof.context -> unit
  val polymorphic_types: Proof.context -> term list -> (indexname * sort) list * term list
  val polymorphic: Proof.context -> term list -> term list
end;

structure Variable: VARIABLE =
struct

(** local context data **)

datatype data = Data of
 {is_body: bool,                        (*inner body mode*)
  names: Name.context,                  (*type/term variable names*)
  consts: string Symtab.table,          (*consts within the local scope*)
  fixes: (string * string) list,        (*term fixes -- extern/intern*)
  binds: (typ * term) Vartab.table,     (*term bindings*)
  type_occs: string list Symtab.table,  (*type variables -- possibly within term variables*)
  maxidx: int,                          (*maximum var index*)
  sorts: sort OrdList.T,                (*declared sort occurrences*)
  constraints:
    typ Vartab.table *                  (*type constraints*)
    sort Vartab.table};                 (*default sorts*)

fun make_data (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =
  Data {is_body = is_body, names = names, consts = consts, fixes = fixes, binds = binds,
    type_occs = type_occs, maxidx = maxidx, sorts = sorts, constraints = constraints};

structure Data = Proof_Data
(
  type T = data;
  fun init _ =
    make_data (false, Name.context, Symtab.empty, [], Vartab.empty, Symtab.empty,
      ~1, [], (Vartab.empty, Vartab.empty));
);

fun map_data f =
  Data.map (fn Data {is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints} =>
    make_data (f (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints)));

fun map_names f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, f names, consts, fixes, binds, type_occs, maxidx, sorts, constraints));

fun map_consts f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, f consts, fixes, binds, type_occs, maxidx, sorts, constraints));

fun map_fixes f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, consts, f fixes, binds, type_occs, maxidx, sorts, constraints));

fun map_binds f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, consts, fixes, f binds, type_occs, maxidx, sorts, constraints));

fun map_type_occs f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, consts, fixes, binds, f type_occs, maxidx, sorts, constraints));

fun map_maxidx f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, consts, fixes, binds, type_occs, f maxidx, sorts, constraints));

fun map_sorts f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, consts, fixes, binds, type_occs, maxidx, f sorts, constraints));

fun map_constraints f =
  map_data (fn (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (is_body, names, consts, fixes, binds, type_occs, maxidx, sorts, f constraints));

fun rep_data ctxt = Data.get ctxt |> (fn Data args => args);

val is_body = #is_body o rep_data;

fun set_body b =
  map_data (fn (_, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints) =>
    (b, names, consts, fixes, binds, type_occs, maxidx, sorts, constraints));

fun restore_body ctxt = set_body (is_body ctxt);

val names_of = #names o rep_data;
val fixes_of = #fixes o rep_data;
val binds_of = #binds o rep_data;
val type_occs_of = #type_occs o rep_data;
val maxidx_of = #maxidx o rep_data;
val sorts_of = #sorts o rep_data;
val constraints_of = #constraints o rep_data;

val is_declared = Name.is_declared o names_of;
fun is_fixed ctxt x = exists (fn (_, y) => x = y) (fixes_of ctxt);
fun newly_fixed inner outer x = is_fixed inner x andalso not (is_fixed outer x);

fun add_fixed ctxt = Term.fold_aterms
  (fn Free (x, T) => if is_fixed ctxt x then insert (op =) (x, T) else I | _ => I);



(** declarations **)

(* default sorts and types *)

fun default_type ctxt x = Vartab.lookup (#1 (constraints_of ctxt)) (x, ~1);

fun def_type ctxt pattern xi =
  let val {binds, constraints = (types, _), ...} = rep_data ctxt in
    (case Vartab.lookup types xi of
      NONE =>
        if pattern then NONE
        else Vartab.lookup binds xi |> Option.map (TypeInfer.polymorphicT o #1)
    | some => some)
  end;

val def_sort = Vartab.lookup o #2 o constraints_of;


(* names *)

fun declare_type_names t =
  map_names (fold_types (fold_atyps Term.declare_typ_names) t) #>
  map_maxidx (fold_types Term.maxidx_typ t);

fun declare_names t =
  declare_type_names t #>
  map_names (fold_aterms Term.declare_term_frees t) #>
  map_maxidx (Term.maxidx_term t);


(* type occurrences *)

fun decl_type_occsT T = fold_atyps (fn TFree (a, _) => Symtab.default (a, []) | _ => I) T;

val decl_type_occs = fold_term_types
  (fn Free (x, _) => fold_atyps (fn TFree (a, _) => Symtab.insert_list (op =) (a, x) | _ => I)
    | _ => decl_type_occsT);

val declare_type_occsT = map_type_occs o fold_types decl_type_occsT;
val declare_type_occs = map_type_occs o decl_type_occs;


(* constraints *)

fun constrain_tvar (xi, S) =
  if S = dummyS then Vartab.delete_safe xi else Vartab.update (xi, S);

fun declare_constraints t = map_constraints (fn (types, sorts) =>
  let
    val types' = fold_aterms
      (fn Free (x, T) => Vartab.update ((x, ~1), T)
        | Var v => Vartab.update v
        | _ => I) t types;
    val sorts' = fold_types (fold_atyps
      (fn TFree (x, S) => constrain_tvar ((x, ~1), S)
        | TVar v => constrain_tvar v
        | _ => I)) t sorts;
  in (types', sorts') end)
  #> declare_type_occsT t
  #> declare_type_names t;


(* common declarations *)

fun declare_internal t =
  declare_names t #>
  declare_type_occs t #>
  map_sorts (Sorts.insert_term t);

fun declare_term t =
  declare_internal t #>
  declare_constraints t;

val declare_typ = declare_term o Logic.mk_type;

val declare_prf = Proofterm.fold_proof_terms declare_internal (declare_internal o Logic.mk_type);

val declare_thm = Thm.fold_terms declare_internal;
fun thm_context th = declare_thm th (ProofContext.init (Thm.theory_of_thm th));


(* renaming term/type frees *)

fun variant_frees ctxt ts frees =
  let
    val names = names_of (fold declare_names ts ctxt);
    val xs = fst (Name.variants (map #1 frees) names);
  in xs ~~ map snd frees end;



(** term bindings **)

fun bind_term (xi, NONE) = map_binds (Vartab.delete_safe xi)
  | bind_term ((x, i), SOME t) =
      let
        val u = Term.close_schematic_term t;
        val U = Term.fastype_of u;
      in declare_term u #> map_binds (Vartab.update ((x, i), (U, u))) end;

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



(** fixes **)

local

fun no_dups [] = ()
  | no_dups dups = error ("Duplicate fixed variable(s): " ^ commas_quote dups);

fun new_fixes names' xs xs' =
  map_names (K names') #>
  fold declare_fixed xs #>
  map_fixes (fn fixes => (rev (xs ~~ xs') @ fixes)) #>
  fold (declare_constraints o Syntax.free) xs' #>
  pair xs';

in

fun add_fixes xs ctxt =
  let
    val _ =
      (case filter (can Name.dest_skolem) xs of [] => ()
      | bads => error ("Illegal internal Skolem constant(s): " ^ commas_quote bads));
    val _ = no_dups (duplicates (op =) xs);
    val (ys, zs) = split_list (fixes_of ctxt);
    val names = names_of ctxt;
    val (xs', names') =
      if is_body ctxt then Name.variants xs names |>> map Name.skolem
      else (no_dups (inter (op =) xs ys); no_dups (inter (op =) xs zs);
        (xs, fold Name.declare xs names));
  in ctxt |> new_fixes names' xs xs' end;

fun variant_fixes raw_xs ctxt =
  let
    val names = names_of ctxt;
    val xs = map (fn x => Name.clean x |> can Name.dest_internal x ? Name.internal) raw_xs;
    val (xs', names') = Name.variants xs names |>> (is_body ctxt ? map Name.skolem);
  in ctxt |> new_fixes names' xs xs' end;

end;


fun add_fixes_direct xs ctxt = ctxt
  |> set_body false
  |> (snd o add_fixes xs)
  |> restore_body ctxt;

fun fix_frees t ctxt = ctxt
  |> add_fixes_direct
      (rev (fold_aterms (fn Free (x, _) =>
        if is_fixed ctxt x then I else insert (op =) x | _ => I) t []));

fun auto_fixes t ctxt =
  (if is_body ctxt then ctxt else fix_frees t ctxt)
  |> declare_term t;

fun invent_types Ss ctxt =
  let
    val tfrees = Name.invents (names_of ctxt) Name.aT (length Ss) ~~ Ss;
    val ctxt' = fold (declare_constraints o Logic.mk_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;



(** export -- generalize type/term variables (beware of closure sizes) **)

fun export_inst inner outer =
  let
    val declared_outer = is_declared outer;
    val fixes_inner = fixes_of inner;
    val fixes_outer = fixes_of outer;

    val gen_fixes = map #2 (take (length fixes_inner - length fixes_outer) fixes_inner);
    val still_fixed = not o member (op =) gen_fixes;

    val type_occs_inner = type_occs_of inner;
    fun gen_fixesT ts =
      Symtab.fold (fn (a, xs) =>
        if declared_outer a orelse exists still_fixed xs
        then I else cons a) (fold decl_type_occs ts type_occs_inner) [];
  in (gen_fixesT, gen_fixes) end;

fun exportT_inst inner outer = #1 (export_inst inner outer);

fun exportT_terms inner outer =
  let val mk_tfrees = exportT_inst inner outer in
    fn ts => ts |> map
      (Term_Subst.generalize (mk_tfrees ts, [])
        (fold (Term.fold_types Term.maxidx_typ) ts ~1 + 1))
  end;

fun export_terms inner outer =
  let val (mk_tfrees, tfrees) = export_inst inner outer in
    fn ts => ts |> map
      (Term_Subst.generalize (mk_tfrees ts, tfrees)
        (fold Term.maxidx_term ts ~1 + 1))
  end;

fun export_prf inner outer prf =
  let
    val (mk_tfrees, frees) = export_inst (declare_prf prf inner) outer;
    val tfrees = mk_tfrees [];
    val idx = Proofterm.maxidx_proof prf ~1 + 1;
    val gen_term = Term_Subst.generalize_option (tfrees, frees) idx;
    val gen_typ = Term_Subst.generalizeT_option tfrees idx;
  in Proofterm.map_proof_terms_option gen_term gen_typ prf end;


fun gen_export (mk_tfrees, frees) ths =
  let
    val tfrees = mk_tfrees (map Thm.full_prop_of ths);
    val maxidx = fold Thm.maxidx_thm ths ~1;
  in map (Thm.generalize (tfrees, frees) (maxidx + 1)) ths end;

fun exportT inner outer = gen_export (exportT_inst inner outer, []);
fun export inner outer = gen_export (export_inst inner outer);

fun export_morphism inner outer =
  let
    val fact = export inner outer;
    val term = singleton (export_terms inner outer);
    val typ = Logic.type_map term;
  in Morphism.morphism {binding = I, typ = typ, term = term, fact = fact} end;



(** import -- fix schematic type/term variables **)

fun importT_inst ts ctxt =
  let
    val tvars = rev (fold Term.add_tvars ts []);
    val (tfrees, ctxt') = invent_types (map #2 tvars) ctxt;
  in (tvars ~~ map TFree tfrees, ctxt') end;

fun import_inst is_open ts ctxt =
  let
    val ren = Name.clean #> (if is_open then I else Name.internal);
    val (instT, ctxt') = importT_inst ts ctxt;
    val vars = map (apsnd (Term_Subst.instantiateT instT)) (rev (fold Term.add_vars ts []));
    val (xs, ctxt'') = variant_fixes (map (ren o #1 o #1) vars) ctxt';
    val inst = vars ~~ map Free (xs ~~ map #2 vars);
  in ((instT, inst), ctxt'') end;

fun importT_terms ts ctxt =
  let val (instT, ctxt') = importT_inst ts ctxt
  in (map (Term_Subst.instantiate (instT, [])) ts, ctxt') end;

fun import_terms is_open ts ctxt =
  let val (inst, ctxt') = import_inst is_open ts ctxt
  in (map (Term_Subst.instantiate inst) ts, ctxt') end;

fun importT ths ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val (instT, ctxt') = importT_inst (map Thm.full_prop_of ths) ctxt;
    val insts' as (instT', _) = Thm.certify_inst thy (instT, []);
    val ths' = map (Thm.instantiate insts') ths;
  in ((instT', ths'), ctxt') end;

fun import_prf is_open prf ctxt =
  let
    val ts = rev (Proofterm.fold_proof_terms cons (cons o Logic.mk_type) prf []);
    val (insts, ctxt') = import_inst is_open ts ctxt;
  in (Proofterm.instantiate insts prf, ctxt') end;

fun import is_open ths ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val (insts, ctxt') = import_inst is_open (map Thm.full_prop_of ths) ctxt;
    val insts' = Thm.certify_inst thy insts;
    val ths' = map (Thm.instantiate insts') ths;
  in ((insts', ths'), ctxt') end;


(* import/export *)

fun gen_trade imp exp f ctxt ths =
  let val ((_, ths'), ctxt') = imp ths ctxt
  in exp ctxt' ctxt (f ctxt' ths') end;

val tradeT = gen_trade importT exportT;
val trade = gen_trade (import true) export;


(* focus on outermost parameters *)

fun forall_elim_prop t prop =
  Thm.beta_conversion false (Thm.capply (Thm.dest_arg prop) t)
  |> Thm.cprop_of |> Thm.dest_arg;

fun focus goal ctxt =
  let
    val cert = Thm.cterm_of (Thm.theory_of_cterm goal);
    val t = Thm.term_of goal;
    val ps = Term.variant_frees t (Term.strip_all_vars t);   (*as they are printed :-*)
    val (xs, Ts) = split_list ps;
    val (xs', ctxt') = variant_fixes xs ctxt;
    val ps' = ListPair.map (cert o Free) (xs', Ts);
    val goal' = fold forall_elim_prop ps' goal;
    val ctxt'' = ctxt' |> fold (declare_constraints o Thm.term_of) ps';
  in ((xs ~~ ps', goal'), ctxt'') end;

fun focus_subgoal i st =
  let
    val all_vars = Thm.fold_terms Term.add_vars st [];
    val no_binds = map (fn (xi, _) => (xi, NONE)) all_vars;
  in
    fold bind_term no_binds #>
    fold (declare_constraints o Var) all_vars #>
    focus (Thm.cprem_of st i)
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
    if null extras then ()
    else warning ("Introduced fixed type variable(s): " ^ commas tfrees ^ " in " ^
      space_implode " or " (map quote frees))
  end;


(* polymorphic terms *)

fun polymorphic_types ctxt ts =
  let
    val ctxt' = fold declare_term ts ctxt;
    val occs = type_occs_of ctxt;
    val occs' = type_occs_of ctxt';
    val types = Symtab.fold (fn (a, _) => if Symtab.defined occs a then I else cons a) occs' [];
    val idx = maxidx_of ctxt' + 1;
    val Ts' = (fold o fold_types o fold_atyps)
      (fn T as TFree _ =>
          (case Term_Subst.generalizeT types idx T of TVar v => insert (op =) v | _ => I)
        | _ => I) ts [];
    val ts' = map (Term_Subst.generalize (types, []) idx) ts;
  in (rev Ts', ts') end;

fun polymorphic ctxt ts = snd (polymorphic_types ctxt ts);

end;
