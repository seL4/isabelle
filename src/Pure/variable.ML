(*  Title:      Pure/variable.ML
    ID:         $Id$
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
  val constraints_of: Proof.context -> typ Vartab.table * sort Vartab.table
  val is_declared: Proof.context -> string -> bool
  val is_fixed: Proof.context -> string -> bool
  val newly_fixed: Proof.context -> Proof.context -> string -> bool
  val default_type: Proof.context -> string -> typ option
  val def_type: Proof.context -> bool -> indexname -> typ option
  val def_sort: Proof.context -> indexname -> sort option
  val declare_constraints: term -> Proof.context -> Proof.context
  val declare_internal: term -> Proof.context -> Proof.context
  val declare_term: term -> Proof.context -> Proof.context
  val declare_prf: Proofterm.proof -> Proof.context -> Proof.context
  val declare_thm: thm -> Proof.context -> Proof.context
  val thm_context: thm -> Proof.context
  val variant_frees: Proof.context -> term list -> (string * 'a) list -> (string * 'a) list
  val hidden_polymorphism: term -> typ -> (indexname * sort) list
  val add_binds: (indexname * term option) list -> Proof.context -> Proof.context
  val expand_binds: Proof.context -> term -> term
  val add_fixes: string list -> Proof.context -> string list * Proof.context
  val add_fixes_direct: string list -> Proof.context -> Proof.context
  val fix_frees: term -> Proof.context -> Proof.context
  val variant_fixes: string list -> Proof.context -> string list * Proof.context
  val invent_types: sort list -> Proof.context -> (string * sort) list * Proof.context
  val export_inst: Proof.context -> Proof.context -> string list * string list
  val exportT_inst: Proof.context -> Proof.context -> string list
  val export_terms: Proof.context -> Proof.context -> term list -> term list
  val exportT_terms: Proof.context -> Proof.context -> term list -> term list
  val exportT: Proof.context -> Proof.context -> thm list -> thm list
  val export_prf: Proof.context -> Proof.context -> Proofterm.proof -> Proofterm.proof
  val export: Proof.context -> Proof.context -> thm list -> thm list
  val importT_inst: term list -> Proof.context -> ((indexname * sort) * typ) list * Proof.context
  val import_inst: bool -> term list -> Proof.context ->
    (((indexname * sort) * typ) list * ((indexname * typ) * term) list) * Proof.context
  val importT_terms: term list -> Proof.context -> term list * Proof.context
  val import_terms: bool -> term list -> Proof.context -> term list * Proof.context
  val importT: thm list -> Proof.context -> (ctyp list * thm list) * Proof.context
  val import_prf: bool -> Proofterm.proof -> Proof.context -> Proofterm.proof * Proof.context
  val import: bool -> thm list -> Proof.context ->
    ((ctyp list * cterm list) * thm list) * Proof.context
  val tradeT: (Proof.context -> thm list -> thm list) -> Proof.context -> thm list -> thm list
  val trade: (Proof.context -> thm list -> thm list) -> Proof.context -> thm list -> thm list
  val focus: cterm -> Proof.context -> (cterm list * cterm) * Proof.context
  val focus_subgoal: int -> thm -> Proof.context -> (cterm list * cterm) * Proof.context
  val warn_extra_tfrees: Proof.context -> Proof.context -> unit
  val polymorphic: Proof.context -> term list -> term list
end;

structure Variable: VARIABLE =
struct

(** local context data **)

datatype data = Data of
 {is_body: bool,                        (*inner body mode*)
  names: Name.context,                  (*type/term variable names*)
  fixes: (string * string) list,        (*term fixes -- extern/intern*)
  binds: (typ * term) Vartab.table,     (*term bindings*)
  type_occs: string list Symtab.table,  (*type variables -- possibly within term variables*)
  constraints:
    typ Vartab.table *                  (*type constraints*)
    sort Vartab.table};                 (*default sorts*)

fun make_data (is_body, names, fixes, binds, type_occs, constraints) =
  Data {is_body = is_body, names = names, fixes = fixes, binds = binds,
    type_occs = type_occs, constraints = constraints};

structure Data = ProofDataFun
(
  val name = "Pure/variable";
  type T = data;
  fun init thy =
    make_data (false, Name.context, [], Vartab.empty, Symtab.empty, (Vartab.empty, Vartab.empty));
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;

fun map_data f =
  Data.map (fn Data {is_body, names, fixes, binds, type_occs, constraints} =>
    make_data (f (is_body, names, fixes, binds, type_occs, constraints)));

fun map_names f = map_data (fn (is_body, names, fixes, binds, type_occs, constraints) =>
  (is_body, f names, fixes, binds, type_occs, constraints));

fun map_fixes f = map_data (fn (is_body, names, fixes, binds, type_occs, constraints) =>
  (is_body, names, f fixes, binds, type_occs, constraints));

fun map_binds f = map_data (fn (is_body, names, fixes, binds, type_occs, constraints) =>
  (is_body, names, fixes, f binds, type_occs, constraints));

fun map_type_occs f = map_data (fn (is_body, names, fixes, binds, type_occs, constraints) =>
  (is_body, names, fixes, binds, f type_occs, constraints));

fun map_constraints f = map_data (fn (is_body, names, fixes, binds, type_occs, constraints) =>
  (is_body, names, fixes, binds, type_occs, f constraints));

fun rep_data ctxt = Data.get ctxt |> (fn Data args => args);

val is_body = #is_body o rep_data;
fun set_body b = map_data (fn (_, names, fixes, binds, type_occs, constraints) =>
  (b, names, fixes, binds, type_occs, constraints));
fun restore_body ctxt = set_body (is_body ctxt);

val names_of = #names o rep_data;
val fixes_of = #fixes o rep_data;
val binds_of = #binds o rep_data;
val type_occs_of = #type_occs o rep_data;
val constraints_of = #constraints o rep_data;

val is_declared = Name.is_declared o names_of;
fun is_fixed ctxt x = exists (fn (_, y) => x = y) (fixes_of ctxt);
fun newly_fixed inner outer x = is_fixed inner x andalso not (is_fixed outer x);



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

val declare_type_names = map_names o
  fold_types (fold_atyps (fn TFree (a, _) => Name.declare a | _ => I));

fun declare_names t =
  declare_type_names t #>
  map_names (fold_aterms (fn Free (x, _) => Name.declare x | _ => I) t);


(* type occurrences *)

val declare_type_occs = map_type_occs o fold_term_types
  (fn Free (x, _) => fold_atyps (fn TFree (a, _) => Symtab.insert_list (op =) (a, x) | _ => I)
    | _ => fold_atyps (fn TFree (a, _) => Symtab.default (a, []) | _ => I));


(* constraints *)

fun redeclare_skolems ctxt = ctxt |> map_constraints (apfst (fn types =>
  let
    fun decl (x, x') =
      (case default_type ctxt x' of
        SOME T => Vartab.update ((x, ~1), T)
      | NONE => I);
  in fold_rev decl (fixes_of ctxt) types end));

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
  #> declare_type_names t
  #> redeclare_skolems;


(* common declarations *)

fun declare_internal t =
  declare_names t #>
  declare_type_occs t;

fun declare_term t =
  declare_internal t #>
  declare_constraints t;

val declare_prf = Proofterm.fold_proof_terms declare_internal (declare_internal o Logic.mk_type);

val declare_thm = Drule.fold_terms declare_internal;
fun thm_context th = declare_thm th (Context.init_proof (Thm.theory_of_thm th));


(* renaming term/type frees *)

fun variant_frees ctxt ts frees =
  let
    val names = names_of (fold declare_names ts ctxt);
    val xs = fst (Name.variants (map #1 frees) names);
  in xs ~~ map snd frees end;



(** term bindings **)

fun hidden_polymorphism t T =
  let
    val tvarsT = Term.add_tvarsT T [];
    val extra_tvars = Term.fold_types (Term.fold_atyps
      (fn TVar v => if member (op =) tvarsT v then I else insert (op =) v | _ => I)) t [];
  in extra_tvars end;

fun add_bind (xi, NONE) = map_binds (Vartab.delete_safe xi)
  | add_bind ((x, i), SOME t) =
      let
        val T = Term.fastype_of t;
        val t' =
          if null (hidden_polymorphism t T) then t
          else Var ((x ^ "_has_extra_type_vars_on_rhs", i), T);
      in declare_term t' #> map_binds (Vartab.update ((x, i), (T, t'))) end;

val add_binds = fold add_bind;

fun expand_binds ctxt =
  let
    val binds = binds_of ctxt;
    fun expand (t as Var (xi, T)) =
          (case Vartab.lookup binds xi of
            SOME u => Envir.expand_atom T u
          | NONE => t)
      | expand t = t;
  in Envir.beta_norm o Term.map_aterms expand end;



(** fixes **)

local

fun no_dups [] = ()
  | no_dups dups = error ("Duplicate fixed variable(s): " ^ commas_quote dups);

fun new_fixes names' xs xs' =
  map_names (K names') #>
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
      else (no_dups (xs inter_string ys); no_dups (xs inter_string zs);
        (xs, fold Name.declare xs names));
  in ctxt |> new_fixes names' xs xs' end;

fun variant_fixes raw_xs ctxt =
  let
    val names = names_of ctxt;
    val xs = map Name.clean raw_xs;
    val (xs', names') = Name.variants xs names |>> map Name.skolem;
  in ctxt |> new_fixes names' xs xs' end;

end;


fun add_fixes_direct xs ctxt = ctxt
  |> set_body false
  |> (snd o add_fixes xs)
  |> restore_body ctxt;

fun fix_frees t ctxt = ctxt
  |> add_fixes_direct
      (rev (fold_aterms (fn Free (x, _) =>
        if is_fixed ctxt x then I else insert (op =) x | _ => I) t []))
  |> declare_term t;

fun invent_types Ss ctxt =
  let
    val tfrees = Name.invents (names_of ctxt) "'a" (length Ss) ~~ Ss;
    val ctxt' = fold (declare_constraints o Logic.mk_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;



(** export -- generalize type/term variables **)

fun export_inst inner outer =
  let
    val declared_outer = is_declared outer;
    val fixes_inner = fixes_of inner;
    val fixes_outer = fixes_of outer;

    val gen_fixes = map #2 (Library.take (length fixes_inner - length fixes_outer, fixes_inner));
    val still_fixed = not o member (op =) gen_fixes;
    val gen_fixesT =
      Symtab.fold (fn (a, xs) =>
        if declared_outer a orelse exists still_fixed xs
        then I else cons a) (type_occs_of inner) [];
  in (gen_fixesT, gen_fixes) end;

fun exportT_inst inner outer = #1 (export_inst inner outer);

fun exportT_terms inner outer ts =
  map (TermSubst.generalize (exportT_inst (fold declare_type_occs ts inner) outer, [])
    (fold (Term.fold_types Term.maxidx_typ) ts ~1 + 1)) ts;

fun export_terms inner outer ts =
  map (TermSubst.generalize (export_inst (fold declare_type_occs ts inner) outer)
    (fold Term.maxidx_term ts ~1 + 1)) ts;

fun export_prf inner outer prf =
  let
    val insts = export_inst (declare_prf prf inner) outer;
    val idx = Proofterm.maxidx_proof prf ~1 + 1;
    val gen_term = TermSubst.generalize_option insts idx;
    val gen_typ = TermSubst.generalizeT_option (#1 insts) idx;
  in Proofterm.map_proof_terms_option gen_term gen_typ prf end;

fun gen_export inst inner outer ths =
  let
    val inner' = fold (declare_type_occs o Thm.full_prop_of) ths inner;
  in map (Thm.generalize (inst inner' outer) (fold Thm.maxidx_thm ths ~1 + 1)) ths end;

val exportT = gen_export (rpair [] oo exportT_inst);
val export = gen_export export_inst;



(** import -- fix schematic type/term variables **)

fun importT_inst ts ctxt =
  let
    val tvars = rev (fold Term.add_tvars ts []);
    val (tfrees, ctxt') = invent_types (map #2 tvars) ctxt;
  in (tvars ~~ map TFree tfrees, ctxt') end;

fun import_inst is_open ts ctxt =
  let
    val ren = if is_open then I else Name.internal;
    val (instT, ctxt') = importT_inst ts ctxt;
    val vars = map (apsnd (TermSubst.instantiateT instT)) (rev (fold Term.add_vars ts []));
    val (xs, ctxt'') = variant_fixes (map (ren o #1 o #1) vars) ctxt';
    val inst = vars ~~ map Free (xs ~~ map #2 vars);
  in ((instT, inst), ctxt'') end;

fun importT_terms ts ctxt =
  let val (instT, ctxt') = importT_inst ts ctxt
  in (map (TermSubst.instantiate (instT, [])) ts, ctxt') end;

fun import_terms is_open ts ctxt =
  let val (inst, ctxt') = import_inst is_open ts ctxt
  in (map (TermSubst.instantiate inst) ts, ctxt') end;

fun importT ths ctxt =
  let
    val thy = Context.theory_of_proof ctxt;
    val certT = Thm.ctyp_of thy;
    val (instT, ctxt') = importT_inst (map Thm.full_prop_of ths) ctxt;
    val instT' = map (fn (v, T) => (certT (TVar v), certT T)) instT;
    val ths' = map (Thm.instantiate (instT', [])) ths;
  in ((map #2 instT', ths'), ctxt') end;

fun import_prf is_open prf ctxt =
  let
    val ts = rev (Proofterm.fold_proof_terms cons (cons o Logic.mk_type) prf []);
    val (insts, ctxt') = import_inst is_open ts ctxt;
  in (Proofterm.instantiate insts prf, ctxt') end;

fun import is_open ths ctxt =
  let
    val thy = Context.theory_of_proof ctxt;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val ((instT, inst), ctxt') = import_inst is_open (map Thm.full_prop_of ths) ctxt;
    val instT' = map (fn (v, T) => (certT (TVar v), certT T)) instT;
    val inst' = map (fn (v, t) => (cert (Var v), cert t)) inst;
    val ths' = map (Thm.instantiate (instT', inst')) ths;
  in (((map #2 instT', map #2 inst'), ths'), ctxt') end;


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
  in ((ps', goal'), ctxt') end;

fun focus_subgoal i st =
  let
    val all_vars = Drule.fold_terms Term.add_vars st [];
    val no_binds = map (fn (xi, _) => (xi, NONE)) all_vars;
  in
    add_binds no_binds #>
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

fun polymorphic ctxt ts =
  let
    val ctxt' = fold declare_term ts ctxt;
    val occs = type_occs_of ctxt;
    val occs' = type_occs_of ctxt';
    val types = Symtab.fold (fn (a, _) => if Symtab.defined occs a then I else cons a) occs' [];
    val idx = fold (Term.fold_types Term.maxidx_typ) ts ~1 + 1;
  in map (TermSubst.generalize (types, []) idx) ts end;

end;
