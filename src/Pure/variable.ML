(*  Title:      Pure/variable.ML
    ID:         $Id$
    Author:     Makarius

Fixed type/term variables and polymorphic term abbreviations.
*)

signature VARIABLE =
sig
  val is_body: Context.proof -> bool
  val set_body: bool -> Context.proof -> Context.proof
  val restore_body: Context.proof -> Context.proof -> Context.proof
  val fixes_of: Context.proof -> (string * string) list
  val fixed_names_of: Context.proof -> string list
  val binds_of: Context.proof -> (typ * term) Vartab.table
  val defaults_of: Context.proof ->
    typ Vartab.table * sort Vartab.table * string list * string list Symtab.table
  val used_types: Context.proof -> string list
  val is_declared: Context.proof -> string -> bool
  val is_fixed: Context.proof -> string -> bool
  val def_sort: Context.proof -> indexname -> sort option
  val def_type: Context.proof -> bool -> indexname -> typ option
  val default_type: Context.proof -> string -> typ option
  val declare_type: typ -> Context.proof -> Context.proof
  val declare_syntax: term -> Context.proof -> Context.proof
  val declare_term: term -> Context.proof -> Context.proof
  val declare_thm: thm -> Context.proof -> Context.proof
  val thm_context: thm -> Context.proof
  val rename_wrt: Context.proof -> term list -> (string * 'a) list -> (string * 'a) list
  val add_fixes: string list -> Context.proof -> string list * Context.proof
  val invent_fixes: string list -> Context.proof -> string list * Context.proof
  val invent_types: sort list -> Context.proof -> (string * sort) list * Context.proof
  val export_inst: Context.proof -> Context.proof -> string list * string list
  val exportT_inst: Context.proof -> Context.proof -> string list
  val export_terms: Context.proof -> Context.proof -> term list -> term list
  val exportT_terms: Context.proof -> Context.proof -> term list -> term list
  val exportT: Context.proof -> Context.proof -> thm list -> thm list
  val export: Context.proof -> Context.proof -> thm list -> thm list
  val importT_inst: term list -> Context.proof -> ((indexname * sort) * typ) list * Context.proof
  val import_inst: bool -> term list -> Context.proof ->
    (((indexname * sort) * typ) list * ((indexname * typ) * term) list) * Context.proof
  val importT_terms: term list -> Context.proof -> term list * Context.proof
  val import_terms: bool -> term list -> Context.proof -> term list * Context.proof
  val importT: thm list -> Context.proof -> thm list * Context.proof
  val import: bool -> thm list -> Context.proof -> thm list * Context.proof
  val tradeT: Context.proof -> (thm list -> thm list) -> thm list -> thm list
  val trade: Context.proof -> (thm list -> thm list) -> thm list -> thm list
  val warn_extra_tfrees: Context.proof -> Context.proof -> unit
  val monomorphic: Context.proof -> term list -> term list
  val polymorphic: Context.proof -> term list -> term list
  val hidden_polymorphism: term -> typ -> (indexname * sort) list
  val add_binds: (indexname * term option) list -> Context.proof -> Context.proof
  val expand_binds: Context.proof -> term -> term
end;

structure Variable: VARIABLE =
struct

(** local context data **)

datatype data = Data of
 {is_body: bool,                          (*inner body mode*)
  fixes: (string * string) list,          (*term fixes -- extern/intern*)
  binds: (typ * term) Vartab.table,       (*term bindings*)
  defaults:
    typ Vartab.table *                    (*type constraints*)
    sort Vartab.table *                   (*default sorts*)
    string list *                         (*used type variables*)
    string list Symtab.table};            (*occurrences of type variables in term variables*)

fun make_data (is_body, fixes, binds, defaults) =
  Data {is_body = is_body, fixes = fixes, binds = binds, defaults = defaults};

structure Data = ProofDataFun
(
  val name = "Pure/variable";
  type T = data;
  fun init thy =
    make_data (false, [], Vartab.empty, (Vartab.empty, Vartab.empty, [], Symtab.empty));
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;

fun map_data f =
  Data.map (fn Data {is_body, fixes, binds, defaults} =>
    make_data (f (is_body, fixes, binds, defaults)));

fun map_fixes f = map_data (fn (is_body, fixes, binds, defaults) =>
  (is_body, f fixes, binds, defaults));

fun map_binds f = map_data (fn (is_body, fixes, binds, defaults) =>
  (is_body, fixes, f binds, defaults));

fun map_defaults f = map_data (fn (is_body, fixes, binds, defaults) =>
  (is_body, fixes, binds, f defaults));

fun rep_data ctxt = Data.get ctxt |> (fn Data args => args);

val is_body = #is_body o rep_data;
fun set_body b = map_data (fn (_, fixes, binds, defaults) => (b, fixes, binds, defaults));
fun restore_body ctxt = set_body (is_body ctxt);

val fixes_of = #fixes o rep_data;
val fixed_names_of = map #2 o fixes_of;

val binds_of = #binds o rep_data;

val defaults_of = #defaults o rep_data;
val used_types = #3 o defaults_of;
val type_occs_of = #4 o defaults_of;

fun is_declared ctxt x = Vartab.defined (#1 (defaults_of ctxt)) (x, ~1);
fun is_fixed ctxt x = exists (fn (_, y) => x = y) (fixes_of ctxt);



(** declarations **)

(* default sorts and types *)

val def_sort = Vartab.lookup o #2 o defaults_of;

fun def_type ctxt pattern xi =
  let val {binds, defaults = (types, _, _, _), ...} = rep_data ctxt in
    (case Vartab.lookup types xi of
      NONE =>
        if pattern then NONE
        else Vartab.lookup binds xi |> Option.map (TypeInfer.polymorphicT o #1)
    | some => some)
  end;

fun default_type ctxt x = Vartab.lookup (#1 (defaults_of ctxt)) (x, ~1);


(* declare types/terms *)

local

val ins_types = fold_aterms
  (fn Free (x, T) => Vartab.update ((x, ~1), T)
    | Var v => Vartab.update v
    | _ => I);

val ins_sorts = fold_atyps
  (fn TFree (x, S) => Vartab.update ((x, ~1), S)
    | TVar v => Vartab.update v
    | _ => I);

val ins_used = fold_atyps
  (fn TFree (x, _) => insert (op =) x | _ => I);

val ins_occs = fold_term_types (fn t =>
  let val x = case t of Free (x, _) => x | _ => ""
  in fold_atyps (fn TFree (a, _) => Symtab.insert_list (op =) (a, x) | _ => I) end);

fun ins_skolem def_ty = fold_rev (fn (x, x') =>
  (case def_ty x' of
    SOME T => Vartab.update ((x, ~1), T)
  | NONE => I));

in

fun declare_type T = map_defaults (fn (types, sorts, used, occ) =>
 (types,
  ins_sorts T sorts,
  ins_used T used,
  occ));

fun declare_syntax t = map_defaults (fn (types, sorts, used, occ) =>
 (ins_types t types,
  fold_types ins_sorts t sorts,
  fold_types ins_used t used,
  occ));

fun declare_occs t = map_defaults (fn (types, sorts, used, occ) =>
  (types, sorts, used, ins_occs t occ));

fun declare_term t ctxt =
  ctxt
  |> declare_syntax t
  |> map_defaults (fn (types, sorts, used, occ) =>
     (ins_skolem (fn x => Vartab.lookup types (x, ~1)) (fixes_of ctxt) types,
      sorts,
      used,
      ins_occs t occ));

fun declare_thm th = fold declare_term (Thm.full_prop_of th :: Thm.hyps_of th);
fun thm_context th = Context.init_proof (Thm.theory_of_thm th) |> declare_thm th;

end;


(* renaming term/type frees *)

fun rename_wrt ctxt ts frees =
  let
    val (types, sorts, _, _) = defaults_of (ctxt |> fold declare_syntax ts);
    fun ren (x, X) xs =
      let
        fun used y = y = "" orelse y = "'" orelse member (op =) xs y orelse
          Vartab.defined types (y, ~1) orelse Vartab.defined sorts (y, ~1);
        val x' = Term.variant_name used x;
      in ((x', X), x' :: xs) end;
  in #1 (fold_map ren frees []) end;



(** fixes **)

fun no_dups [] = ()
  | no_dups dups = error ("Duplicate fixed variable(s): " ^ commas_quote dups);

fun add_fixes xs ctxt =
  let
    val (ys, zs) = split_list (fixes_of ctxt);
    val _ = no_dups (duplicates (op =) xs);
    val _ =
      (case filter (can Term.dest_skolem) xs of [] => ()
      | bads => error ("Illegal internal Skolem constant(s): " ^ commas_quote bads));
    val xs' =
      if is_body ctxt then Term.variantlist (map Term.skolem xs, zs)
      else (no_dups (xs inter_string ys); no_dups (xs inter_string zs); xs);
  in
    ctxt
    |> map_fixes (fn fixes => rev (xs ~~ xs') @ fixes)
    |> fold (declare_syntax o Syntax.free) xs'
    |> pair xs'
  end;

fun invent_fixes xs ctxt =
  ctxt
  |> set_body true
  |> add_fixes (Term.variantlist (xs, []))
  ||> restore_body ctxt;

fun invent_types Ss ctxt =
  let
    val tfrees = Term.invent_names (used_types ctxt) "'a" (length Ss) ~~ Ss;
    val ctxt' = fold (declare_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;



(** export -- generalize type/term variables **)

fun export_inst inner outer =
  let
    val types_outer = used_types outer;
    val fixes_inner = fixes_of inner;
    val fixes_outer = fixes_of outer;

    val gen_fixes = map #2 (Library.take (length fixes_inner - length fixes_outer, fixes_inner));
    val still_fixed = not o member (op =) ("" :: gen_fixes);
    val gen_fixesT =
      Symtab.fold (fn (a, xs) =>
        if member (op =) types_outer a orelse exists still_fixed xs
        then I else cons a) (type_occs_of inner) [];
  in (gen_fixesT, gen_fixes) end;

fun exportT_inst inner outer = #1 (export_inst inner outer);

fun exportT_terms inner outer ts =
  map (Term.generalize (exportT_inst (fold declare_occs ts inner) outer, [])
    (fold (Term.fold_types Term.maxidx_typ) ts ~1 + 1)) ts;

fun export_terms inner outer ts =
  map (Term.generalize (export_inst (fold declare_occs ts inner) outer)
    (fold Term.maxidx_term ts ~1 + 1)) ts;

fun gen_export inst inner outer ths =
  let
    val ths' = map Thm.adjust_maxidx_thm ths;
    val maxidx = fold Thm.maxidx_thm ths' ~1;
    val inner' = fold (declare_occs o Thm.full_prop_of) ths' inner;
  in map (Thm.generalize (inst inner' outer) (maxidx + 1)) ths' end;

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
    val (instT, ctxt') = importT_inst ts ctxt;
    val vars = map (apsnd (Term.instantiateT instT)) (rev (fold Term.add_vars ts []));
    val ren = if is_open then I else Term.internal;
    val (xs, ctxt'') = invent_fixes (map (ren o #1 o #1) vars) ctxt';
    val inst = vars ~~ map Free (xs ~~ map #2 vars);
  in ((instT, inst), ctxt'') end;

fun importT_terms ts ctxt =
  let val (instT, ctxt') = importT_inst ts ctxt
  in (map (Term.instantiate (instT, [])) ts, ctxt') end;

fun import_terms is_open ts ctxt =
  let val (inst, ctxt') = import_inst is_open ts ctxt
  in (map (Term.instantiate inst) ts, ctxt') end;

fun importT ths ctxt =
  let
    val thy = Context.theory_of_proof ctxt;
    val certT = Thm.ctyp_of thy;
    val (instT, ctxt') = importT_inst (map Thm.full_prop_of ths) ctxt;
    val instT' = map (fn (v, T) => (certT (TVar v), certT T)) instT;
    val ths' = map (Thm.instantiate (instT', [])) ths;
  in (ths', ctxt') end;

fun import is_open ths ctxt =
  let
    val thy = Context.theory_of_proof ctxt;
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val ((instT, inst), ctxt') = import_inst is_open (map Thm.full_prop_of ths) ctxt;
    val instT' = map (fn (v, T) => (certT (TVar v), certT T)) instT;
    val inst' = map (fn (v, t) => (cert (Var v), cert t)) inst;
    val ths' = map (Thm.instantiate (instT', inst')) ths;
  in (ths', ctxt') end;


(* import/export *)

fun gen_trade imp exp ctxt f ths =
  let val (ths', ctxt') = imp ths ctxt
  in exp ctxt' ctxt (f ths') end;

val tradeT = gen_trade importT exportT;
val trade = gen_trade (import true) export;



(** implicit polymorphism **)

(* warn_extra_tfrees *)

fun warn_extra_tfrees ctxt1 ctxt2 =
  let
    fun occs_typ a = Term.exists_subtype (fn TFree (b, _) => a = b | _ => false);
    fun occs_free _ "" = I
      | occs_free a x =
          (case def_type ctxt1 false (x, ~1) of
            SOME T => if occs_typ a T then I else cons (a, x)
          | NONE => cons (a, x));

    val occs1 = type_occs_of ctxt1 and occs2 = type_occs_of ctxt2;
    val extras = Symtab.fold (fn (a, xs) =>
      if Symtab.defined occs1 a then I else fold (occs_free a) xs) occs2 [];
    val tfrees = map #1 extras |> sort_distinct string_ord;
    val frees = map #2 extras |> sort_distinct string_ord;
  in
    if null extras then ()
    else warning ("Introduced fixed type variable(s): " ^ commas tfrees ^ " in " ^
      space_implode " or " (map quote frees))
  end;


(* monomorphic vs. polymorphic terms *)

fun monomorphic ctxt ts =
  #1 (importT_terms ts (fold declare_term ts ctxt));

fun polymorphic ctxt ts =
  exportT_terms (fold declare_term ts ctxt) ctxt ts;


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

end;
