(*  Title:      HOL/Tools/record_package.ML
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Extensible records with structural subtyping in HOL.
*)

signature BASIC_RECORD_PACKAGE =
sig
  val record_simproc: simproc
  val record_split_tac: int -> tactic
  val record_split_name: string
  val record_split_wrapper: string * wrapper
end;

signature RECORD_PACKAGE =
sig
  include BASIC_RECORD_PACKAGE
  val quiet_mode: bool ref
  val updateN: string
  val mk_fieldT: (string * typ) * typ -> typ
  val dest_fieldT: typ -> (string * typ) * typ
  val mk_field: (string * term) * term -> term
  val mk_fst: term -> term
  val mk_snd: term -> term
  val mk_recordT: (string * typ) list * typ -> typ
  val dest_recordT: typ -> (string * typ) list * typ
  val mk_record: (string * term) list * term -> term
  val mk_sel: term -> string -> term
  val mk_update: term -> string * term -> term
  val print_records: theory -> unit
  val add_record: (string list * bstring) -> string option
    -> (bstring * string) list -> theory -> theory * {simps: thm list, iffs: thm list}
  val add_record_i: (string list * bstring) -> (typ list * string) option
    -> (bstring * typ) list -> theory -> theory * {simps: thm list, iffs: thm list}
  val setup: (theory -> theory) list
end;

structure RecordPackage: RECORD_PACKAGE =
struct


(*** theory context references ***)

val product_typeN = "Record.product_type";

val product_typeI = thm "product_typeI";
val product_type_inject = thm "product_type_inject";
val product_type_conv1 = thm "product_type_conv1";
val product_type_conv2 = thm "product_type_conv2";
val product_type_induct = thm "product_type_induct";
val product_type_cases = thm "product_type_cases";
val product_type_split_paired_all = thm "product_type_split_paired_all";



(*** utilities ***)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* fundamental syntax *)

fun prefix_base s = NameSpace.map_base (fn bname => s ^ bname);

val Trueprop = HOLogic.mk_Trueprop;
fun All xs t = Term.list_all_free (xs, t);

infix 9 $$;
infix 0 :== ===;
infixr 0 ==>;

val (op $$) = Term.list_comb;
val (op :==) = Logic.mk_defpair;
val (op ===) = Trueprop o HOLogic.mk_eq;
val (op ==>) = Logic.mk_implies;


(* proof tools *)

fun prove_goal sign goal tacs =
  Goals.prove_goalw_cterm [] (Thm.cterm_of sign goal) tacs
  handle ERROR => error ("The error(s) above occurred while trying to prove " ^
    quote (Sign.string_of_term sign goal));

fun prove_simp sign ss tacs simps =
  let
    val ss' = Simplifier.addsimps (ss, simps);
    fun prove goal = prove_goal sign goal
      (K (tacs @ [ALLGOALS (Simplifier.asm_full_simp_tac ss')]));
  in prove end;

fun try_param_tac x s rule i st =
  res_inst_tac [(x, (case Tactic.innermost_params i st of [] => s | (p, _) :: _ => p))] rule i st;



(*** syntax operations ***)

(** name components **)

val rN = "r";
val moreN = "more";
val schemeN = "_scheme";
val field_typeN = "_field_type";
val fieldN = "_field";
val fstN = "_val";
val sndN = "_more";
val updateN = "_update";
val makeN = "make";
val extendN = "extend";
val truncateN = "truncate";
val fieldsN = "fields";


(*see typedef_package.ML*)
val RepN = "Rep_";
val AbsN = "Abs_";



(** tuple operations **)

(* types *)

fun mk_fieldT ((c, T), U) = Type (suffix field_typeN c, [T, U]);

fun dest_fieldT (typ as Type (c_field_type, [T, U])) =
      (case try (unsuffix field_typeN) c_field_type of
        None => raise TYPE ("dest_fieldT", [typ], [])
      | Some c => ((c, T), U))
  | dest_fieldT typ = raise TYPE ("dest_fieldT", [typ], []);


(* morphisms *)

fun mk_Rep U (c, T) =
  Const (suffix field_typeN (prefix_base RepN c),
    mk_fieldT ((c, T), U) --> HOLogic.mk_prodT (T, U));

fun mk_Abs U (c, T) =
  Const (suffix field_typeN (prefix_base AbsN c),
    HOLogic.mk_prodT (T, U) --> mk_fieldT ((c, T), U));


(* constructors *)

fun mk_fieldC U (c, T) = (suffix fieldN c, T --> U --> mk_fieldT ((c, T), U));

fun mk_field ((c, t), u) =
  let val T = fastype_of t and U = fastype_of u
  in Const (suffix fieldN c, [T, U] ---> mk_fieldT ((c, T), U)) $ t $ u end;


(* destructors *)

fun mk_fstC U (c, T) = (suffix fstN c, mk_fieldT ((c, T), U) --> T);
fun mk_sndC U (c, T) = (suffix sndN c, mk_fieldT ((c, T), U) --> U);

fun dest_field fst_or_snd p =
  let
    val pT = fastype_of p;
    val ((c, T), U) = dest_fieldT pT;
    val (destN, destT) = if fst_or_snd then (fstN, T) else (sndN, U);
  in Const (suffix destN c, pT --> destT) $ p end;

val mk_fst = dest_field true;
val mk_snd = dest_field false;



(** record operations **)

(* types *)

val mk_recordT = foldr mk_fieldT;

fun dest_recordT T =
  (case try dest_fieldT T of
    None => ([], T)
  | Some (c_T, U) => apfst (cons c_T) (dest_recordT U));

fun find_fieldT c rT =
  (case assoc (fst (dest_recordT rT), c) of
    None => raise TYPE ("find_field: " ^ c, [rT], [])
  | Some T => T);


(* constructors *)

val mk_record = foldr mk_field;


(* selectors *)

fun mk_selC rT (c, T) = (c, rT --> T);

fun mk_sel r c =
  let val rT = fastype_of r
  in Const (mk_selC rT (c, find_fieldT c rT)) $ r end;

fun mk_named_sels names r = names ~~ map (mk_sel r) names;

val mk_moreC = mk_selC;

fun mk_more r c =
  let val rT = fastype_of r
  in Const (mk_moreC rT (c, snd (dest_recordT rT))) $ r end;


(* updates *)

fun mk_updateC rT (c, T) = (suffix updateN c, T --> rT --> rT);

fun mk_update r (c, x) =
  let val rT = fastype_of r
  in Const (mk_updateC rT (c, find_fieldT c rT)) $ x $ r end;

val mk_more_updateC = mk_updateC;

fun mk_more_update r (c, x) =
  let val rT = fastype_of r
  in Const (mk_more_updateC rT (c, snd (dest_recordT rT))) $ x $ r end;



(** concrete syntax for records **)

(* parse translations *)

fun gen_field_tr mark sfx (t as Const (c, _) $ Const (name, _) $ arg) =
      if c = mark then Syntax.const (suffix sfx name) $ arg
      else raise TERM ("gen_field_tr: " ^ mark, [t])
  | gen_field_tr mark _ t = raise TERM ("gen_field_tr: " ^ mark, [t]);

fun gen_fields_tr sep mark sfx (tm as Const (c, _) $ t $ u) =
      if c = sep then gen_field_tr mark sfx t :: gen_fields_tr sep mark sfx u
      else [gen_field_tr mark sfx tm]
  | gen_fields_tr _ mark sfx tm = [gen_field_tr mark sfx tm];

fun gen_record_tr sep mark sfx unit [t] = foldr (op $) (gen_fields_tr sep mark sfx t, unit)
  | gen_record_tr _ _ _ _ ts = raise TERM ("gen_record_tr", ts);

fun gen_record_scheme_tr sep mark sfx [t, more] = foldr (op $) (gen_fields_tr sep mark sfx t, more)
  | gen_record_scheme_tr _ _ _ ts = raise TERM ("gen_record_scheme_tr", ts);


val record_type_tr = gen_record_tr "_field_types" "_field_type" field_typeN (Syntax.const "unit");
val record_type_scheme_tr = gen_record_scheme_tr "_field_types" "_field_type" field_typeN;

val record_tr = gen_record_tr "_fields" "_field" fieldN HOLogic.unit;
val record_scheme_tr = gen_record_scheme_tr "_fields" "_field" fieldN;

fun record_update_tr [t, u] =
      foldr (op $) (rev (gen_fields_tr "_updates" "_update" updateN u), t)
  | record_update_tr ts = raise TERM ("record_update_tr", ts);


fun update_name_tr (Free (x, T) :: ts) = Free (suffix updateN x, T) $$ ts
  | update_name_tr (Const (x, T) :: ts) = Const (suffix updateN x, T) $$ ts
  | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
      (c $ update_name_tr [t] $ (Syntax.const "fun" $ ty $ Syntax.const "dummy")) $$ ts
  | update_name_tr ts = raise TERM ("update_name_tr", ts);


val parse_translation =
 [("_record_type", record_type_tr),
  ("_record_type_scheme", record_type_scheme_tr),
  ("_record", record_tr),
  ("_record_scheme", record_scheme_tr),
  ("_record_update", record_update_tr),
  ("_update_name", update_name_tr)];


(* print translations *)

fun gen_fields_tr' mark sfx (tm as Const (name_field, _) $ t $ u) =
      (case try (unsuffix sfx) name_field of
        Some name =>
          apfst (cons (Syntax.const mark $ Syntax.free name $ t)) (gen_fields_tr' mark sfx u)
      | None => ([], tm))
  | gen_fields_tr' _ _ tm = ([], tm);

fun gen_record_tr' sep mark sfx is_unit record record_scheme tm =
  let
    val (ts, u) = gen_fields_tr' mark sfx tm;
    val t' = foldr1 (fn (v, w) => Syntax.const sep $ v $ w) ts;
  in
    if is_unit u then Syntax.const record $ t'
    else Syntax.const record_scheme $ t' $ u
  end;


val record_type_tr' =
  gen_record_tr' "_field_types" "_field_type" field_typeN
    (fn Const ("unit", _) => true | _ => false) "_record_type" "_record_type_scheme";

val record_tr' =
  gen_record_tr' "_fields" "_field" fieldN
    (fn Const ("Unity", _) => true | _ => false) "_record" "_record_scheme";

fun record_update_tr' tm =
  let val (ts, u) = gen_fields_tr' "_update" updateN tm in
    Syntax.const "_record_update" $ u $
      foldr1 (fn (v, w) => Syntax.const "_updates" $ v $ w) (rev ts)
  end;


fun gen_field_tr' sfx tr' name =
  let val name_sfx = suffix sfx name
  in (name_sfx, fn [t, u] => tr' (Syntax.const name_sfx $ t $ u) | _ => raise Match) end;

fun print_translation names =
  map (gen_field_tr' field_typeN record_type_tr') names @
  map (gen_field_tr' fieldN record_tr') names @
  map (gen_field_tr' updateN record_update_tr') names;



(*** extend theory by record definition ***)

(** record info **)

(* type record_info and parent_info *)

type record_info =
 {args: (string * sort) list,
  parent: (typ list * string) option,
  fields: (string * typ) list,
  simps: thm list, induct: thm, cases: thm};

fun make_record_info args parent fields simps induct cases =
 {args = args, parent = parent, fields = fields, simps = simps,
  induct = induct, cases = cases}: record_info;

type parent_info =
 {name: string,
  fields: (string * typ) list,
  simps: thm list, induct: thm, cases: thm};

fun make_parent_info name fields simps induct cases =
 {name = name, fields = fields, simps = simps,
  induct = induct, cases = cases}: parent_info;



(* data kind 'HOL/records' *)

type record_data =
 {records: record_info Symtab.table,
  sel_upd:
   {selectors: unit Symtab.table,
    updates: string Symtab.table,
    simpset: Simplifier.simpset},
  field_splits:
   {fields: unit Symtab.table,
    simpset: Simplifier.simpset}};

fun make_record_data records sel_upd field_splits =
 {records = records, sel_upd = sel_upd, field_splits = field_splits}: record_data;

structure RecordsArgs =
struct
  val name = "HOL/records";
  type T = record_data;

  val empty =
    make_record_data Symtab.empty
      {selectors = Symtab.empty, updates = Symtab.empty, simpset = HOL_basic_ss}
      {fields = Symtab.empty, simpset = HOL_basic_ss};

  val copy = I;
  val prep_ext = I;
  fun merge
   ({records = recs1,
     sel_upd = {selectors = sels1, updates = upds1, simpset = ss1},
     field_splits = {fields = flds1, simpset = fld_ss1}},
    {records = recs2,
     sel_upd = {selectors = sels2, updates = upds2, simpset = ss2},
     field_splits = {fields = flds2, simpset = fld_ss2}}) =
    make_record_data
      (Symtab.merge (K true) (recs1, recs2))
      {selectors = Symtab.merge (K true) (sels1, sels2),
        updates = Symtab.merge (K true) (upds1, upds2),
        simpset = Simplifier.merge_ss (ss1, ss2)}
      {fields = Symtab.merge (K true) (flds1, flds2),
        simpset = Simplifier.merge_ss (fld_ss1, fld_ss2)};

  fun print sg ({records = recs, ...}: record_data) =
    let
      val prt_typ = Sign.pretty_typ sg;
      val ext_const = Sign.cond_extern sg Sign.constK;

      fun pretty_parent None = []
        | pretty_parent (Some (Ts, name)) =
            [Pretty.block [prt_typ (Type (name, Ts)), Pretty.str " +"]];

      fun pretty_field (c, T) = Pretty.block
        [Pretty.str (ext_const c), Pretty.str " ::", Pretty.brk 1, Pretty.quote (prt_typ T)];

      fun pretty_record (name, {args, parent, fields, simps = _, induct = _, cases = _}) =
        Pretty.block (Pretty.fbreaks (Pretty.block
          [prt_typ (Type (name, map TFree args)), Pretty.str " = "] ::
          pretty_parent parent @ map pretty_field fields));
    in
      map pretty_record (Sign.cond_extern_table sg Sign.typeK recs)
      |> Pretty.chunks |> Pretty.writeln
    end;
end;

structure RecordsData = TheoryDataFun(RecordsArgs);
val print_records = RecordsData.print;


(* access 'records' *)

fun get_record thy name = Symtab.lookup (#records (RecordsData.get thy), name);

fun put_record name info thy =
  let
    val {records, sel_upd, field_splits} = RecordsData.get thy;
    val data = make_record_data (Symtab.update ((name, info), records)) sel_upd field_splits;
  in RecordsData.put data thy end;


(* access 'sel_upd' *)

fun get_sel_upd sg = #sel_upd (RecordsData.get_sg sg);

fun get_selectors sg name = Symtab.lookup (#selectors (get_sel_upd sg), name);
fun get_updates sg name = Symtab.lookup (#updates (get_sel_upd sg), name);
fun get_simpset sg = #simpset (get_sel_upd sg);


fun put_sel_upd names simps thy =
  let
    val sels = map (rpair ()) names;
    val upds = map (suffix updateN) names ~~ names;

    val {records, sel_upd = {selectors, updates, simpset}, field_splits} = RecordsData.get thy;
    val data = make_record_data records
      {selectors = Symtab.extend (selectors, sels),
        updates = Symtab.extend (updates, upds),
        simpset = Simplifier.addsimps (simpset, simps)}
      field_splits;
  in RecordsData.put data thy end;


(* access 'field_splits' *)

fun add_record_splits splits thy =
  let
    val {records, sel_upd, field_splits = {fields, simpset}} = RecordsData.get thy;
    val flds = map (rpair () o fst) splits;
    val simps = map snd splits;
    val data = make_record_data records sel_upd
      {fields = Symtab.extend (fields, flds), simpset = Simplifier.addsimps (simpset, simps)};
  in RecordsData.put data thy end;


(* parent records *)

fun inst_record thy (types, name) =
  let
    val sign = Theory.sign_of thy;
    fun err msg = error (msg ^ " parent record " ^ quote name);

    val {args, parent, fields, simps, induct, cases} =
      (case get_record thy name of Some info => info | None => err "Unknown");
    val _ = if length types <> length args then err "Bad number of arguments for" else ();

    fun bad_inst ((x, S), T) =
      if Sign.of_sort sign (T, S) then None else Some x
    val bads = mapfilter bad_inst (args ~~ types);

    val inst = map fst args ~~ types;
    val subst = Term.map_type_tfree (fn (x, _) => the (assoc (inst, x)));
  in
    if not (null bads) then
      err ("Ill-sorted instantiation of " ^ commas bads ^ " in")
    else (apsome (apfst (map subst)) parent, map (apsnd subst) fields, simps, induct, cases)
  end;

fun add_parents thy (None, parents) = parents
  | add_parents thy (Some (types, name), parents) =
      let val (parent, fields, simps, induct, cases) = inst_record thy (types, name)
      in add_parents thy (parent, make_parent_info name fields simps induct cases :: parents) end;



(** record simproc **)

local

val sel_upd_pat = [Thm.read_cterm (Theory.sign_of HOL.thy) ("s (u k r)", HOLogic.termT)];

fun proc sg _ t =
  (case t of (sel as Const (s, _)) $ ((upd as Const (u, _)) $ k $ r) =>
    (case get_selectors sg s of Some () =>
      (case get_updates sg u of Some u_name =>
        let
          fun atomize x t = Free (x, fastype_of t);
          val k' = atomize "k" k;
          val r' = atomize "r" r;
          val t' = sel $ (upd $ k' $ r');
          val prove = mk_meta_eq o prove_simp sg (get_simpset sg) [] [];
        in
          if u_name = s then Some (prove (t' === k'))
          else Some (prove (t' === sel $ r'))
        end
      | None => None)
    | None => None)
  | _ => None);

in

val record_simproc = Simplifier.mk_simproc "record_simp" sel_upd_pat proc;

end;



(** record field splitting **)

(* tactic *)

fun record_split_tac i st =
  let
    val {field_splits = {fields, simpset}, ...} = RecordsData.get_sg (Thm.sign_of_thm st);

    fun is_fieldT (_, Type (a, [_, _])) = is_some (Symtab.lookup (fields, a))
      | is_fieldT _ = false;
    val params = Logic.strip_params (Library.nth_elem (i - 1, Thm.prems_of st));
  in
    if exists is_fieldT params then Simplifier.full_simp_tac simpset i st
    else Seq.empty
  end handle Library.LIST _ => Seq.empty;


(* wrapper *)

val record_split_name = "record_split_tac";
val record_split_wrapper = (record_split_name, fn tac => record_split_tac ORELSE' tac);


(* method *)

val record_split_method =
  ("record_split", Method.no_args (Method.SIMPLE_METHOD' HEADGOAL record_split_tac),
    "split record fields");


(** internal theory extenders **)

(* field_typedefs *)

fun field_typedefs zeta moreT names theory =
  let
    val alpha = "'a";
    val aT = TFree (alpha, HOLogic.termS);
    val UNIV = HOLogic.mk_UNIV (HOLogic.mk_prodT (aT, moreT));

    fun type_def (thy, name) =
      let val (thy', {type_definition, set_def = Some def, ...}) =
        thy |> setmp TypedefPackage.quiet_mode true
          (TypedefPackage.add_typedef_i true None
            (suffix field_typeN (Sign.base_name name), [alpha, zeta], Syntax.NoSyn) UNIV None
          (Tactic.rtac UNIV_witness 1))
      in (thy', Tactic.rewrite_rule [def] type_definition) end
  in foldl_map type_def (theory, names) end;


(* field_definitions *)

fun field_definitions fields names xs alphas zeta moreT more vars named_vars thy =
  let
    val sign = Theory.sign_of thy;
    val base = Sign.base_name;
    val full_path = Sign.full_name_path sign;

    val xT = TFree (variant alphas "'x", HOLogic.termS);


    (* prepare declarations and definitions *)

    (*field constructors*)
    val field_decls = map (mk_fieldC moreT) fields;

    fun mk_field_spec ((c, T), v) =
      Term.head_of (mk_field ((c, v), more)) :==
        lambda v (lambda more (mk_Abs moreT (c, T) $ (HOLogic.mk_prod (v, more))));
    val field_specs = map mk_field_spec (fields ~~ vars);

    (*field destructors*)
    val dest_decls = map (mk_fstC moreT) fields @ map (mk_sndC moreT) fields;

    fun mk_dest_spec dest sel (c, T) =
      let val p = Free ("p", mk_fieldT ((c, T), moreT));
      in Term.head_of (dest p) :== lambda p (sel (mk_Rep moreT (c, T) $ p)) end;
    val dest_specs1 = map (mk_dest_spec mk_fst HOLogic.mk_fst) fields;
    val dest_specs2 = map (mk_dest_spec mk_snd HOLogic.mk_snd) fields;


    (* 1st stage: defs_thy *)

    val (defs_thy, (((typedefs, field_defs), dest_defs1), dest_defs2)) =
      thy
      |> field_typedefs zeta moreT names
      |>> (Theory.add_consts_i o map (Syntax.no_syn o apfst base)) (field_decls @ dest_decls)
      |>>> (PureThy.add_defs_i false o map Thm.no_attributes) field_specs
      |>>> (PureThy.add_defs_i false o map Thm.no_attributes) dest_specs1
      |>>> (PureThy.add_defs_i false o map Thm.no_attributes) dest_specs2;

    val prod_types = map (fn (((a, b), c), d) => product_typeI OF [a, b, c, d])
      (typedefs ~~ field_defs ~~ dest_defs1 ~~ dest_defs2);


    (* 2nd stage: thms_thy *)

    fun make th = map (fn prod_type => Drule.standard (th OF [prod_type])) prod_types;

    val dest_convs = make product_type_conv1 @ make product_type_conv2;
    val field_injects = make product_type_inject;
    val field_inducts = make product_type_induct;
    val field_cases = make product_type_cases;
    val field_splits = make product_type_split_paired_all;

    val (thms_thy, [field_defs', dest_defs', dest_convs', field_injects',
        field_splits', field_inducts', field_cases']) = defs_thy
      |> (PureThy.add_thmss o map Thm.no_attributes)
       [("field_defs", field_defs),
        ("dest_defs", dest_defs1 @ dest_defs2),
        ("dest_convs", dest_convs),
        ("field_injects", field_injects),
        ("field_splits", field_splits),
        ("field_inducts", field_inducts),
        ("field_cases", field_cases)];

  in (thms_thy, dest_convs', field_injects', field_splits', field_inducts', field_cases') end;


(* record_definition *)

fun record_definition (args, bname) parent (parents: parent_info list) bfields thy =
  let
    val sign = Theory.sign_of thy;
    val full = Sign.full_name_path sign bname;
    val base = Sign.base_name;


    (* basic components *)

    val alphas = map fst args;
    val name = Sign.full_name sign bname;       (*not made part of record name space!*)

    val previous = if null parents then None else Some (last_elem parents);

    val parent_fields = flat (map #fields parents);
    val parent_names = map fst parent_fields;
    val parent_types = map snd parent_fields;
    val parent_len = length parent_fields;
    val parent_xs = variantlist (map (base o fst) parent_fields, [moreN, rN]);
    val parent_vars = ListPair.map Free (parent_xs, parent_types);
    val parent_named_vars = parent_names ~~ parent_vars;

    val fields = map (apfst full) bfields;
    val names = map fst fields;
    val types = map snd fields;
    val len = length fields;
    val xs = variantlist (map fst bfields, moreN :: rN :: parent_xs);
    val vars = ListPair.map Free (xs, types);
    val named_vars = names ~~ vars;

    val all_fields = parent_fields @ fields;
    val all_names = parent_names @ names;
    val all_types = parent_types @ types;
    val all_len = parent_len + len;
    val all_xs = parent_xs @ xs;
    val all_vars = parent_vars @ vars;
    val all_named_vars = parent_named_vars @ named_vars;

    val zeta = variant alphas "'z";
    val moreT = TFree (zeta, HOLogic.termS);
    val more = Free (moreN, moreT);
    val full_moreN = full moreN;
    fun more_part t = mk_more t full_moreN;
    fun more_part_update t x = mk_more_update t (full_moreN, x);
    val all_types_more = all_types @ [moreT];
    val all_xs_more = all_xs @ [moreN];

    val parent_more = funpow parent_len mk_snd;
    val idxs = 0 upto (len - 1);

    val parentT = if null parent_fields then [] else [mk_recordT (parent_fields, HOLogic.unitT)];
    val r_parent = if null parent_fields then [] else [Free (rN, hd parentT)];

    val rec_schemeT = mk_recordT (all_fields, moreT);
    val rec_scheme = mk_record (all_named_vars, more);
    val recT = mk_recordT (all_fields, HOLogic.unitT);
    val rec_ = mk_record (all_named_vars, HOLogic.unit);
    val r_scheme = Free (rN, rec_schemeT);
    val r = Free (rN, recT);


    (* prepare print translation functions *)

    val field_tr's =
      print_translation (distinct (flat (map NameSpace.accesses (full_moreN :: names))));


    (* prepare declarations *)

    val sel_decls = map (mk_selC rec_schemeT) bfields @
      [mk_moreC rec_schemeT (moreN, moreT)];
    val update_decls = map (mk_updateC rec_schemeT) bfields @
      [mk_more_updateC rec_schemeT (moreN, moreT)];
    val make_decl = (makeN, parentT ---> types ---> recT);
    val extend_decl = (extendN, recT --> moreT --> rec_schemeT);
    val truncate_decl = (truncateN, rec_schemeT --> recT);


    (* prepare definitions *)

    (*record (scheme) type abbreviation*)
    val recordT_specs =
      [(suffix schemeN bname, alphas @ [zeta], rec_schemeT, Syntax.NoSyn),
        (bname, alphas, recT, Syntax.NoSyn)];

    (*selectors*)
    fun mk_sel_spec (i, c) =
      mk_sel r_scheme c :== mk_fst (funpow i mk_snd (parent_more r_scheme));
    val sel_specs =
      ListPair.map mk_sel_spec (idxs, names) @
        [more_part r_scheme :== funpow len mk_snd (parent_more r_scheme)];

    (*updates*)
    val all_sels = mk_named_sels all_names r_scheme;
    fun mk_upd_spec (i, (c, x)) =
      mk_update r_scheme (c, x) :==
        mk_record (nth_update (c, x) (parent_len + i, all_sels), more_part r_scheme)
    val update_specs =
      ListPair.map mk_upd_spec (idxs, named_vars) @
        [more_part_update r_scheme more :== mk_record (all_sels, more)];

    (*derived operations*)
    val make_spec = Const (full makeN, parentT ---> types ---> recT) $$ r_parent $$ vars :==
      mk_record (flat (map (mk_named_sels parent_names) r_parent) @ named_vars, HOLogic.unit);
    val extend_spec = Const (full extendN, recT --> moreT --> rec_schemeT) $ r $ more :==
      mk_record (mk_named_sels all_names r, more);
    val truncate_spec = Const (full truncateN, rec_schemeT --> recT) $ r_scheme :==
      mk_record (all_sels, HOLogic.unit);


    (* prepare propositions *)

    (*selectors*)
    val sel_props =
      map (fn (c, x) => mk_sel rec_scheme c === x) named_vars @
        [more_part rec_scheme === more];

    (*updates*)
    fun mk_upd_prop (i, (c, T)) =
      let val x' = Free (variant all_xs (base c ^ "'"), T) in
        mk_update rec_scheme (c, x') ===
          mk_record (nth_update (c, x') (parent_len + i, all_named_vars), more)
      end;
    val update_props =
      ListPair.map mk_upd_prop (idxs, fields) @
        let val more' = Free (variant all_xs (moreN ^ "'"), moreT)
        in [more_part_update rec_scheme more' === mk_record (all_named_vars, more')] end;

    (*equality*)
    fun mk_sel_eq (t, T) =
      let val t' = Term.abstract_over (r_scheme, t)
      in Trueprop (HOLogic.eq_const T $ Term.incr_boundvars 1 t' $ t') end;
    val sel_eqs =
      map2 mk_sel_eq (map (mk_sel r_scheme) all_names @ [more_part r_scheme], all_types @ [moreT]);
    val equality_prop =
      Term.all rec_schemeT $ (Abs ("r", rec_schemeT,
        Term.all rec_schemeT $ (Abs ("r'", rec_schemeT,
          Logic.list_implies (sel_eqs,
            Trueprop (HOLogic.eq_const rec_schemeT $ Bound 1 $ Bound 0))))));

    (*induct*)
    val P = Free ("P", rec_schemeT --> HOLogic.boolT);
    val P' = Free ("P", recT --> HOLogic.boolT);
    val induct_scheme_prop =
      All (all_xs_more ~~ all_types_more) (Trueprop (P $ rec_scheme)) ==> Trueprop (P $ r_scheme);
    val induct_prop = All (all_xs ~~ all_types) (Trueprop (P' $ rec_)) ==> Trueprop (P' $ r);

    (*cases*)
    val C = Trueprop (Free (variant all_xs_more "C", HOLogic.boolT));
    val cases_scheme_prop =
      All (all_xs_more ~~ all_types_more) ((r_scheme === rec_scheme) ==> C) ==> C;
    val cases_prop = All (all_xs ~~ all_types) ((r === rec_) ==> C) ==> C;


    (* 1st stage: fields_thy *)

    val (fields_thy, field_simps, field_injects, field_splits, field_inducts, field_cases) =
      thy
      |> Theory.add_path bname
      |> field_definitions fields names xs alphas zeta moreT more vars named_vars;

    val named_splits = map2 (fn (c, th) => (suffix field_typeN c, th)) (names, field_splits);


    (* 2nd stage: defs_thy *)

    val (defs_thy, (((sel_defs, update_defs), derived_defs))) =
      fields_thy
      |> add_record_splits named_splits
      |> Theory.parent_path
      |> Theory.add_tyabbrs_i recordT_specs     (*not made part of record name space!*)
      |> Theory.add_path bname
      |> Theory.add_trfuns ([], [], field_tr's, [])
      |> (Theory.add_consts_i o map Syntax.no_syn)
        (sel_decls @ update_decls @ [make_decl, extend_decl, truncate_decl])
      |> (PureThy.add_defs_i false o map Thm.no_attributes) sel_specs
      |>>> (PureThy.add_defs_i false o map Thm.no_attributes) update_specs
      |>>> (PureThy.add_defs_i false o map Thm.no_attributes)
        [make_spec, extend_spec, truncate_spec];

    val defs_sg = Theory.sign_of defs_thy;


    (* 3rd stage: thms_thy *)

    val parent_simps = flat (map #simps parents);
    val prove = prove_simp defs_sg HOL_basic_ss [];
    val prove' = prove_simp defs_sg HOL_ss;

    val sel_convs = map (prove (parent_simps @ sel_defs @ field_simps)) sel_props;
    val update_convs = map (prove (parent_simps @ update_defs @ sel_convs)) update_props;
    val equality =
      prove' [ALLGOALS record_split_tac] (parent_simps @ sel_convs @ field_injects) equality_prop;

    val induct_scheme = prove_goal defs_sg induct_scheme_prop (fn prems =>
        (case previous of Some {induct, ...} => res_inst_tac [(rN, rN)] induct 1
        | None => all_tac) :: map (fn rule => try_param_tac "p" rN rule 1) field_inducts @
        [resolve_tac prems 1]);

    val induct = prove_goal defs_sg induct_prop (fn prems =>
        [res_inst_tac [(rN, rN)] induct_scheme 1,
         try_param_tac "x" "more" unit_induct 1, resolve_tac prems 1]);

    val cases_scheme = prove_goal defs_sg cases_scheme_prop (fn prems =>
        Method.insert_tac prems 1 ::
        (case previous of Some {cases, ...} => try_param_tac rN rN cases 1
        | None => all_tac) :: map (fn rule => try_param_tac "p" rN rule 1) field_cases @
        [Simplifier.asm_full_simp_tac HOL_basic_ss 1]);

    val cases = prove_goal defs_sg cases_prop (fn prems =>
        [Method.insert_tac prems 1, res_inst_tac [(rN, rN)] cases_scheme 1,
         Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps [unit_all_eq1]) 1]);

    val (thms_thy, ([sel_convs', update_convs', sel_defs', update_defs', _],
        [equality', induct_scheme', induct', cases_scheme', cases'])) =
      defs_thy
      |> (PureThy.add_thmss o map Thm.no_attributes)
       [("select_convs", sel_convs),
        ("update_convs", update_convs),
        ("select_defs", sel_defs),
        ("update_defs", update_defs),
        ("derived_defs", derived_defs)]
      |>>> PureThy.add_thms
       [(("equality", equality), [Classical.xtra_intro_global]),
        (("induct_scheme", induct_scheme), [RuleCases.case_names [fieldsN],
          InductAttrib.induct_type_global (suffix schemeN name)]),
        (("induct", induct), [RuleCases.case_names [fieldsN],
          InductAttrib.induct_type_global name]),
        (("cases_scheme", cases_scheme), [RuleCases.case_names [fieldsN],
          InductAttrib.cases_type_global (suffix schemeN name)]),
        (("cases", cases), [RuleCases.case_names [fieldsN],
          InductAttrib.cases_type_global name])];

    val simps = field_simps @ sel_convs' @ update_convs' @ [equality'];
    val iffs = field_injects;

    val thms_thy' =
      thms_thy |> (#1 oo PureThy.add_thmss)
        [(("simps", simps), [Simplifier.simp_add_global]),
         (("iffs", iffs), [iff_add_global])];


    (* 4th stage: final_thy *)

    val final_thy =
      thms_thy'
      |> put_record name (make_record_info args parent fields simps induct_scheme' cases_scheme')
      |> put_sel_upd (names @ [full_moreN]) (field_simps @ sel_defs' @ update_defs')
      |> Theory.parent_path;

  in (final_thy, {simps = simps, iffs = iffs}) end;



(** theory extender interface **)

(* prepare arguments *)

(*note: read_raw_typ avoids expanding type abbreviations*)
fun read_raw_parent sign s =
  (case Sign.read_raw_typ (sign, K None) s handle TYPE (msg, _, _) => error msg of
    Type (name, Ts) => (Ts, name)
  | _ => error ("Bad parent record specification: " ^ quote s));

fun read_typ sign (env, s) =
  let
    fun def_sort (x, ~1) = assoc (env, x)
      | def_sort _ = None;
    val T = Type.no_tvars (Sign.read_typ (sign, def_sort) s) handle TYPE (msg, _, _) => error msg;
  in (Term.add_typ_tfrees (T, env), T) end;

fun cert_typ sign (env, raw_T) =
  let val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle TYPE (msg, _, _) => error msg
  in (Term.add_typ_tfrees (T, env), T) end;


(* add_record *)

(*we do all preparations and error checks here, deferring the real
  work to record_definition*)

fun gen_add_record prep_typ prep_raw_parent (params, bname) raw_parent raw_fields thy =
  let
    val _ = Theory.requires thy "Record" "record definitions";
    val sign = Theory.sign_of thy;
    val _ = message ("Defining record " ^ quote bname ^ " ...");


    (* parents *)

    fun prep_inst T = snd (cert_typ sign ([], T));

    val parent = apsome (apfst (map prep_inst) o prep_raw_parent sign) raw_parent
      handle ERROR => error ("The error(s) above in parent record specification");
    val parents = add_parents thy (parent, []);

    val init_env =
      (case parent of
        None => []
      | Some (types, _) => foldr Term.add_typ_tfrees (types, []));


    (* fields *)

    fun prep_field (env, (c, raw_T)) =
      let val (env', T) = prep_typ sign (env, raw_T) handle ERROR =>
        error ("The error(s) above occured in field " ^ quote c)
      in (env', (c, T)) end;

    val (envir, bfields) = foldl_map prep_field (init_env, raw_fields);
    val envir_names = map fst envir;


    (* args *)

    val defaultS = Sign.defaultS sign;
    val args = map (fn x => (x, if_none (assoc (envir, x)) defaultS)) params;


    (* errors *)

    val name = Sign.full_name sign bname;
    val err_dup_record =
      if is_none (get_record thy name) then []
      else ["Duplicate definition of record " ^ quote name];

    val err_dup_parms =
      (case duplicates params of
        [] => []
      | dups => ["Duplicate parameter(s) " ^ commas dups]);

    val err_extra_frees =
      (case gen_rems (op =) (envir_names, params) of
        [] => []
      | extras => ["Extra free type variable(s) " ^ commas extras]);

    val err_no_fields = if null bfields then ["No fields present"] else [];

    val err_dup_fields =
      (case duplicates (map fst bfields) of
        [] => []
      | dups => ["Duplicate field(s) " ^ commas_quote dups]);

    val err_bad_fields =
      if forall (not_equal moreN o fst) bfields then []
      else ["Illegal field name " ^ quote moreN];

    val err_dup_sorts =
      (case duplicates envir_names of
        [] => []
      | dups => ["Inconsistent sort constraints for " ^ commas dups]);

    val errs =
      err_dup_record @ err_dup_parms @ err_extra_frees @ err_no_fields @
      err_dup_fields @ err_bad_fields @ err_dup_sorts;
  in
    if null errs then () else error (cat_lines errs);
    thy |> record_definition (args, bname) parent parents bfields
  end
  handle ERROR => error ("Failed to define record " ^ quote bname);

val add_record = gen_add_record read_typ read_raw_parent;
val add_record_i = gen_add_record cert_typ (K I);



(** package setup **)

(* setup theory *)

val setup =
 [RecordsData.init,
  Theory.add_trfuns ([], parse_translation, [], []),
  Method.add_methods [record_split_method],
  Simplifier.change_simpset_of Simplifier.addsimprocs [record_simproc]];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val record_decl =
  P.type_args -- P.name -- (P.$$$ "=" |-- Scan.option (P.typ --| P.$$$ "+")
    -- Scan.repeat1 (P.name -- (P.$$$ "::" |-- P.typ) --| P.marg_comment));

val recordP =
  OuterSyntax.command "record" "define extensible record" K.thy_decl
    (record_decl >> (fn (x, (y, z)) => Toplevel.theory (#1 o add_record x y z)));

val _ = OuterSyntax.add_parsers [recordP];

end;

end;

structure BasicRecordPackage: BASIC_RECORD_PACKAGE = RecordPackage;
open BasicRecordPackage;
