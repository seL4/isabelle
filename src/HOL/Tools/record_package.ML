(*  Title:      HOL/Tools/record_package.ML
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Extensible records with structural subtyping in HOL.
*)

signature BASIC_RECORD_PACKAGE =
sig
  val record_split_tac: int -> tactic
  val record_split_name: string
  val record_split_wrapper: string * wrapper
end;

signature RECORD_PACKAGE =
sig
  include BASIC_RECORD_PACKAGE
  val quiet_mode: bool ref
  val moreS: sort
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
    -> (bstring * string) list -> theory -> theory
  val add_record_i: (string list * bstring) -> (typ list * string) option
    -> (bstring * typ) list -> theory -> theory
  val setup: (theory -> theory) list
end;

structure RecordPackage: RECORD_PACKAGE =
struct


(*** utilities ***)

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;


(* attributes etc. *)        (* FIXME move to Provers *)

fun add_iffs_global (thy, th) =
  let
    val ss = Simplifier.simpset_ref_of thy;
    val cs = Classical.claset_ref_of thy;
    val (cs', ss') = (! cs, ! ss) addIffs [th];
  in ss := ss'; cs := cs'; (thy, th) end;

fun add_wrapper wrapper thy =
  let val r = Classical.claset_ref_of thy
  in r := ! r addSWrapper wrapper; thy end;


(* definitions and equations *)

infix 0 :== ===;

val (op :==) = Logic.mk_defpair;
val (op ===) = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun get_defs thy specs = map (PureThy.get_thm thy o fst) specs;


(* proof by simplification *)

fun prove_simp thy tacs simps =
  let
    val sign = Theory.sign_of thy;
    val ss = Simplifier.addsimps (HOL_basic_ss, simps);

    fun prove goal =
      Goals.prove_goalw_cterm [] (Thm.cterm_of sign goal)
        (K (tacs @ [ALLGOALS (Simplifier.simp_tac ss)]))
      handle ERROR => error ("The error(s) above occurred while trying to prove "
        ^ quote (Sign.string_of_term sign goal));
  in prove end;



(*** syntax operations ***)

(** name components **)

val moreN = "more";
val schemeN = "_scheme";
val fieldN = "_field";
val raw_fieldN = "_raw_field";
val field_typeN = "_field_type";
val fstN = "_val";
val sndN = "_more";
val updateN = "_update";
val makeN = "make";
val make_schemeN = "make_scheme";

(*see datatype package*)
val caseN = "_case";



(** generic operations **)

(* adhoc priming of vars *)

fun prime (Free (x, T)) = Free (x ^ "'", T)
  | prime t = raise TERM ("prime: no free variable", [t]);


(* product case *)

fun fst_fn T U = Abs ("x", T, Abs ("y", U, Bound 1));
fun snd_fn T U = Abs ("x", T, Abs ("y", U, Bound 0));

fun mk_prod_case name f p =
  let
    val fT as Type ("fun", [A, Type ("fun", [B, C])]) = fastype_of f;
    val pT = fastype_of p;
  in Const (suffix caseN name, fT --> pT --> C) $ f $ p end;



(** tuple operations **)

(* more type class *)

val moreS = ["Record.more"];


(* types *)

fun mk_fieldT ((c, T), U) = Type (suffix field_typeN c, [T, U]);

fun dest_fieldT (typ as Type (c_field_type, [T, U])) =
      (case try (unsuffix field_typeN) c_field_type of
        None => raise TYPE ("dest_fieldT", [typ], [])
      | Some c => ((c, T), U))
  | dest_fieldT typ = raise TYPE ("dest_fieldT", [typ], []);


(* constructors *)

fun mk_fieldC U (c, T) = (suffix fieldN c, T --> U --> mk_fieldT ((c, T), U));

fun gen_mk_field sfx ((c, t), u) =
  let val T = fastype_of t and U = fastype_of u
  in Const (suffix sfx c, [T, U] ---> mk_fieldT ((c, T), U)) $ t $ u end;

val mk_field = gen_mk_field fieldN;
val mk_raw_field = gen_mk_field raw_fieldN;


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


(* make *)

fun mk_makeC rT (c, Ts) = (c, Ts ---> rT);



(** concrete syntax for records **)

(* parse translations *)

fun gen_field_tr mark sfx (t as Const (c, _) $ Free (name, _) $ arg) =
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


val parse_translation =
 [("_record_type", record_type_tr),
  ("_record_type_scheme", record_type_scheme_tr),
  ("_record", record_tr),
  ("_record_scheme", record_scheme_tr),
  ("_record_update", record_update_tr)];


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
  gen_record_tr' "_fields" "_field" fieldN HOLogic.is_unit "_record" "_record_scheme";

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
  simps: thm list};

type parent_info =
 {name: string,
  fields: (string * typ) list,
  simps: thm list};


(* data kind 'HOL/records' *)

structure RecordsArgs =
struct
  val name = "HOL/records";
  type T =
    record_info Symtab.table *                          (*records*)
      (thm Symtab.table * Simplifier.simpset);          (*field split rules*)

  val empty = (Symtab.empty, (Symtab.empty, HOL_basic_ss));
  val prep_ext = I;
  fun merge ((recs1, (sps1, ss1)), (recs2, (sps2, ss2))) =
    (Symtab.merge (K true) (recs1, recs2),
      (Symtab.merge (K true) (sps1, sps2), Simplifier.merge_ss (ss1, ss2)));

  fun print sg (recs, _) =
    let
      val prt_typ = Sign.pretty_typ sg;
      val ext_const = Sign.cond_extern sg Sign.constK;

      fun pretty_parent None = []
        | pretty_parent (Some (Ts, name)) =
            [Pretty.block [prt_typ (Type (name, Ts)), Pretty.str " +"]];

      fun pretty_field (c, T) = Pretty.block
        [Pretty.str (ext_const c), Pretty.str " ::", Pretty.brk 1, Pretty.quote (prt_typ T)];

      fun pretty_record (name, {args, parent, fields, simps = _}) = Pretty.block (Pretty.fbreaks
        (Pretty.block [prt_typ (Type (name, map TFree args)), Pretty.str " = "] ::
          pretty_parent parent @ map pretty_field fields));
    in
      seq (Pretty.writeln o pretty_record) (Symtab.dest recs)
    end;
end;

structure RecordsData = TheoryDataFun(RecordsArgs);
val print_records = RecordsData.print;


(* get and put data *)

fun get_record thy name = Symtab.lookup (#1 (RecordsData.get thy), name);

fun put_record name info thy =
  let val (tab, sp) = RecordsData.get thy
  in RecordsData.put (Symtab.update ((name, info), tab), sp) thy end;

fun add_record_splits splits thy =
  let
    val (tab, (sps, ss)) = RecordsData.get thy;
    val simps = map #2 splits;
  in RecordsData.put (tab, (Symtab.extend (sps, splits), Simplifier.addsimps (ss, simps))) thy end;


(* parent records *)

fun inst_record thy (types, name) =
  let
    val sign = Theory.sign_of thy;
    fun err msg = error (msg ^ " parent record " ^ quote name);

    val {args, parent, fields, simps} =
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
    else (apsome (apfst (map subst)) parent, map (apsnd subst) fields, simps)
  end;

fun add_parents thy (None, parents) = parents
  | add_parents thy (Some (types, name), parents) =
      let val (pparent, pfields, psimps) = inst_record thy (types, name)
      in add_parents thy (pparent, {name = name, fields = pfields, simps = psimps} :: parents) end;



(** record field splitting **)

(* tactic *)

fun record_split_tac i st =
  let
    val (_, (sps, ss)) = RecordsData.get_sg (Thm.sign_of_thm st);

    fun is_fieldT (_, Type (a, [_, _])) = is_some (Symtab.lookup (sps, a))
      | is_fieldT _ = false;
    val params = Logic.strip_params (Library.nth_elem (i - 1, Thm.prems_of st));
  in
    if exists is_fieldT params then Simplifier.full_simp_tac ss i st
    else Seq.empty
  end handle Library.LIST _ => Seq.empty;


(* wrapper *)

val record_split_name = "record_split_tac";
val record_split_wrapper = (record_split_name, fn tac => record_split_tac ORELSE' tac);


(* method *)

val record_split_method =
  ("record_split", Method.no_args (Method.METHOD0 (FIRSTGOAL record_split_tac)),
    "split record fields");



(** internal theory extenders **)

(* field_type_defs *)

fun field_type_def ((thy, simps), (name, tname, vs, T, U)) =
  let
    val full = Sign.full_name (sign_of thy);
    val (thy', {simps = simps', ...}) =
      thy
      |> setmp DatatypePackage.quiet_mode true
        (DatatypePackage.add_datatype_i true [tname]
          [(vs, tname, Syntax.NoSyn, [(name, [T, U], Syntax.NoSyn)])]);
    val thy'' =
      thy'
      |> setmp AxClass.quiet_mode true
        (AxClass.add_inst_arity_i (full tname, [HOLogic.termS, moreS], moreS) [] [] None);
  in (thy'', simps' @ simps) end;

fun field_type_defs args thy = foldl field_type_def ((thy, []), args);


(* field_definitions *)

fun field_definitions fields names zeta moreT more vars named_vars thy =
  let
    val sign = Theory.sign_of thy;
    val base = Sign.base_name;
    val full_path = Sign.full_name_path sign;


    (* prepare declarations and definitions *)

    (*field types*)
    fun mk_fieldT_spec c =
      (suffix raw_fieldN c, suffix field_typeN c,
        ["'a", zeta], TFree ("'a", HOLogic.termS), moreT);
    val fieldT_specs = map (mk_fieldT_spec o base) names;

    (*field constructors*)
    val field_decls = map (mk_fieldC moreT) fields;

    fun mk_field_spec (c, v) =
      mk_field ((c, v), more) :== mk_raw_field ((c, v), more);
    val field_specs = map mk_field_spec named_vars;

    (*field destructors*)
    val dest_decls = map (mk_fstC moreT) fields @ map (mk_sndC moreT) fields;

    fun mk_dest_spec dest f (c, T) =
      let val p = Free ("p", mk_fieldT ((c, T), moreT));
      in dest p :== mk_prod_case (suffix field_typeN c) (f T moreT) p end;
    val dest_specs =
      map (mk_dest_spec mk_fst fst_fn) fields @
      map (mk_dest_spec mk_snd snd_fn) fields;


    (* prepare theorems *)

    (*constructor injects*)
    fun mk_inject_prop (c, v) =
      HOLogic.mk_eq (mk_field ((c, v), more), mk_field ((c, prime v), prime more)) ===
        (HOLogic.conj $ HOLogic.mk_eq (v, prime v) $ HOLogic.mk_eq (more, prime more));
    val inject_props = map mk_inject_prop named_vars;

    (*destructor conversions*)
    fun mk_dest_prop dest dest' (c, v) =
      dest (mk_field ((c, v), more)) === dest' (v, more);
    val dest_props =
      map (mk_dest_prop mk_fst fst) named_vars @
      map (mk_dest_prop mk_snd snd) named_vars;

    (*surjective pairing*)
    fun mk_surj_prop (c, T) =
      let val p = Free ("p", mk_fieldT ((c, T), moreT));
      in p === mk_field ((c, mk_fst p), mk_snd p) end;
    val surj_props = map mk_surj_prop fields;


    (* 1st stage: types_thy *)

    val (types_thy, datatype_simps) =
      thy
      |> field_type_defs fieldT_specs;


    (* 2nd stage: defs_thy *)

    val defs_thy =
      types_thy
       |> (Theory.add_consts_i o map (Syntax.no_syn o apfst base))
         (field_decls @ dest_decls)
       |> (PureThy.add_defs_i o map (fn x => (x, [Drule.tag_internal])))
         (field_specs @ dest_specs);

    val field_defs = get_defs defs_thy field_specs;
    val dest_defs = get_defs defs_thy dest_specs;


    (* 3rd stage: thms_thy *)

    val prove = prove_simp defs_thy;
    val prove_std = prove [] (field_defs @ dest_defs @ datatype_simps);

    val field_injects = map prove_std inject_props;
    val dest_convs = map prove_std dest_props;
    val surj_pairs = map (prove [DatatypePackage.induct_tac "p" 1]
      (map Thm.symmetric field_defs @ dest_convs)) surj_props;

    fun mk_split th = SplitPairedAll.rule (th RS eq_reflection);
    val field_splits = map mk_split surj_pairs;

    val thms_thy =
      defs_thy
      |> (PureThy.add_thmss o map Thm.no_attributes)
        [("field_defs", field_defs),
          ("dest_defs", dest_defs),
          ("dest_convs", dest_convs),
          ("surj_pairs", surj_pairs),
          ("field_splits", field_splits)];

  in (thms_thy, dest_convs, field_injects, field_splits) end;


(* record_definition *)

fun record_definition (args, bname) parent (parents: parent_info list) bfields thy =
  let
    val sign = Theory.sign_of thy;
    val full = Sign.full_name_path sign bname;
    val base = Sign.base_name;


    (* basic components *)

    val alphas = map fst args;
    val name = Sign.full_name sign bname;       (*not made part of record name space!*)

    val parent_fields = flat (map #fields parents);
    val parent_names = map fst parent_fields;
    val parent_types = map snd parent_fields;
    val parent_len = length parent_fields;
    val parent_xs = variantlist (map (base o fst) parent_fields, [moreN]);
    val parent_vars = ListPair.map Free (parent_xs, parent_types);
    val parent_named_vars = parent_names ~~ parent_vars;

    val fields = map (apfst full) bfields;
    val names = map fst fields;
    val types = map snd fields;
    val len = length fields;
    val xs = variantlist (map fst bfields, moreN :: parent_xs);
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
    val moreT = TFree (zeta, moreS);
    val more = Free (moreN, moreT);
    val full_moreN = full moreN;
    fun more_part t = mk_more t full_moreN;
    fun more_part_update t x = mk_more_update t (full_moreN, x);

    val parent_more = funpow parent_len mk_snd;
    val idxs = 0 upto (len - 1);

    val rec_schemeT = mk_recordT (all_fields, moreT);
    val rec_scheme = mk_record (all_named_vars, more);
    val r = Free ("r", rec_schemeT);
    val recT = mk_recordT (all_fields, HOLogic.unitT);


    (* prepare print translation functions *)

    val field_tr's =
      print_translation (distinct (flat (map NameSpace.accesses (full_moreN :: names))));


    (* prepare declarations *)

    val sel_decls = map (mk_selC rec_schemeT) bfields @
      [mk_moreC rec_schemeT (moreN, moreT)];
    val update_decls = map (mk_updateC rec_schemeT) bfields @
      [mk_more_updateC rec_schemeT (moreN, moreT)];
    val make_decls =
      [(mk_makeC rec_schemeT (make_schemeN, all_types @ [moreT])),
       (mk_makeC recT (makeN, all_types))];


    (* prepare definitions *)

    (*record (scheme) type abbreviation*)
    val recordT_specs =
      [(suffix schemeN bname, alphas @ [zeta], rec_schemeT, Syntax.NoSyn),
        (bname, alphas, recT, Syntax.NoSyn)];

    (*selectors*)
    fun mk_sel_spec (i, c) =
      mk_sel r c :== mk_fst (funpow i mk_snd (parent_more r));
    val sel_specs =
      ListPair.map mk_sel_spec (idxs, names) @
        [more_part r :== funpow len mk_snd (parent_more r)];

    (*updates*)
    val all_sels = all_names ~~ map (mk_sel r) all_names;
    fun mk_upd_spec (i, (c, x)) =
      mk_update r (c, x) :==
        mk_record (nth_update (c, x) (parent_len + i, all_sels), more_part r)
    val update_specs =
      ListPair.map mk_upd_spec (idxs, named_vars) @
        [more_part_update r more :== mk_record (all_sels, more)];

    (*makes*)
    val make_scheme = Const (mk_makeC rec_schemeT (full make_schemeN, all_types @ [moreT]));
    val make = Const (mk_makeC recT (full makeN, all_types));
    val make_specs =
      [list_comb (make_scheme, all_vars) $ more :== rec_scheme,
        list_comb (make, all_vars) :== mk_record (all_named_vars, HOLogic.unit)];


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


    (* 1st stage: fields_thy *)

    val (fields_thy, field_simps, field_injects, field_splits) =
      thy
      |> Theory.add_path bname
      |> field_definitions fields names zeta moreT more vars named_vars;

    val named_splits = map2 (fn (c, th) => (suffix field_typeN c, th)) (names, field_splits);


    (* 2nd stage: defs_thy *)

    val defs_thy =
      fields_thy
      |> Theory.parent_path
      |> Theory.add_tyabbrs_i recordT_specs     (*not made part of record name space!*)
      |> Theory.add_path bname
      |> Theory.add_trfuns ([], [], field_tr's, [])
      |> (Theory.add_consts_i o map Syntax.no_syn)
        (sel_decls @ update_decls @ make_decls)
      |> (PureThy.add_defs_i o map (fn x => (x, [Drule.tag_internal])))
        (sel_specs @ update_specs)
      |> (PureThy.add_defs_i o map Thm.no_attributes) make_specs;

    val sel_defs = get_defs defs_thy sel_specs;
    val update_defs = get_defs defs_thy update_specs;
    val make_defs = get_defs defs_thy make_specs;


    (* 3rd stage: thms_thy *)

    val parent_simps = flat (map #simps parents);
    val prove = prove_simp defs_thy [];

    val sel_convs = map (prove (parent_simps @ sel_defs @ field_simps)) sel_props;
    val update_convs = map (prove (parent_simps @ update_defs @ sel_convs)) update_props;

    val simps = field_simps @ sel_convs @ update_convs @ make_defs;

    val thms_thy =
      defs_thy
      |> (PureThy.add_thmss o map Thm.no_attributes)
        [("select_defs", sel_defs),
          ("update_defs", update_defs),
          ("make_defs", make_defs),
          ("select_convs", sel_convs),
          ("update_convs", update_convs)]
      |> PureThy.add_thmss
        [(("simps", simps), [Simplifier.simp_add_global]),
         (("iffs", field_injects), [add_iffs_global])];


    (* 4th stage: final_thy *)

    val final_thy =
      thms_thy
      |> put_record name {args = args, parent = parent, fields = fields, simps = simps}
      |> add_record_splits named_splits
      |> Theory.parent_path;

  in final_thy end;



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
  add_wrapper record_split_wrapper];


(* outer syntax *)

open OuterParse;

val record_decl =
  type_args -- name -- ($$$ "=" |-- Scan.option (typ --| $$$ "+")
    -- Scan.repeat1 (name -- ($$$ "::" |-- typ)));

val recordP =
  OuterSyntax.parser false "record" "define extensible record"
    (record_decl >> (fn (x, (y, z)) => Toplevel.theory (add_record x y z)));

val _ = OuterSyntax.add_parsers [recordP];

end;


structure BasicRecordPackage: BASIC_RECORD_PACKAGE = RecordPackage;
open BasicRecordPackage;
