(*  Title:      HOL/Tools/record_package.ML
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Extensible records with structural subtyping in HOL.

TODO:
  - record_info: tr' funs;
  - trfuns for record types;
  - field types: typedef;
  - make selector types as general as possible (no!?);
*)

signature RECORD_PACKAGE =
sig
  val print_records: theory -> unit
  val add_record: (string list * bstring) -> string option
    -> (bstring * string) list -> theory -> theory
  val add_record_i: (string list * bstring) -> (typ list * string) option
    -> (bstring * typ) list -> theory -> theory
  val setup: (theory -> theory) list
end;

structure RecordPackage: RECORD_PACKAGE =
struct


(*** syntax operations ***)

(** names **)

(* name components *)

val moreN = "more";
val schemeN = "_scheme";
val fieldN = "_field";
val field_typeN = "_field_type";
val fstN = "_val";
val sndN = "_more";
val updateN = "_update";
val makeN = "make";
val make_schemeN = "make_scheme";


(* suffixes *)

fun suffix sfx s = s ^ sfx;

fun unsuffix sfx s =
  let
    val cs = explode s;
    val prfx_len = size s - size sfx;
  in
    if prfx_len >= 0 andalso implode (drop (prfx_len, cs)) = sfx then
      implode (take (prfx_len, cs))
    else raise LIST "unsuffix"
  end;



(** tuple operations **)

(* more type class *)

val moreS = ["more"];


(* types *)

fun mk_fieldT ((c, T), U) = Type (suffix field_typeN c, [T, U]);

fun dest_fieldT (typ as Type (c_field_type, [T, U])) =
      (case try (unsuffix field_typeN) c_field_type of
        None => raise TYPE ("dest_fieldT", [typ], [])
      | Some c => ((c, T), U))
  | dest_fieldT typ = raise TYPE ("dest_fieldT", [typ], []);


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

fun mk_sel c r =
  let val rT = fastype_of r
  in Const (mk_selC rT (c, find_fieldT c rT)) $ r end;


(* updates *)

fun mk_updateC rT (c, T) = (suffix updateN c, T --> rT --> rT);

fun mk_update c x r =
  let val rT = fastype_of r
  in Const (mk_updateC rT (c, find_fieldT c rT)) $ x $ r end;



(** concrete syntax for records **)

(* parse translations *)

fun field_tr (Const ("_field", _) $ Free (name, _) $ arg) =
      Syntax.const (suffix fieldN name) $ arg
  | field_tr t = raise TERM ("field_tr", [t]);

fun fields_tr (Const ("_fields", _) $ field $ fields) =
      field_tr field :: fields_tr fields
  | fields_tr field = [field_tr field];

fun record_tr (*"_record"*) [fields] =
      foldr (op $) (fields_tr fields, HOLogic.unit)
  | record_tr (*"_record"*) ts = raise TERM ("record_tr", ts);

fun record_scheme_tr (*"_record_scheme"*) [fields, more] =
      foldr (op $) (fields_tr fields, more)
  | record_scheme_tr (*"_record_scheme"*) ts = raise TERM ("record_scheme_tr", ts);


(* print translations *)		(* FIXME tune, activate *)

(* FIXME ... :: tms *)
fun fields_tr' (tm as Const (name_field, _) $ arg $ more) =
      (case try (unsuffix fieldN) name_field of
        Some name =>
          apfst (cons (Syntax.const "_field" $ Syntax.free name $ arg)) (fields_tr' more)
      | None => ([], tm))
  | fields_tr' tm = ([], tm);

fun record_tr' tm =
  let
    val mk_fields = foldr (fn (field, fields) => Syntax.const "_fields" $ field $ fields);
    val (fields, more) = fields_tr' tm;
  in
    if HOLogic.is_unit more then
      Syntax.const "_record" $ mk_fields (split_last fields)
    else Syntax.const "_record_scheme" $ mk_fields (fields, more)
  end;

fun field_tr' name [arg, more] = record_tr' (Syntax.const name $ arg $ more)
  | field_tr' _ _ = raise Match;



(*** extend theory by record definition ***)

(** record info **)

(* type record_info and parent_info *)

type record_info =
 {args: (string * sort) list,
  parent: (typ list * string) option,
  fields: (string * typ) list,
  simps: tthm list};

type parent_info =
 {name: string,
  fields: (string * typ) list,
  simps: tthm list};


(* theory data *)

val recordsK = "HOL/records";
exception Records of record_info Symtab.table;

fun print_records thy = Display.print_data thy recordsK;

local
  val empty = Records Symtab.empty;

  fun prep_ext (x as Records _) = x;

  fun merge (Records tab1, Records tab2) =
    Records (Symtab.merge (K true) (tab1, tab2));

  fun print sg (Records tab) =
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
      seq (Pretty.writeln o pretty_record) (Symtab.dest tab)
    end;
in
  val record_thy_data = (recordsK, (empty, prep_ext, merge, print));
end;


(* get and put records *)

fun get_records thy =
  (case Theory.get_data thy recordsK of
    Records tab => tab
  | _ => type_error recordsK);

fun get_record thy name = Symtab.lookup (get_records thy, name);


fun put_records tab thy =
  Theory.put_data (recordsK, Records tab) thy;

fun put_new_record name info thy =
  thy |> put_records
    (Symtab.update_new ((name, info), get_records thy)
      handle Symtab.DUP _ => error ("Duplicate definition of record " ^ quote name));


(* parent records *)

fun inst_record thy (types, name) =
  let
    val sign = Theory.sign_of thy;
    fun err msg = error (msg ^ " parent record " ^ quote name);

    val {args, parent, fields, simps} =
      (case get_record thy name of Some info => info | None => err "Unknown");

    fun bad_inst ((x, S), T) =
      if Sign.of_sort sign (T, S) then None else Some x
    val bads = mapfilter bad_inst (args ~~ types);

    val inst = map fst args ~~ types;
    val subst = Term.map_type_tfree (fn (x, _) => the (assoc (inst, x)));
  in
    if length types <> length args then
      err "Bad number of arguments for"
    else if not (null bads) then
      err ("Ill-sorted instantiation of " ^ commas bads ^ " in")
    else (apsome (apfst (map subst)) parent, map (apsnd subst) fields, simps)
  end;

fun add_parents thy (None, parents) = parents
  | add_parents thy (Some (types, name), parents) =
      let val (pparent, pfields, psimps) = inst_record thy (types, name)
      in add_parents thy (pparent, {name = name, fields = pfields, simps = psimps} :: parents) end;



(** record theorems **)

(* proof by simplification *)

fun prove_simp thy opt_ss simps =
  let val ss = if_none opt_ss HOL_basic_ss addsimps simps in
    fn goal => Goals.prove_goalw_cterm [] (Thm.cterm_of (sign_of thy) goal)
      (K [ALLGOALS (Simplifier.simp_tac ss)])
  end;



(** internal theory extender **)

(*do the actual record definition, assuming that all arguments are
  well-formed*)

fun record_definition (args, bname) parent (parents: parent_info list) bfields thy =
  let
    val sign = Theory.sign_of thy;
    val full = Sign.full_name_path sign bname;


    (* input *)

    val alphas = map fst args;
    val name = Sign.full_name sign bname;		(* FIXME !? *)
    val parent_fields = flat (map #fields parents);
    val fields = map (apfst full) bfields;

    val all_fields = parent_fields @ fields;
    val all_types = map snd all_fields;


    (* term / type components *)

    val zeta = variant alphas "'z";
    val moreT = TFree (zeta, moreS);

    val xs = variantlist (map fst bfields, []);
    val vars = map2 Free (xs, map snd fields);
    val more = Free (variant xs moreN, moreT);

    val rec_schemeT = mk_recordT (all_fields, moreT);
    val recT = mk_recordT (all_fields, HOLogic.unitT);

    (* FIXME tune *)
    val make_schemeT = all_types ---> moreT --> rec_schemeT;
    val make_scheme = Const (full make_schemeN, make_schemeT);
    val makeT = all_types ---> recT;
    val make = Const (full makeN, makeT);

    val parent_more = funpow (length parent_fields) mk_snd;


    (* prepare type definitions *)

    (*field types*)
    fun mk_fieldT_spec ((c, T), a) =
      (suffix field_typeN c, [a, zeta],
        HOLogic.mk_prodT (TFree (a, HOLogic.termS), moreT), Syntax.NoSyn);
    val fieldT_specs = map2 mk_fieldT_spec (bfields, alphas);

    (*record types*)
    val recordT_specs =
      [(suffix schemeN bname, alphas @ [zeta], rec_schemeT, Syntax.NoSyn),
        (bname, alphas, recT, Syntax.NoSyn)];


    (* prepare declarations *)

    val field_decls = map (mk_fieldC moreT) fields;
    val dest_decls = map (mk_fstC moreT) fields @ map (mk_sndC moreT) fields;
    val sel_decls = map (mk_selC rec_schemeT) fields;
    val update_decls = map (mk_updateC rec_schemeT) fields;
    val make_decls = [(make_schemeN, make_schemeT), (makeN, makeT)];


    (* prepare definitions *)

    (*field constructors*)
    fun mk_field_spec ((c, _), v) =
      Logic.mk_defpair (mk_field ((c, v), more), HOLogic.mk_prod (v, more));
    val field_specs = map2 mk_field_spec (fields, vars);

    (*field destructors*)
    fun mk_dest_spec dest dest' (c, T) =
      let
        val p = Free ("p",  mk_fieldT ((c, T), moreT));
        val p' = Free ("p",  HOLogic.mk_prodT (T, moreT));  (*Note: field types are abbreviations*)
      in Logic.mk_defpair (dest p, dest' p') end;
    val dest_specs =
      map (mk_dest_spec mk_fst HOLogic.mk_fst) fields @
      map (mk_dest_spec mk_snd HOLogic.mk_snd) fields;

    (*field selectors*)		(* FIXME tune *)
    fun mk_sel_specs _ [] specs = rev specs
      | mk_sel_specs prfx ((c, T) :: fs) specs =
          let
            val prfx' = prfx @ [(c, T)];
            val r = Free ("r", mk_recordT (prfx' @ fs, moreT));
            val spec = Logic.mk_defpair (mk_sel c r, mk_fst (funpow (length prfx) mk_snd r));
          in mk_sel_specs prfx' fs (spec :: specs) end;
    val sel_specs = mk_sel_specs parent_fields fields [];

    (*updates*)
    val update_specs = [];	(* FIXME *)

    (*makes*)
    val make_specs =
      map Logic.mk_defpair
        [(list_comb (make_scheme, vars) $ more, mk_record (map fst fields ~~ vars, more)),
          (list_comb (make, vars), mk_record (map fst fields ~~ vars, HOLogic.unit))];


    (* 1st stage: defs_thy *)

    val defs_thy =
      thy
      |> Theory.add_path bname
      |> Theory.add_tyabbrs_i (fieldT_specs @ recordT_specs)
      |> (Theory.add_consts_i o map (Syntax.no_syn o apfst Sign.base_name))
        (field_decls @ dest_decls @ sel_decls @ update_decls @ make_decls)
      |> (PureThy.add_defs_i o map Attribute.none)
        (field_specs @ dest_specs @ sel_specs @ update_specs @ make_specs);

    local fun get_defs specs = map (PureThy.get_tthm defs_thy o fst) specs in
      val make_defs = get_defs make_specs;
      val field_defs = get_defs field_specs;
      val sel_defs = get_defs sel_specs;
      val update_defs = get_defs update_specs;
    end;


    (* 2nd stage: thms_thy *)

    val thms_thy =
      defs_thy
      |> (PureThy.add_tthmss o map Attribute.none)
        [("make_defs", make_defs),
          ("field_defs", field_defs),
          ("sel_defs", sel_defs),
          ("update_defs", update_defs)]
(*    |> record_theorems FIXME *)


    (* 3rd stage: final_thy *)

    val final_thy =
      thms_thy
      |> put_new_record name
        {args = args, parent = parent, fields = fields, simps = [] (* FIXME *)}
      |> Theory.parent_path;

  in final_thy end;



(** theory extender interface **)

(*do all preparations and error checks here, deferring the real work
  to record_definition above*)


(* prepare arguments *)

(*Note: read_raw_typ avoids expanding type abbreviations*)
fun read_raw_parent sign s =
  (case Sign.read_raw_typ (sign, K None) s handle TYPE (msg, _, _) => error msg of
    Type (name, Ts) => (Ts, name)
  | _ => error ("Bad parent record specification: " ^ quote s));

fun read_typ sign (env, s) =
  let
    fun def_type (x, ~1) = assoc (env, x)
      | def_type _ = None;
    val T = Type.no_tvars (Sign.read_typ (sign, def_type) s) handle TYPE (msg, _, _) => error msg;
  in (Term.add_typ_tfrees (T, env), T) end;

fun cert_typ sign (env, raw_T) =
  let val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle TYPE (msg, _, _) => error msg
  in (Term.add_typ_tfrees (T, env), T) end;


(* add_record *)

fun gen_add_record prep_typ prep_raw_parent (params, bname) raw_parent raw_fields thy =
  let
    val _ = Theory.require thy "Record" "record definitions";
    val sign = Theory.sign_of thy;


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

    fun prep_fields (env, []) = (env, [])
      | prep_fields (env, (c, raw_T) :: fs) =
          let
            val (env', T) = prep_typ sign (env, raw_T) handle ERROR =>
              error ("The error(s) above occured in field " ^ quote c);
            val (env'', fs') = prep_fields (env', fs);
      in (env'', (c, T) :: fs') end;

    val (envir, bfields) = prep_fields (init_env, raw_fields);
    val envir_names = map fst envir;


    (* args *)

    val defaultS = Sign.defaultS sign;
    val args = map (fn x => (x, if_none (assoc (envir, x)) defaultS)) params;


    (* errors *)

    val err_dup_parms =
      (case duplicates params of
        [] => []
      | dups => ["Duplicate parameters " ^ commas params]);

    val err_extra_frees =
      (case gen_rems (op =) (envir_names, params) of
        [] => []
      | extras => ["Extraneous free type variables " ^ commas extras]);

    val err_no_fields = if null bfields then ["No fields"] else [];

    val err_dup_fields =
      (case duplicates (map fst bfields) of
        [] => []
      | dups => ["Duplicate fields " ^ commas_quote dups]);

    val err_dup_sorts =
      (case duplicates envir_names of
        [] => []
      | dups => ["Inconsistent sort constraints for " ^ commas dups]);

    val errs =
      err_dup_parms @ err_extra_frees @ err_no_fields @ err_dup_fields @ err_dup_sorts;
  in
    if null errs then ()
    else error (cat_lines errs);

    writeln ("Defining record " ^ quote bname ^ " ...");
    thy |> record_definition (args, bname) parent parents bfields
  end
  handle ERROR => error ("Failed to define record " ^ quote bname);

val add_record = gen_add_record read_typ read_raw_parent;
val add_record_i = gen_add_record cert_typ (K I);



(** setup theory **)

val setup =
 [Theory.init_data [record_thy_data],
  Theory.add_trfuns
    ([], [("_record", record_tr), ("_record_scheme", record_scheme_tr)], [], [])];


end;
