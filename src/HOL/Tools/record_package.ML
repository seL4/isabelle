(*  Title:      HOL/Tools/record_package.ML
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen

Extensible records with structural subtyping in HOL.

TODO:
  - field types: typedef;
  - trfuns for record types;
  - provide more operations and theorems: split, split_all/ex, ...;
  - field constructor: specific type for snd component;
*)

signature RECORD_PACKAGE =
sig
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


(*** syntax operations ***)

(** names **)

(* name components *)

val moreN = "more";
val schemeN = "_scheme";
val fieldN = "_field";
val field_typeN = "_field_type";
val fstN = "_fst";
val sndN = "_snd";
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



(** generic Pure / HOL **)		(* FIXME move(?) *)

val mk_def = Logic.mk_defpair;
val mk_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;



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

fun mk_sel r c =
  let val rT = fastype_of r
  in Const (mk_selC rT (c, find_fieldT c rT)) $ r end;


(* updates *)

fun mk_updateC rT (c, T) = (suffix updateN c, T --> rT --> rT);

fun mk_update r (c, x) =
  let val rT = fastype_of r
  in Const (mk_updateC rT (c, find_fieldT c rT)) $ x $ r end;


(* make *)

fun mk_makeC rT (c, Ts) = (c, Ts ---> rT);



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


(* print translations *)

fun fields_tr' (tm as Const (name_field, _) $ arg $ more) =
      (case try (unsuffix fieldN) name_field of
        Some name =>
          apfst (cons (Syntax.const "_field" $ Syntax.free name $ arg)) (fields_tr' more)
      | None => ([], tm))
  | fields_tr' tm = ([], tm);

fun record_tr' tm =
  let
    val (fields, more) = fields_tr' tm;
    val fields' = foldr1 (fn (f, fs) => Syntax.const "_fields" $ f $ fs) fields;
  in
    if HOLogic.is_unit more then Syntax.const "_record" $ fields'
    else Syntax.const "_record_scheme" $ fields' $ more
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
  simpset: Simplifier.simpset};

type parent_info =
 {name: string,
  fields: (string * typ) list,
  simpset: Simplifier.simpset};


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

      fun pretty_record (name, {args, parent, fields, simpset = _}) = Pretty.block (Pretty.fbreaks
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

fun put_record name info thy =
  thy |> put_records (Symtab.update ((name, info), get_records thy));


(* parent records *)

fun inst_record thy (types, name) =
  let
    val sign = Theory.sign_of thy;
    fun err msg = error (msg ^ " parent record " ^ quote name);

    val {args, parent, fields, simpset} =
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
    else (apsome (apfst (map subst)) parent, map (apsnd subst) fields, simpset)
  end;

fun add_parents thy (None, parents) = parents
  | add_parents thy (Some (types, name), parents) =
      let val (pparent, pfields, psimpset) = inst_record thy (types, name)
      in add_parents thy (pparent, {name = name, fields = pfields, simpset = psimpset} :: parents) end;



(** internal theory extenders **)

(* utils *)

fun get_defs thy specs = map (PureThy.get_tthm thy o fst) specs;

(*proof by simplification*)
fun prove_simp opt_ss simps =
  let
    val ss = if_none opt_ss HOL_basic_ss addsimps (map Attribute.thm_of simps);
    fun prove thy goal =
      Attribute.tthm_of
        (Goals.prove_goalw_cterm [] (Thm.cterm_of (Theory.sign_of thy) goal)
          (K [ALLGOALS (Simplifier.simp_tac ss)])
        handle ERROR => error ("The error(s) above occurred while trying to prove "
          ^ quote (Sign.string_of_term (Theory.sign_of thy) goal)));
  in prove end;

(*thms from Prod.thy*)
val prod_convs = map Attribute.tthm_of [fst_conv, snd_conv];


(* field_definitions *)		(* FIXME tune; actual typedefs! *)

fun field_definitions fields names zeta moreT more vars thy =
  let
    val base = Sign.base_name;


    (* prepare declarations and definitions *)

    (*field types*)
    fun mk_fieldT_spec c =
      (suffix field_typeN c, ["'a", zeta],
        HOLogic.mk_prodT (TFree ("'a", HOLogic.termS), moreT), Syntax.NoSyn);
    val fieldT_specs = map (mk_fieldT_spec o base) names;

    (*field declarations*)
    val field_decls = map (mk_fieldC moreT) fields;
    val dest_decls = map (mk_fstC moreT) fields @ map (mk_sndC moreT) fields;

    (*field constructors*)
    fun mk_field_spec (c, v) =
      mk_def (mk_field ((c, v), more), HOLogic.mk_prod (v, more));
    val field_specs = ListPair.map mk_field_spec (names, vars);

    (*field destructors*)
    fun mk_dest_spec dest dest' (c, T) =
      let
        val p = Free ("p",  mk_fieldT ((c, T), moreT));
        val p' = Free ("p",  HOLogic.mk_prodT (T, moreT));  (*Note: field types are just abbreviations*)
      in mk_def (dest p, dest' p') end;
    val dest_specs =
      map (mk_dest_spec mk_fst HOLogic.mk_fst) fields @
      map (mk_dest_spec mk_snd HOLogic.mk_snd) fields;


    (* prepare theorems *)
    fun mk_dest_prop dest dest' (c, v) =
      mk_eq (dest (mk_field ((c, v), more)), dest' (v, more));
    val dest_props =
      ListPair.map (mk_dest_prop mk_fst fst) (names, vars) @
      ListPair.map (mk_dest_prop mk_snd snd) (names, vars);


    (* 1st stage: defs_thy *)

    val defs_thy =
      thy
      |> Theory.add_tyabbrs_i fieldT_specs
      |> (Theory.add_consts_i o map (Syntax.no_syn o apfst base))
        (field_decls @ dest_decls)
      |> (PureThy.add_defs_i o map Attribute.none)
        (field_specs @ dest_specs);

    val field_defs = get_defs defs_thy field_specs;
    val dest_defs = get_defs defs_thy dest_specs;

    val dest_convs =
      map (prove_simp None (prod_convs @ field_defs @ dest_defs) defs_thy) dest_props;


    (* 2nd stage: thms_thy *)

    val thms_thy =
      defs_thy
      |> (PureThy.add_tthmss o map Attribute.none)
        [("field_defs", field_defs),
          ("dest_defs", dest_defs),
          ("dest_convs", dest_convs)];

  in (thms_thy, dest_convs) end;


(* record_definition *)

(*do the actual record definition, assuming that all arguments are
  well-formed*)

fun record_definition (args, bname) parent (parents: parent_info list) bfields thy =
  let
    val sign = Theory.sign_of thy;
    val full = Sign.full_name_path sign bname;
    val base = Sign.base_name;


    (* basic components *)

    val alphas = map fst args;
    val name = Sign.full_name sign bname;	(*not made part of record name space!*)

    val parent_fields = flat (map #fields parents);
    val parent_names = map fst parent_fields;
    val parent_types = map snd parent_fields;
    val parent_len = length parent_fields;
    val parent_xs = variantlist (map (base o fst) parent_fields, [moreN]);
    val parent_vars = ListPair.map Free (parent_xs, parent_types);

    val fields = map (apfst full) bfields;
    val names = map fst fields;
    val types = map snd fields;
    val len = length fields;
    val xs = variantlist (map fst bfields, moreN :: parent_xs);
    val vars = ListPair.map Free (xs, types);

    val all_fields = parent_fields @ fields;
    val all_names = parent_names @ names;
    val all_types = parent_types @ types;
    val all_len = parent_len + len;
    val all_xs = parent_xs @ xs;
    val all_vars = parent_vars @ vars;


    val zeta = variant alphas "'z";
    val moreT = TFree (zeta, moreS);
    val more = Free (variant xs moreN, moreT);

    val rec_schemeT = mk_recordT (all_fields, moreT);
    val recT = mk_recordT (all_fields, HOLogic.unitT);
    val r = Free ("r", rec_schemeT);

    val parent_more = funpow parent_len mk_snd;


    (* prepare print translation functions *)

    val field_tr'_names =
      distinct (flat (map (NameSpace.accesses o suffix fieldN) names)) \\
        #3 (Syntax.trfun_names (Theory.syn_of thy));
    val field_trfuns = ([], [], field_tr'_names ~~ map field_tr' field_tr'_names, []);


    (* prepare declarations *)

    val sel_decls = map (mk_selC rec_schemeT) fields;
    val more_decl = (moreN, rec_schemeT --> moreT);
    val update_decls = map (mk_updateC rec_schemeT) fields;
    val make_decls =
      [(mk_makeC rec_schemeT (make_schemeN, all_types @ [moreT])),
       (mk_makeC recT (makeN, all_types))];


    (* prepare definitions *)

    (* record (scheme) type abbreviation *)
    val recordT_specs =
      [(suffix schemeN bname, alphas @ [zeta], rec_schemeT, Syntax.NoSyn),
        (bname, alphas, recT, Syntax.NoSyn)];

    (*field selectors*)
    fun mk_sel_spec (i, c) =
      mk_def (mk_sel r c, mk_fst (funpow i mk_snd (parent_more r)));
    val sel_specs = ListPair.map mk_sel_spec (0 upto (len - 1), names);

    (*more quasi-selector*)
    val more_part = Const (full moreN, rec_schemeT --> moreT) $ r;
    val more_spec = mk_def (more_part, funpow len mk_snd (parent_more r));
        
    (*updates*)
    fun mk_upd_spec (i, (c, x)) =
      let
        val prfx = map (mk_sel r) (parent_names @ take (i, names));
        val sffx = map (mk_sel r) (drop (i + 1, names));
      in mk_def (mk_update r (c, x), mk_record (all_names ~~ (prfx @ [x] @ sffx), more_part)) end;
    val update_specs = ListPair.map mk_upd_spec (0 upto (len - 1), names ~~ vars);

    (*makes*)
    val make_scheme = Const (mk_makeC rec_schemeT (full make_schemeN, all_types @ [moreT]));
    val make = Const (mk_makeC recT (full makeN, all_types));
    val make_specs =
      map mk_def
        [(list_comb (make_scheme, all_vars) $ more, mk_record (all_names ~~ all_vars, more)),
          (list_comb (make, all_vars), mk_record (all_names ~~ all_vars, HOLogic.unit))];


    (* 1st stage: fields_thy *)

    val (fields_thy, field_simps) =
      thy
      |> Theory.add_path bname
      |> field_definitions fields names zeta moreT more vars;


    (* 2nd stage: defs_thy *)

    val defs_thy =
      fields_thy
      |> Theory.parent_path
      |> Theory.add_tyabbrs_i recordT_specs	(*not made part of record name space!*)
      |> Theory.add_path bname
      |> Theory.add_trfuns field_trfuns
      |> (Theory.add_consts_i o map (Syntax.no_syn o apfst base))
        (sel_decls @ [more_decl] @ update_decls @ make_decls)
      |> (PureThy.add_defs_i o map Attribute.none)
        (sel_specs @ [more_spec] @ update_specs @ make_specs);

    val sel_defs = get_defs defs_thy sel_specs;
    val more_def = hd (get_defs defs_thy [more_spec]);
    val update_defs = get_defs defs_thy update_specs;
    val make_defs = get_defs defs_thy make_specs;


    (* 3rd stage: thms_thy *)

    val parent_simpset =
      (case parent of
        None => HOL_basic_ss
      | Some (_, pname) => #simpset (the (get_record thy pname)));

    val simpset = parent_simpset;	(* FIXME *)

    val thms_thy =
      defs_thy
      |> (PureThy.add_tthmss o map Attribute.none)
        [("sel_defs", sel_defs),
          ("update_defs", update_defs),
          ("make_defs", make_defs)];

(*    |> record_theorems FIXME *)


    (* 4th stage: final_thy *)

    val final_thy =
      thms_thy
      |> put_record name {args = args, parent = parent, fields = fields, simpset = simpset}
      |> Theory.parent_path;

  in final_thy end;



(** theory extender interface **)

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

(*do all preparations and error checks here, deferring the real work
  to record_definition above*)

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
    writeln ("Defining record " ^ quote bname ^ " ...");
    if null errs then () else error (cat_lines errs);
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
