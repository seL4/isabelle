(*  Title:      HOL/Tools/record.ML
    Author:     Wolfgang Naraschewski, TU Muenchen
    Author:     Markus Wenzel, TU Muenchen
    Author:     Norbert Schirmer, TU Muenchen
    Author:     Thomas Sewell, NICTA

Extensible records with structural subtyping.
*)

signature RECORD =
sig
  val type_abbr: bool Config.T
  val type_as_fields: bool Config.T
  val timing: bool Config.T

  type info =
   {args: (string * sort) list,
    parent: (typ list * string) option,
    fields: (string * typ) list,
    extension: (string * typ list),
    ext_induct: thm, ext_inject: thm, ext_surjective: thm, ext_split: thm, ext_def: thm,
    select_convs: thm list, update_convs: thm list, select_defs: thm list, update_defs: thm list,
    fold_congs: thm list, unfold_congs: thm list, splits: thm list, defs: thm list,
    surjective: thm, equality: thm, induct_scheme: thm, induct: thm, cases_scheme: thm,
    cases: thm, simps: thm list, iffs: thm list}
  val get_info: theory -> string -> info option
  val the_info: theory -> string -> info
  val get_hierarchy: theory -> (string * typ list) -> (string * ((string * sort) * typ) list) list
  val add_record: {overloaded: bool} -> (string * sort) list * binding ->
    (typ list * string) option -> (binding * typ * mixfix) list -> theory -> theory

  val last_extT: typ -> (string * typ list) option
  val dest_recTs: typ -> (string * typ list) list
  val get_extT_fields: theory -> typ -> (string * typ) list * (string * typ)
  val get_recT_fields: theory -> typ -> (string * typ) list * (string * typ)
  val get_parent: theory -> string -> (typ list * string) option
  val get_extension: theory -> string -> (string * typ list) option
  val get_extinjects: theory -> thm list
  val get_simpset: theory -> simpset
  val simproc: simproc
  val eq_simproc: simproc
  val upd_simproc: simproc
  val split_simproc: (term -> int) -> simproc
  val ex_sel_eq_simproc: simproc
  val split_tac: Proof.context -> int -> tactic
  val split_simp_tac: Proof.context -> thm list -> (term -> int) -> int -> tactic
  val split_wrapper: string * (Proof.context -> wrapper)

  val pretty_recT: Proof.context -> typ -> Pretty.T
  val string_of_record: Proof.context -> string -> string

  val codegen: bool Config.T
  val updateN: string
  val ext_typeN: string
  val extN: string
end;


signature ISO_TUPLE_SUPPORT =
sig
  val add_iso_tuple_type: {overloaded: bool} -> binding * (string * sort) list ->
    typ * typ -> theory -> (term * term) * theory
  val mk_cons_tuple: term * term -> term
  val dest_cons_tuple: term -> term * term
  val iso_tuple_intros_tac: Proof.context -> int -> tactic
end;

structure Iso_Tuple_Support: ISO_TUPLE_SUPPORT =
struct

val isoN = "_Tuple_Iso";

val iso_tuple_intro = @{thm isomorphic_tuple_intro};
val iso_tuple_intros = Tactic.build_net @{thms isomorphic_tuple.intros};

val tuple_iso_tuple = (\<^const_name>\<open>Record.tuple_iso_tuple\<close>, @{thm tuple_iso_tuple});

structure Iso_Tuple_Thms = Theory_Data
(
  type T = thm Symtab.table;
  val empty = Symtab.make [tuple_iso_tuple];
  val extend = I;
  fun merge data = Symtab.merge Thm.eq_thm_prop data;   (* FIXME handle Symtab.DUP ?? *)
);

fun get_typedef_info tyco vs
    (({rep_type, Abs_name, ...}, {Rep_inject, Abs_inverse, ... }) : Typedef.info) thy =
  let
    val exists_thm =
      UNIV_I
      |> Thm.instantiate' [SOME (Thm.global_ctyp_of thy (Logic.varifyT_global rep_type))] [];
    val proj_constr = Abs_inverse OF [exists_thm];
    val absT = Type (tyco, map TFree vs);
  in
    thy
    |> pair (tyco, ((Rep_inject, proj_constr), Const (Abs_name, rep_type --> absT), absT))
  end

fun do_typedef overloaded raw_tyco repT raw_vs thy =
  let
    val ctxt = Proof_Context.init_global thy |> Variable.declare_typ repT;
    val vs = map (Proof_Context.check_tfree ctxt) raw_vs;
  in
    thy
    |> Named_Target.theory_map_result (apsnd o Typedef.transform_info)
        (Typedef.add_typedef overloaded (raw_tyco, vs, NoSyn)
          (HOLogic.mk_UNIV repT) NONE (fn ctxt' => resolve_tac ctxt' [UNIV_witness] 1))
    |-> (fn (tyco, info) => get_typedef_info tyco vs info)
  end;

fun mk_cons_tuple (left, right) =
  let
    val (leftT, rightT) = (fastype_of left, fastype_of right);
    val prodT = HOLogic.mk_prodT (leftT, rightT);
    val isomT = Type (\<^type_name>\<open>tuple_isomorphism\<close>, [prodT, leftT, rightT]);
  in
    Const (\<^const_name>\<open>Record.iso_tuple_cons\<close>, isomT --> leftT --> rightT --> prodT) $
      Const (fst tuple_iso_tuple, isomT) $ left $ right
  end;

fun dest_cons_tuple (Const (\<^const_name>\<open>Record.iso_tuple_cons\<close>, _) $ Const _ $ t $ u) = (t, u)
  | dest_cons_tuple t = raise TERM ("dest_cons_tuple", [t]);

fun add_iso_tuple_type overloaded (b, alphas) (leftT, rightT) thy =
  let
    val repT = HOLogic.mk_prodT (leftT, rightT);

    val ((_, ((rep_inject, abs_inverse), absC, absT)), typ_thy) =
      thy
      |> do_typedef overloaded b repT alphas
      ||> Sign.add_path (Binding.name_of b); (*FIXME proper prefixing instead*)
    val typ_ctxt = Proof_Context.init_global typ_thy;

    (*construct a type and body for the isomorphism constant by
      instantiating the theorem to which the definition will be applied*)
    val intro_inst =
      rep_inject RS
        infer_instantiate typ_ctxt
          [(("abst", 0), Thm.cterm_of typ_ctxt absC)] iso_tuple_intro;
    val (_, body) = Logic.dest_equals (List.last (Thm.prems_of intro_inst));
    val isomT = fastype_of body;
    val isom_binding = Binding.suffix_name isoN b;
    val isom_name = Sign.full_name typ_thy isom_binding;
    val isom = Const (isom_name, isomT);

    val ([isom_def], cdef_thy) =
      typ_thy
      |> Sign.declare_const_global ((isom_binding, isomT), NoSyn) |> snd
      |> Global_Theory.add_defs false
        [((Binding.concealed (Thm.def_binding isom_binding), Logic.mk_equals (isom, body)), [])];

    val iso_tuple = isom_def RS (abs_inverse RS (rep_inject RS iso_tuple_intro));
    val cons = Const (\<^const_name>\<open>Record.iso_tuple_cons\<close>, isomT --> leftT --> rightT --> absT);

    val thm_thy =
      cdef_thy
      |> Iso_Tuple_Thms.map (Symtab.insert Thm.eq_thm_prop (isom_name, iso_tuple))
      |> Sign.restore_naming thy
  in
    ((isom, cons $ isom), thm_thy)
  end;

fun iso_tuple_intros_tac ctxt =
  resolve_from_net_tac ctxt iso_tuple_intros THEN'
  CSUBGOAL (fn (cgoal, i) =>
    let
      val goal = Thm.term_of cgoal;

      val isthms = Iso_Tuple_Thms.get (Proof_Context.theory_of ctxt);
      fun err s t = raise TERM ("iso_tuple_intros_tac: " ^ s, [t]);

      val goal' = Envir.beta_eta_contract goal;
      val is =
        (case goal' of
          Const (\<^const_name>\<open>Trueprop\<close>, _) $
            (Const (\<^const_name>\<open>isomorphic_tuple\<close>, _) $ Const is) => is
        | _ => err "unexpected goal format" goal');
      val isthm =
        (case Symtab.lookup isthms (#1 is) of
          SOME isthm => isthm
        | NONE => err "no thm found for constant" (Const is));
    in resolve_tac ctxt [isthm] i end);

end;


structure Record: RECORD =
struct

val surject_assistI = @{thm iso_tuple_surjective_proof_assistI};
val surject_assist_idE = @{thm iso_tuple_surjective_proof_assist_idE};

val updacc_accessor_eqE = @{thm update_accessor_accessor_eqE};
val updacc_updator_eqE = @{thm update_accessor_updator_eqE};
val updacc_eq_idI = @{thm iso_tuple_update_accessor_eq_assist_idI};
val updacc_eq_triv = @{thm iso_tuple_update_accessor_eq_assist_triv};

val updacc_foldE = @{thm update_accessor_congruence_foldE};
val updacc_unfoldE = @{thm update_accessor_congruence_unfoldE};
val updacc_noopE = @{thm update_accessor_noopE};
val updacc_noop_compE = @{thm update_accessor_noop_compE};
val updacc_cong_idI = @{thm update_accessor_cong_assist_idI};
val updacc_cong_triv = @{thm update_accessor_cong_assist_triv};
val updacc_cong_from_eq = @{thm iso_tuple_update_accessor_cong_from_eq};

val codegen = Attrib.setup_config_bool \<^binding>\<open>record_codegen\<close> (K true);


(** name components **)

val rN = "r";
val wN = "w";
val moreN = "more";
val schemeN = "_scheme";
val ext_typeN = "_ext";
val inner_typeN = "_inner";
val extN ="_ext";
val updateN = "_update";
val makeN = "make";
val fields_selN = "fields";
val extendN = "extend";
val truncateN = "truncate";



(*** utilities ***)

fun varifyT idx = map_type_tfree (fn (a, S) => TVar ((a, idx), S));


(* timing *)

val timing = Attrib.setup_config_bool \<^binding>\<open>record_timing\<close> (K false);
fun timeit_msg ctxt s x = if Config.get ctxt timing then (warning s; timeit x) else x ();
fun timing_msg ctxt s = if Config.get ctxt timing then warning s else ();


(* syntax *)

val Trueprop = HOLogic.mk_Trueprop;

infix 0 :== ===;
infixr 0 ==>;

val op :== = Misc_Legacy.mk_defpair;
val op === = Trueprop o HOLogic.mk_eq;
val op ==> = Logic.mk_implies;


(* constructor *)

fun mk_ext (name, T) ts =
  let val Ts = map fastype_of ts
  in list_comb (Const (suffix extN name, Ts ---> T), ts) end;


(* selector *)

fun mk_selC sT (c, T) = (c, sT --> T);

fun mk_sel s (c, T) =
  let val sT = fastype_of s
  in Const (mk_selC sT (c, T)) $ s end;


(* updates *)

fun mk_updC sfx sT (c, T) = (suffix sfx c, (T --> T) --> sT --> sT);

fun mk_upd' sfx c v sT =
  let val vT = domain_type (fastype_of v);
  in Const (mk_updC sfx sT (c, vT)) $ v end;

fun mk_upd sfx c v s = mk_upd' sfx c v (fastype_of s) $ s;


(* types *)

fun dest_recT (typ as Type (c_ext_type, Ts as (_ :: _))) =
      (case try (unsuffix ext_typeN) c_ext_type of
        NONE => raise TYPE ("Record.dest_recT", [typ], [])
      | SOME c => ((c, Ts), List.last Ts))
  | dest_recT typ = raise TYPE ("Record.dest_recT", [typ], []);

val is_recT = can dest_recT;

fun dest_recTs T =
  let val ((c, Ts), U) = dest_recT T
  in (c, Ts) :: dest_recTs U
  end handle TYPE _ => [];

fun last_extT T =
  let val ((c, Ts), U) = dest_recT T in
    (case last_extT U of
      NONE => SOME (c, Ts)
    | SOME l => SOME l)
  end handle TYPE _ => NONE;

fun rec_id i T =
  let
    val rTs = dest_recTs T;
    val rTs' = if i < 0 then rTs else take i rTs;
  in implode (map #1 rTs') end;



(*** extend theory by record definition ***)

(** record info **)

(* type info and parent_info *)

type info =
 {args: (string * sort) list,
  parent: (typ list * string) option,
  fields: (string * typ) list,
  extension: (string * typ list),

  ext_induct: thm,
  ext_inject: thm,
  ext_surjective: thm,
  ext_split: thm,
  ext_def: thm,

  select_convs: thm list,
  update_convs: thm list,
  select_defs: thm list,
  update_defs: thm list,
  fold_congs: thm list,  (* potentially used in L4.verified *)
  unfold_congs: thm list,  (* potentially used in L4.verified *)
  splits: thm list,
  defs: thm list,

  surjective: thm,
  equality: thm,
  induct_scheme: thm,
  induct: thm,
  cases_scheme: thm,
  cases: thm,

  simps: thm list,
  iffs: thm list};

fun make_info args parent fields extension
    ext_induct ext_inject ext_surjective ext_split ext_def
    select_convs update_convs select_defs update_defs fold_congs unfold_congs splits defs
    surjective equality induct_scheme induct cases_scheme cases
    simps iffs : info =
 {args = args, parent = parent, fields = fields, extension = extension,
  ext_induct = ext_induct, ext_inject = ext_inject, ext_surjective = ext_surjective,
  ext_split = ext_split, ext_def = ext_def, select_convs = select_convs,
  update_convs = update_convs, select_defs = select_defs, update_defs = update_defs,
  fold_congs = fold_congs, unfold_congs = unfold_congs, splits = splits, defs = defs,
  surjective = surjective, equality = equality, induct_scheme = induct_scheme,
  induct = induct, cases_scheme = cases_scheme, cases = cases, simps = simps, iffs = iffs};

type parent_info =
 {name: string,
  fields: (string * typ) list,
  extension: (string * typ list),
  induct_scheme: thm,
  ext_def: thm};

fun make_parent_info name fields extension ext_def induct_scheme : parent_info =
 {name = name, fields = fields, extension = extension,
  ext_def = ext_def, induct_scheme = induct_scheme};


(* theory data *)

type data =
 {records: info Symtab.table,
  sel_upd:
   {selectors: (int * bool) Symtab.table,
    updates: string Symtab.table,
    simpset: simpset,
    defset: simpset},
  equalities: thm Symtab.table,
  extinjects: thm list,
  extsplit: thm Symtab.table,  (*maps extension name to split rule*)
  splits: (thm * thm * thm * thm) Symtab.table,  (*!!, ALL, EX - split-equalities, induct rule*)
  extfields: (string * typ) list Symtab.table,  (*maps extension to its fields*)
  fieldext: (string * typ list) Symtab.table};  (*maps field to its extension*)

fun make_data
    records sel_upd equalities extinjects extsplit splits extfields fieldext =
 {records = records, sel_upd = sel_upd,
  equalities = equalities, extinjects=extinjects, extsplit = extsplit, splits = splits,
  extfields = extfields, fieldext = fieldext }: data;

structure Data = Theory_Data
(
  type T = data;
  val empty =
    make_data Symtab.empty
      {selectors = Symtab.empty, updates = Symtab.empty,
        simpset = HOL_basic_ss, defset = HOL_basic_ss}
       Symtab.empty [] Symtab.empty Symtab.empty Symtab.empty Symtab.empty;
  val extend = I;
  fun merge
   ({records = recs1,
     sel_upd = {selectors = sels1, updates = upds1, simpset = ss1, defset = ds1},
     equalities = equalities1,
     extinjects = extinjects1,
     extsplit = extsplit1,
     splits = splits1,
     extfields = extfields1,
     fieldext = fieldext1},
    {records = recs2,
     sel_upd = {selectors = sels2, updates = upds2, simpset = ss2, defset = ds2},
     equalities = equalities2,
     extinjects = extinjects2,
     extsplit = extsplit2,
     splits = splits2,
     extfields = extfields2,
     fieldext = fieldext2}) =
    make_data
      (Symtab.merge (K true) (recs1, recs2))
      {selectors = Symtab.merge (K true) (sels1, sels2),
        updates = Symtab.merge (K true) (upds1, upds2),
        simpset = Simplifier.merge_ss (ss1, ss2),
        defset = Simplifier.merge_ss (ds1, ds2)}
      (Symtab.merge Thm.eq_thm_prop (equalities1, equalities2))
      (Thm.merge_thms (extinjects1, extinjects2))
      (Symtab.merge Thm.eq_thm_prop (extsplit1, extsplit2))
      (Symtab.merge (fn ((a, b, c, d), (w, x, y, z)) =>
          Thm.eq_thm (a, w) andalso Thm.eq_thm (b, x) andalso
          Thm.eq_thm (c, y) andalso Thm.eq_thm (d, z)) (splits1, splits2))
      (Symtab.merge (K true) (extfields1, extfields2))
      (Symtab.merge (K true) (fieldext1, fieldext2));
);


(* access 'records' *)

val get_info = Symtab.lookup o #records o Data.get;

fun the_info thy name =
  (case get_info thy name of
    SOME info => info
  | NONE => error ("Unknown record type " ^ quote name));

fun put_record name info =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    make_data (Symtab.update (name, info) records)
      sel_upd equalities extinjects extsplit splits extfields fieldext);


(* access 'sel_upd' *)

val get_sel_upd = #sel_upd o Data.get;

val is_selector = Symtab.defined o #selectors o get_sel_upd;
val get_updates = Symtab.lookup o #updates o get_sel_upd;

val get_simpset = #simpset o get_sel_upd;
val get_sel_upd_defs = #defset o get_sel_upd;

fun get_update_details u thy =
  let val sel_upd = get_sel_upd thy in
    (case Symtab.lookup (#updates sel_upd) u of
      SOME s =>
        let val SOME (dep, ismore) = Symtab.lookup (#selectors sel_upd) s
        in SOME (s, dep, ismore) end
    | NONE => NONE)
  end;

fun put_sel_upd names more depth simps defs thy =
  let
    val ctxt0 = Proof_Context.init_global thy;

    val all = names @ [more];
    val sels = map (rpair (depth, false)) names @ [(more, (depth, true))];
    val upds = map (suffix updateN) all ~~ all;

    val {records, sel_upd = {selectors, updates, simpset, defset},
      equalities, extinjects, extsplit, splits, extfields, fieldext} = Data.get thy;
    val data =
      make_data records
        {selectors = fold Symtab.update_new sels selectors,
          updates = fold Symtab.update_new upds updates,
          simpset = simpset_map ctxt0 (fn ctxt => ctxt addsimps simps) simpset,
          defset = simpset_map ctxt0 (fn ctxt => ctxt addsimps defs) defset}
         equalities extinjects extsplit splits extfields fieldext;
  in Data.put data thy end;


(* access 'equalities' *)

fun add_equalities name thm =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    make_data records sel_upd
      (Symtab.update_new (name, thm) equalities) extinjects extsplit splits extfields fieldext);

val get_equalities = Symtab.lookup o #equalities o Data.get;


(* access 'extinjects' *)

fun add_extinjects thm =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    make_data records sel_upd equalities (insert Thm.eq_thm_prop thm extinjects)
      extsplit splits extfields fieldext);

val get_extinjects = rev o #extinjects o Data.get;


(* access 'extsplit' *)

fun add_extsplit name thm =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    make_data records sel_upd equalities extinjects
      (Symtab.update_new (name, thm) extsplit) splits extfields fieldext);


(* access 'splits' *)

fun add_splits name thmP =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    make_data records sel_upd equalities extinjects extsplit
      (Symtab.update_new (name, thmP) splits) extfields fieldext);

val get_splits = Symtab.lookup o #splits o Data.get;


(* parent/extension of named record *)

val get_parent = (Option.join o Option.map #parent) oo (Symtab.lookup o #records o Data.get);
val get_extension = Option.map #extension oo (Symtab.lookup o #records o Data.get);


(* access 'extfields' *)

fun add_extfields name fields =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    make_data records sel_upd equalities extinjects extsplit splits
      (Symtab.update_new (name, fields) extfields) fieldext);

val get_extfields = Symtab.lookup o #extfields o Data.get;

fun get_extT_fields thy T =
  let
    val ((name, Ts), moreT) = dest_recT T;
    val recname =
      let val (nm :: _ :: rst) = rev (Long_Name.explode name)   (* FIXME !? *)
      in Long_Name.implode (rev (nm :: rst)) end;
    val varifyT = varifyT (maxidx_of_typs (moreT :: Ts) + 1);
    val {records, extfields, ...} = Data.get thy;
    val (fields, (more, _)) = split_last (Symtab.lookup_list extfields name);
    val args = map varifyT (snd (#extension (the (Symtab.lookup records recname))));

    val subst = fold (Sign.typ_match thy) (#1 (split_last args) ~~ #1 (split_last Ts)) Vartab.empty;
    val fields' = map (apsnd (Envir.norm_type subst o varifyT)) fields;
  in (fields', (more, moreT)) end;

fun get_recT_fields thy T =
  let
    val (root_fields, (root_more, root_moreT)) = get_extT_fields thy T;
    val (rest_fields, rest_more) =
      if is_recT root_moreT then get_recT_fields thy root_moreT
      else ([], (root_more, root_moreT));
  in (root_fields @ rest_fields, rest_more) end;


(* access 'fieldext' *)

fun add_fieldext extname_types fields =
  Data.map (fn {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =>
    let
      val fieldext' =
        fold (fn field => Symtab.update_new (field, extname_types)) fields fieldext;
    in make_data records sel_upd equalities extinjects extsplit splits extfields fieldext' end);

val get_fieldext = Symtab.lookup o #fieldext o Data.get;


(* parent records *)

local

fun add_parents _ NONE = I
  | add_parents thy (SOME (types, name)) =
      let
        fun err msg = error (msg ^ " parent record " ^ quote name);

        val {args, parent, ...} =
          (case get_info thy name of SOME info => info | NONE => err "Unknown");
        val _ = if length types <> length args then err "Bad number of arguments for" else ();

        fun bad_inst ((x, S), T) =
          if Sign.of_sort thy (T, S) then NONE else SOME x
        val bads = map_filter bad_inst (args ~~ types);
        val _ = null bads orelse err ("Ill-sorted instantiation of " ^ commas bads ^ " in");

        val inst = args ~~ types;
        val subst = Term.map_type_tfree (the o AList.lookup (op =) inst);
        val parent' = Option.map (apfst (map subst)) parent;
      in cons (name, inst) #> add_parents thy parent' end;

in

fun get_hierarchy thy (name, types) = add_parents thy (SOME (types, name)) [];

fun get_parent_info thy parent =
  add_parents thy parent [] |> map (fn (name, inst) =>
    let
      val subst = Term.map_type_tfree (the o AList.lookup (op =) inst);
      val {fields, extension, induct_scheme, ext_def, ...} = the_info thy name;
      val fields' = map (apsnd subst) fields;
      val extension' = apsnd (map subst) extension;
    in make_parent_info name fields' extension' ext_def induct_scheme end);

end;



(** concrete syntax for records **)

(* parse translations *)

local

fun split_args (field :: fields) ((name, arg) :: fargs) =
      if can (unsuffix name) field then
        let val (args, rest) = split_args fields fargs
        in (arg :: args, rest) end
      else raise Fail ("expecting field " ^ quote field ^ " but got " ^ quote name)
  | split_args [] (fargs as (_ :: _)) = ([], fargs)
  | split_args (_ :: _) [] = raise Fail "expecting more fields"
  | split_args _ _ = ([], []);

fun field_type_tr ((Const (\<^syntax_const>\<open>_field_type\<close>, _) $ Const (name, _) $ arg)) =
      (name, arg)
  | field_type_tr t = raise TERM ("field_type_tr", [t]);

fun field_types_tr (Const (\<^syntax_const>\<open>_field_types\<close>, _) $ t $ u) =
      field_type_tr t :: field_types_tr u
  | field_types_tr t = [field_type_tr t];

fun record_field_types_tr more ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun err msg = raise TERM ("Error in record-type input: " ^ msg, [t]);

    fun mk_ext (fargs as (name, _) :: _) =
          (case get_fieldext thy (Proof_Context.intern_const ctxt name) of
            SOME (ext, alphas) =>
              (case get_extfields thy ext of
                SOME fields =>
                  let
                    val (fields', _) = split_last fields;
                    val types = map snd fields';
                    val (args, rest) = split_args (map fst fields') fargs
                      handle Fail msg => err msg;
                    val argtypes = Syntax.check_typs ctxt (map Syntax_Phases.decode_typ args);
                    val varifyT = varifyT (fold Term.maxidx_typ argtypes ~1 + 1);
                    val vartypes = map varifyT types;

                    val subst = Type.raw_matches (vartypes, argtypes) Vartab.empty
                      handle Type.TYPE_MATCH => err "type is no proper record (extension)";
                    val alphas' =
                      map (Syntax_Phases.term_of_typ ctxt o Envir.norm_type subst o varifyT)
                        (#1 (split_last alphas));

                    val more' = mk_ext rest;
                  in
                    list_comb
                      (Syntax.const (Lexicon.mark_type (suffix ext_typeN ext)), alphas' @ [more'])
                  end
              | NONE => err ("no fields defined for " ^ quote ext))
          | NONE => err (quote name ^ " is no proper field"))
      | mk_ext [] = more;
  in
    mk_ext (field_types_tr t)
  end;

fun record_type_tr ctxt [t] = record_field_types_tr (Syntax.const \<^type_syntax>\<open>unit\<close>) ctxt t
  | record_type_tr _ ts = raise TERM ("record_type_tr", ts);

fun record_type_scheme_tr ctxt [t, more] = record_field_types_tr more ctxt t
  | record_type_scheme_tr _ ts = raise TERM ("record_type_scheme_tr", ts);


fun field_tr ((Const (\<^syntax_const>\<open>_field\<close>, _) $ Const (name, _) $ arg)) = (name, arg)
  | field_tr t = raise TERM ("field_tr", [t]);

fun fields_tr (Const (\<^syntax_const>\<open>_fields\<close>, _) $ t $ u) = field_tr t :: fields_tr u
  | fields_tr t = [field_tr t];

fun record_fields_tr more ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun err msg = raise TERM ("Error in record input: " ^ msg, [t]);

    fun mk_ext (fargs as (name, _) :: _) =
          (case get_fieldext thy (Proof_Context.intern_const ctxt name) of
            SOME (ext, _) =>
              (case get_extfields thy ext of
                SOME fields =>
                  let
                    val (args, rest) = split_args (map fst (fst (split_last fields))) fargs
                      handle Fail msg => err msg;
                    val more' = mk_ext rest;
                  in list_comb (Syntax.const (Lexicon.mark_const (ext ^ extN)), args @ [more']) end
              | NONE => err ("no fields defined for " ^ quote ext))
          | NONE => err (quote name ^ " is no proper field"))
      | mk_ext [] = more;
  in mk_ext (fields_tr t) end;

fun record_tr ctxt [t] = record_fields_tr (Syntax.const \<^const_syntax>\<open>Unity\<close>) ctxt t
  | record_tr _ ts = raise TERM ("record_tr", ts);

fun record_scheme_tr ctxt [t, more] = record_fields_tr more ctxt t
  | record_scheme_tr _ ts = raise TERM ("record_scheme_tr", ts);


fun field_update_tr (Const (\<^syntax_const>\<open>_field_update\<close>, _) $ Const (name, _) $ arg) =
      Syntax.const (suffix updateN name) $ Abs (Name.uu_, dummyT, arg)
  | field_update_tr t = raise TERM ("field_update_tr", [t]);

fun field_updates_tr (Const (\<^syntax_const>\<open>_field_updates\<close>, _) $ t $ u) =
      field_update_tr t :: field_updates_tr u
  | field_updates_tr t = [field_update_tr t];

fun record_update_tr [t, u] = fold (curry op $) (field_updates_tr u) t
  | record_update_tr ts = raise TERM ("record_update_tr", ts);

in

val _ =
  Theory.setup
   (Sign.parse_translation
     [(\<^syntax_const>\<open>_record_update\<close>, K record_update_tr),
      (\<^syntax_const>\<open>_record\<close>, record_tr),
      (\<^syntax_const>\<open>_record_scheme\<close>, record_scheme_tr),
      (\<^syntax_const>\<open>_record_type\<close>, record_type_tr),
      (\<^syntax_const>\<open>_record_type_scheme\<close>, record_type_scheme_tr)]);

end;


(* print translations *)

val type_abbr = Attrib.setup_config_bool \<^binding>\<open>record_type_abbr\<close> (K true);
val type_as_fields = Attrib.setup_config_bool \<^binding>\<open>record_type_as_fields\<close> (K true);


local

(* FIXME early extern (!??) *)
(* FIXME Syntax.free (??) *)
fun field_type_tr' (c, t) = Syntax.const \<^syntax_const>\<open>_field_type\<close> $ Syntax.const c $ t;

fun field_types_tr' (t, u) = Syntax.const \<^syntax_const>\<open>_field_types\<close> $ t $ u;

fun record_type_tr' ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;

    val T = Syntax_Phases.decode_typ t;
    val varifyT = varifyT (Term.maxidx_of_typ T + 1);

    fun strip_fields T =
      (case T of
        Type (ext, args as _ :: _) =>
          (case try (unsuffix ext_typeN) ext of
            SOME ext' =>
              (case get_extfields thy ext' of
                SOME (fields as (x, _) :: _) =>
                  (case get_fieldext thy x of
                    SOME (_, alphas) =>
                     (let
                        val (f :: fs, _) = split_last fields;
                        val fields' =
                          apfst (Proof_Context.extern_const ctxt) f ::
                            map (apfst Long_Name.base_name) fs;
                        val (args', more) = split_last args;
                        val alphavars = map varifyT (#1 (split_last alphas));
                        val subst = Type.raw_matches (alphavars, args') Vartab.empty;
                        val fields'' = (map o apsnd) (Envir.norm_type subst o varifyT) fields';
                      in fields'' @ strip_fields more end
                      handle Type.TYPE_MATCH => [("", T)])
                  | _ => [("", T)])
              | _ => [("", T)])
          | _ => [("", T)])
      | _ => [("", T)]);

    val (fields, (_, moreT)) = split_last (strip_fields T);
    val _ = null fields andalso raise Match;
    val u =
      foldr1 field_types_tr'
        (map (field_type_tr' o apsnd (Syntax_Phases.term_of_typ ctxt)) fields);
  in
    if not (Config.get ctxt type_as_fields) orelse null fields then raise Match
    else if moreT = HOLogic.unitT then Syntax.const \<^syntax_const>\<open>_record_type\<close> $ u
    else
      Syntax.const \<^syntax_const>\<open>_record_type_scheme\<close> $ u $
        Syntax_Phases.term_of_typ ctxt moreT
  end;

(*try to reconstruct the record name type abbreviation from
  the (nested) extension types*)
fun record_type_abbr_tr' abbr alphas zeta last_ext schemeT ctxt tm =
  let
    val T = Syntax_Phases.decode_typ tm;
    val varifyT = varifyT (maxidx_of_typ T + 1);

    fun mk_type_abbr subst name args =
      let val abbrT = Type (name, map (varifyT o TFree) args)
      in Syntax_Phases.term_of_typ ctxt (Envir.norm_type subst abbrT) end;

    fun match rT T = Type.raw_match (varifyT rT, T) Vartab.empty;
  in
    if Config.get ctxt type_abbr then
      (case last_extT T of
        SOME (name, _) =>
          if name = last_ext then
            let val subst = match schemeT T in
              if HOLogic.is_unitT (Envir.norm_type subst (varifyT (TFree zeta)))
              then mk_type_abbr subst abbr alphas
              else mk_type_abbr subst (suffix schemeN abbr) (alphas @ [zeta])
            end handle Type.TYPE_MATCH => record_type_tr' ctxt tm
          else raise Match (*give print translation of specialised record a chance*)
      | _ => raise Match)
    else record_type_tr' ctxt tm
  end;

in

fun record_ext_type_tr' name =
  let
    val ext_type_name = Lexicon.mark_type (suffix ext_typeN name);
    fun tr' ctxt ts =
      record_type_tr' ctxt (list_comb (Syntax.const ext_type_name, ts));
  in (ext_type_name, tr') end;

fun record_ext_type_abbr_tr' abbr alphas zeta last_ext schemeT name =
  let
    val ext_type_name = Lexicon.mark_type (suffix ext_typeN name);
    fun tr' ctxt ts =
      record_type_abbr_tr' abbr alphas zeta last_ext schemeT ctxt
        (list_comb (Syntax.const ext_type_name, ts));
  in (ext_type_name, tr') end;

end;


local

(* FIXME Syntax.free (??) *)
fun field_tr' (c, t) = Syntax.const \<^syntax_const>\<open>_field\<close> $ Syntax.const c $ t;
fun fields_tr' (t, u) = Syntax.const \<^syntax_const>\<open>_fields\<close> $ t $ u;

fun record_tr' ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun strip_fields t =
      (case strip_comb t of
        (Const (ext, _), args as (_ :: _)) =>
          (case try (Lexicon.unmark_const o unsuffix extN) ext of
            SOME ext' =>
              (case get_extfields thy ext' of
                SOME fields =>
                 (let
                    val (f :: fs, _) = split_last (map fst fields);
                    val fields' = Proof_Context.extern_const ctxt f :: map Long_Name.base_name fs;
                    val (args', more) = split_last args;
                  in (fields' ~~ args') @ strip_fields more end
                  handle ListPair.UnequalLengths => [("", t)])
              | NONE => [("", t)])
          | NONE => [("", t)])
       | _ => [("", t)]);

    val (fields, (_, more)) = split_last (strip_fields t);
    val _ = null fields andalso raise Match;
    val u = foldr1 fields_tr' (map field_tr' fields);
  in
    (case more of
      Const (\<^const_syntax>\<open>Unity\<close>, _) => Syntax.const \<^syntax_const>\<open>_record\<close> $ u
    | _ => Syntax.const \<^syntax_const>\<open>_record_scheme\<close> $ u $ more)
  end;

in

fun record_ext_tr' name =
  let
    val ext_name = Lexicon.mark_const (name ^ extN);
    fun tr' ctxt ts = record_tr' ctxt (list_comb (Syntax.const ext_name, ts));
  in (ext_name, tr') end;

end;


local

fun dest_update ctxt c =
  (case try Lexicon.unmark_const c of
    SOME d => try (unsuffix updateN) (Proof_Context.extern_const ctxt d)
  | NONE => NONE);

fun field_updates_tr' ctxt (tm as Const (c, _) $ k $ u) =
      (case dest_update ctxt c of
        SOME name =>
          (case try Syntax_Trans.const_abs_tr' k of
            SOME t =>
              apfst (cons (Syntax.const \<^syntax_const>\<open>_field_update\<close> $ Syntax.free name $ t))
                (field_updates_tr' ctxt u)
          | NONE => ([], tm))
      | NONE => ([], tm))
  | field_updates_tr' _ tm = ([], tm);

fun record_update_tr' ctxt tm =
  (case field_updates_tr' ctxt tm of
    ([], _) => raise Match
  | (ts, u) =>
      Syntax.const \<^syntax_const>\<open>_record_update\<close> $ u $
        foldr1 (fn (v, w) => Syntax.const \<^syntax_const>\<open>_field_updates\<close> $ v $ w) (rev ts));

in

fun field_update_tr' name =
  let
    val update_name = Lexicon.mark_const (name ^ updateN);
    fun tr' ctxt [t, u] = record_update_tr' ctxt (Syntax.const update_name $ t $ u)
      | tr' _ _ = raise Match;
  in (update_name, tr') end;

end;



(** record simprocs **)

fun is_sel_upd_pair thy (Const (s, _)) (Const (u, t')) =
  (case get_updates thy u of
    SOME u_name => u_name = s
  | NONE => raise TERM ("is_sel_upd_pair: not update", [Const (u, t')]));

fun mk_comp_id f =
  let val T = range_type (fastype_of f)
  in HOLogic.mk_comp (Const (\<^const_name>\<open>Fun.id\<close>, T --> T), f) end;

fun get_upd_funs (upd $ _ $ t) = upd :: get_upd_funs t
  | get_upd_funs _ = [];

fun get_accupd_simps ctxt term defset =
  let
    val thy = Proof_Context.theory_of ctxt;

    val (acc, [body]) = strip_comb term;
    val upd_funs = sort_distinct Term_Ord.fast_term_ord (get_upd_funs body);
    fun get_simp upd =
      let
        (* FIXME fresh "f" (!?) *)
        val T = domain_type (fastype_of upd);
        val lhs = HOLogic.mk_comp (acc, upd $ Free ("f", T));
        val rhs =
          if is_sel_upd_pair thy acc upd
          then HOLogic.mk_comp (Free ("f", T), acc)
          else mk_comp_id acc;
        val prop = lhs === rhs;
        val othm =
          Goal.prove ctxt [] [] prop
            (fn {context = ctxt', ...} =>
              simp_tac (put_simpset defset ctxt') 1 THEN
              REPEAT_DETERM (Iso_Tuple_Support.iso_tuple_intros_tac ctxt' 1) THEN
              TRY (simp_tac (put_simpset HOL_ss ctxt' addsimps @{thms id_apply id_o o_id}) 1));
        val dest =
          if is_sel_upd_pair thy acc upd
          then @{thm o_eq_dest}
          else @{thm o_eq_id_dest};
      in Drule.export_without_context (othm RS dest) end;
  in map get_simp upd_funs end;

fun get_updupd_simp ctxt defset u u' comp =
  let
    (* FIXME fresh "f" (!?) *)
    val f = Free ("f", domain_type (fastype_of u));
    val f' = Free ("f'", domain_type (fastype_of u'));
    val lhs = HOLogic.mk_comp (u $ f, u' $ f');
    val rhs =
      if comp
      then u $ HOLogic.mk_comp (f, f')
      else HOLogic.mk_comp (u' $ f', u $ f);
    val prop = lhs === rhs;
    val othm =
      Goal.prove ctxt [] [] prop
        (fn {context = ctxt', ...} =>
          simp_tac (put_simpset defset ctxt') 1 THEN
          REPEAT_DETERM (Iso_Tuple_Support.iso_tuple_intros_tac ctxt' 1) THEN
          TRY (simp_tac (put_simpset HOL_ss ctxt' addsimps @{thms id_apply}) 1));
    val dest = if comp then @{thm o_eq_dest_lhs} else @{thm o_eq_dest};
  in Drule.export_without_context (othm RS dest) end;

fun get_updupd_simps ctxt term defset =
  let
    val upd_funs = get_upd_funs term;
    val cname = fst o dest_Const;
    fun getswap u u' = get_updupd_simp ctxt defset u u' (cname u = cname u');
    fun build_swaps_to_eq _ [] swaps = swaps
      | build_swaps_to_eq upd (u :: us) swaps =
          let
            val key = (cname u, cname upd);
            val newswaps =
              if Symreltab.defined swaps key then swaps
              else Symreltab.insert (K true) (key, getswap u upd) swaps;
          in
            if cname u = cname upd then newswaps
            else build_swaps_to_eq upd us newswaps
          end;
    fun swaps_needed [] _ _ swaps = map snd (Symreltab.dest swaps)
      | swaps_needed (u :: us) prev seen swaps =
          if Symtab.defined seen (cname u)
          then swaps_needed us prev seen (build_swaps_to_eq u prev swaps)
          else swaps_needed us (u :: prev) (Symtab.insert (K true) (cname u, ()) seen) swaps;
  in swaps_needed upd_funs [] Symtab.empty Symreltab.empty end;

fun prove_unfold_defs thy ex_simps ex_simprs prop =
  let
    val ctxt = Proof_Context.init_global thy;

    val defset = get_sel_upd_defs thy;
    val prop' = Envir.beta_eta_contract prop;
    val (lhs, _) = Logic.dest_equals (Logic.strip_assums_concl prop');
    val (_, args) = strip_comb lhs;
    val simps = (if length args = 1 then get_accupd_simps else get_updupd_simps) ctxt lhs defset;
  in
    Goal.prove ctxt [] [] prop'
      (fn {context = ctxt', ...} =>
        simp_tac (put_simpset HOL_basic_ss ctxt' addsimps (simps @ @{thms K_record_comp})) 1 THEN
        TRY (simp_tac (put_simpset HOL_basic_ss ctxt' addsimps ex_simps addsimprocs ex_simprs) 1))
  end;


local

fun eq (s1: string) (s2: string) = (s1 = s2);

fun has_field extfields f T =
  exists (fn (eN, _) => exists (eq f o fst) (Symtab.lookup_list extfields eN)) (dest_recTs T);

fun K_skeleton n (T as Type (_, [_, kT])) (b as Bound i) (Abs (x, xT, t)) =
      if null (loose_bnos t) then ((n, kT), (Abs (x, xT, Bound (i + 1)))) else ((n, T), b)
  | K_skeleton n T b _ = ((n, T), b);

in

(* simproc *)

(*
  Simplify selections of an record update:
    (1)  S (S_update k r) = k (S r)
    (2)  S (X_update k r) = S r

  The simproc skips multiple updates at once, eg:
   S (X_update x (Y_update y (S_update k r))) = k (S r)

  But be careful in (2) because of the extensibility of records.
  - If S is a more-selector we have to make sure that the update on component
    X does not affect the selected subrecord.
  - If X is a more-selector we have to make sure that S is not in the updated
    subrecord.
*)
val simproc =
  Simplifier.make_simproc \<^context> "record"
   {lhss = [\<^term>\<open>x::'a::{}\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val t = Thm.term_of ct;
      in
        (case t of
          (sel as Const (s, Type (_, [_, rangeS]))) $
              ((upd as Const (u, Type (_, [_, Type (_, [rT, _])]))) $ k $ r) =>
            if is_selector thy s andalso is_some (get_updates thy u) then
              let
                val {sel_upd = {updates, ...}, extfields, ...} = Data.get thy;

                fun mk_eq_terms ((upd as Const (u, Type(_, [kT, _]))) $ k $ r) =
                      (case Symtab.lookup updates u of
                        NONE => NONE
                      | SOME u_name =>
                          if u_name = s then
                            (case mk_eq_terms r of
                              NONE =>
                                let
                                  val rv = ("r", rT);
                                  val rb = Bound 0;
                                  val (kv, kb) = K_skeleton "k" kT (Bound 1) k;
                                in SOME (upd $ kb $ rb, kb $ (sel $ rb), [kv, rv]) end
                            | SOME (trm, trm', vars) =>
                                let
                                  val (kv, kb) = K_skeleton "k" kT (Bound (length vars)) k;
                                in SOME (upd $ kb $ trm, kb $ trm', kv :: vars) end)
                          else if has_field extfields u_name rangeS orelse
                            has_field extfields s (domain_type kT) then NONE
                          else
                            (case mk_eq_terms r of
                              SOME (trm, trm', vars) =>
                                let val (kv, kb) = K_skeleton "k" kT (Bound (length vars)) k
                                in SOME (upd $ kb $ trm, trm', kv :: vars) end
                            | NONE =>
                                let
                                  val rv = ("r", rT);
                                  val rb = Bound 0;
                                  val (kv, kb) = K_skeleton "k" kT (Bound 1) k;
                                in SOME (upd $ kb $ rb, sel $ rb, [kv, rv]) end))
                  | mk_eq_terms _ = NONE;
              in
                (case mk_eq_terms (upd $ k $ r) of
                  SOME (trm, trm', vars) =>
                    SOME
                      (prove_unfold_defs thy [] []
                        (Logic.list_all (vars, Logic.mk_equals (sel $ trm, trm'))))
                | NONE => NONE)
              end
            else NONE
        | _ => NONE)
      end};

fun get_upd_acc_cong_thm upd acc thy ss =
  let
    val ctxt = Proof_Context.init_global thy;
    val prop =
      infer_instantiate ctxt
        [(("upd", 0), Thm.cterm_of ctxt upd), (("ac", 0), Thm.cterm_of ctxt acc)]
        updacc_cong_triv
      |> Thm.concl_of;
  in
    Goal.prove ctxt [] [] prop
      (fn {context = ctxt', ...} =>
        simp_tac (put_simpset ss ctxt') 1 THEN
        REPEAT_DETERM (Iso_Tuple_Support.iso_tuple_intros_tac ctxt' 1) THEN
        TRY (resolve_tac ctxt' [updacc_cong_idI] 1))
  end;


(* upd_simproc *)

(*Simplify multiple updates:
    (1) "N_update y (M_update g (N_update x (M_update f r))) =
          (N_update (y o x) (M_update (g o f) r))"
    (2)  "r(|M:= M r|) = r"

  In both cases "more" updates complicate matters: for this reason
  we omit considering further updates if doing so would introduce
  both a more update and an update to a field within it.*)
val upd_simproc =
  Simplifier.make_simproc \<^context> "record_upd"
   {lhss = [\<^term>\<open>x::'a::{}\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val t = Thm.term_of ct;
        (*We can use more-updators with other updators as long
          as none of the other updators go deeper than any more
          updator. min here is the depth of the deepest other
          updator, max the depth of the shallowest more updator.*)
        fun include_depth (dep, true) (min, max) =
              if min <= dep
              then SOME (min, if dep <= max orelse max = ~1 then dep else max)
              else NONE
          | include_depth (dep, false) (min, max) =
              if dep <= max orelse max = ~1
              then SOME (if min <= dep then dep else min, max)
              else NONE;

        fun getupdseq (term as (upd as Const (u, _)) $ f $ tm) min max =
              (case get_update_details u thy of
                SOME (s, dep, ismore) =>
                  (case include_depth (dep, ismore) (min, max) of
                    SOME (min', max') =>
                      let val (us, bs, _) = getupdseq tm min' max'
                      in ((upd, s, f) :: us, bs, fastype_of term) end
                  | NONE => ([], term, HOLogic.unitT))
              | NONE => ([], term, HOLogic.unitT))
          | getupdseq term _ _ = ([], term, HOLogic.unitT);

        val (upds, base, baseT) = getupdseq t 0 ~1;

        fun is_upd_noop s (Abs (n, T, Const (s', T') $ tm')) tm =
              if s = s' andalso null (loose_bnos tm')
                andalso subst_bound (HOLogic.unit, tm') = tm
              then (true, Abs (n, T, Const (s', T') $ Bound 1))
              else (false, HOLogic.unit)
          | is_upd_noop _ _ _ = (false, HOLogic.unit);

        fun get_noop_simps (upd as Const _) (Abs (_, _, (acc as Const _) $ _)) =
          let
            val ss = get_sel_upd_defs thy;
            val uathm = get_upd_acc_cong_thm upd acc thy ss;
          in
           [Drule.export_without_context (uathm RS updacc_noopE),
            Drule.export_without_context (uathm RS updacc_noop_compE)]
          end;

        (*If f is constant then (f o g) = f.  We know that K_skeleton
          only returns constant abstractions thus when we see an
          abstraction we can discard inner updates.*)
        fun add_upd (f as Abs _) _ = [f]
          | add_upd f fs = (f :: fs);

        (*mk_updterm returns
          (orig-term-skeleton, simplified-skeleton,
            variables, duplicate-updates, simp-flag, noop-simps)

          where duplicate-updates is a table used to pass upward
          the list of update functions which can be composed
          into an update above them, simp-flag indicates whether
          any simplification was achieved, and noop-simps are
          used for eliminating case (2) defined above*)
        fun mk_updterm ((upd as Const (u, T), s, f) :: upds) above term =
              let
                val (lhs, rhs, vars, dups, simp, noops) =
                  mk_updterm upds (Symtab.update (u, ()) above) term;
                val (fvar, skelf) =
                  K_skeleton (Long_Name.base_name s) (domain_type T) (Bound (length vars)) f;
                val (isnoop, skelf') = is_upd_noop s f term;
                val funT = domain_type T;
                fun mk_comp_local (f, f') =
                  Const (\<^const_name>\<open>Fun.comp\<close>, funT --> funT --> funT) $ f $ f';
              in
                if isnoop then
                  (upd $ skelf' $ lhs, rhs, vars,
                    Symtab.update (u, []) dups, true,
                    if Symtab.defined noops u then noops
                    else Symtab.update (u, get_noop_simps upd skelf') noops)
                else if Symtab.defined above u then
                  (upd $ skelf $ lhs, rhs, fvar :: vars,
                    Symtab.map_default (u, []) (add_upd skelf) dups,
                    true, noops)
                else
                  (case Symtab.lookup dups u of
                    SOME fs =>
                     (upd $ skelf $ lhs,
                      upd $ foldr1 mk_comp_local (add_upd skelf fs) $ rhs,
                      fvar :: vars, dups, true, noops)
                  | NONE => (upd $ skelf $ lhs, upd $ skelf $ rhs, fvar :: vars, dups, simp, noops))
              end
          | mk_updterm [] _ _ =
              (Bound 0, Bound 0, [("r", baseT)], Symtab.empty, false, Symtab.empty)
          | mk_updterm us _ _ = raise TERM ("mk_updterm match", map (fn (x, _, _) => x) us);

        val (lhs, rhs, vars, _, simp, noops) = mk_updterm upds Symtab.empty base;
        val noops' = maps snd (Symtab.dest noops);
      in
        if simp then
          SOME
            (prove_unfold_defs thy noops' [simproc]
              (Logic.list_all (vars, Logic.mk_equals (lhs, rhs))))
        else NONE
      end};

end;


(* eq_simproc *)

(*Look up the most specific record-equality.

 Note on efficiency:
 Testing equality of records boils down to the test of equality of all components.
 Therefore the complexity is: #components * complexity for single component.
 Especially if a record has a lot of components it may be better to split up
 the record first and do simplification on that (split_simp_tac).
 e.g. r(|lots of updates|) = x

             eq_simproc          split_simp_tac
 Complexity: #components * #updates     #updates
*)
val eq_simproc =
  Simplifier.make_simproc \<^context> "record_eq"
   {lhss = [\<^term>\<open>r = s\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.eq\<close>, Type (_, [T, _])) $ _ $ _ =>
          (case rec_id ~1 T of
            "" => NONE
          | name =>
              (case get_equalities (Proof_Context.theory_of ctxt) name of
                NONE => NONE
              | SOME thm => SOME (thm RS @{thm Eq_TrueI})))
      | _ => NONE)};


(* split_simproc *)

(*Split quantified occurrences of records, for which P holds.  P can peek on the
  subterm starting at the quantified occurrence of the record (including the quantifier):
    P t = 0: do not split
    P t = ~1: completely split
    P t > 0: split up to given bound of record extensions.*)
fun split_simproc P =
  Simplifier.make_simproc \<^context> "record_split"
   {lhss = [\<^term>\<open>x::'a::{}\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      (case Thm.term_of ct of
        Const (quantifier, Type (_, [Type (_, [T, _]), _])) $ _ =>
          if quantifier = \<^const_name>\<open>Pure.all\<close> orelse
            quantifier = \<^const_name>\<open>All\<close> orelse
            quantifier = \<^const_name>\<open>Ex\<close>
          then
            (case rec_id ~1 T of
              "" => NONE
            | _ =>
                let val split = P (Thm.term_of ct) in
                  if split <> 0 then
                    (case get_splits (Proof_Context.theory_of ctxt) (rec_id split T) of
                      NONE => NONE
                    | SOME (all_thm, All_thm, Ex_thm, _) =>
                        SOME
                          (case quantifier of
                            \<^const_name>\<open>Pure.all\<close> => all_thm
                          | \<^const_name>\<open>All\<close> => All_thm RS @{thm eq_reflection}
                          | \<^const_name>\<open>Ex\<close> => Ex_thm RS @{thm eq_reflection}
                          | _ => raise Fail "split_simproc"))
                  else NONE
                end)
          else NONE
      | _ => NONE)};

val ex_sel_eq_simproc =
  Simplifier.make_simproc \<^context> "ex_sel_eq"
   {lhss = [\<^term>\<open>Ex t\<close>],
    proc = fn _ => fn ctxt => fn ct =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val t = Thm.term_of ct;
        fun mkeq (lr, Teq, (sel, Tsel), x) i =
          if is_selector thy sel then
            let
              val x' =
                if not (Term.is_dependent x)
                then Free ("x" ^ string_of_int i, range_type Tsel)
                else raise TERM ("", [x]);
              val sel' = Const (sel, Tsel) $ Bound 0;
              val (l, r) = if lr then (sel', x') else (x', sel');
            in Const (\<^const_name>\<open>HOL.eq\<close>, Teq) $ l $ r end
          else raise TERM ("", [Const (sel, Tsel)]);

        fun dest_sel_eq (Const (\<^const_name>\<open>HOL.eq\<close>, Teq) $ (Const (sel, Tsel) $ Bound 0) $ X) =
              (true, Teq, (sel, Tsel), X)
          | dest_sel_eq (Const (\<^const_name>\<open>HOL.eq\<close>, Teq) $ X $ (Const (sel, Tsel) $ Bound 0)) =
              (false, Teq, (sel, Tsel), X)
          | dest_sel_eq _ = raise TERM ("", []);
      in
        (case t of
          Const (\<^const_name>\<open>Ex\<close>, Tex) $ Abs (s, T, t) =>
           (let
             val eq = mkeq (dest_sel_eq t) 0;
             val prop =
               Logic.list_all ([("r", T)],
                 Logic.mk_equals
                  (Const (\<^const_name>\<open>Ex\<close>, Tex) $ Abs (s, T, eq), \<^term>\<open>True\<close>));
            in
              SOME (Goal.prove_sorry_global thy [] [] prop
                (fn _ => simp_tac (put_simpset (get_simpset thy) ctxt
                    addsimps @{thms simp_thms} addsimprocs [split_simproc (K ~1)]) 1))
            end handle TERM _ => NONE)
        | _ => NONE)
      end};


(* split_simp_tac *)

(*Split (and simplify) all records in the goal for which P holds.
  For quantified occurrences of a record
  P can peek on the whole subterm (including the quantifier); for free variables P
  can only peek on the variable itself.
  P t = 0: do not split
  P t = ~1: completely split
  P t > 0: split up to given bound of record extensions.*)
fun split_simp_tac ctxt thms P = CSUBGOAL (fn (cgoal, i) =>
  let
    val thy = Proof_Context.theory_of ctxt;

    val goal = Thm.term_of cgoal;
    val frees = filter (is_recT o #2) (Term.add_frees goal []);

    val has_rec = exists_Const
      (fn (s, Type (_, [Type (_, [T, _]), _])) =>
          (s = \<^const_name>\<open>Pure.all\<close> orelse s = \<^const_name>\<open>All\<close> orelse s = \<^const_name>\<open>Ex\<close>)
            andalso is_recT T
        | _ => false);

    fun mk_split_free_tac free induct_thm i =
      let
        val _ $ (_ $ Var (r, _)) = Thm.concl_of induct_thm;
        val thm = infer_instantiate ctxt [(r, Thm.cterm_of ctxt free)] induct_thm;
      in
        simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms induct_atomize}) i THEN
        resolve_tac ctxt [thm] i THEN
        simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms induct_rulify}) i
      end;

    val split_frees_tacs =
      frees |> map_filter (fn (x, T) =>
        (case rec_id ~1 T of
          "" => NONE
        | _ =>
            let
              val free = Free (x, T);
              val split = P free;
            in
              if split <> 0 then
                (case get_splits thy (rec_id split T) of
                  NONE => NONE
                | SOME (_, _, _, induct_thm) =>
                    SOME (mk_split_free_tac free induct_thm i))
              else NONE
            end));

    val simprocs = if has_rec goal then [split_simproc P] else [];
    val thms' = @{thms o_apply K_record_comp} @ thms;
  in
    EVERY split_frees_tacs THEN
    full_simp_tac (put_simpset (get_simpset thy) ctxt addsimps thms' addsimprocs simprocs) i
  end);


(* split_tac *)

(*Split all records in the goal, which are quantified by !! or ALL.*)
fun split_tac ctxt = CSUBGOAL (fn (cgoal, i) =>
  let
    val goal = Thm.term_of cgoal;

    val has_rec = exists_Const
      (fn (s, Type (_, [Type (_, [T, _]), _])) =>
          (s = \<^const_name>\<open>Pure.all\<close> orelse s = \<^const_name>\<open>All\<close>) andalso is_recT T
        | _ => false);

    fun is_all (Const (\<^const_name>\<open>Pure.all\<close>, _) $ _) = ~1
      | is_all (Const (\<^const_name>\<open>All\<close>, _) $ _) = ~1
      | is_all _ = 0;
  in
    if has_rec goal then
      full_simp_tac (put_simpset HOL_basic_ss ctxt addsimprocs [split_simproc is_all]) i
    else no_tac
  end);

val _ =
  Theory.setup
    (map_theory_simpset (fn ctxt => ctxt addsimprocs [simproc, upd_simproc, eq_simproc]));


(* wrapper *)

val split_name = "record_split_tac";
val split_wrapper = (split_name, fn ctxt => fn tac => split_tac ctxt ORELSE' tac);



(** theory extender interface **)

(* attributes *)

fun case_names_fields x = Rule_Cases.case_names ["fields"] x;
fun induct_type_global name = [case_names_fields, Induct.induct_type name];
fun cases_type_global name = [case_names_fields, Induct.cases_type name];


(* tactics *)

(*Do case analysis / induction according to rule on last parameter of ith subgoal
  (or on s if there are no parameters).
  Instatiation of record variable (and predicate) in rule is calculated to
  avoid problems with higher order unification.*)
fun try_param_tac ctxt s rule = CSUBGOAL (fn (cgoal, i) =>
  let
    val g = Thm.term_of cgoal;
    val params = Logic.strip_params g;
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl g);
    val rule' = Thm.lift_rule cgoal rule;
    val (P, ys) = strip_comb (HOLogic.dest_Trueprop (Logic.strip_assums_concl (Thm.prop_of rule')));
    (*ca indicates if rule is a case analysis or induction rule*)
    val (x, ca) =
      (case rev (drop (length params) ys) of
        [] => (head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop
          (hd (rev (Logic.strip_assums_hyp (hd (Thm.prems_of rule')))))))), true)
      | [x] => (head_of x, false));
    val rule'' =
      infer_instantiate ctxt
        (map (apsnd (Thm.cterm_of ctxt))
          (case rev params of
            [] =>
              (case AList.lookup (op =) (Term.add_frees g []) s of
                NONE => error "try_param_tac: no such variable"
              | SOME T =>
                  [(#1 (dest_Var P), if ca then concl else lambda (Free (s, T)) concl),
                   (#1 (dest_Var x), Free (s, T))])
          | (_, T) :: _ =>
              [(#1 (dest_Var P),
                fold_rev Term.abs params
                  (if ca then concl else incr_boundvars 1 (Abs (s, T, concl)))),
               (#1 (dest_Var x), fold_rev Term.abs params (Bound 0))])) rule';
  in compose_tac ctxt (false, rule'', Thm.nprems_of rule) i end);


fun extension_definition overloaded name fields alphas zeta moreT more vars thy =
  let
    val ctxt = Proof_Context.init_global thy;

    val base_name = Long_Name.base_name name;

    val fieldTs = map snd fields;
    val fields_moreTs = fieldTs @ [moreT];

    val alphas_zeta = alphas @ [zeta];

    val ext_binding = Binding.name (suffix extN base_name);
    val ext_name = suffix extN name;
    val ext_tyco = suffix ext_typeN name;
    val extT = Type (ext_tyco, map TFree alphas_zeta);
    val ext_type = fields_moreTs ---> extT;


    (* the tree of new types that will back the record extension *)

    val mktreeV = Balanced_Tree.make Iso_Tuple_Support.mk_cons_tuple;

    fun mk_iso_tuple (left, right) (thy, i) =
      let
        val suff = if i = 0 then ext_typeN else inner_typeN ^ string_of_int i;
        val ((_, cons), thy') = thy
          |> Iso_Tuple_Support.add_iso_tuple_type overloaded
            (Binding.suffix_name suff (Binding.name base_name), alphas_zeta)
              (fastype_of left, fastype_of right);
      in
        (cons $ left $ right, (thy', i + 1))
      end;

    (*trying to create a 1-element iso_tuple will fail, and is pointless anyway*)
    fun mk_even_iso_tuple [arg] = pair arg
      | mk_even_iso_tuple args = mk_iso_tuple (Iso_Tuple_Support.dest_cons_tuple (mktreeV args));

    fun build_meta_tree_type i thy vars more =
      let val len = length vars in
        if len < 1 then raise TYPE ("meta_tree_type args too short", [], vars)
        else if len > 16 then
          let
            fun group16 [] = []
              | group16 xs = take 16 xs :: group16 (drop 16 xs);
            val vars' = group16 vars;
            val (composites, (thy', i')) = fold_map mk_even_iso_tuple vars' (thy, i);
          in
            build_meta_tree_type i' thy' composites more
          end
        else
          let val (term, (thy', _)) = mk_iso_tuple (mktreeV vars, more) (thy, 0)
          in (term, thy') end
      end;

    val _ = timing_msg ctxt "record extension preparing definitions";


    (* 1st stage part 1: introduce the tree of new types *)

    val (ext_body, typ_thy) = timeit_msg ctxt "record extension nested type def:" (fn () =>
      build_meta_tree_type 1 thy vars more);


    (* prepare declarations and definitions *)

    (* 1st stage part 2: define the ext constant *)

    fun mk_ext args = list_comb (Const (ext_name, ext_type), args);
    val ext_spec = Logic.mk_equals (mk_ext (vars @ [more]), ext_body);

    val ([ext_def], defs_thy) = timeit_msg ctxt "record extension constructor def:" (fn () =>
      typ_thy
      |> Sign.declare_const_global ((ext_binding, ext_type), NoSyn) |> snd
      |> Global_Theory.add_defs false [((Thm.def_binding ext_binding, ext_spec), [])]);
    val defs_ctxt = Proof_Context.init_global defs_thy;


    (* prepare propositions *)

    val _ = timing_msg ctxt "record extension preparing propositions";
    val vars_more = vars @ [more];
    val variants = map (fn Free (x, _) => x) vars_more;
    val ext = mk_ext vars_more;
    val s = Free (rN, extT);
    val P = Free (singleton (Name.variant_list variants) "P", extT --> HOLogic.boolT);

    val inject_prop =  (* FIXME local x x' *)
      let val vars_more' = map (fn (Free (x, T)) => Free (x ^ "'", T)) vars_more in
        HOLogic.mk_conj (HOLogic.eq_const extT $
          mk_ext vars_more $ mk_ext vars_more', \<^term>\<open>True\<close>)
        ===
        foldr1 HOLogic.mk_conj
          (map HOLogic.mk_eq (vars_more ~~ vars_more') @ [\<^term>\<open>True\<close>])
      end;

    val induct_prop = (fold_rev Logic.all vars_more (Trueprop (P $ ext)), Trueprop (P $ s));

    val split_meta_prop =  (* FIXME local P *)
      let val P = Free (singleton (Name.variant_list variants) "P", extT --> propT)
      in Logic.mk_equals (Logic.all s (P $ s), fold_rev Logic.all vars_more (P $ ext)) end;

    val inject = timeit_msg ctxt "record extension inject proof:" (fn () =>
      simplify (put_simpset HOL_ss defs_ctxt)
        (Goal.prove_sorry_global defs_thy [] [] inject_prop
          (fn {context = ctxt', ...} =>
            simp_tac (put_simpset HOL_basic_ss ctxt' addsimps [ext_def]) 1 THEN
            REPEAT_DETERM
              (resolve_tac ctxt' @{thms refl_conj_eq} 1 ORELSE
                Iso_Tuple_Support.iso_tuple_intros_tac ctxt' 1 ORELSE
                resolve_tac ctxt' [refl] 1))));


    (*We need a surjection property r = (| f = f r, g = g r ... |)
      to prove other theorems. We haven't given names to the accessors
      f, g etc yet however, so we generate an ext structure with
      free variables as all arguments and allow the introduction tactic to
      operate on it as far as it can. We then use Drule.export_without_context
      to convert the free variables into unifiable variables and unify them with
      (roughly) the definition of the accessor.*)
    val surject = timeit_msg ctxt "record extension surjective proof:" (fn () =>
      let
        val start =
          infer_instantiate defs_ctxt [(("y", 0), Thm.cterm_of defs_ctxt ext)] surject_assist_idE;
        val tactic1 =
          simp_tac (put_simpset HOL_basic_ss defs_ctxt addsimps [ext_def]) 1 THEN
          REPEAT_ALL_NEW (Iso_Tuple_Support.iso_tuple_intros_tac defs_ctxt) 1;
        val tactic2 =
          REPEAT (resolve_tac defs_ctxt [surject_assistI] 1 THEN resolve_tac defs_ctxt [refl] 1);
        val [halfway] = Seq.list_of (tactic1 start);
        val [surject] = Seq.list_of (tactic2 (Drule.export_without_context halfway));
      in
        surject
      end);

    val split_meta = timeit_msg ctxt "record extension split_meta proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] split_meta_prop
        (fn {context = ctxt', ...} =>
          EVERY1
           [resolve_tac ctxt' @{thms equal_intr_rule},
            Goal.norm_hhf_tac ctxt',
            eresolve_tac ctxt' @{thms meta_allE}, assume_tac ctxt',
            resolve_tac ctxt' [@{thm prop_subst} OF [surject]],
            REPEAT o eresolve_tac ctxt' @{thms meta_allE}, assume_tac ctxt']));

    val induct = timeit_msg ctxt "record extension induct proof:" (fn () =>
      let val (assm, concl) = induct_prop in
        Goal.prove_sorry_global defs_thy [] [assm] concl
          (fn {context = ctxt', prems, ...} =>
            cut_tac (split_meta RS Drule.equal_elim_rule2) 1 THEN
            resolve_tac ctxt' prems 2 THEN
            asm_simp_tac (put_simpset HOL_ss ctxt') 1)
      end);

    val ([(_, [induct']), (_, [inject']), (_, [surjective']), (_, [split_meta'])], thm_thy) =
      defs_thy
      |> Global_Theory.note_thmss ""
          [((Binding.name "ext_induct", []), [([induct], [])]),
           ((Binding.name "ext_inject", []), [([inject], [])]),
           ((Binding.name "ext_surjective", []), [([surject], [])]),
           ((Binding.name "ext_split", []), [([split_meta], [])])];
  in
    (((ext_name, ext_type), (ext_tyco, alphas_zeta),
      extT, induct', inject', surjective', split_meta', ext_def), thm_thy)
  end;

fun chunks [] [] = []
  | chunks [] xs = [xs]
  | chunks (l :: ls) xs = take l xs :: chunks ls (drop l xs);

fun chop_last [] = error "chop_last: list should not be empty"
  | chop_last [x] = ([], x)
  | chop_last (x :: xs) = let val (tl, l) = chop_last xs in (x :: tl, l) end;

fun subst_last _ [] = error "subst_last: list should not be empty"
  | subst_last s [_] = [s]
  | subst_last s (x :: xs) = x :: subst_last s xs;


(* mk_recordT *)

(*build up the record type from the current extension tpye extT and a list
  of parent extensions, starting with the root of the record hierarchy*)
fun mk_recordT extT =
  fold_rev (fn (parent, Ts) => fn T => Type (parent, subst_last T Ts)) extT;


(* code generation *)

fun mk_random_eq tyco vs extN Ts =
  let
    (* FIXME local i etc. *)
    val size = \<^term>\<open>i::natural\<close>;
    fun termifyT T = HOLogic.mk_prodT (T, \<^typ>\<open>unit \<Rightarrow> term\<close>);
    val T = Type (tyco, map TFree vs);
    val Tm = termifyT T;
    val params = Name.invent_names Name.context "x" Ts;
    val lhs = HOLogic.mk_random T size;
    val tc = HOLogic.mk_return Tm \<^typ>\<open>Random.seed\<close>
      (HOLogic.mk_valtermify_app extN params T);
    val rhs =
      HOLogic.mk_ST
        (map (fn (v, T') =>
          ((HOLogic.mk_random T' size, \<^typ>\<open>Random.seed\<close>), SOME (v, termifyT T'))) params)
        tc \<^typ>\<open>Random.seed\<close> (SOME Tm, \<^typ>\<open>Random.seed\<close>);
  in
    (lhs, rhs)
  end

fun mk_full_exhaustive_eq tyco vs extN Ts =
  let
    (* FIXME local i etc. *)
    val size = \<^term>\<open>i::natural\<close>;
    fun termifyT T = HOLogic.mk_prodT (T, \<^typ>\<open>unit \<Rightarrow> term\<close>);
    val T = Type (tyco, map TFree vs);
    val test_function = Free ("f", termifyT T --> \<^typ>\<open>(bool \<times> term list) option\<close>);
    val params = Name.invent_names Name.context "x" Ts;
    fun full_exhaustiveT T =
      (termifyT T --> \<^typ>\<open>(bool \<times> Code_Evaluation.term list) option\<close>) -->
        \<^typ>\<open>natural\<close> --> \<^typ>\<open>(bool \<times> Code_Evaluation.term list) option\<close>;
    fun mk_full_exhaustive T =
      Const (\<^const_name>\<open>Quickcheck_Exhaustive.full_exhaustive_class.full_exhaustive\<close>,
        full_exhaustiveT T);
    val lhs = mk_full_exhaustive T $ test_function $ size;
    val tc = test_function $ (HOLogic.mk_valtermify_app extN params T);
    val rhs = fold_rev (fn (v, T) => fn cont =>
        mk_full_exhaustive T $ (lambda (Free (v, termifyT T)) cont) $ size) params tc;
  in
    (lhs, rhs)
  end;

fun instantiate_sort_record (sort, mk_eq) tyco vs extN Ts thy =
  let
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_eq tyco vs extN Ts));
  in
    thy
    |> Class.instantiation ([tyco], vs, sort)
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition NONE [] [] ((Binding.concealed Binding.empty, []), eq))
    |> snd
    |> Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [])
  end;

fun ensure_sort_record (sort, mk_eq) ext_tyco vs extN Ts thy =
  let
    val algebra = Sign.classes_of thy;
    val has_inst = Sorts.has_instance algebra ext_tyco sort;
  in
    if has_inst then thy
    else
      (case Quickcheck_Common.perhaps_constrain thy (map (rpair sort) Ts) vs of
        SOME constrain =>
          instantiate_sort_record (sort, mk_eq) ext_tyco (map constrain vs) extN
            ((map o map_atyps) (fn TFree v => TFree (constrain v)) Ts) thy
      | NONE => thy)
  end;

fun add_code ext_tyco vs extT ext simps inject thy =
  if Config.get_global thy codegen then
    let
      val eq =
        HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (\<^const_name>\<open>HOL.equal\<close>, extT --> extT --> HOLogic.boolT),
           Const (\<^const_name>\<open>HOL.eq\<close>, extT --> extT --> HOLogic.boolT)));
      fun tac ctxt eq_def =
        Class.intro_classes_tac ctxt []
        THEN rewrite_goals_tac ctxt [Simpdata.mk_eq eq_def]
        THEN ALLGOALS (resolve_tac ctxt @{thms refl});
      fun mk_eq ctxt eq_def =
        rewrite_rule ctxt
          [Axclass.unoverload ctxt (Thm.symmetric (Simpdata.mk_eq eq_def))] inject;
      fun mk_eq_refl ctxt =
        @{thm equal_refl}
        |> Thm.instantiate
          (TVars.make [(\<^tvar>\<open>?'a::equal\<close>, Thm.ctyp_of ctxt (Logic.varifyT_global extT))], Vars.empty)
        |> Axclass.unoverload ctxt;
      val ensure_random_record = ensure_sort_record (\<^sort>\<open>random\<close>, mk_random_eq);
      val ensure_exhaustive_record =
        ensure_sort_record (\<^sort>\<open>full_exhaustive\<close>, mk_full_exhaustive_eq);
      fun add_code eq_def thy =
        let
          val ctxt = Proof_Context.init_global thy;
        in
          thy
          |> Code.declare_default_eqns_global [(mk_eq ctxt eq_def, true), (mk_eq_refl ctxt, false)]
        end;
    in
      thy
      |> Code.declare_datatype_global [ext]
      |> Code.declare_default_eqns_global (map (rpair true) simps)
      |> Class.instantiation ([ext_tyco], vs, [HOLogic.class_equal])
      |> `(fn lthy => Syntax.check_term lthy eq)
      |-> (fn eq => Specification.definition NONE [] [] (Binding.empty_atts, eq))
      |-> (fn (_, (_, eq_def)) =>
         Class.prove_instantiation_exit_result Morphism.thm tac eq_def)
      |-> add_code
      |> ensure_random_record ext_tyco vs (fst ext) (binder_types (snd ext))
      |> ensure_exhaustive_record ext_tyco vs (fst ext) (binder_types (snd ext))
    end
  else thy;

fun add_ctr_sugar ctr exhaust inject sel_thms =
  Ctr_Sugar.default_register_ctr_sugar_global (K true)
    {kind = Ctr_Sugar.Record, T = body_type (fastype_of ctr), ctrs = [ctr], casex = Term.dummy,
     discs = [], selss = [], exhaust = exhaust, nchotomy = Drule.dummy_thm, injects = [inject],
     distincts = [], case_thms = [], case_cong = Drule.dummy_thm, case_cong_weak = Drule.dummy_thm,
     case_distribs = [], split = Drule.dummy_thm, split_asm = Drule.dummy_thm, disc_defs = [],
     disc_thmss = [], discIs = [], disc_eq_cases = [], sel_defs = [], sel_thmss = [sel_thms],
     distinct_discsss = [], exhaust_discs = [], exhaust_sels = [], collapses = [], expands = [],
     split_sels = [], split_sel_asms = [], case_eq_ifs = []};

fun lhs_of_equation \<^Const_>\<open>Pure.eq _ for t _\<close> = t
  | lhs_of_equation \<^Const_>\<open>Trueprop for \<^Const_>\<open>HOL.eq _ for t _\<close>\<close> = t;

fun add_spec_rule rule =
  let val head = head_of (lhs_of_equation (Thm.prop_of rule))
  in Spec_Rules.add_global Binding.empty Spec_Rules.equational [head] [rule] end;

(* definition *)

fun definition overloaded (alphas, binding) parent (parents: parent_info list) raw_fields thy0 =
  let
    val ctxt0 = Proof_Context.init_global thy0;

    val prefix = Binding.name_of binding;
    val name = Sign.full_name thy0 binding;
    val full = Sign.full_name_path thy0 prefix;

    val bfields = map (fn (x, T, _) => (x, T)) raw_fields;
    val field_syntax = map #3 raw_fields;

    val parent_fields = maps #fields parents;
    val parent_chunks = map (length o #fields) parents;
    val parent_names = map fst parent_fields;
    val parent_types = map snd parent_fields;
    val parent_fields_len = length parent_fields;
    val parent_variants =
      Name.variant_list [moreN, rN, rN ^ "'", wN] (map Long_Name.base_name parent_names);
    val parent_vars = map2 (curry Free) parent_variants parent_types;
    val parent_len = length parents;

    val fields = map (apfst full) bfields;
    val names = map fst fields;
    val types = map snd fields;
    val alphas_fields = fold Term.add_tfreesT types [];
    val alphas_ext = inter (op =) alphas_fields alphas;
    val len = length fields;
    val variants =
      Name.variant_list (moreN :: rN :: (rN ^ "'") :: wN :: parent_variants)
        (map (Binding.name_of o fst) bfields);
    val vars = map2 (curry Free) variants types;
    val named_vars = names ~~ vars;
    val idxms = 0 upto len;

    val all_fields = parent_fields @ fields;
    val all_types = parent_types @ types;
    val all_variants = parent_variants @ variants;
    val all_vars = parent_vars @ vars;
    val all_named_vars = (parent_names ~~ parent_vars) @ named_vars;

    val zeta = (singleton (Name.variant_list (map #1 alphas)) "'z", \<^sort>\<open>type\<close>);
    val moreT = TFree zeta;
    val more = Free (moreN, moreT);
    val full_moreN = full (Binding.name moreN);
    val bfields_more = bfields @ [(Binding.name moreN, moreT)];
    val fields_more = fields @ [(full_moreN, moreT)];
    val named_vars_more = named_vars @ [(full_moreN, more)];
    val all_vars_more = all_vars @ [more];
    val all_named_vars_more = all_named_vars @ [(full_moreN, more)];


    (* 1st stage: ext_thy *)

    val extension_name = full binding;

    val ((ext, (ext_tyco, vs),
        extT, ext_induct, ext_inject, ext_surjective, ext_split, ext_def), ext_thy) =
      thy0
      |> Sign.qualified_path false binding
      |> extension_definition overloaded extension_name fields alphas_ext zeta moreT more vars;
    val ext_ctxt = Proof_Context.init_global ext_thy;

    val _ = timing_msg ext_ctxt "record preparing definitions";
    val Type extension_scheme = extT;
    val extension_name = unsuffix ext_typeN (fst extension_scheme);
    val extension = let val (n, Ts) = extension_scheme in (n, subst_last HOLogic.unitT Ts) end;
    val extension_names = map (unsuffix ext_typeN o fst o #extension) parents @ [extension_name];
    val extension_id = implode extension_names;

    fun rec_schemeT n = mk_recordT (map #extension (drop n parents)) extT;
    val rec_schemeT0 = rec_schemeT 0;

    fun recT n =
      let val (c, Ts) = extension in
        mk_recordT (map #extension (drop n parents))
          (Type (c, subst_last HOLogic.unitT Ts))
      end;
    val recT0 = recT 0;

    fun mk_rec args n =
      let
        val (args', more) = chop_last args;
        fun mk_ext' ((name, T), args) more = mk_ext (name, T) (args @ [more]);
        fun build Ts =
          fold_rev mk_ext' (drop n ((extension_names ~~ Ts) ~~ chunks parent_chunks args')) more;
      in
        if more = HOLogic.unit
        then build (map_range recT (parent_len + 1))
        else build (map_range rec_schemeT (parent_len + 1))
      end;

    val r_rec0 = mk_rec all_vars_more 0;
    val r_rec_unit0 = mk_rec (all_vars @ [HOLogic.unit]) 0;

    fun r n = Free (rN, rec_schemeT n);
    val r0 = r 0;
    fun r_unit n = Free (rN, recT n);
    val r_unit0 = r_unit 0;


    (* print translations *)

    val record_ext_type_abbr_tr's =
      let
        val trname = hd extension_names;
        val last_ext = unsuffix ext_typeN (fst extension);
      in [record_ext_type_abbr_tr' name alphas zeta last_ext rec_schemeT0 trname] end;

    val record_ext_type_tr's =
      let
        (*avoid conflict with record_type_abbr_tr's*)
        val trnames = if parent_len > 0 then [extension_name] else [];
      in map record_ext_type_tr' trnames end;

    val print_translation =
      map field_update_tr' (full_moreN :: names) @ [record_ext_tr' extension_name] @
      record_ext_type_tr's @ record_ext_type_abbr_tr's;


    (* prepare declarations *)

    val sel_decls = map (mk_selC rec_schemeT0 o apfst Binding.name_of) bfields_more;
    val upd_decls = map (mk_updC updateN rec_schemeT0 o apfst Binding.name_of) bfields_more;
    val make_decl = (makeN, all_types ---> recT0);
    val fields_decl = (fields_selN, types ---> Type extension);
    val extend_decl = (extendN, recT0 --> moreT --> rec_schemeT0);
    val truncate_decl = (truncateN, rec_schemeT0 --> recT0);


    (* prepare definitions *)

    val ext_defs = ext_def :: map #ext_def parents;

    (*Theorems from the iso_tuple intros.
      By unfolding ext_defs from r_rec0 we create a tree of constructor
      calls (many of them Pair, but others as well). The introduction
      rules for update_accessor_eq_assist can unify two different ways
      on these constructors. If we take the complete result sequence of
      running a the introduction tactic, we get one theorem for each upd/acc
      pair, from which we can derive the bodies of our selector and
      updator and their convs.*)
    val (accessor_thms, updator_thms, upd_acc_cong_assists) =
      timeit_msg ext_ctxt "record getting tree access/updates:" (fn () =>
        let
          val r_rec0_Vars =
            let
              (*pick variable indices of 1 to avoid possible variable
                collisions with existing variables in updacc_eq_triv*)
              fun to_Var (Free (c, T)) = Var ((c, 1), T);
            in mk_rec (map to_Var all_vars_more) 0 end;

          val init_thm =
            infer_instantiate ext_ctxt
              [(("v", 0), Thm.cterm_of ext_ctxt r_rec0),
               (("v'", 0), Thm.cterm_of ext_ctxt r_rec0_Vars)]
              updacc_eq_triv;
          val terminal =
            resolve_tac ext_ctxt [updacc_eq_idI] 1 THEN resolve_tac ext_ctxt [refl] 1;
          val tactic =
            simp_tac (put_simpset HOL_basic_ss ext_ctxt addsimps ext_defs) 1 THEN
            REPEAT (Iso_Tuple_Support.iso_tuple_intros_tac ext_ctxt 1 ORELSE terminal);
          val updaccs = Seq.list_of (tactic init_thm);
        in
          (updaccs RL [updacc_accessor_eqE],
           updaccs RL [updacc_updator_eqE],
           updaccs RL [updacc_cong_from_eq])
        end);

    fun lastN xs = drop parent_fields_len xs;

    (*selectors*)
    fun mk_sel_spec ((c, T), thm) =
      let
        val (acc $ arg, _) =
          HOLogic.dest_eq (HOLogic.dest_Trueprop (Envir.beta_eta_contract (Thm.concl_of thm)));
        val _ =
          if arg aconv r_rec0 then ()
          else raise TERM ("mk_sel_spec: different arg", [arg]);
      in
        Const (mk_selC rec_schemeT0 (c, T)) :== acc
      end;
    val sel_specs = map mk_sel_spec (fields_more ~~ lastN accessor_thms);

    (*updates*)
    fun mk_upd_spec ((c, T), thm) =
      let
        val (upd $ _ $ arg, _) =
          HOLogic.dest_eq (HOLogic.dest_Trueprop (Envir.beta_eta_contract (Thm.concl_of thm)));
        val _ =
          if arg aconv r_rec0 then ()
          else raise TERM ("mk_sel_spec: different arg", [arg]);
      in Const (mk_updC updateN rec_schemeT0 (c, T)) :== upd end;
    val upd_specs = map mk_upd_spec (fields_more ~~ lastN updator_thms);

    (*derived operations*)
    val make_spec =
      list_comb (Const (full (Binding.name makeN), all_types ---> recT0), all_vars) :==
        mk_rec (all_vars @ [HOLogic.unit]) 0;
    val fields_spec =
      list_comb (Const (full (Binding.name fields_selN), types ---> Type extension), vars) :==
        mk_rec (all_vars @ [HOLogic.unit]) parent_len;
    val extend_spec =
      Const (full (Binding.name extendN), recT0 --> moreT --> rec_schemeT0) $ r_unit0 $ more :==
        mk_rec ((map (mk_sel r_unit0) all_fields) @ [more]) 0;
    val truncate_spec =
      Const (full (Binding.name truncateN), rec_schemeT0 --> recT0) $ r0 :==
        mk_rec ((map (mk_sel r0) all_fields) @ [HOLogic.unit]) 0;


    (* 2st stage: defs_thy *)

    val (((sel_defs, upd_defs), derived_defs), defs_thy) =
      timeit_msg ext_ctxt "record trfuns/tyabbrs/selectors/updates/make/fields/extend/truncate defs:"
        (fn () =>
          ext_thy
          |> Sign.print_translation print_translation
          |> Sign.restore_naming thy0
          |> Typedecl.abbrev_global (binding, map #1 alphas, NoSyn) recT0 |> snd
          |> Typedecl.abbrev_global
            (Binding.suffix_name schemeN binding, map #1 (alphas @ [zeta]), NoSyn) rec_schemeT0
          |> snd
          |> Sign.qualified_path false binding
          |> fold (fn ((x, T), mx) => snd o Sign.declare_const_global ((Binding.name x, T), mx))
            (sel_decls ~~ (field_syntax @ [NoSyn]))
          |> fold (fn (x, T) => snd o Sign.declare_const_global ((Binding.name x, T), NoSyn))
            (upd_decls @ [make_decl, fields_decl, extend_decl, truncate_decl])
          |> (Global_Theory.add_defs false o
                map (Thm.no_attributes o apfst (Binding.concealed o Binding.name))) sel_specs
          ||>> (Global_Theory.add_defs false o
                map (Thm.no_attributes o apfst (Binding.concealed o Binding.name))) upd_specs
          ||>> (Global_Theory.add_defs false o
                map (Thm.no_attributes o apfst (Binding.concealed o Binding.name)))
            [make_spec, fields_spec, extend_spec, truncate_spec]);
    val defs_ctxt = Proof_Context.init_global defs_thy;

    (* prepare propositions *)
    val _ = timing_msg defs_ctxt "record preparing propositions";
    val P = Free (singleton (Name.variant_list all_variants) "P", rec_schemeT0 --> HOLogic.boolT);
    val C = Free (singleton (Name.variant_list all_variants) "C", HOLogic.boolT);
    val P_unit = Free (singleton (Name.variant_list all_variants) "P", recT0 --> HOLogic.boolT);

    (*selectors*)
    val sel_conv_props =
      map (fn (c, x as Free (_, T)) => mk_sel r_rec0 (c, T) === x) named_vars_more;

    (*updates*)
    fun mk_upd_prop i (c, T) =
      let
        val x' =
          Free (singleton (Name.variant_list all_variants) (Long_Name.base_name c ^ "'"), T --> T);
        val n = parent_fields_len + i;
        val args' = nth_map n (K (x' $ nth all_vars_more n)) all_vars_more;
      in mk_upd updateN c x' r_rec0 === mk_rec args' 0 end;
    val upd_conv_props = map2 mk_upd_prop idxms fields_more;

    (*induct*)
    val induct_scheme_prop =
      fold_rev Logic.all all_vars_more (Trueprop (P $ r_rec0)) ==> Trueprop (P $ r0);
    val induct_prop =
      (fold_rev Logic.all all_vars (Trueprop (P_unit $ r_rec_unit0)), Trueprop (P_unit $ r_unit0));

    (*surjective*)
    val surjective_prop =
      let val args = map (fn (c, Free (_, T)) => mk_sel r0 (c, T)) all_named_vars_more
      in r0 === mk_rec args 0 end;

    (*cases*)
    val cases_scheme_prop =
      (fold_rev Logic.all all_vars_more ((r0 === r_rec0) ==> Trueprop C), Trueprop C);

    val cases_prop =
      fold_rev Logic.all all_vars ((r_unit0 === r_rec_unit0) ==> Trueprop C) ==> Trueprop C;

    (*split*)
    val split_meta_prop =
      let
        val P = Free (singleton (Name.variant_list all_variants) "P", rec_schemeT0 --> propT);
      in
        Logic.mk_equals (Logic.all r0 (P $ r0), fold_rev Logic.all all_vars_more (P $ r_rec0))
      end;

    val split_object_prop =
      let val ALL = fold_rev (fn (v, T) => fn t => HOLogic.mk_all (v, T, t))
      in ALL [dest_Free r0] (P $ r0) === ALL (map dest_Free all_vars_more) (P $ r_rec0) end;

    val split_ex_prop =
      let val EX = fold_rev (fn (v, T) => fn t => HOLogic.mk_exists (v, T, t))
      in EX [dest_Free r0] (P $ r0) === EX (map dest_Free all_vars_more) (P $ r_rec0) end;

    (*equality*)
    val equality_prop =
      let
        val s' = Free (rN ^ "'", rec_schemeT0);
        fun mk_sel_eq (c, Free (_, T)) = mk_sel r0 (c, T) === mk_sel s' (c, T);
        val seleqs = map mk_sel_eq all_named_vars_more;
      in Logic.all r0 (Logic.all s' (Logic.list_implies (seleqs, r0 === s'))) end;


    (* 3rd stage: thms_thy *)

    val record_ss = get_simpset defs_thy;
    val sel_upd_ctxt =
      put_simpset record_ss defs_ctxt
        addsimps (sel_defs @ accessor_thms @ upd_defs @ updator_thms);

    val (sel_convs, upd_convs) =
      timeit_msg defs_ctxt "record sel_convs/upd_convs proof:" (fn () =>
        grouped 10 Par_List.map (fn prop =>
            Goal.prove_sorry_global defs_thy [] [] prop
              (fn _ => ALLGOALS (asm_full_simp_tac sel_upd_ctxt)))
          (sel_conv_props @ upd_conv_props))
      |> chop (length sel_conv_props);

    val (fold_congs, unfold_congs) = timeit_msg defs_ctxt "record upd fold/unfold congs:" (fn () =>
      let
        val symdefs = map Thm.symmetric (sel_defs @ upd_defs);
        val fold_ctxt = put_simpset HOL_basic_ss defs_ctxt addsimps symdefs;
        val ua_congs = map (Drule.export_without_context o simplify fold_ctxt) upd_acc_cong_assists;
      in (ua_congs RL [updacc_foldE], ua_congs RL [updacc_unfoldE]) end);

    val parent_induct = Option.map #induct_scheme (try List.last parents);

    val induct_scheme = timeit_msg defs_ctxt "record induct_scheme proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] induct_scheme_prop
        (fn {context = ctxt', ...} =>
          EVERY
           [case parent_induct of NONE => all_tac | SOME ind => try_param_tac ctxt' rN ind 1,
            try_param_tac ctxt' rN ext_induct 1,
            asm_simp_tac (put_simpset HOL_basic_ss ctxt') 1]));

    val induct = timeit_msg defs_ctxt "record induct proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [#1 induct_prop] (#2 induct_prop)
        (fn {context = ctxt', prems, ...} =>
          try_param_tac ctxt' rN induct_scheme 1
          THEN try_param_tac ctxt' "more" @{thm unit.induct} 1
          THEN resolve_tac ctxt' prems 1));

    val surjective = timeit_msg defs_ctxt "record surjective proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] surjective_prop
        (fn {context = ctxt', ...} =>
          EVERY
           [resolve_tac ctxt' [surject_assist_idE] 1,
            simp_tac (put_simpset HOL_basic_ss ctxt' addsimps ext_defs) 1,
            REPEAT
              (Iso_Tuple_Support.iso_tuple_intros_tac ctxt' 1 ORELSE
                (resolve_tac ctxt' [surject_assistI] 1 THEN
                  simp_tac (put_simpset (get_sel_upd_defs defs_thy) ctxt'
                    addsimps (sel_defs @ @{thms o_assoc id_apply id_o o_id})) 1))]));

    val cases_scheme = timeit_msg defs_ctxt "record cases_scheme proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [#1 cases_scheme_prop] (#2 cases_scheme_prop)
        (fn {context = ctxt', prems, ...} =>
          resolve_tac ctxt' prems 1 THEN
          resolve_tac ctxt' [surjective] 1));

    val cases = timeit_msg defs_ctxt "record cases proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] cases_prop
        (fn {context = ctxt', ...} =>
          try_param_tac ctxt' rN cases_scheme 1 THEN
          ALLGOALS (asm_full_simp_tac
            (put_simpset HOL_basic_ss ctxt' addsimps @{thms unit_all_eq1}))));

    val split_meta = timeit_msg defs_ctxt "record split_meta proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] split_meta_prop
        (fn {context = ctxt', ...} =>
          EVERY1
           [resolve_tac ctxt' @{thms equal_intr_rule}, Goal.norm_hhf_tac ctxt',
            eresolve_tac ctxt' @{thms meta_allE}, assume_tac ctxt',
            resolve_tac ctxt' [@{thm prop_subst} OF [surjective]],
            REPEAT o eresolve_tac ctxt' @{thms meta_allE}, assume_tac ctxt']));

    val split_object = timeit_msg defs_ctxt "record split_object proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] split_object_prop
        (fn {context = ctxt', ...} =>
          resolve_tac ctxt' [@{lemma "Trueprop A \<equiv> Trueprop B \<Longrightarrow> A = B" by (rule iffI) unfold}] 1 THEN
          rewrite_goals_tac ctxt' @{thms atomize_all [symmetric]} THEN
          resolve_tac ctxt' [split_meta] 1));

    val split_ex = timeit_msg defs_ctxt "record split_ex proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] split_ex_prop
        (fn {context = ctxt', ...} =>
          simp_tac
            (put_simpset HOL_basic_ss ctxt' addsimps
              (@{lemma "\<exists>x. P x \<equiv> \<not> (\<forall>x. \<not> P x)" by simp} ::
                @{thms not_not Not_eq_iff})) 1 THEN
          resolve_tac ctxt' [split_object] 1));

    val equality = timeit_msg defs_ctxt "record equality proof:" (fn () =>
      Goal.prove_sorry_global defs_thy [] [] equality_prop
        (fn {context = ctxt', ...} =>
          asm_full_simp_tac (put_simpset record_ss ctxt' addsimps (split_meta :: sel_convs)) 1));

    val ([(_, sel_convs'), (_, upd_convs'), (_, sel_defs'), (_, upd_defs'),
          (_, fold_congs'), (_, unfold_congs'),
          (_, splits' as [split_meta', split_object', split_ex']), (_, derived_defs'),
          (_, [surjective']), (_, [equality']), (_, [induct_scheme']), (_, [induct']),
          (_, [cases_scheme']), (_, [cases'])], thms_thy) = defs_thy
      |> Code.declare_default_eqns_global (map (rpair true) derived_defs)
      |> Global_Theory.note_thmss ""
       [((Binding.name "select_convs", []), [(sel_convs, [])]),
        ((Binding.name "update_convs", []), [(upd_convs, [])]),
        ((Binding.name "select_defs", []), [(sel_defs, [])]),
        ((Binding.name "update_defs", []), [(upd_defs, [])]),
        ((Binding.name "fold_congs", []), [(fold_congs, [])]),
        ((Binding.name "unfold_congs", []), [(unfold_congs, [])]),
        ((Binding.name "splits", []), [([split_meta, split_object, split_ex], [])]),
        ((Binding.name "defs", []), [(derived_defs, [])]),
        ((Binding.name "surjective", []), [([surjective], [])]),
        ((Binding.name "equality", []), [([equality], [])]),
        ((Binding.name "induct_scheme", induct_type_global (suffix schemeN name)),
          [([induct_scheme], [])]),
        ((Binding.name "induct", induct_type_global name), [([induct], [])]),
        ((Binding.name "cases_scheme", cases_type_global (suffix schemeN name)),
          [([cases_scheme], [])]),
        ((Binding.name "cases", cases_type_global name), [([cases], [])])];

    val sel_upd_simps = sel_convs' @ upd_convs';
    val sel_upd_defs = sel_defs' @ upd_defs';
    val depth = parent_len + 1;

    val ([(_, simps'), (_, iffs')], thms_thy') = thms_thy
      |> Global_Theory.note_thmss ""
          [((Binding.name "simps", [Simplifier.simp_add]), [(sel_upd_simps, [])]),
           ((Binding.name "iffs", [iff_add]), [([ext_inject], [])])];

    val info =
      make_info alphas parent fields extension
        ext_induct ext_inject ext_surjective ext_split ext_def
        sel_convs' upd_convs' sel_defs' upd_defs' fold_congs' unfold_congs' splits' derived_defs'
        surjective' equality' induct_scheme' induct' cases_scheme' cases' simps' iffs';

    val final_thy =
      thms_thy'
      |> put_record name info
      |> put_sel_upd names full_moreN depth sel_upd_simps sel_upd_defs
      |> add_equalities extension_id equality'
      |> add_extinjects ext_inject
      |> add_extsplit extension_name ext_split
      |> add_splits extension_id (split_meta', split_object', split_ex', induct_scheme')
      |> add_extfields extension_name (fields @ [(full_moreN, moreT)])
      |> add_fieldext (extension_name, snd extension) names
      |> add_code ext_tyco vs extT ext simps' ext_inject
      |> add_ctr_sugar (Const ext) cases_scheme' ext_inject sel_convs'
      |> fold add_spec_rule (sel_convs' @ upd_convs' @ derived_defs')
      |> Sign.restore_naming thy0;

  in final_thy end;


(* add_record *)

local

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn (_, raw_T, _) => raw_T) raw_fields);
    val fields = map2 (fn (x, _, mx) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, ctxt') end;

in

fun add_record overloaded (params, binding) raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    fun cert_typ T = Type.no_tvars (Proof_Context.cert_typ ctxt T)
      handle TYPE (msg, _, _) => error msg;


    (* specification *)

    val parent = Option.map (apfst (map cert_typ)) raw_parent
      handle ERROR msg =>
        cat_error msg ("The error(s) above occurred in parent record specification");
    val parent_args = (case parent of SOME (Ts, _) => Ts | NONE => []);
    val parents = get_parent_info thy parent;

    val bfields =
      raw_fields |> map (fn (x, raw_T, mx) => (x, cert_typ raw_T, mx)
        handle ERROR msg =>
          cat_error msg ("The error(s) above occurred in record field " ^ Binding.print x));


    (* errors *)

    val name = Sign.full_name thy binding;
    val err_dup_record =
      if is_none (get_info thy name) then []
      else ["Duplicate definition of record " ^ quote name];

    val spec_frees = fold Term.add_tfreesT (parent_args @ map #2 bfields) [];
    val err_extra_frees =
      (case subtract (op =) params spec_frees of
        [] => []
      | extras => ["Extra free type variable(s) " ^
          commas (map (Syntax.string_of_typ ctxt o TFree) extras)]);

    val err_no_fields = if null bfields then ["No fields present"] else [];

    val err_dup_fields =
      (case duplicates Binding.eq_name (map #1 bfields) of
        [] => []
      | dups => ["Duplicate field(s) " ^ commas (map Binding.print dups)]);

    val err_bad_fields =
      if forall (not_equal moreN o Binding.name_of o #1) bfields then []
      else ["Illegal field name " ^ quote moreN];

    val errs =
      err_dup_record @ err_extra_frees @ err_no_fields @ err_dup_fields @ err_bad_fields;
    val _ = if null errs then () else error (cat_lines errs);
  in
    thy |> definition overloaded (params, binding) parent parents bfields
  end
  handle ERROR msg => cat_error msg ("Failed to define record " ^ Binding.print binding);

fun add_record_cmd overloaded (raw_params, binding) raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    val params' = map (Proof_Context.check_tfree ctxt3) params;
  in thy |> add_record overloaded (params', binding) parent fields end;

end;


(* printing *)

local

fun the_parent_recT (Type (parent, [Type (_, [unit as Type (_,[])])])) = Type (parent, [unit])
  | the_parent_recT (Type (extT, [T])) = Type (extT, [the_parent_recT T])
  | the_parent_recT T = raise TYPE ("Not a unit record scheme with parent: ", [T], [])

in

fun pretty_recT ctxt typ =
  let
    val thy = Proof_Context.theory_of ctxt
    val (fs, (_, moreT)) = get_recT_fields thy typ
    val _ = if moreT = HOLogic.unitT then () else raise TYPE ("Not a unit record scheme: ", [typ], [])
    val parent = if length (dest_recTs typ) >= 2 then SOME (the_parent_recT typ) else NONE
    val pfs = case parent of SOME p => fst (get_recT_fields thy p) | NONE => []
    val fs' = drop (length pfs) fs
    fun pretty_field (name, typ) = Pretty.block [
          Syntax.pretty_term ctxt (Const (name, typ)),
          Pretty.brk 1,
          Pretty.str "::",
          Pretty.brk 1,
          Syntax.pretty_typ ctxt typ
        ]
  in
    Pretty.block (Library.separate (Pretty.brk 1)
      ([Pretty.keyword1 "record", Syntax.pretty_typ ctxt typ, Pretty.str "="] @
        (case parent of
          SOME p => [Syntax.pretty_typ ctxt p, Pretty.str "+"]
        | NONE => [])) @
      Pretty.fbrk ::
      Pretty.fbreaks (map pretty_field fs'))
  end

end

fun string_of_record ctxt s =
  let
    val T = Syntax.read_typ ctxt s
  in
    Pretty.string_of (pretty_recT ctxt T)
      handle TYPE _ => error ("Unknown record: " ^ Syntax.string_of_typ ctxt T)
  end

val print_record =
  let
    fun print_item string_of (modes, arg) = Toplevel.keep (fn state =>
         Print_Mode.with_modes modes (fn () => Output.writeln (string_of state arg)) ());
  in print_item (string_of_record o Toplevel.context_of) end


(* outer syntax *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>record\<close> "define extensible record"
    (Parse_Spec.overloaded -- (Parse.type_args_constrained -- Parse.binding) --
      (\<^keyword>\<open>=\<close> |-- Scan.option (Parse.typ --| \<^keyword>\<open>+\<close>) --
        Scan.repeat1 Parse.const_binding)
    >> (fn ((overloaded, x), (y, z)) =>
        Toplevel.theory (add_record_cmd {overloaded = overloaded} x y z)));

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) []

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_record\<close> "print record definiton"
    (opt_modes -- Parse.typ >> print_record);

end
