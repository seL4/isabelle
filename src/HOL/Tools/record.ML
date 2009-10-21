(*  Title:      HOL/Tools/record.ML
    Author:     Wolfgang Naraschewski, TU Muenchen
    Author:     Markus Wenzel, TU Muenchen
    Author:     Norbert Schirmer, TU Muenchen
    Author:     Thomas Sewell, NICTA

Extensible records with structural subtyping.
*)

signature BASIC_RECORD =
sig
  val record_simproc: simproc
  val record_eq_simproc: simproc
  val record_upd_simproc: simproc
  val record_split_simproc: (term -> int) -> simproc
  val record_ex_sel_eq_simproc: simproc
  val record_split_tac: int -> tactic
  val record_split_simp_tac: thm list -> (term -> int) -> int -> tactic
  val record_split_name: string
  val record_split_wrapper: string * wrapper
  val print_record_type_abbr: bool Unsynchronized.ref
  val print_record_type_as_fields: bool Unsynchronized.ref
end;

signature RECORD =
sig
  include BASIC_RECORD
  val timing: bool Unsynchronized.ref
  val updateN: string
  val ext_typeN: string
  val extN: string
  val makeN: string
  val moreN: string
  val last_extT: typ -> (string * typ list) option
  val dest_recTs: typ -> (string * typ list) list
  val get_extT_fields: theory -> typ -> (string * typ) list * (string * typ)
  val get_recT_fields: theory -> typ -> (string * typ) list * (string * typ)
  val get_parent: theory -> string -> (typ list * string) option
  val get_extension: theory -> string -> (string * typ list) option
  val get_extinjects: theory -> thm list
  val get_simpset: theory -> simpset
  val print_records: theory -> unit
  val read_typ: Proof.context -> string -> (string * sort) list -> typ * (string * sort) list
  val cert_typ: Proof.context -> typ -> (string * sort) list -> typ * (string * sort) list
  val add_record: bool -> string list * string -> string option -> (string * string * mixfix) list
    -> theory -> theory
  val add_record_i: bool -> string list * string -> (typ list * string) option
    -> (string * typ * mixfix) list -> theory -> theory
  val setup: theory -> theory
end;


signature ISTUPLE_SUPPORT =
sig
  val add_istuple_type: bstring * string list -> typ * typ -> theory -> (term * term) * theory
  val mk_cons_tuple: term * term -> term
  val dest_cons_tuple: term -> term * term
  val istuple_intros_tac: int -> tactic
  val named_cterm_instantiate: (string * cterm) list -> thm -> thm
end;

structure IsTupleSupport: ISTUPLE_SUPPORT =
struct

val isomN = "_TupleIsom";

val istuple_intro = @{thm isomorphic_tuple_intro};
val istuple_intros = Tactic.build_net @{thms isomorphic_tuple.intros};

val tuple_istuple = (@{const_name tuple_istuple}, @{thm tuple_istuple});

fun named_cterm_instantiate values thm =
  let
    fun match name ((name', _), _) = name = name'
      | match name _ = false;
    fun getvar name =
      (case find_first (match name) (Term.add_vars (prop_of thm) []) of
        SOME var => cterm_of (theory_of_thm thm) (Var var)
      | NONE => raise THM ("named_cterm_instantiate: " ^ name, 0, [thm]));
  in
    cterm_instantiate (map (apfst getvar) values) thm
  end;

structure IsTupleThms = TheoryDataFun
(
  type T = thm Symtab.table;
  val empty = Symtab.make [tuple_istuple];
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge Thm.eq_thm_prop;
);

fun do_typedef name repT alphas thy =
  let
    fun get_thms thy name =
      let
        val SOME {Rep_inject = rep_inject, Abs_name = absN, abs_type = absT,
          Abs_inverse = abs_inverse, ...} = Typedef.get_info thy name;
        val rewrite_rule =
          MetaSimplifier.rewrite_rule [@{thm istuple_UNIV_I}, @{thm istuple_True_simp}];
      in
        (map rewrite_rule [rep_inject, abs_inverse], Const (absN, repT --> absT), absT)
      end;
  in
    thy
    |> Typecopy.typecopy (Binding.name name, alphas) repT NONE
    |-> (fn (name, _) => `(fn thy => get_thms thy name))
  end;

fun mk_cons_tuple (left, right) =
  let
    val (leftT, rightT) = (fastype_of left, fastype_of right);
    val prodT = HOLogic.mk_prodT (leftT, rightT);
    val isomT = Type (@{type_name tuple_isomorphism}, [prodT, leftT, rightT]);
  in
    Const (@{const_name istuple_cons}, isomT --> leftT --> rightT --> prodT) $
      Const (fst tuple_istuple, isomT) $ left $ right
  end;

fun dest_cons_tuple (Const (@{const_name istuple_cons}, _) $ Const _ $ t $ u) = (t, u)
  | dest_cons_tuple t = raise TERM ("dest_cons_tuple", [t]);

fun add_istuple_type (name, alphas) (leftT, rightT) thy =
  let
    val repT = HOLogic.mk_prodT (leftT, rightT);

    val (([rep_inject, abs_inverse], absC, absT), typ_thy) =
      thy
      |> do_typedef name repT alphas
      ||> Sign.add_path name;

    (*construct a type and body for the isomorphism constant by
      instantiating the theorem to which the definition will be applied*)
    val intro_inst =
      rep_inject RS named_cterm_instantiate [("abst", cterm_of typ_thy absC)] istuple_intro;
    val (_, body) = Logic.dest_equals (List.last (prems_of intro_inst));
    val isomT = fastype_of body;
    val isom_bind = Binding.name (name ^ isomN);
    val isom_name = Sign.full_name typ_thy isom_bind;
    val isom = Const (isom_name, isomT);
    val isom_spec = (Thm.def_name (name ^ isomN), Logic.mk_equals (isom, body));

    val ([isom_def], cdef_thy) =
      typ_thy
      |> Sign.add_consts_i [Syntax.no_syn (isom_bind, isomT)]
      |> PureThy.add_defs false [Thm.no_attributes (apfst Binding.name isom_spec)];

    val istuple = isom_def RS (abs_inverse RS (rep_inject RS istuple_intro));
    val cons = Const (@{const_name istuple_cons}, isomT --> leftT --> rightT --> absT);

    val thm_thy =
      cdef_thy
      |> IsTupleThms.map (Symtab.insert Thm.eq_thm_prop (isom_name, istuple))
      |> Sign.parent_path;
  in
    ((isom, cons $ isom), thm_thy)
  end;

val istuple_intros_tac = resolve_from_net_tac istuple_intros THEN'
  CSUBGOAL (fn (cgoal, i) =>
    let
      val thy = Thm.theory_of_cterm cgoal;
      val goal = Thm.term_of cgoal;

      val isthms = IsTupleThms.get thy;
      fun err s t = raise TERM ("istuple_intros_tac: " ^ s, [t]);

      val goal' = Envir.beta_eta_contract goal;
      val is =
        (case goal' of
          Const (@{const_name Trueprop}, _) $
            (Const (@{const_name isomorphic_tuple}, _) $ Const is) => is
        | _ => err "unexpected goal format" goal');
      val isthm =
        (case Symtab.lookup isthms (#1 is) of
          SOME isthm => isthm
        | NONE => err "no thm found for constant" (Const is));
    in rtac isthm i end);

end;


structure Record: RECORD =
struct

val eq_reflection = @{thm eq_reflection};
val atomize_all = @{thm HOL.atomize_all};
val atomize_imp = @{thm HOL.atomize_imp};
val meta_allE = @{thm Pure.meta_allE};
val prop_subst = @{thm prop_subst};
val K_record_comp = @{thm K_record_comp};
val K_comp_convs = [@{thm o_apply}, K_record_comp]
val o_assoc = @{thm o_assoc};
val id_apply = @{thm id_apply};
val id_o_apps = [@{thm id_apply}, @{thm id_o}, @{thm o_id}];
val Not_eq_iff = @{thm Not_eq_iff};

val refl_conj_eq = @{thm refl_conj_eq};

val surject_assistI = @{thm "istuple_surjective_proof_assistI"};
val surject_assist_idE = @{thm "istuple_surjective_proof_assist_idE"};

val updacc_accessor_eqE = @{thm "update_accessor_accessor_eqE"};
val updacc_updator_eqE = @{thm "update_accessor_updator_eqE"};
val updacc_eq_idI = @{thm "istuple_update_accessor_eq_assist_idI"};
val updacc_eq_triv = @{thm "istuple_update_accessor_eq_assist_triv"};

val updacc_foldE = @{thm "update_accessor_congruence_foldE"};
val updacc_unfoldE = @{thm "update_accessor_congruence_unfoldE"};
val updacc_noopE = @{thm "update_accessor_noopE"};
val updacc_noop_compE = @{thm "update_accessor_noop_compE"};
val updacc_cong_idI = @{thm "update_accessor_cong_assist_idI"};
val updacc_cong_triv = @{thm "update_accessor_cong_assist_triv"};
val updacc_cong_from_eq = @{thm "istuple_update_accessor_cong_from_eq"};

val o_eq_dest = @{thm o_eq_dest};
val o_eq_id_dest = @{thm o_eq_id_dest};
val o_eq_dest_lhs = @{thm o_eq_dest_lhs};



(** name components **)

val rN = "r";
val wN = "w";
val moreN = "more";
val schemeN = "_scheme";
val ext_typeN = "_ext_type";
val inner_typeN = "_inner_type";
val extN ="_ext";
val updateN = "_update";
val makeN = "make";
val fields_selN = "fields";
val extendN = "extend";
val truncateN = "truncate";



(*** utilities ***)

fun but_last xs = fst (split_last xs);

fun varifyT midx =
  let fun varify (a, S) = TVar ((a, midx + 1), S);
  in map_type_tfree varify end;


(* timing *)

val timing = Unsynchronized.ref false;
fun timeit_msg s x = if ! timing then (warning s; timeit x) else x ();
fun timing_msg s = if ! timing then warning s else ();


(* syntax *)

val Trueprop = HOLogic.mk_Trueprop;
fun All xs t = Term.list_all_free (xs, t);

infix 9 $$;
infix 0 :== ===;
infixr 0 ==>;

val op $$ = Term.list_comb;
val op :== = PrimitiveDefs.mk_defpair;
val op === = Trueprop o HOLogic.mk_eq;
val op ==> = Logic.mk_implies;


(* constructor *)

fun mk_extC (name, T) Ts = (suffix extN name, Ts ---> T);

fun mk_ext (name, T) ts =
  let val Ts = map fastype_of ts
  in list_comb (Const (mk_extC (name, T) Ts), ts) end;


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
    val rTs' = if i < 0 then rTs else Library.take (i, rTs);
  in implode (map #1 rTs') end;



(*** extend theory by record definition ***)

(** record info **)

(* type record_info and parent_info *)

type record_info =
 {args: (string * sort) list,
  parent: (typ list * string) option,
  fields: (string * typ) list,
  extension: (string * typ list),
  induct: thm,
  extdef: thm};

fun make_record_info args parent fields extension induct extdef =
 {args = args, parent = parent, fields = fields, extension = extension,
  induct = induct, extdef = extdef}: record_info;


type parent_info =
 {name: string,
  fields: (string * typ) list,
  extension: (string * typ list),
  induct: thm,
  extdef: thm};

fun make_parent_info name fields extension induct extdef =
 {name = name, fields = fields, extension = extension,
  induct = induct, extdef = extdef}: parent_info;


(* theory data *)

type record_data =
 {records: record_info Symtab.table,
  sel_upd:
   {selectors: (int * bool) Symtab.table,
    updates: string Symtab.table,
    simpset: Simplifier.simpset,
    defset: Simplifier.simpset,
    foldcong: Simplifier.simpset,
    unfoldcong: Simplifier.simpset},
  equalities: thm Symtab.table,
  extinjects: thm list,
  extsplit: thm Symtab.table,  (*maps extension name to split rule*)
  splits: (thm * thm * thm * thm) Symtab.table,  (*!!, !, EX - split-equalities, induct rule*)
  extfields: (string * typ) list Symtab.table,  (*maps extension to its fields*)
  fieldext: (string * typ list) Symtab.table};  (*maps field to its extension*)

fun make_record_data
    records sel_upd equalities extinjects extsplit splits extfields fieldext =
 {records = records, sel_upd = sel_upd,
  equalities = equalities, extinjects=extinjects, extsplit = extsplit, splits = splits,
  extfields = extfields, fieldext = fieldext }: record_data;

structure RecordsData = TheoryDataFun
(
  type T = record_data;
  val empty =
    make_record_data Symtab.empty
      {selectors = Symtab.empty, updates = Symtab.empty,
          simpset = HOL_basic_ss, defset = HOL_basic_ss,
          foldcong = HOL_basic_ss, unfoldcong = HOL_basic_ss}
       Symtab.empty [] Symtab.empty Symtab.empty Symtab.empty Symtab.empty;

  val copy = I;
  val extend = I;
  fun merge _
   ({records = recs1,
     sel_upd =
      {selectors = sels1, updates = upds1,
       simpset = ss1, defset = ds1,
       foldcong = fc1, unfoldcong = uc1},
     equalities = equalities1,
     extinjects = extinjects1,
     extsplit = extsplit1,
     splits = splits1,
     extfields = extfields1,
     fieldext = fieldext1},
    {records = recs2,
     sel_upd =
      {selectors = sels2, updates = upds2,
       simpset = ss2, defset = ds2,
       foldcong = fc2, unfoldcong = uc2},
     equalities = equalities2,
     extinjects = extinjects2,
     extsplit = extsplit2,
     splits = splits2,
     extfields = extfields2,
     fieldext = fieldext2}) =
    make_record_data
      (Symtab.merge (K true) (recs1, recs2))
      {selectors = Symtab.merge (K true) (sels1, sels2),
        updates = Symtab.merge (K true) (upds1, upds2),
        simpset = Simplifier.merge_ss (ss1, ss2),
        defset = Simplifier.merge_ss (ds1, ds2),
        foldcong = Simplifier.merge_ss (fc1, fc2),
        unfoldcong = Simplifier.merge_ss (uc1, uc2)}
      (Symtab.merge Thm.eq_thm_prop (equalities1, equalities2))
      (Library.merge Thm.eq_thm_prop (extinjects1, extinjects2))
      (Symtab.merge Thm.eq_thm_prop (extsplit1, extsplit2))
      (Symtab.merge (fn ((a, b, c, d), (w, x, y, z)) =>
          Thm.eq_thm (a, w) andalso Thm.eq_thm (b, x) andalso
          Thm.eq_thm (c, y) andalso Thm.eq_thm (d, z)) (splits1, splits2))
      (Symtab.merge (K true) (extfields1, extfields2))
      (Symtab.merge (K true) (fieldext1, fieldext2));
);

fun print_records thy =
  let
    val {records = recs, ...} = RecordsData.get thy;
    val prt_typ = Syntax.pretty_typ_global thy;

    fun pretty_parent NONE = []
      | pretty_parent (SOME (Ts, name)) =
          [Pretty.block [prt_typ (Type (name, Ts)), Pretty.str " +"]];

    fun pretty_field (c, T) = Pretty.block
      [Pretty.str (Sign.extern_const thy c), Pretty.str " ::",
        Pretty.brk 1, Pretty.quote (prt_typ T)];

    fun pretty_record (name, {args, parent, fields, ...}: record_info) =
      Pretty.block (Pretty.fbreaks (Pretty.block
        [prt_typ (Type (name, map TFree args)), Pretty.str " = "] ::
        pretty_parent parent @ map pretty_field fields));
  in map pretty_record (Symtab.dest recs) |> Pretty.chunks |> Pretty.writeln end;


(* access 'records' *)

val get_record = Symtab.lookup o #records o RecordsData.get;

fun put_record name info thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val data = make_record_data (Symtab.update (name, info) records)
      sel_upd equalities extinjects extsplit splits extfields fieldext;
  in RecordsData.put data thy end;


(* access 'sel_upd' *)

val get_sel_upd = #sel_upd o RecordsData.get;

val is_selector = Symtab.defined o #selectors o get_sel_upd;
val get_updates = Symtab.lookup o #updates o get_sel_upd;
fun get_ss_with_context getss thy = Simplifier.theory_context thy (getss (get_sel_upd thy));

val get_simpset = get_ss_with_context #simpset;
val get_sel_upd_defs = get_ss_with_context #defset;

fun get_update_details u thy =
  let val sel_upd = get_sel_upd thy in
    (case Symtab.lookup (#updates sel_upd) u of
      SOME s =>
        let val SOME (dep, ismore) = Symtab.lookup (#selectors sel_upd) s
        in SOME (s, dep, ismore) end
    | NONE => NONE)
  end;

fun put_sel_upd names more depth simps defs (folds, unfolds) thy =
  let
    val all = names @ [more];
    val sels = map (rpair (depth, false)) names @ [(more, (depth, true))];
    val upds = map (suffix updateN) all ~~ all;

    val {records, sel_upd = {selectors, updates, simpset, defset, foldcong, unfoldcong},
      equalities, extinjects, extsplit, splits, extfields, fieldext} = RecordsData.get thy;
    val data = make_record_data records
      {selectors = fold Symtab.update_new sels selectors,
        updates = fold Symtab.update_new upds updates,
        simpset = Simplifier.addsimps (simpset, simps),
        defset = Simplifier.addsimps (defset, defs),
        foldcong = foldcong addcongs folds,
        unfoldcong = unfoldcong addcongs unfolds}
       equalities extinjects extsplit splits extfields fieldext;
  in RecordsData.put data thy end;


(* access 'equalities' *)

fun add_record_equalities name thm thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val data = make_record_data records sel_upd
      (Symtab.update_new (name, thm) equalities) extinjects extsplit splits extfields fieldext;
  in RecordsData.put data thy end;

val get_equalities = Symtab.lookup o #equalities o RecordsData.get;


(* access 'extinjects' *)

fun add_extinjects thm thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val data =
      make_record_data records sel_upd equalities (insert Thm.eq_thm_prop thm extinjects)
        extsplit splits extfields fieldext;
  in RecordsData.put data thy end;

val get_extinjects = rev o #extinjects o RecordsData.get;


(* access 'extsplit' *)

fun add_extsplit name thm thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val data = make_record_data records sel_upd
      equalities extinjects (Symtab.update_new (name, thm) extsplit) splits
      extfields fieldext;
  in RecordsData.put data thy end;


(* access 'splits' *)

fun add_record_splits name thmP thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val data = make_record_data records sel_upd
      equalities extinjects extsplit (Symtab.update_new (name, thmP) splits)
      extfields fieldext;
  in RecordsData.put data thy end;

val get_splits = Symtab.lookup o #splits o RecordsData.get;


(* parent/extension of named record *)

val get_parent = (Option.join o Option.map #parent) oo (Symtab.lookup o #records o RecordsData.get);
val get_extension = Option.map #extension oo (Symtab.lookup o #records o RecordsData.get);


(* access 'extfields' *)

fun add_extfields name fields thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val data =
      make_record_data records sel_upd
        equalities extinjects extsplit splits
        (Symtab.update_new (name, fields) extfields) fieldext;
  in RecordsData.put data thy end;

val get_extfields = Symtab.lookup o #extfields o RecordsData.get;

fun get_extT_fields thy T =
  let
    val ((name, Ts), moreT) = dest_recT T;
    val recname =
      let val (nm :: _ :: rst) = rev (Long_Name.explode name)   (* FIXME !? *)
      in Long_Name.implode (rev (nm :: rst)) end;
    val midx = maxidx_of_typs (moreT :: Ts);
    val varifyT = varifyT midx;
    val {records, extfields, ...} = RecordsData.get thy;
    val (flds, (more, _)) = split_last (Symtab.lookup_list extfields name);
    val args = map varifyT (snd (#extension (the (Symtab.lookup records recname))));

    val subst = fold (Sign.typ_match thy) (but_last args ~~ but_last Ts) (Vartab.empty);
    val flds' = map (apsnd ((Envir.norm_type subst) o varifyT)) flds;
  in (flds', (more, moreT)) end;

fun get_recT_fields thy T =
  let
    val (root_flds, (root_more, root_moreT)) = get_extT_fields thy T;
    val (rest_flds, rest_more) =
      if is_recT root_moreT then get_recT_fields thy root_moreT
      else ([], (root_more, root_moreT));
  in (root_flds @ rest_flds, rest_more) end;


(* access 'fieldext' *)

fun add_fieldext extname_types fields thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
      RecordsData.get thy;
    val fieldext' =
      fold (fn field => Symtab.update_new (field, extname_types)) fields fieldext;
    val data =
      make_record_data records sel_upd equalities extinjects
        extsplit splits extfields fieldext';
  in RecordsData.put data thy end;

val get_fieldext = Symtab.lookup o #fieldext o RecordsData.get;


(* parent records *)

fun add_parents _ NONE parents = parents
  | add_parents thy (SOME (types, name)) parents =
      let
        fun err msg = error (msg ^ " parent record " ^ quote name);

        val {args, parent, fields, extension, induct, extdef} =
          (case get_record thy name of SOME info => info | NONE => err "Unknown");
        val _ = if length types <> length args then err "Bad number of arguments for" else ();

        fun bad_inst ((x, S), T) =
          if Sign.of_sort thy (T, S) then NONE else SOME x
        val bads = map_filter bad_inst (args ~~ types);
        val _ = null bads orelse err ("Ill-sorted instantiation of " ^ commas bads ^ " in");

        val inst = map fst args ~~ types;
        val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
        val parent' = Option.map (apfst (map subst)) parent;
        val fields' = map (apsnd subst) fields;
        val extension' = apsnd (map subst) extension;
      in
        add_parents thy parent'
          (make_parent_info name fields' extension' induct extdef :: parents)
      end;



(** concrete syntax for records **)

(* decode type *)

fun decode_type thy t =
  let
    fun get_sort xs n = AList.lookup (op =) xs (n: indexname) |> the_default (Sign.defaultS thy);
    val map_sort = Sign.intern_sort thy;
  in
    Syntax.typ_of_term (get_sort (Syntax.term_sorts map_sort t)) map_sort t
    |> Sign.intern_tycons thy
  end;


(* parse translations *)

fun gen_field_tr mark sfx (t as Const (c, _) $ Const (name, _) $ arg) =
      if c = mark then Syntax.const (suffix sfx name) $ Abs ("_", dummyT, arg)
      else raise TERM ("gen_field_tr: " ^ mark, [t])
  | gen_field_tr mark _ t = raise TERM ("gen_field_tr: " ^ mark, [t]);

fun gen_fields_tr sep mark sfx (tm as Const (c, _) $ t $ u) =
      if c = sep then gen_field_tr mark sfx t :: gen_fields_tr sep mark sfx u
      else [gen_field_tr mark sfx tm]
  | gen_fields_tr _ mark sfx tm = [gen_field_tr mark sfx tm];


fun record_update_tr [t, u] =
      Library.foldr (op $) (rev (gen_fields_tr "_updates" "_update" updateN u), t)
  | record_update_tr ts = raise TERM ("record_update_tr", ts);

fun update_name_tr (Free (x, T) :: ts) = Free (suffix updateN x, T) $$ ts
  | update_name_tr (Const (x, T) :: ts) = Const (suffix updateN x, T) $$ ts
  | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
      (c $ update_name_tr [t] $ (Syntax.const "fun" $ ty $ Syntax.const "dummy")) $$ ts
  | update_name_tr ts = raise TERM ("update_name_tr", ts);

fun dest_ext_field mark (t as (Const (c, _) $ Const (name, _) $ arg)) =
      if c = mark then (name, arg)
      else raise TERM ("dest_ext_field: " ^ mark, [t])
  | dest_ext_field _ t = raise TERM ("dest_ext_field", [t]);

fun dest_ext_fields sep mark (trm as (Const (c, _) $ t $ u)) =
      if c = sep then dest_ext_field mark t :: dest_ext_fields sep mark u
      else [dest_ext_field mark trm]
  | dest_ext_fields _ mark t = [dest_ext_field mark t];

fun gen_ext_fields_tr sep mark sfx more ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val msg = "error in record input: ";

    val fieldargs = dest_ext_fields sep mark t;
    fun splitargs (field :: fields) ((name, arg) :: fargs) =
          if can (unsuffix name) field
          then
            let val (args, rest) = splitargs fields fargs
            in (arg :: args, rest) end
          else raise TERM (msg ^ "expecting field " ^ field ^ " but got " ^ name, [t])
      | splitargs [] (fargs as (_ :: _)) = ([], fargs)
      | splitargs (_ :: _) [] = raise TERM (msg ^ "expecting more fields", [t])
      | splitargs _ _ = ([], []);

    fun mk_ext (fargs as (name, _) :: _) =
          (case get_fieldext thy (Sign.intern_const thy name) of
            SOME (ext, _) =>
              (case get_extfields thy ext of
                SOME flds =>
                  let
                    val (args, rest) = splitargs (map fst (but_last flds)) fargs;
                    val more' = mk_ext rest;
                  in list_comb (Syntax.const (suffix sfx ext), args @ [more']) end
              | NONE => raise TERM (msg ^ "no fields defined for " ^ ext, [t]))
          | NONE => raise TERM (msg ^ name ^" is no proper field", [t]))
      | mk_ext [] = more;
  in mk_ext fieldargs end;

fun gen_ext_type_tr sep mark sfx more ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;
    val msg = "error in record-type input: ";

    val fieldargs = dest_ext_fields sep mark t;
    fun splitargs (field :: fields) ((name, arg) :: fargs) =
          if can (unsuffix name) field then
            let val (args, rest) = splitargs fields fargs
            in (arg :: args, rest) end
          else raise TERM (msg ^ "expecting field " ^ field ^ " but got " ^ name, [t])
      | splitargs [] (fargs as (_ :: _)) = ([], fargs)
      | splitargs (_ :: _) [] = raise TERM (msg ^ "expecting more fields", [t])
      | splitargs _ _ = ([], []);

    fun mk_ext (fargs as (name, _) :: _) =
          (case get_fieldext thy (Sign.intern_const thy name) of
            SOME (ext, alphas) =>
              (case get_extfields thy ext of
                SOME flds =>
                 (let
                    val flds' = but_last flds;
                    val types = map snd flds';
                    val (args, rest) = splitargs (map fst flds') fargs;
                    val argtypes = map (Sign.certify_typ thy o decode_type thy) args;
                    val midx = fold (fn T => fn i => Int.max (maxidx_of_typ T, i)) argtypes 0;
                    val varifyT = varifyT midx;
                    val vartypes = map varifyT types;

                    val subst = fold (Sign.typ_match thy) (vartypes ~~ argtypes) Vartab.empty;
                    val alphas' =
                      map (Syntax.term_of_typ (! Syntax.show_sorts) o Envir.norm_type subst o varifyT)
                        (but_last alphas);

                    val more' = mk_ext rest;
                  in
                    list_comb (Syntax.const (suffix sfx ext), alphas' @ [more'])
                  end handle Type.TYPE_MATCH =>
                    raise TERM (msg ^ "type is no proper record (extension)", [t]))
              | NONE => raise TERM (msg ^ "no fields defined for " ^ ext, [t]))
          | NONE => raise TERM (msg ^ name ^" is no proper field", [t]))
      | mk_ext [] = more;

  in mk_ext fieldargs end;

fun gen_adv_record_tr sep mark sfx unit ctxt [t] =
      gen_ext_fields_tr sep mark sfx unit ctxt t
  | gen_adv_record_tr _ _ _ _ _ ts = raise TERM ("gen_record_tr", ts);

fun gen_adv_record_scheme_tr sep mark sfx ctxt [t, more] =
      gen_ext_fields_tr sep mark sfx more ctxt t
  | gen_adv_record_scheme_tr _ _ _ _ ts = raise TERM ("gen_record_scheme_tr", ts);

fun gen_adv_record_type_tr sep mark sfx unit ctxt [t] =
      gen_ext_type_tr sep mark sfx unit ctxt t
  | gen_adv_record_type_tr _ _ _ _ _ ts = raise TERM ("gen_record_tr", ts);

fun gen_adv_record_type_scheme_tr sep mark sfx ctxt [t, more] =
      gen_ext_type_tr sep mark sfx more ctxt t
  | gen_adv_record_type_scheme_tr _ _ _ _ ts = raise TERM ("gen_record_scheme_tr", ts);

val adv_record_tr = gen_adv_record_tr "_fields" "_field" extN HOLogic.unit;

val adv_record_scheme_tr = gen_adv_record_scheme_tr "_fields" "_field" extN;

val adv_record_type_tr =
  gen_adv_record_type_tr "_field_types" "_field_type" ext_typeN
    (Syntax.term_of_typ false (HOLogic.unitT));

val adv_record_type_scheme_tr =
  gen_adv_record_type_scheme_tr "_field_types" "_field_type" ext_typeN;


val parse_translation =
 [("_record_update", record_update_tr),
  ("_update_name", update_name_tr)];

val adv_parse_translation =
 [("_record", adv_record_tr),
  ("_record_scheme", adv_record_scheme_tr),
  ("_record_type", adv_record_type_tr),
  ("_record_type_scheme", adv_record_type_scheme_tr)];


(* print translations *)

val print_record_type_abbr = Unsynchronized.ref true;
val print_record_type_as_fields = Unsynchronized.ref true;

fun gen_field_upds_tr' mark sfx (tm as Const (name_field, _) $ k $ u) =
      let
        val t =
          (case k of
            Abs (_, _, Abs (_, _, t) $ Bound 0) =>
              if null (loose_bnos t) then t else raise Match
          | Abs (_, _, t) =>
              if null (loose_bnos t) then t else raise Match
          | _ => raise Match);

          (* FIXME ? *)
          (* (case k of (Const ("K_record", _) $ t) => t
                   | Abs (x, _, Const ("K_record", _) $ t $ Bound 0) => t
                   | _ => raise Match)*)
      in
        (case try (unsuffix sfx) name_field of
          SOME name =>
            apfst (cons (Syntax.const mark $ Syntax.free name $ t)) (gen_field_upds_tr' mark sfx u)
        | NONE => ([], tm))
      end
  | gen_field_upds_tr' _ _ tm = ([], tm);

fun record_update_tr' tm =
  let val (ts, u) = gen_field_upds_tr' "_update" updateN tm in
    if null ts then raise Match
    else
      Syntax.const "_record_update" $ u $
        foldr1 (fn (v, w) => Syntax.const "_updates" $ v $ w) (rev ts)
  end;

fun gen_field_tr' sfx tr' name =
  let val name_sfx = suffix sfx name
  in (name_sfx, fn [t, u] => tr' (Syntax.const name_sfx $ t $ u) | _ => raise Match) end;

fun record_tr' sep mark record record_scheme unit ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;

    fun field_lst t =
      (case strip_comb t of
        (Const (ext, _), args as (_ :: _)) =>
          (case try (unsuffix extN) (Sign.intern_const thy ext) of
            SOME ext' =>
              (case get_extfields thy ext' of
                SOME flds =>
                 (let
                    val f :: fs = but_last (map fst flds);
                    val flds' = Sign.extern_const thy f :: map Long_Name.base_name fs;
                    val (args', more) = split_last args;
                  in (flds' ~~ args') @ field_lst more end
                  handle Library.UnequalLengths => [("", t)])
              | NONE => [("", t)])
          | NONE => [("", t)])
       | _ => [("", t)]);

    val (flds, (_, more)) = split_last (field_lst t);
    val _ = if null flds then raise Match else ();
    val flds' = map (fn (n, t) => Syntax.const mark $ Syntax.const n $ t) flds;
    val flds'' = foldr1 (fn (x, y) => Syntax.const sep $ x $ y) flds';
  in
    if unit more
    then Syntax.const record $ flds''
    else Syntax.const record_scheme $ flds'' $ more
  end;

fun gen_record_tr' name =
  let
    val name_sfx = suffix extN name;
    val unit = (fn Const (@{const_syntax "Product_Type.Unity"}, _) => true | _ => false);
    fun tr' ctxt ts =
      record_tr' "_fields" "_field" "_record" "_record_scheme" unit ctxt
        (list_comb (Syntax.const name_sfx, ts));
  in (name_sfx, tr') end;

fun print_translation names =
  map (gen_field_tr' updateN record_update_tr') names;


(* record_type_abbr_tr' *)

(*try to reconstruct the record name type abbreviation from
  the (nested) extension types*)
fun record_type_abbr_tr' default_tr' abbr alphas zeta lastExt schemeT ctxt tm =
  let
    val thy = ProofContext.theory_of ctxt;

    (*tm is term representation of a (nested) field type. We first reconstruct the
      type from tm so that we can continue on the type level rather then the term level*)

    (*WORKAROUND:
      If a record type occurs in an error message of type inference there
      may be some internal frees donoted by ??:
      (Const "_tfree",_) $ Free ("??'a", _).

      This will unfortunately be translated to Type ("??'a", []) instead of
      TFree ("??'a", _) by typ_of_term, which will confuse unify below.
      fixT works around.*)
    fun fixT (T as Type (x, [])) =
          if String.isPrefix "??'" x then TFree (x, Sign.defaultS thy) else T
      | fixT (Type (x, xs)) = Type (x, map fixT xs)
      | fixT T = T;

    val T = fixT (decode_type thy tm);
    val midx = maxidx_of_typ T;
    val varifyT = varifyT midx;

    fun mk_type_abbr subst name alphas =
      let val abbrT = Type (name, map (fn a => varifyT (TFree (a, Sign.defaultS thy))) alphas) in
        Syntax.term_of_typ (! Syntax.show_sorts)
          (Sign.extern_typ thy (Envir.norm_type subst abbrT))
      end;

    fun match rT T = Sign.typ_match thy (varifyT rT, T) Vartab.empty;
  in
    if ! print_record_type_abbr then
      (case last_extT T of
        SOME (name, _) =>
          if name = lastExt then
           (let val subst = match schemeT T in
              if HOLogic.is_unitT (Envir.norm_type subst (varifyT (TFree (zeta, Sign.defaultS thy))))
              then mk_type_abbr subst abbr alphas
              else mk_type_abbr subst (suffix schemeN abbr) (alphas @ [zeta])
            end handle Type.TYPE_MATCH => default_tr' ctxt tm)
          else raise Match (*give print translation of specialised record a chance*)
      | _ => raise Match)
    else default_tr' ctxt tm
  end;

fun record_type_tr' sep mark record record_scheme ctxt t =
  let
    val thy = ProofContext.theory_of ctxt;

    val T = decode_type thy t;
    val varifyT = varifyT (Term.maxidx_of_typ T);

    fun term_of_type T = Syntax.term_of_typ (! Syntax.show_sorts) (Sign.extern_typ thy T);

    fun field_lst T =
      (case T of
        Type (ext, args) =>
          (case try (unsuffix ext_typeN) ext of
            SOME ext' =>
              (case get_extfields thy ext' of
                SOME flds =>
                  (case get_fieldext thy (fst (hd flds)) of
                    SOME (_, alphas) =>
                     (let
                        val f :: fs = but_last flds;
                        val flds' = apfst (Sign.extern_const thy) f ::
                          map (apfst Long_Name.base_name) fs;
                        val (args', more) = split_last args;
                        val alphavars = map varifyT (but_last alphas);
                        val subst = fold2 (curry (Sign.typ_match thy)) alphavars args' Vartab.empty;
                        val flds'' = (map o apsnd) (Envir.norm_type subst o varifyT) flds';
                      in flds'' @ field_lst more end
                      handle Type.TYPE_MATCH => [("", T)] | Library.UnequalLengths => [("", T)])
                  | NONE => [("", T)])
              | NONE => [("", T)])
          | NONE => [("", T)])
      | _ => [("", T)]);

    val (flds, (_, moreT)) = split_last (field_lst T);
    val flds' = map (fn (n, T) => Syntax.const mark $ Syntax.const n $ term_of_type T) flds;
    val flds'' =
      foldr1 (fn (x, y) => Syntax.const sep $ x $ y) flds'
        handle Empty => raise Match;
  in
    if not (! print_record_type_as_fields) orelse null flds then raise Match
    else if moreT = HOLogic.unitT then Syntax.const record $ flds''
    else Syntax.const record_scheme $ flds'' $ term_of_type moreT
  end;


fun gen_record_type_tr' name =
  let
    val name_sfx = suffix ext_typeN name;
    fun tr' ctxt ts =
      record_type_tr' "_field_types" "_field_type" "_record_type" "_record_type_scheme"
        ctxt (list_comb (Syntax.const name_sfx, ts))
  in (name_sfx, tr') end;


fun gen_record_type_abbr_tr' abbr alphas zeta lastExt schemeT name =
  let
    val name_sfx = suffix ext_typeN name;
    val default_tr' =
      record_type_tr' "_field_types" "_field_type" "_record_type" "_record_type_scheme";
    fun tr' ctxt ts =
      record_type_abbr_tr' default_tr' abbr alphas zeta lastExt schemeT ctxt
        (list_comb (Syntax.const name_sfx, ts));
  in (name_sfx, tr') end;



(** record simprocs **)

fun quick_and_dirty_prove stndrd thy asms prop tac =
  if ! quick_and_dirty then
    Goal.prove (ProofContext.init thy) [] []
      (Logic.list_implies (map Logic.varify asms, Logic.varify prop))
      (K (Skip_Proof.cheat_tac @{theory HOL}))
      (*Drule.standard can take quite a while for large records, thats why
        we varify the proposition manually here.*)
  else
    let val prf = Goal.prove (ProofContext.init thy) [] asms prop tac
    in if stndrd then Drule.standard prf else prf end;

fun quick_and_dirty_prf noopt opt () =
  if ! quick_and_dirty then noopt () else opt ();

fun is_sel_upd_pair thy (Const (s, _)) (Const (u, t')) =
  (case get_updates thy u of
    SOME u_name => u_name = s
  | NONE => raise TERM ("is_sel_upd_pair: not update", [Const (u, t')]));

fun mk_comp f g =
  let
    val X = fastype_of g;
    val A = domain_type X;
    val B = range_type X;
    val C = range_type (fastype_of f);
    val T = (B --> C) --> (A --> B) --> A --> C;
  in Const ("Fun.comp", T) $ f $ g end;

fun mk_comp_id f =
  let val T = range_type (fastype_of f)
  in mk_comp (Const ("Fun.id", T --> T)) f end;

fun get_upd_funs (upd $ _ $ t) = upd :: get_upd_funs t
  | get_upd_funs _ = [];

fun get_accupd_simps thy term defset =
  let
    val (acc, [body]) = strip_comb term;
    val upd_funs = sort_distinct TermOrd.fast_term_ord (get_upd_funs body);
    fun get_simp upd =
      let
        val T = domain_type (fastype_of upd);
        val lhs = mk_comp acc (upd $ Free ("f", T));
        val rhs =
          if is_sel_upd_pair thy acc upd
          then mk_comp (Free ("f", T)) acc
          else mk_comp_id acc;
        val prop = lhs === rhs;
        val othm =
          Goal.prove (ProofContext.init thy) [] [] prop
            (fn _ =>
              simp_tac defset 1 THEN
              REPEAT_DETERM (IsTupleSupport.istuple_intros_tac 1) THEN
              TRY (simp_tac (HOL_ss addsimps id_o_apps) 1));
        val dest =
          if is_sel_upd_pair thy acc upd
          then o_eq_dest
          else o_eq_id_dest;
      in Drule.standard (othm RS dest) end;
  in map get_simp upd_funs end;

fun get_updupd_simp thy defset u u' comp =
  let
    val f = Free ("f", domain_type (fastype_of u));
    val f' = Free ("f'", domain_type (fastype_of u'));
    val lhs = mk_comp (u $ f) (u' $ f');
    val rhs =
      if comp
      then u $ mk_comp f f'
      else mk_comp (u' $ f') (u $ f);
    val prop = lhs === rhs;
    val othm =
      Goal.prove (ProofContext.init thy) [] [] prop
        (fn _ =>
          simp_tac defset 1 THEN
          REPEAT_DETERM (IsTupleSupport.istuple_intros_tac 1) THEN
          TRY (simp_tac (HOL_ss addsimps [id_apply]) 1));
    val dest = if comp then o_eq_dest_lhs else o_eq_dest;
  in Drule.standard (othm RS dest) end;

fun get_updupd_simps thy term defset =
  let
    val upd_funs = get_upd_funs term;
    val cname = fst o dest_Const;
    fun getswap u u' = get_updupd_simp thy defset u u' (cname u = cname u');
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

val named_cterm_instantiate = IsTupleSupport.named_cterm_instantiate;

fun prove_unfold_defs thy ex_simps ex_simprs prop =
  let
    val defset = get_sel_upd_defs thy;
    val prop' = Envir.beta_eta_contract prop;
    val (lhs, _) = Logic.dest_equals (Logic.strip_assums_concl prop');
    val (_, args) = strip_comb lhs;
    val simps = (if length args = 1 then get_accupd_simps else get_updupd_simps) thy lhs defset;
  in
    Goal.prove (ProofContext.init thy) [] [] prop'
      (fn _ =>
        simp_tac (HOL_basic_ss addsimps (simps @ [K_record_comp])) 1 THEN
        TRY (simp_tac (HOL_basic_ss addsimps ex_simps addsimprocs ex_simprs) 1))
  end;


local

fun eq (s1: string) (s2: string) = (s1 = s2);

fun has_field extfields f T =
  exists (fn (eN, _) => exists (eq f o fst) (Symtab.lookup_list extfields eN)) (dest_recTs T);

fun K_skeleton n (T as Type (_, [_, kT])) (b as Bound i) (Abs (x, xT, t)) =
      if null (loose_bnos t) then ((n, kT), (Abs (x, xT, Bound (i + 1)))) else ((n, T), b)
  | K_skeleton n T b _ = ((n, T), b);

in

(* record_simproc *)

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
val record_simproc =
  Simplifier.simproc @{theory HOL} "record_simp" ["x"]
    (fn thy => fn _ => fn t =>
      (case t of
        (sel as Const (s, Type (_, [_, rangeS]))) $
            ((upd as Const (u, Type (_, [_, Type (_, [rT, _])]))) $ k $ r) =>
          if is_selector thy s andalso is_some (get_updates thy u) then
            let
              val {sel_upd = {updates, ...}, extfields, ...} = RecordsData.get thy;

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
                      (list_all (vars, Logic.mk_equals (sel $ trm, trm'))))
              | NONE => NONE)
            end
          else NONE
      | _ => NONE));

fun get_upd_acc_cong_thm upd acc thy simpset =
  let
    val insts = [("upd", cterm_of thy upd), ("acc", cterm_of thy acc)];
    val prop = Thm.concl_of (named_cterm_instantiate insts updacc_cong_triv);
  in
    Goal.prove (ProofContext.init thy) [] [] prop
      (fn _ =>
        simp_tac simpset 1 THEN
        REPEAT_DETERM (IsTupleSupport.istuple_intros_tac 1) THEN
        TRY (resolve_tac [updacc_cong_idI] 1))
  end;


(* record_upd_simproc *)

(*Simplify multiple updates:
    (1) "N_update y (M_update g (N_update x (M_update f r))) =
          (N_update (y o x) (M_update (g o f) r))"
    (2)  "r(|M:= M r|) = r"

  In both cases "more" updates complicate matters: for this reason
  we omit considering further updates if doing so would introduce
  both a more update and an update to a field within it.*)
val record_upd_simproc =
  Simplifier.simproc @{theory HOL} "record_upd_simp" ["x"]
    (fn thy => fn _ => fn t =>
      let
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
           [Drule.standard (uathm RS updacc_noopE),
            Drule.standard (uathm RS updacc_noop_compE)]
          end;

        (*If f is constant then (f o g) = f.  We know that K_skeleton
          only returns constant abstractions thus when we see an
          abstraction we can discard inner updates.*)
        fun add_upd (f as Abs _) fs = [f]
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
                fun mk_comp_local (f, f') = Const ("Fun.comp", funT --> funT --> funT) $ f $ f';
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
            (prove_unfold_defs thy noops' [record_simproc]
              (list_all (vars, Logic.mk_equals (lhs, rhs))))
        else NONE
      end);

end;


(* record_eq_simproc *)

(*Look up the most specific record-equality.

 Note on efficiency:
 Testing equality of records boils down to the test of equality of all components.
 Therefore the complexity is: #components * complexity for single component.
 Especially if a record has a lot of components it may be better to split up
 the record first and do simplification on that (record_split_simp_tac).
 e.g. r(|lots of updates|) = x

             record_eq_simproc          record_split_simp_tac
 Complexity: #components * #updates     #updates
*)
val record_eq_simproc =
  Simplifier.simproc @{theory HOL} "record_eq_simp" ["r = s"]
    (fn thy => fn _ => fn t =>
      (case t of Const ("op =", Type (_, [T, _])) $ _ $ _ =>
        (case rec_id ~1 T of
          "" => NONE
        | name =>
            (case get_equalities thy name of
              NONE => NONE
            | SOME thm => SOME (thm RS Eq_TrueI)))
      | _ => NONE));


(* record_split_simproc *)

(*Split quantified occurrences of records, for which P holds.  P can peek on the
  subterm starting at the quantified occurrence of the record (including the quantifier):
    P t = 0: do not split
    P t = ~1: completely split
    P t > 0: split up to given bound of record extensions.*)
fun record_split_simproc P =
  Simplifier.simproc @{theory HOL} "record_split_simp" ["x"]
    (fn thy => fn _ => fn t =>
      (case t of
        Const (quantifier, Type (_, [Type (_, [T, _]), _])) $ _ =>
          if quantifier = "All" orelse quantifier = "all" orelse quantifier = "Ex" then
            (case rec_id ~1 T of
              "" => NONE
            | _ =>
                let val split = P t in
                  if split <> 0 then
                    (case get_splits thy (rec_id split T) of
                      NONE => NONE
                    | SOME (all_thm, All_thm, Ex_thm, _) =>
                        SOME
                          (case quantifier of
                            "all" => all_thm
                          | "All" => All_thm RS eq_reflection
                          | "Ex" => Ex_thm RS eq_reflection
                          | _ => error "record_split_simproc"))
                  else NONE
                end)
          else NONE
      | _ => NONE));

val record_ex_sel_eq_simproc =
  Simplifier.simproc @{theory HOL} "record_ex_sel_eq_simproc" ["Ex t"]
    (fn thy => fn ss => fn t =>
      let
        fun prove prop =
          quick_and_dirty_prove true thy [] prop
            (fn _ => simp_tac (Simplifier.inherit_context ss (get_simpset thy)
                addsimps simp_thms addsimprocs [record_split_simproc (K ~1)]) 1);

        fun mkeq (lr, Teq, (sel, Tsel), x) i =
          if is_selector thy sel then
            let
              val x' =
                if not (loose_bvar1 (x, 0))
                then Free ("x" ^ string_of_int i, range_type Tsel)
                else raise TERM ("", [x]);
              val sel' = Const (sel, Tsel) $ Bound 0;
              val (l, r) = if lr then (sel', x') else (x', sel');
            in Const ("op =", Teq) $ l $ r end
          else raise TERM ("", [Const (sel, Tsel)]);

        fun dest_sel_eq (Const ("op =", Teq) $ (Const (sel, Tsel) $ Bound 0) $ X) =
              (true, Teq, (sel, Tsel), X)
          | dest_sel_eq (Const ("op =", Teq) $ X $ (Const (sel, Tsel) $ Bound 0)) =
              (false, Teq, (sel, Tsel), X)
          | dest_sel_eq _ = raise TERM ("", []);
      in
        (case t of
          Const ("Ex", Tex) $ Abs (s, T, t) =>
           (let
              val eq = mkeq (dest_sel_eq t) 0;
              val prop =
                list_all ([("r", T)],
                  Logic.mk_equals (Const ("Ex", Tex) $ Abs (s, T, eq), HOLogic.true_const));
            in SOME (prove prop) end
            handle TERM _ => NONE)
        | _ => NONE)
      end);


(* record_split_simp_tac *)

(*Split (and simplify) all records in the goal for which P holds.
  For quantified occurrences of a record
  P can peek on the whole subterm (including the quantifier); for free variables P
  can only peek on the variable itself.
  P t = 0: do not split
  P t = ~1: completely split
  P t > 0: split up to given bound of record extensions.*)
fun record_split_simp_tac thms P = CSUBGOAL (fn (cgoal, i) =>
  let
    val thy = Thm.theory_of_cterm cgoal;

    val goal = term_of cgoal;
    val frees = filter (is_recT o #2) (Term.add_frees goal []);

    val has_rec = exists_Const
      (fn (s, Type (_, [Type (_, [T, _]), _])) =>
          (s = "all" orelse s = "All" orelse s = "Ex") andalso is_recT T
        | _ => false);

    fun mk_split_free_tac free induct_thm i =
      let
        val cfree = cterm_of thy free;
        val _$ (_ $ r) = concl_of induct_thm;
        val crec = cterm_of thy r;
        val thm = cterm_instantiate [(crec, cfree)] induct_thm;
      in
        simp_tac (HOL_basic_ss addsimps @{thms induct_atomize}) i THEN
        rtac thm i THEN
        simp_tac (HOL_basic_ss addsimps @{thms induct_rulify}) i
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

    val simprocs = if has_rec goal then [record_split_simproc P] else [];
    val thms' = K_comp_convs @ thms;
  in
    EVERY split_frees_tacs THEN
    Simplifier.full_simp_tac (get_simpset thy addsimps thms' addsimprocs simprocs) i
  end);


(* record_split_tac *)

(*Split all records in the goal, which are quantified by ! or !!.*)
val record_split_tac = CSUBGOAL (fn (cgoal, i) =>
  let
    val goal = term_of cgoal;

    val has_rec = exists_Const
      (fn (s, Type (_, [Type (_, [T, _]), _])) =>
          (s = "all" orelse s = "All") andalso is_recT T
        | _ => false);

    fun is_all t =
      (case t of
        Const (quantifier, _) $ _ =>
          if quantifier = "All" orelse quantifier = "all" then ~1 else 0
      | _ => 0);
  in
    if has_rec goal then
      Simplifier.full_simp_tac (HOL_basic_ss addsimprocs [record_split_simproc is_all]) i
    else no_tac
  end);


(* wrapper *)

val record_split_name = "record_split_tac";
val record_split_wrapper = (record_split_name, fn tac => record_split_tac ORELSE' tac);



(** theory extender interface **)

(* prepare arguments *)

fun read_raw_parent ctxt raw_T =
  (case ProofContext.read_typ_abbrev ctxt raw_T of
    Type (name, Ts) => (Ts, name)
  | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun read_typ ctxt raw_T env =
  let
    val ctxt' = fold (Variable.declare_typ o TFree) env ctxt;
    val T = Syntax.read_typ ctxt' raw_T;
    val env' = OldTerm.add_typ_tfrees (T, env);
  in (T, env') end;

fun cert_typ ctxt raw_T env =
  let
    val thy = ProofContext.theory_of ctxt;
    val T = Type.no_tvars (Sign.certify_typ thy raw_T)
      handle TYPE (msg, _, _) => error msg;
    val env' = OldTerm.add_typ_tfrees (T, env);
  in (T, env') end;


(* attributes *)

fun case_names_fields x = RuleCases.case_names ["fields"] x;
fun induct_type_global name = [case_names_fields, Induct.induct_type name];
fun cases_type_global name = [case_names_fields, Induct.cases_type name];


(* tactics *)

fun simp_all_tac ss simps = ALLGOALS (Simplifier.asm_full_simp_tac (ss addsimps simps));

(*Do case analysis / induction according to rule on last parameter of ith subgoal
  (or on s if there are no parameters).
  Instatiation of record variable (and predicate) in rule is calculated to
  avoid problems with higher order unification.*)
fun try_param_tac s rule = CSUBGOAL (fn (cgoal, i) =>
  let
    val cert = Thm.cterm_of (Thm.theory_of_cterm cgoal);

    val g = Thm.term_of cgoal;
    val params = Logic.strip_params g;
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl g);
    val rule' = Thm.lift_rule cgoal rule;
    val (P, ys) = strip_comb (HOLogic.dest_Trueprop
      (Logic.strip_assums_concl (prop_of rule')));
    (*ca indicates if rule is a case analysis or induction rule*)
    val (x, ca) =
      (case rev (Library.drop (length params, ys)) of
        [] => (head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop
          (hd (rev (Logic.strip_assums_hyp (hd (prems_of rule')))))))), true)
      | [x] => (head_of x, false));
    val rule'' = cterm_instantiate (map (pairself cert)
      (case rev params of
        [] =>
          (case AList.lookup (op =) (Term.add_frees g []) s of
            NONE => sys_error "try_param_tac: no such variable"
          | SOME T => [(P, if ca then concl else lambda (Free (s, T)) concl), (x, Free (s, T))])
      | (_, T) :: _ =>
          [(P, list_abs (params, if ca then concl else incr_boundvars 1 (Abs (s, T, concl)))),
            (x, list_abs (params, Bound 0))])) rule';
  in compose_tac (false, rule'', nprems_of rule) i end);


fun extension_definition name fields alphas zeta moreT more vars thy =
  let
    val base = Long_Name.base_name;
    val fieldTs = map snd fields;
    val alphas_zeta = alphas @ [zeta];
    val alphas_zetaTs = map (fn a => TFree (a, HOLogic.typeS)) alphas_zeta;
    val extT_name = suffix ext_typeN name
    val extT = Type (extT_name, alphas_zetaTs);
    val fields_moreTs = fieldTs @ [moreT];


    (*before doing anything else, create the tree of new types
      that will back the record extension*)

    val mktreeV = Balanced_Tree.make IsTupleSupport.mk_cons_tuple;

    fun mk_istuple (left, right) (thy, i) =
      let
        val suff = if i = 0 then ext_typeN else inner_typeN ^ string_of_int i;
        val nm = suffix suff (Long_Name.base_name name);
        val ((_, cons), thy') =
          IsTupleSupport.add_istuple_type
            (nm, alphas_zeta) (fastype_of left, fastype_of right) thy;
      in
        (cons $ left $ right, (thy', i + 1))
      end;

    (*trying to create a 1-element istuple will fail, and is pointless anyway*)
    fun mk_even_istuple [arg] = pair arg
      | mk_even_istuple args = mk_istuple (IsTupleSupport.dest_cons_tuple (mktreeV args));

    fun build_meta_tree_type i thy vars more =
      let val len = length vars in
        if len < 1 then raise TYPE ("meta_tree_type args too short", [], vars)
        else if len > 16 then
          let
            fun group16 [] = []
              | group16 xs = Library.take (16, xs) :: group16 (Library.drop (16, xs));
            val vars' = group16 vars;
            val (composites, (thy', i')) = fold_map mk_even_istuple vars' (thy, i);
          in
            build_meta_tree_type i' thy' composites more
          end
        else
          let val (term, (thy', _)) = mk_istuple (mktreeV vars, more) (thy, 0)
          in (term, thy') end
      end;

    val _ = timing_msg "record extension preparing definitions";


    (* 1st stage part 1: introduce the tree of new types *)

    fun get_meta_tree () = build_meta_tree_type 1 thy vars more;
    val (ext_body, typ_thy) =
      timeit_msg "record extension nested type def:" get_meta_tree;


    (* prepare declarations and definitions *)

    (*fields constructor*)
    val ext_decl = mk_extC (name, extT) fields_moreTs;
    val ext_spec = list_comb (Const ext_decl, vars @ [more]) :== ext_body;

    fun mk_ext args = list_comb (Const ext_decl, args);


    (* 1st stage part 2: define the ext constant *)

    fun mk_defs () =
      typ_thy
      |> Sign.add_consts_i [Syntax.no_syn (apfst (Binding.name o base) ext_decl)]
      |> PureThy.add_defs false [Thm.no_attributes (apfst Binding.name ext_spec)]
    val ([ext_def], defs_thy) =
      timeit_msg "record extension constructor def:" mk_defs;


    (* prepare propositions *)

    val _ = timing_msg "record extension preparing propositions";
    val vars_more = vars @ [more];
    val variants = map (fn Free (x, _) => x) vars_more;
    val ext = mk_ext vars_more;
    val s = Free (rN, extT);
    val P = Free (Name.variant variants "P", extT --> HOLogic.boolT);

    val inject_prop =
      let val vars_more' = map (fn (Free (x, T)) => Free (x ^ "'", T)) vars_more in
        HOLogic.mk_conj (HOLogic.eq_const extT $
          mk_ext vars_more $ mk_ext vars_more', HOLogic.true_const)
        ===
        foldr1 HOLogic.mk_conj
          (map HOLogic.mk_eq (vars_more ~~ vars_more') @ [HOLogic.true_const])
      end;

    val induct_prop =
      (All (map dest_Free vars_more) (Trueprop (P $ ext)), Trueprop (P $ s));

    val split_meta_prop =
      let val P = Free (Name.variant variants "P", extT --> Term.propT) in
        Logic.mk_equals
         (All [dest_Free s] (P $ s), All (map dest_Free vars_more) (P $ ext))
      end;

    val prove_standard = quick_and_dirty_prove true defs_thy;

    fun inject_prf () =
      simplify HOL_ss
        (prove_standard [] inject_prop
          (fn _ =>
            simp_tac (HOL_basic_ss addsimps [ext_def]) 1 THEN
            REPEAT_DETERM
              (rtac refl_conj_eq 1 ORELSE
                IsTupleSupport.istuple_intros_tac 1 ORELSE
                rtac refl 1)));

    val inject = timeit_msg "record extension inject proof:" inject_prf;

    (*We need a surjection property r = (| f = f r, g = g r ... |)
      to prove other theorems. We haven't given names to the accessors
      f, g etc yet however, so we generate an ext structure with
      free variables as all arguments and allow the introduction tactic to
      operate on it as far as it can. We then use Drule.standard to convert
      the free variables into unifiable variables and unify them with
      (roughly) the definition of the accessor.*)
    fun surject_prf () =
      let
        val cterm_ext = cterm_of defs_thy ext;
        val start = named_cterm_instantiate [("y", cterm_ext)] surject_assist_idE;
        val tactic1 =
          simp_tac (HOL_basic_ss addsimps [ext_def]) 1 THEN
          REPEAT_ALL_NEW IsTupleSupport.istuple_intros_tac 1;
        val tactic2 = REPEAT (rtac surject_assistI 1 THEN rtac refl 1);
        val [halfway] = Seq.list_of (tactic1 start);
        val [surject] = Seq.list_of (tactic2 (Drule.standard halfway));
      in
        surject
      end;
    val surject = timeit_msg "record extension surjective proof:" surject_prf;

    fun split_meta_prf () =
      prove_standard [] split_meta_prop
        (fn _ =>
          EVERY1
           [rtac equal_intr_rule, Goal.norm_hhf_tac,
            etac meta_allE, atac,
            rtac (prop_subst OF [surject]),
            REPEAT o etac meta_allE, atac]);
    val split_meta = timeit_msg "record extension split_meta proof:" split_meta_prf;

    fun induct_prf () =
      let val (assm, concl) = induct_prop in
        prove_standard [assm] concl
          (fn {prems, ...} =>
            cut_rules_tac [split_meta RS Drule.equal_elim_rule2] 1 THEN
            resolve_tac prems 2 THEN
            asm_simp_tac HOL_ss 1)
      end;
    val induct = timeit_msg "record extension induct proof:" induct_prf;

    val ([inject', induct', surjective', split_meta'], thm_thy) =
      defs_thy
      |> (PureThy.add_thms o map (Thm.no_attributes o apfst Binding.name))
           [("ext_inject", inject),
            ("ext_induct", induct),
            ("ext_surjective", surject),
            ("ext_split", split_meta)];

  in (thm_thy, extT, induct', inject', split_meta', ext_def) end;

fun chunks [] [] = []
  | chunks [] xs = [xs]
  | chunks (l :: ls) xs = Library.take (l, xs) :: chunks ls (Library.drop (l, xs));

fun chop_last [] = error "chop_last: list should not be empty"
  | chop_last [x] = ([], x)
  | chop_last (x :: xs) = let val (tl, l) = chop_last xs in (x :: tl, l) end;

fun subst_last _ [] = error "subst_last: list should not be empty"
  | subst_last s [_] = [s]
  | subst_last s (x :: xs) = x :: subst_last s xs;


(* mk_recordT *)

(*builds up the record type from the current extension tpye extT and a list
  of parent extensions, starting with the root of the record hierarchy*)
fun mk_recordT extT =
  fold_rev (fn (parent, Ts) => fn T => Type (parent, subst_last T Ts)) extT;


fun obj_to_meta_all thm =
  let
    fun E thm =  (* FIXME proper name *)
      (case (SOME (spec OF [thm]) handle THM _ => NONE) of
        SOME thm' => E thm'
      | NONE => thm);
    val th1 = E thm;
    val th2 = Drule.forall_intr_vars th1;
  in th2 end;

fun meta_to_obj_all thm =
  let
    val thy = Thm.theory_of_thm thm;
    val prop = Thm.prop_of thm;
    val params = Logic.strip_params prop;
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl prop);
    val ct = cterm_of thy (HOLogic.mk_Trueprop (HOLogic.list_all (params, concl)));
    val thm' = Seq.hd (REPEAT (rtac allI 1) (Thm.trivial ct));
  in Thm.implies_elim thm' thm end;


(* record_definition *)

fun record_definition (args, bname) parent (parents: parent_info list) raw_fields thy =
  let
    val external_names = NameSpace.external_names (Sign.naming_of thy);

    val alphas = map fst args;
    val name = Sign.full_bname thy bname;
    val full = Sign.full_bname_path thy bname;
    val base = Long_Name.base_name;

    val (bfields, field_syntax) =
      split_list (map (fn (x, T, mx) => ((x, T), mx)) raw_fields);

    val parent_fields = maps #fields parents;
    val parent_chunks = map (length o #fields) parents;
    val parent_names = map fst parent_fields;
    val parent_types = map snd parent_fields;
    val parent_fields_len = length parent_fields;
    val parent_variants = Name.variant_list [moreN, rN, rN ^ "'", wN] (map base parent_names);
    val parent_vars = ListPair.map Free (parent_variants, parent_types);
    val parent_len = length parents;

    val fields = map (apfst full) bfields;
    val names = map fst fields;
    val extN = full bname;
    val types = map snd fields;
    val alphas_fields = fold Term.add_tfree_namesT types [];
    val alphas_ext = inter (op =) (alphas, alphas_fields);
    val len = length fields;
    val variants =
      Name.variant_list (moreN :: rN :: (rN ^ "'") :: wN :: parent_variants)
        (map fst bfields);
    val vars = ListPair.map Free (variants, types);
    val named_vars = names ~~ vars;
    val idxms = 0 upto len;

    val all_fields = parent_fields @ fields;
    val all_types = parent_types @ types;
    val all_variants = parent_variants @ variants;
    val all_vars = parent_vars @ vars;
    val all_named_vars = (parent_names ~~ parent_vars) @ named_vars;


    val zeta = Name.variant alphas "'z";
    val moreT = TFree (zeta, HOLogic.typeS);
    val more = Free (moreN, moreT);
    val full_moreN = full moreN;
    val bfields_more = bfields @ [(moreN, moreT)];
    val fields_more = fields @ [(full_moreN, moreT)];
    val named_vars_more = named_vars @ [(full_moreN, more)];
    val all_vars_more = all_vars @ [more];
    val all_named_vars_more = all_named_vars @ [(full_moreN, more)];


    (* 1st stage: extension_thy *)

    val (extension_thy, extT, ext_induct, ext_inject, ext_split, ext_def) =
      thy
      |> Sign.add_path bname
      |> extension_definition extN fields alphas_ext zeta moreT more vars;

    val _ = timing_msg "record preparing definitions";
    val Type extension_scheme = extT;
    val extension_name = unsuffix ext_typeN (fst extension_scheme);
    val extension = let val (n, Ts) = extension_scheme in (n, subst_last HOLogic.unitT Ts) end;
    val extension_names = map (unsuffix ext_typeN o fst o #extension) parents @ [extN];
    val extension_id = implode extension_names;

    fun rec_schemeT n = mk_recordT (map #extension (Library.drop (n, parents))) extT;
    val rec_schemeT0 = rec_schemeT 0;

    fun recT n =
      let val (c, Ts) = extension in
        mk_recordT (map #extension (Library.drop (n, parents)))
          (Type (c, subst_last HOLogic.unitT Ts))
      end;
    val recT0 = recT 0;

    fun mk_rec args n =
      let
        val (args', more) = chop_last args;
        fun mk_ext' ((name, T), args) more = mk_ext (name, T) (args @ [more]);
        fun build Ts =
          fold_rev mk_ext' (Library.drop (n, (extension_names ~~ Ts) ~~ chunks parent_chunks args'))
            more;
      in
        if more = HOLogic.unit
        then build (map recT (0 upto parent_len))
        else build (map rec_schemeT (0 upto parent_len))
      end;

    val r_rec0 = mk_rec all_vars_more 0;
    val r_rec_unit0 = mk_rec (all_vars @ [HOLogic.unit]) 0;

    fun r n = Free (rN, rec_schemeT n)
    val r0 = r 0;
    fun r_unit n = Free (rN, recT n)
    val r_unit0 = r_unit 0;
    val w = Free (wN, rec_schemeT 0)


    (* prepare print translation functions *)

    val field_tr's =
      print_translation (distinct (op =) (maps external_names (full_moreN :: names)));

    val adv_ext_tr's =
      let val trnames = external_names extN
      in map (gen_record_tr') trnames end;

    val adv_record_type_abbr_tr's =
      let
        val trnames = external_names (hd extension_names);
        val lastExt = unsuffix ext_typeN (fst extension);
      in map (gen_record_type_abbr_tr' name alphas zeta lastExt rec_schemeT0) trnames end;

    val adv_record_type_tr's =
      let
        val trnames = if parent_len > 0 then external_names extN else [];
        (*avoid conflict with adv_record_type_abbr_tr's*)
      in map (gen_record_type_tr') trnames end;


    (* prepare declarations *)

    val sel_decls = map (mk_selC rec_schemeT0) bfields_more;
    val upd_decls = map (mk_updC updateN rec_schemeT0) bfields_more;
    val make_decl = (makeN, all_types ---> recT0);
    val fields_decl = (fields_selN, types ---> Type extension);
    val extend_decl = (extendN, recT0 --> moreT --> rec_schemeT0);
    val truncate_decl = (truncateN, rec_schemeT0 --> recT0);

    (* prepare definitions *)

    (*record (scheme) type abbreviation*)
    val recordT_specs =
      [(Binding.name (suffix schemeN bname), alphas @ [zeta], rec_schemeT0, Syntax.NoSyn),
        (Binding.name bname, alphas, recT0, Syntax.NoSyn)];

    val ext_defs = ext_def :: map #extdef parents;

    (*Theorems from the istuple intros.
      This is complex enough to deserve a full comment.
      By unfolding ext_defs from r_rec0 we create a tree of constructor
      calls (many of them Pair, but others as well). The introduction
      rules for update_accessor_eq_assist can unify two different ways
      on these constructors. If we take the complete result sequence of
      running a the introduction tactic, we get one theorem for each upd/acc
      pair, from which we can derive the bodies of our selector and
      updator and their convs.*)
    fun get_access_update_thms () =
      let
        val r_rec0_Vars =
          let
            (*pick variable indices of 1 to avoid possible variable
              collisions with existing variables in updacc_eq_triv*)
            fun to_Var (Free (c, T)) = Var ((c, 1), T);
          in mk_rec (map to_Var all_vars_more) 0 end;

        val cterm_rec = cterm_of extension_thy r_rec0;
        val cterm_vrs = cterm_of extension_thy r_rec0_Vars;
        val insts = [("v", cterm_rec), ("v'", cterm_vrs)];
        val init_thm = named_cterm_instantiate insts updacc_eq_triv;
        val terminal = rtac updacc_eq_idI 1 THEN rtac refl 1;
        val tactic =
          simp_tac (HOL_basic_ss addsimps ext_defs) 1 THEN
          REPEAT (IsTupleSupport.istuple_intros_tac 1 ORELSE terminal);
        val updaccs = Seq.list_of (tactic init_thm);
      in
        (updaccs RL [updacc_accessor_eqE],
         updaccs RL [updacc_updator_eqE],
         updaccs RL [updacc_cong_from_eq])
      end;
    val (accessor_thms, updator_thms, upd_acc_cong_assists) =
      timeit_msg "record getting tree access/updates:" get_access_update_thms;

    fun lastN xs = Library.drop (parent_fields_len, xs);

    (*selectors*)
    fun mk_sel_spec ((c, T), thm) =
      let
        val acc $ arg =
          (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Envir.beta_eta_contract o concl_of) thm;
        val _ =
          if (arg aconv r_rec0) then ()
          else raise TERM ("mk_sel_spec: different arg", [arg]);
      in
        Const (mk_selC rec_schemeT0 (c, T)) :== acc
      end;
    val sel_specs = map mk_sel_spec (fields_more ~~ lastN accessor_thms);

    (*updates*)
    fun mk_upd_spec ((c, T), thm) =
      let
        val (upd $ _ $ arg) =
          (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Envir.beta_eta_contract o concl_of) thm;
        val _ =
          if (arg aconv r_rec0) then ()
          else raise TERM ("mk_sel_spec: different arg", [arg]);
      in Const (mk_updC updateN rec_schemeT0 (c, T)) :== upd end;
    val upd_specs = map mk_upd_spec (fields_more ~~ lastN updator_thms);

    (*derived operations*)
    val make_spec = Const (full makeN, all_types ---> recT0) $$ all_vars :==
      mk_rec (all_vars @ [HOLogic.unit]) 0;
    val fields_spec = Const (full fields_selN, types ---> Type extension) $$ vars :==
      mk_rec (all_vars @ [HOLogic.unit]) parent_len;
    val extend_spec =
      Const (full extendN, recT0-->moreT-->rec_schemeT0) $ r_unit0 $ more :==
      mk_rec ((map (mk_sel r_unit0) all_fields) @ [more]) 0;
    val truncate_spec = Const (full truncateN, rec_schemeT0 --> recT0) $ r0 :==
      mk_rec ((map (mk_sel r0) all_fields) @ [HOLogic.unit]) 0;


    (* 2st stage: defs_thy *)

    fun mk_defs () =
      extension_thy
      |> Sign.add_trfuns ([], [], field_tr's, [])
      |> Sign.add_advanced_trfuns
          ([], [], adv_ext_tr's @ adv_record_type_tr's @ adv_record_type_abbr_tr's, [])
      |> Sign.parent_path
      |> Sign.add_tyabbrs_i recordT_specs
      |> Sign.add_path bname
      |> Sign.add_consts_i
          (map2 (fn (x, T) => fn mx => (Binding.name x, T, mx))
            sel_decls (field_syntax @ [Syntax.NoSyn]))
      |> (Sign.add_consts_i o map (fn (x, T) => (Binding.name x, T, Syntax.NoSyn)))
          (upd_decls @ [make_decl, fields_decl, extend_decl, truncate_decl])
      |> ((PureThy.add_defs false o map (Thm.no_attributes o apfst Binding.name)) sel_specs)
      ||>> ((PureThy.add_defs false o map (Thm.no_attributes o apfst Binding.name)) upd_specs)
      ||>> ((PureThy.add_defs false o map (Thm.no_attributes o apfst Binding.name))
             [make_spec, fields_spec, extend_spec, truncate_spec])
      |->
        (fn defs as ((sel_defs, upd_defs), derived_defs) =>
          fold Code.add_default_eqn sel_defs
          #> fold Code.add_default_eqn upd_defs
          #> fold Code.add_default_eqn derived_defs
          #> pair defs)
    val (((sel_defs, upd_defs), derived_defs), defs_thy) =
      timeit_msg "record trfuns/tyabbrs/selectors/updates/make/fields/extend/truncate defs:"
        mk_defs;

    (* prepare propositions *)
    val _ = timing_msg "record preparing propositions";
    val P = Free (Name.variant all_variants "P", rec_schemeT0 --> HOLogic.boolT);
    val C = Free (Name.variant all_variants "C", HOLogic.boolT);
    val P_unit = Free (Name.variant all_variants "P", recT0 --> HOLogic.boolT);

    (*selectors*)
    val sel_conv_props =
       map (fn (c, x as Free (_, T)) => mk_sel r_rec0 (c, T) === x) named_vars_more;

    (*updates*)
    fun mk_upd_prop (i, (c, T)) =
      let
        val x' = Free (Name.variant all_variants (base c ^ "'"), T --> T);
        val n = parent_fields_len + i;
        val args' = nth_map n (K (x' $ nth all_vars_more n)) all_vars_more
      in mk_upd updateN c x' r_rec0 === mk_rec args' 0 end;
    val upd_conv_props = ListPair.map mk_upd_prop (idxms, fields_more);

    (*induct*)
    val induct_scheme_prop =
      All (map dest_Free all_vars_more) (Trueprop (P $ r_rec0)) ==> Trueprop (P $ r0);
    val induct_prop =
      (All (map dest_Free all_vars) (Trueprop (P_unit $ r_rec_unit0)),
        Trueprop (P_unit $ r_unit0));

    (*surjective*)
    val surjective_prop =
      let val args = map (fn (c, Free (_, T)) => mk_sel r0 (c, T)) all_named_vars_more
      in r0 === mk_rec args 0 end;

    (*cases*)
    val cases_scheme_prop =
      (All (map dest_Free all_vars_more) ((r0 === r_rec0) ==> Trueprop C))
        ==> Trueprop C;

    val cases_prop =
      (All (map dest_Free all_vars) ((r_unit0 === r_rec_unit0) ==> Trueprop C))
         ==> Trueprop C;

    (*split*)
    val split_meta_prop =
      let val P = Free (Name.variant all_variants "P", rec_schemeT0-->Term.propT) in
        Logic.mk_equals
         (All [dest_Free r0] (P $ r0), All (map dest_Free all_vars_more) (P $ r_rec0))
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
      in All (map dest_Free [r0, s']) (Logic.list_implies (seleqs, r0 === s')) end;


    (* 3rd stage: thms_thy *)

    fun prove stndrd = quick_and_dirty_prove stndrd defs_thy;
    val prove_standard = quick_and_dirty_prove true defs_thy;

    fun prove_simp stndrd ss simps =
      let val tac = simp_all_tac ss simps
      in fn prop => prove stndrd [] prop (K tac) end;

    val ss = get_simpset defs_thy;

    fun sel_convs_prf () =
      map (prove_simp false ss (sel_defs @ accessor_thms)) sel_conv_props;
    val sel_convs = timeit_msg "record sel_convs proof:" sel_convs_prf;
    fun sel_convs_standard_prf () = map Drule.standard sel_convs
    val sel_convs_standard =
      timeit_msg "record sel_convs_standard proof:" sel_convs_standard_prf;

    fun upd_convs_prf () =
      map (prove_simp false ss (upd_defs @ updator_thms)) upd_conv_props;
    val upd_convs = timeit_msg "record upd_convs proof:" upd_convs_prf;
    fun upd_convs_standard_prf () = map Drule.standard upd_convs
    val upd_convs_standard =
      timeit_msg "record upd_convs_standard proof:" upd_convs_standard_prf;

    fun get_upd_acc_congs () =
      let
        val symdefs = map symmetric (sel_defs @ upd_defs);
        val fold_ss = HOL_basic_ss addsimps symdefs;
        val ua_congs = map (Drule.standard o simplify fold_ss) upd_acc_cong_assists;
      in (ua_congs RL [updacc_foldE], ua_congs RL [updacc_unfoldE]) end;
    val (fold_congs, unfold_congs) =
      timeit_msg "record upd fold/unfold congs:" get_upd_acc_congs;

    val parent_induct = if null parents then [] else [#induct (hd (rev parents))];

    fun induct_scheme_prf () =
      prove_standard [] induct_scheme_prop
        (fn _ =>
          EVERY
           [if null parent_induct then all_tac else try_param_tac rN (hd parent_induct) 1,
            try_param_tac rN ext_induct 1,
            asm_simp_tac HOL_basic_ss 1]);
    val induct_scheme = timeit_msg "record induct_scheme proof:" induct_scheme_prf;

    fun induct_prf () =
      let val (assm, concl) = induct_prop in
        prove_standard [assm] concl (fn {prems, ...} =>
          try_param_tac rN induct_scheme 1
          THEN try_param_tac "more" @{thm unit.induct} 1
          THEN resolve_tac prems 1)
      end;
    val induct = timeit_msg "record induct proof:" induct_prf;

    fun cases_scheme_prf_opt () =
      let
        val _ $ (Pvar $ _) = concl_of induct_scheme;
        val ind =
          cterm_instantiate
            [(cterm_of defs_thy Pvar, cterm_of defs_thy
              (lambda w (HOLogic.imp $ HOLogic.mk_eq (r0, w) $ C)))]
            induct_scheme;
        in Drule.standard (ObjectLogic.rulify (mp OF [ind, refl])) end;

    fun cases_scheme_prf_noopt () =
      prove_standard [] cases_scheme_prop
        (fn _ =>
          EVERY1
           [asm_full_simp_tac (HOL_basic_ss addsimps [atomize_all, atomize_imp]),
            try_param_tac rN induct_scheme,
            rtac impI,
            REPEAT o etac allE,
            etac mp,
            rtac refl]);
    val cases_scheme_prf = quick_and_dirty_prf cases_scheme_prf_noopt cases_scheme_prf_opt;
    val cases_scheme = timeit_msg "record cases_scheme proof:" cases_scheme_prf;

    fun cases_prf () =
      prove_standard [] cases_prop
        (fn _ =>
          try_param_tac rN cases_scheme 1 THEN
          simp_all_tac HOL_basic_ss [unit_all_eq1]);
    val cases = timeit_msg "record cases proof:" cases_prf;

    fun surjective_prf () =
      let
        val leaf_ss = get_sel_upd_defs defs_thy addsimps (sel_defs @ (o_assoc :: id_o_apps));
        val init_ss = HOL_basic_ss addsimps ext_defs;
      in
        prove_standard [] surjective_prop
          (fn _ =>
            EVERY
             [rtac surject_assist_idE 1,
              simp_tac init_ss 1,
              REPEAT
                (IsTupleSupport.istuple_intros_tac 1 ORELSE
                  (rtac surject_assistI 1 THEN simp_tac leaf_ss 1))])
      end;
    val surjective = timeit_msg "record surjective proof:" surjective_prf;

    fun split_meta_prf () =
      prove false [] split_meta_prop
        (fn _ =>
          EVERY1
           [rtac equal_intr_rule, Goal.norm_hhf_tac,
            etac meta_allE, atac,
            rtac (prop_subst OF [surjective]),
            REPEAT o etac meta_allE, atac]);
    val split_meta = timeit_msg "record split_meta proof:" split_meta_prf;
    fun split_meta_standardise () = Drule.standard split_meta;
    val split_meta_standard =
      timeit_msg "record split_meta standard:" split_meta_standardise;

    fun split_object_prf_opt () =
      let
        val cPI= cterm_of defs_thy (lambda r0 (Trueprop (P $ r0)));
        val _ $ Abs (_, _, P $ _) = fst (Logic.dest_equals (concl_of split_meta_standard));
        val cP = cterm_of defs_thy P;
        val split_meta' = cterm_instantiate [(cP, cPI)] split_meta_standard;
        val (l, r) = HOLogic.dest_eq (HOLogic.dest_Trueprop split_object_prop);
        val cl = cterm_of defs_thy (HOLogic.mk_Trueprop l);
        val cr = cterm_of defs_thy (HOLogic.mk_Trueprop r);
        val thl =
          assume cl                   (*All r. P r*) (* 1 *)
          |> obj_to_meta_all          (*!!r. P r*)
          |> equal_elim split_meta'   (*!!n m more. P (ext n m more)*)
          |> meta_to_obj_all          (*All n m more. P (ext n m more)*) (* 2*)
          |> implies_intr cl          (* 1 ==> 2 *)
        val thr =
          assume cr                             (*All n m more. P (ext n m more)*)
          |> obj_to_meta_all                    (*!!n m more. P (ext n m more)*)
          |> equal_elim (symmetric split_meta') (*!!r. P r*)
          |> meta_to_obj_all                    (*All r. P r*)
          |> implies_intr cr                    (* 2 ==> 1 *)
     in Drule.standard (thr COMP (thl COMP iffI)) end;

    fun split_object_prf_noopt () =
      prove_standard [] split_object_prop
        (fn _ =>
          EVERY1
           [rtac iffI,
            REPEAT o rtac allI, etac allE, atac,
            rtac allI, rtac induct_scheme, REPEAT o etac allE, atac]);

    val split_object_prf = quick_and_dirty_prf split_object_prf_noopt split_object_prf_opt;
    val split_object = timeit_msg "record split_object proof:" split_object_prf;


    fun split_ex_prf () =
      let
        val ss = HOL_basic_ss addsimps [not_ex RS sym, Not_eq_iff];
        val P_nm = fst (dest_Free P);
        val not_P = cterm_of defs_thy (lambda r0 (HOLogic.mk_not (P $ r0)));
        val so' = named_cterm_instantiate ([(P_nm, not_P)]) split_object;
        val so'' = simplify ss so';
      in
        prove_standard [] split_ex_prop (fn _ => resolve_tac [so''] 1)
      end;
    val split_ex = timeit_msg "record split_ex proof:" split_ex_prf;

    fun equality_tac thms =
      let
        val s' :: s :: eqs = rev thms;
        val ss' = ss addsimps (s' :: s :: sel_convs_standard);
        val eqs' = map (simplify ss') eqs;
      in simp_tac (HOL_basic_ss addsimps (s' :: s :: eqs')) 1 end;

    fun equality_prf () =
      prove_standard [] equality_prop (fn {context, ...} =>
        fn st =>
          let val [s, s'] = map #1 (rev (Tactic.innermost_params 1 st)) in
            st |> (res_inst_tac context [((rN, 0), s)] cases_scheme 1 THEN
              res_inst_tac context [((rN, 0), s')] cases_scheme 1 THEN
              Subgoal.FOCUS (fn {prems, ...} => equality_tac prems) context 1)
             (*simp_all_tac ss (sel_convs) would also work but is less efficient*)
          end);
    val equality = timeit_msg "record equality proof:" equality_prf;

    val ((([sel_convs', upd_convs', sel_defs', upd_defs',
            fold_congs', unfold_congs',
          [split_meta', split_object', split_ex'], derived_defs'],
          [surjective', equality']),
          [induct_scheme', induct', cases_scheme', cases']), thms_thy) =
      defs_thy
      |> (PureThy.add_thmss o map (Thm.no_attributes o apfst Binding.name))
         [("select_convs", sel_convs_standard),
          ("update_convs", upd_convs_standard),
          ("select_defs", sel_defs),
          ("update_defs", upd_defs),
          ("fold_congs", fold_congs),
          ("unfold_congs", unfold_congs),
          ("splits", [split_meta_standard, split_object, split_ex]),
          ("defs", derived_defs)]
      ||>> (PureThy.add_thms o map (Thm.no_attributes o apfst Binding.name))
          [("surjective", surjective),
           ("equality", equality)]
      ||>> (PureThy.add_thms o (map o apfst o apfst) Binding.name)
        [(("induct_scheme", induct_scheme), induct_type_global (suffix schemeN name)),
         (("induct", induct), induct_type_global name),
         (("cases_scheme", cases_scheme), cases_type_global (suffix schemeN name)),
         (("cases", cases), cases_type_global name)];

    val sel_upd_simps = sel_convs' @ upd_convs';
    val sel_upd_defs = sel_defs' @ upd_defs';
    val iffs = [ext_inject]
    val depth = parent_len + 1;
    val final_thy =
      thms_thy
      |> (snd oo PureThy.add_thmss)
          [((Binding.name "simps", sel_upd_simps),
            [Simplifier.simp_add, Nitpick_Const_Simps.add]),
           ((Binding.name "iffs", iffs), [iff_add])]
      |> put_record name (make_record_info args parent fields extension induct_scheme' ext_def)
      |> put_sel_upd names full_moreN depth sel_upd_simps sel_upd_defs (fold_congs', unfold_congs')
      |> add_record_equalities extension_id equality'
      |> add_extinjects ext_inject
      |> add_extsplit extension_name ext_split
      |> add_record_splits extension_id (split_meta', split_object', split_ex', induct_scheme')
      |> add_extfields extension_name (fields @ [(full_moreN, moreT)])
      |> add_fieldext (extension_name, snd extension) (names @ [full_moreN])
      |> Sign.parent_path;

  in final_thy end;


(* add_record *)

(*We do all preparations and error checks here, deferring the real
  work to record_definition.*)
fun gen_add_record prep_typ prep_raw_parent quiet_mode (params, bname) raw_parent raw_fields thy =
  let
    val _ = Theory.requires thy "Record" "record definitions";
    val _ = if quiet_mode then () else writeln ("Defining record " ^ quote bname ^ " ...");

    val ctxt = ProofContext.init thy;


    (* parents *)

    fun prep_inst T = fst (cert_typ ctxt T []);

    val parent = Option.map (apfst (map prep_inst) o prep_raw_parent ctxt) raw_parent
      handle ERROR msg => cat_error msg ("The error(s) above in parent record specification");
    val parents = add_parents thy parent [];

    val init_env =
      (case parent of
        NONE => []
      | SOME (types, _) => fold Term.add_tfreesT types []);


    (* fields *)

    fun prep_field (c, raw_T, mx) env =
      let val (T, env') = prep_typ ctxt raw_T env handle ERROR msg =>
        cat_error msg ("The error(s) above occured in record field " ^ quote c)
      in ((c, T, mx), env') end;

    val (bfields, envir) = fold_map prep_field raw_fields init_env;
    val envir_names = map fst envir;


    (* args *)

    val defaultS = Sign.defaultS thy;
    val args = map (fn x => (x, AList.lookup (op =) envir x |> the_default defaultS)) params;


    (* errors *)

    val name = Sign.full_bname thy bname;
    val err_dup_record =
      if is_none (get_record thy name) then []
      else ["Duplicate definition of record " ^ quote name];

    val err_dup_parms =
      (case duplicates (op =) params of
        [] => []
      | dups => ["Duplicate parameter(s) " ^ commas dups]);

    val err_extra_frees =
      (case subtract (op =) params envir_names of
        [] => []
      | extras => ["Extra free type variable(s) " ^ commas extras]);

    val err_no_fields = if null bfields then ["No fields present"] else [];

    val err_dup_fields =
      (case duplicates (op =) (map #1 bfields) of
        [] => []
      | dups => ["Duplicate field(s) " ^ commas_quote dups]);

    val err_bad_fields =
      if forall (not_equal moreN o #1) bfields then []
      else ["Illegal field name " ^ quote moreN];

    val err_dup_sorts =
      (case duplicates (op =) envir_names of
        [] => []
      | dups => ["Inconsistent sort constraints for " ^ commas dups]);

    val errs =
      err_dup_record @ err_dup_parms @ err_extra_frees @ err_no_fields @
      err_dup_fields @ err_bad_fields @ err_dup_sorts;

    val _ = if null errs then () else error (cat_lines errs);
  in
    thy |> record_definition (args, bname) parent parents bfields
  end
  handle ERROR msg => cat_error msg ("Failed to define record " ^ quote bname);

val add_record = gen_add_record read_typ read_raw_parent;
val add_record_i = gen_add_record cert_typ (K I);


(* setup theory *)

val setup =
  Sign.add_trfuns ([], parse_translation, [], []) #>
  Sign.add_advanced_trfuns ([], adv_parse_translation, [], []) #>
  Simplifier.map_simpset (fn ss =>
    ss addsimprocs [record_simproc, record_upd_simproc, record_eq_simproc]);


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val record_decl =
  P.type_args -- P.name --
    (P.$$$ "=" |-- Scan.option (P.typ --| P.$$$ "+") -- Scan.repeat1 P.const);

val _ =
  OuterSyntax.command "record" "define extensible record" K.thy_decl
    (record_decl >> (fn (x, (y, z)) => Toplevel.theory (add_record false x y z)));

end;

end;

structure Basic_Record: BASIC_RECORD = Record;
open Basic_Record;
