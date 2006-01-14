(*  Title:      HOL/Tools/record_package.ML
    ID:         $Id$
    Author:     Wolfgang Naraschewski, Norbert Schirmer and Markus Wenzel, TU Muenchen

Extensible records with structural subtyping in HOL.
*)

signature BASIC_RECORD_PACKAGE =
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
  val print_record_type_abbr: bool ref
  val print_record_type_as_fields: bool ref
end;

signature RECORD_PACKAGE =
sig
  include BASIC_RECORD_PACKAGE
  val quiet_mode: bool ref
  val record_quick_and_dirty_sensitive: bool ref
  val updateN: string
  val ext_typeN: string
  val last_extT: typ -> (string * typ list) option
  val dest_recTs : typ -> (string * typ list) list
  val get_extT_fields:  theory -> typ -> ((string * typ) list * (string * typ))
  val get_recT_fields:  theory -> typ -> ((string * typ) list * (string * typ))
  val get_extension: theory -> Symtab.key -> (string * typ list) option
  val get_extinjects: theory -> thm list
  val get_simpset: theory -> simpset
  val print_records: theory -> unit
  val add_record: string list * string -> string option -> (string * string * mixfix) list
    -> theory -> theory
  val add_record_i: string list * string -> (typ list * string) option
    -> (string * typ * mixfix) list -> theory -> theory
  val setup: (theory -> theory) list
end;


structure RecordPackage: RECORD_PACKAGE =
struct

val rec_UNIV_I = thm "rec_UNIV_I";
val rec_True_simp = thm "rec_True_simp";
val Pair_eq = thm "Product_Type.Pair_eq";
val atomize_all = thm "HOL.atomize_all";
val atomize_imp = thm "HOL.atomize_imp";
val meta_allE = thm "Pure.meta_allE";
val prop_subst = thm "prop_subst";
val Pair_sel_convs = [fst_conv,snd_conv];



(** name components **)

val rN = "r";
val wN = "w";
val moreN = "more";
val schemeN = "_scheme";
val ext_typeN = "_ext_type";
val extN ="_ext";
val casesN = "_cases";
val ext_dest = "_sel";
val updateN = "_update";
val updN = "_upd";
val schemeN = "_scheme";
val makeN = "make";
val fields_selN = "fields";
val extendN = "extend";
val truncateN = "truncate";

(*see typedef_package.ML*)
val RepN = "Rep_";
val AbsN = "Abs_";

(*** utilities ***)

fun but_last xs = fst (split_last xs);

(* messages *)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;

(* timing *)

fun timeit_msg s x = if !timing then (warning s; timeit x) else x ();
fun timing_msg s = if !timing then warning s else ();

(* syntax *)

fun prune n xs = Library.drop (n, xs);
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

(* morphisms *)

fun mk_RepN name = suffix ext_typeN (prefix_base RepN name);
fun mk_AbsN name = suffix ext_typeN (prefix_base AbsN name);

fun mk_Rep name repT absT  =
  Const (suffix ext_typeN (prefix_base RepN name),absT --> repT);

fun mk_Abs name repT absT =
  Const (mk_AbsN name,repT --> absT);

(* constructor *)

fun mk_extC (name,T) Ts  = (suffix extN name, Ts ---> T);

fun mk_ext (name,T) ts =
  let val Ts = map fastype_of ts
  in list_comb (Const (mk_extC (name,T) Ts),ts) end;

(* cases *)

fun mk_casesC (name,T,vT) Ts = (suffix casesN name, (Ts ---> vT) --> T --> vT)

fun mk_cases (name,T,vT) f =
  let val Ts = binder_types (fastype_of f)
  in Const (mk_casesC (name,T,vT) Ts) $ f end;

(* selector *)

fun mk_selC sT (c,T) = (c,sT --> T);

fun mk_sel s (c,T) =
  let val sT = fastype_of s
  in Const (mk_selC sT (c,T)) $ s end;

(* updates *)

fun mk_updC sfx sT (c,T) = (suffix sfx c, T --> sT --> sT);

fun mk_upd sfx c v s =
  let val sT = fastype_of s;
      val vT = fastype_of v;
  in Const (mk_updC sfx sT (c, vT)) $ v $ s end;

(* types *)

fun dest_recT (typ as Type (c_ext_type, Ts as (T::_))) =
      (case try (unsuffix ext_typeN) c_ext_type of
        NONE => raise TYPE ("RecordPackage.dest_recT", [typ], [])
      | SOME c => ((c, Ts), List.last Ts))
  | dest_recT typ = raise TYPE ("RecordPackage.dest_recT", [typ], []);

fun is_recT T =
  (case try dest_recT T of NONE => false | SOME _ => true);

fun dest_recTs T =
  let val ((c, Ts), U) = dest_recT T
  in (c, Ts) :: dest_recTs U
  end handle TYPE _ => [];

fun last_extT T =
  let val ((c, Ts), U) = dest_recT T
  in (case last_extT U of
        NONE => SOME (c,Ts)
      | SOME l => SOME l)
  end handle TYPE _ => NONE

fun rec_id i T =
  let val rTs = dest_recTs T
      val rTs' = if i < 0 then rTs else Library.take (i,rTs)
  in Library.foldl (fn (s,(c,T)) => s ^ c) ("",rTs') end;

(*** extend theory by record definition ***)

(** record info **)

(* type record_info and parent_info  *)

type record_info =
 {args: (string * sort) list,
  parent: (typ list * string) option,
  fields: (string * typ) list,
  extension: (string * typ list),
  induct: thm
 };

fun make_record_info args parent fields extension induct =
 {args = args, parent = parent, fields = fields, extension = extension,
  induct = induct}: record_info;


type parent_info =
 {name: string,
  fields: (string * typ) list,
  extension: (string * typ list),
  induct: thm
};

fun make_parent_info name fields extension induct =
 {name = name, fields = fields, extension = extension, induct = induct}: parent_info;

(* data kind 'HOL/record' *)

type record_data =
 {records: record_info Symtab.table,
  sel_upd:
   {selectors: unit Symtab.table,
    updates: string Symtab.table,
    simpset: Simplifier.simpset},
  equalities: thm Symtab.table,
  extinjects: thm list,
  extsplit: thm Symtab.table, (* maps extension name to split rule *)
  splits: (thm*thm*thm*thm) Symtab.table,    (* !!,!,EX - split-equalities,induct rule *)
  extfields: (string*typ) list Symtab.table, (* maps extension to its fields *)
  fieldext: (string*typ list) Symtab.table   (* maps field to its extension *)
};

fun make_record_data
      records sel_upd equalities extinjects extsplit splits extfields fieldext =
 {records = records, sel_upd = sel_upd,
  equalities = equalities, extinjects=extinjects, extsplit = extsplit, splits = splits,
  extfields = extfields, fieldext = fieldext }: record_data;

structure RecordsData = TheoryDataFun
(struct
  val name = "HOL/records";
  type T = record_data;

  val empty =
    make_record_data Symtab.empty
      {selectors = Symtab.empty, updates = Symtab.empty, simpset = HOL_basic_ss}
       Symtab.empty [] Symtab.empty Symtab.empty Symtab.empty Symtab.empty;

  val copy = I;
  val extend = I;
  fun merge _
   ({records = recs1,
     sel_upd = {selectors = sels1, updates = upds1, simpset = ss1},
     equalities = equalities1,
     extinjects = extinjects1,
     extsplit = extsplit1,
     splits = splits1,
     extfields = extfields1,
     fieldext = fieldext1},
    {records = recs2,
     sel_upd = {selectors = sels2, updates = upds2, simpset = ss2},
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
        simpset = Simplifier.merge_ss (ss1, ss2)}
      (Symtab.merge Thm.eq_thm (equalities1, equalities2))
      (gen_merge_lists Thm.eq_thm extinjects1 extinjects2)
      (Symtab.merge Thm.eq_thm (extsplit1,extsplit2))
      (Symtab.merge (fn ((a,b,c,d),(w,x,y,z))
                     => Thm.eq_thm (a,w) andalso Thm.eq_thm (b,x) andalso
                        Thm.eq_thm (c,y) andalso Thm.eq_thm (d,z))
                    (splits1, splits2))
      (Symtab.merge (K true) (extfields1,extfields2))
      (Symtab.merge (K true) (fieldext1,fieldext2));

  fun print sg ({records = recs, ...}: record_data) =
    let
      val prt_typ = Sign.pretty_typ sg;

      fun pretty_parent NONE = []
        | pretty_parent (SOME (Ts, name)) =
            [Pretty.block [prt_typ (Type (name, Ts)), Pretty.str " +"]];

      fun pretty_field (c, T) = Pretty.block
        [Pretty.str (Sign.extern_const sg c), Pretty.str " ::",
          Pretty.brk 1, Pretty.quote (prt_typ T)];

      fun pretty_record (name, {args, parent, fields, ...}: record_info) =
        Pretty.block (Pretty.fbreaks (Pretty.block
          [prt_typ (Type (name, map TFree args)), Pretty.str " = "] ::
          pretty_parent parent @ map pretty_field fields));
    in map pretty_record (Symtab.dest recs) |> Pretty.chunks |> Pretty.writeln end;
end);

val print_records = RecordsData.print;


(* access 'records' *)

val get_record = Symtab.lookup o #records o RecordsData.get;

fun put_record name info thy =
  let
    val {records, sel_upd, equalities, extinjects,extsplit,splits,extfields,fieldext} =
          RecordsData.get thy;
    val data = make_record_data (Symtab.update (name, info) records)
      sel_upd equalities extinjects extsplit splits extfields fieldext;
  in RecordsData.put data thy end;

(* access 'sel_upd' *)

val get_sel_upd = #sel_upd o RecordsData.get;

val is_selector = Symtab.defined o #selectors o get_sel_upd;
val get_updates = Symtab.lookup o #updates o get_sel_upd;
fun get_simpset thy = Simplifier.theory_context thy (#simpset (get_sel_upd thy));

fun put_sel_upd names simps thy =
  let
    val sels = map (rpair ()) names;
    val upds = map (suffix updateN) names ~~ names;

    val {records, sel_upd = {selectors, updates, simpset},
      equalities, extinjects, extsplit, splits, extfields,fieldext} = RecordsData.get thy;
    val data = make_record_data records
      {selectors = Symtab.extend (selectors, sels),
        updates = Symtab.extend (updates, upds),
        simpset = Simplifier.addsimps (simpset, simps)}
       equalities extinjects extsplit splits extfields fieldext;
  in RecordsData.put data thy end;

(* access 'equalities' *)

fun add_record_equalities name thm thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields,fieldext} =
          RecordsData.get thy;
    val data = make_record_data records sel_upd
           (Symtab.update_new (name, thm) equalities) extinjects extsplit
           splits extfields fieldext;
  in RecordsData.put data thy end;

val get_equalities =Symtab.lookup o #equalities o RecordsData.get;

(* access 'extinjects' *)

fun add_extinjects thm thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields,fieldext} =
          RecordsData.get thy;
    val data = make_record_data records sel_upd equalities (extinjects@[thm]) extsplit
                 splits extfields fieldext;
  in RecordsData.put data thy end;

fun get_extinjects sg = #extinjects (RecordsData.get sg);

(* access 'extsplit' *)

fun add_extsplit name thm thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields,fieldext} =
          RecordsData.get thy;
    val data = make_record_data records sel_upd
      equalities extinjects (Symtab.update_new (name, thm) extsplit) splits
      extfields fieldext;
  in RecordsData.put data thy end;

val get_extsplit = Symtab.lookup o #extsplit o RecordsData.get;

(* access 'splits' *)

fun add_record_splits name thmP thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields,fieldext} =
          RecordsData.get thy;
    val data = make_record_data records sel_upd
      equalities extinjects extsplit (Symtab.update_new (name, thmP) splits)
      extfields fieldext;
  in RecordsData.put data thy end;

val get_splits = Symtab.lookup o #splits o RecordsData.get;



(* extension of a record name *)
val get_extension =
  Option.map #extension oo (Symtab.lookup o #records o RecordsData.get);


(* access 'extfields' *)

fun add_extfields name fields thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit,splits, extfields, fieldext} =
          RecordsData.get thy;
    val data = make_record_data records sel_upd
         equalities extinjects extsplit splits
         (Symtab.update_new (name, fields) extfields) fieldext;
  in RecordsData.put data thy end;

val get_extfields = Symtab.lookup o #extfields o RecordsData.get;

fun get_extT_fields sg T =
  let
    val ((name,Ts),moreT) = dest_recT T;
    val recname = let val (nm::recn::rst) = rev (NameSpace.unpack name)
                  in NameSpace.pack (rev (nm::rst)) end;
    val midx = maxidx_of_typs (moreT::Ts);
    fun varify (a, S) = TVar ((a, midx), S);
    val varifyT = map_type_tfree varify;
    val {records,extfields,...} = RecordsData.get sg;
    val (flds,(more,_)) = split_last (Symtab.lookup_multi extfields name);
    val args = map varifyT (snd (#extension (the (Symtab.lookup records recname))));

    val (subst,_) = fold (Sign.typ_unify sg) (but_last args ~~ but_last Ts) (Vartab.empty,0);
    val flds' = map (apsnd ((Envir.norm_type subst) o varifyT)) flds;
  in (flds',(more,moreT)) end;

fun get_recT_fields sg T =
  let
    val (root_flds,(root_more,root_moreT)) = get_extT_fields sg T;
    val (rest_flds,rest_more) =
           if is_recT root_moreT then get_recT_fields sg root_moreT
           else ([],(root_more,root_moreT));
  in (root_flds@rest_flds,rest_more) end;


(* access 'fieldext' *)

fun add_fieldext extname_types fields thy =
  let
    val {records, sel_upd, equalities, extinjects, extsplit, splits, extfields, fieldext} =
           RecordsData.get thy;
    val fieldext' =
      fold (fn field => Symtab.update_new (field, extname_types)) fields fieldext;
    val data=make_record_data records sel_upd equalities extinjects extsplit
              splits extfields fieldext';
  in RecordsData.put data thy end;


val get_fieldext = Symtab.lookup o #fieldext o RecordsData.get;

(* parent records *)

fun add_parents thy NONE parents = parents
  | add_parents thy (SOME (types, name)) parents =
      let
        val sign = Theory.sign_of thy;
        fun err msg = error (msg ^ " parent record " ^ quote name);

        val {args, parent, fields, extension, induct} =
          (case get_record thy name of SOME info => info | NONE => err "Unknown");
        val _ = if length types <> length args then err "Bad number of arguments for" else ();

        fun bad_inst ((x, S), T) =
          if Sign.of_sort sign (T, S) then NONE else SOME x
        val bads = List.mapPartial bad_inst (args ~~ types);

        val inst = map fst args ~~ types;
        val subst = Term.map_type_tfree (the o AList.lookup (op =) inst o fst);
        val parent' = Option.map (apfst (map subst)) parent;
        val fields' = map (apsnd subst) fields;
        val extension' = apsnd (map subst) extension;
      in
        conditional (not (null bads)) (fn () =>
          err ("Ill-sorted instantiation of " ^ commas bads ^ " in"));
        add_parents thy parent'
          (make_parent_info name fields' extension' induct::parents)
      end;


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


fun record_update_tr [t, u] =
      foldr (op $) t (rev (gen_fields_tr "_updates" "_update" updateN u))
  | record_update_tr ts = raise TERM ("record_update_tr", ts);

fun update_name_tr (Free (x, T) :: ts) = Free (suffix updateN x, T) $$ ts
  | update_name_tr (Const (x, T) :: ts) = Const (suffix updateN x, T) $$ ts
  | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
      (c $ update_name_tr [t] $ (Syntax.const "fun" $ ty $ Syntax.const "dummy")) $$ ts
  | update_name_tr ts = raise TERM ("update_name_tr", ts);

fun dest_ext_field mark (t as (Const (c,_) $ Const (name,_) $ arg)) =
     if c = mark then (name,arg) else raise TERM ("dest_ext_field: " ^ mark, [t])
  | dest_ext_field _ t = raise TERM ("dest_ext_field", [t])

fun dest_ext_fields sep mark (trm as (Const (c,_) $ t $ u)) =
     if c = sep then dest_ext_field mark t::dest_ext_fields sep mark u
     else [dest_ext_field mark trm]
  | dest_ext_fields _ mark t = [dest_ext_field mark t]

fun gen_ext_fields_tr sep mark sfx more sg t =
  let
    val msg = "error in record input: ";
    val fieldargs = dest_ext_fields sep mark t;
    fun splitargs (field::fields) ((name,arg)::fargs) =
          if can (unsuffix name) field
          then let val (args,rest) = splitargs fields fargs
               in (arg::args,rest) end
          else raise TERM (msg ^ "expecting field " ^ field ^ " but got " ^ name, [t])
      | splitargs [] (fargs as (_::_)) = ([],fargs)
      | splitargs (_::_) [] = raise TERM (msg ^ "expecting more fields", [t])
      | splitargs _ _ = ([],[]);

    fun mk_ext (fargs as (name,arg)::_) =
         (case get_fieldext sg (Sign.intern_const sg name) of
            SOME (ext,_) => (case get_extfields sg ext of
                               SOME flds
                                 => let val (args,rest) =
                                               splitargs (map fst (but_last flds)) fargs;
                                        val more' = mk_ext rest;
                                    in list_comb (Syntax.const (suffix sfx ext),args@[more'])
                                    end
                             | NONE => raise TERM(msg ^ "no fields defined for "
                                                   ^ ext,[t]))
          | NONE => raise TERM (msg ^ name ^" is no proper field",[t]))
      | mk_ext [] = more

  in mk_ext fieldargs end;

fun gen_ext_type_tr sep mark sfx more sg t =
  let
    val msg = "error in record-type input: ";
    val fieldargs = dest_ext_fields sep mark t;
    fun splitargs (field::fields) ((name,arg)::fargs) =
          if can (unsuffix name) field
          then let val (args,rest) = splitargs fields fargs
               in (arg::args,rest) end
          else raise TERM (msg ^ "expecting field " ^ field ^ " but got " ^ name, [t])
      | splitargs [] (fargs as (_::_)) = ([],fargs)
      | splitargs (_::_) [] = raise TERM (msg ^ "expecting more fields", [t])
      | splitargs _ _ = ([],[]);

    fun get_sort xs n = AList.lookup (op =) xs n |> the_default (Sign.defaultS sg);

    fun to_type t = Sign.certify_typ sg
                       (Sign.intern_typ sg
                         (Syntax.typ_of_term (get_sort (Syntax.raw_term_sorts t)) I t));

    fun mk_ext (fargs as (name,arg)::_) =
         (case get_fieldext sg (Sign.intern_const sg name) of
            SOME (ext,alphas) =>
              (case get_extfields sg ext of
                 SOME flds
                  => (let
                       val flds' = but_last flds;
                       val types = map snd flds';
                       val (args,rest) = splitargs (map fst flds') fargs;
                       val vartypes = map Type.varifyT types;
                       val argtypes = map to_type args;
                       val (subst,_) = fold (Sign.typ_unify sg) (vartypes ~~ argtypes)
                                            (Vartab.empty,0);
                       val alphas' = map ((Syntax.term_of_typ (! Syntax.show_sorts)) o
                                          Envir.norm_type subst o Type.varifyT)
                                         (but_last alphas);

                       val more' = mk_ext rest;
                     in list_comb (Syntax.const (suffix sfx ext),alphas'@[more'])
                     end handle TUNIFY => raise
                           TERM (msg ^ "type is no proper record (extension)", [t]))
               | NONE => raise TERM (msg ^ "no fields defined for " ^ ext,[t]))
          | NONE => raise TERM (msg ^ name ^" is no proper field",[t]))
      | mk_ext [] = more

  in mk_ext fieldargs end;

fun gen_adv_record_tr sep mark sfx unit sg [t] =
      gen_ext_fields_tr sep mark sfx unit sg t
  | gen_adv_record_tr _ _ _ _ _ ts = raise TERM ("gen_record_tr", ts);

fun gen_adv_record_scheme_tr sep mark sfx sg [t, more] =
      gen_ext_fields_tr sep mark sfx more sg t
  | gen_adv_record_scheme_tr _ _ _ _ ts = raise TERM ("gen_record_scheme_tr", ts);

fun gen_adv_record_type_tr sep mark sfx unit sg [t] =
      gen_ext_type_tr sep mark sfx unit sg t
  | gen_adv_record_type_tr _ _ _ _ _ ts = raise TERM ("gen_record_tr", ts);

fun gen_adv_record_type_scheme_tr sep mark sfx sg [t, more] =
      gen_ext_type_tr sep mark sfx more sg t
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
 [("_record",adv_record_tr),
  ("_record_scheme",adv_record_scheme_tr),
  ("_record_type",adv_record_type_tr),
  ("_record_type_scheme",adv_record_type_scheme_tr)];

(* print translations *)

val print_record_type_abbr = ref true;
val print_record_type_as_fields = ref true;

fun gen_field_upds_tr' mark sfx (tm as Const (name_field, _) $ t $ u) =
    (case try (unsuffix sfx) name_field of
      SOME name =>
        apfst (cons (Syntax.const mark $ Syntax.free name $ t)) (gen_field_upds_tr' mark sfx u)
     | NONE => ([], tm))
  | gen_field_upds_tr' _ _ tm = ([], tm);

fun record_update_tr' tm =
  let val (ts, u) = gen_field_upds_tr' "_update" updateN tm in
    Syntax.const "_record_update" $ u $
      foldr1 (fn (v, w) => Syntax.const "_updates" $ v $ w) (rev ts)
  end;

fun gen_field_tr' sfx tr' name =
  let val name_sfx = suffix sfx name
  in (name_sfx, fn [t, u] => tr' (Syntax.const name_sfx $ t $ u) | _ => raise Match) end;

fun record_tr' sep mark record record_scheme unit sg t =
  let
    fun field_lst t =
      (case strip_comb t of
        (Const (ext,_),args as (_::_))
         => (case try (unsuffix extN) (Sign.intern_const sg ext) of
               SOME ext'
               => (case get_extfields sg ext' of
                     SOME flds
                     => (let
                          val (f::fs) = but_last (map fst flds);
                          val flds' = Sign.extern_const sg f :: map NameSpace.base fs;
                          val (args',more) = split_last args;
                         in (flds'~~args')@field_lst more end
                         handle UnequalLengths => [("",t)])
                   | NONE => [("",t)])
             | NONE => [("",t)])
       | _ => [("",t)])

    val (flds,(_,more)) = split_last (field_lst t);
    val flds' = map (fn (n,t)=>Syntax.const mark$Syntax.const n$t) flds;
    val flds'' = foldr1 (fn (x,y) => Syntax.const sep$x$y) flds';

  in if null flds then raise Match
     else if unit more
          then Syntax.const record$flds''
          else Syntax.const record_scheme$flds''$more
  end

fun gen_record_tr' name =
  let val name_sfx = suffix extN name;
      val unit = (fn Const ("Unity",_) => true | _ => false);
      fun tr' sg ts = record_tr' "_fields" "_field" "_record" "_record_scheme" unit sg
                       (list_comb (Syntax.const name_sfx,ts))
  in (name_sfx,tr')
  end

fun print_translation names =
  map (gen_field_tr' updateN record_update_tr') names;

(* record_type_abbr_tr' tries to reconstruct the record name type abbreviation from *)
(* the (nested) extension types.                                                    *)
fun record_type_abbr_tr' default_tr' abbr alphas zeta lastExt schemeT sg tm =
  let
      (* tm is term representation of a (nested) field type. We first reconstruct the      *)
      (* type from tm so that we can continue on the type level rather then the term level.*)

      fun get_sort xs n = AList.lookup (op =) xs n |> the_default (Sign.defaultS sg);

      (* WORKAROUND:
       * If a record type occurs in an error message of type inference there
       * may be some internal frees donoted by ??:
       * (Const "_tfree",_)$Free ("??'a",_).

       * This will unfortunately be translated to Type ("??'a",[]) instead of
       * TFree ("??'a",_) by typ_of_term, which will confuse unify below.
       * fixT works around.
       *)
      fun fixT (T as Type (x,[])) =
            if String.isPrefix "??'" x then TFree (x,Sign.defaultS sg) else T
        | fixT (Type (x,xs)) = Type (x,map fixT xs)
        | fixT T = T;

      val T = fixT (Sign.intern_typ sg
                      (Syntax.typ_of_term (get_sort (Syntax.raw_term_sorts tm)) I tm));

      fun mk_type_abbr subst name alphas =
          let val abbrT = Type (name, map (fn a => TVar ((a, 0), Sign.defaultS sg)) alphas);
          in Syntax.term_of_typ (! Syntax.show_sorts)
               (Sign.extern_typ sg (Envir.norm_type subst abbrT)) end;

      fun unify rT T = fst (Sign.typ_unify sg (Type.varifyT rT,T) (Vartab.empty,0));

   in if !print_record_type_abbr
      then (case last_extT T of
             SOME (name,_)
              => if name = lastExt
                 then
                  (let
                     val subst = unify schemeT T
                   in
                    if HOLogic.is_unitT (Envir.norm_type subst (TVar((zeta,0),Sign.defaultS sg)))
                    then mk_type_abbr subst abbr alphas
                    else mk_type_abbr subst (suffix schemeN abbr) (alphas@[zeta])
                   end handle TUNIFY => default_tr' sg tm)
                 else raise Match (* give print translation of specialised record a chance *)
            | _ => raise Match)
       else default_tr' sg tm
  end

fun record_type_tr' sep mark record record_scheme sg t =
  let
    fun get_sort xs n = AList.lookup (op =) xs n |> the_default (Sign.defaultS sg);

    val T = Sign.intern_typ sg (Syntax.typ_of_term (get_sort (Syntax.raw_term_sorts t)) I t)

    fun term_of_type T = Syntax.term_of_typ (!Syntax.show_sorts) (Sign.extern_typ sg T);

    fun field_lst T =
      (case T of
        Type (ext,args)
         => (case try (unsuffix ext_typeN) ext of
               SOME ext'
               => (case get_extfields sg ext' of
                     SOME flds
                     => (case get_fieldext sg (fst (hd flds)) of
                           SOME (_,alphas)
                           => (let
                                val (f::fs) = but_last flds;
                                val flds' = apfst (Sign.extern_const sg) f
                                            ::map (apfst NameSpace.base) fs;
                                val (args',more) = split_last args;
                                val alphavars = map Type.varifyT (but_last alphas);
                                val (subst,_)= fold (Sign.typ_unify sg) (alphavars~~args')
                                                    (Vartab.empty,0);
                                val flds'' =map (apsnd (Envir.norm_type subst o Type.varifyT))
                                                flds';
                              in flds''@field_lst more end
                              handle TUNIFY         => [("",T)]
                                   | UnequalLengths => [("",T)])
                         | NONE => [("",T)])
                   | NONE => [("",T)])
             | NONE => [("",T)])
        | _ => [("",T)])

    val (flds,(_,moreT)) = split_last (field_lst T);
    val flds' = map (fn (n,T)=>Syntax.const mark$Syntax.const n$term_of_type T) flds;
    val flds'' = foldr1 (fn (x,y) => Syntax.const sep$x$y) flds';

  in if not (!print_record_type_as_fields) orelse null flds then raise Match
     else if moreT = HOLogic.unitT
          then Syntax.const record$flds''
          else Syntax.const record_scheme$flds''$term_of_type moreT
  end


fun gen_record_type_tr' name =
  let val name_sfx = suffix ext_typeN name;
      fun tr' sg ts = record_type_tr' "_field_types" "_field_type"
                       "_record_type" "_record_type_scheme" sg
                       (list_comb (Syntax.const name_sfx,ts))
  in (name_sfx,tr')
  end


fun gen_record_type_abbr_tr' abbr alphas zeta lastExt schemeT name =
  let val name_sfx = suffix ext_typeN name;
      val default_tr' = record_type_tr' "_field_types" "_field_type"
                               "_record_type" "_record_type_scheme"
      fun tr' sg ts = record_type_abbr_tr' default_tr' abbr alphas zeta lastExt schemeT sg
                         (list_comb (Syntax.const name_sfx,ts))
  in (name_sfx, tr') end;

(** record simprocs **)

val record_quick_and_dirty_sensitive = ref false;


fun quick_and_dirty_prove stndrd sg asms prop tac =
  if !record_quick_and_dirty_sensitive andalso !quick_and_dirty
  then Goal.prove sg [] [] (Logic.list_implies (map Logic.varify asms,Logic.varify prop))
        (K (SkipProof.cheat_tac HOL.thy))
        (* standard can take quite a while for large records, thats why
         * we varify the proposition manually here.*)
  else let val prf = Goal.prove sg [] asms prop tac;
       in if stndrd then standard prf else prf end;

fun quick_and_dirty_prf noopt opt () =
      if !record_quick_and_dirty_sensitive andalso !quick_and_dirty
      then noopt ()
      else opt ();


fun prove_split_simp sg ss T prop =
  let
    val {sel_upd={simpset,...},extsplit,...} = RecordsData.get sg;
    val extsplits =
            Library.foldl (fn (thms,(n,_)) => the_list (Symtab.lookup extsplit n) @ thms)
                    ([],dest_recTs T);
    val thms = (case get_splits sg (rec_id (~1) T) of
                   SOME (all_thm,_,_,_) =>
                     all_thm::(case extsplits of [thm] => [] | _ => extsplits)
                              (* [thm] is the same as all_thm *)
                 | NONE => extsplits)
  in
    quick_and_dirty_prove true sg [] prop
      (fn _ => simp_tac (Simplifier.inherit_context ss simpset addsimps thms) 1)
  end;


local
fun eq (s1:string) (s2:string) = (s1 = s2);
fun has_field extfields f T =
     exists (fn (eN,_) => exists (eq f o fst) (Symtab.lookup_multi extfields eN))
       (dest_recTs T);
in
(* record_simproc *)
(* Simplifies selections of an record update:
 *  (1)  S (r(|S:=k|)) = k respectively
 *  (2)  S (r(|X:=k|)) = S r
 * The simproc skips multiple updates at once, eg:
 *  S (r (|S:=k,X:=2,Y:=3|)) = k
 * But be careful in (2) because of the extendibility of records.
 * - If S is a more-selector we have to make sure that the update on component
 *   X does not affect the selected subrecord.
 * - If X is a more-selector we have to make sure that S is not in the updated
 *   subrecord.
 *)
val record_simproc =
  Simplifier.simproc HOL.thy "record_simp" ["x"]
    (fn sg => fn ss => fn t =>
      (case t of (sel as Const (s, Type (_,[domS,rangeS])))$
                   ((upd as Const (u,Type(_,[_,Type (_,[rT,_])]))) $ k $ r)=>
        if is_selector sg s then
          (case get_updates sg u of SOME u_name =>
            let
              val {sel_upd={updates,...},extfields,...} = RecordsData.get sg;

              fun mk_eq_terms ((upd as Const (u,Type(_,[kT,_]))) $ k $ r) =
                  (case Symtab.lookup updates u of
                     NONE => NONE
                   | SOME u_name
                     => if u_name = s
                        then let
                               val rv = ("r",rT)
                               val rb = Bound 0
                               val kv = ("k",kT)
                               val kb = Bound 1
                             in SOME (upd$kb$rb,kb,[kv,rv],true) end
                        else if has_field extfields u_name rangeS
                             orelse has_field extfields s kT
                             then NONE
                             else (case mk_eq_terms r of
                                     SOME (trm,trm',vars,update_s)
                                     => let
                                          val kv = ("k",kT)
                                          val kb = Bound (length vars)
                                        in SOME (upd$kb$trm,trm',kv::vars,update_s) end
                                   | NONE
                                     => let
                                          val rv = ("r",rT)
                                          val rb = Bound 0
                                          val kv = ("k",kT)
                                          val kb = Bound 1
                                        in SOME (upd$kb$rb,rb,[kv,rv],false) end))
                | mk_eq_terms r = NONE
            in
              (case mk_eq_terms (upd$k$r) of
                 SOME (trm,trm',vars,update_s)
                 => if update_s
                    then SOME (prove_split_simp sg ss domS
                                 (list_all(vars,(equals rangeS$(sel$trm)$trm'))))
                    else SOME (prove_split_simp sg ss domS
                                 (list_all(vars,(equals rangeS$(sel$trm)$(sel$trm')))))
               | NONE => NONE)
            end
          | NONE => NONE)
        else NONE
      | _ => NONE));

(* record_upd_simproc *)
(* simplify multiple updates:
 *  (1)  "r(|M:=3,N:=1,M:=2,N:=4|) == r(|M:=2,N:=4|)"
 *  (2)  "r(|M:= M r|) = r"
 * For (2) special care of "more" updates has to be taken:
 *    r(|more := m; A := A r|)
 * If A is contained in the fields of m we cannot remove the update A := A r!
 * (But r(|more := r; A := A (r(|more := r|))|) = r(|more := r|)
*)
val record_upd_simproc =
  Simplifier.simproc HOL.thy "record_upd_simp" ["x"]
    (fn sg => fn ss => fn t =>
      (case t of ((upd as Const (u, Type(_,[_,Type(_,[rT,_])]))) $ k $ r) =>
         let datatype ('a,'b) calc = Init of 'b | Inter of 'a
             val {sel_upd={selectors,updates,...},extfields,...} = RecordsData.get sg;

             (*fun mk_abs_var x t = (x, fastype_of t);*)
             fun sel_name u = NameSpace.base (unsuffix updateN u);

             fun seed s (upd as Const (more,Type(_,[mT,_]))$ k $ r) =
                  if has_field extfields s mT then upd else seed s r
               | seed _ r = r;

             fun grow u uT k kT vars (sprout,skeleton) =
                   if sel_name u = moreN
                   then let val kv = ("k", kT);
                            val kb = Bound (length vars);
                        in ((Const (u,uT)$k$sprout,Const (u,uT)$kb$skeleton),kv::vars) end
                   else ((sprout,skeleton),vars);

             fun is_upd_same (sprout,skeleton) u ((sel as Const (s,_))$r) =
                   if (unsuffix updateN u) = s andalso (seed s sprout) = r
                   then SOME (sel,seed s skeleton)
                   else NONE
               | is_upd_same _ _ _ = NONE

             fun init_seed r = ((r,Bound 0), [("r", rT)]);

             (* mk_updterm returns either
              *  - Init (orig-term, orig-term-skeleton, vars) if no optimisation can be made,
              *     where vars are the bound variables in the skeleton
              *  - Inter (orig-term-skeleton,simplified-term-skeleton,
              *           vars, (term-sprout, skeleton-sprout))
              *     where "All vars. orig-term-skeleton = simplified-term-skeleton" is
              *     the desired simplification rule,
              *     the sprouts accumulate the "more-updates" on the way from the seed
              *     to the outermost update. It is only relevant to calculate the
              *     possible simplification for (2)
              * The algorithm first walks down the updates to the seed-record while
              * memorising the updates in the already-table. While walking up the
              * updates again, the optimised term is constructed.
              *)
             fun mk_updterm upds already
                 (t as ((upd as Const (u,uT as (Type (_,[kT,_])))) $ k $ r)) =
                 if Symtab.defined upds u
                 then let
                         fun rest already = mk_updterm upds already
                      in if u mem_string already
                         then (case (rest already r) of
                                 Init ((sprout,skel),vars) =>
                                 let
                                   val kv = (sel_name u, kT);
                                   val kb = Bound (length vars);
                                   val (sprout',vars')= grow u uT k kT (kv::vars) (sprout,skel);
                                 in Inter (upd$kb$skel,skel,vars',sprout') end
                               | Inter (trm,trm',vars,sprout) =>
                                 let
                                   val kv = (sel_name u, kT);
                                   val kb = Bound (length vars);
                                   val (sprout',vars') = grow u uT k kT (kv::vars) sprout;
                                 in Inter(upd$kb$trm,trm',kv::vars',sprout') end)
                         else
                          (case rest (u::already) r of
                             Init ((sprout,skel),vars) =>
                              (case is_upd_same (sprout,skel) u k of
                                 SOME (sel,skel') =>
                                 let
                                   val (sprout',vars') = grow u uT k kT vars (sprout,skel);
                                  in Inter(upd$(sel$skel')$skel,skel,vars',sprout') end
                               | NONE =>
                                 let
                                   val kv = (sel_name u, kT);
                                   val kb = Bound (length vars);
                                 in Init ((upd$k$sprout,upd$kb$skel),kv::vars) end)
                           | Inter (trm,trm',vars,sprout) =>
                               (case is_upd_same sprout u k of
                                  SOME (sel,skel) =>
                                  let
                                    val (sprout',vars') = grow u uT k kT vars sprout
                                  in Inter(upd$(sel$skel)$trm,trm',vars',sprout') end
                                | NONE =>
                                  let
                                    val kv = (sel_name u, kT)
                                    val kb = Bound (length vars)
                                    val (sprout',vars') = grow u uT k kT (kv::vars) sprout
                                  in Inter (upd$kb$trm,upd$kb$trm',vars',sprout') end))
                      end
                 else Init (init_seed t)
               | mk_updterm _ _ t = Init (init_seed t);

         in (case mk_updterm updates [] t of
               Inter (trm,trm',vars,_)
                => SOME (prove_split_simp sg ss rT
                          (list_all(vars,(equals rT$trm$trm'))))
             | _ => NONE)
         end
       | _ => NONE));
end

(* record_eq_simproc *)
(* looks up the most specific record-equality.
 * Note on efficiency:
 * Testing equality of records boils down to the test of equality of all components.
 * Therefore the complexity is: #components * complexity for single component.
 * Especially if a record has a lot of components it may be better to split up
 * the record first and do simplification on that (record_split_simp_tac).
 * e.g. r(|lots of updates|) = x
 *
 *               record_eq_simproc       record_split_simp_tac
 * Complexity: #components * #updates     #updates
 *
 *)
val record_eq_simproc =
  Simplifier.simproc HOL.thy "record_eq_simp" ["r = s"]
    (fn sg => fn _ => fn t =>
      (case t of Const ("op =", Type (_, [T, _])) $ _ $ _ =>
        (case rec_id (~1) T of
           "" => NONE
         | name => (case get_equalities sg name of
                                NONE => NONE
                              | SOME thm => SOME (thm RS Eq_TrueI)))
       | _ => NONE));

(* record_split_simproc *)
(* splits quantified occurrences of records, for which P holds. P can peek on the
 * subterm starting at the quantified occurrence of the record (including the quantifier)
 * P t = 0: do not split
 * P t = ~1: completely split
 * P t > 0: split up to given bound of record extensions
 *)
fun record_split_simproc P =
  Simplifier.simproc HOL.thy "record_split_simp" ["x"]
    (fn sg => fn _ => fn t =>
      (case t of (Const (quantifier, Type (_, [Type (_, [T, _]), _])))$trm =>
         if quantifier = "All" orelse quantifier = "all" orelse quantifier = "Ex"
         then (case rec_id (~1) T of
                 "" => NONE
               | name
                  => let val split = P t
                     in if split <> 0 then
                        (case get_splits sg (rec_id split T) of
                              NONE => NONE
                            | SOME (all_thm, All_thm, Ex_thm,_)
                               => SOME (case quantifier of
                                          "all" => all_thm
                                        | "All" => All_thm RS HOL.eq_reflection
                                        | "Ex"  => Ex_thm RS HOL.eq_reflection
                                        | _     => error "record_split_simproc"))
                        else NONE
                      end)
         else NONE
       | _ => NONE))

val record_ex_sel_eq_simproc =
  Simplifier.simproc HOL.thy "record_ex_sel_eq_simproc" ["Ex t"]
    (fn sg => fn ss => fn t =>
       let
         fun prove prop =
           quick_and_dirty_prove true sg [] prop
             (fn _ => simp_tac (Simplifier.inherit_context ss (get_simpset sg)
               addsimps simp_thms addsimprocs [record_split_simproc (K ~1)]) 1);

         fun mkeq (lr,Teq,(sel,Tsel),x) i =
              if is_selector sg sel then
                 let val x' = if not (loose_bvar1 (x,0))
                              then Free ("x" ^ string_of_int i, range_type Tsel)
                              else raise TERM ("",[x]);
                     val sel' = Const (sel,Tsel)$Bound 0;
                     val (l,r) = if lr then (sel',x') else (x',sel');
                  in Const ("op =",Teq)$l$r end
              else raise TERM ("",[Const (sel,Tsel)]);

         fun dest_sel_eq (Const ("op =",Teq)$(Const (sel,Tsel)$Bound 0)$X) =
                           (true,Teq,(sel,Tsel),X)
           | dest_sel_eq (Const ("op =",Teq)$X$(Const (sel,Tsel)$Bound 0)) =
                           (false,Teq,(sel,Tsel),X)
           | dest_sel_eq _ = raise TERM ("",[]);

       in
         (case t of
           (Const ("Ex",Tex)$Abs(s,T,t)) =>
             (let val eq = mkeq (dest_sel_eq t) 0;
                 val prop = list_all ([("r",T)],
                              Logic.mk_equals (Const ("Ex",Tex)$Abs(s,T,eq),
                                               HOLogic.true_const));
             in SOME (prove prop) end
             handle TERM _ => NONE)
          | _ => NONE)
         end)




local
val inductive_atomize = thms "induct_atomize";
val inductive_rulify = thms "induct_rulify";
in
(* record_split_simp_tac *)
(* splits (and simplifies) all records in the goal for which P holds.
 * For quantified occurrences of a record
 * P can peek on the whole subterm (including the quantifier); for free variables P
 * can only peek on the variable itself.
 * P t = 0: do not split
 * P t = ~1: completely split
 * P t > 0: split up to given bound of record extensions
 *)
fun record_split_simp_tac thms P i st =
  let
    val sg = Thm.sign_of_thm st;

    val has_rec = exists_Const
      (fn (s, Type (_, [Type (_, [T, _]), _])) =>
          (s = "all" orelse s = "All" orelse s = "Ex") andalso is_recT T
        | _ => false);

    val goal = nth (Thm.prems_of st) (i - 1);
    val frees = List.filter (is_recT o type_of) (term_frees goal);

    fun mk_split_free_tac free induct_thm i =
        let val cfree = cterm_of sg free;
            val (_$(_$r)) = concl_of induct_thm;
            val crec = cterm_of sg r;
            val thm  = cterm_instantiate [(crec,cfree)] induct_thm;
        in EVERY [simp_tac (HOL_basic_ss addsimps inductive_atomize) i,
                  rtac thm i,
                  simp_tac (HOL_basic_ss addsimps inductive_rulify) i]
        end;

    fun split_free_tac P i (free as Free (n,T)) =
        (case rec_id (~1) T of
           "" => NONE
         | name => let val split = P free
                   in if split <> 0 then
                      (case get_splits sg (rec_id split T) of
                             NONE => NONE
                           | SOME (_,_,_,induct_thm)
                               => SOME (mk_split_free_tac free induct_thm i))
                      else NONE
                   end)
     | split_free_tac _ _ _ = NONE;

    val split_frees_tacs = List.mapPartial (split_free_tac P i) frees;

    val simprocs = if has_rec goal then [record_split_simproc P] else [];

  in st |> ((EVERY split_frees_tacs)
           THEN (Simplifier.full_simp_tac (get_simpset sg addsimps thms addsimprocs simprocs) i))
  end handle Empty => Seq.empty;
end;


(* record_split_tac *)
(* splits all records in the goal, which are quantified by ! or !!. *)
fun record_split_tac i st =
  let
    val sg = Thm.sign_of_thm st;

    val has_rec = exists_Const
      (fn (s, Type (_, [Type (_, [T, _]), _])) =>
          (s = "all" orelse s = "All") andalso is_recT T
        | _ => false);

    val goal = nth (Thm.prems_of st) (i - 1);

    fun is_all t =
      (case t of (Const (quantifier, _)$_) =>
         if quantifier = "All" orelse quantifier = "all" then ~1 else 0
       | _ => 0);

  in if has_rec goal
     then Simplifier.full_simp_tac
           (HOL_basic_ss addsimprocs [record_split_simproc is_all]) i st
     else Seq.empty
  end handle Subscript => Seq.empty;

(* wrapper *)

val record_split_name = "record_split_tac";
val record_split_wrapper = (record_split_name, fn tac => record_split_tac ORELSE' tac);



(** theory extender interface **)

(* prepare arguments *)

fun read_raw_parent sign s =
  (case Sign.read_typ_abbrev (sign, K NONE) s handle TYPE (msg, _, _) => error msg of
    Type (name, Ts) => (Ts, name)
  | _ => error ("Bad parent record specification: " ^ quote s));

fun read_typ sign (env, s) =
  let
    fun def_sort (x, ~1) = AList.lookup (op =) env x
      | def_sort _ = NONE;
    val T = Type.no_tvars (Sign.read_typ (sign, def_sort) s) handle TYPE (msg, _, _) => error msg;
  in (Term.add_typ_tfrees (T, env), T) end;

fun cert_typ sign (env, raw_T) =
  let val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle TYPE (msg, _, _) => error msg
  in (Term.add_typ_tfrees (T, env), T) end;

(* attributes *)

fun case_names_fields x = RuleCases.case_names ["fields"] x;
fun induct_type_global name = [case_names_fields, Attrib.theory (InductAttrib.induct_type name)];
fun cases_type_global name = [case_names_fields, Attrib.theory (InductAttrib.cases_type name)];

(* tactics *)

fun simp_all_tac ss simps = ALLGOALS (Simplifier.asm_full_simp_tac (ss addsimps simps));

(* do case analysis / induction according to rule on last parameter of ith subgoal
 * (or on s if there are no parameters);
 * Instatiation of record variable (and predicate) in rule is calculated to
 * avoid problems with higher order unification.
 *)

fun try_param_tac s rule i st =
  let
    val cert = cterm_of (Thm.theory_of_thm st);
    val g = nth (prems_of st) (i - 1);
    val params = Logic.strip_params g;
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl g);
    val rule' = Thm.lift_rule (Thm.cprem_of st i) rule;
    val (P, ys) = strip_comb (HOLogic.dest_Trueprop
      (Logic.strip_assums_concl (prop_of rule')));
    (* ca indicates if rule is a case analysis or induction rule *)
    val (x, ca) = (case rev (Library.drop (length params, ys)) of
        [] => (head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop
          (hd (rev (Logic.strip_assums_hyp (hd (prems_of rule')))))))), true)
      | [x] => (head_of x, false));
    val rule'' = cterm_instantiate (map (pairself cert) (case (rev params) of
        [] => (case AList.lookup (op =) (map dest_Free (term_frees (prop_of st))) s of
          NONE => sys_error "try_param_tac: no such variable"
        | SOME T => [(P, if ca then concl else lambda (Free (s, T)) concl),
            (x, Free (s, T))])
      | (_, T) :: _ => [(P, list_abs (params, if ca then concl
          else incr_boundvars 1 (Abs (s, T, concl)))),
        (x, list_abs (params, Bound 0))])) rule'
  in compose_tac (false, rule'', nprems_of rule) i st end;


(* !!x1 ... xn. ... ==> EX x1 ... xn. P x1 ... xn;
   instantiates x1 ... xn with parameters x1 ... xn *)
fun ex_inst_tac i st =
  let
    val sg = sign_of_thm st;
    val g = nth (prems_of st) (i - 1);
    val params = Logic.strip_params g;
    val exI' = Thm.lift_rule (Thm.cprem_of st i) exI;
    val (_$(_$x)) = Logic.strip_assums_concl (hd (prems_of exI'));
    val cx = cterm_of sg (fst (strip_comb x));

  in Seq.single (Library.foldl (fn (st,v) =>
        Seq.hd
        (compose_tac (false, cterm_instantiate
                                [(cx,cterm_of sg (list_abs (params,Bound v)))] exI',1)
                i st)) (st,((length params) - 1) downto 0))
  end;

fun extension_typedef name repT alphas thy =
  let
    val UNIV = HOLogic.mk_UNIV repT;

    val (thy',{set_def=SOME def, Abs_induct = abs_induct,
               Abs_inject=abs_inject, Abs_inverse = abs_inverse,...}) =
        thy |> setmp TypedefPackage.quiet_mode true
           (TypedefPackage.add_typedef_i true NONE
             (suffix ext_typeN (Sign.base_name name), alphas, Syntax.NoSyn) UNIV NONE
             (Tactic.rtac UNIV_witness 1))
    val rewrite_rule = Tactic.rewrite_rule [def, rec_UNIV_I, rec_True_simp];
  in (map rewrite_rule [abs_inject, abs_inverse, abs_induct], thy')
  end;

fun mixit convs refls =
  let fun f ((res,lhs,rhs),refl) = ((refl,List.revAppend (lhs,refl::tl rhs))::res,hd rhs::lhs,tl rhs);
  in #1 (Library.foldl f (([],[],convs),refls)) end;

fun extension_definition full name fields names alphas zeta moreT more vars thy =
  let
    val base = Sign.base_name;
    val fieldTs = (map snd fields);
    val alphas_zeta = alphas@[zeta];
    val alphas_zetaTs = map (fn n => TFree (n, HOLogic.typeS)) alphas_zeta;
    val vT = TFree (variant alphas_zeta "'v", HOLogic.typeS);
    val extT_name = suffix ext_typeN name
    val extT = Type (extT_name, alphas_zetaTs);
    val repT = foldr1 HOLogic.mk_prodT (fieldTs@[moreT]);
    val fields_more = fields@[(full moreN,moreT)];
    val fields_moreTs = fieldTs@[moreT];
    val bfields_more = map (apfst base) fields_more;
    val r = Free (rN,extT)
    val len = length fields;
    val idxms = 0 upto len;

    (* prepare declarations and definitions *)

    (*fields constructor*)
    val ext_decl = (mk_extC (name,extT) fields_moreTs);
    (*
    val ext_spec = Const ext_decl :==
         (foldr (uncurry lambda)
            (mk_Abs name repT extT $ (foldr1 HOLogic.mk_prod (vars@[more]))) (vars@[more]))
    *)
    val ext_spec = list_comb (Const ext_decl,vars@[more]) :==
         (mk_Abs name repT extT $ (foldr1 HOLogic.mk_prod (vars@[more])));

    fun mk_ext args = list_comb (Const ext_decl, args);

    (*destructors*)
    val _ = timing_msg "record extension preparing definitions";
    val dest_decls = map (mk_selC extT o (apfst (suffix ext_dest))) bfields_more;

    fun mk_dest_spec (i, (c,T)) =
      let val snds = (funpow i HOLogic.mk_snd (mk_Rep name repT extT $ r))
      in Const (mk_selC extT (suffix ext_dest c,T))
         :== (lambda r (if i=len then snds else HOLogic.mk_fst snds))
      end;
    val dest_specs =
      ListPair.map mk_dest_spec (idxms, fields_more);

    (*updates*)
    val upd_decls = map (mk_updC updN extT) bfields_more;
    fun mk_upd_spec (c,T) =
      let
        val args = map (fn (n,nT) => if n=c then Free (base c,T)
                                     else (mk_sel r (suffix ext_dest n,nT)))
                       fields_more;
      in Const (mk_updC updN extT (c,T))$(Free (base c,T))$r
          :== mk_ext args
      end;
    val upd_specs = map mk_upd_spec fields_more;

    (* 1st stage: defs_thy *)
    fun mk_defs () =
      thy
        |> extension_typedef name repT (alphas@[zeta])
        ||> Theory.add_consts_i
              (map Syntax.no_syn ((apfst base ext_decl)::dest_decls@upd_decls))
        ||>> PureThy.add_defs_i false (map Thm.no_attributes (ext_spec::dest_specs))
        ||>> PureThy.add_defs_i false (map Thm.no_attributes upd_specs)
        |> swap
    val (defs_thy, (([abs_inject, abs_inverse, abs_induct],ext_def::dest_defs),upd_defs)) =
        timeit_msg "record extension type/selector/update defs:" mk_defs;


    (* prepare propositions *)
    val _ = timing_msg "record extension preparing propositions";
    val vars_more = vars@[more];
    val named_vars_more = (names@[full moreN])~~vars_more;
    val variants = map (fn (Free (x,_))=>x) vars_more;
    val ext = mk_ext vars_more;
    val s     = Free (rN, extT);
    val w     = Free (wN, extT);
    val P = Free (variant variants "P", extT-->HOLogic.boolT);
    val C = Free (variant variants "C", HOLogic.boolT);

    val inject_prop =
      let val vars_more' = map (fn (Free (x,T)) => Free (x ^ "'",T)) vars_more;
      in All (map dest_Free (vars_more@vars_more'))
          ((HOLogic.eq_const extT $
            mk_ext vars_more$mk_ext vars_more')
           ===
           foldr1 HOLogic.mk_conj (map HOLogic.mk_eq (vars_more ~~ vars_more')))
      end;

    val induct_prop =
      (All (map dest_Free vars_more) (Trueprop (P $ ext)), Trueprop (P $ s));

    val cases_prop =
      (All (map dest_Free vars_more)
        (Trueprop (HOLogic.mk_eq (s,ext)) ==> Trueprop C))
      ==> Trueprop C;

    (*destructors*)
    val dest_conv_props =
       map (fn (c, x as Free (_,T)) => mk_sel ext (suffix ext_dest c,T) === x) named_vars_more;

    (*updates*)
    fun mk_upd_prop (i,(c,T)) =
      let val x' = Free (variant variants (base c ^ "'"),T)
          val args' = nth_update (i, x') vars_more
      in mk_upd updN c x' ext === mk_ext args'  end;
    val upd_conv_props = ListPair.map mk_upd_prop (idxms, fields_more);

    val surjective_prop =
      let val args =
           map (fn (c, Free (_,T)) => mk_sel s (suffix ext_dest c,T)) named_vars_more;
      in s === mk_ext args end;

    val split_meta_prop =
      let val P = Free (variant variants "P", extT-->Term.propT) in
        Logic.mk_equals
         (All [dest_Free s] (P $ s), All (map dest_Free vars_more) (P $ ext))
      end;

    fun prove stndrd = quick_and_dirty_prove stndrd defs_thy;
    val prove_standard = quick_and_dirty_prove true defs_thy;
    fun prove_simp stndrd simps =
      let val tac = simp_all_tac HOL_ss simps
      in fn prop => prove stndrd [] prop (K tac) end;

    fun inject_prf () = (prove_simp true [ext_def,abs_inject,Pair_eq] inject_prop);
    val inject = timeit_msg "record extension inject proof:" inject_prf;

    fun induct_prf () =
      let val (assm, concl) = induct_prop
      in prove_standard [assm] concl (fn prems =>
           EVERY [try_param_tac rN abs_induct 1,
                  simp_tac (HOL_ss addsimps [split_paired_all]) 1,
                  resolve_tac (map (rewrite_rule [ext_def]) prems) 1])
      end;
    val induct = timeit_msg "record extension induct proof:" induct_prf;

    fun cases_prf_opt () =
      let
        val sg = (sign_of defs_thy);
        val (_$(Pvar$_)) = concl_of induct;
        val ind = cterm_instantiate
                    [(cterm_of sg Pvar, cterm_of sg
                            (lambda w (HOLogic.imp$HOLogic.mk_eq(r,w)$C)))]
                    induct;
        in standard (ObjectLogic.rulify (mp OF [ind, refl])) end;

    fun cases_prf_noopt () =
        prove_standard [] cases_prop (fn prems =>
         EVERY [asm_full_simp_tac (HOL_basic_ss addsimps [atomize_all, atomize_imp]) 1,
                try_param_tac rN induct 1,
                rtac impI 1,
                REPEAT (etac allE 1),
                etac mp 1,
                rtac refl 1])

    val cases_prf = quick_and_dirty_prf cases_prf_noopt cases_prf_opt;
    val cases = timeit_msg "record extension cases proof:" cases_prf;

    fun dest_convs_prf () = map (prove_simp false
                      ([ext_def,abs_inverse]@Pair_sel_convs@dest_defs)) dest_conv_props;
    val dest_convs = timeit_msg "record extension dest_convs proof:" dest_convs_prf;
    fun dest_convs_standard_prf () = map standard dest_convs;

    val dest_convs_standard =
        timeit_msg "record extension dest_convs_standard proof:" dest_convs_standard_prf;

    fun upd_convs_prf_noopt () = map (prove_simp true (dest_convs_standard@upd_defs))
                                       upd_conv_props;
    fun upd_convs_prf_opt () =
      let
        val sg = sign_of defs_thy;
        fun mkrefl (c,T) = Thm.reflexive
                            (cterm_of sg (Free (variant variants (base c ^ "'"),T)));
        val refls = map mkrefl fields_more;
        val constr_refl = Thm.reflexive (cterm_of sg (head_of ext));
        val dest_convs' = map mk_meta_eq dest_convs;

        fun mkthm (udef,(fld_refl,thms)) =
          let val bdyeq = Library.foldl (uncurry Thm.combination) (constr_refl,thms);
               (* (|N=N (|N=N,M=M,K=K,more=more|)
                    M=M (|N=N,M=M,K=K,more=more|)
                    K=K'
                    more = more (|N=N,M=M,K=K,more=more|) =
                  (|N=N,M=M,K=K',more=more|)
                *)
              val (_$(_$v$r)$_) = prop_of udef;
              val (_$v'$_) = prop_of fld_refl;
              val udef' = cterm_instantiate
                            [(cterm_of sg v,cterm_of sg v'),
                             (cterm_of sg r,cterm_of sg ext)] udef;
          in  standard (Thm.transitive udef' bdyeq) end;
      in map mkthm (rev upd_defs  ~~ (mixit dest_convs' refls)) end;

    val upd_convs_prf = quick_and_dirty_prf upd_convs_prf_noopt upd_convs_prf_opt;

    val upd_convs =
         timeit_msg "record extension upd_convs proof:" upd_convs_prf;

    fun surjective_prf () =
      prove_standard [] surjective_prop (fn prems =>
          (EVERY [try_param_tac rN induct 1,
                  simp_tac (HOL_basic_ss addsimps dest_convs_standard) 1]));
    val surjective = timeit_msg "record extension surjective proof:" surjective_prf;

    fun split_meta_prf () =
        prove_standard [] split_meta_prop (fn prems =>
         EVERY [rtac equal_intr_rule 1, norm_hhf_tac 1,
                etac meta_allE 1, atac 1,
                rtac (prop_subst OF [surjective]) 1,
                REPEAT (etac meta_allE 1), atac 1]);
    val split_meta = timeit_msg "record extension split_meta proof:" split_meta_prf;

    val (([inject',induct',cases',surjective',split_meta'], [dest_convs',upd_convs']),
      thm_thy) =
      defs_thy
      |> (PureThy.add_thms o map Thm.no_attributes)
           [("ext_inject", inject),
            ("ext_induct", induct),
            ("ext_cases", cases),
            ("ext_surjective", surjective),
            ("ext_split", split_meta)]
      ||>> (PureThy.add_thmss o map Thm.no_attributes)
              [("dest_convs",dest_convs_standard),("upd_convs",upd_convs)]

  in (thm_thy,extT,induct',inject',dest_convs',split_meta',upd_convs')
  end;

fun chunks []      []   = []
  | chunks []      xs   = [xs]
  | chunks (l::ls) xs  = Library.take (l,xs)::chunks ls (Library.drop (l,xs));

fun chop_last [] = error "last: list should not be empty"
  | chop_last [x] = ([],x)
  | chop_last (x::xs) = let val (tl,l) = chop_last xs in (x::tl,l) end;

fun subst_last s []      = error "subst_last: list should not be empty"
  | subst_last s ([x])   = [s]
  | subst_last s (x::xs) = (x::subst_last s xs);

(* mk_recordT builds up the record type from the current extension tpye extT and a list
 * of parent extensions, starting with the root of the record hierarchy
*)
fun mk_recordT extT parent_exts =
    foldr (fn ((parent,Ts),T) => Type (parent, subst_last T Ts)) extT parent_exts;



fun obj_to_meta_all thm =
  let
    fun E thm = case (SOME (spec OF [thm]) handle THM _ => NONE) of
                  SOME thm' => E thm'
                | NONE => thm;
    val th1 = E thm;
    val th2 = Drule.forall_intr_vars th1;
  in th2 end;

fun meta_to_obj_all thm =
  let
    val {sign, prop, ...} = rep_thm thm;
    val params = Logic.strip_params prop;
    val concl = HOLogic.dest_Trueprop (Logic.strip_assums_concl prop);
    val ct = cterm_of sign
      (HOLogic.mk_Trueprop (HOLogic.list_all (params, concl)));
    val thm' = Seq.hd (REPEAT (rtac allI 1) (Thm.trivial ct));
  in
    Thm.implies_elim thm' thm
  end;



(* record_definition *)
fun record_definition (args, bname) parent (parents: parent_info list) raw_fields thy =
  (* smlnj needs type annotation of parents *)
  let
    val sign = Theory.sign_of thy;

    val alphas = map fst args;
    val name = Sign.full_name sign bname;
    val full = Sign.full_name_path sign bname;
    val base = Sign.base_name;

    val (bfields, field_syntax) = split_list (map (fn (x, T, mx) => ((x, T), mx)) raw_fields);

    val parent_fields = List.concat (map #fields parents);
    val parent_chunks = map (length o #fields) parents;
    val parent_names = map fst parent_fields;
    val parent_types = map snd parent_fields;
    val parent_fields_len = length parent_fields;
    val parent_variants = variantlist (map base parent_names, [moreN, rN, rN ^ "'", wN]);
    val parent_vars = ListPair.map Free (parent_variants, parent_types);
    val parent_len = length parents;
    val parents_idx = (map #name parents) ~~ (0 upto (parent_len - 1));

    val fields = map (apfst full) bfields;
    val names = map fst fields;
    val extN = full bname;
    val types = map snd fields;
    val alphas_fields = foldr add_typ_tfree_names [] types;
    val alphas_ext = alphas inter alphas_fields;
    val len = length fields;
    val variants = variantlist (map fst bfields, moreN::rN::rN ^ "'"::wN::parent_variants);
    val vars = ListPair.map Free (variants, types);
    val named_vars = names ~~ vars;
    val idxs = 0 upto (len - 1);
    val idxms = 0 upto len;

    val all_fields = parent_fields @ fields;
    val all_names = parent_names @ names;
    val all_types = parent_types @ types;
    val all_len = parent_fields_len + len;
    val all_variants = parent_variants @ variants;
    val all_vars = parent_vars @ vars;
    val all_named_vars = (parent_names ~~ parent_vars) @ named_vars;


    val zeta = variant alphas "'z";
    val moreT = TFree (zeta, HOLogic.typeS);
    val more = Free (moreN, moreT);
    val full_moreN = full moreN;
    val bfields_more = bfields @ [(moreN,moreT)];
    val fields_more = fields @ [(full_moreN,moreT)];
    val vars_more = vars @ [more];
    val named_vars_more = named_vars @[(full_moreN,more)];
    val all_vars_more = all_vars @ [more];
    val all_named_vars_more = all_named_vars @ [(full_moreN,more)];

    (* 1st stage: extension_thy *)
    val (extension_thy,extT,ext_induct,ext_inject,ext_dest_convs,ext_split,u_convs) =
      thy
      |> Theory.add_path bname
      |> extension_definition full extN fields names alphas_ext zeta moreT more vars;

    val _ = timing_msg "record preparing definitions";
    val Type extension_scheme = extT;
    val extension_name = unsuffix ext_typeN (fst extension_scheme);
    val extension = let val (n,Ts) = extension_scheme in (n,subst_last HOLogic.unitT Ts) end;
    val extension_names =
         (map ((unsuffix ext_typeN) o fst o #extension) parents) @ [extN];
    val extension_id = Library.foldl (op ^) ("",extension_names);


    fun rec_schemeT n = mk_recordT extT (map #extension (prune n parents));
    val rec_schemeT0 = rec_schemeT 0;

    fun recT n =
      let val (c,Ts) = extension
      in mk_recordT (Type (c,subst_last HOLogic.unitT Ts))(map #extension (prune n parents))
      end;
    val recT0 = recT 0;

    fun mk_rec args n =
      let val (args',more) = chop_last args;
          fun mk_ext' (((name,T),args),more) = mk_ext (name,T) (args@[more]);
          fun build Ts =
           foldr mk_ext' more (prune n (extension_names ~~ Ts ~~ (chunks parent_chunks args')))
      in
        if more = HOLogic.unit
        then build (map recT (0 upto parent_len))
        else build (map rec_schemeT (0 upto parent_len))
      end;

    val r_rec0 = mk_rec all_vars_more 0;
    val r_rec_unit0 = mk_rec (all_vars@[HOLogic.unit]) 0;

    fun r n = Free (rN, rec_schemeT n)
    val r0 = r 0;
    fun r_unit n = Free (rN, recT n)
    val r_unit0 = r_unit 0;
    val w = Free (wN, rec_schemeT 0)

    (* prepare print translation functions *)
    val field_tr's =
      print_translation (distinct (List.concat (map NameSpace.accesses' (full_moreN :: names))));

    val adv_ext_tr's =
    let
      val trnames = NameSpace.accesses' extN;
    in map (gen_record_tr') trnames end;

    val adv_record_type_abbr_tr's =
      let val trnames = NameSpace.accesses' (hd extension_names);
          val lastExt = (unsuffix ext_typeN (fst extension));
      in map (gen_record_type_abbr_tr' name alphas zeta lastExt rec_schemeT0) trnames
      end;

    val adv_record_type_tr's =
      let val trnames = if parent_len > 0 then NameSpace.accesses' extN else [];
                        (* avoid conflict with adv_record_type_abbr_tr's *)
      in map (gen_record_type_tr') trnames
      end;


    (* prepare declarations *)

    val sel_decls = map (mk_selC rec_schemeT0) bfields_more;
    val upd_decls = map (mk_updC updateN rec_schemeT0) bfields_more;
    val make_decl = (makeN, all_types ---> recT0);
    val fields_decl = (fields_selN, types ---> Type extension);
    val extend_decl = (extendN, recT0 --> moreT --> rec_schemeT0);
    val truncate_decl = (truncateN, rec_schemeT0 --> recT0);

    (* prepare definitions *)

    fun parent_more s =
         if null parents then s
         else mk_sel s (NameSpace.qualified (#name (List.last parents)) moreN, extT);

    fun parent_more_upd v s =
      if null parents then v
      else let val mp = NameSpace.qualified (#name (List.last parents)) moreN;
           in mk_upd updateN mp v s end;

    (*record (scheme) type abbreviation*)
    val recordT_specs =
      [(suffix schemeN bname, alphas @ [zeta], rec_schemeT0, Syntax.NoSyn),
        (bname, alphas, recT0, Syntax.NoSyn)];

    (*selectors*)
    fun mk_sel_spec (c,T) =
         Const (mk_selC rec_schemeT0 (c,T))
          :== (lambda r0 (Const (mk_selC extT (suffix ext_dest c,T))$parent_more r0));
    val sel_specs = map mk_sel_spec fields_more;

    (*updates*)

    fun mk_upd_spec (c,T) =
      let
        val new = mk_upd updN c (Free (base c,T)) (parent_more r0);
      in Const (mk_updC updateN rec_schemeT0 (c,T))$(Free (base c,T))$r0
          :== (parent_more_upd new r0)
      end;
    val upd_specs = map mk_upd_spec fields_more;

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
        |> Theory.add_trfuns
            ([],[],field_tr's, [])
        |> Theory.add_advanced_trfuns
            ([],[],adv_ext_tr's @ adv_record_type_tr's @ adv_record_type_abbr_tr's,[])
        |> Theory.parent_path
        |> Theory.add_tyabbrs_i recordT_specs
        |> Theory.add_path bname
        |> Theory.add_consts_i
            (map2 (fn (x, T) => fn mx => (x, T, mx)) sel_decls (field_syntax @ [Syntax.NoSyn]))
        |> (Theory.add_consts_i o map Syntax.no_syn)
            (upd_decls @ [make_decl, fields_decl, extend_decl, truncate_decl])
        |> ((PureThy.add_defs_i false o map Thm.no_attributes) sel_specs)
        ||>> ((PureThy.add_defs_i false o map Thm.no_attributes) upd_specs)
        ||>> ((PureThy.add_defs_i false o map Thm.no_attributes)
               [make_spec, fields_spec, extend_spec, truncate_spec])
        |> swap
    val (defs_thy,((sel_defs,upd_defs),derived_defs)) =
        timeit_msg "record trfuns/tyabbrs/selectors/updates/make/fields/extend/truncate defs:"
         mk_defs;


    (* prepare propositions *)
    val _ = timing_msg "record preparing propositions";
    val P = Free (variant all_variants "P", rec_schemeT0-->HOLogic.boolT);
    val C = Free (variant all_variants "C", HOLogic.boolT);
    val P_unit = Free (variant all_variants "P", recT0-->HOLogic.boolT);

    (*selectors*)
    val sel_conv_props =
       map (fn (c, x as Free (_,T)) => mk_sel r_rec0 (c,T) === x) named_vars_more;

    (*updates*)
    fun mk_upd_prop (i,(c,T)) =
      let val x' = Free (variant all_variants (base c ^ "'"),T)
          val args' = nth_update (parent_fields_len + i, x') all_vars_more
      in mk_upd updateN c x' r_rec0 === mk_rec args' 0  end;
    val upd_conv_props = ListPair.map mk_upd_prop (idxms, fields_more);

    (*induct*)
    val induct_scheme_prop =
      All (map dest_Free all_vars_more) (Trueprop (P $ r_rec0)) ==> Trueprop (P $ r0);
    val induct_prop =
      (All (map dest_Free all_vars) (Trueprop (P_unit $ r_rec_unit0)),
       Trueprop (P_unit $ r_unit0));

    (*surjective*)
    val surjective_prop =
      let val args = map (fn (c,Free (_,T)) => mk_sel r0 (c,T)) all_named_vars_more
      in r0 === mk_rec args 0 end;

    (*cases*)
    val cases_scheme_prop =
      (All (map dest_Free all_vars_more)
        (Trueprop (HOLogic.mk_eq (r0,r_rec0)) ==> Trueprop C))
      ==> Trueprop C;

    val cases_prop =
      (All (map dest_Free all_vars)
        (Trueprop (HOLogic.mk_eq (r_unit0,r_rec_unit0)) ==> Trueprop C))
       ==> Trueprop C;

    (*split*)
    val split_meta_prop =
      let val P = Free (variant all_variants "P", rec_schemeT0-->Term.propT) in
        Logic.mk_equals
         (All [dest_Free r0] (P $ r0), All (map dest_Free all_vars_more) (P $ r_rec0))
      end;

    val split_object_prop =
      let fun ALL vs t = foldr (fn ((v,T),t) => HOLogic.mk_all (v,T,t)) t vs
      in (ALL [dest_Free r0] (P $ r0)) === (ALL (map dest_Free all_vars_more) (P $ r_rec0))
      end;


    val split_ex_prop =
      let fun EX vs t = foldr (fn ((v,T),t) => HOLogic.mk_exists (v,T,t)) t vs
      in (EX [dest_Free r0] (P $ r0)) === (EX (map dest_Free all_vars_more) (P $ r_rec0))
      end;

    (*equality*)
    val equality_prop =
      let
        val s' = Free (rN ^ "'", rec_schemeT0)
        fun mk_sel_eq (c,Free (_,T)) =  mk_sel r0 (c,T) === mk_sel s' (c,T)
        val seleqs = map mk_sel_eq all_named_vars_more
      in All (map dest_Free [r0,s']) (Logic.list_implies (seleqs,r0 === s')) end;

    (* 3rd stage: thms_thy *)

    fun prove stndrd = quick_and_dirty_prove stndrd defs_thy;
    val prove_standard = quick_and_dirty_prove true defs_thy;

    fun prove_simp stndrd ss simps =
      let val tac = simp_all_tac ss simps
      in fn prop => prove stndrd [] prop (K tac) end;

    val ss = get_simpset defs_thy;

    fun sel_convs_prf () = map (prove_simp false ss
                           (sel_defs@ext_dest_convs)) sel_conv_props;
    val sel_convs = timeit_msg "record sel_convs proof:" sel_convs_prf;
    fun sel_convs_standard_prf () = map standard sel_convs
    val sel_convs_standard =
          timeit_msg "record sel_convs_standard proof:" sel_convs_standard_prf;

    fun upd_convs_prf () =
          map (prove_simp true ss (upd_defs@u_convs)) upd_conv_props;

    val upd_convs = timeit_msg "record upd_convs proof:" upd_convs_prf;

    val parent_induct = if null parents then [] else [#induct (hd (rev parents))];

    fun induct_scheme_prf () = prove_standard [] induct_scheme_prop (fn prems =>
          (EVERY [if null parent_induct
                  then all_tac else try_param_tac rN (hd parent_induct) 1,
                  try_param_tac rN ext_induct 1,
                  asm_simp_tac HOL_basic_ss 1]));
    val induct_scheme = timeit_msg "record induct_scheme proof:" induct_scheme_prf;

    fun induct_prf () =
      let val (assm, concl) = induct_prop;
      in
        prove_standard [assm] concl (fn prems =>
          try_param_tac rN induct_scheme 1
          THEN try_param_tac "more" unit_induct 1
          THEN resolve_tac prems 1)
      end;
    val induct = timeit_msg "record induct proof:" induct_prf;

    fun surjective_prf () =
      prove_standard [] surjective_prop (fn prems =>
          (EVERY [try_param_tac rN induct_scheme 1,
                  simp_tac (ss addsimps sel_convs_standard) 1]))
    val surjective = timeit_msg "record surjective proof:" surjective_prf;

    fun cases_scheme_prf_opt () =
      let
        val sg = (sign_of defs_thy);
        val (_$(Pvar$_)) = concl_of induct_scheme;
        val ind = cterm_instantiate
                    [(cterm_of sg Pvar, cterm_of sg
                            (lambda w (HOLogic.imp$HOLogic.mk_eq(r0,w)$C)))]
                    induct_scheme;
        in standard (ObjectLogic.rulify (mp OF [ind, refl])) end;

    fun cases_scheme_prf_noopt () =
        prove_standard [] cases_scheme_prop (fn prems =>
         EVERY [asm_full_simp_tac (HOL_basic_ss addsimps [atomize_all, atomize_imp]) 1,
               try_param_tac rN induct_scheme 1,
               rtac impI 1,
               REPEAT (etac allE 1),
               etac mp 1,
               rtac refl 1])
    val cases_scheme_prf = quick_and_dirty_prf cases_scheme_prf_noopt cases_scheme_prf_opt;
    val cases_scheme = timeit_msg "record cases_scheme proof:" cases_scheme_prf;

    fun cases_prf () =
      prove_standard [] cases_prop  (fn _ =>
        try_param_tac rN cases_scheme 1
        THEN simp_all_tac HOL_basic_ss [unit_all_eq1]);
    val cases = timeit_msg "record cases proof:" cases_prf;

    fun split_meta_prf () =
        prove false [] split_meta_prop (fn prems =>
         EVERY [rtac equal_intr_rule 1, norm_hhf_tac 1,
                etac meta_allE 1, atac 1,
                rtac (prop_subst OF [surjective]) 1,
                REPEAT (etac meta_allE 1), atac 1]);
    val split_meta = timeit_msg "record split_meta proof:" split_meta_prf;
    val split_meta_standard = standard split_meta;

    fun split_object_prf_opt () =
      let
        val sg = sign_of defs_thy;
        val cPI= cterm_of sg (lambda r0 (Trueprop (P$r0)));
        val (_$Abs(_,_,P$_)) = fst (Logic.dest_equals (concl_of split_meta_standard));
        val cP = cterm_of sg P;
        val split_meta' = cterm_instantiate [(cP,cPI)] split_meta_standard;
        val (l,r) = HOLogic.dest_eq (HOLogic.dest_Trueprop split_object_prop);
        val cl = cterm_of sg (HOLogic.mk_Trueprop l);
        val cr = cterm_of sg (HOLogic.mk_Trueprop r);
        val thl = assume cl                 (*All r. P r*) (* 1 *)
                |> obj_to_meta_all          (*!!r. P r*)
                |> equal_elim split_meta'   (*!!n m more. P (ext n m more)*)
                |> meta_to_obj_all          (*All n m more. P (ext n m more)*) (* 2*)
                |> implies_intr cl          (* 1 ==> 2 *)
        val thr = assume cr                           (*All n m more. P (ext n m more)*)
                |> obj_to_meta_all                    (*!!n m more. P (ext n m more)*)
                |> equal_elim (symmetric split_meta') (*!!r. P r*)
                |> meta_to_obj_all                    (*All r. P r*)
                |> implies_intr cr                    (* 2 ==> 1 *)
     in standard (thr COMP (thl COMP iffI)) end;

    fun split_object_prf_noopt () =
        prove_standard [] split_object_prop (fn prems =>
         EVERY [rtac iffI 1,
                REPEAT (rtac allI 1), etac allE 1, atac 1,
                rtac allI 1, rtac induct_scheme 1,REPEAT (etac allE 1),atac 1]);

    val split_object_prf = quick_and_dirty_prf split_object_prf_noopt split_object_prf_opt;
    val split_object = timeit_msg "record split_object proof:" split_object_prf;


    fun split_ex_prf () =
        prove_standard [] split_ex_prop (fn prems =>
          EVERY [rtac iffI 1,
                   etac exE 1,
                   simp_tac (HOL_basic_ss addsimps [split_meta_standard]) 1,
                   ex_inst_tac 1,
                   (*REPEAT (rtac exI 1),*)
                   atac 1,
                 REPEAT (etac exE 1),
                 rtac exI 1,
                 atac 1]);
    val split_ex = timeit_msg "record split_ex proof:" split_ex_prf;

    fun equality_tac thms =
      let val (s'::s::eqs) = rev thms;
          val ss' = ss addsimps (s'::s::sel_convs_standard);
          val eqs' = map (simplify ss') eqs;
      in simp_tac (HOL_basic_ss addsimps (s'::s::eqs')) 1 end;

   fun equality_prf () = prove_standard [] equality_prop (fn _ =>
      fn st => let val [s, s'] = map #1 (rev (Tactic.innermost_params 1 st)) in
        st |> (res_inst_tac [(rN, s)] cases_scheme 1
        THEN res_inst_tac [(rN, s')] cases_scheme 1
        THEN (METAHYPS equality_tac 1))
             (* simp_all_tac ss (sel_convs) would also work but is less efficient *)
      end);
     val equality = timeit_msg "record equality proof:" equality_prf;

    val ((([sel_convs',upd_convs',sel_defs',upd_defs',[split_meta',split_object',split_ex'],derived_defs'],
            [surjective',equality']),[induct_scheme',induct',cases_scheme',cases']), thms_thy) =
      defs_thy
      |> (PureThy.add_thmss o map Thm.no_attributes)
         [("select_convs", sel_convs_standard),
          ("update_convs", upd_convs),
          ("select_defs", sel_defs),
          ("update_defs", upd_defs),
          ("splits", [split_meta_standard,split_object,split_ex]),
          ("defs", derived_defs)]
      ||>> (PureThy.add_thms o map Thm.no_attributes)
          [("surjective", surjective),
           ("equality", equality)]
      ||>> PureThy.add_thms
        [(("induct_scheme", induct_scheme), induct_type_global (suffix schemeN name)),
         (("induct", induct), induct_type_global name),
         (("cases_scheme", cases_scheme), cases_type_global (suffix schemeN name)),
         (("cases", cases), cases_type_global name)];


    val sel_upd_simps = sel_convs' @ upd_convs';
    val iffs = [ext_inject]
    val final_thy =
      thms_thy
      |> (snd oo PureThy.add_thmss)
          [(("simps", sel_upd_simps), [Attrib.theory Simplifier.simp_add]),
           (("iffs",iffs), [Attrib.theory iff_add])]
      |> put_record name (make_record_info args parent fields extension induct_scheme')
      |> put_sel_upd (names @ [full_moreN]) sel_upd_simps
      |> add_record_equalities extension_id equality'
      |> add_extinjects ext_inject
      |> add_extsplit extension_name ext_split
      |> add_record_splits extension_id (split_meta',split_object',split_ex',induct_scheme')
      |> add_extfields extension_name (fields @ [(full_moreN,moreT)])
      |> add_fieldext (extension_name,snd extension) (names @ [full_moreN])
      |> Theory.parent_path;

  in final_thy
  end;

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

    val parent = Option.map (apfst (map prep_inst) o prep_raw_parent sign) raw_parent
      handle ERROR msg => cat_error msg ("The error(s) above in parent record specification");
    val parents = add_parents thy parent [];

    val init_env =
      (case parent of
        NONE => []
      | SOME (types, _) => foldr Term.add_typ_tfrees [] types);


    (* fields *)

    fun prep_field (env, (c, raw_T, mx)) =
      let val (env', T) = prep_typ sign (env, raw_T) handle ERROR msg =>
        cat_error msg ("The error(s) above occured in field " ^ quote c)
      in (env', (c, T, mx)) end;

    val (envir, bfields) = foldl_map prep_field (init_env, raw_fields);
    val envir_names = map fst envir;


    (* args *)

    val defaultS = Sign.defaultS sign;
    val args = map (fn x => (x, AList.lookup (op =) envir x |> the_default defaultS)) params;


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
      (case duplicates (map #1 bfields) of
        [] => []
      | dups => ["Duplicate field(s) " ^ commas_quote dups]);

    val err_bad_fields =
      if forall (not_equal moreN o #1) bfields then []
      else ["Illegal field name " ^ quote moreN];

    val err_dup_sorts =
      (case duplicates envir_names of
        [] => []
      | dups => ["Inconsistent sort constraints for " ^ commas dups]);

    val errs =
      err_dup_record @ err_dup_parms @ err_extra_frees @ err_no_fields @
      err_dup_fields @ err_bad_fields @ err_dup_sorts;
  in
    if null errs then () else error (cat_lines errs)  ;
    thy |> record_definition (args, bname) parent parents bfields
  end
  handle ERROR msg => cat_error msg ("Failed to define record " ^ quote bname);

val add_record = gen_add_record read_typ read_raw_parent;
val add_record_i = gen_add_record cert_typ (K I);

(* setup theory *)

val setup =
 [RecordsData.init,
  Theory.add_trfuns ([], parse_translation, [], []),
  Theory.add_advanced_trfuns ([], adv_parse_translation, [], []),
  (fn thy => (Simplifier.change_simpset_of thy
    (fn ss => ss addsimprocs [record_simproc, record_upd_simproc, record_eq_simproc]); thy))];

(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val record_decl =
  P.type_args -- P.name --
    (P.$$$ "=" |-- Scan.option (P.typ --| P.$$$ "+") -- Scan.repeat1 P.const);

val recordP =
  OuterSyntax.command "record" "define extensible record" K.thy_decl
    (record_decl >> (fn (x, (y, z)) => Toplevel.theory (add_record x y z)));

val _ = OuterSyntax.add_parsers [recordP];

end;

end;


structure BasicRecordPackage: BASIC_RECORD_PACKAGE = RecordPackage;
open BasicRecordPackage;
