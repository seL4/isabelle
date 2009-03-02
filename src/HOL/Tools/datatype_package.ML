(*  Title:      HOL/Tools/datatype_package.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package for Isabelle/HOL.
*)

signature DATATYPE_PACKAGE =
sig
  val quiet_mode : bool ref
  val get_datatypes : theory -> DatatypeAux.datatype_info Symtab.table
  val print_datatypes : theory -> unit
  val get_datatype : theory -> string -> DatatypeAux.datatype_info option
  val the_datatype : theory -> string -> DatatypeAux.datatype_info
  val datatype_of_constr : theory -> string -> DatatypeAux.datatype_info option
  val datatype_of_case : theory -> string -> DatatypeAux.datatype_info option
  val the_datatype_spec : theory -> string -> (string * sort) list * (string * typ list) list
  val get_datatype_constrs : theory -> string -> (string * typ) list option
  val construction_interpretation : theory
    -> {atom : typ -> 'a, dtyp : string -> 'a, rtyp : string -> 'a list -> 'a}
    -> (string * sort) list -> string list
    -> (string * (string * 'a list) list) list
  val distinct_simproc : simproc
  val make_case :  Proof.context -> bool -> string list -> term ->
    (term * term) list -> term * (term * (int * bool)) list
  val strip_case : Proof.context -> bool -> term -> (term * (term * term) list) option
  val read_typ: theory ->
    (typ list * (string * sort) list) * string -> typ list * (string * sort) list
  val interpretation : (string list -> theory -> theory) -> theory -> theory
  val rep_datatype : ({distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} -> Proof.context -> Proof.context) -> string list option -> term list
    -> theory -> Proof.state;
  val rep_datatype_cmd : string list option -> string list -> theory -> Proof.state;
  val add_datatype : bool -> bool -> string list -> (string list * bstring * mixfix *
    (bstring * typ list * mixfix) list) list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} * theory
  val add_datatype_cmd : bool -> string list -> (string list * bstring * mixfix *
    (bstring * string list * mixfix) list) list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} * theory
  val setup: theory -> theory
end;

structure DatatypePackage : DATATYPE_PACKAGE =
struct

open DatatypeAux;

val quiet_mode = quiet_mode;


(* theory data *)

structure DatatypesData = TheoryDataFun
(
  type T =
    {types: datatype_info Symtab.table,
     constrs: datatype_info Symtab.table,
     cases: datatype_info Symtab.table};

  val empty =
    {types = Symtab.empty, constrs = Symtab.empty, cases = Symtab.empty};
  val copy = I;
  val extend = I;
  fun merge _
    ({types = types1, constrs = constrs1, cases = cases1},
     {types = types2, constrs = constrs2, cases = cases2}) =
    {types = Symtab.merge (K true) (types1, types2),
     constrs = Symtab.merge (K true) (constrs1, constrs2),
     cases = Symtab.merge (K true) (cases1, cases2)};
);

val get_datatypes = #types o DatatypesData.get;
val map_datatypes = DatatypesData.map;

fun print_datatypes thy =
  Pretty.writeln (Pretty.strs ("datatypes:" ::
    map #1 (NameSpace.extern_table (Sign.type_space thy, get_datatypes thy))));


(** theory information about datatypes **)

fun put_dt_infos (dt_infos : (string * datatype_info) list) =
  map_datatypes (fn {types, constrs, cases} =>
    {types = fold Symtab.update dt_infos types,
     constrs = fold Symtab.update
       (maps (fn (_, info as {descr, index, ...}) => map (rpair info o fst)
          (#3 (the (AList.lookup op = descr index)))) dt_infos) constrs,
     cases = fold Symtab.update
       (map (fn (_, info as {case_name, ...}) => (case_name, info)) dt_infos)
       cases});

val get_datatype = Symtab.lookup o get_datatypes;

fun the_datatype thy name = (case get_datatype thy name of
      SOME info => info
    | NONE => error ("Unknown datatype " ^ quote name));

val datatype_of_constr = Symtab.lookup o #constrs o DatatypesData.get;
val datatype_of_case = Symtab.lookup o #cases o DatatypesData.get;

fun get_datatype_descr thy dtco =
  get_datatype thy dtco
  |> Option.map (fn info as { descr, index, ... } =>
       (info, (((fn SOME (_, dtys, cos) => (dtys, cos)) o AList.lookup (op =) descr) index)));

fun the_datatype_spec thy dtco =
  let
    val info as { descr, index, sorts = raw_sorts, ... } = the_datatype thy dtco;
    val SOME (_, dtys, raw_cos) = AList.lookup (op =) descr index;
    val sorts = map ((fn v => (v, (the o AList.lookup (op =) raw_sorts) v))
      o DatatypeAux.dest_DtTFree) dtys;
    val cos = map
      (fn (co, tys) => (co, map (DatatypeAux.typ_of_dtyp descr sorts) tys)) raw_cos;
  in (sorts, cos) end;

fun get_datatype_constrs thy dtco =
  case try (the_datatype_spec thy) dtco
   of SOME (sorts, cos) =>
        let
          fun subst (v, sort) = TVar ((v, 0), sort);
          fun subst_ty (TFree v) = subst v
            | subst_ty ty = ty;
          val dty = Type (dtco, map subst sorts);
          fun mk_co (co, tys) = (co, map (Term.map_atyps subst_ty) tys ---> dty);
        in SOME (map mk_co cos) end
    | NONE => NONE;

fun construction_interpretation thy { atom, dtyp, rtyp } sorts tycos =
  let
    val descr = (#descr o the_datatype thy o hd) tycos;
    val k = length tycos;
    val descr_of = the o AList.lookup (op =) descr;
    fun interpT (T as DtTFree _) = atom (typ_of_dtyp descr sorts T)
      | interpT (T as DtType (tyco, Ts)) = if is_rec_type T
          then rtyp tyco (map interpT Ts)
          else atom (typ_of_dtyp descr sorts T)
      | interpT (DtRec l) = if l < k then (dtyp o #1 o descr_of) l
          else let val (tyco, Ts, _) = descr_of l
          in rtyp tyco (map interpT Ts) end;
    fun interpC (c, Ts) = (c, map interpT Ts);
    fun interpK (_, (tyco, _, cs)) = (tyco, map interpC cs);
  in map interpK (Library.take (k, descr)) end;



(** induct method setup **)

(* case names *)

local

fun dt_recs (DtTFree _) = []
  | dt_recs (DtType (_, dts)) = maps dt_recs dts
  | dt_recs (DtRec i) = [i];

fun dt_cases (descr: descr) (_, args, constrs) =
  let
    fun the_bname i = Sign.base_name (#1 (the (AList.lookup (op =) descr i)));
    val bnames = map the_bname (distinct (op =) (maps dt_recs args));
  in map (fn (c, _) => space_implode "_" (Sign.base_name c :: bnames)) constrs end;


fun induct_cases descr =
  DatatypeProp.indexify_names (maps (dt_cases descr) (map #2 descr));

fun exhaust_cases descr i = dt_cases descr (the (AList.lookup (op =) descr i));

in

fun mk_case_names_induct descr = RuleCases.case_names (induct_cases descr);

fun mk_case_names_exhausts descr new =
  map (RuleCases.case_names o exhaust_cases descr o #1)
    (filter (fn ((_, (name, _, _))) => member (op =) new name) descr);

end;

fun add_rules simps case_thms rec_thms inject distinct
                  weak_case_congs cong_att =
  PureThy.add_thmss [((Binding.name "simps", simps), []),
    ((Binding.empty, flat case_thms @
          flat distinct @ rec_thms), [Simplifier.simp_add]),
    ((Binding.empty, rec_thms), [Code.add_default_eqn_attribute]),
    ((Binding.empty, flat inject), [iff_add]),
    ((Binding.empty, map (fn th => th RS notE) (flat distinct)), [Classical.safe_elim NONE]),
    ((Binding.empty, weak_case_congs), [cong_att])]
  #> snd;


(* add_cases_induct *)

fun add_cases_induct infos induction thy =
  let
    val inducts = ProjectRule.projections (ProofContext.init thy) induction;

    fun named_rules (name, {index, exhaustion, ...}: datatype_info) =
      [((Binding.empty, nth inducts index), [Induct.induct_type name]),
       ((Binding.empty, exhaustion), [Induct.cases_type name])];
    fun unnamed_rule i =
      ((Binding.empty, nth inducts i), [Thm.kind_internal, Induct.induct_type ""]);
  in
    thy |> PureThy.add_thms
      (maps named_rules infos @
        map unnamed_rule (length infos upto length inducts - 1)) |> snd
    |> PureThy.add_thmss [((Binding.name "inducts", inducts), [])] |> snd
  end;



(**** simplification procedure for showing distinctness of constructors ****)

fun stripT (i, Type ("fun", [_, T])) = stripT (i + 1, T)
  | stripT p = p;

fun stripC (i, f $ x) = stripC (i + 1, f)
  | stripC p = p;

val distinctN = "constr_distinct";

fun distinct_rule thy ss tname eq_t = case #distinct (the_datatype thy tname) of
    FewConstrs thms => Goal.prove (Simplifier.the_context ss) [] [] eq_t (K
      (EVERY [rtac eq_reflection 1, rtac iffI 1, rtac notE 1,
        atac 2, resolve_tac thms 1, etac FalseE 1]))
  | ManyConstrs (thm, simpset) =>
      let
        val [In0_inject, In1_inject, In0_not_In1, In1_not_In0] =
          map (PureThy.get_thm (ThyInfo.the_theory "Datatype" thy))
            ["In0_inject", "In1_inject", "In0_not_In1", "In1_not_In0"];
      in
        Goal.prove (Simplifier.the_context ss) [] [] eq_t (K
        (EVERY [rtac eq_reflection 1, rtac iffI 1, dtac thm 1,
          full_simp_tac (Simplifier.inherit_context ss simpset) 1,
          REPEAT (dresolve_tac [In0_inject, In1_inject] 1),
          eresolve_tac [In0_not_In1 RS notE, In1_not_In0 RS notE] 1,
          etac FalseE 1]))
      end;

fun distinct_proc thy ss (t as Const ("op =", _) $ t1 $ t2) =
  (case (stripC (0, t1), stripC (0, t2)) of
     ((i, Const (cname1, T1)), (j, Const (cname2, T2))) =>
         (case (stripT (0, T1), stripT (0, T2)) of
            ((i', Type (tname1, _)), (j', Type (tname2, _))) =>
                if tname1 = tname2 andalso not (cname1 = cname2) andalso i = i' andalso j = j' then
                   (case (get_datatype_descr thy) tname1 of
                      SOME (_, (_, constrs)) => let val cnames = map fst constrs
                        in if cname1 mem cnames andalso cname2 mem cnames then
                             SOME (distinct_rule thy ss tname1
                               (Logic.mk_equals (t, Const ("False", HOLogic.boolT))))
                           else NONE
                        end
                    | NONE => NONE)
                else NONE
          | _ => NONE)
   | _ => NONE)
  | distinct_proc _ _ _ = NONE;

val distinct_simproc =
  Simplifier.simproc @{theory HOL} distinctN ["s = t"] distinct_proc;

val dist_ss = HOL_ss addsimprocs [distinct_simproc];

val simproc_setup =
  Simplifier.map_simpset (fn ss => ss addsimprocs [distinct_simproc]);


(**** translation rules for case ****)

fun make_case ctxt = DatatypeCase.make_case
  (datatype_of_constr (ProofContext.theory_of ctxt)) ctxt;

fun strip_case ctxt = DatatypeCase.strip_case
  (datatype_of_case (ProofContext.theory_of ctxt));

fun add_case_tr' case_names thy =
  Sign.add_advanced_trfuns ([], [],
    map (fn case_name =>
      let val case_name' = Sign.const_syntax_name thy case_name
      in (case_name', DatatypeCase.case_tr' datatype_of_case case_name')
      end) case_names, []) thy;

val trfun_setup =
  Sign.add_advanced_trfuns ([],
    [("_case_syntax", DatatypeCase.case_tr true datatype_of_constr)],
    [], []);


(* prepare types *)

fun read_typ thy ((Ts, sorts), str) =
  let
    val ctxt = ProofContext.init thy
      |> fold (Variable.declare_typ o TFree) sorts;
    val T = Syntax.read_typ ctxt str;
  in (Ts @ [T], Term.add_tfreesT T sorts) end;

fun cert_typ sign ((Ts, sorts), raw_T) =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle
      TYPE (msg, _, _) => error msg;
    val sorts' = Term.add_tfreesT T sorts;
  in (Ts @ [T],
      case duplicates (op =) (map fst sorts') of
         [] => sorts'
       | dups => error ("Inconsistent sort constraints for " ^ commas dups))
  end;


(**** make datatype info ****)

fun make_dt_info alt_names descr sorts induct reccomb_names rec_thms
    (((((((((i, (_, (tname, _, _))), case_name), case_thms),
      exhaustion_thm), distinct_thm), inject), nchotomy), case_cong), weak_case_cong) =
  (tname,
   {index = i,
    alt_names = alt_names,
    descr = descr,
    sorts = sorts,
    rec_names = reccomb_names,
    rec_rewrites = rec_thms,
    case_name = case_name,
    case_rewrites = case_thms,
    induction = induct,
    exhaustion = exhaustion_thm,
    distinct = distinct_thm,
    inject = inject,
    nchotomy = nchotomy,
    case_cong = case_cong,
    weak_case_cong = weak_case_cong});

structure DatatypeInterpretation = InterpretationFun(type T = string list val eq = op =);
val interpretation = DatatypeInterpretation.interpretation;


(******************* definitional introduction of datatypes *******************)

fun add_datatype_def flat_names new_type_names descr sorts types_syntax constr_syntax dt_info
    case_names_induct case_names_exhausts thy =
  let
    val _ = message ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val ((inject, distinct, dist_rewrites, simproc_dists, induct), thy2) = thy |>
      DatatypeRepProofs.representation_proofs flat_names dt_info new_type_names descr sorts
        types_syntax constr_syntax case_names_induct;

    val (casedist_thms, thy3) = DatatypeAbsProofs.prove_casedist_thms new_type_names descr
      sorts induct case_names_exhausts thy2;
    val ((reccomb_names, rec_thms), thy4) = DatatypeAbsProofs.prove_primrec_thms
      flat_names new_type_names descr sorts dt_info inject dist_rewrites
      (Simplifier.theory_context thy3 dist_ss) induct thy3;
    val ((case_thms, case_names), thy6) = DatatypeAbsProofs.prove_case_thms
      flat_names new_type_names descr sorts reccomb_names rec_thms thy4;
    val (split_thms, thy7) = DatatypeAbsProofs.prove_split_thms new_type_names
      descr sorts inject dist_rewrites casedist_thms case_thms thy6;
    val (nchotomys, thy8) = DatatypeAbsProofs.prove_nchotomys new_type_names
      descr sorts casedist_thms thy7;
    val (case_congs, thy9) = DatatypeAbsProofs.prove_case_congs new_type_names
      descr sorts nchotomys case_thms thy8;
    val (weak_case_congs, thy10) = DatatypeAbsProofs.prove_weak_case_congs new_type_names
      descr sorts thy9;

    val dt_infos = map (make_dt_info NONE (flat descr) sorts induct reccomb_names rec_thms)
      ((0 upto length (hd descr) - 1) ~~ (hd descr) ~~ case_names ~~ case_thms ~~
        casedist_thms ~~ simproc_dists ~~ inject ~~ nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ rec_thms;

    val thy12 =
      thy10
      |> add_case_tr' case_names
      |> Sign.add_path (space_implode "_" new_type_names)
      |> add_rules simps case_thms rec_thms inject distinct
          weak_case_congs (Simplifier.attrib (op addcongs))
      |> put_dt_infos dt_infos
      |> add_cases_induct dt_infos induct
      |> Sign.parent_path
      |> store_thmss "splits" new_type_names (map (fn (x, y) => [x, y]) split_thms) |> snd
      |> DatatypeInterpretation.data (map fst dt_infos);
  in
    ({distinct = distinct,
      inject = inject,
      exhaustion = casedist_thms,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induct,
      simps = simps}, thy12)
  end;


(*********************** declare existing type as datatype *********************)

fun prove_rep_datatype alt_names new_type_names descr sorts induct inject half_distinct thy =
  let
    val ((_, [induct']), _) =
      Variable.importT_thms [induct] (Variable.thm_context induct);

    fun err t = error ("Ill-formed predicate in induction rule: " ^
      Syntax.string_of_term_global thy t);

    fun get_typ (t as _ $ Var (_, Type (tname, Ts))) =
          ((tname, map (fst o dest_TFree) Ts) handle TERM _ => err t)
      | get_typ t = err t;
    val dtnames = map get_typ (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of induct')));

    val dt_info = get_datatypes thy;

    val distinct = (map o maps) (fn thm => [thm, thm RS not_sym]) half_distinct;
    val (case_names_induct, case_names_exhausts) =
      (mk_case_names_induct descr, mk_case_names_exhausts descr (map #1 dtnames));

    val _ = message ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val (casedist_thms, thy2) = thy |>
      DatatypeAbsProofs.prove_casedist_thms new_type_names [descr] sorts induct
        case_names_exhausts;
    val ((reccomb_names, rec_thms), thy3) = DatatypeAbsProofs.prove_primrec_thms
      false new_type_names [descr] sorts dt_info inject distinct
      (Simplifier.theory_context thy2 dist_ss) induct thy2;
    val ((case_thms, case_names), thy4) = DatatypeAbsProofs.prove_case_thms false
      new_type_names [descr] sorts reccomb_names rec_thms thy3;
    val (split_thms, thy5) = DatatypeAbsProofs.prove_split_thms
      new_type_names [descr] sorts inject distinct casedist_thms case_thms thy4;
    val (nchotomys, thy6) = DatatypeAbsProofs.prove_nchotomys new_type_names
      [descr] sorts casedist_thms thy5;
    val (case_congs, thy7) = DatatypeAbsProofs.prove_case_congs new_type_names
      [descr] sorts nchotomys case_thms thy6;
    val (weak_case_congs, thy8) = DatatypeAbsProofs.prove_weak_case_congs new_type_names
      [descr] sorts thy7;

    val ((_, [induct']), thy10) =
      thy8
      |> store_thmss "inject" new_type_names inject
      ||>> store_thmss "distinct" new_type_names distinct
      ||> Sign.add_path (space_implode "_" new_type_names)
      ||>> PureThy.add_thms [((Binding.name "induct", induct), [case_names_induct])];

    val dt_infos = map (make_dt_info alt_names descr sorts induct' reccomb_names rec_thms)
      ((0 upto length descr - 1) ~~ descr ~~ case_names ~~ case_thms ~~ casedist_thms ~~
        map FewConstrs distinct ~~ inject ~~ nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ rec_thms;

    val thy11 =
      thy10
      |> add_case_tr' case_names
      |> add_rules simps case_thms rec_thms inject distinct
           weak_case_congs (Simplifier.attrib (op addcongs))
      |> put_dt_infos dt_infos
      |> add_cases_induct dt_infos induct'
      |> Sign.parent_path
      |> store_thmss "splits" new_type_names (map (fn (x, y) => [x, y]) split_thms)
      |> snd
      |> DatatypeInterpretation.data (map fst dt_infos);
  in
    ({distinct = distinct,
      inject = inject,
      exhaustion = casedist_thms,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induct',
      simps = simps}, thy11)
  end;

fun gen_rep_datatype prep_term after_qed alt_names raw_ts thy =
  let
    fun constr_of_term (Const (c, T)) = (c, T)
      | constr_of_term t =
          error ("Not a constant: " ^ Syntax.string_of_term_global thy t);
    fun no_constr (c, T) = error ("Bad constructor: "
      ^ Sign.extern_const thy c ^ "::"
      ^ Syntax.string_of_typ_global thy T);
    fun type_of_constr (cT as (_, T)) =
      let
        val frees = OldTerm.typ_tfrees T;
        val (tyco, vs) = ((apsnd o map) (dest_TFree) o dest_Type o snd o strip_type) T
          handle TYPE _ => no_constr cT
        val _ = if has_duplicates (eq_fst (op =)) vs then no_constr cT else ();
        val _ = if length frees <> length vs then no_constr cT else ();
      in (tyco, (vs, cT)) end;

    val raw_cs = AList.group (op =) (map (type_of_constr o constr_of_term o prep_term thy) raw_ts);
    val _ = case map_filter (fn (tyco, _) =>
        if Symtab.defined (get_datatypes thy) tyco then SOME tyco else NONE) raw_cs
     of [] => ()
      | tycos => error ("Type(s) " ^ commas (map quote tycos)
          ^ " already represented inductivly");
    val raw_vss = maps (map (map snd o fst) o snd) raw_cs;
    val ms = case distinct (op =) (map length raw_vss)
     of [n] => 0 upto n - 1
      | _ => error ("Different types in given constructors");
    fun inter_sort m = map (fn xs => nth xs m) raw_vss
      |> Library.foldr1 (Sorts.inter_sort (Sign.classes_of thy))
    val sorts = map inter_sort ms;
    val vs = Name.names Name.context Name.aT sorts;

    fun norm_constr (raw_vs, (c, T)) = (c, map_atyps
      (TFree o (the o AList.lookup (op =) (map fst raw_vs ~~ vs)) o fst o dest_TFree) T);

    val cs = map (apsnd (map norm_constr)) raw_cs;
    val dtyps_of_typ = map (dtyp_of_typ (map (rpair (map fst vs) o fst) cs))
      o fst o strip_type;
    val new_type_names = map NameSpace.base (the_default (map fst cs) alt_names);

    fun mk_spec (i, (tyco, constr)) = (i, (tyco,
      map (DtTFree o fst) vs,
      (map o apsnd) dtyps_of_typ constr))
    val descr = map_index mk_spec cs;
    val injs = DatatypeProp.make_injs [descr] vs;
    val half_distincts = map snd (DatatypeProp.make_distincts [descr] vs);
    val ind = DatatypeProp.make_ind [descr] vs;
    val rules = (map o map o map) Logic.close_form [[[ind]], injs, half_distincts];

    fun after_qed' raw_thms =
      let
        val [[[induct]], injs, half_distincts] =
          unflat rules (map Drule.zero_var_indexes_list raw_thms);
            (*FIXME somehow dubious*)
      in
        ProofContext.theory_result
          (prove_rep_datatype alt_names new_type_names descr vs induct injs half_distincts)
        #-> after_qed
      end;
  in
    thy
    |> ProofContext.init
    |> Proof.theorem_i NONE after_qed' ((map o map) (rpair []) (flat rules))
  end;

val rep_datatype = gen_rep_datatype Sign.cert_term;
val rep_datatype_cmd = gen_rep_datatype Syntax.read_term_global (K I);



(******************************** add datatype ********************************)

fun gen_add_datatype prep_typ err flat_names new_type_names dts thy =
  let
    val _ = Theory.requires thy "Datatype" "datatype definitions";

    (* this theory is used just for parsing *)

    val tmp_thy = thy |>
      Theory.copy |>
      Sign.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) dts);

    val (tyvars, _, _, _)::_ = dts;
    val (new_dts, types_syntax) = ListPair.unzip (map (fn (tvs, tname, mx, _) =>
      let val full_tname = Sign.full_bname tmp_thy (Syntax.type_name tname mx)
      in (case duplicates (op =) tvs of
            [] => if eq_set (tyvars, tvs) then ((full_tname, tvs), (tname, mx))
                  else error ("Mutually recursive datatypes must have same type parameters")
          | dups => error ("Duplicate parameter(s) for datatype " ^ full_tname ^
              " : " ^ commas dups))
      end) dts);

    val _ = (case duplicates (op =) (map fst new_dts) @ duplicates (op =) new_type_names of
      [] => () | dups => error ("Duplicate datatypes: " ^ commas dups));

    fun prep_dt_spec (tvs, tname, mx, constrs) (dts', constr_syntax, sorts, i) =
      let
        fun prep_constr (cname, cargs, mx') (constrs, constr_syntax', sorts') =
          let
            val (cargs', sorts'') = Library.foldl (prep_typ tmp_thy) (([], sorts'), cargs);
            val _ = (case fold (curry OldTerm.add_typ_tfree_names) cargs' [] \\ tvs of
                [] => ()
              | vs => error ("Extra type variables on rhs: " ^ commas vs))
          in (constrs @ [((if flat_names then Sign.full_bname tmp_thy else
                Sign.full_bname_path tmp_thy tname) (Syntax.const_name cname mx'),
                   map (dtyp_of_typ new_dts) cargs')],
              constr_syntax' @ [(cname, mx')], sorts'')
          end handle ERROR msg =>
            cat_error msg ("The error above occured in constructor " ^ cname ^
              " of datatype " ^ tname);

        val (constrs', constr_syntax', sorts') =
          fold prep_constr constrs ([], [], sorts)

      in
        case duplicates (op =) (map fst constrs') of
           [] =>
             (dts' @ [(i, (Sign.full_bname tmp_thy (Syntax.type_name tname mx),
                map DtTFree tvs, constrs'))],
              constr_syntax @ [constr_syntax'], sorts', i + 1)
         | dups => error ("Duplicate constructors " ^ commas dups ^
             " in datatype " ^ tname)
      end;

    val (dts', constr_syntax, sorts', i) = fold prep_dt_spec dts ([], [], [], 0);
    val sorts = sorts' @ (map (rpair (Sign.defaultS tmp_thy)) (tyvars \\ map fst sorts'));
    val dt_info = get_datatypes thy;
    val (descr, _) = unfold_datatypes tmp_thy dts' sorts dt_info dts' i;
    val _ = check_nonempty descr handle (exn as Datatype_Empty s) =>
      if err then error ("Nonemptiness check failed for datatype " ^ s)
      else raise exn;

    val descr' = flat descr;
    val case_names_induct = mk_case_names_induct descr';
    val case_names_exhausts = mk_case_names_exhausts descr' (map #1 new_dts);
  in
    add_datatype_def
      flat_names new_type_names descr sorts types_syntax constr_syntax dt_info
      case_names_induct case_names_exhausts thy
  end;

val add_datatype = gen_add_datatype cert_typ;
val add_datatype_cmd = gen_add_datatype read_typ true;


(** a datatype antiquotation **)

local

val sym_datatype = Pretty.command "datatype";
val sym_binder = Pretty.str "\\ {\\isacharequal}"; (*FIXME use proper symbol*)
val sym_sep = Pretty.str "{\\isacharbar}\\ ";

in

fun args_datatype (ctxt, args) =
  let
    val (tyco, (ctxt', args')) = Args.tyname (ctxt, args);
    val thy = Context.theory_of ctxt';
    val spec = the_datatype_spec thy tyco;
  in ((tyco, spec), (ctxt', args')) end;

fun pretty_datatype ctxt (dtco, (vs, cos)) =
  let
    val ty = Type (dtco, map TFree vs);
    fun pretty_typ_br ty =
      let
        val p = Syntax.pretty_typ ctxt ty;
        val s = explode (Pretty.str_of p);
      in if member (op =) s " " then Pretty.enclose "(" ")" [p]
        else p
      end;
    fun pretty_constr (co, []) =
          Syntax.pretty_term ctxt (Const (co, ty))
      | pretty_constr (co, [ty']) =
          (Pretty.block o Pretty.breaks)
            [Syntax.pretty_term ctxt (Const (co, ty' --> ty)),
              pretty_typ_br ty']
      | pretty_constr (co, tys) =
          (Pretty.block o Pretty.breaks)
            (Syntax.pretty_term ctxt (Const (co, tys ---> ty)) ::
              map pretty_typ_br tys);
  in
    Pretty.block
      (sym_datatype :: Pretty.brk 1 ::
       Syntax.pretty_typ ctxt ty ::
       sym_binder :: Pretty.brk 1 ::
       flat (separate [Pretty.brk 1, sym_sep]
         (map (single o pretty_constr) cos)))
  end

end;

(** package setup **)

(* setup theory *)

val setup =
  DatatypeRepProofs.distinctness_limit_setup #>
  simproc_setup #>
  trfun_setup #>
  DatatypeInterpretation.init;


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val datatype_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.type_args -- P.name -- P.opt_infix --
    (P.$$$ "=" |-- P.enum1 "|" (P.name -- Scan.repeat P.typ -- P.opt_mixfix));

fun mk_datatype args =
  let
    val names = map (fn ((((NONE, _), t), _), _) => t | ((((SOME t, _), _), _), _) => t) args;
    val specs = map (fn ((((_, vs), t), mx), cons) =>
      (vs, t, mx, map (fn ((x, y), z) => (x, y, z)) cons)) args;
  in snd o add_datatype_cmd false names specs end;

val _ =
  OuterSyntax.command "datatype" "define inductive datatypes" K.thy_decl
    (P.and_list1 datatype_decl >> (Toplevel.theory o mk_datatype));

val _ =
  OuterSyntax.command "rep_datatype" "represent existing types inductively" K.thy_goal
    (Scan.option (P.$$$ "(" |-- Scan.repeat1 P.name --| P.$$$ ")") -- Scan.repeat1 P.term
      >> (fn (alt_names, ts) => Toplevel.print
           o Toplevel.theory_to_proof (rep_datatype_cmd alt_names ts)));

val _ =
  ThyOutput.add_commands [("datatype",
    ThyOutput.args args_datatype (ThyOutput.output pretty_datatype))];

end;

end;

