(*  Title:      HOL/Tools/datatype.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package for Isabelle/HOL.
*)

signature DATATYPE =
sig
  include DATATYPE_COMMON
  val add_datatype : config -> string list -> (string list * binding * mixfix *
    (binding * typ list * mixfix) list) list -> theory -> string list * theory
  val datatype_cmd : string list -> (string list * binding * mixfix *
    (binding * string list * mixfix) list) list -> theory -> theory
  val rep_datatype : config -> (string list -> Proof.context -> Proof.context)
    -> string list option -> term list -> theory -> Proof.state
  val rep_datatype_cmd : string list option -> string list -> theory -> Proof.state
  val get_info : theory -> string -> info option
  val the_info : theory -> string -> info
  val the_descr : theory -> string list
    -> descr * (string * sort) list * string list
      * string * (string list * string list) * (typ list * typ list)
  val the_spec : theory -> string -> (string * sort) list * (string * typ list) list
  val get_constrs : theory -> string -> (string * typ) list option
  val get_all : theory -> info Symtab.table
  val info_of_constr : theory -> string -> info option
  val info_of_case : theory -> string -> info option
  val interpretation : (config -> string list -> theory -> theory) -> theory -> theory
  val distinct_simproc : simproc
  val make_case :  Proof.context -> bool -> string list -> term ->
    (term * term) list -> term * (term * (int * bool)) list
  val strip_case : Proof.context -> bool -> term -> (term * (term * term) list) option
  val read_typ: theory ->
    (typ list * (string * sort) list) * string -> typ list * (string * sort) list
  val setup: theory -> theory
end;

structure Datatype : DATATYPE =
struct

open DatatypeAux;


(* theory data *)

structure DatatypesData = TheoryDataFun
(
  type T =
    {types: info Symtab.table,
     constrs: info Symtab.table,
     cases: info Symtab.table};

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

val get_all = #types o DatatypesData.get;
val map_datatypes = DatatypesData.map;


(** theory information about datatypes **)

fun put_dt_infos (dt_infos : (string * info) list) =
  map_datatypes (fn {types, constrs, cases} =>
    {types = fold Symtab.update dt_infos types,
     constrs = fold Symtab.default (*conservative wrt. overloaded constructors*)
       (maps (fn (_, info as {descr, index, ...}) => map (rpair info o fst)
          (#3 (the (AList.lookup op = descr index)))) dt_infos) constrs,
     cases = fold Symtab.update
       (map (fn (_, info as {case_name, ...}) => (case_name, info)) dt_infos)
       cases});

val get_info = Symtab.lookup o get_all;

fun the_info thy name = (case get_info thy name of
      SOME info => info
    | NONE => error ("Unknown datatype " ^ quote name));

val info_of_constr = Symtab.lookup o #constrs o DatatypesData.get;
val info_of_case = Symtab.lookup o #cases o DatatypesData.get;

fun get_info_descr thy dtco =
  get_info thy dtco
  |> Option.map (fn info as { descr, index, ... } =>
       (info, (((fn SOME (_, dtys, cos) => (dtys, cos)) o AList.lookup (op =) descr) index)));

fun the_spec thy dtco =
  let
    val info as { descr, index, sorts = raw_sorts, ... } = the_info thy dtco;
    val SOME (_, dtys, raw_cos) = AList.lookup (op =) descr index;
    val sorts = map ((fn v => (v, (the o AList.lookup (op =) raw_sorts) v))
      o DatatypeAux.dest_DtTFree) dtys;
    val cos = map
      (fn (co, tys) => (co, map (DatatypeAux.typ_of_dtyp descr sorts) tys)) raw_cos;
  in (sorts, cos) end;

fun the_descr thy (raw_tycos as raw_tyco :: _) =
  let
    val info = the_info thy raw_tyco;
    val descr = #descr info;

    val SOME (_, dtys, raw_cos) = AList.lookup (op =) descr (#index info);
    val vs = map ((fn v => (v, (the o AList.lookup (op =) (#sorts info)) v))
      o dest_DtTFree) dtys;

    fun is_DtTFree (DtTFree _) = true
      | is_DtTFree _ = false
    val k = find_index (fn (_, (_, dTs, _)) => not (forall is_DtTFree dTs)) descr;
    val protoTs as (dataTs, _) = chop k descr
      |> (pairself o map) (fn (_, (tyco, dTs, _)) => (tyco, map (typ_of_dtyp descr vs) dTs));
    
    val tycos = map fst dataTs;
    val _ = if gen_eq_set (op =) (tycos, raw_tycos) then ()
      else error ("Type constructors " ^ commas (map quote raw_tycos)
        ^ "do not belong exhaustively to one mutual recursive datatype");

    val (Ts, Us) = (pairself o map) Type protoTs;

    val names = map Long_Name.base_name (the_default tycos (#alt_names info));
    val (auxnames, _) = Name.make_context names
      |> fold_map (yield_singleton Name.variants o name_of_typ) Us;
    val prefix = space_implode "_" names;

  in (descr, vs, tycos, prefix, (names, auxnames), (Ts, Us)) end;

fun get_constrs thy dtco =
  case try (the_spec thy) dtco
   of SOME (sorts, cos) =>
        let
          fun subst (v, sort) = TVar ((v, 0), sort);
          fun subst_ty (TFree v) = subst v
            | subst_ty ty = ty;
          val dty = Type (dtco, map subst sorts);
          fun mk_co (co, tys) = (co, map (Term.map_atyps subst_ty) tys ---> dty);
        in SOME (map mk_co cos) end
    | NONE => NONE;


(** induct method setup **)

(* case names *)

local

fun dt_recs (DtTFree _) = []
  | dt_recs (DtType (_, dts)) = maps dt_recs dts
  | dt_recs (DtRec i) = [i];

fun dt_cases (descr: descr) (_, args, constrs) =
  let
    fun the_bname i = Long_Name.base_name (#1 (the (AList.lookup (op =) descr i)));
    val bnames = map the_bname (distinct (op =) (maps dt_recs args));
  in map (fn (c, _) => space_implode "_" (Long_Name.base_name c :: bnames)) constrs end;


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

    fun named_rules (name, {index, exhaustion, ...}: info) =
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

fun distinct_rule thy ss tname eq_t = case #distinct (the_info thy tname) of
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
                   (case (get_info_descr thy) tname1 of
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
  (info_of_constr (ProofContext.theory_of ctxt)) ctxt;

fun strip_case ctxt = DatatypeCase.strip_case
  (info_of_case (ProofContext.theory_of ctxt));

fun add_case_tr' case_names thy =
  Sign.add_advanced_trfuns ([], [],
    map (fn case_name =>
      let val case_name' = Sign.const_syntax_name thy case_name
      in (case_name', DatatypeCase.case_tr' info_of_case case_name')
      end) case_names, []) thy;

val trfun_setup =
  Sign.add_advanced_trfuns ([],
    [("_case_syntax", DatatypeCase.case_tr true info_of_constr)],
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

structure DatatypeInterpretation = InterpretationFun
  (type T = config * string list val eq: T * T -> bool = eq_snd op =);
fun interpretation f = DatatypeInterpretation.interpretation (uncurry f);


(******************* definitional introduction of datatypes *******************)

fun add_datatype_def (config : config) new_type_names descr sorts types_syntax constr_syntax dt_info
    case_names_induct case_names_exhausts thy =
  let
    val _ = message config ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val ((inject, distinct, dist_rewrites, simproc_dists, induct), thy2) = thy |>
      DatatypeRepProofs.representation_proofs config dt_info new_type_names descr sorts
        types_syntax constr_syntax case_names_induct;

    val (casedist_thms, thy3) = DatatypeAbsProofs.prove_casedist_thms config new_type_names descr
      sorts induct case_names_exhausts thy2;
    val ((reccomb_names, rec_thms), thy4) = DatatypeAbsProofs.prove_primrec_thms
      config new_type_names descr sorts dt_info inject dist_rewrites
      (Simplifier.theory_context thy3 dist_ss) induct thy3;
    val ((case_thms, case_names), thy6) = DatatypeAbsProofs.prove_case_thms
      config new_type_names descr sorts reccomb_names rec_thms thy4;
    val (split_thms, thy7) = DatatypeAbsProofs.prove_split_thms config new_type_names
      descr sorts inject dist_rewrites casedist_thms case_thms thy6;
    val (nchotomys, thy8) = DatatypeAbsProofs.prove_nchotomys config new_type_names
      descr sorts casedist_thms thy7;
    val (case_congs, thy9) = DatatypeAbsProofs.prove_case_congs new_type_names
      descr sorts nchotomys case_thms thy8;
    val (weak_case_congs, thy10) = DatatypeAbsProofs.prove_weak_case_congs new_type_names
      descr sorts thy9;

    val dt_infos = map
      (make_dt_info (SOME new_type_names) (flat descr) sorts induct reccomb_names rec_thms)
      ((0 upto length (hd descr) - 1) ~~ hd descr ~~ case_names ~~ case_thms ~~
        casedist_thms ~~ simproc_dists ~~ inject ~~ nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ rec_thms;
    val dt_names = map fst dt_infos;

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
      |> DatatypeInterpretation.data (config, map fst dt_infos);
  in (dt_names, thy12) end;


(*********************** declare existing type as datatype *********************)

fun prove_rep_datatype (config : config) alt_names new_type_names descr sorts induct inject half_distinct thy =
  let
    val ((_, [induct']), _) =
      Variable.importT [induct] (Variable.thm_context induct);

    fun err t = error ("Ill-formed predicate in induction rule: " ^
      Syntax.string_of_term_global thy t);

    fun get_typ (t as _ $ Var (_, Type (tname, Ts))) =
          ((tname, map (fst o dest_TFree) Ts) handle TERM _ => err t)
      | get_typ t = err t;
    val dtnames = map get_typ (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of induct')));

    val dt_info = get_all thy;

    val distinct = (map o maps) (fn thm => [thm, thm RS not_sym]) half_distinct;
    val (case_names_induct, case_names_exhausts) =
      (mk_case_names_induct descr, mk_case_names_exhausts descr (map #1 dtnames));

    val _ = message config ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val (casedist_thms, thy2) = thy |>
      DatatypeAbsProofs.prove_casedist_thms config new_type_names [descr] sorts induct
        case_names_exhausts;
    val ((reccomb_names, rec_thms), thy3) = DatatypeAbsProofs.prove_primrec_thms
      config new_type_names [descr] sorts dt_info inject distinct
      (Simplifier.theory_context thy2 dist_ss) induct thy2;
    val ((case_thms, case_names), thy4) = DatatypeAbsProofs.prove_case_thms
      config new_type_names [descr] sorts reccomb_names rec_thms thy3;
    val (split_thms, thy5) = DatatypeAbsProofs.prove_split_thms
      config new_type_names [descr] sorts inject distinct casedist_thms case_thms thy4;
    val (nchotomys, thy6) = DatatypeAbsProofs.prove_nchotomys config new_type_names
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
    val dt_names = map fst dt_infos;

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
      |> DatatypeInterpretation.data (config, dt_names);
  in (dt_names, thy11) end;

fun gen_rep_datatype prep_term (config : config) after_qed alt_names raw_ts thy =
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
        if Symtab.defined (get_all thy) tyco then SOME tyco else NONE) raw_cs
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
    val new_type_names = map Long_Name.base_name (the_default (map fst cs) alt_names);

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
          (prove_rep_datatype config alt_names new_type_names descr vs induct injs half_distincts)
        #-> after_qed
      end;
  in
    thy
    |> ProofContext.init
    |> Proof.theorem_i NONE after_qed' ((map o map) (rpair []) (flat rules))
  end;

val rep_datatype = gen_rep_datatype Sign.cert_term;
val rep_datatype_cmd = gen_rep_datatype Syntax.read_term_global default_config (K I);



(******************************** add datatype ********************************)

fun gen_add_datatype prep_typ (config : config) new_type_names dts thy =
  let
    val _ = Theory.requires thy "Datatype" "datatype definitions";

    (* this theory is used just for parsing *)

    val tmp_thy = thy |>
      Theory.copy |>
      Sign.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) dts);

    val (tyvars, _, _, _)::_ = dts;
    val (new_dts, types_syntax) = ListPair.unzip (map (fn (tvs, tname, mx, _) =>
      let val full_tname = Sign.full_name tmp_thy (Binding.map_name (Syntax.type_name mx) tname)
      in (case duplicates (op =) tvs of
            [] => if eq_set (tyvars, tvs) then ((full_tname, tvs), (tname, mx))
                  else error ("Mutually recursive datatypes must have same type parameters")
          | dups => error ("Duplicate parameter(s) for datatype " ^ quote (Binding.str_of tname) ^
              " : " ^ commas dups))
      end) dts);

    val _ = (case duplicates (op =) (map fst new_dts) @ duplicates (op =) new_type_names of
      [] => () | dups => error ("Duplicate datatypes: " ^ commas dups));

    fun prep_dt_spec ((tvs, tname, mx, constrs), tname') (dts', constr_syntax, sorts, i) =
      let
        fun prep_constr (cname, cargs, mx') (constrs, constr_syntax', sorts') =
          let
            val (cargs', sorts'') = Library.foldl (prep_typ tmp_thy) (([], sorts'), cargs);
            val _ = (case fold (curry OldTerm.add_typ_tfree_names) cargs' [] \\ tvs of
                [] => ()
              | vs => error ("Extra type variables on rhs: " ^ commas vs))
          in (constrs @ [(Sign.full_name_path tmp_thy tname'
                  (Binding.map_name (Syntax.const_name mx') cname),
                   map (dtyp_of_typ new_dts) cargs')],
              constr_syntax' @ [(cname, mx')], sorts'')
          end handle ERROR msg => cat_error msg
           ("The error above occured in constructor " ^ quote (Binding.str_of cname) ^
            " of datatype " ^ quote (Binding.str_of tname));

        val (constrs', constr_syntax', sorts') =
          fold prep_constr constrs ([], [], sorts)

      in
        case duplicates (op =) (map fst constrs') of
           [] =>
             (dts' @ [(i, (Sign.full_name tmp_thy (Binding.map_name (Syntax.type_name mx) tname),
                map DtTFree tvs, constrs'))],
              constr_syntax @ [constr_syntax'], sorts', i + 1)
         | dups => error ("Duplicate constructors " ^ commas dups ^
             " in datatype " ^ quote (Binding.str_of tname))
      end;

    val (dts', constr_syntax, sorts', i) =
      fold prep_dt_spec (dts ~~ new_type_names) ([], [], [], 0);
    val sorts = sorts' @ (map (rpair (Sign.defaultS tmp_thy)) (tyvars \\ map fst sorts'));
    val dt_info = get_all thy;
    val (descr, _) = unfold_datatypes tmp_thy dts' sorts dt_info dts' i;
    val _ = check_nonempty descr handle (exn as Datatype_Empty s) =>
      if #strict config then error ("Nonemptiness check failed for datatype " ^ s)
      else raise exn;

    val descr' = flat descr;
    val case_names_induct = mk_case_names_induct descr';
    val case_names_exhausts = mk_case_names_exhausts descr' (map #1 new_dts);
  in
    add_datatype_def
      (config : config) new_type_names descr sorts types_syntax constr_syntax dt_info
      case_names_induct case_names_exhausts thy
  end;

val add_datatype = gen_add_datatype cert_typ;
val datatype_cmd = snd ooo gen_add_datatype read_typ default_config;



(** package setup **)

(* setup theory *)

val setup =
  DatatypeRepProofs.distinctness_limit_setup #>
  simproc_setup #>
  trfun_setup #>
  DatatypeInterpretation.init;


(* outer syntax *)

local

structure P = OuterParse and K = OuterKeyword

fun prep_datatype_decls args =
  let
    val names = map
      (fn ((((NONE, _), t), _), _) => Binding.name_of t | ((((SOME t, _), _), _), _) => t) args;
    val specs = map (fn ((((_, vs), t), mx), cons) =>
      (vs, t, mx, map (fn ((x, y), z) => (x, y, z)) cons)) args;
  in (names, specs) end;

val parse_datatype_decl =
  (Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.type_args -- P.binding -- P.opt_infix --
    (P.$$$ "=" |-- P.enum1 "|" (P.binding -- Scan.repeat P.typ -- P.opt_mixfix)));

val parse_datatype_decls = P.and_list1 parse_datatype_decl >> prep_datatype_decls;

in

val _ =
  OuterSyntax.command "datatype" "define inductive datatypes" K.thy_decl
    (parse_datatype_decls >> (fn (names, specs) => Toplevel.theory (datatype_cmd names specs)));

val _ =
  OuterSyntax.command "rep_datatype" "represent existing types inductively" K.thy_goal
    (Scan.option (P.$$$ "(" |-- Scan.repeat1 P.name --| P.$$$ ")") -- Scan.repeat1 P.term
      >> (fn (alt_names, ts) => Toplevel.print
           o Toplevel.theory_to_proof (rep_datatype_cmd alt_names ts)));

end;


(* document antiquotation *)

val _ = ThyOutput.antiquotation "datatype" Args.tyname
  (fn {source = src, context = ctxt, ...} => fn dtco =>
    let
      val thy = ProofContext.theory_of ctxt;
      val (vs, cos) = the_spec thy dtco;
      val ty = Type (dtco, map TFree vs);
      fun pretty_typ_bracket (ty as Type (_, _ :: _)) =
            Pretty.enclose "(" ")" [Syntax.pretty_typ ctxt ty]
        | pretty_typ_bracket ty =
            Syntax.pretty_typ ctxt ty;
      fun pretty_constr (co, tys) =
        (Pretty.block o Pretty.breaks)
          (Syntax.pretty_term ctxt (Const (co, tys ---> ty)) ::
            map pretty_typ_bracket tys);
      val pretty_datatype =
        Pretty.block
          (Pretty.command "datatype" :: Pretty.brk 1 ::
           Syntax.pretty_typ ctxt ty ::
           Pretty.str " =" :: Pretty.brk 1 ::
           flat (separate [Pretty.brk 1, Pretty.str "| "]
             (map (single o pretty_constr) cos)));
    in ThyOutput.output (ThyOutput.maybe_pretty_source (K pretty_datatype) src [()]) end);

end;

