(*  Title:      HOL/Tools/datatype_package.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Datatype package for Isabelle/HOL.
*)

signature BASIC_DATATYPE_PACKAGE =
sig
  val induct_tac : string -> int -> tactic
  val induct_thm_tac : thm -> string -> int -> tactic
  val case_tac : string -> int -> tactic
  val distinct_simproc : simproc
end;

signature DATATYPE_PACKAGE =
sig
  include BASIC_DATATYPE_PACKAGE
  val quiet_mode : bool ref
  val add_datatype_i : bool -> bool -> string list -> (string list * bstring * mixfix *
    (bstring * typ list * mixfix) list) list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} * theory
  val add_datatype : bool -> string list -> (string list * bstring * mixfix *
    (bstring * string list * mixfix) list) list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} * theory
  val rep_datatype_i : string list option -> (thm list * attribute list) list list ->
    (thm list * attribute list) list list -> (thm list * attribute list) ->
    theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} * theory
  val rep_datatype : string list option -> (thmref * Attrib.src list) list list ->
    (thmref * Attrib.src list) list list -> thmref * Attrib.src list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       simps : thm list} * theory
  val get_datatypes : theory -> DatatypeAux.datatype_info Symtab.table
  val get_datatype : theory -> string -> DatatypeAux.datatype_info option
  val the_datatype : theory -> string -> DatatypeAux.datatype_info
  val datatype_of_constr : theory -> string -> DatatypeAux.datatype_info option
  val datatype_of_case : theory -> string -> DatatypeAux.datatype_info option
  val get_datatype_spec : theory -> string -> ((string * sort) list * (string * typ list) list) option
  val get_datatype_constrs : theory -> string -> (string * typ) list option
  val interpretation: (string list -> theory -> theory) -> theory -> theory
  val print_datatypes : theory -> unit
  val make_case :  Proof.context -> bool -> string list -> term ->
    (term * term) list -> term * (term * (int * bool)) list
  val strip_case: Proof.context -> bool ->
    term -> (term * (term * term) list) option
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

fun get_datatype_spec thy dtco =
  let
    fun mk_cons typ_of_dtyp (co, tys) =
      (co, map typ_of_dtyp tys);
    fun mk_dtyp ({ sorts = raw_sorts, descr, ... } : DatatypeAux.datatype_info, (dtys, cos)) =
      let
        val sorts = map ((fn v => (v, (the o AList.lookup (op =) raw_sorts) v))
          o DatatypeAux.dest_DtTFree) dtys;
        val typ_of_dtyp = DatatypeAux.typ_of_dtyp descr sorts;
        val tys = map typ_of_dtyp dtys;
      in (sorts, map (mk_cons typ_of_dtyp) cos) end;
  in Option.map mk_dtyp (get_datatype_descr thy dtco) end;

fun get_datatype_constrs thy dtco =
  case get_datatype_spec thy dtco
   of SOME (sorts, cos) =>
        let
          fun subst (v, sort) = TVar ((v, 0), sort);
          fun subst_ty (TFree v) = subst v
            | subst_ty ty = ty;
          val dty = Type (dtco, map subst sorts);
          fun mk_co (co, tys) = (co, map (Term.map_atyps subst_ty) tys ---> dty);
        in SOME (map mk_co cos) end
    | NONE => NONE;

fun find_tname var Bi =
  let val frees = map dest_Free (term_frees Bi)
      val params = rename_wrt_term Bi (Logic.strip_params Bi);
  in case AList.lookup (op =) (frees @ params) var of
       NONE => error ("No such variable in subgoal: " ^ quote var)
     | SOME(Type (tn, _)) => tn
     | _ => error ("Cannot determine type of " ^ quote var)
  end;

fun infer_tname state i aterm =
  let
    val sign = Thm.theory_of_thm state;
    val (_, _, Bi, _) = Thm.dest_state (state, i)
    val params = Logic.strip_params Bi;   (*params of subgoal i*)
    val params = rev (rename_wrt_term Bi params);   (*as they are printed*)
    val (types, sorts) = types_sorts state;
    fun types' (a, ~1) = (case AList.lookup (op =) params a of NONE => types(a, ~1) | sm => sm)
      | types' ixn = types ixn;
    val ([ct], _) = Thm.read_def_cterms (sign, types', sorts) [] false [(aterm, dummyT)];
  in case #T (rep_cterm ct) of
       Type (tn, _) => tn
     | _ => error ("Cannot determine type of " ^ quote aterm)
  end;

(*Warn if the (induction) variable occurs Free among the premises, which
  usually signals a mistake.  But calls the tactic either way!*)
fun occs_in_prems tacf vars =
  SUBGOAL (fn (Bi, i) =>
           (if exists (fn (a, _) => member (op =) vars a)
                      (fold Term.add_frees (#2 (strip_context Bi)) [])
             then warning "Induction variable occurs also among premises!"
             else ();
            tacf i));


(* generic induction tactic for datatypes *)

local

fun prep_var (Var (ixn, _), SOME x) = SOME (ixn, x)
  | prep_var _ = NONE;

fun prep_inst (concl, xs) = (*exception Library.UnequalLengths*)
  let val vs = Induct.vars_of concl
  in map_filter prep_var (Library.drop (length vs - length xs, vs) ~~ xs) end;

in

fun gen_induct_tac inst_tac (varss, opt_rule) i state =
  SUBGOAL (fn (Bi,_) =>
  let
    val (rule, rule_name) =
      case opt_rule of
          SOME r => (r, "Induction rule")
        | NONE =>
            let val tn = find_tname (hd (map_filter I (flat varss))) Bi
                val thy = Thm.theory_of_thm state
            in (#induction (the_datatype thy tn), "Induction rule for type " ^ tn)
            end
    val concls = HOLogic.dest_concls (Thm.concl_of rule);
    val insts = maps prep_inst (concls ~~ varss) handle Library.UnequalLengths =>
      error (rule_name ^ " has different numbers of variables");
  in occs_in_prems (inst_tac insts rule) (map #2 insts) i end)
  i state;

fun induct_tac s =
  gen_induct_tac Tactic.res_inst_tac'
    (map (single o SOME) (Syntax.read_idents s), NONE);

fun induct_thm_tac th s =
  gen_induct_tac Tactic.res_inst_tac'
    ([map SOME (Syntax.read_idents s)], SOME th);

end;


(* generic case tactic for datatypes *)

fun case_inst_tac inst_tac t rule i state =
  let
    val _ $ Var (ixn, _) $ _ = HOLogic.dest_Trueprop
      (hd (Logic.strip_assums_hyp (hd (Thm.prems_of rule))));
  in inst_tac [(ixn, t)] rule i state end;

fun gen_case_tac inst_tac (t, SOME rule) i state =
      case_inst_tac inst_tac t rule i state
  | gen_case_tac inst_tac (t, NONE) i state =
      let val tn = infer_tname state i t in
        if tn = HOLogic.boolN then inst_tac [(("P", 0), t)] case_split_thm i state
        else case_inst_tac inst_tac t
               (#exhaustion (the_datatype (Thm.theory_of_thm state) tn))
               i state
      end handle THM _ => Seq.empty;

fun case_tac t = gen_case_tac Tactic.res_inst_tac' (t, NONE);



(** Isar tactic emulations **)

local

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.$$$ ":");
val opt_rule = Scan.option (rule_spec |-- Attrib.thm);

val varss =
  Args.and_list (Scan.repeat (Scan.unless rule_spec (Scan.lift (Args.maybe Args.name))));

val inst_tac = RuleInsts.bires_inst_tac false;

fun induct_meth ctxt (varss, opt_rule) =
  gen_induct_tac (inst_tac ctxt) (varss, opt_rule);
fun case_meth ctxt (varss, opt_rule) =
  gen_case_tac (inst_tac ctxt) (varss, opt_rule);

in

val tactic_emulations =
 [("induct_tac", Method.goal_args_ctxt' (varss -- opt_rule) induct_meth,
    "induct_tac emulation (dynamic instantiation)"),
  ("case_tac", Method.goal_args_ctxt' (Scan.lift Args.name -- opt_rule) case_meth,
    "case_tac emulation (dynamic instantiation)")];

end;



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
  PureThy.add_thmss [(("simps", simps), []),
    (("", flat case_thms @
          flat distinct @ rec_thms), [Simplifier.simp_add]),
    (("", rec_thms), [RecfunCodegen.add_default]),
    (("", flat inject), [iff_add]),
    (("", map (fn th => th RS notE) (flat distinct)), [Classical.safe_elim NONE]),
    (("", weak_case_congs), [cong_att])]
  #> snd;


(* add_cases_induct *)

fun add_cases_induct infos induction thy =
  let
    val inducts = ProjectRule.projections (ProofContext.init thy) induction;

    fun named_rules (name, {index, exhaustion, ...}: datatype_info) =
      [(("", nth inducts index), [Induct.induct_type name]),
       (("", exhaustion), [Induct.cases_type name])];
    fun unnamed_rule i =
      (("", nth inducts i), [PureThy.kind_internal, Induct.induct_type ""]);
  in
    thy |> PureThy.add_thms
      (maps named_rules infos @
        map unnamed_rule (length infos upto length inducts - 1)) |> snd
    |> PureThy.add_thmss [(("inducts", inducts), [])] |> snd
  end;



(**** simplification procedure for showing distinctness of constructors ****)

fun stripT (i, Type ("fun", [_, T])) = stripT (i + 1, T)
  | stripT p = p;

fun stripC (i, f $ x) = stripC (i + 1, f)
  | stripC p = p;

val distinctN = "constr_distinct";

exception ConstrDistinct of term;

fun distinct_proc thy ss (t as Const ("op =", _) $ t1 $ t2) =
  (case (stripC (0, t1), stripC (0, t2)) of
     ((i, Const (cname1, T1)), (j, Const (cname2, T2))) =>
         (case (stripT (0, T1), stripT (0, T2)) of
            ((i', Type (tname1, _)), (j', Type (tname2, _))) =>
                if tname1 = tname2 andalso not (cname1 = cname2) andalso i = i' andalso j = j' then
                   (case (get_datatype_descr thy) tname1 of
                      SOME (_, (_, constrs)) => let val cnames = map fst constrs
                        in if cname1 mem cnames andalso cname2 mem cnames then
                             let val eq_t = Logic.mk_equals (t, Const ("False", HOLogic.boolT));
                                 val eq_ct = cterm_of thy eq_t;
                                 val Datatype_thy = ThyInfo.the_theory "Datatype" thy;
                                 val [In0_inject, In1_inject, In0_not_In1, In1_not_In0] =
                                   map (get_thm Datatype_thy o Name)
                                     ["In0_inject", "In1_inject", "In0_not_In1", "In1_not_In0"]
                             in (case (#distinct (the_datatype thy tname1)) of
                                 QuickAndDirty => SOME (Thm.invoke_oracle
                                   Datatype_thy distinctN (thy, ConstrDistinct eq_t))
                               | FewConstrs thms =>
                                   SOME (Goal.prove (Simplifier.the_context ss) [] [] eq_t (K
                                     (EVERY [rtac eq_reflection 1, rtac iffI 1, rtac notE 1,
                                       atac 2, resolve_tac thms 1, etac FalseE 1])))
                               | ManyConstrs (thm, simpset) =>
                                   SOME (Goal.prove (Simplifier.the_context ss) [] [] eq_t (K
                                     (EVERY [rtac eq_reflection 1, rtac iffI 1, dtac thm 1,
                                      full_simp_tac (Simplifier.inherit_context ss simpset) 1,
                                      REPEAT (dresolve_tac [In0_inject, In1_inject] 1),
                                      eresolve_tac [In0_not_In1 RS notE, In1_not_In0 RS notE] 1,
                                      etac FalseE 1]))))
                             end
                           else NONE
                        end
                    | NONE => NONE)
                else NONE
          | _ => NONE)
   | _ => NONE)
  | distinct_proc _ _ _ = NONE;

val distinct_simproc =
  Simplifier.simproc HOL.thy distinctN ["s = t"] distinct_proc;

val dist_ss = HOL_ss addsimprocs [distinct_simproc];

val simproc_setup =
  Theory.add_oracle (distinctN, fn (_, ConstrDistinct t) => t) #>
  (fn thy => ((change_simpset_of thy) (fn ss => ss addsimprocs [distinct_simproc]); thy));


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

fun read_typ sign ((Ts, sorts), str) =
  let
    val T = Type.no_tvars (Sign.read_def_typ (sign, AList.lookup (op =)
      (map (apfst (rpair ~1)) sorts)) str) handle TYPE (msg, _, _) => error msg
  in (Ts @ [T], add_typ_tfrees (T, sorts)) end;

fun cert_typ sign ((Ts, sorts), raw_T) =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle
      TYPE (msg, _, _) => error msg;
    val sorts' = add_typ_tfrees (T, sorts)
  in (Ts @ [T],
      case duplicates (op =) (map fst sorts') of
         [] => sorts'
       | dups => error ("Inconsistent sort constraints for " ^ commas dups))
  end;


(**** make datatype info ****)

fun make_dt_info head_len descr sorts induct reccomb_names rec_thms
    (((((((((i, (_, (tname, _, _))), case_name), case_thms),
      exhaustion_thm), distinct_thm), inject), nchotomy), case_cong), weak_case_cong) =
  (tname,
   {index = i,
    head_len = head_len,
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


(********************* axiomatic introduction of datatypes ********************)

fun add_axiom label t atts thy =
  thy
  |> PureThy.add_axioms_i [((label, t), atts)];

fun add_axioms label ts atts thy =
  thy
  |> PureThy.add_axiomss_i [((label, ts), atts)];

fun add_and_get_axioms_atts label tnames ts attss =
  fold_map (fn (tname, (atts, t)) => fn thy =>
    thy
    |> Sign.add_path tname
    |> add_axiom label t atts
    ||> Sign.parent_path
    |-> (fn [ax] => pair ax)) (tnames ~~ (attss ~~ ts));

fun add_and_get_axioms label tnames ts =
  add_and_get_axioms_atts label tnames ts (replicate (length tnames) []);

fun add_and_get_axiomss label tnames tss =
  fold_map (fn (tname, ts) => fn thy =>
    thy
    |> Sign.add_path tname
    |> add_axioms label ts []
    ||> Sign.parent_path
    |-> (fn [ax] => pair ax)) (tnames ~~ tss);

fun gen_specify_consts add args thy =
  let
    val specs = map (fn (c, T, mx) =>
      Const (Sign.full_name thy (Syntax.const_name c mx), T)) args;
  in
    thy
    |> add args
    |> Theory.add_finals_i false specs
  end;

val specify_consts = gen_specify_consts Sign.add_consts_i;
val specify_consts_authentic = gen_specify_consts (fold (snd oo Sign.declare_const []));

structure DatatypeInterpretation = InterpretationFun(type T = string list val eq = op =);
val interpretation = DatatypeInterpretation.interpretation;

fun add_datatype_axm flat_names new_type_names descr sorts types_syntax constr_syntax dt_info
    case_names_induct case_names_exhausts thy =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used = map fst (fold Term.add_tfreesT recTs []);
    val newTs = Library.take (length (hd descr), recTs);

    (**** declare new types and constants ****)

    val tyvars = map (fn (_, (_, Ts, _)) => map dest_DtTFree Ts) (hd descr);

    val constr_decls = map (fn (((_, (_, _, constrs)), T), constr_syntax') =>
      map (fn ((_, cargs), (cname, mx)) =>
        (cname, map (typ_of_dtyp descr' sorts) cargs ---> T, mx))
          (constrs ~~ constr_syntax')) ((hd descr) ~~ newTs ~~ constr_syntax);

    val (rec_result_Ts, reccomb_fn_Ts) = DatatypeProp.make_primrec_Ts descr sorts used;

    val big_reccomb_name = (space_implode "_" new_type_names) ^ "_rec";
    val reccomb_names = if length descr' = 1 then [big_reccomb_name] else
      (map ((curry (op ^) (big_reccomb_name ^ "_")) o string_of_int)
        (1 upto (length descr')));

    val freeT = TFree (Name.variant used "'t", HOLogic.typeS);
    val case_fn_Ts = map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let val Ts = map (typ_of_dtyp descr' sorts) cargs
        in Ts ---> freeT end) constrs) (hd descr);

    val case_names = map (fn s => (s ^ "_case")) new_type_names;

    val thy2' = thy

      (** new types **)
      |> fold2 (fn (name, mx) => fn tvs => Typedecl.add (name, tvs, mx) #> snd)
           types_syntax tyvars
      |> add_path flat_names (space_implode "_" new_type_names)

      (** primrec combinators **)

      |> specify_consts (map (fn ((name, T), T') =>
           (name, reccomb_fn_Ts @ [T] ---> T', NoSyn)) (reccomb_names ~~ recTs ~~ rec_result_Ts))

      (** case combinators **)

      |> specify_consts_authentic (map (fn ((name, T), Ts) =>
           (name, Ts @ [T] ---> freeT, NoSyn)) (case_names ~~ newTs ~~ case_fn_Ts));

    val reccomb_names' = map (Sign.full_name thy2') reccomb_names;
    val case_names' = map (Sign.full_name thy2') case_names;

    val thy2 = thy2'

      (** constructors **)

      |> parent_path flat_names
      |> fold (fn ((((_, (_, _, constrs)), T), tname),
        constr_syntax') =>
          add_path flat_names tname #>
            specify_consts (map (fn ((_, cargs), (cname, mx)) =>
              (cname, map (typ_of_dtyp descr' sorts) cargs ---> T, mx))
                (constrs ~~ constr_syntax')) #>
          parent_path flat_names)
            (hd descr ~~ newTs ~~ new_type_names ~~ constr_syntax);

    (**** introduction of axioms ****)

    val rec_axs = DatatypeProp.make_primrecs new_type_names descr sorts thy2;

    val ((([induct], [rec_thms]), inject), thy3) =
      thy2
      |> Sign.add_path (space_implode "_" new_type_names)
      |> add_axiom "induct" (DatatypeProp.make_ind descr sorts) [case_names_induct]
      ||>> add_axioms "recs" rec_axs []
      ||> Sign.parent_path
      ||>> add_and_get_axiomss "inject" new_type_names
            (DatatypeProp.make_injs descr sorts);
    val (distinct, thy4) = add_and_get_axiomss "distinct" new_type_names
      (DatatypeProp.make_distincts new_type_names descr sorts thy3) thy3;

    val exhaust_ts = DatatypeProp.make_casedists descr sorts;
    val (exhaustion, thy5) = add_and_get_axioms_atts "exhaust" new_type_names
      exhaust_ts (map single case_names_exhausts) thy4;
    val (case_thms, thy6) = add_and_get_axiomss "cases" new_type_names
      (DatatypeProp.make_cases new_type_names descr sorts thy5) thy5;
    val (split_ts, split_asm_ts) = ListPair.unzip
      (DatatypeProp.make_splits new_type_names descr sorts thy6);
    val (split, thy7) = add_and_get_axioms "split" new_type_names split_ts thy6;
    val (split_asm, thy8) = add_and_get_axioms "split_asm" new_type_names
      split_asm_ts thy7;
    val (nchotomys, thy9) = add_and_get_axioms "nchotomy" new_type_names
      (DatatypeProp.make_nchotomys descr sorts) thy8;
    val (case_congs, thy10) = add_and_get_axioms "case_cong" new_type_names
      (DatatypeProp.make_case_congs new_type_names descr sorts thy9) thy9;
    val (weak_case_congs, thy11) = add_and_get_axioms "weak_case_cong" new_type_names
      (DatatypeProp.make_weak_case_congs new_type_names descr sorts thy10) thy10;

    val dt_infos = map (make_dt_info (length (hd descr)) descr' sorts induct
        reccomb_names' rec_thms)
      ((0 upto length (hd descr) - 1) ~~ (hd descr) ~~ case_names' ~~ case_thms ~~
        exhaustion ~~ replicate (length (hd descr)) QuickAndDirty ~~ inject ~~
          nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ rec_thms;
    val split_thms = split ~~ split_asm;

    val thy12 =
      thy11
      |> add_case_tr' case_names'
      |> Sign.add_path (space_implode "_" new_type_names)
      |> add_rules simps case_thms rec_thms inject distinct
          weak_case_congs Simplifier.cong_add
      |> put_dt_infos dt_infos
      |> add_cases_induct dt_infos induct
      |> Sign.parent_path
      |> store_thmss "splits" new_type_names (map (fn (x, y) => [x, y]) split_thms)
      |> snd
      |> DatatypeInterpretation.data (map fst dt_infos);
  in
    ({distinct = distinct,
      inject = inject,
      exhaustion = exhaustion,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induct,
      simps = simps}, thy12)
  end;


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

    val dt_infos = map (make_dt_info (length (hd descr)) (flat descr) sorts induct
        reccomb_names rec_thms)
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

fun gen_rep_datatype apply_theorems alt_names raw_distinct raw_inject raw_induction thy0 =
  let
    val (((distinct, inject), [induction]), thy1) =
      thy0
      |> fold_map apply_theorems raw_distinct
      ||>> fold_map apply_theorems raw_inject
      ||>> apply_theorems [raw_induction];

    val ((_, [induction']), _) =
      Variable.importT_thms [induction] (Variable.thm_context induction);

    fun err t = error ("Ill-formed predicate in induction rule: " ^
      Sign.string_of_term thy1 t);

    fun get_typ (t as _ $ Var (_, Type (tname, Ts))) =
          ((tname, map dest_TFree Ts) handle TERM _ => err t)
      | get_typ t = err t;

    val dtnames = map get_typ (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of induction')));
    val new_type_names = getOpt (alt_names, map fst dtnames);

    fun get_constr t = (case Logic.strip_assums_concl t of
        _ $ (_ $ t') => (case head_of t' of
            Const (cname, cT) => (case strip_type cT of
                (Ts, Type (tname, _)) => (tname, (cname, map (dtyp_of_typ dtnames) Ts))
              | _ => err t)
          | _ => err t)
      | _ => err t);

    fun make_dt_spec [] _ _ = []
      | make_dt_spec ((tname, tvs)::dtnames') i constrs =
          let val (constrs', constrs'') = take_prefix (equal tname o fst) constrs
          in (i, (tname, map DtTFree tvs, map snd constrs'))::
            (make_dt_spec dtnames' (i + 1) constrs'')
          end;

    val descr = make_dt_spec dtnames 0 (map get_constr (prems_of induction'));
    val sorts = add_term_tfrees (concl_of induction', []);
    val dt_info = get_datatypes thy1;

    val (case_names_induct, case_names_exhausts) =
      (mk_case_names_induct descr, mk_case_names_exhausts descr (map #1 dtnames));

    val _ = message ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val (casedist_thms, thy2) = thy1 |>
      DatatypeAbsProofs.prove_casedist_thms new_type_names [descr] sorts induction
        case_names_exhausts;
    val ((reccomb_names, rec_thms), thy3) = DatatypeAbsProofs.prove_primrec_thms
      false new_type_names [descr] sorts dt_info inject distinct
      (Simplifier.theory_context thy2 dist_ss) induction thy2;
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

    val ((_, [induction']), thy10) =
      thy8
      |> store_thmss "inject" new_type_names inject
      ||>> store_thmss "distinct" new_type_names distinct
      ||> Sign.add_path (space_implode "_" new_type_names)
      ||>> PureThy.add_thms [(("induct", induction), [case_names_induct])];

    val dt_infos = map (make_dt_info (length descr) descr sorts induction'
        reccomb_names rec_thms)
      ((0 upto length descr - 1) ~~ descr ~~ case_names ~~ case_thms ~~ casedist_thms ~~
        map FewConstrs distinct ~~ inject ~~ nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ rec_thms;

    val thy11 =
      thy10
      |> add_case_tr' case_names
      |> add_rules simps case_thms rec_thms inject distinct
           weak_case_congs (Simplifier.attrib (op addcongs))
      |> put_dt_infos dt_infos
      |> add_cases_induct dt_infos induction'
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
      induction = induction',
      simps = simps}, thy11)
  end;

val rep_datatype = gen_rep_datatype IsarCmd.apply_theorems;
val rep_datatype_i = gen_rep_datatype IsarCmd.apply_theorems_i;



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
      let val full_tname = Sign.full_name tmp_thy (Syntax.type_name tname mx)
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
            val _ = (case fold (curry add_typ_tfree_names) cargs' [] \\ tvs of
                [] => ()
              | vs => error ("Extra type variables on rhs: " ^ commas vs))
          in (constrs @ [((if flat_names then Sign.full_name tmp_thy else
                Sign.full_name_path tmp_thy tname) (Syntax.const_name cname mx'),
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
             (dts' @ [(i, (Sign.full_name tmp_thy (Syntax.type_name tname mx),
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
    (if (!quick_and_dirty) then add_datatype_axm else add_datatype_def)
      flat_names new_type_names descr sorts types_syntax constr_syntax dt_info
      case_names_induct case_names_exhausts thy
  end;

val add_datatype_i = gen_add_datatype cert_typ;
val add_datatype = gen_add_datatype read_typ true;



(** package setup **)

(* setup theory *)

val setup =
  DatatypeProp.distinctness_limit_setup #>
  Method.add_methods tactic_emulations #>
  simproc_setup #>
  trfun_setup #>
  DatatypeInterpretation.init;


(* outer syntax *)

local structure P = OuterParse and K = OuterKeyword in

val _ = OuterSyntax.keywords ["distinct", "inject", "induction"];

val datatype_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.type_args -- P.name -- P.opt_infix --
    (P.$$$ "=" |-- P.enum1 "|" (P.name -- Scan.repeat P.typ -- P.opt_mixfix));

fun mk_datatype args =
  let
    val names = map (fn ((((NONE, _), t), _), _) => t | ((((SOME t, _), _), _), _) => t) args;
    val specs = map (fn ((((_, vs), t), mx), cons) =>
      (vs, t, mx, map (fn ((x, y), z) => (x, y, z)) cons)) args;
  in snd o add_datatype false names specs end;

val _ =
  OuterSyntax.command "datatype" "define inductive datatypes" K.thy_decl
    (P.and_list1 datatype_decl >> (Toplevel.theory o mk_datatype));


val rep_datatype_decl =
  Scan.option (Scan.repeat1 P.name) --
    Scan.optional (P.$$$ "distinct" |-- P.!!! (P.and_list1 SpecParse.xthms1)) [[]] --
    Scan.optional (P.$$$ "inject" |-- P.!!! (P.and_list1 SpecParse.xthms1)) [[]] --
    (P.$$$ "induction" |-- P.!!! SpecParse.xthm);

fun mk_rep_datatype (((opt_ts, dss), iss), ind) = #2 o rep_datatype opt_ts dss iss ind;

val _ =
  OuterSyntax.command "rep_datatype" "represent existing types inductively" K.thy_decl
    (rep_datatype_decl >> (Toplevel.theory o mk_rep_datatype));

end;


end;

structure BasicDatatypePackage: BASIC_DATATYPE_PACKAGE = DatatypePackage;
open BasicDatatypePackage;

