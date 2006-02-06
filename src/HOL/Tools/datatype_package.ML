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
  val add_datatype : bool -> string list -> (string list * bstring * mixfix *
    (bstring * string list * mixfix) list) list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
       simps : thm list} * theory
  val add_datatype_i : bool -> bool -> string list -> (string list * bstring * mixfix *
    (bstring * typ list * mixfix) list) list -> theory ->
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
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
       size : thm list,
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
       size : thm list,
       simps : thm list} * theory
  val get_datatypes : theory -> DatatypeAux.datatype_info Symtab.table
  val print_datatypes : theory -> unit
  val datatype_info : theory -> string -> DatatypeAux.datatype_info option
  val datatype_info_err : theory -> string -> DatatypeAux.datatype_info
  val is_datatype : theory -> string -> bool
  val get_datatype : theory -> string -> ((string * sort) list * string list) option
  val get_datatype_cons : theory -> string * string -> typ list option
  val get_datatype_case_consts : theory -> string list
  val get_case_const_data : theory -> string -> (string * int) list option
  val get_all_datatype_cons : theory -> (string * string) list
  val constrs_of : theory -> string -> term list option
  val case_const_of : theory -> string -> term option
  val weak_case_congs_of : theory -> thm list
  val setup: theory -> theory
end;

structure DatatypePackage : DATATYPE_PACKAGE =
struct

open DatatypeAux;

val quiet_mode = quiet_mode;


(* data kind 'HOL/datatypes' *)

structure DatatypesData = TheoryDataFun
(struct
  val name = "HOL/datatypes";
  type T = datatype_info Symtab.table;

  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ tabs : T = Symtab.merge (K true) tabs;

  fun print sg tab =
    Pretty.writeln (Pretty.strs ("datatypes:" ::
      map #1 (NameSpace.extern_table (Sign.type_space sg, tab))));
end);

val get_datatypes = DatatypesData.get;
val put_datatypes = DatatypesData.put;
val print_datatypes = DatatypesData.print;


(** theory information about datatypes **)

val datatype_info = Symtab.lookup o get_datatypes;

fun datatype_info_err thy name = (case datatype_info thy name of
      SOME info => info
    | NONE => error ("Unknown datatype " ^ quote name));

fun constrs_of thy tname = (case datatype_info thy tname of
   SOME {index, descr, ...} =>
     let val (_, _, constrs) = valOf (AList.lookup (op =) descr index)
     in SOME (map (fn (cname, _) => Const (cname, Sign.the_const_type thy cname)) constrs)
     end
 | _ => NONE);

fun case_const_of thy tname = (case datatype_info thy tname of
   SOME {case_name, ...} => SOME (Const (case_name, Sign.the_const_type thy case_name))
 | _ => NONE);

val weak_case_congs_of = map (#weak_case_cong o #2) o Symtab.dest o get_datatypes;

fun is_datatype thy dtco =
  Symtab.lookup (get_datatypes thy) dtco
  |> is_some;

fun get_datatype thy dtco =
  dtco
  |> Symtab.lookup (get_datatypes thy)
  |> Option.map (fn info => (#sorts info,
      (get_first (fn (_, (dtco', _, cs)) =>
        if dtco = dtco'
        then SOME (map fst cs)
        else NONE) (#descr info) |> the)));
  
fun get_datatype_cons thy (co, dtco) =
  let
    val descr =
      dtco
      |> Symtab.lookup (get_datatypes thy)
      |> Option.map #descr
      |> these
    val one_descr =
      descr
      |> get_first (fn (_, (dtco', vs, cs)) =>
          if dtco = dtco'
          then SOME (vs, cs)
          else NONE);
  in
    if is_some one_descr
    then
      the one_descr
      |> (fn (vs, cs) =>
          co
          |> AList.lookup (op =) cs
          |> Option.map (map (DatatypeAux.typ_of_dtyp descr (map (rpair [])
               (map DatatypeAux.dest_DtTFree vs)))))
    else NONE
  end;

fun get_datatype_case_consts thy =
  Symtab.fold (fn (_, {case_name, ...}) => cons case_name) (get_datatypes thy) [];

fun get_case_const_data thy c =
  case find_first (fn (_, {index, descr, case_name, ...}) =>
      case_name = c
    ) ((Symtab.dest o get_datatypes) thy)
   of NONE => NONE
    | SOME (_, {index, descr, ...}) =>
        (SOME o map (apsnd length) o #3 o the o AList.lookup (op =) descr) index;

fun get_all_datatype_cons thy =
  Symtab.fold (fn (dtco, _) => fold
    (fn co => cons (co, dtco))
      ((snd o the oo get_datatype) thy dtco)) (get_datatypes thy) [];

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
    val sign = Thm.sign_of_thm state;
    val (_, _, Bi, _) = Thm.dest_state (state, i)
    val params = Logic.strip_params Bi;   (*params of subgoal i*)
    val params = rev (rename_wrt_term Bi params);   (*as they are printed*)
    val (types, sorts) = types_sorts state;
    fun types' (a, ~1) = (case AList.lookup (op =) params a of NONE => types(a, ~1) | sm => sm)
      | types' ixn = types ixn;
    val (ct, _) = read_def_cterm (sign, types', sorts) [] false (aterm, TypeInfer.logicT);
  in case #T (rep_cterm ct) of
       Type (tn, _) => tn
     | _ => error ("Cannot determine type of " ^ quote aterm)
  end;

(*Warn if the (induction) variable occurs Free among the premises, which
  usually signals a mistake.  But calls the tactic either way!*)
fun occs_in_prems tacf vars =
  SUBGOAL (fn (Bi, i) =>
           (if  exists (fn Free (a, _) => a mem vars)
                      (foldr add_term_frees [] (#2 (strip_context Bi)))
             then warning "Induction variable occurs also among premises!"
             else ();
            tacf i));


(* generic induction tactic for datatypes *)

local

fun prep_var (Var (ixn, _), SOME x) = SOME (ixn, x)
  | prep_var _ = NONE;

fun prep_inst (concl, xs) =	(*exception UnequalLengths *)
  let val vs = InductAttrib.vars_of concl
  in List.mapPartial prep_var (Library.drop (length vs - length xs, vs) ~~ xs) end;

in

fun gen_induct_tac inst_tac (varss, opt_rule) i state = 
  SUBGOAL (fn (Bi,_) =>
  let
    val (rule, rule_name) =
      case opt_rule of
	  SOME r => (r, "Induction rule")
	| NONE =>
	    let val tn = find_tname (hd (List.mapPartial I (List.concat varss))) Bi
                val {sign, ...} = Thm.rep_thm state
	    in (#induction (datatype_info_err sign tn), "Induction rule for type " ^ tn) 
	    end
    val concls = HOLogic.dest_concls (Thm.concl_of rule);
    val insts = List.concat (map prep_inst (concls ~~ varss)) handle UnequalLengths =>
      error (rule_name ^ " has different numbers of variables");
  in occs_in_prems (inst_tac insts rule) (map #2 insts) i end)
  i state;

fun induct_tac s =
  gen_induct_tac Tactic.res_inst_tac'
    (map (Library.single o SOME) (Syntax.read_idents s), NONE);

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
               (#exhaustion (datatype_info_err (Thm.sign_of_thm state) tn))
               i state
      end handle THM _ => Seq.empty;

fun case_tac t = gen_case_tac Tactic.res_inst_tac' (t, NONE);



(** Isar tactic emulations **)

local

val rule_spec = Scan.lift (Args.$$$ "rule" -- Args.$$$ ":");
val opt_rule = Scan.option (rule_spec |-- Attrib.local_thm);

val varss =
  Args.and_list (Scan.repeat (Scan.unless rule_spec (Scan.lift (Args.maybe Args.name))));

val inst_tac = Method.bires_inst_tac false;

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
  | dt_recs (DtType (_, dts)) = List.concat (map dt_recs dts)
  | dt_recs (DtRec i) = [i];

fun dt_cases (descr: descr) (_, args, constrs) =
  let
    fun the_bname i = Sign.base_name (#1 (valOf (AList.lookup (op =) descr i)));
    val bnames = map the_bname (distinct (List.concat (map dt_recs args)));
  in map (fn (c, _) => space_implode "_" (Sign.base_name c :: bnames)) constrs end;


fun induct_cases descr =
  DatatypeProp.indexify_names (List.concat (map (dt_cases descr) (map #2 descr)));

fun exhaust_cases descr i = dt_cases descr (valOf (AList.lookup (op =) descr i));

in

fun mk_case_names_induct descr = RuleCases.case_names (induct_cases descr);

fun mk_case_names_exhausts descr new =
  map (RuleCases.case_names o exhaust_cases descr o #1)
    (List.filter (fn ((_, (name, _, _))) => name mem_string new) descr);

end;

(*Name management for ATP linkup. The suffix here must agree with the one given
  for notE in Clasimp.addIff*)
fun name_notE th =
    Thm.name_thm (Thm.name_of_thm th ^ "_iff1", th RS notE);
      
fun add_rules simps case_thms size_thms rec_thms inject distinct
                  weak_case_congs cong_att =
  (snd o PureThy.add_thmss [(("simps", simps), []),
    (("", List.concat case_thms @ size_thms @ 
          List.concat distinct  @ rec_thms), [Simplifier.simp_add]),
    (("", size_thms @ rec_thms),             [RecfunCodegen.add NONE]),
    (("", List.concat inject),               [iff_add]),
    (("", map name_notE (List.concat distinct)),  [Classical.safe_elim NONE]),
    (("", weak_case_congs),                  [cong_att])]);


(* add_cases_induct *)

fun add_cases_induct infos induction =
  let
    val n = length (HOLogic.dest_concls (Thm.concl_of induction));
    fun proj i = ProjectRule.project induction (i + 1);

    fun named_rules (name, {index, exhaustion, ...}: datatype_info) =
      [(("", proj index), [InductAttrib.induct_type name]),
       (("", exhaustion), [InductAttrib.cases_type name])];
    fun unnamed_rule i =
      (("", proj i), [PureThy.kind_internal, InductAttrib.induct_type ""]);
  in
    PureThy.add_thms
      (List.concat (map named_rules infos) @
        map unnamed_rule (length infos upto n - 1)) #> snd #>
    PureThy.add_thmss [(("inducts",
      map (proj #> standard #> RuleCases.save induction) (0 upto n - 1)), [])] #> snd
  end;



(**** simplification procedure for showing distinctness of constructors ****)

fun stripT (i, Type ("fun", [_, T])) = stripT (i + 1, T)
  | stripT p = p;

fun stripC (i, f $ x) = stripC (i + 1, f)
  | stripC p = p;

val distinctN = "constr_distinct";

exception ConstrDistinct of term;

fun distinct_proc sg ss (t as Const ("op =", _) $ t1 $ t2) =
  (case (stripC (0, t1), stripC (0, t2)) of
     ((i, Const (cname1, T1)), (j, Const (cname2, T2))) =>
         (case (stripT (0, T1), stripT (0, T2)) of
            ((i', Type (tname1, _)), (j', Type (tname2, _))) =>
                if tname1 = tname2 andalso not (cname1 = cname2) andalso i = i' andalso j = j' then
                   (case (constrs_of sg tname1) of
                      SOME constrs => let val cnames = map (fst o dest_Const) constrs
                        in if cname1 mem cnames andalso cname2 mem cnames then
                             let val eq_t = Logic.mk_equals (t, Const ("False", HOLogic.boolT));
                                 val eq_ct = cterm_of sg eq_t;
                                 val Datatype_thy = theory "Datatype";
                                 val [In0_inject, In1_inject, In0_not_In1, In1_not_In0] =
                                   map (get_thm Datatype_thy o Name)
                                     ["In0_inject", "In1_inject", "In0_not_In1", "In1_not_In0"]
                             in (case (#distinct (datatype_info_err sg tname1)) of
                                 QuickAndDirty => SOME (Thm.invoke_oracle
                                   Datatype_thy distinctN (sg, ConstrDistinct eq_t))
                               | FewConstrs thms => SOME (Goal.prove sg [] [] eq_t (K
                                   (EVERY [rtac eq_reflection 1, rtac iffI 1, rtac notE 1,
                                    atac 2, resolve_tac thms 1, etac FalseE 1])))
                               | ManyConstrs (thm, simpset) => SOME (Goal.prove sg [] [] eq_t (K
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
  | distinct_proc sg _ _ = NONE;

val distinct_simproc =
  Simplifier.simproc HOL.thy distinctN ["s = t"] distinct_proc;

val dist_ss = HOL_ss addsimprocs [distinct_simproc];

val simproc_setup =
  Theory.add_oracle (distinctN, fn (_, ConstrDistinct t) => t) #>
  (fn thy => ((change_simpset_of thy) (fn ss => ss addsimprocs [distinct_simproc]); thy));


(**** translation rules for case ****)

fun find_first f = Library.find_first f;

fun case_tr context [t, u] =
    let
      val thy = Context.theory_of context;
      fun case_error s name ts = raise TERM ("Error in case expression" ^
        getOpt (Option.map (curry op ^ " for datatype ") name, "") ^ ":\n" ^ s, ts);
      fun dest_case1 (Const ("_case1", _) $ t $ u) = (case strip_comb t of
            (Const (s, _), ts) => (Sign.intern_const thy s, ts)
          | (Free (s, _), ts) => (Sign.intern_const thy s, ts)
          | _ => case_error "Head is not a constructor" NONE [t, u], u)
        | dest_case1 t = raise TERM ("dest_case1", [t]);
      fun dest_case2 (Const ("_case2", _) $ t $ u) = t :: dest_case2 u
        | dest_case2 t = [t];
      val cases as ((cname, _), _) :: _ = map dest_case1 (dest_case2 u);
      val tab = Symtab.dest (get_datatypes thy);
      val (cases', default) = (case split_last cases of
          (cases', (("dummy_pattern", []), t)) => (cases', SOME t)
        | _ => (cases, NONE))
      fun abstr (Free (x, T), body) = Term.absfree (x, T, body)
        | abstr (Const ("_constrain", _) $ Free (x, T) $ tT, body) =
            Syntax.const Syntax.constrainAbsC $ Term.absfree (x, T, body) $ tT
        | abstr (Const ("Pair", _) $ x $ y, body) =
            Syntax.const "split" $ abstr (x, abstr (y, body))
        | abstr (t, _) = case_error "Illegal pattern" NONE [t];
    in case find_first (fn (_, {descr, index, ...}) =>
      exists (equal cname o fst) (#3 (snd (List.nth (descr, index))))) tab of
        NONE => case_error ("Not a datatype constructor: " ^ cname) NONE [u]
      | SOME (tname, {descr, sorts, case_name, index, ...}) =>
        let
          val _ = if exists (equal "dummy_pattern" o fst o fst) cases' then
            case_error "Illegal occurrence of '_' dummy pattern" (SOME tname) [u] else ();
          val (_, (_, dts, constrs)) = List.nth (descr, index);
          fun find_case (cases, (s, dt)) =
            (case find_first (equal s o fst o fst) cases' of
               NONE => (case default of
                   NONE => case_error ("No clause for constructor " ^ s) (SOME tname) [u]
                 | SOME t => (cases, list_abs (map (rpair dummyT) (DatatypeProp.make_tnames
                     (map (typ_of_dtyp descr sorts) dt)), t)))
             | SOME (c as ((_, vs), t)) =>
                 if length dt <> length vs then
                    case_error ("Wrong number of arguments for constructor " ^ s)
                      (SOME tname) vs
                 else (cases \ c, foldr abstr t vs))
          val (cases'', fs) = foldl_map find_case (cases', constrs)
        in case (cases'', length constrs = length cases', default) of
            ([], true, SOME _) =>
              case_error "Extra '_' dummy pattern" (SOME tname) [u]
          | (_ :: _, _, _) =>
              let val extra = distinct (map (fst o fst) cases'')
              in case extra \\ map fst constrs of
                  [] => case_error ("More than one clause for constructor(s) " ^
                    commas extra) (SOME tname) [u]
                | extra' => case_error ("Illegal constructor(s): " ^ commas extra')
                    (SOME tname) [u]
              end
          | _ => list_comb (Syntax.const case_name, fs) $ t
        end
    end
  | case_tr _ ts = raise TERM ("case_tr", ts);

fun case_tr' constrs context ts =
  if length ts <> length constrs + 1 then raise Match else
  let
    val (fs, x) = split_last ts;
    fun strip_abs 0 t = ([], t)
      | strip_abs i (Abs p) =
        let val (x, u) = Syntax.atomic_abs_tr' p
        in apfst (cons x) (strip_abs (i-1) u) end
      | strip_abs i (Const ("split", _) $ t) = (case strip_abs (i+1) t of
          (v :: v' :: vs, u) => (Syntax.const "Pair" $ v $ v' :: vs, u));
    fun is_dependent i t =
      let val k = length (strip_abs_vars t) - i
      in k < 0 orelse exists (fn j => j >= k)
        (loose_bnos (strip_abs_body t))
      end;
    val cases = map (fn ((cname, dts), t) =>
      (Sign.extern_const (Context.theory_of context) cname,
       strip_abs (length dts) t, is_dependent (length dts) t))
      (constrs ~~ fs);
    fun count_cases (cs, (_, _, true)) = cs
      | count_cases (cs, (cname, (_, body), false)) = (case AList.lookup (op =) cs body of
          NONE => (body, [cname]) :: cs
        | SOME cnames => AList.update (op =) (body, cnames @ [cname]) cs);
    val cases' = sort (int_ord o Library.swap o pairself (length o snd))
      (Library.foldl count_cases ([], cases));
    fun mk_case1 (cname, (vs, body), _) = Syntax.const "_case1" $
      list_comb (Syntax.const cname, vs) $ body;
  in
    Syntax.const "_case_syntax" $ x $
      foldr1 (fn (t, u) => Syntax.const "_case2" $ t $ u) (map mk_case1
        (case cases' of
           [] => cases
         | (default, cnames) :: _ =>
           if length cnames = 1 then cases
           else if length cnames = length constrs then
             [hd cases, ("dummy_pattern", ([], default), false)]
           else
             filter_out (fn (cname, _, _) => cname mem cnames) cases @
             [("dummy_pattern", ([], default), false)]))
  end;

fun make_case_tr' case_names descr = List.concat (map
  (fn ((_, (_, _, constrs)), case_name) => map (rpair (case_tr' constrs))
    (NameSpace.accesses' case_name)) (descr ~~ case_names));

val trfun_setup =
  Theory.add_advanced_trfuns ([], [("_case_syntax", case_tr)], [], []);


(* prepare types *)

fun read_typ sign ((Ts, sorts), str) =
  let
    val T = Type.no_tvars (Sign.read_typ (sign, AList.lookup (op =)
      (map (apfst (rpair ~1)) sorts)) str) handle TYPE (msg, _, _) => error msg
  in (Ts @ [T], add_typ_tfrees (T, sorts)) end;

fun cert_typ sign ((Ts, sorts), raw_T) =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle
      TYPE (msg, _, _) => error msg;
    val sorts' = add_typ_tfrees (T, sorts)
  in (Ts @ [T],
      case gen_duplicates (op =) (map fst sorts') of
         [] => sorts'
       | dups => error ("Inconsistent sort constraints for " ^ commas dups))
  end;


(**** make datatype info ****)

fun make_dt_info descr sorts induct reccomb_names rec_thms
    (((((((((i, (_, (tname, _, _))), case_name), case_thms),
      exhaustion_thm), distinct_thm), inject), nchotomy), case_cong), weak_case_cong) =
  (tname,
   {index = i,
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

fun add_and_get_axioms_atts label tnames attss ts thy =
  foldr (fn (((tname, atts), t), (thy', axs)) =>
    let
      val ([ax], thy'') =
        thy'
        |> Theory.add_path tname
        |> PureThy.add_axioms_i [((label, t), atts)];
    in (Theory.parent_path thy'', ax::axs)
    end) (thy, []) (tnames ~~ attss ~~ ts) |> swap;

fun add_and_get_axioms label tnames =
  add_and_get_axioms_atts label tnames (replicate (length tnames) []);

fun add_and_get_axiomss label tnames tss thy =
  foldr (fn ((tname, ts), (thy', axss)) =>
    let
      val ([axs], thy'') =
        thy'
        |> Theory.add_path tname
        |> PureThy.add_axiomss_i [((label, ts), [])];
    in (Theory.parent_path thy'', axs::axss)
    end) (thy, []) (tnames ~~ tss) |> swap;

fun add_datatype_axm flat_names new_type_names descr sorts types_syntax constr_syntax dt_info
    case_names_induct case_names_exhausts thy =
  let
    val descr' = List.concat descr;
    val recTs = get_rec_types descr' sorts;
    val used = foldr add_typ_tfree_names [] recTs;
    val newTs = Library.take (length (hd descr), recTs);

    val no_size = exists (fn (_, (_, _, constrs)) => exists (fn (_, cargs) => exists
      (fn dt => is_rec_type dt andalso not (null (fst (strip_dtyp dt))))
        cargs) constrs) descr';

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

    val size_names = DatatypeProp.indexify_names
      (map (fn T => name_of_typ T ^ "_size") (Library.drop (length (hd descr), recTs)));

    val freeT = TFree (variant used "'t", HOLogic.typeS);
    val case_fn_Ts = map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let val Ts = map (typ_of_dtyp descr' sorts) cargs
        in Ts ---> freeT end) constrs) (hd descr);

    val case_names = map (fn s => (s ^ "_case")) new_type_names;

    val thy2' = thy |>

      (** new types **)

      curry (Library.foldr (fn (((name, mx), tvs), thy') => thy' |>
          TypedefPackage.add_typedecls [(name, tvs, mx)]))
        (types_syntax ~~ tyvars) |>
      add_path flat_names (space_implode "_" new_type_names) |>

      (** primrec combinators **)

      Theory.add_consts_i (map (fn ((name, T), T') =>
        (name, reccomb_fn_Ts @ [T] ---> T', NoSyn))
          (reccomb_names ~~ recTs ~~ rec_result_Ts)) |>

      (** case combinators **)

      Theory.add_consts_i (map (fn ((name, T), Ts) =>
        (name, Ts @ [T] ---> freeT, NoSyn))
          (case_names ~~ newTs ~~ case_fn_Ts));

    val reccomb_names' = map (Sign.intern_const thy2') reccomb_names;
    val case_names' = map (Sign.intern_const thy2') case_names;

    val thy2 = thy2' |>

      (** size functions **)

      (if no_size then I else Theory.add_consts_i (map (fn (s, T) =>
        (Sign.base_name s, T --> HOLogic.natT, NoSyn))
          (size_names ~~ Library.drop (length (hd descr), recTs)))) |>

      (** constructors **)

      parent_path flat_names |>
      curry (Library.foldr (fn (((((_, (_, _, constrs)), T), tname),
        constr_syntax'), thy') => thy' |>
          add_path flat_names tname |>
            Theory.add_consts_i (map (fn ((_, cargs), (cname, mx)) =>
              (cname, map (typ_of_dtyp descr' sorts) cargs ---> T, mx))
                (constrs ~~ constr_syntax')) |>
          parent_path flat_names))
            (hd descr ~~ newTs ~~ new_type_names ~~ constr_syntax);

    (**** introduction of axioms ****)

    val rec_axs = DatatypeProp.make_primrecs new_type_names descr sorts thy2;
    val size_axs = if no_size then [] else DatatypeProp.make_size descr sorts thy2;

    val ((([induct], [rec_thms]), inject), thy3) =
      thy2
      |> Theory.add_path (space_implode "_" new_type_names)
      |> PureThy.add_axioms_i [(("induct", DatatypeProp.make_ind descr sorts),
          [case_names_induct])]
      ||>> PureThy.add_axiomss_i [(("recs", rec_axs), [])]
      ||> (if no_size then I else snd o PureThy.add_axiomss_i [(("size", size_axs), [])])
      ||> Theory.parent_path
      ||>> add_and_get_axiomss "inject" new_type_names
            (DatatypeProp.make_injs descr sorts);
    val size_thms = if no_size then [] else get_thms thy3 (Name "size");
    val (distinct, thy4) = add_and_get_axiomss "distinct" new_type_names
      (DatatypeProp.make_distincts new_type_names descr sorts thy3) thy3;

    val exhaust_ts = DatatypeProp.make_casedists descr sorts;
    val (exhaustion, thy5) = add_and_get_axioms_atts "exhaust" new_type_names
      (map Library.single case_names_exhausts) exhaust_ts thy4;
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

    val dt_infos = map (make_dt_info descr' sorts induct reccomb_names' rec_thms)
      ((0 upto length (hd descr) - 1) ~~ (hd descr) ~~ case_names' ~~ case_thms ~~
        exhaustion ~~ replicate (length (hd descr)) QuickAndDirty ~~ inject ~~
          nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = List.concat (distinct @ inject @ case_thms) @ size_thms @ rec_thms;
    val split_thms = split ~~ split_asm;

    val thy12 =
      thy11
      |> Theory.add_advanced_trfuns ([], [], make_case_tr' case_names' (hd descr), [])
      |> Theory.add_path (space_implode "_" new_type_names)
      |> add_rules simps case_thms size_thms rec_thms inject distinct
          weak_case_congs Simplifier.cong_add
      |> put_datatypes (fold Symtab.update dt_infos dt_info)
      |> add_cases_induct dt_infos induct
      |> Theory.parent_path
      |> store_thmss "splits" new_type_names (map (fn (x, y) => [x, y]) split_thms) |> snd
      |> DatatypeRealizer.add_dt_realizers sorts (map snd dt_infos)
      |> fold (CodegenPackage.add_case_const_i get_case_const_data) case_names';
  in
    ({distinct = distinct,
      inject = inject,
      exhaustion = exhaustion,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induct,
      size = size_thms,
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
      flat_names new_type_names descr sorts dt_info inject dist_rewrites dist_ss induct thy3;
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
    val (size_thms, thy11) = DatatypeAbsProofs.prove_size_thms flat_names new_type_names
      descr sorts reccomb_names rec_thms thy10;

    val dt_infos = map (make_dt_info (List.concat descr) sorts induct reccomb_names rec_thms)
      ((0 upto length (hd descr) - 1) ~~ (hd descr) ~~ case_names ~~ case_thms ~~
        casedist_thms ~~ simproc_dists ~~ inject ~~ nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = List.concat (distinct @ inject @ case_thms) @ size_thms @ rec_thms;

    val thy12 =
      thy11
      |> Theory.add_advanced_trfuns ([], [], make_case_tr' case_names (hd descr), [])
      |> Theory.add_path (space_implode "_" new_type_names)
      |> add_rules simps case_thms size_thms rec_thms inject distinct
          weak_case_congs (Simplifier.attrib (op addcongs))
      |> put_datatypes (fold Symtab.update dt_infos dt_info)
      |> add_cases_induct dt_infos induct
      |> Theory.parent_path
      |> store_thmss "splits" new_type_names (map (fn (x, y) => [x, y]) split_thms) |> snd
      |> DatatypeRealizer.add_dt_realizers sorts (map snd dt_infos)
      |> fold (CodegenPackage.add_case_const_i get_case_const_data) case_names;
  in
    ({distinct = distinct,
      inject = inject,
      exhaustion = casedist_thms,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induct,
      size = size_thms,
      simps = simps}, thy12)
  end;


(*********************** declare existing type as datatype *********************)

fun gen_rep_datatype apply_theorems alt_names raw_distinct raw_inject raw_induction thy0 =
  let
    val _ = Theory.requires thy0 "Inductive" "datatype representations";

    val (((distinct, inject), [induction]), thy1) =
      thy0
      |> fold_map apply_theorems raw_distinct
      ||>> fold_map apply_theorems raw_inject
      ||>> apply_theorems [raw_induction];
    val sign = Theory.sign_of thy1;

    val induction' = freezeT induction;

    fun err t = error ("Ill-formed predicate in induction rule: " ^
      Sign.string_of_term sign t);

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

    val case_names_induct = mk_case_names_induct descr;
    val case_names_exhausts = mk_case_names_exhausts descr (map #1 dtnames);
    

    val _ = message ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val (casedist_thms, thy2) = thy1 |>
      DatatypeAbsProofs.prove_casedist_thms new_type_names [descr] sorts induction
        case_names_exhausts;
    val ((reccomb_names, rec_thms), thy3) = DatatypeAbsProofs.prove_primrec_thms
      false new_type_names [descr] sorts dt_info inject distinct dist_ss induction thy2;
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
    val (size_thms, thy9) =
      if Context.exists_name "NatArith" thy8 then
        DatatypeAbsProofs.prove_size_thms false new_type_names
          [descr] sorts reccomb_names rec_thms thy8
      else ([], thy8);

    val ((_, [induction']), thy10) =
      thy9
      |> store_thmss "inject" new_type_names inject
      ||>> store_thmss "distinct" new_type_names distinct
      ||> Theory.add_path (space_implode "_" new_type_names)
      ||>> PureThy.add_thms [(("induct", induction), [case_names_induct])];

    val dt_infos = map (make_dt_info descr sorts induction' reccomb_names rec_thms)
      ((0 upto length descr - 1) ~~ descr ~~ case_names ~~ case_thms ~~ casedist_thms ~~
        map FewConstrs distinct ~~ inject ~~ nchotomys ~~ case_congs ~~ weak_case_congs);

    val simps = List.concat (distinct @ inject @ case_thms) @ size_thms @ rec_thms;

    val thy11 = thy10 |>
      Theory.add_advanced_trfuns ([], [], make_case_tr' case_names descr, []) |>
      add_rules simps case_thms size_thms rec_thms inject distinct
        weak_case_congs (Simplifier.attrib (op addcongs)) |> 
      put_datatypes (fold Symtab.update dt_infos dt_info) |>
      add_cases_induct dt_infos induction' |>
      Theory.parent_path |>
      (snd o store_thmss "splits" new_type_names (map (fn (x, y) => [x, y]) split_thms)) |>
      DatatypeRealizer.add_dt_realizers sorts (map snd dt_infos);
  in
    ({distinct = distinct,
      inject = inject,
      exhaustion = casedist_thms,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induction',
      size = size_thms,
      simps = simps}, thy11)
  end;

val rep_datatype = gen_rep_datatype IsarThy.apply_theorems;
val rep_datatype_i = gen_rep_datatype IsarThy.apply_theorems_i;



(******************************** add datatype ********************************)

fun gen_add_datatype prep_typ err flat_names new_type_names dts thy =
  let
    val _ = Theory.requires thy "Datatype_Universe" "datatype definitions";

    (* this theory is used just for parsing *)

    val tmp_thy = thy |>
      Theory.copy |>
      Theory.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) dts);

    val sign = Theory.sign_of tmp_thy;

    val (tyvars, _, _, _)::_ = dts;
    val (new_dts, types_syntax) = ListPair.unzip (map (fn (tvs, tname, mx, _) =>
      let val full_tname = Sign.full_name sign (Syntax.type_name tname mx)
      in (case gen_duplicates (op =) tvs of
            [] => if eq_set (tyvars, tvs) then ((full_tname, tvs), (tname, mx))
                  else error ("Mutually recursive datatypes must have same type parameters")
          | dups => error ("Duplicate parameter(s) for datatype " ^ full_tname ^
              " : " ^ commas dups))
      end) dts);

    val _ = (case gen_duplicates (op =) (map fst new_dts) @ gen_duplicates (op =) new_type_names of
      [] => () | dups => error ("Duplicate datatypes: " ^ commas dups));

    fun prep_dt_spec ((dts', constr_syntax, sorts, i), (tvs, tname, mx, constrs)) =
      let
        fun prep_constr ((constrs, constr_syntax', sorts'), (cname, cargs, mx')) =
          let
            val (cargs', sorts'') = Library.foldl (prep_typ sign) (([], sorts'), cargs);
            val _ = (case foldr add_typ_tfree_names [] cargs' \\ tvs of
                [] => ()
              | vs => error ("Extra type variables on rhs: " ^ commas vs))
          in (constrs @ [((if flat_names then Sign.full_name sign else
                Sign.full_name_path sign tname) (Syntax.const_name cname mx'),
                   map (dtyp_of_typ new_dts) cargs')],
              constr_syntax' @ [(cname, mx')], sorts'')
          end handle ERROR msg =>
            cat_error msg ("The error above occured in constructor " ^ cname ^
              " of datatype " ^ tname);

        val (constrs', constr_syntax', sorts') =
          Library.foldl prep_constr (([], [], sorts), constrs)

      in
        case gen_duplicates (op =) (map fst constrs') of
           [] =>
             (dts' @ [(i, (Sign.full_name sign (Syntax.type_name tname mx),
                map DtTFree tvs, constrs'))],
              constr_syntax @ [constr_syntax'], sorts', i + 1)
         | dups => error ("Duplicate constructors " ^ commas dups ^
             " in datatype " ^ tname)
      end;

    val (dts', constr_syntax, sorts', i) = Library.foldl prep_dt_spec (([], [], [], 0), dts);
    val sorts = sorts' @ (map (rpair (Sign.defaultS sign)) (tyvars \\ map fst sorts'));
    val dt_info = get_datatypes thy;
    val (descr, _) = unfold_datatypes sign dts' sorts dt_info dts' i;
    val _ = check_nonempty descr handle (exn as Datatype_Empty s) =>
      if err then error ("Nonemptiness check failed for datatype " ^ s)
      else raise exn;

    val descr' = List.concat descr;
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
  DatatypesData.init #> Method.add_methods tactic_emulations #> simproc_setup #> trfun_setup;


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
  in snd o add_datatype false names specs end;

val datatypeP =
  OuterSyntax.command "datatype" "define inductive datatypes" K.thy_decl
    (P.and_list1 datatype_decl >> (Toplevel.theory o mk_datatype));


val rep_datatype_decl =
  Scan.option (Scan.repeat1 P.name) --
    Scan.optional (P.$$$ "distinct" |-- P.!!! (P.and_list1 P.xthms1)) [[]] --
    Scan.optional (P.$$$ "inject" |-- P.!!! (P.and_list1 P.xthms1)) [[]] --
    (P.$$$ "induction" |-- P.!!! P.xthm);

fun mk_rep_datatype (((opt_ts, dss), iss), ind) = #2 o rep_datatype opt_ts dss iss ind;

val rep_datatypeP =
  OuterSyntax.command "rep_datatype" "represent existing types inductively" K.thy_decl
    (rep_datatype_decl >> (Toplevel.theory o mk_rep_datatype));


val _ = OuterSyntax.add_keywords ["distinct", "inject", "induction"];
val _ = OuterSyntax.add_parsers [datatypeP, rep_datatypeP];

end;


end;

structure BasicDatatypePackage: BASIC_DATATYPE_PACKAGE = DatatypePackage;
open BasicDatatypePackage;

