(*  Title:      HOL/Tools/datatype_package.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1998  TU Muenchen

Datatype package for Isabelle/HOL.

TODO:
  - streamline internal interfaces (!??);
  - methods: induct, exhaust;
  - infix types (!?!?);
*)

signature BASIC_DATATYPE_PACKAGE =
sig
  val mutual_induct_tac : string list -> int -> tactic
  val induct_tac : string -> int -> tactic
  val exhaust_tac : string -> int -> tactic
end;

signature DATATYPE_PACKAGE =
sig
  include BASIC_DATATYPE_PACKAGE
  val quiet_mode : bool ref
  val add_datatype : bool -> string list -> (string list * bstring * mixfix *
    (bstring * string list * mixfix) list) list -> theory -> theory *
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
       simps : thm list}
  val add_datatype_i : bool -> string list -> (string list * bstring * mixfix *
    (bstring * typ list * mixfix) list) list -> theory -> theory *
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
       simps : thm list}
  val rep_datatype_i : string list option -> (thm * theory attribute list) list list ->
    (thm * theory attribute list) list list -> (thm * theory attribute list) -> theory -> theory *
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
       simps : thm list}
  val rep_datatype : string list option -> (xstring * Args.src list) list list ->
    (xstring * Args.src list) list list -> xstring * Args.src list -> theory -> theory *
      {distinct : thm list list,
       inject : thm list list,
       exhaustion : thm list,
       rec_thms : thm list,
       case_thms : thm list list,
       split_thms : (thm * thm) list,
       induction : thm,
       size : thm list,
       simps : thm list}
  val get_datatypes : theory -> DatatypeAux.datatype_info Symtab.table
  val datatype_info_sg : Sign.sg -> string -> DatatypeAux.datatype_info
  val datatype_info : theory -> string -> DatatypeAux.datatype_info
  val constrs_of : theory -> string -> term list option
  val case_const_of : theory -> string -> term option
  val setup: (theory -> theory) list
end;

structure DatatypePackage : DATATYPE_PACKAGE =
struct

open DatatypeAux;

val quiet_mode = quiet_mode;


(* data kind 'HOL/datatypes' *)

structure DatatypesArgs =
struct
  val name = "HOL/datatypes";
  type T = datatype_info Symtab.table;

  val empty = Symtab.empty;
  val prep_ext = I;
  val merge: T * T -> T = Symtab.merge (K true);

  fun print sg tab =
    Pretty.writeln (Pretty.strs ("datatypes:" ::
      map (Sign.cond_extern sg Sign.typeK o fst) (Symtab.dest tab)));
end;

structure DatatypesData = TheoryDataFun(DatatypesArgs);
val get_datatypes_sg = DatatypesData.get_sg;
val get_datatypes = DatatypesData.get;
val put_datatypes = DatatypesData.put;


(** theory information about datatypes **)

fun datatype_info_sg sg name =
  (case Symtab.lookup (get_datatypes_sg sg, name) of
    Some info => info
  | None => error ("Unknown datatype " ^ quote name));

val datatype_info = datatype_info_sg o Theory.sign_of;

fun constrs_of thy tname =
  let
    val {index, descr, ...} = datatype_info thy tname;
    val (_, _, constrs) = the (assoc (descr, index))
  in
    Some (map (fn (cname, _) =>
      Const (cname, the (Sign.const_type (Theory.sign_of thy) cname))) constrs)
  end handle _ => None;

fun case_const_of thy tname =
  let
    val {case_name, ...} = datatype_info thy tname;
  in
    Some (Const (case_name, the (Sign.const_type (Theory.sign_of thy) case_name)))
  end handle _ => None;

fun find_tname var Bi =
  let val frees = map dest_Free (term_frees Bi)
      val params = Logic.strip_params Bi;
  in case assoc (frees @ params, var) of
       None => error ("No such variable in subgoal: " ^ quote var)
     | Some(Type (tn, _)) => tn
     | _ => error ("Cannot determine type of " ^ quote var)
  end;

fun infer_tname state sign i aterm =
  let
    val (_, _, Bi, _) = dest_state (state, i)
    val params = Logic.strip_params Bi;   (*params of subgoal i*)
    val params = rev (rename_wrt_term Bi params);   (*as they are printed*)
    val (types, sorts) = types_sorts state;
    fun types' (a, ~1) = (case assoc (params, a) of None => types(a, ~1) | sm => sm)
      | types' ixn = types ixn;
    val (ct, _) = read_def_cterm (sign, types', sorts) [] false
                                  (aterm, TVar (("", 0), []));
  in case #T (rep_cterm ct) of
       Type (tn, _) => tn
     | _ => error ("Cannot determine type of " ^ quote aterm)
  end;

(*Warn if the (induction) variable occurs Free among the premises, which
  usually signals a mistake.  But calls the tactic either way!*)
fun occs_in_prems tacf vars = 
  SUBGOAL (fn (Bi, i) =>
	   (if  exists (fn Free (a, _) => a mem vars)
	              (foldr add_term_frees (#2 (strip_context Bi), []))
	     then warning "Induction variable occurs also among premises!"
	     else ();
	    tacf i));

(* generic induction tactic for datatypes *)

fun mutual_induct_tac vars i state =
  let
    val (_, _, Bi, _) = dest_state (state, i);
    val {sign, ...} = rep_thm state;
    val tn = find_tname (hd vars) Bi;
    val {induction, ...} = datatype_info_sg sign tn;
    val ind_vnames = map (fn (_ $ Var (ixn, _)) =>
      implode (tl (explode (Syntax.string_of_vname ixn))))
        (dest_conj (HOLogic.dest_Trueprop (concl_of induction)));
    val insts = (ind_vnames ~~ vars) handle _ =>
      error ("Induction rule for type " ^ tn ^ " has different number of variables")
  in
    occs_in_prems (res_inst_tac insts induction) vars i state
  end;

fun induct_tac var = mutual_induct_tac [var];

(* generic exhaustion tactic for datatypes *)

fun exhaust_tac aterm i state =
  let
    val {sign, ...} = rep_thm state;
    val tn = infer_tname state sign i aterm;
    val {exhaustion, ...} = datatype_info_sg sign tn;
    val _ $ Var (ixn, _) $ _ = HOLogic.dest_Trueprop
      (hd (Logic.strip_assums_hyp (hd (prems_of exhaustion))));
    val exh_vname = implode (tl (explode (Syntax.string_of_vname ixn)))
  in
    res_inst_tac [(exh_vname, aterm)] exhaustion i state
  end;


(* prepare types *)

fun read_typ sign ((Ts, sorts), str) =
  let
    val T = Type.no_tvars (Sign.read_typ (sign, (curry assoc)
      (map (apfst (rpair ~1)) sorts)) str) handle TYPE (msg, _, _) => error msg
  in (Ts @ [T], add_typ_tfrees (T, sorts)) end;

fun cert_typ sign ((Ts, sorts), raw_T) =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T) handle
      TYPE (msg, _, _) => error msg;
    val sorts' = add_typ_tfrees (T, sorts)
  in (Ts @ [T],
      case duplicates (map fst sorts') of
         [] => sorts'
       | dups => error ("Inconsistent sort constraints for " ^ commas dups))
  end;


(**** make datatype info ****)

fun make_dt_info descr induct reccomb_names rec_thms
  ((((((((i, (_, (tname, _, _))), case_name), case_thms),
    exhaustion_thm), distinct_thm), inject), nchotomy), case_cong) = (tname,
      {index = i,
       descr = descr,
       rec_names = reccomb_names,
       rec_rewrites = rec_thms,
       case_name = case_name,
       case_rewrites = case_thms,
       induction = induct,
       exhaustion = exhaustion_thm,
       distinct = distinct_thm,
       inject = inject,
       nchotomy = nchotomy,
       case_cong = case_cong});

fun store_clasimp thy (cla, simp) =
  (claset_ref_of thy := cla; simpset_ref_of thy := simp);

infix 4 addDistinct;

fun clasimp addDistinct ([], _) = clasimp
  | clasimp addDistinct (thms::thmss, (_, (_, _, constrs))::descr) =
      if length constrs < DatatypeProp.dtK then
        clasimp addIffs thms addDistinct (thmss, descr)
      else
        clasimp addsimps2 thms addDistinct (thmss, descr);


(********************* axiomatic introduction of datatypes ********************)

fun add_and_get_axioms label tnames ts thy =
  foldr (fn ((tname, t), (thy', axs)) =>
    let
      val thy'' = thy' |>
        Theory.add_path tname |>
        PureThy.add_axioms_i [((label, t), [])];
      val ax = get_axiom thy'' label
    in (Theory.parent_path thy'', ax::axs)
    end) (tnames ~~ ts, (thy, []));

fun add_and_get_axiomss label tnames tss thy =
  foldr (fn ((tname, ts), (thy', axss)) =>
    let
      val thy'' = thy' |>
        Theory.add_path tname |>
        PureThy.add_axiomss_i [((label, ts), [])];
      val axs = PureThy.get_thms thy'' label
    in (Theory.parent_path thy'', axs::axss)
    end) (tnames ~~ tss, (thy, []));

fun add_datatype_axm flat_names new_type_names descr sorts types_syntax constr_syntax dt_info thy =
  let
    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used = foldr add_typ_tfree_names (recTs, []);
    val newTs = take (length (hd descr), recTs);

    val _ = message ("Adding axioms for datatype(s) " ^ commas_quote new_type_names);

    (**** declare new types and constants ****)

    val tyvars = map (fn (_, (_, Ts, _)) => map dest_DtTFree Ts) (hd descr);

    val constr_decls = map (fn (((_, (_, _, constrs)), T), constr_syntax') =>
      map (fn ((_, cargs), (cname, mx)) =>
        (cname, map (typ_of_dtyp descr' sorts) cargs ---> T, mx))
          (constrs ~~ constr_syntax')) ((hd descr) ~~ newTs ~~ constr_syntax);

    val rec_result_Ts = map TFree (variantlist (replicate (length descr') "'t", used) ~~
      replicate (length descr') HOLogic.termS);

    val reccomb_fn_Ts = flat (map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let
          val recs = filter is_rec_type cargs;
          val argTs = (map (typ_of_dtyp descr' sorts) cargs) @
            (map (fn r => nth_elem (dest_DtRec r, rec_result_Ts)) recs)
        in argTs ---> nth_elem (i, rec_result_Ts)
        end) constrs) descr');

    val big_reccomb_name = (space_implode "_" new_type_names) ^ "_rec";
    val reccomb_names = if length descr' = 1 then [big_reccomb_name] else
      (map ((curry (op ^) (big_reccomb_name ^ "_")) o string_of_int)
        (1 upto (length descr')));

    val big_size_name = space_implode "_" new_type_names ^ "_size";
    val size_names = if length (flat (tl descr)) = 1 then [big_size_name] else
      map (fn i => big_size_name ^ "_" ^ string_of_int i)
        (1 upto length (flat (tl descr)));

    val freeT = TFree (variant used "'t", HOLogic.termS);
    val case_fn_Ts = map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let val Ts = map (typ_of_dtyp descr' sorts) cargs
        in Ts ---> freeT end) constrs) (hd descr);

    val case_names = map (fn s => (s ^ "_case")) new_type_names;

    val thy2' = thy |>

      (** new types **)

      curry (foldr (fn (((name, mx), tvs), thy') => thy' |>
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
          (case_names ~~ newTs ~~ case_fn_Ts)) |>
      Theory.add_trrules_i (DatatypeProp.make_case_trrules new_type_names descr);

    val reccomb_names' = map (Sign.intern_const (Theory.sign_of thy2')) reccomb_names;
    val case_names' = map (Sign.intern_const (Theory.sign_of thy2')) case_names;

    val thy2 = thy2' |>

      (** t_ord functions **)

      Theory.add_consts_i
        (foldr (fn ((((_, (_, _, constrs)), tname), T), decls) =>
          if length constrs < DatatypeProp.dtK then decls
          else (tname ^ "_ord", T --> HOLogic.natT, NoSyn)::decls)
            ((hd descr) ~~ new_type_names ~~ newTs, [])) |>

      (** size functions **)

      Theory.add_consts_i (map (fn (s, T) =>
        (Sign.base_name s, T --> HOLogic.natT, NoSyn))
          (size_names ~~ drop (length (hd descr), recTs))) |>

      (** constructors **)

      parent_path flat_names |>
      curry (foldr (fn (((((_, (_, _, constrs)), T), tname),
        constr_syntax'), thy') => thy' |>
          add_path flat_names tname |>
            Theory.add_consts_i (map (fn ((_, cargs), (cname, mx)) =>
              (cname, map (typ_of_dtyp descr' sorts) cargs ---> T, mx))
                (constrs ~~ constr_syntax')) |>
          parent_path flat_names))
            (hd descr ~~ newTs ~~ new_type_names ~~ constr_syntax);

    (**** introduction of axioms ****)

    val rec_axs = DatatypeProp.make_primrecs new_type_names descr sorts thy2;
    val size_axs = DatatypeProp.make_size new_type_names descr sorts thy2;

    val (thy3, inject) = thy2 |>
      Theory.add_path (space_implode "_" new_type_names) |>
      PureThy.add_axioms_i [(("induct", DatatypeProp.make_ind descr sorts), [])] |>
      PureThy.add_axiomss_i [(("recs", rec_axs), [])] |>
      PureThy.add_axiomss_i [(("size", size_axs), [])] |>
      Theory.parent_path |>
      add_and_get_axiomss "inject" new_type_names
        (DatatypeProp.make_injs descr sorts);
    val induct = get_axiom thy3 "induct";
    val rec_thms = get_thms thy3 "recs";
    val size_thms = get_thms thy3 "size";
    val (thy4, distinct) = add_and_get_axiomss "distinct" new_type_names
      (DatatypeProp.make_distincts new_type_names descr sorts thy3) thy3;
    val (thy5, exhaustion) = add_and_get_axioms "exhaust" new_type_names
      (DatatypeProp.make_casedists descr sorts) thy4;
    val (thy6, case_thms) = add_and_get_axiomss "cases" new_type_names
      (DatatypeProp.make_cases new_type_names descr sorts thy5) thy5;
    val (split_ts, split_asm_ts) = ListPair.unzip
      (DatatypeProp.make_splits new_type_names descr sorts thy6);
    val (thy7, split) = add_and_get_axioms "split" new_type_names split_ts thy6;
    val (thy8, split_asm) = add_and_get_axioms "split_asm" new_type_names
      split_asm_ts thy7;
    val (thy9, nchotomys) = add_and_get_axioms "nchotomy" new_type_names
      (DatatypeProp.make_nchotomys descr sorts) thy8;
    val (thy10, case_congs) = add_and_get_axioms "case_cong" new_type_names
      (DatatypeProp.make_case_congs new_type_names descr sorts thy9) thy9;
    
    val dt_infos = map (make_dt_info descr' induct reccomb_names' rec_thms)
      ((0 upto length (hd descr) - 1) ~~ (hd descr) ~~ case_names' ~~ case_thms ~~
        exhaustion ~~ distinct ~~ inject ~~ nchotomys ~~ case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ size_thms @ rec_thms;

    val thy11 = thy10 |>
      Theory.add_path (space_implode "_" new_type_names) |>
      PureThy.add_thmss [(("simps", simps), [])] |>
      put_datatypes (foldr Symtab.update (dt_infos, dt_info)) |>
      Theory.parent_path;

    val _ = store_clasimp thy11 ((claset_of thy11, simpset_of thy11)
      addsimps2 flat case_thms addsimps2 size_thms addsimps2 rec_thms
      addIffs flat inject addDistinct (distinct, hd descr));

  in
    (thy11,
     {distinct = distinct,
      inject = inject,
      exhaustion = exhaustion,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split ~~ split_asm,
      induction = induct,
      size = size_thms,
      simps = simps})
  end;


(******************* definitional introduction of datatypes *******************)

fun add_datatype_def flat_names new_type_names descr sorts types_syntax constr_syntax dt_info thy =
  let
    val _ = message ("Proofs for datatype(s) " ^ commas_quote new_type_names);

    val (thy2, inject, dist_rewrites, induct) = thy |>
      DatatypeRepProofs.representation_proofs flat_names dt_info new_type_names descr sorts
        types_syntax constr_syntax;

    val (thy3, casedist_thms) =
      DatatypeAbsProofs.prove_casedist_thms new_type_names descr sorts induct thy2;
    val (thy4, reccomb_names, rec_thms) = DatatypeAbsProofs.prove_primrec_thms
      flat_names new_type_names descr sorts dt_info inject dist_rewrites induct thy3;
    val (thy5, case_names, case_thms) = DatatypeAbsProofs.prove_case_thms
      flat_names new_type_names descr sorts reccomb_names rec_thms thy4;
    val (thy6, distinct) = DatatypeAbsProofs.prove_distinctness_thms
      flat_names new_type_names descr sorts dist_rewrites case_thms thy5;
    val (thy7, split_thms) = DatatypeAbsProofs.prove_split_thms new_type_names
      descr sorts inject dist_rewrites casedist_thms case_thms thy6;
    val (thy8, nchotomys) = DatatypeAbsProofs.prove_nchotomys new_type_names
      descr sorts casedist_thms thy7;
    val (thy9, case_congs) = DatatypeAbsProofs.prove_case_congs new_type_names
      descr sorts nchotomys case_thms thy8;
    val (thy10, size_thms) = DatatypeAbsProofs.prove_size_thms flat_names new_type_names
      descr sorts reccomb_names rec_thms thy9;

    val dt_infos = map (make_dt_info (flat descr) induct reccomb_names rec_thms)
      ((0 upto length (hd descr) - 1) ~~ (hd descr) ~~ case_names ~~ case_thms ~~
        casedist_thms ~~ distinct ~~ inject ~~ nchotomys ~~ case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ size_thms @ rec_thms;

    val thy11 = thy10 |>
      Theory.add_path (space_implode "_" new_type_names) |>
      PureThy.add_thmss [(("simps", simps), [])] |>
      put_datatypes (foldr Symtab.update (dt_infos, dt_info)) |>
      Theory.parent_path;

    val _ = store_clasimp thy11 ((claset_of thy11, simpset_of thy11)
      addsimps2 flat case_thms addsimps2 size_thms addsimps2 rec_thms
      addIffs flat inject addDistinct (distinct, hd descr));

  in
    (thy11,
     {distinct = distinct,
      inject = inject,
      exhaustion = casedist_thms,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induct,
      size = size_thms,
      simps = simps})
  end;


(*********************** declare existing type as datatype *********************)

fun gen_rep_datatype apply_theorems alt_names raw_distinct raw_inject raw_induction thy0 =
  let
    fun app_thmss srcs thy = foldl_map (fn (thy, x) => apply_theorems x thy) (thy, srcs);
    fun app_thm src thy = apsnd Library.hd (apply_theorems [src] thy);

    val (((thy1, induction), inject), distinct) = thy0
      |> app_thmss raw_distinct
      |> apfst (app_thmss raw_inject)
      |> apfst (apfst (app_thm raw_induction));
    val sign = Theory.sign_of thy1;

    val induction' = freezeT induction;

    fun err t = error ("Ill-formed predicate in induction rule: " ^
      Sign.string_of_term sign t);

    fun get_typ (t as _ $ Var (_, Type (tname, Ts))) =
          ((tname, map dest_TFree Ts) handle _ => err t)
      | get_typ t = err t;

    val dtnames = map get_typ (dest_conj (HOLogic.dest_Trueprop (concl_of induction')));
    val new_type_names = if_none alt_names (map fst dtnames);

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

    val _ = writeln ("Proofs for datatype(s) " ^ commas new_type_names);

    val (thy2, casedist_thms) = thy1 |>
      DatatypeAbsProofs.prove_casedist_thms new_type_names [descr] sorts induction;
    val (thy3, reccomb_names, rec_thms) = DatatypeAbsProofs.prove_primrec_thms
      false new_type_names [descr] sorts dt_info inject distinct induction thy2;
    val (thy4, case_names, case_thms) = DatatypeAbsProofs.prove_case_thms false
      new_type_names [descr] sorts reccomb_names rec_thms thy3;
    val (thy5, split_thms) = DatatypeAbsProofs.prove_split_thms
      new_type_names [descr] sorts inject distinct casedist_thms case_thms thy4;
    val (thy6, nchotomys) = DatatypeAbsProofs.prove_nchotomys new_type_names
      [descr] sorts casedist_thms thy5;
    val (thy7, case_congs) = DatatypeAbsProofs.prove_case_congs new_type_names
      [descr] sorts nchotomys case_thms thy6;
    val (thy8, size_thms) =
      if exists (equal "Arith") (Sign.stamp_names_of (Theory.sign_of thy7)) then
        DatatypeAbsProofs.prove_size_thms false new_type_names
          [descr] sorts reccomb_names rec_thms thy7
      else (thy7, []);

    val dt_infos = map (make_dt_info descr induction reccomb_names rec_thms)
      ((0 upto length descr - 1) ~~ descr ~~ case_names ~~ case_thms ~~
        casedist_thms ~~ distinct ~~ inject ~~ nchotomys ~~ case_congs);

    val simps = flat (distinct @ inject @ case_thms) @ size_thms @ rec_thms;

    val thy9 = thy8 |>
      Theory.add_path (space_implode "_" new_type_names) |>
      PureThy.add_thmss [(("simps", simps), [])] |>
      put_datatypes (foldr Symtab.update (dt_infos, dt_info)) |>
      Theory.parent_path;

    val _ = store_clasimp thy9 ((claset_of thy9, simpset_of thy9)
      addsimps2 flat case_thms addsimps2 size_thms addsimps2 rec_thms
      addIffs flat inject addDistinct (distinct, descr));

  in
    (thy9,
     {distinct = distinct,
      inject = inject,
      exhaustion = casedist_thms,
      rec_thms = rec_thms,
      case_thms = case_thms,
      split_thms = split_thms,
      induction = induction,
      size = size_thms,
      simps = simps})
  end;

val rep_datatype = gen_rep_datatype IsarThy.apply_theorems;
val rep_datatype_i = gen_rep_datatype IsarThy.apply_theorems_i;


(******************************** add datatype ********************************)

fun gen_add_datatype prep_typ flat_names new_type_names dts thy =
  let
    val _ = Theory.requires thy "Datatype" "datatype definitions";

    (* this theory is used just for parsing *)

    val tmp_thy = thy |>
      Theory.copy |>
      Theory.add_types (map (fn (tvs, tname, mx, _) =>
        (tname, length tvs, mx)) dts);

    val sign = Theory.sign_of tmp_thy;

    val (tyvars, _, _, _)::_ = dts;
    val (new_dts, types_syntax) = ListPair.unzip (map (fn (tvs, tname, mx, _) =>
      let val full_tname = Sign.full_name sign (Syntax.type_name tname mx)
      in (case duplicates tvs of
            [] => if eq_set (tyvars, tvs) then ((full_tname, tvs), (tname, mx))
                  else error ("Mutually recursive datatypes must have same type parameters")
          | dups => error ("Duplicate parameter(s) for datatype " ^ full_tname ^
              " : " ^ commas dups))
      end) dts);

    val _ = (case duplicates (map fst new_dts) @ duplicates new_type_names of
      [] => () | dups => error ("Duplicate datatypes: " ^ commas dups));

    fun prep_dt_spec ((dts', constr_syntax, sorts, i), (tvs, tname, mx, constrs)) =
      let
        fun prep_constr ((constrs, constr_syntax', sorts'), (cname, cargs, mx')) =
          let
            val (cargs', sorts'') = foldl (prep_typ sign) (([], sorts'), cargs);
            val _ = (case foldr add_typ_tfree_names (cargs', []) \\ tvs of
                [] => ()
              | vs => error ("Extra type variables on rhs: " ^ commas vs))
          in (constrs @ [((if flat_names then Sign.full_name sign else
                Sign.full_name_path sign tname) (Syntax.const_name cname mx'),
                   map (dtyp_of_typ new_dts) cargs')],
              constr_syntax' @ [(cname, mx')], sorts'')
          end handle ERROR =>
            error ("The error above occured in constructor " ^ cname ^
              " of datatype " ^ tname);

        val (constrs', constr_syntax', sorts') =
          foldl prep_constr (([], [], sorts), constrs)

      in 
        case duplicates (map fst constrs') of
           [] =>
             (dts' @ [(i, (Sign.full_name sign (Syntax.type_name tname mx),
                map DtTFree tvs, constrs'))],
              constr_syntax @ [constr_syntax'], sorts', i + 1)
         | dups => error ("Duplicate constructors " ^ commas dups ^
             " in datatype " ^ tname)
      end;

    val (dts', constr_syntax, sorts', i) = foldl prep_dt_spec (([], [], [], 0), dts);
    val dt_info = get_datatypes thy;
    val (descr, _) = unfold_datatypes dt_info dts' i;
    val _ = check_nonempty descr;
    val sorts = sorts' @ (map (rpair (Sign.defaultS sign)) (tyvars \\ map fst sorts'));

  in
    (if (!quick_and_dirty) then add_datatype_axm else add_datatype_def)
      flat_names new_type_names descr sorts types_syntax constr_syntax dt_info thy
  end;

val add_datatype_i = gen_add_datatype cert_typ;
val add_datatype = gen_add_datatype read_typ;


(** package setup **)

(* setup theory *)

val setup = [DatatypesData.init];


(* outer syntax *)

local open OuterParse in

val datatype_decl =
  Scan.option ($$$ "(" |-- name --| $$$ ")") -- type_args -- name -- opt_infix --
    ($$$ "=" |-- enum1 "|" (name -- Scan.repeat typ -- opt_mixfix));

fun mk_datatype args =
  let
    val names = map (fn ((((None, _), t), _), _) => t | ((((Some t, _), _), _), _) => t) args;
    val specs = map (fn ((((_, vs), t), mx), cons) => (vs, t, mx, map (fn ((x, y), z) => (x, y, z)) cons)) args;
  in #1 o add_datatype false names specs end;

val datatypeP =
  OuterSyntax.command "datatype" "define inductive datatypes"
    (enum1 "and" datatype_decl >> (Toplevel.theory o mk_datatype));


val rep_datatype_decl =
  Scan.option (Scan.repeat1 name) --
    Scan.optional ($$$ "distinct" |-- !!! (and_list1 xthms1)) [] --
    Scan.optional ($$$ "inject" |-- !!! (and_list1 xthms1)) [] --
    ($$$ "induct" |-- !!! xthm);

fun mk_rep_datatype (((opt_ts, dss), iss), ind) = #1 o rep_datatype opt_ts dss iss ind;

val rep_datatypeP =
  OuterSyntax.command "rep_datatype" "represent existing types inductively"
    (rep_datatype_decl >> (Toplevel.theory o mk_rep_datatype));


val _ = OuterSyntax.add_keywords ["distinct", "inject", "induct"];
val _ = OuterSyntax.add_parsers [datatypeP, rep_datatypeP];

end;


end;

structure BasicDatatypePackage: BASIC_DATATYPE_PACKAGE = DatatypePackage;
open BasicDatatypePackage;
