(*  Title:      HOL/Tools/BNF/bnf_lfp_compat.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013, 2014

Compatibility layer with the old datatype package. Parly based on:

    Title:      HOL/Tools/Old_Datatype/old_datatype_data.ML
    Author:     Stefan Berghofer, TU Muenchen
*)

signature BNF_LFP_COMPAT =
sig
  val get_all: theory -> bool -> Old_Datatype_Aux.info Symtab.table
  val get_info: theory -> bool -> string -> Old_Datatype_Aux.info option
  val the_info: theory -> bool -> string -> Old_Datatype_Aux.info
  val the_spec: theory -> bool -> string -> (string * sort) list * (string * typ list) list
  val the_descr: theory -> bool -> string list ->
    Old_Datatype_Aux.descr * (string * sort) list * string list * string
    * (string list * string list) * (typ list * typ list)
  val get_constrs: theory -> bool -> string -> (string * typ) list option
  val interpretation: bool -> (Old_Datatype_Aux.config -> string list -> theory -> theory) ->
    theory -> theory
  val add_datatype: Old_Datatype_Aux.config -> Old_Datatype_Aux.spec list -> theory ->
    string list * theory
  val datatype_compat_cmd: string list -> local_theory -> local_theory
end;

structure BNF_LFP_Compat : BNF_LFP_COMPAT =
struct

open Ctr_Sugar
open BNF_Util
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar

val compatN = "compat_";

fun reindex_desc desc =
  let
    val kks = map fst desc;
    val perm_kks = sort int_ord kks;

    fun perm_dtyp (Old_Datatype_Aux.DtType (s, Ds)) = Old_Datatype_Aux.DtType (s, map perm_dtyp Ds)
      | perm_dtyp (Old_Datatype_Aux.DtRec kk) =
        Old_Datatype_Aux.DtRec (find_index (curry (op =) kk) kks)
      | perm_dtyp D = D;
  in
    if perm_kks = kks then
      desc
    else
      perm_kks ~~
      map (fn (_, (s, Ds, sDss)) => (s, map perm_dtyp Ds, map (apsnd (map perm_dtyp)) sDss)) desc
  end;

fun mk_infos_of_mutually_recursive_new_datatypes unfold_nesting need_co_inducts_recs check_names
    raw_fpT_names0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    fun not_datatype s = error (quote s ^ " is not a new-style datatype");
    fun not_mutually_recursive ss =
      error ("{" ^ commas ss ^ "} is not a complete set of mutually recursive new-style datatypes");

    val fpT_names0 =
      map (fst o dest_Type o Proof_Context.read_type_name {proper = true, strict = false} lthy)
        raw_fpT_names0;

    fun lfp_sugar_of s =
      (case fp_sugar_of lthy s of
        SOME (fp_sugar as {fp = Least_FP, ...}) => fp_sugar
      | _ => not_datatype s);

    val fpTs0 as Type (_, var_As) :: _ = #Ts (#fp_res (lfp_sugar_of (hd fpT_names0)));
    val fpT_names = map (fst o dest_Type) fpTs0;

    val _ = check_names (op =) (fpT_names0, fpT_names) orelse not_mutually_recursive fpT_names0;

    val (As_names, _) = Variable.variant_fixes (map (fn TVar ((s, _), _) => s) var_As) lthy;
    val As = map2 (fn s => fn TVar (_, S) => TFree (s, S)) As_names var_As;
    val fpTs = map (fn s => Type (s, As)) fpT_names;

    val nn_fp = length fpTs;

    val mk_dtyp = Old_Datatype_Aux.dtyp_of_typ (map (apsnd (map Term.dest_TFree) o dest_Type) fpTs);

    fun mk_ctr_descr Ts = mk_ctr Ts #> dest_Const ##> (binder_types #> map mk_dtyp);
    fun mk_typ_descr index (Type (T_name, Ts)) ({ctrs, ...} : ctr_sugar) =
      (index, (T_name, map mk_dtyp Ts, map (mk_ctr_descr Ts) ctrs));

    val fp_ctr_sugars = map (#ctr_sugar o lfp_sugar_of) fpT_names;
    val orig_descr = map3 mk_typ_descr (0 upto nn_fp - 1) fpTs fp_ctr_sugars;
    val all_infos = Old_Datatype_Data.get_all thy;
    val (orig_descr' :: nested_descrs) =
      if unfold_nesting then
        fst (Old_Datatype_Aux.unfold_datatypes lthy orig_descr all_infos orig_descr nn_fp)
      else
        [orig_descr];

    fun cliquify_descr [] = []
      | cliquify_descr [entry] = [[entry]]
      | cliquify_descr (full_descr as (_, (T_name1, _, _)) :: _) =
        let
          val nn =
            if member (op =) fpT_names T_name1 then
              nn_fp
            else
              (case Symtab.lookup all_infos T_name1 of
                SOME {descr, ...} =>
                length (filter_out (exists Old_Datatype_Aux.is_rec_type o #2 o snd) descr)
              | NONE => raise Fail "unknown old-style datatype");
        in
          chop nn full_descr ||> cliquify_descr |> op ::
        end;

    (* put nested types before the types that nest them, as needed for N2M *)
    val descrs = burrow reindex_desc (orig_descr' :: rev nested_descrs);
    val (cliques, descr) =
      split_list (flat (map_index (fn (i, descr) => map (pair i) descr)
        (maps cliquify_descr descrs)));

    val dest_dtyp = Old_Datatype_Aux.typ_of_dtyp descr;

    val Ts = Old_Datatype_Aux.get_rec_types descr;
    val nn = length Ts;

    val fp_sugars0 = map (lfp_sugar_of o fst o dest_Type) Ts;
    val ctr_Tsss = map (map (map dest_dtyp o snd) o #3 o snd) descr;
    val kkssss =
      map (map (map (fn Old_Datatype_Aux.DtRec kk => [kk] | _ => []) o snd) o #3 o snd) descr;

    val callers = map (fn kk => Var ((Name.uu, kk), @{typ "unit => unit"})) (0 upto nn - 1);

    fun apply_comps n kk =
      mk_partial_compN n (replicate n HOLogic.unitT ---> HOLogic.unitT) (nth callers kk);

    val callssss =
      map2 (map2 (map2 (fn ctr_T => map (apply_comps (num_binder_types ctr_T))))) ctr_Tsss kkssss;

    val b_names = Name.variant_list [] (map base_name_of_typ Ts);
    val compat_b_names = map (prefix compatN) b_names;
    val compat_bs = map Binding.name compat_b_names;

    val ((fp_sugars, (lfp_sugar_thms, _)), lthy') =
      if nn > nn_fp then
        mutualize_fp_sugars Least_FP need_co_inducts_recs cliques compat_bs Ts callers callssss
          fp_sugars0 lthy
      else
        ((fp_sugars0, (NONE, NONE)), lthy);

    val recs = map (fst o dest_Const o #co_rec) fp_sugars;
    val rec_thms = maps #co_rec_thms fp_sugars;

    val {common_co_inducts = [induct], ...} :: _ = fp_sugars;
    val inducts = map (the_single o #co_inducts) fp_sugars;

    fun mk_info (kk, {T = Type (T_name0, _), ctr_sugar = {casex, exhaust, nchotomy, injects,
        distincts, case_thms, case_cong, case_cong_weak, split, split_asm, ...}, ...} : fp_sugar) =
      (T_name0,
       {index = kk, descr = descr, inject = injects, distinct = distincts, induct = induct,
        inducts = inducts, exhaust = exhaust, nchotomy = nchotomy, rec_names = recs,
        rec_rewrites = rec_thms, case_name = fst (dest_Const casex), case_rewrites = case_thms,
        case_cong = case_cong, case_cong_weak = case_cong_weak, split = split,
        split_asm = split_asm});

    val infos = map_index mk_info (take nn_fp fp_sugars);
  in
    (nn, b_names, compat_b_names, lfp_sugar_thms, infos, lthy')
  end;

fun infos_of_new_datatype_mutual_cluster lthy unfold_nesting raw_fpt_names01 =
  mk_infos_of_mutually_recursive_new_datatypes unfold_nesting false subset [raw_fpt_names01] lthy
  |> #5;

fun get_all thy unfold_nesting =
  let
    val lthy = Named_Target.theory_init thy;
    val old_info_tab = Old_Datatype_Data.get_all thy;
    val new_T_names = BNF_FP_Def_Sugar.fp_sugars_of_global thy
      |> map_filter (try (fn {T = Type (s, _), fp_res_index = 0, ...} => s));
    val new_infos = maps (infos_of_new_datatype_mutual_cluster lthy unfold_nesting) new_T_names;
  in
    fold (if unfold_nesting then Symtab.default else Symtab.update) new_infos old_info_tab
  end;

fun get_one get_old get_new thy unfold_nesting x =
  let val (get_fst, get_snd) = (get_new thy unfold_nesting, get_old thy) |> unfold_nesting ? swap in
    (case get_fst x of NONE => get_snd x | res => res)
  end;

fun get_info_of_new_datatype thy unfold_nesting T_name =
  let val lthy = Named_Target.theory_init thy in
    AList.lookup (op =) (infos_of_new_datatype_mutual_cluster lthy unfold_nesting T_name) T_name
  end;

val get_info = get_one Old_Datatype_Data.get_info get_info_of_new_datatype;

fun the_info thy unfold_nesting T_name =
  (case get_info thy unfold_nesting T_name of
    SOME info => info
  | NONE => error ("Unknown datatype " ^ quote T_name));

fun the_spec thy unfold_nesting T_name =
  let
    val {descr, index, ...} = the_info thy unfold_nesting T_name;
    val (_, Ds, ctrs0) = the (AList.lookup (op =) descr index);
    val Ts = map Old_Datatype_Aux.dest_DtTFree Ds;
    val ctrs = map (apsnd (map (Old_Datatype_Aux.typ_of_dtyp descr))) ctrs0;
  in (Ts, ctrs) end;

fun the_descr thy unfold_nesting (T_names0 as T_name01 :: _) =
  let
    fun not_mutually_recursive ss =
      error ("{" ^ commas ss ^ "} is not a complete set of mutually recursive datatypes");

    val info = the_info thy unfold_nesting T_name01;
    val descr = #descr info;

    val (_, Ds, _) = the (AList.lookup (op =) descr (#index info));
    val vs = map Old_Datatype_Aux.dest_DtTFree Ds;

    fun is_DtTFree (Old_Datatype_Aux.DtTFree _) = true
      | is_DtTFree _ = false;

    val k = find_index (fn (_, (_, dTs, _)) => not (forall is_DtTFree dTs)) descr;
    val protoTs as (dataTs, _) = chop k descr
      |> (pairself o map)
        (fn (_, (T_name, Ds, _)) => (T_name, map (Old_Datatype_Aux.typ_of_dtyp descr) Ds));

    val T_names = map fst dataTs;
    val _ = eq_set (op =) (T_names, T_names0) orelse not_mutually_recursive T_names0

    val (Ts, Us) = (pairself o map) Type protoTs;

    val names = map Long_Name.base_name T_names;
    val (auxnames, _) = Name.make_context names
      |> fold_map (Name.variant o Old_Datatype_Aux.name_of_typ) Us;
    val prefix = space_implode "_" names;
  in
    (descr, vs, T_names, prefix, (names, auxnames), (Ts, Us))
  end;

fun get_constrs thy unfold_nesting T_name =
  try (the_spec thy unfold_nesting) T_name
  |> Option.map (fn (tfrees, ctrs) =>
    let
      fun varify_tfree (s, S) = TVar ((s, 0), S);
      fun varify_typ (TFree x) = varify_tfree x
        | varify_typ T = T;

      val dataT = Type (T_name, map varify_tfree tfrees);

      fun mk_ctr_typ Ts = map (Term.map_atyps varify_typ) Ts ---> dataT;
    in
      map (apsnd mk_ctr_typ) ctrs
    end);

fun old_interpretation_of unfold_nesting f config T_names thy =
  if not unfold_nesting orelse exists (is_none o fp_sugar_of_global thy) T_names then
    f config T_names thy
  else
    thy;

fun new_interpretation_of unfold_nesting f fp_sugars thy =
  let val T_names = map (fst o dest_Type o #T) fp_sugars in
    if unfold_nesting orelse exists (is_none o Old_Datatype_Data.get_info thy) T_names then
      f {strict = true, quiet = true} T_names thy
    else
      thy
  end;

fun interpretation unfold_nesting f =
  Old_Datatype_Data.interpretation (old_interpretation_of unfold_nesting f)
  #> fp_sugar_interpretation (new_interpretation_of unfold_nesting f);

fun add_datatype config specs thy = ([], thy);

val code_nitpicksimp_simp_attrs = Code.add_default_eqn_attrib :: @{attributes [nitpick_simp, simp]};

fun datatype_compat_cmd raw_fpT_names0 lthy =
  let
    val (nn, b_names, compat_b_names, lfp_sugar_thms, infos, lthy') =
      mk_infos_of_mutually_recursive_new_datatypes true true eq_set raw_fpT_names0 lthy;

    val all_notes =
      (case lfp_sugar_thms of
        NONE => []
      | SOME ((induct_thms, induct_thm, induct_attrs), (rec_thmss, _)) =>
        let
          val common_name = compatN ^ mk_common_name b_names;

          val common_notes =
            (if nn > 1 then [(inductN, [induct_thm], induct_attrs)] else [])
            |> filter_out (null o #2)
            |> map (fn (thmN, thms, attrs) =>
              ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));

          val notes =
            [(inductN, map single induct_thms, induct_attrs),
             (recN, rec_thmss, code_nitpicksimp_simp_attrs)]
            |> filter_out (null o #2)
            |> maps (fn (thmN, thmss, attrs) =>
              if forall null thmss then
                []
              else
                map2 (fn b_name => fn thms =>
                    ((Binding.qualify true b_name (Binding.name thmN), attrs), [(thms, [])]))
                  compat_b_names thmss);
        in
          common_notes @ notes
        end);

    val register_interpret =
      Old_Datatype_Data.register infos
      #> Old_Datatype_Data.interpretation_data (Old_Datatype_Aux.default_config, map fst infos);
  in
    lthy'
    |> Local_Theory.raw_theory register_interpret
    |> Local_Theory.notes all_notes
    |> snd
  end;

val _ =
  Outer_Syntax.local_theory @{command_spec "datatype_compat"}
    "register new-style datatypes as old-style datatypes"
    (Scan.repeat1 Parse.type_const >> datatype_compat_cmd);

end;
