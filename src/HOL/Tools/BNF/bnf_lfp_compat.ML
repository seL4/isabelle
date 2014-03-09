(*  Title:      HOL/Tools/BNF/bnf_lfp_compat.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Compatibility layer with the old datatype package ("datatype_compat").
*)

signature BNF_LFP_COMPAT =
sig
  val datatype_compat_cmd : string list -> local_theory -> local_theory
end;

structure BNF_LFP_Compat : BNF_LFP_COMPAT =
struct

open Ctr_Sugar
open BNF_Util
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar

val compatN = "compat_";

val code_nitpicksimp_simp_attrs = Code.add_default_eqn_attrib :: @{attributes [nitpick_simp, simp]};

(* TODO: graceful failure for local datatypes -- perhaps by making the command global *)
fun datatype_compat_cmd raw_fpT_names lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    fun not_datatype s = error (quote s ^ " is not a new-style datatype");
    fun not_mutually_recursive ss =
      error ("{" ^ commas ss ^ "} is not a complete set of mutually recursive new-style datatypes");

    val fpT_names =
      map (fst o dest_Type o Proof_Context.read_type_name {proper = true, strict = false} lthy)
        raw_fpT_names;

    fun lfp_sugar_of s =
      (case fp_sugar_of lthy s of
        SOME (fp_sugar as {fp = Least_FP, ...}) => fp_sugar
      | _ => not_datatype s);

    val fp_ctr_sugars = map (#ctr_sugar o lfp_sugar_of) fpT_names;
    val fpTs0 as Type (_, var_As) :: _ = map (body_type o fastype_of o hd o #ctrs) fp_ctr_sugars;
    val fpT_names' = map (fst o dest_Type) fpTs0;

    val _ = eq_set (op =) (fpT_names, fpT_names') orelse not_mutually_recursive fpT_names;

    val (unsorted_As, _) = lthy |> mk_TFrees (length var_As);
    val As = map2 (resort_tfree o Type.sort_of_atyp) var_As unsorted_As;
    val fpTs as fpT1 :: _ = map (fn s => Type (s, As)) fpT_names';

    fun nested_Tparentss_indicessss_of parent_Tkks (T as Type (s, _)) kk =
      (case try lfp_sugar_of s of
        SOME ({T = T0, fp_res = {Ts = mutual_Ts0, ...}, ...}) =>
        let
          val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (T0, T) Vartab.empty) [];
          val substT = Term.typ_subst_TVars rho;
          val mutual_Ts = map substT mutual_Ts0;
          val mutual_nn = length mutual_Ts;
          val mutual_kks = kk upto kk + mutual_nn - 1;
          val mutual_Tkks = mutual_Ts ~~ mutual_kks;

          fun indices_of_ctr_arg parent_Tkks (U as Type (s, Us)) (accum as (Tparents_ksss, kk')) =
              if s = @{type_name fun} then
                if exists_subtype_in mutual_Ts U then
                  (warning "Incomplete support for recursion through functions -- \
                     \the old 'primrec' will fail";
                   indices_of_ctr_arg parent_Tkks (range_type U) accum)
                else
                  ([], accum)
              else
                (case AList.lookup (op =) (parent_Tkks @ mutual_Tkks) U of
                  SOME kk => ([kk], accum)
                | NONE =>
                  if exists (exists_strict_subtype_in mutual_Ts) Us then
                    error "Deeply nested recursion not supported"
                  else if exists (member (op =) mutual_Ts) Us then
                    ([kk'],
                     nested_Tparentss_indicessss_of parent_Tkks U kk' |>> append Tparents_ksss)
                  else
                    ([], accum))
            | indices_of_ctr_arg _ _ accum = ([], accum);

          fun Tparents_indicesss_of_mutual_type T kk ctr_Tss =
            let val parent_Tkks' = (T, kk) :: parent_Tkks in
              fold_map (fold_map (indices_of_ctr_arg parent_Tkks')) ctr_Tss
              #>> pair parent_Tkks'
            end;

          val ctrss = map (#ctrs o #ctr_sugar o lfp_sugar_of o fst o dest_Type) mutual_Ts;
          val ctr_Tsss = map (map (binder_types o substT o fastype_of)) ctrss;
        in
          ([], kk + mutual_nn)
          |> fold_map3 Tparents_indicesss_of_mutual_type mutual_Ts mutual_kks ctr_Tsss
          |> (fn (Tparentss_kkssss, (Tparentss_kkssss', kk)) =>
            (Tparentss_kkssss @ Tparentss_kkssss', kk))
        end
      | NONE => error ("Unsupported recursion via type constructor " ^ quote s ^
          " not corresponding to new-style datatype (cf. \"datatype_new\")"));

    val (Tparentss_kkssss, _) = nested_Tparentss_indicessss_of [] fpT1 0;
    val Tparentss = map fst Tparentss_kkssss;
    val Ts = map (fst o hd) Tparentss;
    val kkssss = map snd Tparentss_kkssss;

    val fp_sugars0 = map (lfp_sugar_of o fst o dest_Type) Ts;
    val ctrss0 = map (#ctrs o #ctr_sugar) fp_sugars0;
    val ctr_Tsss0 = map (map (binder_types o fastype_of)) ctrss0;

    val b_names = Name.variant_list [] (map base_name_of_typ Ts);
    val compat_b_names = map (prefix compatN) b_names;
    val compat_bs = map Binding.name compat_b_names;
    val common_name = compatN ^ mk_common_name b_names;

    val nn_fp = length fpTs;
    val nn = length Ts;

    val callers = map (fn kk => Var ((Name.uu, kk), @{typ "unit => unit"})) (0 upto nn - 1);

    fun apply_comps n kk =
      mk_partial_compN n (replicate n HOLogic.unitT ---> HOLogic.unitT) (nth callers kk);

    val callssss =
      map2 (map2 (map2 (fn kks => fn ctr_T => map (apply_comps (num_binder_types ctr_T)) kks)))
        kkssss ctr_Tsss0;

    val ((fp_sugars, (lfp_sugar_thms, _)), lthy) =
      if nn > nn_fp then
        mutualize_fp_sugars Least_FP compat_bs Ts callers callssss fp_sugars0 lthy
      else
        ((fp_sugars0, (NONE, NONE)), lthy);

    val {common_co_inducts = [induct], ...} :: _ = fp_sugars;
    val inducts = map (the_single o #co_inducts) fp_sugars;

    fun mk_dtyp [] (TFree a) = Datatype_Aux.DtTFree a
      | mk_dtyp [] (Type (s, Ts)) = Datatype_Aux.DtType (s, map (mk_dtyp []) Ts)
      | mk_dtyp [kk] (Type (@{type_name fun}, [T, T'])) =
        Datatype_Aux.DtType (@{type_name fun}, [mk_dtyp [] T, mk_dtyp [kk] T'])
      | mk_dtyp [kk] T = if nth Ts kk = T then Datatype_Aux.DtRec kk else mk_dtyp [] T;

    fun mk_ctr_descr Ts kkss ctr0 =
      mk_ctr Ts ctr0 |> (fn Const (s, T) => (s, map2 mk_dtyp kkss (binder_types T)));
    fun mk_typ_descr kksss ((Type (T_name, Ts), kk) :: parents) ctrs0 =
      (kk, (T_name, map (mk_dtyp (map snd (take 1 parents))) Ts, map2 (mk_ctr_descr Ts) kksss ctrs0));

    val descr = map3 mk_typ_descr kkssss Tparentss ctrss0;
    val recs = map (fst o dest_Const o #co_rec) fp_sugars;
    val rec_thms = maps #co_rec_thms fp_sugars;

    fun mk_info (kk, {T = Type (T_name0, _), ctr_sugar = {casex, exhaust, nchotomy, injects,
        distincts, case_thms, case_cong, weak_case_cong, split, split_asm, ...}, ...} : fp_sugar) =
      (T_name0,
       {index = kk, descr = descr, inject = injects, distinct = distincts, induct = induct,
       inducts = inducts, exhaust = exhaust, nchotomy = nchotomy, rec_names = recs,
       rec_rewrites = rec_thms, case_name = fst (dest_Const casex), case_rewrites = case_thms,
       case_cong = case_cong, weak_case_cong = weak_case_cong, split = split,
       split_asm = split_asm});

    val infos = map_index mk_info (take nn_fp fp_sugars);

    val all_notes =
      (case lfp_sugar_thms of
        NONE => []
      | SOME ((induct_thms, induct_thm, induct_attrs), (rec_thmss, _)) =>
        let
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
      Datatype_Data.register infos
      #> Datatype_Data.interpretation_data (Datatype_Aux.default_config, map fst infos)
  in
    lthy
    |> Local_Theory.raw_theory register_interpret
    |> Local_Theory.notes all_notes |> snd
  end;

val _ =
  Outer_Syntax.local_theory @{command_spec "datatype_compat"}
    "register new-style datatypes as old-style datatypes"
    (Scan.repeat1 Parse.type_const >> datatype_compat_cmd);

end;
