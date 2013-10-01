(*  Title:      HOL/BNF/Tools/bnf_lfp_compat.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Compatibility layer with the old datatype package.
*)

signature BNF_LFP_COMPAT =
sig
  val datatype_new_compat_cmd : string list -> local_theory -> local_theory
end;

structure BNF_LFP_Compat : BNF_LFP_COMPAT =
struct

open Ctr_Sugar
open BNF_Util
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar

fun dtyp_of_typ _ (TFree a) = Datatype_Aux.DtTFree a
  | dtyp_of_typ recTs (T as Type (s, Ts)) =
    (case find_index (curry (op =) T) recTs of
      ~1 => Datatype_Aux.DtType (s, map (dtyp_of_typ recTs) Ts)
    | kk => Datatype_Aux.DtRec kk);

val compatN = "compat_";

(* TODO: graceful failure for local datatypes -- perhaps by making the command global *)
fun datatype_new_compat_cmd raw_fpT_names lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    fun not_datatype s = error (quote s ^ " is not a new-style datatype");
    fun not_mutually_recursive ss =
      error ("{" ^ commas ss ^ "} is not a complete set of mutually recursive new-style datatypes");

    val (fpT_names as fpT_name1 :: _) =
      map (fst o dest_Type o Proof_Context.read_type_name_proper lthy false) raw_fpT_names;

    val Ss = Sign.arity_sorts thy fpT_name1 HOLogic.typeS;

    val (unsorted_As, _) = lthy |> mk_TFrees (length Ss);
    val As = map2 resort_tfree Ss unsorted_As;

    fun lfp_sugar_of s =
      (case fp_sugar_of lthy s of
        SOME (fp_sugar as {fp = Least_FP, ...}) => fp_sugar
      | _ => not_datatype s);

    val fp_sugar0 as {fp_res = {Ts = fpTs0, ...}, ...} = lfp_sugar_of fpT_name1;
    val fpT_names' = map (fst o dest_Type) fpTs0;

    val _ = eq_set (op =) (fpT_names, fpT_names') orelse not_mutually_recursive fpT_names;

    val fpTs as fpT1 :: _ = map (fn s => Type (s, As)) fpT_names';

    fun add_nested_types_of (T as Type (s, _)) seen =
      if member (op =) seen T orelse s = @{type_name fun} then
        seen
      else
        (case try lfp_sugar_of s of
          SOME ({T = T0, fp_res = {Ts = mutual_Ts0, ...}, ctr_sugars, ...}) =>
          let
            val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (T0, T) Vartab.empty) [];
            val substT = Term.typ_subst_TVars rho;

            val mutual_Ts = map substT mutual_Ts0;

            fun add_interesting_subtypes (U as Type (_, Us)) =
                (case filter (exists_subtype_in mutual_Ts) Us of [] => I
                | Us' => insert (op =) U #> fold add_interesting_subtypes Us')
              | add_interesting_subtypes _ = I;

            val ctrs = maps #ctrs ctr_sugars;
            val ctr_Ts = maps (binder_types o substT o fastype_of) ctrs |> distinct (op =);
            val subTs = fold add_interesting_subtypes ctr_Ts [];
          in
            fold add_nested_types_of subTs (seen @ mutual_Ts)
          end
        | NONE => error ("Unsupported recursion via type constructor " ^ quote s ^
            " not associated with new-style datatype (cf. \"datatype_new\")"));

    val Ts = add_nested_types_of fpT1 [];
    val b_names = map base_name_of_typ Ts;
    val compat_b_names = map (prefix compatN) b_names;
    val compat_bs = map Binding.name compat_b_names;
    val common_name = compatN ^ mk_common_name b_names;
    val nn_fp = length fpTs;
    val nn = length Ts;
    val get_indices = K [];
    val fp_sugars0 = if nn = 1 then [fp_sugar0] else map (lfp_sugar_of o fst o dest_Type) Ts;
    val callssss = pad_and_indexify_calls fp_sugars0 nn [];
    val has_nested = nn > nn_fp;

    val ((fp_sugars, (lfp_sugar_thms, _)), lthy) =
      mutualize_fp_sugars has_nested Least_FP compat_bs Ts get_indices callssss fp_sugars0 lthy;

    val {ctr_sugars, co_inducts = [induct], co_iterss, co_iter_thmsss = iter_thmsss, ...} :: _ =
      fp_sugars;
    val inducts = conj_dests nn induct;

    val frozen_Ts = map Type.legacy_freeze_type Ts;
    val mk_dtyp = dtyp_of_typ frozen_Ts;

    fun mk_ctr_descr (Const (s, T)) =
      (s, map mk_dtyp (binder_types (Type.legacy_freeze_type T)));
    fun mk_typ_descr index (Type (T_name, Ts)) ({ctrs, ...} : ctr_sugar) =
      (index, (T_name, map mk_dtyp Ts, map mk_ctr_descr ctrs));

    val descr = map3 mk_typ_descr (0 upto nn - 1) frozen_Ts ctr_sugars;
    val recs = map (fst o dest_Const o co_rec_of) co_iterss;
    val rec_thms = flat (map co_rec_of iter_thmsss);

    fun mk_info ({T = Type (T_name0, _), index, ...} : fp_sugar) =
      let
        val {casex, exhaust, nchotomy, injects, distincts, case_thms, case_cong, weak_case_cong,
          split, split_asm, ...} = nth ctr_sugars index;
      in
        (T_name0,
         {index = index, descr = descr, inject = injects, distinct = distincts, induct = induct,
         inducts = inducts, exhaust = exhaust, nchotomy = nchotomy, rec_names = recs,
         rec_rewrites = rec_thms, case_name = fst (dest_Const casex), case_rewrites = case_thms,
         case_cong = case_cong, weak_case_cong = weak_case_cong, split = split,
         split_asm = split_asm})
      end;

    val infos = map mk_info (take nn_fp fp_sugars);

    val all_notes =
      (case lfp_sugar_thms of
        NONE => []
      | SOME ((induct_thms, induct_thm, induct_attrs), (fold_thmss, rec_thmss, _)) =>
        let
          val common_notes =
            (if nn > 1 then [(inductN, [induct_thm], induct_attrs)] else [])
            |> filter_out (null o #2)
            |> map (fn (thmN, thms, attrs) =>
              ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));

          val notes =
            [(foldN, fold_thmss, []),
             (inductN, map single induct_thms, induct_attrs),
             (recN, rec_thmss, [])]
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
  Outer_Syntax.local_theory @{command_spec "datatype_new_compat"}
    "register a new-style datatype as an old-style datatype"
    (Scan.repeat1 Parse.type_const >> datatype_new_compat_cmd);

end;
