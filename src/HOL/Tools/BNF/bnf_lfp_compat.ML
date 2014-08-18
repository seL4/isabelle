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

fun reindex_desc desc =
  let
    val kks = map fst desc;
    val perm_kks = sort int_ord kks;

    fun perm_dtyp (Datatype_Aux.DtType (s, Ds)) = Datatype_Aux.DtType (s, map perm_dtyp Ds)
      | perm_dtyp (Datatype_Aux.DtRec kk) = Datatype_Aux.DtRec (find_index (curry (op =) kk) kks)
      | perm_dtyp D = D
  in
    if perm_kks = kks then
      desc
    else
      perm_kks ~~
      map (fn (_, (s, Ds, sDss)) => (s, map perm_dtyp Ds, map (apsnd (map perm_dtyp)) sDss)) desc
  end

(* TODO: graceful failure for local datatypes -- perhaps by making the command global *)
fun datatype_compat_cmd raw_fpT_names0 lthy =
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

    val _ = eq_set (op =) (fpT_names0, fpT_names) orelse not_mutually_recursive fpT_names0;

    val (As_names, _) = lthy |> Variable.variant_fixes (map (fn TVar ((s, _), _) => s) var_As);
    val As = map2 (fn s => fn TVar (_, S) => TFree (s, S)) As_names var_As;
    val fpTs = map (fn s => Type (s, As)) fpT_names;

    val nn_fp = length fpTs;

    val mk_dtyp = Datatype_Aux.dtyp_of_typ (map (apsnd (map Term.dest_TFree) o dest_Type) fpTs);

    fun mk_ctr_descr Ts = mk_ctr Ts #> dest_Const ##> (binder_types #> map mk_dtyp);
    fun mk_typ_descr index (Type (T_name, Ts)) ({ctrs, ...} : ctr_sugar) =
      (index, (T_name, map mk_dtyp Ts, map (mk_ctr_descr Ts) ctrs));

    val fp_ctr_sugars = map (#ctr_sugar o lfp_sugar_of) fpT_names;
    val orig_descr = map3 mk_typ_descr (0 upto nn_fp - 1) fpTs fp_ctr_sugars;
    val all_infos = Datatype_Data.get_all thy;
    val (orig_descr' :: nested_descrs, _) =
      Datatype_Aux.unfold_datatypes lthy orig_descr all_infos orig_descr nn_fp;

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
                length (filter_out (exists Datatype_Aux.is_rec_type o #2 o snd) descr)
              | NONE => raise Fail "unknown old-style datatype");
        in
          chop nn full_descr ||> cliquify_descr |> op ::
        end;

    (* put nested types before the types that nest them, as needed for N2M *)
    val descrs = burrow reindex_desc (orig_descr' :: rev nested_descrs);
    val (cliques, descr) =
      split_list (flat (map_index (fn (i, descr) => map (pair i) descr)
        (maps cliquify_descr descrs)));

    val dest_dtyp = Datatype_Aux.typ_of_dtyp descr;

    val Ts = Datatype_Aux.get_rec_types descr;
    val nn = length Ts;

    val fp_sugars0 = map (lfp_sugar_of o fst o dest_Type) Ts;
    val ctr_Tsss = map (map (map dest_dtyp o snd) o #3 o snd) descr;
    val kkssss =
      map (map (map (fn Datatype_Aux.DtRec kk => [kk] | _ => []) o snd) o #3 o snd) descr;

    val callers = map (fn kk => Var ((Name.uu, kk), @{typ "unit => unit"})) (0 upto nn - 1);

    fun apply_comps n kk =
      mk_partial_compN n (replicate n HOLogic.unitT ---> HOLogic.unitT) (nth callers kk);

    val callssss =
      map2 (map2 (map2 (fn ctr_T => map (apply_comps (num_binder_types ctr_T))))) ctr_Tsss kkssss;

    val b_names = Name.variant_list [] (map base_name_of_typ Ts);
    val compat_b_names = map (prefix compatN) b_names;
    val compat_bs = map Binding.name compat_b_names;
    val common_name = compatN ^ mk_common_name b_names;

    val ((fp_sugars, (lfp_sugar_thms, _)), lthy) =
      if nn > nn_fp then
        mutualize_fp_sugars Least_FP cliques compat_bs Ts callers callssss fp_sugars0 lthy
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
    |> Local_Theory.notes all_notes
    |> snd
  end;

val _ =
  Outer_Syntax.local_theory @{command_spec "datatype_compat"}
    "register new-style datatypes as old-style datatypes"
    (Scan.repeat1 Parse.type_const >> datatype_compat_cmd);

end;
