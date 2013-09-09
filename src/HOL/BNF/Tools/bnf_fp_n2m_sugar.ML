(*  Title:      HOL/BNF/Tools/bnf_fp_n2m_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Suggared flattening of nested to mutual (co)recursion.
*)

signature BNF_FP_N2M_SUGAR =
sig
  val mutualize_fp_sugars: bool -> bool -> BNF_FP_Util.fp_kind -> binding list -> typ list ->
    (term -> int list) -> term list list list list -> BNF_FP_Def_Sugar.fp_sugar list ->
    local_theory -> (bool * BNF_FP_Def_Sugar.fp_sugar list) * local_theory
  val pad_and_indexify_calls: BNF_FP_Def_Sugar.fp_sugar list -> int ->
    (term * term list list) list list -> term list list list list
  val nested_to_mutual_fps: bool -> BNF_FP_Util.fp_kind -> binding list -> typ list ->
    (term -> int list) -> ((term * term list list) list) list -> local_theory ->
    (bool * typ list * int list * BNF_FP_Def_Sugar.fp_sugar list) * local_theory
end;

structure BNF_FP_N2M_Sugar : BNF_FP_N2M_SUGAR =
struct

open BNF_Util
open BNF_Def
open BNF_Ctr_Sugar
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M

val n2mN = "n2m_"

(* TODO: test with sort constraints on As *)
(* TODO: use right sorting order for "fp_sort" w.r.t. original BNFs (?) -- treat new variables
   as deads? *)
fun mutualize_fp_sugars lose_co_rec mutualize fp bs fpTs get_indices callssss fp_sugars0
    no_defs_lthy0 =
  (* TODO: Also check whether there's any lost recursion? *)
  if mutualize orelse has_duplicates (op =) fpTs then
    let
      val thy = Proof_Context.theory_of no_defs_lthy0;

      val qsotm = quote o Syntax.string_of_term no_defs_lthy0;

      fun heterogeneous_call t = error ("Heterogeneous recursive call: " ^ qsotm t);
      fun incompatible_calls t1 t2 =
        error ("Incompatible recursive calls: " ^ qsotm t1 ^ " vs. " ^ qsotm t2);

      val b_names = map Binding.name_of bs;
      val fp_b_names = map base_name_of_typ fpTs;

      val nn = length fpTs;

      fun target_ctr_sugar_of_fp_sugar fpT {T, index, ctr_sugars, ...} =
        let
          val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (T, fpT) Vartab.empty) [];
          val phi = Morphism.term_morphism (Term.subst_TVars rho);
        in
          morph_ctr_sugar phi (nth ctr_sugars index)
        end;

      val ctr_defss = map (of_fp_sugar #ctr_defss) fp_sugars0;
      val ctr_sugars0 = map2 target_ctr_sugar_of_fp_sugar fpTs fp_sugars0;

      val ctrss = map #ctrs ctr_sugars0;
      val ctr_Tss = map (map fastype_of) ctrss;

      val As' = fold (fold Term.add_tfreesT) ctr_Tss [];
      val As = map TFree As';

      val ((Cs, Xs), no_defs_lthy) =
        no_defs_lthy0
        |> fold Variable.declare_typ As
        |> mk_TFrees nn
        ||>> variant_tfrees fp_b_names;

      (* If "lose_co_rec" is "true", the function "null" on "'a list" gives rise to
           'list = unit + 'a list
         instead of
           'list = unit + 'list
         resulting in a simpler (co)induction rule and (co)recursor. *)
      fun freeze_fp_default (T as Type (s, Ts)) =
          (case find_index (curry (op =) T) fpTs of
            ~1 => Type (s, map freeze_fp_default Ts)
          | kk => nth Xs kk)
        | freeze_fp_default T = T;

      fun get_indices_checked call =
        (case get_indices call of
          _ :: _ :: _ => heterogeneous_call call
        | kks => kks);

      fun freeze_fp calls (T as Type (s, Ts)) =
          (case map_filter (try (snd o dest_map no_defs_lthy s)) calls of
            [] =>
            (case union (op = o pairself fst)
                (maps (fn call => map (rpair call) (get_indices_checked call)) calls) [] of
              [] => T |> not lose_co_rec ? freeze_fp_default
            | [(kk, _)] => nth Xs kk
            | (_, call1) :: (_, call2) :: _ => incompatible_calls call1 call2)
          | callss =>
            Type (s, map2 freeze_fp (flatten_type_args_of_bnf (the (bnf_of no_defs_lthy s)) []
              (transpose callss)) Ts))
        | freeze_fp _ T = T;

      val ctr_Tsss = map (map binder_types) ctr_Tss;
      val ctrXs_Tsss = map2 (map2 (map2 freeze_fp)) callssss ctr_Tsss;
      val ctrXs_sum_prod_Ts = map (mk_sumTN_balanced o map HOLogic.mk_tupleT) ctrXs_Tsss;
      val Ts = map (body_type o hd) ctr_Tss;

      val ns = map length ctr_Tsss;
      val kss = map (fn n => 1 upto n) ns;
      val mss = map (map length) ctr_Tsss;

      val fp_eqs = map dest_TFree Xs ~~ ctrXs_sum_prod_Ts;

      val base_fp_names = Name.variant_list [] fp_b_names;
      val fp_bs = map2 (fn b_name => fn base_fp_name =>
          Binding.qualify true b_name (Binding.name (n2mN ^ base_fp_name)))
        b_names base_fp_names;

      val (pre_bnfs, (fp_res as {xtor_co_iterss = xtor_co_iterss0, xtor_co_induct,
             dtor_injects, dtor_ctors, xtor_co_iter_thmss, ...}, lthy)) =
        fp_bnf (construct_mutualized_fp fp fpTs fp_sugars0) fp_bs As' fp_eqs no_defs_lthy;

      val nesting_bnfs = nesty_bnfs lthy ctrXs_Tsss As;
      val nested_bnfs = nesty_bnfs lthy ctrXs_Tsss Xs;

      val ((xtor_co_iterss, iters_args_types, coiters_args_types), _) =
        mk_co_iters_prelims fp fpTs Cs ns mss xtor_co_iterss0 lthy;

      fun mk_binding b suf = Binding.suffix_name ("_" ^ suf) b;

      val ((co_iterss, co_iter_defss), lthy) =
        fold_map2 (fn b =>
          (if fp = Least_FP then define_iters [foldN, recN] (the iters_args_types)
           else define_coiters [unfoldN, corecN] (the coiters_args_types))
            (mk_binding b) fpTs Cs) fp_bs xtor_co_iterss lthy
        |>> split_list;

      val rho = tvar_subst thy Ts fpTs;
      val ctr_sugar_phi =
        Morphism.compose (Morphism.typ_morphism (Term.typ_subst_TVars rho))
          (Morphism.term_morphism (Term.subst_TVars rho));
      val inst_ctr_sugar = morph_ctr_sugar ctr_sugar_phi;

      val ctr_sugars = map inst_ctr_sugar ctr_sugars0;

      val (co_inducts, un_fold_thmss, co_rec_thmss, disc_unfold_thmss, disc_corec_thmss,
           sel_unfold_thmsss, sel_corec_thmsss) =
        if fp = Least_FP then
          derive_induct_iters_thms_for_types pre_bnfs (the iters_args_types) xtor_co_induct
            xtor_co_iter_thmss nesting_bnfs nested_bnfs fpTs Cs Xs ctrXs_Tsss ctrss ctr_defss
            co_iterss co_iter_defss lthy
          |> (fn ((_, induct, _), (fold_thmss, _), (rec_thmss, _)) =>
            ([induct], fold_thmss, rec_thmss, [], [], [], []))
        else
          derive_coinduct_coiters_thms_for_types pre_bnfs (the coiters_args_types) xtor_co_induct
            dtor_injects dtor_ctors xtor_co_iter_thmss nesting_bnfs fpTs Cs kss mss ns ctr_defss
            ctr_sugars co_iterss co_iter_defss (Proof_Context.export lthy no_defs_lthy) lthy
          |> (fn ((coinduct_thms_pairs, _), (unfold_thmss, corec_thmss, _), _, _,
                  (disc_unfold_thmss, disc_corec_thmss, _),
                  (sel_unfold_thmsss, sel_corec_thmsss, _)) =>
            (map snd coinduct_thms_pairs, unfold_thmss, corec_thmss, disc_unfold_thmss,
             disc_corec_thmss, sel_unfold_thmsss, sel_corec_thmsss));

      val phi = Proof_Context.export_morphism no_defs_lthy no_defs_lthy0;

      fun mk_target_fp_sugar (kk, T) =
        {T = T, fp = fp, index = kk, pre_bnfs = pre_bnfs, nested_bnfs = nested_bnfs,
         nesting_bnfs = nesting_bnfs, fp_res = fp_res, ctr_defss = ctr_defss,
         ctr_sugars = ctr_sugars, co_inducts = co_inducts, co_iterss = co_iterss,
         co_iter_thmsss = transpose [un_fold_thmss, co_rec_thmss],
         disc_co_itersss = transpose [disc_unfold_thmss, disc_corec_thmss],
         sel_co_iterssss = transpose [sel_unfold_thmsss, sel_corec_thmsss]}
        |> morph_fp_sugar phi;
    in
      ((true, map_index mk_target_fp_sugar fpTs), lthy)
    end
  else
    (* TODO: reorder hypotheses and predicates in (co)induction rules? *)
    ((false, fp_sugars0), no_defs_lthy0);

fun indexify_callsss fp_sugar callsss =
  let
    val {ctrs, ...} = of_fp_sugar #ctr_sugars fp_sugar;
    fun do_ctr ctr =
      (case AList.lookup Term.aconv_untyped callsss ctr of
        NONE => replicate (num_binder_types (fastype_of ctr)) []
      | SOME callss => map (map Envir.beta_eta_contract) callss);
  in
    map do_ctr ctrs
  end;

fun pad_and_indexify_calls fp_sugars0 = map2 indexify_callsss fp_sugars0 oo pad_list [];

fun nested_to_mutual_fps lose_co_rec fp actual_bs actual_Ts get_indices actual_callssss0 lthy =
  let
    val qsoty = quote o Syntax.string_of_typ lthy;
    val qsotys = space_implode " or " o map qsoty;

    fun not_co_datatype0 T = error (qsoty T ^ " is not a " ^ co_prefix fp ^ "datatype");
    fun not_co_datatype (T as Type (s, _)) =
        if fp = Least_FP andalso
           is_some (Datatype_Data.get_info (Proof_Context.theory_of lthy) s) then
          error (qsoty T ^ " is not a new-style datatype (cf. \"datatype_new\")")
        else
          not_co_datatype0 T
      | not_co_datatype T = not_co_datatype0 T;
    fun not_mutually_nested_rec Ts1 Ts2 =
      error (qsotys Ts1 ^ " is neither mutually recursive with nor nested recursive via " ^
        qsotys Ts2);

    val perm_actual_Ts as Type (_, ty_args0) :: _ =
      sort (int_ord o pairself Term.size_of_typ) actual_Ts;

    fun check_enrich_with_mutuals _ [] = []
      | check_enrich_with_mutuals seen ((T as Type (T_name, ty_args)) :: Ts) =
        (case fp_sugar_of lthy T_name of
          SOME ({fp = fp', fp_res = {Ts = Ts', ...}, ...}) =>
          if fp = fp' then
            let
              val mutual_Ts = map (fn Type (s, _) => Type (s, ty_args)) Ts';
              val _ =
                seen = [] orelse exists (exists_subtype_in seen) mutual_Ts orelse
                not_mutually_nested_rec mutual_Ts seen;
              val (seen', Ts') = List.partition (member (op =) mutual_Ts) Ts;
            in
              mutual_Ts @ check_enrich_with_mutuals (seen @ T :: seen') Ts'
            end
          else
            not_co_datatype T
        | NONE => not_co_datatype T)
      | check_enrich_with_mutuals _ (T :: _) = not_co_datatype T;

    val perm_Ts = check_enrich_with_mutuals [] perm_actual_Ts;

    val missing_Ts = perm_Ts |> subtract (op =) actual_Ts;
    val Ts = actual_Ts @ missing_Ts;

    val nn = length Ts;
    val kks = 0 upto nn - 1;

    val common_name = mk_common_name (map Binding.name_of actual_bs);
    val bs = pad_list (Binding.name common_name) nn actual_bs;

    fun permute xs = permute_like (op =) Ts perm_Ts xs;
    fun unpermute perm_xs = permute_like (op =) perm_Ts Ts perm_xs;

    val perm_bs = permute bs;
    val perm_kks = permute kks;
    val perm_fp_sugars0 = map (the o fp_sugar_of lthy o fst o dest_Type) perm_Ts;

    val mutualize = exists (fn Type (_, ty_args) => ty_args <> ty_args0) Ts;
    val perm_callssss = pad_and_indexify_calls perm_fp_sugars0 nn actual_callssss0;

    val get_perm_indices = map (fn kk => find_index (curry (op =) kk) perm_kks) o get_indices;

    val ((nontriv, perm_fp_sugars), lthy) =
      mutualize_fp_sugars lose_co_rec mutualize fp perm_bs perm_Ts get_perm_indices perm_callssss
        perm_fp_sugars0 lthy;

    val fp_sugars = unpermute perm_fp_sugars;
  in
    ((nontriv, missing_Ts, perm_kks, fp_sugars), lthy)
  end;

end;
