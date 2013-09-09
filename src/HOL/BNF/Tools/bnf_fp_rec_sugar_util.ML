(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar_util.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Library for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_UTIL =
sig
  datatype rec_call =
    No_Rec of int |
    Direct_Rec of int (*before*) * int (*after*) |
    Indirect_Rec of int

  datatype corec_call =
    Dummy_No_Corec of int |
    No_Corec of int |
    Direct_Corec of int (*stop?*) * int (*end*) * int (*continue*) |
    Indirect_Corec of int

  type rec_ctr_spec =
    {ctr: term,
     offset: int,
     calls: rec_call list,
     rec_thm: thm}

  type corec_ctr_spec =
    {ctr: term,
     disc: term,
     sels: term list,
     pred: int option,
     calls: corec_call list,
     collapse: thm,
     corec_thm: thm,
     disc_corec: thm,
     sel_corecs: thm list}

  type rec_spec =
    {recx: term,
     nested_map_idents: thm list,
     nested_map_comps: thm list,
     ctr_specs: rec_ctr_spec list}

  type corec_spec =
    {corec: term,
     nested_maps: thm list,
     nested_map_idents: thm list,
     nested_map_comps: thm list,
     ctr_specs: corec_ctr_spec list}

  val massage_indirect_rec_call: Proof.context -> (term -> bool) -> (typ -> typ -> term -> term) ->
    typ list -> term -> term -> term -> term
  val massage_direct_corec_call: Proof.context -> (term -> bool) -> (typ -> typ -> term -> term) ->
    typ list -> typ -> term -> term
  val massage_indirect_corec_call: Proof.context -> (term -> bool) ->
    (typ -> typ -> term -> term) -> typ list -> typ -> term -> term
  val rec_specs_of: binding list -> typ list -> typ list -> (term -> int list) ->
    ((term * term list list) list) list -> local_theory ->
    (bool * rec_spec list * typ list * thm * thm list) * local_theory
  val corec_specs_of: binding list -> typ list -> typ list -> (term -> int list) ->
    ((term * term list list) list) list -> local_theory ->
    (bool * corec_spec list * typ list * thm * thm * thm list * thm list) * local_theory
end;

structure BNF_FP_Rec_Sugar_Util : BNF_FP_REC_SUGAR_UTIL =
struct

open BNF_Util
open BNF_Def
open BNF_Ctr_Sugar
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar

datatype rec_call =
  No_Rec of int |
  Direct_Rec of int * int |
  Indirect_Rec of int;

datatype corec_call =
  Dummy_No_Corec of int |
  No_Corec of int |
  Direct_Corec of int * int * int |
  Indirect_Corec of int;

type rec_ctr_spec =
  {ctr: term,
   offset: int,
   calls: rec_call list,
   rec_thm: thm};

type corec_ctr_spec =
  {ctr: term,
   disc: term,
   sels: term list,
   pred: int option,
   calls: corec_call list,
   collapse: thm,
   corec_thm: thm,
   disc_corec: thm,
   sel_corecs: thm list};

type rec_spec =
  {recx: term,
   nested_map_idents: thm list,
   nested_map_comps: thm list,
   ctr_specs: rec_ctr_spec list};

type corec_spec =
  {corec: term,
   nested_maps: thm list,
   nested_map_idents: thm list,
   nested_map_comps: thm list,
   ctr_specs: corec_ctr_spec list};

val id_def = @{thm id_def};

exception AINT_NO_MAP of term;

fun ill_formed_rec_call ctxt t =
  error ("Ill-formed recursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun ill_formed_corec_call ctxt t =
  error ("Ill-formed corecursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun invalid_map ctxt t =
  error ("Invalid map function in " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_rec_call ctxt t =
  error ("Unexpected recursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_corec_call ctxt t =
  error ("Unexpected corecursive call: " ^ quote (Syntax.string_of_term ctxt t));

fun factor_out_types ctxt massage destU U T =
  (case try destU U of
    SOME (U1, U2) => if U1 = T then massage T U2 else invalid_map ctxt
  | NONE => invalid_map ctxt);

fun map_flattened_map_args ctxt s map_args fs =
  let
    val flat_fs = flatten_type_args_of_bnf (the (bnf_of ctxt s)) Term.dummy fs;
    val flat_fs' = map_args flat_fs;
  in
    permute_like (op aconv) flat_fs fs flat_fs'
  end;

fun massage_indirect_rec_call ctxt has_call massage_unapplied_direct_call bound_Ts y y' =
  let
    val typof = curry fastype_of1 bound_Ts;
    val build_map_fst = build_map ctxt (fst_const o fst);

    val yT = typof y;
    val yU = typof y';

    fun y_of_y' () = build_map_fst (yU, yT) $ y';
    val elim_y = Term.map_aterms (fn t => if t = y then y_of_y' () else t);

    fun check_and_massage_unapplied_direct_call U T t =
      if has_call t then
        factor_out_types ctxt massage_unapplied_direct_call HOLogic.dest_prodT U T t
      else
        HOLogic.mk_comp (t, build_map_fst (U, T));

    fun massage_map (Type (_, Us)) (Type (s, Ts)) t =
        (case try (dest_map ctxt s) t of
          SOME (map0, fs) =>
          let
            val Type (_, ran_Ts) = range_type (typof t);
            val map' = mk_map (length fs) Us ran_Ts map0;
            val fs' = map_flattened_map_args ctxt s (map3 massage_map_or_map_arg Us Ts) fs;
          in
            list_comb (map', fs')
          end
        | NONE => raise AINT_NO_MAP t)
      | massage_map _ _ t = raise AINT_NO_MAP t
    and massage_map_or_map_arg U T t =
      if T = U then
        if has_call t then unexpected_rec_call ctxt t else t
      else
        massage_map U T t
        handle AINT_NO_MAP _ => check_and_massage_unapplied_direct_call U T t;

    fun massage_call (t as t1 $ t2) =
        if t2 = y then
          massage_map yU yT (elim_y t1) $ y'
          handle AINT_NO_MAP t' => invalid_map ctxt t'
        else
          ill_formed_rec_call ctxt t
      | massage_call t = if t = y then y_of_y' () else ill_formed_rec_call ctxt t;
  in
    massage_call o Envir.beta_eta_contract
  end;

fun massage_let_and_if ctxt has_call massage_rec massage_else U T t =
  (case Term.strip_comb t of
    (Const (@{const_name Let}, _), [arg1, arg2]) => massage_rec U T (betapply (arg2, arg1))
  | (Const (@{const_name If}, _), arg :: args) =>
    if has_call arg then unexpected_corec_call ctxt arg
    else list_comb (If_const U $ arg, map (massage_rec U T) args)
  | _ => massage_else U T t);

fun massage_direct_corec_call ctxt has_call massage_direct_call bound_Ts res_U t =
  let
    val typof = curry fastype_of1 bound_Ts;

    fun massage_call U T =
      massage_let_and_if ctxt has_call massage_call massage_direct_call U T;
  in
    massage_call res_U (typof t) (Envir.beta_eta_contract t)
  end;

fun massage_indirect_corec_call ctxt has_call massage_direct_call bound_Ts res_U t =
  let
    val typof = curry fastype_of1 bound_Ts;
    val build_map_Inl = build_map ctxt (uncurry Inl_const o dest_sumT o snd)

    fun check_and_massage_direct_call U T t =
      if has_call t then factor_out_types ctxt massage_direct_call dest_sumT U T t
      else build_map_Inl (T, U) $ t;

    fun check_and_massage_unapplied_direct_call U T t =
      let val var = Var ((Name.uu, Term.maxidx_of_term t + 1), domain_type (typof t)) in
        Term.lambda var (check_and_massage_direct_call U T (t $ var))
      end;

    fun massage_map (Type (_, Us)) (Type (s, Ts)) t =
        (case try (dest_map ctxt s) t of
          SOME (map0, fs) =>
          let
            val Type (_, dom_Ts) = domain_type (typof t);
            val map' = mk_map (length fs) dom_Ts Us map0;
            val fs' = map_flattened_map_args ctxt s (map3 massage_map_or_map_arg Us Ts) fs;
          in
            list_comb (map', fs')
          end
        | NONE => raise AINT_NO_MAP t)
      | massage_map _ _ t = raise AINT_NO_MAP t
    and massage_map_or_map_arg U T t =
      if T = U then
        if has_call t then unexpected_corec_call ctxt t else t
      else
        massage_map U T t
        handle AINT_NO_MAP _ => check_and_massage_unapplied_direct_call U T t;

    fun massage_call U T =
      massage_let_and_if ctxt has_call massage_call
        (fn U => fn T => fn t =>
            (case U of
              Type (s, Us) =>
              (case try (dest_ctr ctxt s) t of
                SOME (f, args) =>
                let val f' = mk_ctr Us f in
                  list_comb (f', map3 massage_call (binder_types (typof f')) (map typof args) args)
                end
              | NONE =>
                (case t of
                  t1 $ t2 =>
                  (if has_call t2 then
                    check_and_massage_direct_call U T t
                  else
                    massage_map U T t1 $ t2
                    handle AINT_NO_MAP _ => check_and_massage_direct_call U T t)
                | _ => check_and_massage_direct_call U T t))
            | _ => ill_formed_corec_call ctxt t))
        U T
  in
    massage_call res_U (typof t) (Envir.beta_eta_contract t)
  end;

fun indexed xs h = let val h' = h + length xs in (h upto h' - 1, h') end;
fun indexedd xss = fold_map indexed xss;
fun indexeddd xsss = fold_map indexedd xsss;
fun indexedddd xssss = fold_map indexeddd xssss;

fun find_index_eq hs h = find_index (curry (op =) h) hs;

val lose_co_rec = false (*FIXME: try true?*);

fun rec_specs_of bs arg_Ts res_Ts get_indices callssss0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val ((nontriv, missing_arg_Ts, perm0_kks,
          fp_sugars as {nested_bnfs, fp_res = {xtor_co_iterss = ctor_iters1 :: _, ...},
            co_inducts = [induct_thm], ...} :: _), lthy') =
      nested_to_mutual_fps lose_co_rec Least_FP bs arg_Ts get_indices callssss0 lthy;

    val perm_fp_sugars = sort (int_ord o pairself #index) fp_sugars;

    val indices = map #index fp_sugars;
    val perm_indices = map #index perm_fp_sugars;

    val perm_ctrss = map (#ctrs o of_fp_sugar #ctr_sugars) perm_fp_sugars;
    val perm_ctr_Tsss = map (map (binder_types o fastype_of)) perm_ctrss;
    val perm_fpTs = map (body_type o fastype_of o hd) perm_ctrss;

    val nn0 = length arg_Ts;
    val nn = length perm_fpTs;
    val kks = 0 upto nn - 1;
    val perm_ns = map length perm_ctr_Tsss;
    val perm_mss = map (map length) perm_ctr_Tsss;

    val perm_Cs = map (body_type o fastype_of o co_rec_of o of_fp_sugar (#xtor_co_iterss o #fp_res))
      perm_fp_sugars;
    val perm_fun_arg_Tssss = mk_iter_fun_arg_types perm_Cs perm_ns perm_mss (co_rec_of ctor_iters1);

    fun unpermute0 perm0_xs = permute_like (op =) perm0_kks kks perm0_xs;
    fun unpermute perm_xs = permute_like (op =) perm_indices indices perm_xs;

    val induct_thms = unpermute0 (conj_dests nn induct_thm);

    val fpTs = unpermute perm_fpTs;
    val Cs = unpermute perm_Cs;

    val As_rho = tvar_subst thy (take nn0 fpTs) arg_Ts;
    val Cs_rho = map (fst o dest_TVar) Cs ~~ pad_list HOLogic.unitT nn res_Ts;

    val substA = Term.subst_TVars As_rho;
    val substAT = Term.typ_subst_TVars As_rho;
    val substCT = Term.typ_subst_TVars Cs_rho;

    val perm_Cs' = map substCT perm_Cs;

    fun offset_of_ctr 0 _ = 0
      | offset_of_ctr n ({ctrs, ...} :: ctr_sugars) =
        length ctrs + offset_of_ctr (n - 1) ctr_sugars;

    fun call_of [i] [T] = (if exists_subtype_in Cs T then Indirect_Rec else No_Rec) i
      | call_of [i, i'] _ = Direct_Rec (i, i');

    fun mk_ctr_spec ctr offset fun_arg_Tss rec_thm =
      let
        val (fun_arg_hss, _) = indexedd fun_arg_Tss 0;
        val fun_arg_hs = flat_rec_arg_args fun_arg_hss;
        val fun_arg_iss = map (map (find_index_eq fun_arg_hs)) fun_arg_hss;
      in
        {ctr = substA ctr, offset = offset, calls = map2 call_of fun_arg_iss fun_arg_Tss,
         rec_thm = rec_thm}
      end;

    fun mk_ctr_specs index ctr_sugars iter_thmsss =
      let
        val ctrs = #ctrs (nth ctr_sugars index);
        val rec_thmss = co_rec_of (nth iter_thmsss index);
        val k = offset_of_ctr index ctr_sugars;
        val n = length ctrs;
      in
        map4 mk_ctr_spec ctrs (k upto k + n - 1) (nth perm_fun_arg_Tssss index) rec_thmss
      end;

    fun mk_spec {T, index, ctr_sugars, co_iterss = iterss, co_iter_thmsss = iter_thmsss, ...} =
      {recx = mk_co_iter thy Least_FP (substAT T) perm_Cs' (co_rec_of (nth iterss index)),
       nested_map_idents = map (unfold_thms lthy [id_def] o map_id0_of_bnf) nested_bnfs,
       nested_map_comps = map map_comp_of_bnf nested_bnfs,
       ctr_specs = mk_ctr_specs index ctr_sugars iter_thmsss};
  in
    ((nontriv, map mk_spec fp_sugars, missing_arg_Ts, induct_thm, induct_thms), lthy')
  end;

fun corec_specs_of bs arg_Ts res_Ts get_indices callssss0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val ((nontriv, missing_res_Ts, perm0_kks,
          fp_sugars as {nested_bnfs, fp_res = {xtor_co_iterss = dtor_coiters1 :: _, ...},
          co_inducts = coinduct_thms, ...} :: _), lthy') =
      nested_to_mutual_fps lose_co_rec Greatest_FP bs res_Ts get_indices callssss0 lthy;

    val perm_fp_sugars = sort (int_ord o pairself #index) fp_sugars;

    val indices = map #index fp_sugars;
    val perm_indices = map #index perm_fp_sugars;

    val perm_ctrss = map (#ctrs o of_fp_sugar #ctr_sugars) perm_fp_sugars;
    val perm_ctr_Tsss = map (map (binder_types o fastype_of)) perm_ctrss;
    val perm_fpTs = map (body_type o fastype_of o hd) perm_ctrss;

    val nn0 = length res_Ts;
    val nn = length perm_fpTs;
    val kks = 0 upto nn - 1;
    val perm_ns = map length perm_ctr_Tsss;
    val perm_mss = map (map length) perm_ctr_Tsss;

    val perm_Cs = map (domain_type o body_fun_type o fastype_of o co_rec_of o
      of_fp_sugar (#xtor_co_iterss o #fp_res)) perm_fp_sugars;
    val (perm_p_Tss, (perm_q_Tssss, _, perm_f_Tssss, _)) =
      mk_coiter_fun_arg_types perm_Cs perm_ns perm_mss (co_rec_of dtor_coiters1);

    val (perm_p_hss, h) = indexedd perm_p_Tss 0;
    val (perm_q_hssss, h') = indexedddd perm_q_Tssss h;
    val (perm_f_hssss, _) = indexedddd perm_f_Tssss h';

    val fun_arg_hs =
      flat (map3 flat_corec_preds_predsss_gettersss perm_p_hss perm_q_hssss perm_f_hssss);

    fun unpermute0 perm0_xs = permute_like (op =) perm0_kks kks perm0_xs;
    fun unpermute perm_xs = permute_like (op =) perm_indices indices perm_xs;

    val coinduct_thmss = map (unpermute0 o conj_dests nn) coinduct_thms;

    val p_iss = map (map (find_index_eq fun_arg_hs)) (unpermute perm_p_hss);
    val q_issss = map (map (map (map (find_index_eq fun_arg_hs)))) (unpermute perm_q_hssss);
    val f_issss = map (map (map (map (find_index_eq fun_arg_hs)))) (unpermute perm_f_hssss);

    val f_Tssss = unpermute perm_f_Tssss;
    val fpTs = unpermute perm_fpTs;
    val Cs = unpermute perm_Cs;

    val As_rho = tvar_subst thy (take nn0 fpTs) res_Ts;
    val Cs_rho = map (fst o dest_TVar) Cs ~~ pad_list HOLogic.unitT nn arg_Ts;

    val substA = Term.subst_TVars As_rho;
    val substAT = Term.typ_subst_TVars As_rho;
    val substCT = Term.typ_subst_TVars Cs_rho;

    val perm_Cs' = map substCT perm_Cs;

    fun call_of nullary [] [g_i] [Type (@{type_name fun}, [_, T])] =
        (if exists_subtype_in Cs T then Indirect_Corec
         else if nullary then Dummy_No_Corec
         else No_Corec) g_i
      | call_of _ [q_i] [g_i, g_i'] _ = Direct_Corec (q_i, g_i, g_i');

    fun mk_ctr_spec ctr disc sels p_ho q_iss f_iss f_Tss collapse corec_thm disc_corec sel_corecs =
      let val nullary = not (can dest_funT (fastype_of ctr)) in
        {ctr = substA ctr, disc = substA disc, sels = map substA sels, pred = p_ho,
         calls = map3 (call_of nullary) q_iss f_iss f_Tss, collapse = collapse,
         corec_thm = corec_thm, disc_corec = disc_corec, sel_corecs = sel_corecs}
      end;

    fun mk_ctr_specs index ctr_sugars p_is q_isss f_isss f_Tsss coiter_thmsss disc_coitersss
        sel_coiterssss =
      let
        val ctrs = #ctrs (nth ctr_sugars index);
        val discs = #discs (nth ctr_sugars index);
        val selss = #selss (nth ctr_sugars index);
        val p_ios = map SOME p_is @ [NONE];
        val collapses = #collapses (nth ctr_sugars index);
        val corec_thms = co_rec_of (nth coiter_thmsss index);
        val disc_corecs = co_rec_of (nth disc_coitersss index);
        val sel_corecss = co_rec_of (nth sel_coiterssss index);
      in
        map11 mk_ctr_spec ctrs discs selss p_ios q_isss f_isss f_Tsss collapses corec_thms
          disc_corecs sel_corecss
      end;

    fun mk_spec {T, index, ctr_sugars, co_iterss = coiterss, co_iter_thmsss = coiter_thmsss,
          disc_co_itersss = disc_coitersss, sel_co_iterssss = sel_coiterssss, ...}
        p_is q_isss f_isss f_Tsss =
      {corec = mk_co_iter thy Greatest_FP (substAT T) perm_Cs' (co_rec_of (nth coiterss index)),
       nested_maps = [] (*FIXME*),
       nested_map_idents = map (unfold_thms lthy [id_def] o map_id0_of_bnf) nested_bnfs,
       nested_map_comps = map map_comp_of_bnf nested_bnfs,
       ctr_specs = mk_ctr_specs index ctr_sugars p_is q_isss f_isss f_Tsss coiter_thmsss
         disc_coitersss sel_coiterssss};
  in
    ((nontriv, map5 mk_spec fp_sugars p_iss q_issss f_issss f_Tssss, missing_res_Ts,
      co_induct_of coinduct_thms, strong_co_induct_of coinduct_thms, co_induct_of coinduct_thmss,
      strong_co_induct_of coinduct_thmss), lthy')
  end;

end;
