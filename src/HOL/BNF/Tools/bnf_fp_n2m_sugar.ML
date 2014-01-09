(*  Title:      HOL/BNF/Tools/bnf_fp_n2m_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Suggared flattening of nested to mutual (co)recursion.
*)

signature BNF_FP_N2M_SUGAR =
sig
  val unfold_let: term -> term
  val dest_map: Proof.context -> string -> term -> term * term list

  val mutualize_fp_sugars: BNF_FP_Util.fp_kind -> binding list -> typ list -> (term -> int list) ->
    term list list list list -> BNF_FP_Def_Sugar.fp_sugar list -> local_theory ->
    (BNF_FP_Def_Sugar.fp_sugar list
     * (BNF_FP_Def_Sugar.lfp_sugar_thms option * BNF_FP_Def_Sugar.gfp_sugar_thms option))
    * local_theory
  val indexify_callsss: BNF_FP_Def_Sugar.fp_sugar -> (term * term list list) list ->
    term list list list
  val nested_to_mutual_fps: BNF_FP_Util.fp_kind -> binding list -> typ list -> (term -> int list) ->
    (term * term list list) list list -> local_theory ->
    (typ list * int list * BNF_FP_Def_Sugar.fp_sugar list
     * (BNF_FP_Def_Sugar.lfp_sugar_thms option * BNF_FP_Def_Sugar.gfp_sugar_thms option))
    * local_theory
end;

structure BNF_FP_N2M_Sugar : BNF_FP_N2M_SUGAR =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M

val n2mN = "n2m_"

type n2m_sugar = fp_sugar list * (lfp_sugar_thms option * gfp_sugar_thms option);

structure Data = Generic_Data
(
  type T = n2m_sugar Typtab.table;
  val empty = Typtab.empty;
  val extend = I;
  val merge = Typtab.merge (eq_fst (eq_list eq_fp_sugar));
);

fun morph_n2m_sugar phi (fp_sugars, (lfp_sugar_thms_opt, gfp_sugar_thms_opt)) =
  (map (morph_fp_sugar phi) fp_sugars,
   (Option.map (morph_lfp_sugar_thms phi) lfp_sugar_thms_opt,
    Option.map (morph_gfp_sugar_thms phi) gfp_sugar_thms_opt));

val transfer_n2m_sugar =
  morph_n2m_sugar o Morphism.transfer_morphism o Proof_Context.theory_of;

fun n2m_sugar_of ctxt =
  Typtab.lookup (Data.get (Context.Proof ctxt))
  #> Option.map (transfer_n2m_sugar ctxt);

fun register_n2m_sugar key n2m_sugar =
  Local_Theory.declaration {syntax = false, pervasive = false}
    (fn phi => Data.map (Typtab.default (key, morph_n2m_sugar phi n2m_sugar)));

fun unfold_let (Const (@{const_name Let}, _) $ arg1 $ arg2) = unfold_let (betapply (arg2, arg1))
  | unfold_let (Const (@{const_name prod_case}, _) $ t) =
    (case unfold_let t of
      t' as Abs (s1, T1, Abs (s2, T2, _)) =>
      let val v = Var ((s1 ^ s2, Term.maxidx_of_term t' + 1), HOLogic.mk_prodT (T1, T2)) in
        lambda v (incr_boundvars 1 (betapplys (t', [HOLogic.mk_fst v, HOLogic.mk_snd v])))
      end
    | _ => t)
  | unfold_let (t $ u) = betapply (unfold_let t, unfold_let u)
  | unfold_let (Abs (s, T, t)) = Abs (s, T, unfold_let t)
  | unfold_let t = t;

fun mk_map_pattern ctxt s =
  let
    val bnf = the (bnf_of ctxt s);
    val mapx = map_of_bnf bnf;
    val live = live_of_bnf bnf;
    val (f_Ts, _) = strip_typeN live (fastype_of mapx);
    val fs = map_index (fn (i, T) => Var (("?f", i), T)) f_Ts;
  in
    (mapx, betapplys (mapx, fs))
  end;

fun dest_map ctxt s call =
  let
    val (map0, pat) = mk_map_pattern ctxt s;
    val (_, tenv) = fo_match ctxt call pat;
  in
    (map0, Vartab.fold_rev (fn (_, (_, f)) => cons f) tenv [])
  end;

fun dest_abs_or_applied_map _ _ (Abs (_, _, t)) = (Term.dummy, [t])
  | dest_abs_or_applied_map ctxt s (t1 $ _) = dest_map ctxt s t1;

fun map_partition f xs =
  fold_rev (fn x => fn (ys, (good, bad)) =>
      case f x of SOME y => (y :: ys, (x :: good, bad)) | NONE => (ys, (good, x :: bad)))
    xs ([], ([], []));

fun key_of_fp_eqs fp fpTs fp_eqs =
  Type (fp_case fp "l" "g", fpTs @ maps (fn (x, T) => [TFree x, T]) fp_eqs);

(* TODO: test with sort constraints on As *)
fun mutualize_fp_sugars fp bs fpTs get_indices callssss fp_sugars0 no_defs_lthy0 =
  let
    val thy = Proof_Context.theory_of no_defs_lthy0;

    val qsotm = quote o Syntax.string_of_term no_defs_lthy0;

    fun incompatible_calls t1 t2 =
      error ("Incompatible " ^ co_prefix fp ^ "recursive calls: " ^ qsotm t1 ^ " vs. " ^ qsotm t2);
    fun nested_self_call t =
      error ("Unsupported nested self-call " ^ qsotm t);

    val b_names = map Binding.name_of bs;
    val fp_b_names = map base_name_of_typ fpTs;

    val nn = length fpTs;

    fun target_ctr_sugar_of_fp_sugar fpT ({T, index, ctr_sugars, ...} : fp_sugar) =
      let
        val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (T, fpT) Vartab.empty) [];
        val phi = Morphism.term_morphism "BNF" (Term.subst_TVars rho);
      in
        morph_ctr_sugar phi (nth ctr_sugars index)
      end;

    val ctr_defss = map (of_fp_sugar #ctr_defss) fp_sugars0;
    val mapss = map (of_fp_sugar #mapss) fp_sugars0;
    val ctr_sugars = map2 target_ctr_sugar_of_fp_sugar fpTs fp_sugars0;

    val ctrss = map #ctrs ctr_sugars;
    val ctr_Tss = map (map fastype_of) ctrss;

    val As' = fold (fold Term.add_tfreesT) ctr_Tss [];
    val As = map TFree As';

    val ((Cs, Xs), no_defs_lthy) =
      no_defs_lthy0
      |> fold Variable.declare_typ As
      |> mk_TFrees nn
      ||>> variant_tfrees fp_b_names;

    fun check_call_dead live_call call =
      if null (get_indices call) then () else incompatible_calls live_call call;

    fun freeze_fpTs_simple (T as Type (s, Ts)) =
        (case find_index (curry (op =) T) fpTs of
          ~1 => Type (s, map freeze_fpTs_simple Ts)
        | kk => nth Xs kk)
      | freeze_fpTs_simple T = T;

    fun freeze_fpTs_map (fpT as Type (_, Ts')) (callss, (live_call :: _, dead_calls))
        (T as Type (s, Ts)) =
      if Ts' = Ts then
        nested_self_call live_call
      else
        (List.app (check_call_dead live_call) dead_calls;
         Type (s, map2 (freeze_fpTs fpT) (flatten_type_args_of_bnf (the (bnf_of no_defs_lthy s)) []
           (transpose callss)) Ts))
    and freeze_fpTs fpT calls (T as Type (s, _)) =
        (case map_partition (try (snd o dest_map no_defs_lthy s)) calls of
          ([], _) =>
          (case map_partition (try (snd o dest_abs_or_applied_map no_defs_lthy s)) calls of
            ([], _) => freeze_fpTs_simple T
          | callsp => freeze_fpTs_map fpT callsp T)
        | callsp => freeze_fpTs_map fpT callsp T)
      | freeze_fpTs _ _ T = T;

    val ctr_Tsss = map (map binder_types) ctr_Tss;
    val ctrXs_Tsss = map3 (map2 o map2 o freeze_fpTs) fpTs callssss ctr_Tsss;
    val ctrXs_sum_prod_Ts = map (mk_sumTN_balanced o map HOLogic.mk_tupleT) ctrXs_Tsss;
    val ctr_Ts = map (body_type o hd) ctr_Tss;

    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;

    val fp_eqs = map dest_TFree Xs ~~ ctrXs_sum_prod_Ts;
    val key = key_of_fp_eqs fp fpTs fp_eqs;
  in
    (case n2m_sugar_of no_defs_lthy key of
      SOME n2m_sugar => (n2m_sugar, no_defs_lthy)
    | NONE =>
      let
        val base_fp_names = Name.variant_list [] fp_b_names;
        val fp_bs = map2 (fn b_name => fn base_fp_name =>
            Binding.qualify true b_name (Binding.name (n2mN ^ base_fp_name)))
          b_names base_fp_names;

        val (pre_bnfs, (fp_res as {xtor_co_iterss = xtor_co_iterss0, xtor_co_induct, dtor_injects,
               dtor_ctors, xtor_co_iter_thmss, ...}, lthy)) =
          fp_bnf (construct_mutualized_fp fp fpTs fp_sugars0) fp_bs As' fp_eqs no_defs_lthy;

        val nesting_bnfs = nesty_bnfs lthy ctrXs_Tsss As;
        val nested_bnfs = nesty_bnfs lthy ctrXs_Tsss Xs;

        val ((xtor_co_iterss, iters_args_types, coiters_args_types), _) =
          mk_co_iters_prelims fp ctr_Tsss fpTs Cs ns mss xtor_co_iterss0 lthy;

        fun mk_binding b suf = Binding.suffix_name ("_" ^ suf) b;

        val ((co_iterss, co_iter_defss), lthy) =
          fold_map2 (fn b =>
            (if fp = Least_FP then define_iters [foldN, recN] (the iters_args_types)
             else define_coiters [unfoldN, corecN] (the coiters_args_types))
              (mk_binding b) fpTs Cs) fp_bs xtor_co_iterss lthy
          |>> split_list;

        val ((co_inducts, un_fold_thmss, co_rec_thmss, disc_unfold_thmss, disc_corec_thmss,
              sel_unfold_thmsss, sel_corec_thmsss), fp_sugar_thms) =
          if fp = Least_FP then
            derive_induct_iters_thms_for_types pre_bnfs (the iters_args_types) xtor_co_induct
              xtor_co_iter_thmss nesting_bnfs nested_bnfs fpTs Cs Xs ctrXs_Tsss ctrss ctr_defss
              co_iterss co_iter_defss lthy
            |> `(fn ((_, induct, _), (fold_thmss, rec_thmss, _)) =>
              ([induct], fold_thmss, rec_thmss, [], [], [], []))
            ||> (fn info => (SOME info, NONE))
          else
            derive_coinduct_coiters_thms_for_types pre_bnfs (the coiters_args_types) xtor_co_induct
              dtor_injects dtor_ctors xtor_co_iter_thmss nesting_bnfs fpTs Cs Xs ctrXs_Tsss kss mss
              ns ctr_defss ctr_sugars co_iterss co_iter_defss
              (Proof_Context.export lthy no_defs_lthy) lthy
            |> `(fn ((coinduct_thms_pairs, _), (unfold_thmss, corec_thmss, _),
                    (disc_unfold_thmss, disc_corec_thmss, _), _,
                    (sel_unfold_thmsss, sel_corec_thmsss, _)) =>
              (map snd coinduct_thms_pairs, unfold_thmss, corec_thmss, disc_unfold_thmss,
               disc_corec_thmss, sel_unfold_thmsss, sel_corec_thmsss))
            ||> (fn info => (NONE, SOME info));

        val phi = Proof_Context.export_morphism no_defs_lthy no_defs_lthy0;

        fun mk_target_fp_sugar (kk, T) =
          {T = T, fp = fp, index = kk, pre_bnfs = pre_bnfs, nested_bnfs = nested_bnfs,
           nesting_bnfs = nesting_bnfs, fp_res = fp_res, ctr_defss = ctr_defss,
           ctr_sugars = ctr_sugars, co_iterss = co_iterss, mapss = mapss, co_inducts = co_inducts,
           co_iter_thmsss = transpose [un_fold_thmss, co_rec_thmss],
           disc_co_itersss = transpose [disc_unfold_thmss, disc_corec_thmss],
           sel_co_iterssss = transpose [sel_unfold_thmsss, sel_corec_thmsss]}
          |> morph_fp_sugar phi;

        val n2m_sugar = (map_index mk_target_fp_sugar fpTs, fp_sugar_thms);
      in
        (n2m_sugar, lthy |> register_n2m_sugar key n2m_sugar)
      end)
  end;

fun indexify_callsss fp_sugar callsss =
  let
    val {ctrs, ...} = of_fp_sugar #ctr_sugars fp_sugar;
    fun indexify_ctr ctr =
      (case AList.lookup Term.aconv_untyped callsss ctr of
        NONE => replicate (num_binder_types (fastype_of ctr)) []
      | SOME callss => map (map (Envir.beta_eta_contract o unfold_let)) callss);
  in
    map indexify_ctr ctrs
  end;

fun retypargs tyargs (Type (s, _)) = Type (s, tyargs);

fun fold_subtype_pairs f (T as Type (s, Ts), U as Type (s', Us)) =
    f (T, U) #> (if s = s' then fold (fold_subtype_pairs f) (Ts ~~ Us) else I)
  | fold_subtype_pairs f TU = f TU;

fun nested_to_mutual_fps fp actual_bs actual_Ts get_indices actual_callssss0 lthy =
  let
    val qsoty = quote o Syntax.string_of_typ lthy;
    val qsotys = space_implode " or " o map qsoty;

    fun duplicate_datatype T = error (qsoty T ^ " is not mutually recursive with itself");
    fun not_co_datatype0 T = error (qsoty T ^ " is not a " ^ co_prefix fp ^ "datatype");
    fun not_co_datatype (T as Type (s, _)) =
        if fp = Least_FP andalso
           is_some (Datatype_Data.get_info (Proof_Context.theory_of lthy) s) then
          error (qsoty T ^ " is not a new-style datatype (cf. \"datatype_new\")")
        else
          not_co_datatype0 T
      | not_co_datatype T = not_co_datatype0 T;
    fun not_mutually_nested_rec Ts1 Ts2 =
      error (qsotys Ts1 ^ " is neither mutually recursive with " ^ qsotys Ts2 ^
        " nor nested recursive via " ^ qsotys Ts2);

    val _ = (case Library.duplicates (op =) actual_Ts of [] => () | T :: _ => duplicate_datatype T);

    val perm_actual_Ts =
      sort (prod_ord int_ord Term_Ord.typ_ord o pairself (`Term.size_of_typ)) actual_Ts;

    fun the_ctrs_of (Type (s, Ts)) = map (mk_ctr Ts) (#ctrs (the (ctr_sugar_of lthy s)));

    fun the_fp_sugar_of (T as Type (T_name, _)) =
      (case fp_sugar_of lthy T_name of
        SOME (fp_sugar as {fp = fp', ...}) => if fp = fp' then fp_sugar else not_co_datatype T
      | NONE => not_co_datatype T);

    fun gen_rhss_in gen_Ts rho subTs =
      let
        fun maybe_insert (T, Type (_, gen_tyargs)) =
            if member (op =) subTs T then insert (op =) gen_tyargs else I
          | maybe_insert _ = I;

        val ctrs = maps the_ctrs_of gen_Ts;
        val gen_ctr_Ts = maps (binder_types o fastype_of) ctrs;
        val ctr_Ts = map (Term.typ_subst_atomic rho) gen_ctr_Ts;
      in
        fold (fold_subtype_pairs maybe_insert) (ctr_Ts ~~ gen_ctr_Ts) []
      end;

    fun gather_types _ _ num_groups seen gen_seen [] = (num_groups, seen, gen_seen)
      | gather_types lthy rho num_groups seen gen_seen ((T as Type (_, tyargs)) :: Ts) =
        let
          val {fp_res = {Ts = mutual_Ts0, ...}, ...} = the_fp_sugar_of T;
          val mutual_Ts = map (retypargs tyargs) mutual_Ts0;

          val _ = seen = [] orelse exists (exists_subtype_in seen) mutual_Ts orelse
            not_mutually_nested_rec mutual_Ts seen;

          fun fresh_tyargs () =
            let
              (* The name "'z" is unlikely to clash with the context, yielding more cache hits. *)
              val (gen_tyargs, lthy') =
                variant_tfrees (replicate (length tyargs) "z") lthy
                |>> map Logic.varifyT_global;
              val rho' = (gen_tyargs ~~ tyargs) @ rho;
            in
              (rho', gen_tyargs, gen_seen, lthy')
            end;

          val (rho', gen_tyargs, gen_seen', lthy') =
            if exists (exists_subtype_in seen) mutual_Ts then
              (case gen_rhss_in gen_seen rho mutual_Ts of
                [] => fresh_tyargs ()
              | gen_tyargs :: gen_tyargss_tl =>
                let
                  val unify_pairs = split_list (maps (curry (op ~~) gen_tyargs) gen_tyargss_tl);
                  val mgu = Type.raw_unifys unify_pairs Vartab.empty;
                  val gen_tyargs' = map (Envir.subst_type mgu) gen_tyargs;
                  val gen_seen' = map (Envir.subst_type mgu) gen_seen;
                in
                  (rho, gen_tyargs', gen_seen', lthy)
                end)
            else
              fresh_tyargs ();

          val gen_mutual_Ts = map (retypargs gen_tyargs) mutual_Ts0;
          val Ts' = filter_out (member (op =) mutual_Ts) Ts;
        in
          gather_types lthy' rho' (num_groups + 1) (seen @ mutual_Ts) (gen_seen' @ gen_mutual_Ts)
            Ts'
        end
      | gather_types _ _ _ _ _ (T :: _) = not_co_datatype T;

    val (num_groups, perm_Ts, perm_gen_Ts) = gather_types lthy [] 0 [] [] perm_actual_Ts;
    val perm_frozen_gen_Ts = map Logic.unvarifyT_global perm_gen_Ts;

    val missing_Ts = perm_Ts |> subtract (op =) actual_Ts;
    val Ts = actual_Ts @ missing_Ts;

    val nn = length Ts;
    val kks = 0 upto nn - 1;

    val callssss0 = pad_list [] nn actual_callssss0;

    val common_name = mk_common_name (map Binding.name_of actual_bs);
    val bs = pad_list (Binding.name common_name) nn actual_bs;

    fun permute xs = permute_like (op =) Ts perm_Ts xs;
    fun unpermute perm_xs = permute_like (op =) perm_Ts Ts perm_xs;

    val perm_bs = permute bs;
    val perm_kks = permute kks;
    val perm_callssss0 = permute callssss0;
    val perm_fp_sugars0 = map (the o fp_sugar_of lthy o fst o dest_Type) perm_Ts;

    val perm_callssss = map2 indexify_callsss perm_fp_sugars0 perm_callssss0;

    val get_perm_indices = map (fn kk => find_index (curry (op =) kk) perm_kks) o get_indices;

    val ((perm_fp_sugars, fp_sugar_thms), lthy) =
      if num_groups > 1 then
        mutualize_fp_sugars fp perm_bs perm_frozen_gen_Ts get_perm_indices perm_callssss
          perm_fp_sugars0 lthy
      else
        ((perm_fp_sugars0, (NONE, NONE)), lthy);

    val fp_sugars = unpermute perm_fp_sugars;
  in
    ((missing_Ts, perm_kks, fp_sugars, fp_sugar_thms), lthy)
  end;

end;
