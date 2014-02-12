(*  Title:      HOL/Tools/BNF/bnf_fp_n2m.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Flattening of nested to mutual (co)recursion.
*)

signature BNF_FP_N2M =
sig
  val construct_mutualized_fp: BNF_FP_Util.fp_kind  -> typ list -> BNF_FP_Def_Sugar.fp_sugar list ->
    binding list -> (string * sort) list -> typ list * typ list list -> BNF_Def.bnf list ->
    local_theory -> BNF_FP_Util.fp_result * local_theory
end;

structure BNF_FP_N2M : BNF_FP_N2M =
struct

open BNF_Def
open BNF_Util
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_Tactics
open BNF_FP_N2M_Tactics

fun force_typ ctxt T =
  map_types Type_Infer.paramify_vars
  #> Type.constraint T
  #> Syntax.check_term ctxt
  #> singleton (Variable.polymorphic ctxt);

fun mk_prod_map f g =
  let
    val ((fAT, fBT), fT) = `dest_funT (fastype_of f);
    val ((gAT, gBT), gT) = `dest_funT (fastype_of g);
  in
    Const (@{const_name map_pair},
      fT --> gT --> HOLogic.mk_prodT (fAT, gAT) --> HOLogic.mk_prodT (fBT, gBT)) $ f $ g
  end;

fun mk_sum_map f g =
  let
    val ((fAT, fBT), fT) = `dest_funT (fastype_of f);
    val ((gAT, gBT), gT) = `dest_funT (fastype_of g);
  in
    Const (@{const_name sum_map}, fT --> gT --> mk_sumT (fAT, gAT) --> mk_sumT (fBT, gBT)) $ f $ g
  end;

fun construct_mutualized_fp fp fpTs fp_sugars bs resBs (resDs, Dss) bnfs lthy =
  let
    fun steal get = map (of_fp_sugar (get o #fp_res)) fp_sugars;

    val n = length bnfs;
    val deads = fold (union (op =)) Dss resDs;
    val As = subtract (op =) deads (map TFree resBs);
    val names_lthy = fold Variable.declare_typ (As @ deads) lthy;
    val m = length As;
    val live = m + n;
    val ((Xs, Bs), names_lthy) = names_lthy
      |> mk_TFrees n
      ||>> mk_TFrees m;
    val allAs = As @ Xs;
    val phiTs = map2 mk_pred2T As Bs;
    val theta = As ~~ Bs;
    val fpTs' = map (Term.typ_subst_atomic theta) fpTs;
    val pre_phiTs = map2 mk_pred2T fpTs fpTs';

    fun mk_co_algT T U = fp_case fp (T --> U) (U --> T);
    fun co_swap pair = fp_case fp I swap pair;
    val dest_co_algT = co_swap o dest_funT;
    val co_alg_argT = fp_case fp range_type domain_type;
    val co_alg_funT = fp_case fp domain_type range_type;
    val mk_co_product = curry (fp_case fp mk_convol mk_case_sum);
    val mk_map_co_product = fp_case fp mk_prod_map mk_sum_map;
    val co_proj1_const = fp_case fp (fst_const o fst) (uncurry Inl_const o dest_sumT o snd);
    val mk_co_productT = curry (fp_case fp HOLogic.mk_prodT mk_sumT);
    val dest_co_productT = fp_case fp HOLogic.dest_prodT dest_sumT;

    val ((ctors, dtors), (xtor's, xtors)) =
      let
        val ctors = map2 (force_typ names_lthy o (fn T => dummyT --> T)) fpTs (steal #ctors);
        val dtors = map2 (force_typ names_lthy o (fn T => T --> dummyT)) fpTs (steal #dtors);
      in
        ((ctors, dtors), `(map (Term.subst_atomic_types theta)) (fp_case fp ctors dtors))
      end;

    val xTs = map (domain_type o fastype_of) xtors;
    val yTs = map (domain_type o fastype_of) xtor's;

    val (((((phis, phis'), pre_phis), xs), ys), names_lthy) = names_lthy
      |> mk_Frees' "R" phiTs
      ||>> mk_Frees "S" pre_phiTs
      ||>> mk_Frees "x" xTs
      ||>> mk_Frees "y" yTs;

    val fp_bnfs = steal #bnfs;
    val pre_bnfs = map (of_fp_sugar #pre_bnfs) fp_sugars;
    val pre_bnfss = map #pre_bnfs fp_sugars;
    val nesty_bnfss = map (fn sugar => #nested_bnfs sugar @ #nesting_bnfs sugar) fp_sugars;
    val fp_nesty_bnfss = fp_bnfs :: nesty_bnfss;
    val fp_nesty_bnfs = distinct (op = o pairself T_of_bnf) (flat fp_nesty_bnfss);

    val rels =
      let
        fun find_rel T As Bs = fp_nesty_bnfss
          |> map (filter_out (curry (op = o pairself name_of_bnf) BNF_Comp.DEADID_bnf))
          |> get_first (find_first (fn bnf => Type.could_unify (T_of_bnf bnf, T)))
          |> Option.map (fn bnf =>
            let val live = live_of_bnf bnf;
            in (mk_rel live As Bs (rel_of_bnf bnf), live) end)
          |> the_default (HOLogic.eq_const T, 0);

        fun mk_rel (T as Type (_, Ts)) (Type (_, Us)) =
              let
                val (rel, live) = find_rel T Ts Us;
                val (Ts', Us') = fastype_of rel |> strip_typeN live |> fst |> map_split dest_pred2T;
                val rels = map2 mk_rel Ts' Us';
              in
                Term.list_comb (rel, rels)
              end
          | mk_rel (T as TFree _) _ = (nth phis (find_index (curry op = T) As)
              handle General.Subscript => HOLogic.eq_const T)
          | mk_rel _ _ = raise Fail "fpTs contains schematic type variables";
      in
        map2 (fold_rev Term.absfree phis' oo mk_rel) fpTs fpTs'
      end;

    val pre_rels = map2 (fn Ds => mk_rel_of_bnf Ds (As @ fpTs) (Bs @ fpTs')) Dss bnfs;

    val rel_unfoldss = map (maps (fn bnf => no_refl [rel_def_of_bnf bnf])) pre_bnfss;
    val rel_xtor_co_inducts = steal (split_conj_thm o #rel_xtor_co_induct_thm)
      |> map2 (fn unfs => unfold_thms lthy (id_apply :: unfs)) rel_unfoldss;

    val rel_defs = map rel_def_of_bnf bnfs;
    val rel_monos = map rel_mono_of_bnf bnfs;

    val rel_xtor_co_induct_thm =
      mk_rel_xtor_co_induct_thm fp pre_rels pre_phis rels phis xs ys xtors xtor's
        (mk_rel_xtor_co_induct_tactic fp rel_xtor_co_inducts rel_defs rel_monos) lthy;

    val rel_eqs = no_refl (map rel_eq_of_bnf fp_nesty_bnfs);
    val map_id0s = no_refl (map map_id0_of_bnf bnfs);

    val xtor_co_induct_thm =
      (case fp of
        Least_FP =>
          let
            val (Ps, names_lthy) = names_lthy
              |> mk_Frees "P" (map (fn T => T --> HOLogic.boolT) fpTs);
            fun mk_Grp_id P =
              let val T = domain_type (fastype_of P);
              in mk_Grp (HOLogic.Collect_const T $ P) (HOLogic.id_const T) end;
            val cts = map (SOME o certify lthy) (map HOLogic.eq_const As @ map mk_Grp_id Ps);
          in
            cterm_instantiate_pos cts rel_xtor_co_induct_thm
            |> singleton (Proof_Context.export names_lthy lthy)
            |> unfold_thms lthy (@{thms eq_le_Grp_id_iff all_simps(1,2)[symmetric]} @ rel_eqs)
            |> funpow n (fn thm => thm RS spec)
            |> unfold_thms lthy (@{thm eq_alt} :: map rel_Grp_of_bnf bnfs @ map_id0s)
            |> unfold_thms lthy @{thms Grp_id_mono_subst eqTrueI[OF subset_UNIV] simp_thms(22)}
            |> unfold_thms lthy @{thms subset_iff mem_Collect_eq
               atomize_conjL[symmetric] atomize_all[symmetric] atomize_imp[symmetric]}
            |> unfold_thms lthy (maps set_defs_of_bnf bnfs)
          end
      | Greatest_FP =>
          let
            val cts = NONE :: map (SOME o certify lthy) (map HOLogic.eq_const As);
          in
            cterm_instantiate_pos cts rel_xtor_co_induct_thm
            |> unfold_thms lthy (@{thms le_fun_def le_bool_def all_simps(1,2)[symmetric]} @ rel_eqs)
            |> funpow (2 * n) (fn thm => thm RS spec)
            |> Conv.fconv_rule (Object_Logic.atomize lthy)
            |> funpow n (fn thm => thm RS mp)
          end);

    val fold_preTs = map2 (fn Ds => mk_T_of_bnf Ds allAs) Dss bnfs;
    val fold_pre_deads_only_Ts = map2 (fn Ds => mk_T_of_bnf Ds (replicate live dummyT)) Dss bnfs;
    val rec_theta = Xs ~~ map2 mk_co_productT fpTs Xs;
    val rec_preTs = map (Term.typ_subst_atomic rec_theta) fold_preTs;

    val fold_strTs = map2 mk_co_algT fold_preTs Xs;
    val rec_strTs = map2 mk_co_algT rec_preTs Xs;
    val resTs = map2 mk_co_algT fpTs Xs;

    val (((fold_strs, fold_strs'), (rec_strs, rec_strs')), names_lthy) = names_lthy
      |> mk_Frees' "s" fold_strTs
      ||>> mk_Frees' "s" rec_strTs;

    val co_iters = steal #xtor_co_iterss;
    val ns = map (length o #pre_bnfs) fp_sugars;
    fun substT rho (Type (@{type_name "fun"}, [T, U])) = substT rho T --> substT rho U
      | substT rho (Type (s, Ts)) = Type (s, map (typ_subst_nonatomic rho) Ts)
      | substT _ T = T;
    fun force_iter is_rec i TU TU_rec raw_iters =
      let
        val approx_fold = un_fold_of raw_iters
          |> force_typ names_lthy
            (replicate (nth ns i) dummyT ---> (if is_rec then TU_rec else TU));
        val TUs = binder_fun_types (Term.typ_subst_atomic (Xs ~~ fpTs) (fastype_of approx_fold));
        val js = find_indices Type.could_unify
          TUs (map (Term.typ_subst_atomic (Xs ~~ fpTs)) fold_strTs);
        val Tpats = map (fn j => mk_co_algT (nth fold_pre_deads_only_Ts j) (nth Xs j)) js;
        val iter = raw_iters |> (if is_rec then co_rec_of else un_fold_of);
      in
        force_typ names_lthy (Tpats ---> TU) iter
      end;

    fun mk_iter b_opt is_rec iters lthy TU =
      let
        val x = co_alg_argT TU;
        val i = find_index (fn T => x = T) Xs;
        val TUiter =
          (case find_first (fn f => body_fun_type (fastype_of f) = TU) iters of
            NONE => nth co_iters i
              |> force_iter is_rec i
                (TU |> (is_none b_opt andalso not is_rec) ? substT (fpTs ~~ Xs))
                (TU |> (is_none b_opt) ? substT (map2 mk_co_productT fpTs Xs ~~ Xs))
          | SOME f => f);
        val TUs = binder_fun_types (fastype_of TUiter);
        val iter_preTs = if is_rec then rec_preTs else fold_preTs;
        val iter_strs = if is_rec then rec_strs else fold_strs;
        fun mk_s TU' =
          let
            val i = find_index (fn T => co_alg_argT TU' = T) Xs;
            val sF = co_alg_funT TU';
            val F = nth iter_preTs i;
            val s = nth iter_strs i;
          in
            (if sF = F then s
            else
              let
                val smapT = replicate live dummyT ---> mk_co_algT sF F;
                fun hidden_to_unit t =
                  Term.subst_TVars (map (rpair HOLogic.unitT) (Term.add_tvar_names t [])) t;
                val smap = map_of_bnf (nth bnfs i)
                  |> force_typ names_lthy smapT
                  |> hidden_to_unit;
                val smap_argTs = strip_typeN live (fastype_of smap) |> fst;
                fun mk_smap_arg TU =
                  (if domain_type TU = range_type TU then
                    HOLogic.id_const (domain_type TU)
                  else if is_rec then
                    let
                      val (TY, (U, X)) = TU |> dest_co_algT ||> dest_co_productT;
                      val T = mk_co_algT TY U;
                    in
                      (case try (force_typ lthy T o build_map lthy co_proj1_const o dest_funT) T of
                        SOME f => mk_co_product f
                          (fst (fst (mk_iter NONE is_rec iters lthy (mk_co_algT TY X))))
                      | NONE => mk_map_co_product
                          (build_map lthy co_proj1_const
                            (dest_funT (mk_co_algT (dest_co_productT TY |> fst) U)))
                          (HOLogic.id_const X))
                    end
                  else
                    fst (fst (mk_iter NONE is_rec iters lthy TU)))
                val smap_args = map mk_smap_arg smap_argTs;
              in
                HOLogic.mk_comp (co_swap (s, Term.list_comb (smap, smap_args)))
              end)
          end;
        val t = Term.list_comb (TUiter, map mk_s TUs);
      in
        (case b_opt of
          NONE => ((t, Drule.dummy_thm), lthy)
        | SOME b => Local_Theory.define ((b, NoSyn), ((Binding.conceal (Thm.def_binding b), []),
            fold_rev Term.absfree (if is_rec then rec_strs' else fold_strs') t)) lthy |>> apsnd snd)
      end;

    fun mk_iters is_rec name lthy =
      fold2 (fn TU => fn b => fn ((iters, defs), lthy) =>
        mk_iter (SOME b) is_rec iters lthy TU |>> (fn (f, d) => (f :: iters, d :: defs)))
      resTs (map (Binding.suffix_name ("_" ^ name)) bs) (([], []), lthy)
      |>> apfst rev o apsnd rev;
    val foldN = fp_case fp ctor_foldN dtor_unfoldN;
    val recN = fp_case fp ctor_recN dtor_corecN;
    val (((raw_un_folds, raw_un_fold_defs), (raw_co_recs, raw_co_rec_defs)), (lthy, raw_lthy)) =
      lthy
      |> mk_iters false foldN
      ||>> mk_iters true recN
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism raw_lthy lthy;

    val un_folds = map (Morphism.term phi) raw_un_folds;
    val co_recs = map (Morphism.term phi) raw_co_recs;

    val (xtor_un_fold_thms, xtor_co_rec_thms) =
      let
        val folds = map (fn f => Term.list_comb (f, fold_strs)) raw_un_folds;
        val recs = map (fn r => Term.list_comb (r, rec_strs)) raw_co_recs;
        val fold_mapTs = co_swap (As @ fpTs, As @ Xs);
        val rec_mapTs = co_swap (As @ fpTs, As @ map2 mk_co_productT fpTs Xs);
        val pre_fold_maps =
          map2 (fn Ds => fn bnf =>
            Term.list_comb (uncurry (mk_map_of_bnf Ds) fold_mapTs bnf,
              map HOLogic.id_const As @ folds))
          Dss bnfs;
        val pre_rec_maps =
          map2 (fn Ds => fn bnf =>
            Term.list_comb (uncurry (mk_map_of_bnf Ds) rec_mapTs bnf,
              map HOLogic.id_const As @ map2 (mk_co_product o HOLogic.id_const) fpTs recs))
          Dss bnfs;

        fun mk_goals f xtor s smap =
          ((f, xtor), (s, smap))
          |> pairself (HOLogic.mk_comp o co_swap)
          |> HOLogic.mk_eq;

        val fold_goals = map4 mk_goals folds xtors fold_strs pre_fold_maps
        val rec_goals = map4 mk_goals recs xtors rec_strs pre_rec_maps;

        fun mk_thms ss goals tac =
          Library.foldr1 HOLogic.mk_conj goals
          |> HOLogic.mk_Trueprop
          |> fold_rev Logic.all ss
          |> (fn goal => Goal.prove_sorry raw_lthy [] [] goal tac)
          |> Thm.close_derivation
          |> Morphism.thm phi
          |> split_conj_thm
          |> map (fn thm => thm RS @{thm comp_eq_dest});

        val pre_map_defs = no_refl (map map_def_of_bnf bnfs);
        val fp_pre_map_defs = no_refl (map map_def_of_bnf pre_bnfs);

        val map_unfoldss = map (maps (fn bnf => no_refl [map_def_of_bnf bnf])) pre_bnfss;
        val unfold_map = map2 (fn unfs => unfold_thms lthy (id_apply :: unfs)) map_unfoldss;

        val fp_xtor_co_iterss = steal #xtor_co_iter_thmss;
        val fp_xtor_un_folds = map (mk_pointfree lthy o un_fold_of) fp_xtor_co_iterss |> unfold_map;
        val fp_xtor_co_recs = map (mk_pointfree lthy o co_rec_of) fp_xtor_co_iterss |> unfold_map;

        val fp_co_iter_o_mapss = steal #xtor_co_iter_o_map_thmss;
        val fp_fold_o_maps = map un_fold_of fp_co_iter_o_mapss |> unfold_map;
        val fp_rec_o_maps = map co_rec_of fp_co_iter_o_mapss |> unfold_map;
        val fold_thms = fp_case fp @{thm comp_assoc} @{thm comp_assoc[symmetric]} :: @{thms id_apply
          o_apply comp_id id_comp map_pair.comp map_pair.id sum_map.comp sum_map.id};
        val rec_thms = fold_thms @ fp_case fp
          @{thms fst_convol map_pair_o_convol convol_o}
          @{thms case_sum_o_inj(1) case_sum_o_sum_map o_case_sum};
        val map_thms = no_refl (maps (fn bnf =>
          [map_comp0_of_bnf bnf RS sym, map_id0_of_bnf bnf]) fp_nesty_bnfs);

        fun mk_tac defs o_map_thms xtor_thms thms {context = ctxt, prems = _} =
          unfold_thms_tac ctxt
            (flat [thms, defs, pre_map_defs, fp_pre_map_defs, xtor_thms, o_map_thms, map_thms]) THEN
          CONJ_WRAP (K (HEADGOAL (rtac refl))) bnfs;

        val fold_tac = mk_tac raw_un_fold_defs fp_fold_o_maps fp_xtor_un_folds fold_thms;
        val rec_tac = mk_tac raw_co_rec_defs fp_rec_o_maps fp_xtor_co_recs rec_thms;
      in
        (mk_thms fold_strs fold_goals fold_tac, mk_thms rec_strs rec_goals rec_tac)
      end;

    (* These results are half broken. This is deliberate. We care only about those fields that are
       used by "primrec_new", "primcorecursive", and "datatype_new_compat". *)
    val fp_res =
      ({Ts = fpTs,
        bnfs = steal #bnfs,
        dtors = dtors,
        ctors = ctors,
        xtor_co_iterss = transpose [un_folds, co_recs],
        xtor_co_induct = xtor_co_induct_thm,
        dtor_ctors = steal #dtor_ctors (*too general types*),
        ctor_dtors = steal #ctor_dtors (*too general types*),
        ctor_injects = steal #ctor_injects (*too general types*),
        dtor_injects = steal #dtor_injects (*too general types*),
        xtor_map_thms = steal #xtor_map_thms (*too general types and terms*),
        xtor_set_thmss = steal #xtor_set_thmss (*too general types and terms*),
        xtor_rel_thms = steal #xtor_rel_thms (*too general types and terms*),
        xtor_co_iter_thmss = transpose [xtor_un_fold_thms, xtor_co_rec_thms],
        xtor_co_iter_o_map_thmss = steal #xtor_co_iter_o_map_thmss (*theorem about old constant*),
        rel_xtor_co_induct_thm = rel_xtor_co_induct_thm}
       |> morph_fp_result (Morphism.term_morphism "BNF" (singleton (Variable.polymorphic lthy))));
  in
    (fp_res, lthy)
  end;

end;
