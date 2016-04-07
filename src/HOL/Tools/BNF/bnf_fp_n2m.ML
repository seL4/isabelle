(*  Title:      HOL/Tools/BNF/bnf_fp_n2m.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Flattening of nested to mutual (co)recursion.
*)

signature BNF_FP_N2M =
sig
  val construct_mutualized_fp: BNF_Util.fp_kind -> int list -> typ list ->
    (int * BNF_FP_Util.fp_result) list -> binding list -> (string * sort) list ->
    typ list * typ list list -> BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory ->
    BNF_FP_Util.fp_result * local_theory
end;

structure BNF_FP_N2M : BNF_FP_N2M =
struct

open BNF_Def
open BNF_Util
open BNF_Comp
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_Tactics
open BNF_FP_N2M_Tactics

fun mk_prod_map f g =
  let
    val ((fAT, fBT), fT) = `dest_funT (fastype_of f);
    val ((gAT, gBT), gT) = `dest_funT (fastype_of g);
  in
    Const (@{const_name map_prod},
      fT --> gT --> HOLogic.mk_prodT (fAT, gAT) --> HOLogic.mk_prodT (fBT, gBT)) $ f $ g
  end;

fun mk_map_sum f g =
  let
    val ((fAT, fBT), fT) = `dest_funT (fastype_of f);
    val ((gAT, gBT), gT) = `dest_funT (fastype_of g);
  in
    Const (@{const_name map_sum}, fT --> gT --> mk_sumT (fAT, gAT) --> mk_sumT (fBT, gBT)) $ f $ g
  end;

fun construct_mutualized_fp fp flat_mutual_cliques fpTs indexed_fp_ress bs resBs (resDs, Dss) bnfs
    (absT_infos : absT_info list) lthy =
  let
    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    val b_names = map Binding.name_of bs;
    val b_name = mk_common_name b_names;
    val b = Binding.name b_name;

    fun of_fp_res get = map (uncurry nth o swap o apsnd get) indexed_fp_ress;
    fun mk_co_algT T U = case_fp fp (T --> U) (U --> T);
    fun co_swap pair = case_fp fp I swap pair;
    val mk_co_comp = HOLogic.mk_comp o co_swap;
    val co_productC = case_fp fp @{type_name prod} @{type_name sum};

    val dest_co_algT = co_swap o dest_funT;
    val co_alg_argT = case_fp fp range_type domain_type;
    val co_alg_funT = case_fp fp domain_type range_type;
    val mk_co_product = curry (case_fp fp mk_convol mk_case_sum);
    val mk_map_co_product = case_fp fp mk_prod_map mk_map_sum;
    val co_proj1_const = case_fp fp (fst_const o fst) (uncurry Inl_const o dest_sumT o snd);
    val mk_co_productT = curry (case_fp fp HOLogic.mk_prodT mk_sumT);
    val dest_co_productT = case_fp fp HOLogic.dest_prodT dest_sumT;
    val rewrite_comp_comp = case_fp fp @{thm rewriteL_comp_comp} @{thm rewriteR_comp_comp};

    val fp_absT_infos = of_fp_res #absT_infos;
    val fp_bnfs = of_fp_res #bnfs;
    val pre_bnfs = of_fp_res #pre_bnfs;

    val fp_absTs = map #absT fp_absT_infos;
    val fp_repTs = map #repT fp_absT_infos;
    val fp_abss = map #abs fp_absT_infos;
    val fp_reps = map #rep fp_absT_infos;
    val fp_type_definitions = map #type_definition fp_absT_infos;

    val absTs = map #absT absT_infos;
    val repTs = map #repT absT_infos;
    val absTs' = map (Logic.type_map (singleton (Variable.polymorphic lthy))) absTs;
    val repTs' = map (Logic.type_map (singleton (Variable.polymorphic lthy))) repTs;
    val abss = map #abs absT_infos;
    val reps = map #rep absT_infos;
    val abs_inverses = map #abs_inverse absT_infos;
    val type_definitions = map #type_definition absT_infos;

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
    val allBs = Bs @ Xs;
    val phiTs = map2 mk_pred2T As Bs;
    val thetaBs = As ~~ Bs;
    val fpTs' = map (Term.typ_subst_atomic thetaBs) fpTs;
    val fold_thetaAs = Xs ~~ fpTs;
    val fold_thetaBs = Xs ~~ fpTs';
    val rec_theta = Xs ~~ map2 mk_co_productT fpTs Xs;
    val pre_phiTs = map2 mk_pred2T fpTs fpTs';

    val ((ctors, dtors), (xtor's, xtors)) =
      let
        val ctors = map2 (force_typ names_lthy o (fn T => dummyT --> T)) fpTs (of_fp_res #ctors);
        val dtors = map2 (force_typ names_lthy o (fn T => T --> dummyT)) fpTs (of_fp_res #dtors);
      in
        ((ctors, dtors), `(map (Term.subst_atomic_types thetaBs)) (case_fp fp ctors dtors))
      end;

    val absATs = map (domain_type o fastype_of) ctors;
    val absBTs = map (Term.typ_subst_atomic thetaBs) absATs;
    val xTs = map (domain_type o fastype_of) xtors;
    val yTs = map (domain_type o fastype_of) xtor's;

    val absAs = @{map 3} (fn Ds => mk_abs o mk_T_of_bnf Ds allAs) Dss bnfs abss;
    val absBs = @{map 3} (fn Ds => mk_abs o mk_T_of_bnf Ds allBs) Dss bnfs abss;
    val fp_repAs = map2 mk_rep absATs fp_reps;
    val fp_repBs = map2 mk_rep absBTs fp_reps;

    val typ_subst_nonatomic_sorted = fold_rev (typ_subst_nonatomic o single);
    val sorted_theta = sort (int_ord o apply2 (Term.size_of_typ o fst)) (fpTs ~~ Xs)
    val sorted_fpTs = map fst sorted_theta;

    val nesting_bnfs = nesting_bnfs lthy
      [[map (typ_subst_nonatomic_sorted (rev sorted_theta) o range_type o fastype_of) fp_repAs]]
      allAs;
    val fp_or_nesting_bnfs = distinct (op = o apply2 T_of_bnf) (fp_bnfs @ nesting_bnfs);

    val (((((phis, phis'), pre_phis), xs), ys), names_lthy) = names_lthy
      |> mk_Frees' "R" phiTs
      ||>> mk_Frees "S" pre_phiTs
      ||>> mk_Frees "x" xTs
      ||>> mk_Frees "y" yTs;

    val rels =
      let
        fun find_rel T As Bs = fp_or_nesting_bnfs
          |> filter_out (curry (op = o apply2 name_of_bnf) BNF_Comp.DEADID_bnf)
          |> find_first (fn bnf => Type.could_unify (T_of_bnf bnf, T))
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

    val rel_unfolds = maps (no_refl o single o rel_def_of_bnf) pre_bnfs;
    val rel_xtor_co_inducts = of_fp_res (split_conj_thm o #xtor_rel_co_induct)
      |> map (zero_var_indexes o unfold_thms lthy (id_apply :: rel_unfolds));

    val rel_defs = map rel_def_of_bnf bnfs;
    val rel_monos = map rel_mono_of_bnf bnfs;

    fun cast castA castB pre_rel =
      let
        val castAB = mk_vimage2p (Term.subst_atomic_types fold_thetaAs castA)
          (Term.subst_atomic_types fold_thetaBs castB);
      in
        fold_rev (fold_rev Term.absdummy) [phiTs, pre_phiTs]
          (castAB $ Term.list_comb (pre_rel, map Bound (live - 1 downto 0)))
      end;

    val castAs = map2 (curry HOLogic.mk_comp) absAs fp_repAs;
    val castBs = map2 (curry HOLogic.mk_comp) absBs fp_repBs;

    val fp_or_nesting_rel_eqs = no_refl (map rel_eq_of_bnf fp_or_nesting_bnfs);
    val fp_or_nesting_rel_monos = map rel_mono_of_bnf fp_or_nesting_bnfs;

    val rel_xtor_co_inducts_inst =
      let
        val extract =
          case_fp fp (snd o Term.dest_comb) (snd o Term.dest_comb o fst o Term.dest_comb);
        val raw_phis = map (extract o HOLogic.dest_Trueprop o Thm.concl_of) rel_xtor_co_inducts;
        val thetas =
          AList.group (op =)
            (flat_mutual_cliques ~~
              map (fn (t, u) => (#1 (dest_Var t), Thm.cterm_of lthy u)) (raw_phis ~~ pre_phis));
      in
        map2 (infer_instantiate lthy o the o AList.lookup (op =) thetas)
        flat_mutual_cliques rel_xtor_co_inducts
      end

    val xtor_rel_co_induct =
      mk_xtor_rel_co_induct_thm fp (@{map 3} cast castAs castBs pre_rels) pre_phis rels phis xs ys
        xtors xtor's (mk_rel_xtor_co_induct_tactic fp abs_inverses rel_xtor_co_inducts_inst rel_defs
          rel_monos fp_or_nesting_rel_eqs fp_or_nesting_rel_monos)
        lthy;

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
            val cts =
              map (SOME o Thm.cterm_of names_lthy) (map HOLogic.eq_const As @ map mk_Grp_id Ps);
            fun mk_fp_type_copy_thms thm = map (curry op RS thm)
              @{thms type_copy_Abs_o_Rep type_copy_vimage2p_Grp_Rep};
            fun mk_type_copy_thms thm = map (curry op RS thm)
              @{thms type_copy_Rep_o_Abs type_copy_vimage2p_Grp_Abs};
          in
            infer_instantiate' names_lthy cts xtor_rel_co_induct
            |> singleton (Proof_Context.export names_lthy lthy)
            |> unfold_thms lthy (@{thms eq_le_Grp_id_iff all_simps(1,2)[symmetric]} @
                fp_or_nesting_rel_eqs)
            |> funpow n (fn thm => thm RS spec)
            |> unfold_thms lthy (@{thm eq_alt} :: map rel_Grp_of_bnf bnfs @ map_id0s)
            |> unfold_thms lthy (@{thms vimage2p_id vimage2p_comp comp_apply comp_id
               Grp_id_mono_subst eqTrueI[OF subset_UNIV] simp_thms(22)} @
               maps mk_fp_type_copy_thms fp_type_definitions @
               maps mk_type_copy_thms type_definitions)
            |> unfold_thms lthy @{thms subset_iff mem_Collect_eq
               atomize_conjL[symmetric] atomize_all[symmetric] atomize_imp[symmetric]}
          end
      | Greatest_FP =>
          let
            val cts = NONE :: map (SOME o Thm.cterm_of lthy) (map HOLogic.eq_const As);
          in
            infer_instantiate' lthy cts xtor_rel_co_induct
            |> unfold_thms lthy (@{thms le_fun_def le_bool_def all_simps(1,2)[symmetric]} @
                fp_or_nesting_rel_eqs)
            |> funpow (2 * n) (fn thm => thm RS spec)
            |> Conv.fconv_rule (Object_Logic.atomize lthy)
            |> funpow n (fn thm => thm RS mp)
          end);

    val timer = time (timer "Nested-to-mutual (co)induction");

    val fold_preTs = map2 (fn Ds => mk_T_of_bnf Ds allAs) Dss bnfs;
    val rec_preTs = map (Term.typ_subst_atomic rec_theta) fold_preTs;

    val rec_strTs = map2 mk_co_algT rec_preTs Xs;
    val resTs = map2 mk_co_algT fpTs Xs;

    val ((rec_strs, rec_strs'), names_lthy) = names_lthy
      |> mk_Frees' "s" rec_strTs;

    val xtor_co_recs = of_fp_res #xtor_co_recs;
    val ns = map (length o #Ts o snd) indexed_fp_ress;

    fun foldT_of_recT recT =
      let
        val ((FTXs, Ys), TX) = strip_fun_type recT |>> map_split dest_co_algT;
        val Zs = union op = Xs Ys;
        fun subst (Type (C, Ts as [_, X])) =
            if C = co_productC andalso member op = Zs X then X else Type (C, map subst Ts)
          | subst (Type (C, Ts)) = Type (C, map subst Ts)
          | subst T = T;
      in
        map2 (mk_co_algT o subst) FTXs Ys ---> TX
      end;

    fun force_rec i TU raw_rec =
      let
        val thy = Proof_Context.theory_of lthy;

        val approx_rec = raw_rec
          |> force_typ names_lthy (replicate (nth ns i) dummyT ---> TU);
        val subst = Term.typ_subst_atomic fold_thetaAs;

        fun mk_fp_absT_repT fp_repT fp_absT = mk_absT thy fp_repT fp_absT ooo mk_repT;
        val mk_fp_absT_repTs = @{map 5} mk_fp_absT_repT fp_repTs fp_absTs absTs repTs;

        val fold_preTs' = mk_fp_absT_repTs (map subst fold_preTs);

        val fold_pre_deads_only_Ts =
          map (typ_subst_nonatomic_sorted (map (rpair dummyT) (As @ sorted_fpTs))) fold_preTs';

        val (mutual_clique, TUs) =
          map_split dest_co_algT (binder_fun_types (foldT_of_recT (fastype_of approx_rec)))
          |>> map subst
          |> `(fn (_, Ys) => nth flat_mutual_cliques
            (find_index (fn X => X = the (find_first (can dest_TFree) Ys)) Xs))
          ||> uncurry (map2 mk_co_algT);
        val cands = flat_mutual_cliques ~~ map2 mk_co_algT fold_preTs' Xs;
        val js = find_indices (fn ((cl, cand), TU) =>
          cl = mutual_clique andalso Type.could_unify (TU, cand)) TUs cands;
        val Tpats = map (fn j => mk_co_algT (nth fold_pre_deads_only_Ts j) (nth Xs j)) js;
      in
        force_typ names_lthy (Tpats ---> TU) raw_rec
      end;

    fun mk_co_comp_abs_rep fp_absT absT fp_abs fp_rep abs rep t =
      case_fp fp (HOLogic.mk_comp (HOLogic.mk_comp (t, mk_abs absT abs), mk_rep fp_absT fp_rep))
        (HOLogic.mk_comp (mk_abs fp_absT fp_abs, HOLogic.mk_comp (mk_rep absT rep, t)));

    fun mk_rec b_opt recs lthy TU =
      let
        val thy = Proof_Context.theory_of lthy;

        val x = co_alg_argT TU;
        val i = find_index (fn T => x = T) Xs;
        val TUrec =
          (case find_first (fn f => body_fun_type (fastype_of f) = TU) recs of
            NONE => force_rec i TU (nth xtor_co_recs i)
          | SOME f => f);

        val TUs = binder_fun_types (fastype_of TUrec);

        fun mk_s TU' =
          let
            fun mk_absT_fp_repT repT absT = mk_absT thy repT absT ooo mk_repT;

            val i = find_index (fn T => co_alg_argT TU' = T) Xs;
            val fp_abs = nth fp_abss i;
            val fp_rep = nth fp_reps i;
            val abs = nth abss i;
            val rep = nth reps i;
            val sF = co_alg_funT TU';
            val sF' =
              mk_absT_fp_repT (nth repTs' i) (nth absTs' i) (nth fp_absTs i) (nth fp_repTs i) sF
                handle Term.TYPE _ => sF;
            val F = nth rec_preTs i;
            val s = nth rec_strs i;
          in
            if sF = F then s
            else if sF' = F then mk_co_comp_abs_rep sF sF' fp_abs fp_rep abs rep s
            else
              let
                val smapT = replicate live dummyT ---> mk_co_algT sF' F;
                fun hidden_to_unit t =
                  Term.subst_TVars (map (rpair HOLogic.unitT) (Term.add_tvar_names t [])) t;
                val smap = map_of_bnf (nth bnfs i)
                  |> force_typ names_lthy smapT
                  |> hidden_to_unit;
                val smap_argTs = strip_typeN live (fastype_of smap) |> fst;
                fun mk_smap_arg T_to_U =
                  (if domain_type T_to_U = range_type T_to_U then
                    HOLogic.id_const (domain_type T_to_U)
                  else
                    let
                      val (TY, (U, X)) = T_to_U |> dest_co_algT ||> dest_co_productT;
                      val T = mk_co_algT TY U;
                      fun mk_co_proj TU =
                        build_map lthy [] (fn TU =>
                          let val ((T1, T2), U) = TU |> co_swap |>> dest_co_productT in
                            if T1 = U then co_proj1_const TU
                            else mk_co_comp (mk_co_proj (co_swap (T1, U)),
                              co_proj1_const (co_swap (mk_co_productT T1 T2, T1)))
                          end)
                          TU;
                      fun default () =
                        mk_co_product (mk_co_proj (dest_funT T))
                          (fst (fst (mk_rec NONE recs lthy (mk_co_algT TY X))));
                    in
                      if can dest_co_productT TY then
                        mk_map_co_product (mk_co_proj (co_swap (dest_co_productT TY |> fst, U)))
                          (HOLogic.id_const X)
                        handle TYPE _ => default () (*N2M involving "prod" type*)
                      else
                        default ()
                    end)
                val smap_args = map mk_smap_arg smap_argTs;
              in
                mk_co_comp_abs_rep sF sF' fp_abs fp_rep abs rep
                  (mk_co_comp (s, Term.list_comb (smap, smap_args)))
              end
          end;
        val t = Term.list_comb (TUrec, map mk_s TUs);
      in
        (case b_opt of
          NONE => ((t, Drule.dummy_thm), lthy)
        | SOME b => Local_Theory.define ((b, NoSyn), ((Binding.concealed (Thm.def_binding b), []),
            fold_rev Term.absfree rec_strs' t)) lthy |>> apsnd snd)
      end;

    val recN = case_fp fp ctor_recN dtor_corecN;
    fun mk_recs lthy =
      fold2 (fn TU => fn b => fn ((recs, defs), lthy) =>
        mk_rec (SOME b) recs lthy TU |>> (fn (f, d) => (f :: recs, d :: defs)))
      resTs (map (Binding.suffix_name ("_" ^ recN)) bs) (([], []), lthy)
      |>> map_prod rev rev;
    val ((raw_xtor_co_recs, raw_xtor_co_rec_defs), (lthy, raw_lthy)) = lthy
      |> Local_Theory.open_target |> snd
      |> mk_recs
      ||> `Local_Theory.close_target;

    val phi = Proof_Context.export_morphism raw_lthy lthy;

    val xtor_co_recs = map (Morphism.term phi) raw_xtor_co_recs;

    val fp_rec_o_maps = of_fp_res #xtor_co_rec_o_maps
      |> maps (fn thm => [thm, thm RS rewrite_comp_comp]);

    val xtor_co_rec_thms =
      let
        val recs = map (fn r => Term.list_comb (r, rec_strs)) raw_xtor_co_recs;
        val rec_mapTs = co_swap (As @ fpTs, As @ map2 mk_co_productT fpTs Xs);
        val pre_rec_maps =
          map2 (fn Ds => fn bnf =>
            Term.list_comb (uncurry (mk_map_of_bnf Ds) rec_mapTs bnf,
              map HOLogic.id_const As @ map2 (mk_co_product o HOLogic.id_const) fpTs recs))
          Dss bnfs;

        fun mk_goals f xtor s smap fp_abs fp_rep abs rep =
          let
            val lhs = mk_co_comp (f, xtor);
            val rhs = mk_co_comp (s, smap);
          in
            HOLogic.mk_eq (lhs,
              mk_co_comp_abs_rep (co_alg_funT (fastype_of lhs)) (co_alg_funT (fastype_of rhs))
                fp_abs fp_rep abs rep rhs)
          end;

        val goals = @{map 8} mk_goals recs xtors rec_strs pre_rec_maps fp_abss fp_reps abss reps;

        val pre_map_defs = no_refl (map map_def_of_bnf bnfs);
        val fp_pre_map_defs = no_refl (map map_def_of_bnf pre_bnfs);

        val unfold_map = map (unfold_thms lthy (id_apply :: pre_map_defs));

        val fp_xtor_co_recs = map (mk_pointfree lthy) (of_fp_res #xtor_co_rec_thms);

        val fold_thms = case_fp fp @{thm comp_assoc} @{thm comp_assoc[symmetric]} ::
          map (fn thm => thm RS rewrite_comp_comp) @{thms map_prod.comp map_sum.comp} @
          @{thms id_apply comp_id id_comp map_prod.comp map_prod.id map_sum.comp map_sum.id};
        val rec_thms = fold_thms @ case_fp fp
          @{thms fst_convol map_prod_o_convol convol_o fst_comp_map_prod}
          @{thms case_sum_o_inj(1) case_sum_o_map_sum o_case_sum map_sum_o_inj(1)};

        val eq_thm_prop_untyped = Term.aconv_untyped o apply2 Thm.full_prop_of;

        val map_thms = no_refl (maps (fn bnf =>
           let val map_comp0 = map_comp0_of_bnf bnf RS sym
           in [map_comp0, map_comp0 RS rewrite_comp_comp, map_id0_of_bnf bnf] end)
          fp_or_nesting_bnfs) @
          remove eq_thm_prop_untyped (case_fp fp @{thm comp_assoc[symmetric]} @{thm comp_assoc})
          (map2 (fn thm => fn bnf =>
            @{thm type_copy_map_comp0_undo} OF
              (replicate 3 thm @ unfold_map [map_comp0_of_bnf bnf]) RS
              rewrite_comp_comp)
          type_definitions bnfs);

        fun mk_Rep_o_Abs thm = (thm RS @{thm type_copy_Rep_o_Abs})
          |> (fn thm => [thm, thm RS rewrite_comp_comp]);

        val fp_Rep_o_Abss = maps mk_Rep_o_Abs fp_type_definitions;
        val Rep_o_Abss = maps mk_Rep_o_Abs type_definitions;

        fun tac {context = ctxt, prems = _} =
          unfold_thms_tac ctxt (flat [rec_thms, raw_xtor_co_rec_defs, pre_map_defs,
            fp_pre_map_defs, fp_xtor_co_recs, fp_rec_o_maps, map_thms, fp_Rep_o_Abss,
            Rep_o_Abss]) THEN
          CONJ_WRAP (K (HEADGOAL (rtac ctxt refl))) bnfs;
      in
        Library.foldr1 HOLogic.mk_conj goals
        |> HOLogic.mk_Trueprop
        |> fold_rev Logic.all rec_strs
        |> (fn goal => Goal.prove_sorry raw_lthy [] [] goal tac)
        |> Thm.close_derivation
        |> Morphism.thm phi
        |> split_conj_thm
        |> map (fn thm => thm RS @{thm comp_eq_dest})
      end;

    val timer = time (timer "Nested-to-mutual (co)recursion");

    val common_notes =
      (case fp of
        Least_FP =>
        [(ctor_inductN, [xtor_co_induct_thm]),
         (ctor_rel_inductN, [xtor_rel_co_induct])]
      | Greatest_FP =>
        [(dtor_coinductN, [xtor_co_induct_thm]),
         (dtor_rel_coinductN, [xtor_rel_co_induct])])
      |> map (fn (thmN, thms) =>
        ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

    val notes =
      (case fp of
        Least_FP => [(ctor_recN, xtor_co_rec_thms)]
      | Greatest_FP => [(dtor_corecN, xtor_co_rec_thms)])
      |> map (apsnd (map single))
      |> maps (fn (thmN, thmss) =>
        map2 (fn b => fn thms =>
          ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
        bs thmss);

    val lthy = lthy |> Config.get lthy bnf_internals
      ? snd o Local_Theory.notes (common_notes @ notes);

    (* These results are half broken. This is deliberate. We care only about those fields that are
       used by "primrec", "primcorecursive", and "datatype_compat". *)
    val fp_res =
      ({Ts = fpTs, bnfs = of_fp_res #bnfs, pre_bnfs = bnfs, absT_infos = absT_infos,
        dtors = dtors, ctors = ctors,
        xtor_un_folds_legacy = xtor_co_recs (*wrong*), xtor_co_recs = xtor_co_recs,
        xtor_co_induct = xtor_co_induct_thm,
        dtor_ctors = of_fp_res #dtor_ctors (*too general types*),
        ctor_dtors = of_fp_res #ctor_dtors (*too general types*),
        ctor_injects = of_fp_res #ctor_injects (*too general types*),
        dtor_injects = of_fp_res #dtor_injects (*too general types*),
        xtor_maps = of_fp_res #xtor_maps (*too general types and terms*),
        xtor_map_unique = TrueI (*wrong*),
        xtor_setss = of_fp_res #xtor_setss (*too general types and terms*),
        xtor_rels = of_fp_res #xtor_rels (*too general types and terms*),
        xtor_un_fold_thms_legacy = xtor_co_rec_thms (*wrong*),
        xtor_co_rec_thms = xtor_co_rec_thms (*too general types and terms*),
        xtor_un_fold_unique_legacy = TrueI (*too general types and terms*),
        xtor_co_rec_unique = TrueI (*wrong*),
        xtor_un_fold_o_maps_legacy = fp_rec_o_maps (*wrong*),
        xtor_co_rec_o_maps = fp_rec_o_maps (*theorems about old constants*),
        xtor_un_fold_transfers_legacy = [], xtor_co_rec_transfers = [],
        xtor_rel_co_induct = xtor_rel_co_induct, dtor_set_inducts = []}
       |> morph_fp_result (Morphism.term_morphism "BNF" (singleton (Variable.polymorphic lthy))));
  in
    timer; (fp_res, lthy)
  end;

end;
