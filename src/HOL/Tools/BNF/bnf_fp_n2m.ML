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

fun mk_arg_cong ctxt n t =
  let
    val Us = fastype_of t |> strip_typeN n |> fst;
    val ((xs, ys), _) = ctxt
      |> mk_Frees "x" Us
      ||>> mk_Frees "y" Us;
    val goal = Logic.list_implies (@{map 2} (curry mk_Trueprop_eq) xs ys,
      mk_Trueprop_eq (list_comb (t, xs), list_comb (t, ys)));
    val vars = Variable.add_free_names ctxt goal [];
  in
    Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (hyp_subst_tac ctxt THEN' rtac ctxt refl))
    |> Thm.close_derivation \<^here>
  end;

val cacheN = "cache"
fun mk_cacheN i = cacheN ^ string_of_int i ^ "_";
val cache_threshold = Attrib.setup_config_int \<^binding>\<open>bnf_n2m_cache_threshold\<close> (K 200);
type cache = int * (term * thm) Typtab.table
val empty_cache = (0, Typtab.empty)
fun update_cache b0 TU t (cache as (i, tab), lthy) =
  if size_of_term t < Config.get lthy cache_threshold then (t, (cache, lthy))
  else
    let
      val b = Binding.prefix_name (mk_cacheN i) b0;
      val ((c, thm), lthy') =
        Local_Theory.define ((b, NoSyn), ((Binding.concealed (Thm.def_binding b), []), t)) lthy
        |>> apsnd snd;
    in
      (c, ((i + 1, Typtab.update (TU, (c, thm)) tab), lthy'))
    end;

fun lookup_cache (SOME _) _ _ = NONE
  | lookup_cache NONE TU ((_, tab), _) = Typtab.lookup tab TU |> Option.map fst;

fun construct_mutualized_fp fp mutual_cliques fpTs indexed_fp_ress bs resBs (resDs, Dss) bnfs
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
    val mk_co_comp = curry (HOLogic.mk_comp o co_swap);

    val dest_co_algT = co_swap o dest_funT;
    val co_alg_argT = case_fp fp range_type domain_type;
    val co_alg_funT = case_fp fp domain_type range_type;
    val rewrite_comp_comp = case_fp fp @{thm rewriteL_comp_comp} @{thm rewriteR_comp_comp};

    val fp_absT_infos = of_fp_res #absT_infos;
    val fp_bnfs = of_fp_res #bnfs;
    val fp_pre_bnfs = of_fp_res #pre_bnfs;

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

    val (((Xs, Ys), Bs), names_lthy) = names_lthy
      |> mk_TFrees n
      ||>> mk_TFrees n
      ||>> mk_TFrees m;

    val allAs = As @ Xs;
    val allBs = Bs @ Xs;
    val phiTs = map2 mk_pred2T As Bs;
    val thetaBs = As ~~ Bs;
    val fpTs' = map (Term.typ_subst_atomic thetaBs) fpTs;
    val fold_thetaAs = Xs ~~ fpTs;
    val fold_thetaBs = Xs ~~ fpTs';
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

    val rel_unfolds = maps (no_refl o single o rel_def_of_bnf) fp_pre_bnfs;
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

    fun mutual_instantiate ctxt inst =
      let
        val thetas = AList.group (op =) (mutual_cliques ~~ inst);
      in
        map2 (infer_instantiate ctxt o the o AList.lookup (op =) thetas) mutual_cliques
      end;

    val rel_xtor_co_inducts_inst =
      let
        val extract =
          case_fp fp (snd o Term.dest_comb) (snd o Term.dest_comb o fst o Term.dest_comb);
        val raw_phis = map (extract o HOLogic.dest_Trueprop o Thm.concl_of) rel_xtor_co_inducts;
        val inst = map (fn (t, u) => (#1 (dest_Var t), Thm.cterm_of lthy u)) (raw_phis ~~ pre_phis);
      in
        mutual_instantiate lthy inst rel_xtor_co_inducts
      end

    val xtor_rel_co_induct =
      mk_xtor_rel_co_induct_thm fp (@{map 3} cast castAs castBs pre_rels) pre_phis rels phis xs ys
        xtors xtor's (mk_rel_xtor_co_induct_tac fp abs_inverses rel_xtor_co_inducts_inst rel_defs
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

    val fold_strTs = map2 mk_co_algT fold_preTs Xs;
    val resTs = map2 mk_co_algT fpTs Xs;

    val fp_un_folds = of_fp_res #xtor_un_folds;
    val ns = map (length o #Ts o snd) indexed_fp_ress;

    fun force_fold i TU raw_un_fold =
      let
        val thy = Proof_Context.theory_of lthy;

        val approx_un_fold = raw_un_fold
          |> force_typ names_lthy (replicate (nth ns i) dummyT ---> TU);
        val subst = Term.typ_subst_atomic fold_thetaAs;

        fun mk_fp_absT_repT fp_repT fp_absT = mk_absT thy fp_repT fp_absT ooo mk_repT;
        val mk_fp_absT_repTs = @{map 5} mk_fp_absT_repT fp_repTs fp_absTs absTs repTs;

        val fold_preTs' = mk_fp_absT_repTs (map subst fold_preTs);

        val fold_pre_deads_only_Ts =
          map (typ_subst_nonatomic_sorted (map (rpair dummyT) (As @ sorted_fpTs))) fold_preTs';

        val (mutual_clique, TUs) =
          map_split dest_co_algT (binder_fun_types (fastype_of approx_un_fold))
          |>> map subst
          |> `(fn (_, Ys) => nth mutual_cliques
            (find_index (fn X => X = the (find_first (can dest_TFree) Ys)) Xs))
          ||> uncurry (map2 mk_co_algT);
        val cands = mutual_cliques ~~ map2 mk_co_algT fold_preTs' Xs;
        val js = find_indices (fn ((cl, cand), TU) =>
          cl = mutual_clique andalso Type.could_unify (TU, cand)) TUs cands;
        val Tpats = map (fn j => mk_co_algT (nth fold_pre_deads_only_Ts j) (nth Xs j)) js;
      in
        force_typ names_lthy (Tpats ---> TU) raw_un_fold
      end;

    fun mk_co_comp_abs_rep fp_absT absT fp_abs fp_rep abs rep t =
      case_fp fp (HOLogic.mk_comp (HOLogic.mk_comp (t, mk_abs absT abs), mk_rep fp_absT fp_rep))
        (HOLogic.mk_comp (mk_abs fp_absT fp_abs, HOLogic.mk_comp (mk_rep absT rep, t)));

    val thy = Proof_Context.theory_of lthy;
    fun mk_absT_fp_repT repT absT = mk_absT thy repT absT ooo mk_repT;

    fun mk_un_fold b_opt ss un_folds cache_lthy TU =
      (case lookup_cache b_opt TU cache_lthy of
        SOME t => ((t, Drule.dummy_thm), cache_lthy)
      | NONE =>
        let
          val x = co_alg_argT TU;
          val i = find_index (fn T => x = T) Xs;
          val TUfold =
            (case find_first (fn f => body_fun_type (fastype_of f) = TU) un_folds of
              NONE => force_fold i TU (nth fp_un_folds i)
            | SOME f => f);

          val TUs = binder_fun_types (fastype_of TUfold);

          fun mk_s TU' cache_lthy =
            let
              val i = find_index (fn T => co_alg_argT TU' = T) Xs;
              val fp_abs = nth fp_abss i;
              val fp_rep = nth fp_reps i;
              val abs = nth abss i;
              val rep = nth reps i;
              val sF = co_alg_funT TU';
              val sF' =
                mk_absT_fp_repT (nth repTs' i) (nth absTs' i) (nth fp_absTs i) (nth fp_repTs i) sF
                  handle Term.TYPE _ => sF;
              val F = nth fold_preTs i;
              val s = nth ss i;
            in
              if sF = F then (s, cache_lthy)
              else if sF' = F then (mk_co_comp_abs_rep sF sF' fp_abs fp_rep abs rep s, cache_lthy)
              else
                let
                  val smapT = replicate live dummyT ---> mk_co_algT sF' F;
                  fun hidden_to_unit t =
                    Term.subst_TVars (map (rpair HOLogic.unitT) (Term.add_tvar_names t [])) t;
                  val smap = map_of_bnf (nth bnfs i)
                    |> force_typ names_lthy smapT
                    |> hidden_to_unit;
                  val smap_argTs = strip_typeN live (fastype_of smap) |> fst;
                  fun mk_smap_arg T_to_U cache_lthy =
                    (if domain_type T_to_U = range_type T_to_U then
                      (HOLogic.id_const (domain_type T_to_U), cache_lthy)
                    else
                      mk_un_fold NONE ss un_folds cache_lthy T_to_U |>> fst);
                  val (smap_args, cache_lthy') = fold_map mk_smap_arg smap_argTs cache_lthy;
                in
                  (mk_co_comp_abs_rep sF sF' fp_abs fp_rep abs rep
                    (mk_co_comp s (Term.list_comb (smap, smap_args))), cache_lthy')
                end
            end;
          val (args, cache_lthy) = fold_map mk_s TUs cache_lthy;
          val t = Term.list_comb (TUfold, args);
        in
          (case b_opt of
            NONE => update_cache b TU t cache_lthy |>> rpair Drule.dummy_thm
          | SOME b => cache_lthy
             |-> (fn cache =>
               let
                 val S = HOLogic.mk_tupleT fold_strTs;
                 val s = HOLogic.mk_tuple ss;
                 val u = Const (\<^const_name>\<open>Let\<close>, S --> (S --> TU) --> TU) $ s $ absdummy S t;
               in
                 Local_Theory.define ((b, NoSyn), ((Binding.concealed (Thm.def_binding b), []), u))
                 #>> apsnd snd ##> pair cache
               end))
        end);

    val un_foldN = case_fp fp ctor_foldN dtor_unfoldN;
    fun mk_un_folds (ss_names, lthy) =
      let val ss = map2 (curry Free) ss_names fold_strTs;
      in
        fold2 (fn TU => fn b => fn ((un_folds, defs), cache_lthy) =>
          mk_un_fold (SOME b) (map2 (curry Free) ss_names fold_strTs) un_folds cache_lthy TU
          |>> (fn (f, d) => (f :: un_folds, d :: defs)))
        resTs (map (Binding.suffix_name ("_" ^ un_foldN)) bs) (([], []), (empty_cache, lthy))
        |>> map_prod rev rev
        |>> pair ss
      end;
    val ((ss, (un_folds, un_fold_defs0)), (cache, (lthy, raw_lthy))) = lthy
      |> (snd o Local_Theory.begin_nested)
      |> Variable.add_fixes (mk_names n "s")
      |> mk_un_folds
      ||> apsnd (`(Local_Theory.end_nested));

    val un_fold_defs = map (unfold_thms raw_lthy @{thms Let_const}) un_fold_defs0;

    val cache_defs = snd cache |> Typtab.dest |> map (snd o snd);

    val phi = Proof_Context.export_morphism raw_lthy lthy;

    val xtor_un_folds = map (head_of o Morphism.term phi) un_folds;
    val xtor_un_fold_defs = map (Drule.abs_def o Morphism.thm phi) un_fold_defs;
    val xtor_cache_defs = map (Drule.abs_def o Morphism.thm phi) cache_defs;
    val xtor_un_folds' = map2 (fn raw => fn t =>
        Const (fst (dest_Const t), fold_strTs ---> fastype_of raw))
      un_folds xtor_un_folds;

    val fp_un_fold_o_maps = of_fp_res #xtor_un_fold_o_maps
      |> maps (fn thm => [thm, thm RS rewrite_comp_comp]);

    val fold_mapTs = co_swap (As @ fpTs, As @ Xs);
    val pre_fold_maps = @{map 2} (fn Ds => uncurry (mk_map_of_bnf Ds) fold_mapTs) Dss bnfs
    fun mk_pre_fold_maps fs =
      map (fn mapx => Term.list_comb (mapx, map HOLogic.id_const As @ fs)) pre_fold_maps;

    val pre_map_defs = no_refl (map map_def_of_bnf bnfs);
    val fp_map_defs = no_refl (map map_def_of_bnf fp_pre_bnfs);
    val map_defs = pre_map_defs @ fp_map_defs;
    val pre_rel_defs = no_refl (map rel_def_of_bnf bnfs);
    val fp_rel_defs = no_refl (map rel_def_of_bnf fp_pre_bnfs);
    val rel_defs = pre_rel_defs @ fp_rel_defs;
    fun mk_Rep_o_Abs thm = (thm RS @{thm type_copy_Rep_o_Abs})
      |> (fn thm => [thm, thm RS rewrite_comp_comp]);
    val fp_Rep_o_Abss = maps mk_Rep_o_Abs fp_type_definitions;
    val pre_Rep_o_Abss = maps mk_Rep_o_Abs type_definitions;
    val Rep_o_Abss = fp_Rep_o_Abss @ pre_Rep_o_Abss;

    val unfold_map = map (unfold_thms lthy (id_apply :: pre_map_defs));
    val simp_thms = case_fp fp @{thm comp_assoc} @{thm comp_assoc[symmetric]} ::
      @{thms id_apply comp_id id_comp};

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

    val xtor_un_fold_thms =
      let
        val pre_fold_maps = mk_pre_fold_maps un_folds;
        fun mk_goals f xtor s smap fp_abs fp_rep abs rep =
          let
            val lhs = mk_co_comp f xtor;
            val rhs = mk_co_comp s smap;
          in
            HOLogic.mk_eq (lhs,
              mk_co_comp_abs_rep (co_alg_funT (fastype_of lhs)) (co_alg_funT (fastype_of rhs))
                fp_abs fp_rep abs rep rhs)
          end;

        val goals =
          @{map 8} mk_goals un_folds xtors ss pre_fold_maps fp_abss fp_reps abss reps;

        val fp_un_folds = map (mk_pointfree2 lthy) (of_fp_res #xtor_un_fold_thms);

        val simps = flat [simp_thms, un_fold_defs, map_defs, fp_un_folds,
          fp_un_fold_o_maps, map_thms, Rep_o_Abss];
      in
        Library.foldr1 HOLogic.mk_conj goals
        |> HOLogic.mk_Trueprop
        |> (fn goal => Goal.prove_sorry raw_lthy [] [] goal
          (fn {context = ctxt, prems = _} => mk_xtor_un_fold_tac ctxt n simps cache_defs))
        |> Thm.close_derivation \<^here>
        |> Morphism.thm phi
        |> split_conj_thm
        |> map (fn thm => thm RS @{thm comp_eq_dest})
      end;

    val xtor_un_fold_o_maps = of_fp_res #xtor_un_fold_o_maps
      |> maps (fn thm => [thm, thm RS rewrite_comp_comp]);
    val xtor_un_fold_unique_thm =
      let
        val (fs, _) = names_lthy |> mk_Frees "f" resTs;
        val fold_maps = mk_pre_fold_maps fs;
        fun mk_prem f s mapx xtor fp_abs fp_rep abs rep =
          let
            val lhs = mk_co_comp f xtor;
            val rhs = mk_co_comp s mapx;
          in
            mk_Trueprop_eq (lhs,
              mk_co_comp_abs_rep (co_alg_funT (fastype_of lhs)) (co_alg_funT (fastype_of rhs))
                fp_abs fp_rep abs rep rhs)
          end;
        val prems = @{map 8} mk_prem fs ss fold_maps xtors fp_abss fp_reps abss reps;
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 (curry HOLogic.mk_eq) fs un_folds));
        val vars = Variable.add_free_names raw_lthy concl [];
        val fp_un_fold_uniques0 = of_fp_res (split_conj_thm o #xtor_un_fold_unique)
          |> map (Drule.zero_var_indexes o unfold_thms lthy fp_map_defs);
        val names = fp_un_fold_uniques0
          |> map (Thm.concl_of #> HOLogic.dest_Trueprop
            #> HOLogic.dest_eq #> fst #> dest_Var #> fst);
        val inst = names ~~ map (Thm.cterm_of lthy) fs;
        val fp_un_fold_uniques = mutual_instantiate lthy inst fp_un_fold_uniques0;
        val map_arg_congs =
          map (fn bnf => mk_arg_cong lthy (live_of_bnf bnf) (map_of_bnf bnf)
            |> unfold_thms lthy (pre_map_defs @ simp_thms)) nesting_bnfs;
      in
        Goal.prove_sorry raw_lthy vars prems concl
          (mk_xtor_un_fold_unique_tac fp un_fold_defs map_arg_congs xtor_un_fold_o_maps
            Rep_o_Abss fp_un_fold_uniques simp_thms map_thms map_defs cache_defs)
          |> Thm.close_derivation \<^here>
          |> case_fp fp I (fn thm => thm OF replicate n sym)
          |> Morphism.thm phi
      end;

    val ABs = As ~~ Bs;
    val XYs = Xs ~~ Ys;
    val ABphiTs = @{map 2} mk_pred2T As Bs;
    val XYphiTs = @{map 2} mk_pred2T Xs Ys;

    val ((ABphis, XYphis), _) = names_lthy
      |> mk_Frees "R" ABphiTs
      ||>> mk_Frees "S" XYphiTs;

    val pre_rels = @{map 2} (fn Ds => mk_rel_of_bnf Ds (As @ Xs) (Bs @ Ys)) Dss bnfs;

    val ns = map (fn i => length (filter (fn c => i = c) mutual_cliques)) mutual_cliques;

    val map_transfers = map (funpow live (fn thm => thm RS @{thm rel_funD})
        #> unfold_thms lthy pre_rel_defs)
      (map map_transfer_of_bnf bnfs);
    val fp_un_fold_transfers = map2 (fn n => funpow n (fn thm => thm RS @{thm rel_funD})
        #> unfold_thms lthy fp_rel_defs)
      ns (of_fp_res #xtor_un_fold_transfers);
    val pre_Abs_transfers = map (fn thm => @{thm Abs_transfer} OF [thm, thm]) type_definitions;
    val fp_Abs_transfers = map (fn thm => @{thm Abs_transfer} OF [thm, thm]) fp_type_definitions;
    val Abs_transfers = pre_Abs_transfers @ fp_Abs_transfers;

    fun tac {context = ctxt, prems = _} =
      mk_xtor_un_fold_transfer_tac ctxt n xtor_un_fold_defs rel_defs fp_un_fold_transfers
        map_transfers Abs_transfers fp_or_nesting_rel_eqs xtor_cache_defs;

    val xtor_un_fold_transfer_thms =
      mk_xtor_co_iter_transfer_thms fp pre_rels XYphis XYphis rels ABphis
        xtor_un_folds' (map (subst_atomic_types (ABs @ XYs)) xtor_un_folds') tac lthy;

    val timer = time (timer "Nested-to-mutual (co)iteration");

    val xtor_maps = of_fp_res #xtor_maps;
    val xtor_rels = of_fp_res #xtor_rels;
    fun mk_Ts Cs = map (typ_subst_atomic (As ~~ Cs)) fpTs;
    val phi = Local_Theory.target_morphism lthy;
    val export = map (Morphism.term phi);
    val ((xtor_co_recs, (xtor_co_rec_thms, xtor_co_rec_unique_thm, xtor_co_rec_o_map_thms,
        xtor_co_rec_transfer_thms)), lthy) = lthy
      |> derive_xtor_co_recs fp bs mk_Ts (Dss, resDs) bnfs
        (export xtors) (export xtor_un_folds)
        xtor_un_fold_unique_thm xtor_un_fold_thms xtor_un_fold_transfer_thms xtor_maps xtor_rels
        (@{map 2} (curry (SOME o @{apply 2} (morph_absT_info phi))) fp_absT_infos absT_infos);

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
        Least_FP => [(ctor_foldN, xtor_un_fold_thms)]
      | Greatest_FP => [(dtor_unfoldN, xtor_un_fold_thms)])
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
        xtor_un_folds = xtor_un_folds, xtor_co_recs = xtor_co_recs,
        xtor_co_induct = xtor_co_induct_thm,
        dtor_ctors = of_fp_res #dtor_ctors (*too general types*),
        ctor_dtors = of_fp_res #ctor_dtors (*too general types*),
        ctor_injects = of_fp_res #ctor_injects (*too general types*),
        dtor_injects = of_fp_res #dtor_injects (*too general types*),
        xtor_maps = of_fp_res #xtor_maps (*too general types and terms*),
        xtor_map_unique = xtor_un_fold_unique_thm (*wrong*),
        xtor_setss = of_fp_res #xtor_setss (*too general types and terms*),
        xtor_rels = of_fp_res #xtor_rels (*too general types and terms*),
        xtor_un_fold_thms = xtor_un_fold_thms,
        xtor_co_rec_thms = xtor_co_rec_thms,
        xtor_un_fold_unique = xtor_un_fold_unique_thm,
        xtor_co_rec_unique = xtor_co_rec_unique_thm,
        xtor_un_fold_o_maps = fp_un_fold_o_maps (*wrong*),
        xtor_co_rec_o_maps = xtor_co_rec_o_map_thms (*wrong*),
        xtor_un_fold_transfers = xtor_un_fold_transfer_thms,
        xtor_co_rec_transfers = xtor_co_rec_transfer_thms (*wrong*),
        xtor_rel_co_induct = xtor_rel_co_induct, dtor_set_inducts = []}
       |> morph_fp_result (Morphism.term_morphism "BNF" (singleton (Variable.polymorphic lthy))));
  in
    timer; (fp_res, lthy)
  end;

end;
