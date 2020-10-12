(*  Title:      HOL/Tools/BNF/bnf_lfp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Datatype construction.
*)

signature BNF_LFP =
sig
  val construct_lfp: mixfix list -> binding list -> binding list -> binding list ->
    binding list list -> binding list -> (string * sort) list -> typ list * typ list list ->
    BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory ->
    BNF_FP_Util.fp_result * local_theory
end;

structure BNF_LFP : BNF_LFP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_Comp
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_LFP_Util
open BNF_LFP_Tactics

(*all BNFs have the same lives*)
fun construct_lfp mixfixes map_bs rel_bs pred_bs set_bss0 bs resBs (resDs, Dss) bnfs absT_infos
    lthy =
  let
    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    val live = live_of_bnf (hd bnfs);
    val n = length bnfs; (*active*)
    val ks = 1 upto n;
    val m = live - n; (*passive, if 0 don't generate a new BNF*)

    val internals = Config.get lthy bnf_internals;
    val b_names = map Binding.name_of bs;
    val b_name = mk_common_name b_names;
    val b = Binding.name b_name;

    fun mk_internal_of_b name =
      Binding.prefix_name (name ^ "_") #> Binding.prefix true b_name #> Binding.concealed;
    fun mk_internal_b name = mk_internal_of_b name b;
    fun mk_internal_bs name = map (mk_internal_of_b name) bs;
    val external_bs = map2 (Binding.prefix false) b_names bs
      |> not internals ? map Binding.concealed;

    val deads = fold (union (op =)) Dss resDs;
    val names_lthy = fold Variable.declare_typ deads lthy;
    val passives = map fst (subtract (op = o apsnd TFree) deads resBs);

    (* tvars *)
    val (((((passiveAs, activeAs), passiveBs), activeBs), passiveCs), activeCs) =
      names_lthy
      |> variant_tfrees passives
      ||>> mk_TFrees n
      ||>> variant_tfrees passives
      ||>> mk_TFrees n
      ||>> variant_tfrees passives
      ||>> mk_TFrees n
      |> fst;

    val allAs = passiveAs @ activeAs;
    val allBs' = passiveBs @ activeBs;
    val Ass = replicate n allAs;
    val allBs = passiveAs @ activeBs;
    val Bss = replicate n allBs;
    val allCs = passiveAs @ activeCs;
    val allCs' = passiveBs @ activeCs;
    val Css' = replicate n allCs';

    (* types *)
    val dead_poss =
      map (fn x => if member (op =) deads (TFree x) then SOME (TFree x) else NONE) resBs;
    fun mk_param NONE passive = (hd passive, tl passive)
      | mk_param (SOME a) passive = (a, passive);
    val mk_params = fold_map mk_param dead_poss #> fst;

    fun mk_FTs Ts = map2 (fn Ds => mk_T_of_bnf Ds Ts) Dss bnfs;
    val (params, params') = `(map Term.dest_TFree) (mk_params passiveAs);
    val FTsAs = mk_FTs allAs;
    val FTsBs = mk_FTs allBs;
    val FTsCs = mk_FTs allCs;
    val BTs = map HOLogic.mk_setT activeAs;
    val B'Ts = map HOLogic.mk_setT activeBs;
    val B''Ts = map HOLogic.mk_setT activeCs;
    val sTs = map2 (curry op -->) FTsAs activeAs;
    val s'Ts = map2 (curry op -->) FTsBs activeBs;
    val s''Ts = map2 (curry op -->) FTsCs activeCs;
    val fTs = map2 (curry op -->) activeAs activeBs;
    val inv_fTs = map2 (curry op -->) activeBs activeAs;
    val self_fTs = map2 (curry op -->) activeAs activeAs;
    val gTs = map2 (curry op -->) activeBs activeCs;
    val all_gTs = map2 (curry op -->) allBs allCs';

    (* terms *)
    val mapsAsAs = @{map 4} mk_map_of_bnf Dss Ass Ass bnfs;
    val mapsAsBs = @{map 4} mk_map_of_bnf Dss Ass Bss bnfs;
    val mapsBsCs' = @{map 4} mk_map_of_bnf Dss Bss Css' bnfs;
    val mapsAsCs' = @{map 4} mk_map_of_bnf Dss Ass Css' bnfs;
    fun mk_setss Ts = @{map 3} mk_sets_of_bnf (map (replicate live) Dss)
      (map (replicate live) (replicate n Ts)) bnfs;
    val setssAs = mk_setss allAs;
    val bd0s = @{map 3} mk_bd_of_bnf Dss Ass bnfs;
    val bds =
      @{map 3} (fn bd0 => fn Ds => fn bnf => mk_csum bd0
        (mk_card_of (HOLogic.mk_UNIV
          (mk_T_of_bnf Ds (replicate live (fst (dest_relT (fastype_of bd0)))) bnf))))
      bd0s Dss bnfs;
    val witss = map wits_of_bnf bnfs;

    val ((((((((zs, zs'), Bs), ss), fs), self_fs), all_gs), (xFs, xFs')), _) =
      lthy
      |> mk_Frees' "z" activeAs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" self_fTs
      ||>> mk_Frees "g" all_gTs
      ||>> mk_Frees' "x" FTsAs;

    val passive_UNIVs = map HOLogic.mk_UNIV passiveAs;
    val active_UNIVs = map HOLogic.mk_UNIV activeAs;
    val passive_ids = map HOLogic.id_const passiveAs;
    val active_ids = map HOLogic.id_const activeAs;

    (* thms *)
    val bd0_card_orders = map bd_card_order_of_bnf bnfs;
    val bd0_Card_orders = map bd_Card_order_of_bnf bnfs;
    val bd0_Cinfinites = map bd_Cinfinite_of_bnf bnfs;
    val set_bd0ss = map set_bd_of_bnf bnfs;

    val bd_Card_order = @{thm Card_order_csum};
    val bd_Card_orders = replicate n bd_Card_order;
    val bd_Cinfinites = map (fn thm => thm RS @{thm Cinfinite_csum1}) bd0_Cinfinites;
    val bd_Cnotzeros = map (fn thm => thm RS @{thm Cinfinite_Cnotzero}) bd_Cinfinites;
    val bd_Cinfinite = hd bd_Cinfinites;
    val set_bdss =
      map2 (fn set_bd0s => fn bd0_Card_order =>
        map (fn thm => ctrans OF [thm, bd0_Card_order RS @{thm ordLeq_csum1}]) set_bd0s)
      set_bd0ss bd0_Card_orders;
    val in_bds = map in_bd_of_bnf bnfs;
    val sym_map_comps = map (fn bnf => map_comp0_of_bnf bnf RS sym) bnfs;
    val map_comps = map map_comp_of_bnf bnfs;
    val map_cong0s = map map_cong0_of_bnf bnfs;
    val map_id0s = map map_id0_of_bnf bnfs;
    val map_ids = map map_id_of_bnf bnfs;
    val set_mapss = map set_map_of_bnf bnfs;
    val rel_mono_strong0s = map rel_mono_strong0_of_bnf bnfs;
    val le_rel_OOs = map le_rel_OO_of_bnf bnfs;

    val timer = time (timer "Extracted terms & thms");

    (* nonemptiness check *)
    fun new_wit X (wit: nonemptiness_witness) = subset (op =) (#I wit, (0 upto m - 1) @ map snd X);

    val all = m upto m + n - 1;

    fun enrich X = map_filter (fn i =>
      (case find_first (fn (_, i') => i = i') X of
        NONE =>
          (case find_index (new_wit X) (nth witss (i - m)) of
            ~1 => NONE
          | j => SOME (j, i))
      | SOME ji => SOME ji)) all;
    val reachable = fixpoint (op =) enrich [];
    val _ = (case subtract (op =) (map snd reachable) all of
        [] => ()
      | i :: _ => raise EMPTY_DATATYPE (Binding.name_of (nth bs (i - m))));

    val wit_thms = flat (map2 (fn bnf => fn (j, _) => nth (wit_thmss_of_bnf bnf) j) bnfs reachable);

    val timer = time (timer "Checked nonemptiness");

    (* derived thms *)

    (*map g1 ... gm g(m+1) ... g(m+n) (map id ... id f(m+1) ... f(m+n) x) =
      map g1 ... gm (g(m+1) o f(m+1)) ... (g(m+n) o f(m+n)) x*)
    fun mk_map_comp_id x mapAsBs mapBsCs mapAsCs map_comp0 =
      let
        val lhs = Term.list_comb (mapBsCs, all_gs) $
          (Term.list_comb (mapAsBs, passive_ids @ fs) $ x);
        val rhs = Term.list_comb (mapAsCs,
          take m all_gs @ map HOLogic.mk_comp (drop m all_gs ~~ fs)) $ x;
        val vars = fold (Variable.add_free_names lthy) [lhs, rhs] [];
      in
        Goal.prove_sorry lthy vars [] (mk_Trueprop_eq (lhs, rhs))
          (fn {context = ctxt, prems = _} => mk_map_comp_id_tac ctxt map_comp0)
        |> Thm.close_derivation \<^here>
      end;

    val map_comp_id_thms = @{map 5} mk_map_comp_id xFs mapsAsBs mapsBsCs' mapsAsCs' map_comps;

    (*forall a : set(m+1) x. f(m+1) a = a; ...; forall a : set(m+n) x. f(m+n) a = a ==>
      map id ... id f(m+1) ... f(m+n) x = x*)
    fun mk_map_cong0L x mapAsAs sets map_cong0 map_id =
      let
        fun mk_prem set f z z' = HOLogic.mk_Trueprop
          (mk_Ball (set $ x) (Term.absfree z' (HOLogic.mk_eq (f $ z, z))));
        val prems = @{map 4} mk_prem (drop m sets) self_fs zs zs';
        val goal = mk_Trueprop_eq (Term.list_comb (mapAsAs, passive_ids @ self_fs) $ x, x);
        val vars = fold (Variable.add_free_names lthy) (goal :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, goal))
          (fn {context = ctxt, prems = _} => mk_map_cong0L_tac ctxt m map_cong0 map_id)
        |> Thm.close_derivation \<^here>
      end;

    val map_cong0L_thms = @{map 5} mk_map_cong0L xFs mapsAsAs setssAs map_cong0s map_ids;
    val in_mono'_thms = map (fn bnf => in_mono_of_bnf bnf OF (replicate m subset_refl)) bnfs;
    val in_cong'_thms = map (fn bnf => in_cong_of_bnf bnf OF (replicate m refl)) bnfs;

    val timer = time (timer "Derived simple theorems");

    (* algebra *)

    val alg_bind = mk_internal_b algN;
    val alg_def_bind = (Thm.def_binding alg_bind, []);

    (*forall i = 1 ... n: (\<forall>x \<in> Fi_in UNIV .. UNIV B1 ... Bn. si x \<in> Bi)*)
    val alg_spec =
      let
        val ins = @{map 3} mk_in (replicate n (passive_UNIVs @ Bs)) setssAs FTsAs;
        fun mk_alg_conjunct B s X x x' =
          mk_Ball X (Term.absfree x' (HOLogic.mk_mem (s $ x, B)));

        val rhs = Library.foldr1 HOLogic.mk_conj (@{map 5} mk_alg_conjunct Bs ss ins xFs xFs')
      in
        fold_rev (Term.absfree o Term.dest_Free) (Bs @ ss) rhs
      end;

    val ((alg_free, (_, alg_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((alg_bind, NoSyn), (alg_def_bind, alg_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val alg = fst (Term.dest_Const (Morphism.term phi alg_free));
    val alg_def = mk_unabs_def (2 * n) (HOLogic.mk_obj_eq (Morphism.thm phi alg_def_free));

    fun mk_alg Bs ss =
      let
        val args = Bs @ ss;
        val Ts = map fastype_of args;
        val algT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (alg, algT), args)
      end;

    val ((((((((zs, zs'), Bs), B's), ss), s's), fs), (xFs, xFs')), _) =
      lthy
      |> mk_Frees' "z" activeAs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees' "x" FTsAs;

    val alg_set_thms =
      let
        val alg_prem = HOLogic.mk_Trueprop (mk_alg Bs ss);
        fun mk_prem x set B = HOLogic.mk_Trueprop (mk_leq (set $ x) B);
        fun mk_concl s x B = mk_Trueprop_mem (s $ x, B);
        val premss = map2 ((fn x => fn sets => map2 (mk_prem x) (drop m sets) Bs)) xFs setssAs;
        val concls = @{map 3} mk_concl ss xFs Bs;
        val goals = map2 (fn prems => fn concl =>
          Logic.list_implies (alg_prem :: prems, concl)) premss concls;
      in
        map (fn goal =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            mk_alg_set_tac ctxt alg_def))
          |> Thm.close_derivation \<^here>)
        goals
      end;

    val timer = time (timer "Algebra definition & thms");

    val alg_not_empty_thms =
      let
        val alg_prem =
          HOLogic.mk_Trueprop (mk_alg Bs ss);
        val concls = map (HOLogic.mk_Trueprop o mk_not_empty) Bs;
        val goals =
          map (fn concl => Logic.mk_implies (alg_prem, concl)) concls;
      in
        map2 (fn goal => fn alg_set =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal
            (fn {context = ctxt, prems = _} =>
              mk_alg_not_empty_tac ctxt alg_set alg_set_thms wit_thms))
          |> Thm.close_derivation \<^here>)
        goals alg_set_thms
      end;

    val timer = time (timer "Proved nonemptiness");

    (* morphism *)

    val mor_bind = mk_internal_b morN;
    val mor_def_bind = (Thm.def_binding mor_bind, []);

    (*fbetw) forall i = 1 ... n: (\<forall>x \<in> Bi. f x \<in> B'i)*)
    (*mor) forall i = 1 ... n: (\<forall>x \<in> Fi_in UNIV ... UNIV B1 ... Bn.
       f (s1 x) = s1' (Fi_map id ... id f1 ... fn x))*)
    val mor_spec =
      let
        fun mk_fbetw f B1 B2 z z' =
          mk_Ball B1 (Term.absfree z' (HOLogic.mk_mem (f $ z, B2)));
        fun mk_mor sets mapAsBs f s s' T x x' =
          mk_Ball (mk_in (passive_UNIVs @ Bs) sets T)
            (Term.absfree x' (HOLogic.mk_eq (f $ (s $ x), s' $
              (Term.list_comb (mapAsBs, passive_ids @ fs) $ x))));
        val rhs = HOLogic.mk_conj
          (Library.foldr1 HOLogic.mk_conj (@{map 5} mk_fbetw fs Bs B's zs zs'),
          Library.foldr1 HOLogic.mk_conj
            (@{map 8} mk_mor setssAs mapsAsBs fs ss s's FTsAs xFs xFs'))
      in
        fold_rev (Term.absfree o Term.dest_Free) (Bs @ ss @ B's @ s's @ fs) rhs
      end;

    val ((mor_free, (_, mor_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((mor_bind, NoSyn), (mor_def_bind, mor_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val mor = fst (Term.dest_Const (Morphism.term phi mor_free));
    val mor_def = mk_unabs_def (5 * n) (HOLogic.mk_obj_eq (Morphism.thm phi mor_def_free));

    fun mk_mor Bs1 ss1 Bs2 ss2 fs =
      let
        val args = Bs1 @ ss1 @ Bs2 @ ss2 @ fs;
        val Ts = map fastype_of (Bs1 @ ss1 @ Bs2 @ ss2 @ fs);
        val morT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (mor, morT), args)
      end;

    val (((((((((((Bs, Bs_copy), B's), B''s), ss), s's), s''s), fs), fs_copy), gs), xFs), _) =
      lthy
      |> mk_Frees "B" BTs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "B''" B''Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "s''" s''Ts
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "g" gTs
      ||>> mk_Frees "x" FTsAs;

    val morE_thms =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs);
        fun mk_elim_prem sets x T = HOLogic.mk_Trueprop
          (HOLogic.mk_mem (x, mk_in (passive_UNIVs @ Bs) sets T));
        fun mk_elim_goal sets mapAsBs f s s' x T =
          Logic.list_implies ([prem, mk_elim_prem sets x T],
            mk_Trueprop_eq (f $ (s $ x), s' $ Term.list_comb (mapAsBs, passive_ids @ fs @ [x])));
        val elim_goals = @{map 7} mk_elim_goal setssAs mapsAsBs fs ss s's xFs FTsAs;
        fun prove goal =
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            mk_mor_elim_tac ctxt mor_def))
          |> Thm.close_derivation \<^here>;
      in
        map prove elim_goals
      end;

    val mor_incl_thm =
      let
        val prems = map2 (HOLogic.mk_Trueprop oo mk_leq) Bs Bs_copy;
        val concl = HOLogic.mk_Trueprop (mk_mor Bs ss Bs_copy ss active_ids);
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => mk_mor_incl_tac ctxt mor_def map_ids)
        |> Thm.close_derivation \<^here>
      end;

    val mor_comp_thm =
      let
        val prems =
          [HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs),
           HOLogic.mk_Trueprop (mk_mor B's s's B''s s''s gs)];
        val concl =
          HOLogic.mk_Trueprop (mk_mor Bs ss B''s s''s (map2 (curry HOLogic.mk_comp) gs fs));
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => mk_mor_comp_tac ctxt mor_def set_mapss map_comp_id_thms)
        |> Thm.close_derivation \<^here>
      end;

    val mor_cong_thm =
      let
        val prems = map HOLogic.mk_Trueprop
         (map2 (curry HOLogic.mk_eq) fs_copy fs @ [mk_mor Bs ss B's s's fs])
        val concl = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs_copy);
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => (hyp_subst_tac ctxt THEN' assume_tac ctxt) 1)
        |> Thm.close_derivation \<^here>
      end;

    val mor_str_thm =
      let
        val maps = map2 (fn Ds => fn bnf => Term.list_comb
          (mk_map_of_bnf Ds (passiveAs @ FTsAs) allAs bnf, passive_ids @ ss)) Dss bnfs;
        val goal = HOLogic.mk_Trueprop
          (mk_mor (map HOLogic.mk_UNIV FTsAs) maps active_UNIVs ss ss);
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_mor_str_tac ctxt ks mor_def)
        |> Thm.close_derivation \<^here>
      end;

    val mor_UNIV_thm =
      let
        fun mk_conjunct mapAsBs f s s' = HOLogic.mk_eq
            (HOLogic.mk_comp (f, s),
            HOLogic.mk_comp (s', Term.list_comb (mapAsBs, passive_ids @ fs)));
        val lhs = mk_mor active_UNIVs ss (map HOLogic.mk_UNIV activeBs) s's fs;
        val rhs = Library.foldr1 HOLogic.mk_conj (@{map 4} mk_conjunct mapsAsBs fs ss s's);
        val vars = fold (Variable.add_free_names lthy) [lhs, rhs] [];
      in
        Goal.prove_sorry lthy vars [] (mk_Trueprop_eq (lhs, rhs))
          (fn {context = ctxt, prems = _} => mk_mor_UNIV_tac ctxt m morE_thms mor_def)
        |> Thm.close_derivation \<^here>
      end;

    val timer = time (timer "Morphism definition & thms");

    (* bounds *)

    val sum_bd = Library.foldr1 (uncurry mk_csum) bds;
    val sum_bdT = fst (dest_relT (fastype_of sum_bd));
    val (sum_bdT_params, sum_bdT_params') = `(map TFree) (Term.add_tfreesT sum_bdT []);

    val (lthy, sbd, sbd_Cinfinite, sbd_Card_order, set_sbdss, in_sbds) =
      if n = 1
      then (lthy, sum_bd, bd_Cinfinite, bd_Card_order, set_bdss, in_bds)
      else
        let
          val sbdT_bind = mk_internal_b sum_bdTN;

          val ((sbdT_name, (sbdT_glob_info, sbdT_loc_info)), lthy) =
            typedef (sbdT_bind, sum_bdT_params', NoSyn)
              (HOLogic.mk_UNIV sum_bdT) NONE (fn ctxt =>
                EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;

          val sbdT = Type (sbdT_name, sum_bdT_params);
          val Abs_sbdT = Const (#Abs_name sbdT_glob_info, sum_bdT --> sbdT);

          val sbd_bind = mk_internal_b sum_bdN;
          val sbd_def_bind = (Thm.def_binding sbd_bind, []);

          val sbd_spec = mk_dir_image sum_bd Abs_sbdT;

          val ((sbd_free, (_, sbd_def_free)), (lthy, lthy_old)) =
            lthy
            |> (snd o Local_Theory.begin_nested)
            |> Local_Theory.define ((sbd_bind, NoSyn), (sbd_def_bind, sbd_spec))
            ||> `Local_Theory.end_nested;

          val phi = Proof_Context.export_morphism lthy_old lthy;

          val sbd_def = HOLogic.mk_obj_eq (Morphism.thm phi sbd_def_free);
          val sbd = Const (fst (Term.dest_Const (Morphism.term phi sbd_free)), mk_relT (`I sbdT));

          val Abs_sbdT_inj = mk_Abs_inj_thm (#Abs_inject sbdT_loc_info);

          val sum_Cinfinite = mk_sum_Cinfinite bd_Cinfinites;
          val sum_Card_order = sum_Cinfinite RS conjunct2;

          val sbd_ordIso = @{thm ssubst_Pair_rhs} OF
            [@{thm dir_image} OF [Abs_sbdT_inj, sum_Card_order], sbd_def];
          val sbd_Cinfinite = @{thm Cinfinite_cong} OF [sbd_ordIso, sum_Cinfinite];
          val sbd_Card_order = sbd_Cinfinite RS conjunct2;

          fun mk_set_sbd i bd_Card_order bds =
            map (fn thm => @{thm ordLeq_ordIso_trans} OF
              [bd_Card_order RS mk_ordLeq_csum n i thm, sbd_ordIso]) bds;
          val set_sbdss = @{map 3} mk_set_sbd ks bd_Card_orders set_bdss;

          fun mk_in_bd_sum i Co Cnz bd =
            Cnz RS ((@{thm ordLeq_ordIso_trans} OF
              [Co RS mk_ordLeq_csum n i (Co RS @{thm ordLeq_refl}), sbd_ordIso]) RS
              (bd RS @{thm ordLeq_transitive[OF _ cexp_mono2_Cnotzero[OF _ Card_order_csum]]}));
          val in_sbds = @{map 4} mk_in_bd_sum ks bd_Card_orders bd_Cnotzeros in_bds;
       in
         (lthy, sbd, sbd_Cinfinite, sbd_Card_order, set_sbdss, in_sbds)
       end;

    val sbd_Cnotzero = sbd_Cinfinite RS @{thm Cinfinite_Cnotzero};
    val suc_bd = mk_cardSuc sbd;

    val field_suc_bd = mk_Field suc_bd;
    val suc_bdT = fst (dest_relT (fastype_of suc_bd));
    fun mk_Asuc_bd [] = mk_cexp ctwo suc_bd
      | mk_Asuc_bd As =
        mk_cexp (mk_csum (Library.foldr1 (uncurry mk_csum) (map mk_card_of As)) ctwo) suc_bd;

    val suc_bd_Card_order =  sbd_Card_order RS @{thm cardSuc_Card_order};
    val suc_bd_Cinfinite = sbd_Cinfinite RS @{thm Cinfinite_cardSuc};
    val suc_bd_Cnotzero = suc_bd_Cinfinite RS @{thm Cinfinite_Cnotzero};
    val suc_bd_worel = suc_bd_Card_order RS @{thm Card_order_wo_rel}
    val basis_Asuc = if m = 0 then @{thm ordLeq_refl[OF Card_order_ctwo]}
        else @{thm ordLeq_csum2[OF Card_order_ctwo]};
    val Asuc_bd_Cinfinite = suc_bd_Cinfinite RS (basis_Asuc RS @{thm Cinfinite_cexp});

    val suc_bd_Asuc_bd = @{thm ordLess_ordLeq_trans[OF ordLess_ctwo_cexp cexp_mono1]} OF
      [suc_bd_Card_order, basis_Asuc, suc_bd_Card_order];


    val Asuc_bd = mk_Asuc_bd passive_UNIVs;
    val Asuc_bdT = fst (dest_relT (fastype_of Asuc_bd));
    val II_BTs = replicate n (HOLogic.mk_setT Asuc_bdT);
    val II_sTs = map2 (fn Ds => fn bnf =>
      mk_T_of_bnf Ds (passiveAs @ replicate n Asuc_bdT) bnf --> Asuc_bdT) Dss bnfs;

    val ((((((Bs, ss), idxs), Asi_name), (idx, idx')), (jdx, jdx')), _) =
      lthy
      |> mk_Frees "B" BTs
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "i" (replicate n suc_bdT)
      ||>> (fn ctxt => apfst the_single (mk_fresh_names ctxt 1 "Asi"))
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "i") suc_bdT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "j") suc_bdT;

    val suc_bd_limit_thm =
      let
        val prem = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map (fn idx => HOLogic.mk_mem (idx, field_suc_bd)) idxs));
        fun mk_conjunct idx = HOLogic.mk_conj (mk_not_eq idx jdx,
          HOLogic.mk_mem (HOLogic.mk_prod (idx, jdx), suc_bd));
        val concl = HOLogic.mk_Trueprop (mk_Bex field_suc_bd
          (Term.absfree jdx' (Library.foldr1 HOLogic.mk_conj (map mk_conjunct idxs))));
        val vars = fold (Variable.add_free_names lthy) [prem, concl] [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies ([prem], concl))
          (fn {context = ctxt, prems = _} => mk_bd_limit_tac ctxt n suc_bd_Cinfinite)
        |> Thm.close_derivation \<^here>
      end;

    val timer = time (timer "Bounds");

    (* minimal algebra *)

    fun mk_minG Asi i k = mk_UNION (mk_underS suc_bd $ i)
      (Term.absfree jdx' (mk_nthN n (Asi $ jdx) k));

    fun mk_minH_component Asi i sets Ts s k =
      HOLogic.mk_binop \<^const_name>\<open>sup\<close>
      (mk_minG Asi i k, mk_image s $ mk_in (passive_UNIVs @ map (mk_minG Asi i) ks) sets Ts);

    fun mk_min_algs ss =
      let
        val BTs = map (range_type o fastype_of) ss;
        val Ts = passiveAs @ BTs;
        val (Asi, Asi') = `Free (Asi_name, suc_bdT -->
          Library.foldr1 HOLogic.mk_prodT (map HOLogic.mk_setT BTs));
      in
         mk_worec suc_bd (Term.absfree Asi' (Term.absfree idx' (HOLogic.mk_tuple
           (@{map 4} (mk_minH_component Asi idx) (mk_setss Ts) (mk_FTs Ts) ss ks))))
      end;

    val (min_algs_thms, min_algs_mono_thms, card_of_min_algs_thm, least_min_algs_thm) =
      let
        val i_field = HOLogic.mk_mem (idx, field_suc_bd);
        val min_algs = mk_min_algs ss;

        val min_algss = map (fn k => mk_nthN n (min_algs $ idx) k) ks;

        val concl = HOLogic.mk_Trueprop
          (HOLogic.mk_eq (min_algs $ idx, HOLogic.mk_tuple
            (@{map 4} (mk_minH_component min_algs idx) setssAs FTsAs ss ks)));
        val goal = Logic.mk_implies (HOLogic.mk_Trueprop i_field, concl);
        val vars = Variable.add_free_names lthy goal [];

        val min_algs_thm = Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_min_algs_tac ctxt suc_bd_worel in_cong'_thms)
          |> Thm.close_derivation \<^here>;

        val min_algs_thms = map (fn k => min_algs_thm RS mk_nthI n k) ks;

        fun mk_mono_goal min_alg =
          HOLogic.mk_Trueprop (mk_relChain suc_bd (Term.absfree idx' min_alg));

        val monos =
          map2 (fn goal => fn min_algs =>
            Variable.add_free_names lthy goal []
            |> (fn vars => Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_min_algs_mono_tac ctxt min_algs))
            |> Thm.close_derivation \<^here>)
          (map mk_mono_goal min_algss) min_algs_thms;

        fun mk_card_conjunct min_alg = mk_ordLeq (mk_card_of min_alg) Asuc_bd;
        val card_conjunction = Library.foldr1 HOLogic.mk_conj (map mk_card_conjunct min_algss);
        val card_cT = Thm.ctyp_of lthy suc_bdT;
        val card_ct = Thm.cterm_of lthy (Term.absfree idx' card_conjunction);

        val card_of =
          let
            val goal = HOLogic.mk_Trueprop (HOLogic.mk_imp (i_field, card_conjunction));
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_min_algs_card_of_tac ctxt card_cT card_ct
                m suc_bd_worel min_algs_thms in_sbds
                sbd_Card_order sbd_Cnotzero suc_bd_Card_order suc_bd_Cinfinite suc_bd_Cnotzero
                suc_bd_Asuc_bd Asuc_bd_Cinfinite)
            |> Thm.close_derivation \<^here>
          end;

        val least_prem = HOLogic.mk_Trueprop (mk_alg Bs ss);
        val least_conjunction = Library.foldr1 HOLogic.mk_conj (map2 mk_leq min_algss Bs);
        val least_cT = Thm.ctyp_of lthy suc_bdT;
        val least_ct = Thm.cterm_of lthy (Term.absfree idx' least_conjunction);

        val least =
          let
            val goal = Logic.mk_implies (least_prem,
              HOLogic.mk_Trueprop (HOLogic.mk_imp (i_field, least_conjunction)));
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_min_algs_least_tac ctxt least_cT least_ct
                suc_bd_worel min_algs_thms alg_set_thms)
            |> Thm.close_derivation \<^here>
          end;
      in
        (min_algs_thms, monos, card_of, least)
      end;

    val timer = time (timer "min_algs definition & thms");

    val min_alg_binds = mk_internal_bs min_algN;
    fun min_alg_bind i = nth min_alg_binds (i - 1);
    val min_alg_def_bind = rpair [] o Thm.def_binding o min_alg_bind;

    fun min_alg_spec i =
      let
        val rhs = mk_UNION (field_suc_bd)
          (Term.absfree idx' (mk_nthN n (mk_min_algs ss $ idx) i));
      in
        fold_rev (Term.absfree o Term.dest_Free) ss rhs
      end;

    val ((min_alg_frees, (_, min_alg_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i => Local_Theory.define
        ((min_alg_bind i, NoSyn), (min_alg_def_bind i, min_alg_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val min_algs = map (fst o Term.dest_Const o Morphism.term phi) min_alg_frees;
    val min_alg_defs = map (fn def =>
      mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi def))) min_alg_def_frees;

    fun mk_min_alg ss i =
      let
        val T = HOLogic.mk_setT (range_type (fastype_of (nth ss (i - 1))))
        val Ts = map fastype_of ss;
        val min_algT = Library.foldr (op -->) (Ts, T);
      in
        Term.list_comb (Const (nth min_algs (i - 1), min_algT), ss)
      end;

    val min_algs = map (mk_min_alg ss) ks;

    val ((Bs, ss), _) =
      lthy
      |> mk_Frees "B" BTs
      ||>> mk_Frees "s" sTs;

    val (alg_min_alg_thm, card_of_min_alg_thms, least_min_alg_thms, mor_incl_min_alg_thm) =
      let
        val alg_min_alg =
          let
            val goal = HOLogic.mk_Trueprop (mk_alg min_algs ss);
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_alg_min_alg_tac ctxt m alg_def min_alg_defs
                suc_bd_limit_thm sbd_Cinfinite set_sbdss min_algs_thms min_algs_mono_thms)
            |> Thm.close_derivation \<^here>
          end;

        fun mk_card_of_thm min_alg def =
          let
            val goal = HOLogic.mk_Trueprop (mk_ordLeq (mk_card_of min_alg) Asuc_bd);
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_card_of_min_alg_tac ctxt def card_of_min_algs_thm
                suc_bd_Card_order suc_bd_Asuc_bd Asuc_bd_Cinfinite)
            |> Thm.close_derivation \<^here>
          end;

        fun mk_least_thm min_alg B def =
          let
            val prem = HOLogic.mk_Trueprop (mk_alg Bs ss);
            val goal = Logic.mk_implies (prem, HOLogic.mk_Trueprop (mk_leq min_alg B));
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_least_min_alg_tac ctxt def least_min_algs_thm)
            |> Thm.close_derivation \<^here>
          end;

        val leasts = @{map 3} mk_least_thm min_algs Bs min_alg_defs;

        val incl =
          let
            val prem = HOLogic.mk_Trueprop (mk_alg Bs ss);
            val goal = Logic.mk_implies (prem,
              HOLogic.mk_Trueprop (mk_mor min_algs ss Bs ss active_ids));
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                EVERY' (rtac ctxt mor_incl_thm :: map (etac ctxt) leasts) 1)
            |> Thm.close_derivation \<^here>
          end;
      in
        (alg_min_alg, map2 mk_card_of_thm min_algs min_alg_defs, leasts, incl)
      end;

    val timer = time (timer "Minimal algebra definition & thms");

    val II_repT = HOLogic.mk_prodT (HOLogic.mk_tupleT II_BTs, HOLogic.mk_tupleT II_sTs);
    val IIT_bind = mk_internal_b IITN;

    val ((IIT_name, (IIT_glob_info, IIT_loc_info)), lthy) =
      typedef (IIT_bind, params, NoSyn)
        (HOLogic.mk_UNIV II_repT) NONE (fn ctxt => EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;

    val IIT = Type (IIT_name, params');
    val Abs_IIT = Const (#Abs_name IIT_glob_info, II_repT --> IIT);
    val Rep_IIT = Const (#Rep_name IIT_glob_info, IIT --> II_repT);
    val Abs_IIT_inverse_thm = UNIV_I RS #Abs_inverse IIT_loc_info;

    val initT = IIT --> Asuc_bdT;
    val active_initTs = replicate n initT;
    val init_FTs = map2 (fn Ds => mk_T_of_bnf Ds (passiveAs @ active_initTs)) Dss bnfs;
    val init_fTs = map (fn T => initT --> T) activeAs;

    val ((((II_Bs, II_ss), (iidx, iidx')), init_xFs), _) =
      lthy
      |> mk_Frees "IIB" II_BTs
      ||>> mk_Frees "IIs" II_sTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "i") IIT
      ||>> mk_Frees "x" init_FTs;

    val II = HOLogic.mk_Collect (fst iidx', IIT, list_exists_free (II_Bs @ II_ss)
      (HOLogic.mk_conj (HOLogic.mk_eq (iidx,
        Abs_IIT $ (HOLogic.mk_prod (HOLogic.mk_tuple II_Bs, HOLogic.mk_tuple II_ss))),
        mk_alg II_Bs II_ss)));

    val select_Bs = map (mk_nthN n (HOLogic.mk_fst (Rep_IIT $ iidx))) ks;
    val select_ss = map (mk_nthN n (HOLogic.mk_snd (Rep_IIT $ iidx))) ks;

    val str_init_binds = mk_internal_bs str_initN;
    fun str_init_bind i = nth str_init_binds (i - 1);
    val str_init_def_bind = rpair [] o Thm.def_binding o str_init_bind;

    fun str_init_spec i =
      let
        val init_xF = nth init_xFs (i - 1)
        val select_s = nth select_ss (i - 1);
        val map = mk_map_of_bnf (nth Dss (i - 1))
          (passiveAs @ active_initTs) (passiveAs @ replicate n Asuc_bdT)
          (nth bnfs (i - 1));
        val map_args = passive_ids @ replicate n (mk_rapp iidx Asuc_bdT);
        val rhs = select_s $ (Term.list_comb (map, map_args) $ init_xF);
      in
        fold_rev (Term.absfree o Term.dest_Free) [init_xF, iidx] rhs
      end;

    val ((str_init_frees, (_, str_init_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i => Local_Theory.define
        ((str_init_bind i, NoSyn), (str_init_def_bind i, str_init_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val str_inits =
      map (Term.subst_atomic_types (map (`(Morphism.typ phi)) params') o Morphism.term phi)
        str_init_frees;

    val str_init_defs = map (fn def =>
      mk_unabs_def 2 (HOLogic.mk_obj_eq (Morphism.thm phi def))) str_init_def_frees;

    val car_inits = map (mk_min_alg str_inits) ks;

    val (((((((((Bs, ss), Asuc_fs), (iidx, iidx')), init_xs), (init_xFs, init_xFs')), init_fs),
        init_fs_copy), init_phis), _) =
      lthy
      |> mk_Frees "B" BTs
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "f" (map (fn T => Asuc_bdT --> T) activeAs)
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "i") IIT
      ||>> mk_Frees "ix" active_initTs
      ||>> mk_Frees' "x" init_FTs
      ||>> mk_Frees "f" init_fTs
      ||>> mk_Frees "f" init_fTs
      ||>> mk_Frees "P" (replicate n (mk_pred1T initT));

    val alg_init_thm =
      infer_instantiate' lthy (map (SOME o Thm.cterm_of lthy) str_inits) alg_min_alg_thm;

    val alg_select_thm = Goal.prove_sorry lthy [] []
      (HOLogic.mk_Trueprop (mk_Ball II
        (Term.absfree iidx' (mk_alg select_Bs select_ss))))
      (fn {context = ctxt, prems = _} => mk_alg_select_tac ctxt Abs_IIT_inverse_thm)
      |> Thm.close_derivation \<^here>;

    val mor_select_thm =
      let
        val i_prem = mk_Trueprop_mem (iidx, II);
        val mor_prem = HOLogic.mk_Trueprop (mk_mor select_Bs select_ss active_UNIVs ss Asuc_fs);
        val prems = [i_prem, mor_prem];
        val concl = HOLogic.mk_Trueprop
          (mk_mor car_inits str_inits active_UNIVs ss
            (map (fn f => HOLogic.mk_comp (f, mk_rapp iidx Asuc_bdT)) Asuc_fs));
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => mk_mor_select_tac ctxt mor_def mor_cong_thm
            mor_comp_thm mor_incl_min_alg_thm alg_def alg_select_thm alg_set_thms set_mapss
            str_init_defs)
        |> Thm.close_derivation \<^here>
      end;

    val init_unique_mor_thms =
      let
        val prems = map2 (HOLogic.mk_Trueprop oo curry HOLogic.mk_mem) init_xs car_inits
        val mor_prems = map HOLogic.mk_Trueprop
          [mk_mor car_inits str_inits Bs ss init_fs,
          mk_mor car_inits str_inits Bs ss init_fs_copy];
        fun mk_fun_eq f g x = HOLogic.mk_eq (f $ x, g $ x);
        val unique = HOLogic.mk_Trueprop
          (Library.foldr1 HOLogic.mk_conj (@{map 3} mk_fun_eq init_fs init_fs_copy init_xs));
        val cts = map (Thm.cterm_of lthy) ss;
        val all_prems = prems @ mor_prems;
        val vars = fold (Variable.add_free_names lthy) (unique :: all_prems) [];
        val unique_mor =
          Goal.prove_sorry lthy vars [] (Logic.list_implies (all_prems, unique))
            (fn {context = ctxt, prems = _} => mk_init_unique_mor_tac ctxt cts m alg_def
              alg_init_thm least_min_alg_thms in_mono'_thms alg_set_thms morE_thms map_cong0s)
          |> Thm.close_derivation \<^here>;
      in
        split_conj_thm unique_mor
      end;

    val init_setss = mk_setss (passiveAs @ active_initTs);
    val active_init_setss = map (drop m) init_setss;
    val init_ins = map2 (fn sets => mk_in (passive_UNIVs @ car_inits) sets) init_setss init_FTs;

    fun mk_closed phis =
      let
        fun mk_conjunct phi str_init init_sets init_in x x' =
          let
            val prem = Library.foldr1 HOLogic.mk_conj
              (map2 (fn set => mk_Ball (set $ x)) init_sets phis);
            val concl = phi $ (str_init $ x);
          in
            mk_Ball init_in (Term.absfree x' (HOLogic.mk_imp (prem, concl)))
          end;
      in
        Library.foldr1 HOLogic.mk_conj
          (@{map 6} mk_conjunct phis str_inits active_init_setss init_ins init_xFs init_xFs')
      end;

    val init_induct_thm =
      let
        val prem = HOLogic.mk_Trueprop (mk_closed init_phis);
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 mk_Ball car_inits init_phis));
        val vars = fold (Variable.add_free_names lthy) [concl, prem] [];
      in
        Goal.prove_sorry lthy vars [] (Logic.mk_implies (prem, concl))
          (fn {context = ctxt, prems = _} => mk_init_induct_tac ctxt m alg_def alg_init_thm
            least_min_alg_thms alg_set_thms)
        |> Thm.close_derivation \<^here>
      end;

    val timer = time (timer "Initiality definition & thms");

    val ((T_names, (T_glob_infos, T_loc_infos)), lthy) =
      lthy
      |> @{fold_map 3} (fn b => fn mx => fn car_init =>
        typedef (b, params, mx) car_init NONE
          (fn ctxt =>
            EVERY' [rtac ctxt iffD2, rtac ctxt @{thm ex_in_conv}, resolve_tac ctxt alg_not_empty_thms,
            rtac ctxt alg_init_thm] 1)) bs mixfixes car_inits
      |>> apsnd split_list o split_list;

    val Ts = map (fn name => Type (name, params')) T_names;
    fun mk_Ts passive = map (Term.typ_subst_atomic (passiveAs ~~ passive)) Ts;
    val Ts' = mk_Ts passiveBs;
    val Rep_Ts = map2 (fn info => fn T => Const (#Rep_name info, T --> initT)) T_glob_infos Ts;
    val Abs_Ts = map2 (fn info => fn T => Const (#Abs_name info, initT --> T)) T_glob_infos Ts;

    val type_defs = map #type_definition T_loc_infos;
    val Reps = map #Rep T_loc_infos;
    val Rep_inverses = map #Rep_inverse T_loc_infos;
    val Abs_inverses = map #Abs_inverse T_loc_infos;

    val timer = time (timer "THE TYPEDEFs & Rep/Abs thms");

    val UNIVs = map HOLogic.mk_UNIV Ts;
    val FTs = mk_FTs (passiveAs @ Ts);
    val FTs' = mk_FTs (passiveBs @ Ts');
    fun mk_set_Ts T = passiveAs @ replicate n (HOLogic.mk_setT T);
    val setFTss = map (mk_FTs o mk_set_Ts) passiveAs;
    val FTs_setss = mk_setss (passiveAs @ Ts);
    val FTs'_setss = mk_setss (passiveBs @ Ts');
    val map_FT_inits = map2 (fn Ds =>
      mk_map_of_bnf Ds (passiveAs @ Ts) (passiveAs @ active_initTs)) Dss bnfs;
    val fTs = map2 (curry op -->) Ts activeAs;
    val foldT = Library.foldr1 HOLogic.mk_prodT (map2 (curry op -->) Ts activeAs);

    val ((ss, (fold_f, fold_f')), _) =
      lthy
      |> mk_Frees "s" sTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "f") foldT;

    fun ctor_bind i = nth external_bs (i - 1) |> Binding.prefix_name (ctorN ^ "_");
    val ctor_def_bind = rpair [] o Binding.concealed o Thm.def_binding o ctor_bind;

    fun ctor_spec abs str map_FT_init =
      Library.foldl1 HOLogic.mk_comp [abs, str,
        Term.list_comb (map_FT_init, map HOLogic.id_const passiveAs @ Rep_Ts)];

    val ((ctor_frees, (_, ctor_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> @{fold_map 4} (fn i => fn abs => fn str => fn mapx =>
        Local_Theory.define
          ((ctor_bind i, NoSyn), (ctor_def_bind i, ctor_spec abs str mapx)))
          ks Abs_Ts str_inits map_FT_inits
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_ctors passive =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ (mk_params passive)) o
        Morphism.term phi) ctor_frees;
    val ctors = mk_ctors passiveAs;
    val ctor's = mk_ctors passiveBs;
    val ctor_defs = map (fn def => HOLogic.mk_obj_eq (Morphism.thm phi def)) ctor_def_frees;

    val (mor_Rep_thm, mor_Abs_thm) =
      let
        val defs = mor_def :: ctor_defs;

        val mor_Rep =
          Goal.prove_sorry lthy [] []
            (HOLogic.mk_Trueprop (mk_mor UNIVs ctors car_inits str_inits Rep_Ts))
            (fn {context = ctxt, prems = _} => mk_mor_Rep_tac ctxt m defs Reps Abs_inverses
              alg_min_alg_thm alg_set_thms set_mapss)
          |> Thm.close_derivation \<^here>;

        fun mk_ct initFT str abs = Term.absdummy initFT (abs $ (str $ Bound 0))
        val cts = @{map 3} (Thm.cterm_of lthy ooo mk_ct) init_FTs str_inits Abs_Ts;

        val mor_Abs =
          Goal.prove_sorry lthy [] []
            (HOLogic.mk_Trueprop (mk_mor car_inits str_inits UNIVs ctors Abs_Ts))
            (fn {context = ctxt, prems = _} => mk_mor_Abs_tac ctxt cts defs Abs_inverses
              map_comp_id_thms map_cong0L_thms)
          |> Thm.close_derivation \<^here>;
      in
        (mor_Rep, mor_Abs)
      end;

    val timer = time (timer "ctor definitions & thms");

    val fold_fun = Term.absfree fold_f'
      (mk_mor UNIVs ctors active_UNIVs ss (map (mk_nthN n fold_f) ks));
    val foldx = HOLogic.choice_const foldT $ fold_fun;

    fun fold_bind i = nth external_bs (i - 1) |> Binding.prefix_name (ctor_foldN ^ "_");
    val fold_def_bind = rpair [] o Binding.concealed o Thm.def_binding o fold_bind;

    fun fold_spec i = fold_rev (Term.absfree o Term.dest_Free) ss (mk_nthN n foldx i);

    val ((fold_frees, (_, fold_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i =>
        Local_Theory.define ((fold_bind i, NoSyn), (fold_def_bind i, fold_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val folds = map (Morphism.term phi) fold_frees;
    val fold_names = map (fst o dest_Const) folds;
    fun mk_folds passives actives =
      @{map 3} (fn name => fn T => fn active =>
        Const (name, Library.foldr (op -->)
          (map2 (curry op -->) (mk_FTs (passives @ actives)) actives, T --> active)))
      fold_names (mk_Ts passives) actives;
    fun mk_fold Ts ss i = Term.list_comb (Const (nth fold_names (i - 1), Library.foldr (op -->)
      (map fastype_of ss, nth Ts (i - 1) --> range_type (fastype_of (nth ss (i - 1))))), ss);
    val fold_defs = map (fn def =>
      mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi def))) fold_def_frees;

    (* algebra copies *)

    val ((((((Bs, B's), ss), s's), inv_fs), fs), _) =
      lthy
      |> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "f" inv_fTs
      ||>> mk_Frees "f" fTs;

    val copy_thm =
      let
        val prems = HOLogic.mk_Trueprop (mk_alg Bs ss) ::
          @{map 3} (HOLogic.mk_Trueprop ooo mk_bij_betw) inv_fs B's Bs;
        val concl = HOLogic.mk_Trueprop (list_exists_free s's
          (HOLogic.mk_conj (mk_alg B's s's, mk_mor B's s's Bs ss inv_fs)));
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => mk_copy_tac ctxt m alg_def mor_def alg_set_thms
            set_mapss)
        |> Thm.close_derivation \<^here>
      end;

    val init_ex_mor_thm =
      let
        val goal = HOLogic.mk_Trueprop
          (list_exists_free fs (mk_mor UNIVs ctors active_UNIVs ss fs));
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} =>
            mk_init_ex_mor_tac ctxt Abs_IIT_inverse_thm (alg_min_alg_thm RS copy_thm)
              card_of_min_alg_thms mor_Rep_thm mor_comp_thm mor_select_thm mor_incl_thm)
        |> Thm.close_derivation \<^here>
      end;

    val mor_fold_thm =
      let
        val mor_cong = mor_cong_thm OF (map (mk_nth_conv n) ks);
        val cT = Thm.ctyp_of lthy foldT;
        val ct = Thm.cterm_of lthy fold_fun
        val goal = HOLogic.mk_Trueprop (mk_mor UNIVs ctors active_UNIVs ss (map (mk_fold Ts ss) ks));
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, ...} =>
            mk_mor_fold_tac ctxt cT ct fold_defs init_ex_mor_thm mor_cong)
        |> Thm.close_derivation \<^here>
      end;

    val ctor_fold_thms = map (fn morE => rule_by_tactic lthy
      ((rtac lthy CollectI THEN' CONJ_WRAP' (K (rtac lthy @{thm subset_UNIV})) (1 upto m + n)) 1)
      (mor_fold_thm RS morE)) morE_thms;

    val (fold_unique_mor_thms, fold_unique_mor_thm) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor UNIVs ctors active_UNIVs ss fs);
        fun mk_fun_eq f i = HOLogic.mk_eq (f, mk_fold Ts ss i);
        val unique = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_fun_eq fs ks));
        val vars = fold (Variable.add_free_names lthy) [prem, unique] [];
        val unique_mor = Goal.prove_sorry lthy vars [] (Logic.mk_implies (prem, unique))
          (fn {context = ctxt, prems = _} => mk_fold_unique_mor_tac ctxt type_defs
            init_unique_mor_thms Reps mor_comp_thm mor_Abs_thm mor_fold_thm)
          |> Thm.close_derivation \<^here>;
      in
        `split_conj_thm unique_mor
      end;

    val (ctor_fold_unique_thms, ctor_fold_unique_thm) =
      `split_conj_thm (mk_conjIN n RS
        (mor_UNIV_thm RS iffD2 RS fold_unique_mor_thm))

    val fold_ctor_thms =
      map (fn thm => (mor_incl_thm OF replicate n @{thm subset_UNIV}) RS thm RS sym)
        fold_unique_mor_thms;

    val ctor_o_fold_thms =
      let
        val mor = mor_comp_thm OF [mor_fold_thm, mor_str_thm];
      in
        map2 (fn unique => fn fold_ctor =>
          trans OF [mor RS unique, fold_ctor]) fold_unique_mor_thms fold_ctor_thms
      end;

    val timer = time (timer "fold definitions & thms");

    val map_ctors = map2 (fn Ds => fn bnf =>
      Term.list_comb (mk_map_of_bnf Ds (passiveAs @ FTs) (passiveAs @ Ts) bnf,
        map HOLogic.id_const passiveAs @ ctors)) Dss bnfs;

    fun dtor_bind i = nth external_bs (i - 1) |> Binding.prefix_name (dtorN ^ "_");
    val dtor_def_bind = rpair [] o Binding.concealed o Thm.def_binding o dtor_bind;

    fun dtor_spec i = mk_fold Ts map_ctors i;

    val ((dtor_frees, (_, dtor_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i =>
        Local_Theory.define ((dtor_bind i, NoSyn), (dtor_def_bind i, dtor_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_dtors params =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ params) o Morphism.term phi)
        dtor_frees;
    val dtors = mk_dtors params';
    val dtor_defs = map (fn def => HOLogic.mk_obj_eq (Morphism.thm phi def)) dtor_def_frees;

    val ctor_o_dtor_thms = map2 (Local_Defs.fold lthy o single) dtor_defs ctor_o_fold_thms;

    val dtor_o_ctor_thms =
      let
        fun mk_goal dtor ctor FT =
          mk_Trueprop_eq (HOLogic.mk_comp (dtor, ctor), HOLogic.id_const FT);
        val goals = @{map 3} mk_goal dtors ctors FTs;
      in
        @{map 5} (fn goal => fn dtor_def => fn foldx => fn map_comp_id => fn map_cong0L =>
          Goal.prove_sorry lthy [] [] goal
            (fn {context = ctxt, prems = _} => mk_dtor_o_ctor_tac ctxt dtor_def foldx map_comp_id
              map_cong0L ctor_o_fold_thms)
          |> Thm.close_derivation \<^here>)
        goals dtor_defs ctor_fold_thms map_comp_id_thms map_cong0L_thms
      end;

    val dtor_ctor_thms = map (fn thm => thm RS @{thm pointfree_idE}) dtor_o_ctor_thms;
    val ctor_dtor_thms = map (fn thm => thm RS @{thm pointfree_idE}) ctor_o_dtor_thms;

    val bij_dtor_thms =
      map2 (fn thm1 => fn thm2 => @{thm o_bij} OF [thm1, thm2]) ctor_o_dtor_thms dtor_o_ctor_thms;
    val inj_dtor_thms = map (fn thm => thm RS @{thm bij_is_inj}) bij_dtor_thms;
    val surj_dtor_thms = map (fn thm => thm RS @{thm bij_is_surj}) bij_dtor_thms;
    val dtor_nchotomy_thms = map (fn thm => thm RS @{thm surjD}) surj_dtor_thms;
    val dtor_inject_thms = map (fn thm => thm RS @{thm inj_eq}) inj_dtor_thms;
    val dtor_exhaust_thms = map (fn thm => thm RS exE) dtor_nchotomy_thms;

    val bij_ctor_thms =
      map2 (fn thm1 => fn thm2 => @{thm o_bij} OF [thm1, thm2]) dtor_o_ctor_thms ctor_o_dtor_thms;
    val inj_ctor_thms = map (fn thm => thm RS @{thm bij_is_inj}) bij_ctor_thms;
    val surj_ctor_thms = map (fn thm => thm RS @{thm bij_is_surj}) bij_ctor_thms;
    val ctor_nchotomy_thms = map (fn thm => thm RS @{thm surjD}) surj_ctor_thms;
    val ctor_inject_thms = map (fn thm => thm RS @{thm inj_eq}) inj_ctor_thms;
    val ctor_exhaust_thms = map (fn thm => thm RS exE) ctor_nchotomy_thms;

    val timer = time (timer "dtor definitions & thms");

    val (((((((Izs, (Izs1, Izs1'))), (Izs2, Izs2')), xFs), yFs), init_phis), _) =
      lthy
      |> mk_Frees "z" Ts
      ||>> mk_Frees' "z1" Ts
      ||>> mk_Frees' "z2" Ts'
      ||>> mk_Frees "x" FTs
      ||>> mk_Frees "y" FTs'
      ||>> mk_Frees "P" (replicate n (mk_pred1T initT));

    val phis = map2 retype_const_or_free (map mk_pred1T Ts) init_phis;
    val phi2s = map2 retype_const_or_free (map2 mk_pred2T Ts Ts') init_phis;

    val (ctor_induct_thm, induct_params) =
      let
        fun mk_prem phi ctor sets x =
          let
            fun mk_IH phi set z =
              let
                val prem = mk_Trueprop_mem (z, set $ x);
                val concl = HOLogic.mk_Trueprop (phi $ z);
              in
                Logic.all z (Logic.mk_implies (prem, concl))
              end;

            val IHs = @{map 3} mk_IH phis (drop m sets) Izs;
            val concl = HOLogic.mk_Trueprop (phi $ (ctor $ x));
          in
            Logic.all x (Logic.list_implies (IHs, concl))
          end;

        val prems = @{map 4} mk_prem phis ctors FTs_setss xFs;

        fun mk_concl phi z = phi $ z;
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_concl phis Izs));

        val goal = Logic.list_implies (prems, concl);
        val vars = Variable.add_free_names lthy goal [];
      in
        (Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} =>
            mk_ctor_induct_tac ctxt m set_mapss init_induct_thm morE_thms mor_Abs_thm
            Rep_inverses Abs_inverses Reps)
        |> Thm.close_derivation \<^here>,
        rev (Term.add_tfrees goal []))
      end;

    val cTs = map (SOME o Thm.ctyp_of lthy o TFree) induct_params;

    val weak_ctor_induct_thms =
      let fun insts i = (replicate (i - 1) TrueI) @ (asm_rl :: replicate (n - i) TrueI);
      in map (fn i => (ctor_induct_thm OF insts i) RS mk_conjunctN n i) ks end;

    val (ctor_induct2_thm, induct2_params) =
      let
        fun mk_prem phi ctor ctor' sets sets' x y =
          let
            fun mk_IH phi set set' z1 z2 =
              let
                val prem1 = mk_Trueprop_mem (z1, (set $ x));
                val prem2 = mk_Trueprop_mem (z2, (set' $ y));
                val concl = HOLogic.mk_Trueprop (phi $ z1 $ z2);
              in
                fold_rev Logic.all [z1, z2] (Logic.list_implies ([prem1, prem2], concl))
              end;

            val IHs = @{map 5} mk_IH phi2s (drop m sets) (drop m sets') Izs1 Izs2;
            val concl = HOLogic.mk_Trueprop (phi $ (ctor $ x) $ (ctor' $ y));
          in
            fold_rev Logic.all [x, y] (Logic.list_implies (IHs, concl))
          end;

        val prems = @{map 7} mk_prem phi2s ctors ctor's FTs_setss FTs'_setss xFs yFs;

        fun mk_concl phi z1 z2 = phi $ z1 $ z2;
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (@{map 3} mk_concl phi2s Izs1 Izs2));
        fun mk_t phi (z1, z1') (z2, z2') =
          Term.absfree z1' (HOLogic.mk_all (fst z2', snd z2', phi $ z1 $ z2));
        val cts = @{map 3} (SOME o Thm.cterm_of lthy ooo mk_t) phi2s (Izs1 ~~ Izs1') (Izs2 ~~ Izs2');
        val goal = Logic.list_implies (prems, concl);
        val vars = Variable.add_free_names lthy goal [];
      in
        (Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_ctor_induct2_tac ctxt cTs cts ctor_induct_thm
            weak_ctor_induct_thms)
        |> Thm.close_derivation \<^here>,
        rev (Term.add_tfrees goal []))
      end;

    val timer = time (timer "induction");

    fun mk_ctor_map_DEADID_thm ctor_inject map_id0 =
      trans OF [id_apply, iffD2 OF [ctor_inject, map_id0 RS sym]];

    fun mk_ctor_map_unique_DEADID_thm () =
      let
        val (funs, algs) =
          HOLogic.conjuncts (HOLogic.dest_Trueprop (Thm.concl_of ctor_fold_unique_thm))
          |> map_split HOLogic.dest_eq
          ||>  snd o strip_comb o hd
          |> @{apply 2} (map (fst o dest_Var));
        fun mk_fun_insts T ix = Thm.cterm_of lthy (Var (ix, T --> T));
        val theta =
          (funs ~~ @{map 2} mk_fun_insts Ts funs) @ (algs ~~ map (Thm.cterm_of lthy) ctors);
        val ctor_fold_ctors = (ctor_fold_unique_thm OF
          map (fn thm => mk_trans @{thm id_o} (mk_sym (thm RS
            @{thm trans[OF arg_cong2[of _ _ _ _ "(\<circ>)", OF refl] o_id]}))) map_id0s)
          |> split_conj_thm |> map mk_sym;
      in
        infer_instantiate lthy theta ctor_fold_unique_thm
        |> unfold_thms lthy ctor_fold_ctors
        |> Morphism.thm (Local_Theory.target_morphism lthy)
      end;

    fun mk_ctor_Irel_DEADID_thm ctor_inject bnf =
      trans OF [ctor_inject, rel_eq_of_bnf bnf RS @{thm predicate2_eqD} RS sym];

    val IphiTs = map2 mk_pred2T passiveAs passiveBs;
    val Ipsi1Ts = map2 mk_pred2T passiveAs passiveCs;
    val Ipsi2Ts = map2 mk_pred2T passiveCs passiveBs;
    val activephiTs = map2 mk_pred2T activeAs activeBs;
    val activeIphiTs = map2 mk_pred2T Ts Ts';

    val rels = map2 (fn Ds => mk_rel_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;

    (*register new datatypes as BNFs*)
    val (timer, Ibnfs, (ctor_Imap_o_thms, ctor_Imap_thms), ctor_Imap_unique_thm, ctor_Iset_thmss',
        ctor_Irel_thms, Ibnf_notes, lthy) =
      if m = 0 then
        (timer, replicate n DEADID_bnf,
        map_split (`(mk_pointfree2 lthy)) (map2 mk_ctor_map_DEADID_thm ctor_inject_thms map_ids),
        mk_ctor_map_unique_DEADID_thm (),
        replicate n [], map2 mk_ctor_Irel_DEADID_thm ctor_inject_thms bnfs, [], lthy)
      else let
        val fTs = map2 (curry op -->) passiveAs passiveBs;
        val uTs = map2 (curry op -->) Ts Ts';

        val ((((fs, fs'), (AFss, AFss')), (ys, ys')), _) =
          lthy
          |> mk_Frees' "f" fTs
          ||>> mk_Freess' "z" setFTss
          ||>> mk_Frees' "y" passiveAs;

        val map_FTFT's = map2 (fn Ds =>
          mk_map_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;
        fun mk_passive_maps ATs BTs Ts =
          map2 (fn Ds => mk_map_of_bnf Ds (ATs @ Ts) (BTs @ Ts)) Dss bnfs;
        fun mk_map_fold_arg fs Ts ctor fmap =
          HOLogic.mk_comp (ctor, Term.list_comb (fmap, fs @ map HOLogic.id_const Ts));
        fun mk_map Ts fs Ts' ctors mk_maps =
          mk_fold Ts (map2 (mk_map_fold_arg fs Ts') ctors (mk_maps Ts'));
        val pmapsABT' = mk_passive_maps passiveAs passiveBs;
        val fs_maps = map (mk_map Ts fs Ts' ctor's pmapsABT') ks;

        val ls = 1 upto m;
        val setsss = map (mk_setss o mk_set_Ts) passiveAs;

        fun mk_col l T z z' sets =
          let
            fun mk_UN set = mk_Union T $ (set $ z);
          in
            Term.absfree z'
              (mk_union (nth sets (l - 1) $ z,
                Library.foldl1 mk_union (map mk_UN (drop m sets))))
          end;

        val colss = @{map 5} (fn l => fn T => @{map 3} (mk_col l T)) ls passiveAs AFss AFss' setsss;
        val setss_by_range = map (fn cols => map (mk_fold Ts cols) ks) colss;
        val setss_by_bnf = transpose setss_by_range;

        val set_bss =
          map (flat o map2 (fn B => fn b =>
            if member (op =) deads (TFree B) then [] else [b]) resBs) set_bss0;

        val ctor_witss =
          let
            val witss = map2 (fn Ds => fn bnf => mk_wits_of_bnf
              (replicate (nwits_of_bnf bnf) Ds)
              (replicate (nwits_of_bnf bnf) (passiveAs @ Ts)) bnf) Dss bnfs;
            fun close_wit (I, wit) = fold_rev Term.absfree (map (nth ys') I) wit;
            fun wit_apply (arg_I, arg_wit) (fun_I, fun_wit) =
              (union (op =) arg_I fun_I, fun_wit $ arg_wit);

            fun gen_arg support i =
              if i < m then [([i], nth ys i)]
              else maps (mk_wit support (nth ctors (i - m)) (i - m)) (nth support (i - m))
            and mk_wit support ctor i (I, wit) =
              let val args = map (gen_arg (nth_map i (remove (op =) (I, wit)) support)) I;
              in
                (args, [([], wit)])
                |-> fold (map_product wit_apply)
                |> map (apsnd (fn t => ctor $ t))
                |> minimize_wits
              end;
          in
            @{map 3} (fn ctor => fn i => map close_wit o minimize_wits o maps (mk_wit witss ctor i))
              ctors (0 upto n - 1) witss
          end;

        val (lthy, sbd0, sbd0_card_order, sbd0_Cinfinite, set_sbd0ss) =
          if n = 1
          then (lthy, hd bd0s, hd bd0_card_orders, hd bd0_Cinfinites, set_bd0ss)
          else
            let
              val sum_bd0 = Library.foldr1 (uncurry mk_csum) bd0s;
              val sum_bd0T = fst (dest_relT (fastype_of sum_bd0));
              val (sum_bd0T_params, sum_bd0T_params') = `(map TFree) (Term.add_tfreesT sum_bd0T []);

              val sbd0T_bind = mk_internal_b (sum_bdTN ^ "0");

              val ((sbd0T_name, (sbd0T_glob_info, sbd0T_loc_info)), lthy) =
                typedef (sbd0T_bind, sum_bd0T_params', NoSyn)
                  (HOLogic.mk_UNIV sum_bd0T) NONE (fn ctxt =>
                    EVERY' [rtac ctxt exI, rtac ctxt UNIV_I] 1) lthy;

              val sbd0T = Type (sbd0T_name, sum_bd0T_params);
              val Abs_sbd0T = Const (#Abs_name sbd0T_glob_info, sum_bd0T --> sbd0T);

              val sbd0_bind = mk_internal_b (sum_bdN ^ "0");
              val sbd0_def_bind = (Thm.def_binding sbd0_bind, []);

              val sbd0_spec = mk_dir_image sum_bd0 Abs_sbd0T;

              val ((sbd0_free, (_, sbd0_def_free)), (lthy, lthy_old)) =
                lthy
                |> (snd o Local_Theory.begin_nested)
                |> Local_Theory.define ((sbd0_bind, NoSyn), (sbd0_def_bind, sbd0_spec))
                ||> `Local_Theory.end_nested;

              val phi = Proof_Context.export_morphism lthy_old lthy;

              val sbd0_def = HOLogic.mk_obj_eq (Morphism.thm phi sbd0_def_free);
              val sbd0 = Const (fst (Term.dest_Const (Morphism.term phi sbd0_free)),
                mk_relT (`I sbd0T));

              val Abs_sbd0T_inj = mk_Abs_inj_thm (#Abs_inject sbd0T_loc_info);
              val Abs_sbd0T_bij = mk_Abs_bij_thm lthy Abs_sbd0T_inj (#Abs_cases sbd0T_loc_info);

              val sum_Cinfinite = mk_sum_Cinfinite bd0_Cinfinites;
              val sum_Card_order = sum_Cinfinite RS conjunct2;
              val sum_card_order = mk_sum_card_order bd0_card_orders;

              val sbd0_ordIso = @{thm ssubst_Pair_rhs} OF
                [@{thm dir_image} OF [Abs_sbd0T_inj, sum_Card_order], sbd0_def];
              val sbd0_Cinfinite = @{thm Cinfinite_cong} OF [sbd0_ordIso, sum_Cinfinite];

              val sbd0_card_order = @{thm iffD2[OF arg_cong[of _ _ card_order]]} OF
                [sbd0_def, @{thm card_order_dir_image} OF [Abs_sbd0T_bij, sum_card_order]];

              fun mk_set_sbd0 i bd0_Card_order bd0s =
                map (fn thm => @{thm ordLeq_ordIso_trans} OF
                  [bd0_Card_order RS mk_ordLeq_csum n i thm, sbd0_ordIso]) bd0s;
              val set_sbd0ss = @{map 3} mk_set_sbd0 ks bd0_Card_orders set_bd0ss;
            in
              (lthy, sbd0, sbd0_card_order, sbd0_Cinfinite, set_sbd0ss)
            end;

        val (Ibnf_consts, lthy) =
          @{fold_map 9} (fn b => fn map_b => fn rel_b => fn pred_b => fn set_bs => fn mapx =>
              fn sets => fn wits => fn T => fn lthy =>
            define_bnf_consts Hardly_Inline (user_policy Note_Some lthy) false (SOME deads)
              map_b rel_b pred_b set_bs
              (((((((b, T), fold_rev Term.absfree fs' mapx), sets), sbd0), wits), NONE), NONE) lthy)
          bs map_bs rel_bs pred_bs set_bss fs_maps setss_by_bnf ctor_witss Ts lthy;

        val ((((((((((((((Izs, (Izs1, Izs1')), (Izs2, Izs2')), xFs), yFs))), Iphis), Ipsi1s),
            Ipsi2s), fs), fs_copy), us), (ys, ys')), _) =
          lthy
          |> mk_Frees "z" Ts
          ||>> mk_Frees' "z1" Ts
          ||>> mk_Frees' "z2" Ts'
          ||>> mk_Frees "x" FTs
          ||>> mk_Frees "y" FTs'
          ||>> mk_Frees "R" IphiTs
          ||>> mk_Frees "R" Ipsi1Ts
          ||>> mk_Frees "Q" Ipsi2Ts
          ||>> mk_Frees "f" fTs
          ||>> mk_Frees "f" fTs
          ||>> mk_Frees "u" uTs
          ||>> mk_Frees' "y" passiveAs;

        val (_, Iconsts, Iconst_defs, mk_Iconsts) = @{split_list 4} Ibnf_consts;
        val (_, Isetss, Ibds_Ds, Iwitss_Ds, _, _) = @{split_list 6} Iconsts;
        val (Imap_defs, Iset_defss, Ibd_defs, Iwit_defss, Irel_defs, Ipred_defs) =
          @{split_list 6} Iconst_defs;
        val (mk_Imaps_Ds, mk_It_Ds, _, mk_Irels_Ds, mk_Ipreds_Ds, _, _) =
          @{split_list 7} mk_Iconsts;

        val Irel_unabs_defs = map (fn def => mk_unabs_def m (HOLogic.mk_obj_eq def)) Irel_defs;
        val Ipred_unabs_defs = map (fn def => mk_unabs_def m (HOLogic.mk_obj_eq def)) Ipred_defs;
        val Iset_defs = flat Iset_defss;

        fun mk_Imaps As Bs = map (fn mk => mk deads As Bs) mk_Imaps_Ds;
        fun mk_Isetss As = map2 (fn mk => fn Isets => map (mk deads As) Isets) mk_It_Ds Isetss;
        val Ibds = map2 (fn mk => mk deads passiveAs) mk_It_Ds Ibds_Ds;
        val Iwitss =
          map2 (fn mk => fn Iwits => map (mk deads passiveAs o snd) Iwits) mk_It_Ds Iwitss_Ds;
        fun mk_Irels As Bs = map (fn mk => mk deads As Bs) mk_Irels_Ds;
        fun mk_Ipreds As = map (fn mk => mk deads As) mk_Ipreds_Ds;

        val Imaps = mk_Imaps passiveAs passiveBs;
        val fs_Imaps = map (fn m => Term.list_comb (m, fs)) Imaps;
        val fs_copy_Imaps = map (fn m => Term.list_comb (m, fs_copy)) Imaps;
        val (Isetss_by_range, Isetss_by_bnf) = `transpose (mk_Isetss passiveAs);

        val map_setss = map (fn T => map2 (fn Ds =>
          mk_map_of_bnf Ds (passiveAs @ Ts) (mk_set_Ts T)) Dss bnfs) passiveAs;

        val timer = time (timer "bnf constants for the new datatypes");

        val (ctor_Imap_thms, ctor_Imap_o_thms) =
          let
            fun mk_goal fs_map map ctor ctor' =
              mk_Trueprop_eq (HOLogic.mk_comp (fs_map, ctor),
                HOLogic.mk_comp (ctor', Term.list_comb (map, fs @ fs_Imaps)));
            val goals = @{map 4} mk_goal fs_Imaps map_FTFT's ctors ctor's;
            val maps =
              @{map 4} (fn goal => fn foldx => fn map_comp_id => fn map_cong0 =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Imap_defs THEN
                    mk_map_tac ctxt m n foldx map_comp_id map_cong0))
                |> Thm.close_derivation \<^here>)
              goals ctor_fold_thms map_comp_id_thms map_cong0s;
          in
            `(map (fn thm => thm RS @{thm comp_eq_dest})) maps
          end;

        val (ctor_Imap_unique_thms, ctor_Imap_unique_thm) =
          let
            fun mk_prem u map ctor ctor' =
              mk_Trueprop_eq (HOLogic.mk_comp (u, ctor),
                HOLogic.mk_comp (ctor', Term.list_comb (map, fs @ us)));
            val prems = @{map 4} mk_prem us map_FTFT's ctors ctor's;
            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map2 (curry HOLogic.mk_eq) us fs_Imaps));
            val vars = fold (Variable.add_free_names lthy) (goal :: prems) [];
            val unique = Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, goal))
              (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Imap_defs THEN
                mk_ctor_map_unique_tac ctxt ctor_fold_unique_thm sym_map_comps)
              |> Thm.close_derivation \<^here>;
          in
            `split_conj_thm unique
          end;

        val timer = time (timer "map functions for the new datatypes");

        val ctor_Iset_thmss =
          let
            fun mk_goal sets ctor set col map =
              mk_Trueprop_eq (HOLogic.mk_comp (set, ctor),
                HOLogic.mk_comp (col, Term.list_comb (map, passive_ids @ sets)));
            val goalss =
              @{map 3} (fn sets => @{map 4} (mk_goal sets) ctors sets)
                Isetss_by_range colss map_setss;
            val setss = map (map2 (fn foldx => fn goal =>
                Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
                  unfold_thms_tac ctxt Iset_defs THEN mk_set_tac ctxt foldx)
                |> Thm.close_derivation \<^here>)
              ctor_fold_thms) goalss;

            fun mk_simp_goal pas_set act_sets sets ctor z set =
              mk_Trueprop_eq (set $ (ctor $ z),
                mk_union (pas_set $ z,
                  Library.foldl1 mk_union (map2 (fn X => mk_UNION (X $ z)) act_sets sets)));
            val simp_goalss =
              map2 (fn i => fn sets =>
                @{map 4} (fn Fsets => mk_simp_goal (nth Fsets (i - 1)) (drop m Fsets) sets)
                  FTs_setss ctors xFs sets)
                ls Isetss_by_range;

            val ctor_setss = @{map 3} (fn i => @{map 3} (fn set_nats => fn goal => fn set =>
              Variable.add_free_names lthy goal []
              |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} =>
                    mk_ctor_set_tac ctxt set (nth set_nats (i - 1)) (drop m set_nats)))
                |> Thm.close_derivation \<^here>)
              set_mapss) ls simp_goalss setss;
          in
            ctor_setss
          end;

        fun mk_set_thms ctor_set = (@{thm xt1(3)} OF [ctor_set, @{thm Un_upper1}]) ::
          map (fn i => (@{thm xt1(3)} OF [ctor_set, @{thm Un_upper2}]) RS
            (mk_Un_upper n i RS subset_trans) RSN
            (2, @{thm UN_upper} RS subset_trans))
            (1 upto n);
        val set_Iset_thmsss = transpose (map (map mk_set_thms) ctor_Iset_thmss);

        val timer = time (timer "set functions for the new datatypes");

        val cxs = map (SOME o Thm.cterm_of lthy) Izs;
        val Isetss_by_range' =
          map (map (Term.subst_atomic_types (passiveAs ~~ passiveBs))) Isetss_by_range;

        val Iset_Imap0_thmss =
          let
            fun mk_set_map0 f map z set set' =
              HOLogic.mk_eq (mk_image f $ (set $ z), set' $ (map $ z));

            fun mk_cphi f map z set set' = Thm.cterm_of lthy
              (Term.absfree (dest_Free z) (mk_set_map0 f map z set set'));

            val csetss = map (map (Thm.cterm_of lthy)) Isetss_by_range';

            val cphiss = @{map 3} (fn f => fn sets => fn sets' =>
              (@{map 4} (mk_cphi f) fs_Imaps Izs sets sets')) fs Isetss_by_range Isetss_by_range';

            val inducts = map (fn cphis =>
              Thm.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm) cphiss;

            val goals =
              @{map 3} (fn f => fn sets => fn sets' =>
                HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                  (@{map 4} (mk_set_map0 f) fs_Imaps Izs sets sets')))
                  fs Isetss_by_range Isetss_by_range';

            fun mk_tac ctxt induct = mk_set_nat_tac ctxt m (rtac ctxt induct) set_mapss ctor_Imap_thms;
            val thms =
              @{map 5} (fn goal => fn csets => fn ctor_sets => fn induct => fn i =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} => mk_tac ctxt induct csets ctor_sets i))
                |> Thm.close_derivation \<^here>)
              goals csetss ctor_Iset_thmss inducts ls;
          in
            map split_conj_thm thms
          end;

        val Iset_bd_thmss =
          let
            fun mk_set_bd z bd set = mk_ordLeq (mk_card_of (set $ z)) bd;

            fun mk_cphi z set = Thm.cterm_of lthy (Term.absfree (dest_Free z) (mk_set_bd z sbd0 set));

            val cphiss = map (map2 mk_cphi Izs) Isetss_by_range;

            val inducts = map (fn cphis =>
              Thm.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm) cphiss;

            val goals =
              map (fn sets =>
                HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                  (@{map 3} mk_set_bd Izs Ibds sets))) Isetss_by_range;

            fun mk_tac ctxt induct = mk_set_bd_tac ctxt m (rtac ctxt induct) sbd0_Cinfinite set_sbd0ss;
            val thms =
              @{map 4} (fn goal => fn ctor_sets => fn induct => fn i =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                    (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Ibd_defs THEN
                      mk_tac ctxt induct ctor_sets i))
                |> Thm.close_derivation \<^here>)
              goals ctor_Iset_thmss inducts ls;
          in
            map split_conj_thm thms
          end;

        val Imap_cong0_thms =
          let
            fun mk_prem z set f g y y' =
              mk_Ball (set $ z) (Term.absfree y' (HOLogic.mk_eq (f $ y, g $ y)));

            fun mk_map_cong0 sets z fmap gmap =
              HOLogic.mk_imp
                (Library.foldr1 HOLogic.mk_conj (@{map 5} (mk_prem z) sets fs fs_copy ys ys'),
                HOLogic.mk_eq (fmap $ z, gmap $ z));

            fun mk_cphi sets z fmap gmap =
              Thm.cterm_of lthy (Term.absfree (dest_Free z) (mk_map_cong0 sets z fmap gmap));

            val cphis = @{map 4} mk_cphi Isetss_by_bnf Izs fs_Imaps fs_copy_Imaps;

            val induct = Thm.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm;

            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (@{map 4} mk_map_cong0 Isetss_by_bnf Izs fs_Imaps fs_copy_Imaps));
            val vars = Variable.add_free_names lthy goal [];

            val thm = Goal.prove_sorry lthy vars [] goal
                (fn {context = ctxt, prems = _} => mk_mcong_tac ctxt (rtac ctxt induct) set_Iset_thmsss
                  map_cong0s ctor_Imap_thms)
              |> Thm.close_derivation \<^here>;
          in
            split_conj_thm thm
          end;

        val in_rels = map in_rel_of_bnf bnfs;
        val in_Irels = map (fn def => trans OF [def, @{thm OO_Grp_alt}] RS @{thm predicate2_eqD})
            Irel_unabs_defs;

        val ctor_Iset_incl_thmss = map (map hd) set_Iset_thmsss;
        val ctor_set_Iset_incl_thmsss = map (transpose o map tl) set_Iset_thmsss;
        val ctor_Iset_thmss' = transpose ctor_Iset_thmss;

        val Irels = mk_Irels passiveAs passiveBs;
        val Ipreds = mk_Ipreds passiveAs;
        val Irelphis = map (fn rel => Term.list_comb (rel, Iphis)) Irels;
        val relphis = map (fn rel => Term.list_comb (rel, Iphis @ Irelphis)) rels;
        val Irelpsi1s = map (fn rel => Term.list_comb (rel, Ipsi1s)) (mk_Irels passiveAs passiveCs);
        val Irelpsi2s = map (fn rel => Term.list_comb (rel, Ipsi2s)) (mk_Irels passiveCs passiveBs);
        val Irelpsi12s = map (fn rel =>
            Term.list_comb (rel, map2 (curry mk_rel_compp) Ipsi1s Ipsi2s)) Irels;

        val ctor_Irel_thms =
          let
            fun mk_goal xF yF ctor ctor' Irelphi relphi =
              mk_Trueprop_eq (Irelphi $ (ctor $ xF) $ (ctor' $ yF), relphi $ xF $ yF);
            val goals = @{map 6} mk_goal xFs yFs ctors ctor's Irelphis relphis;
          in
            @{map 12} (fn i => fn goal => fn in_rel => fn map_comp0 => fn map_cong0 =>
              fn ctor_map => fn ctor_sets => fn ctor_inject => fn ctor_dtor =>
              fn set_map0s => fn ctor_set_incls => fn ctor_set_set_inclss =>
              Variable.add_free_names lthy goal []
              |> (fn vars => Goal.prove_sorry lthy vars [] goal
               (fn {context = ctxt, prems = _} =>
                 mk_ctor_rel_tac ctxt in_Irels i in_rel map_comp0 map_cong0 ctor_map ctor_sets
                   ctor_inject ctor_dtor set_map0s ctor_set_incls ctor_set_set_inclss))
              |> Thm.close_derivation \<^here>)
            ks goals in_rels map_comps map_cong0s ctor_Imap_thms ctor_Iset_thmss'
              ctor_inject_thms ctor_dtor_thms set_mapss ctor_Iset_incl_thmss
              ctor_set_Iset_incl_thmsss
          end;

        val le_Irel_OO_thm =
          let
            fun mk_le_Irel_OO Irelpsi1 Irelpsi2 Irelpsi12 Iz1 Iz2 =
              HOLogic.mk_imp (mk_rel_compp (Irelpsi1, Irelpsi2) $ Iz1 $ Iz2,
                Irelpsi12 $ Iz1 $ Iz2);
            val goals = @{map 5} mk_le_Irel_OO Irelpsi1s Irelpsi2s Irelpsi12s Izs1 Izs2;

            val cTs = map (SOME o Thm.ctyp_of lthy o TFree) induct2_params;
            val cxs = map (SOME o Thm.cterm_of lthy) (splice Izs1 Izs2);
            fun mk_cphi z1 z2 goal = SOME (Thm.cterm_of lthy (Term.absfree z1 (Term.absfree z2 goal)));
            val cphis = @{map 3} mk_cphi Izs1' Izs2' goals;
            val induct = Thm.instantiate' cTs (cphis @ cxs) ctor_induct2_thm;

            val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj goals);
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} => mk_le_rel_OO_tac ctxt m induct ctor_nchotomy_thms
                ctor_Irel_thms rel_mono_strong0s le_rel_OOs)
            |> Thm.close_derivation \<^here>
          end;

        val timer = time (timer "helpers for BNF properties");

        val map_id0_tacs = map (fn thm => fn ctxt => mk_map_id0_tac ctxt map_id0s thm)
          ctor_Imap_unique_thms;
        val map_comp0_tacs =
          map2 (fn thm => fn i => fn ctxt =>
            mk_map_comp0_tac ctxt map_comps ctor_Imap_thms thm i)
          ctor_Imap_unique_thms ks;
        val map_cong0_tacs = map (fn thm => fn ctxt => mk_map_cong0_tac ctxt m thm) Imap_cong0_thms;
        val set_map0_tacss = map (map (fn thm => fn ctxt => mk_set_map0_tac ctxt thm))
          (transpose Iset_Imap0_thmss);
        val bd_co_tacs = replicate n (fn ctxt =>
          unfold_thms_tac ctxt Ibd_defs THEN rtac ctxt sbd0_card_order 1);
        val bd_cinf_tacs = replicate n (fn ctxt =>
          unfold_thms_tac ctxt Ibd_defs THEN rtac ctxt (sbd0_Cinfinite RS conjunct1) 1);
        val set_bd_tacss = map (map (fn thm => fn ctxt => rtac ctxt thm 1)) (transpose Iset_bd_thmss);
        val le_rel_OO_tacs = map (fn i => fn ctxt =>
          (rtac ctxt @{thm predicate2I} THEN' etac ctxt (le_Irel_OO_thm RS mk_conjunctN n i RS mp)) 1) ks;

        val rel_OO_Grp_tacs = map (fn def => fn ctxt => rtac ctxt def 1) Irel_unabs_defs;

        val pred_set_tacs = map (fn def => fn ctxt => rtac ctxt def 1) Ipred_unabs_defs;

        val tacss = @{map 10} zip_axioms map_id0_tacs map_comp0_tacs map_cong0_tacs set_map0_tacss
          bd_co_tacs bd_cinf_tacs set_bd_tacss le_rel_OO_tacs rel_OO_Grp_tacs pred_set_tacs;

        fun wit_tac ctxt = unfold_thms_tac ctxt (flat Iwit_defss) THEN
          mk_wit_tac ctxt n (flat ctor_Iset_thmss) (maps wit_thms_of_bnf bnfs);

        val (Ibnfs, lthy) =
          @{fold_map 6} (fn tacs => fn map_b => fn rel_b => fn pred_b => fn set_bs => fn consts =>
            bnf_def Do_Inline (user_policy Note_Some) false I tacs wit_tac (SOME deads)
              map_b rel_b pred_b set_bs consts)
          tacss map_bs rel_bs pred_bs set_bss
            (((((((replicate n Binding.empty ~~ Ts) ~~ Imaps) ~~ Isetss_by_bnf) ~~ Ibds) ~~
              Iwitss) ~~ map SOME Irels) ~~ map SOME Ipreds) lthy;

        val timer = time (timer "registered new datatypes as BNFs");

        val ls' = if m = 1 then [0] else ls

        val Ibnf_common_notes =
          [(ctor_map_uniqueN, [ctor_Imap_unique_thm])]
          |> map (fn (thmN, thms) =>
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

        val Ibnf_notes =
          [(ctor_mapN, map single ctor_Imap_thms),
          (ctor_relN, map single ctor_Irel_thms),
          (ctor_set_inclN, ctor_Iset_incl_thmss),
          (ctor_set_set_inclN, map flat ctor_set_Iset_incl_thmsss)] @
          map2 (fn i => fn thms => (mk_ctor_setN i, map single thms)) ls' ctor_Iset_thmss
          |> maps (fn (thmN, thmss) =>
            map2 (fn b => fn thms =>
              ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
            bs thmss)
      in
        (timer, Ibnfs, (ctor_Imap_o_thms, ctor_Imap_thms), ctor_Imap_unique_thm, ctor_Iset_thmss',
          ctor_Irel_thms, Ibnf_common_notes @ Ibnf_notes, lthy)
      end;

    val ((((((xFs, yFs)), Iphis), activephis), activeIphis), _) =
      lthy
      |> mk_Frees "x" FTs
      ||>> mk_Frees "y" FTs'
      ||>> mk_Frees "R" IphiTs
      ||>> mk_Frees "S" activephiTs
      ||>> mk_Frees "IR" activeIphiTs;

    val ctor_fold_o_Imap_thms = mk_xtor_co_iter_o_map_thms Least_FP false m ctor_fold_unique_thm
      ctor_Imap_o_thms (map (mk_pointfree2 lthy) ctor_fold_thms) sym_map_comps map_cong0s;

    val Irels = if m = 0 then map HOLogic.eq_const Ts
      else map (mk_rel_of_bnf deads passiveAs passiveBs) Ibnfs;
    val Irel_induct_thm =
      mk_xtor_rel_co_induct_thm Least_FP rels activeIphis Irels Iphis xFs yFs ctors ctor's
        (fn {context = ctxt, prems = IHs} => mk_rel_induct_tac ctxt IHs m ctor_induct2_thm ks
           ctor_Irel_thms rel_mono_strong0s) lthy;

    val rels = map2 (fn Ds => mk_rel_of_bnf Ds allAs allBs') Dss bnfs;
    val ctor_fold_transfer_thms =
      mk_xtor_co_iter_transfer_thms Least_FP rels activephis activephis Irels Iphis
        (mk_folds passiveAs activeAs) (mk_folds passiveBs activeBs)
        (fn {context = ctxt, prems = _} => mk_fold_transfer_tac ctxt m Irel_induct_thm
          (map map_transfer_of_bnf bnfs) ctor_fold_thms)
        lthy;

    val timer = time (timer "relator induction");

    fun mk_Ts As = map (typ_subst_atomic (passiveAs ~~ As)) Ts;
    val export = map (Morphism.term (Local_Theory.target_morphism lthy))
    val ((recs, (ctor_rec_thms, ctor_rec_unique_thm, ctor_rec_o_Imap_thms, ctor_rec_transfer_thms)),
        lthy) = lthy
      |> derive_xtor_co_recs Least_FP external_bs mk_Ts (Dss, resDs) bnfs
        (export ctors) (export folds)
        ctor_fold_unique_thm ctor_fold_thms ctor_fold_transfer_thms ctor_Imap_thms ctor_Irel_thms
        (replicate n NONE);

    val timer = time (timer "recursor");

    val common_notes =
      [(ctor_inductN, [ctor_induct_thm]),
      (ctor_induct2N, [ctor_induct2_thm]),
      (ctor_rel_inductN, [Irel_induct_thm])]
      |> map (fn (thmN, thms) =>
        ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

    val notes =
      [(ctor_dtorN, ctor_dtor_thms),
      (ctor_exhaustN, ctor_exhaust_thms),
      (ctor_foldN, ctor_fold_thms),
      (ctor_fold_o_mapN, ctor_fold_o_Imap_thms),
      (ctor_fold_transferN, ctor_fold_transfer_thms),
      (ctor_fold_uniqueN, ctor_fold_unique_thms),
      (ctor_injectN, ctor_inject_thms),
      (dtor_ctorN, dtor_ctor_thms),
      (dtor_exhaustN, dtor_exhaust_thms),
      (dtor_injectN, dtor_inject_thms)]
      |> map (apsnd (map single))
      |> maps (fn (thmN, thmss) =>
        map2 (fn b => fn thms =>
          ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
        bs thmss);

    val lthy' = lthy |> internals ? snd o Local_Theory.notes (common_notes @ notes @ Ibnf_notes);

    val fp_res =
      {Ts = Ts, bnfs = Ibnfs, pre_bnfs = bnfs, absT_infos = absT_infos,
       ctors = ctors, dtors = dtors, xtor_un_folds = folds, xtor_co_recs = export recs,
       xtor_co_induct = ctor_induct_thm, dtor_ctors = dtor_ctor_thms,
       ctor_dtors = ctor_dtor_thms, ctor_injects = ctor_inject_thms,
       dtor_injects = dtor_inject_thms, xtor_maps = ctor_Imap_thms,
       xtor_map_unique = ctor_Imap_unique_thm, xtor_setss = ctor_Iset_thmss',
       xtor_rels = ctor_Irel_thms, xtor_un_fold_thms = ctor_fold_thms,
       xtor_co_rec_thms = ctor_rec_thms, xtor_un_fold_unique = ctor_fold_unique_thm,
       xtor_co_rec_unique = ctor_rec_unique_thm,
       xtor_un_fold_o_maps = ctor_fold_o_Imap_thms,
       xtor_co_rec_o_maps = ctor_rec_o_Imap_thms,
       xtor_un_fold_transfers = ctor_fold_transfer_thms,
       xtor_co_rec_transfers = ctor_rec_transfer_thms, xtor_rel_co_induct = Irel_induct_thm,
       dtor_set_inducts = []};
  in
    timer; (fp_res, lthy')
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>datatype\<close> "define inductive datatypes"
    (parse_co_datatype_cmd Least_FP construct_lfp);

end;
