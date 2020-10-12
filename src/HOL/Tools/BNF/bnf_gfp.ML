(*  Title:      HOL/Tools/BNF/bnf_gfp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Codatatype construction.
*)

signature BNF_GFP =
sig
  val construct_gfp: mixfix list -> binding list -> binding list -> binding list ->
    binding list list -> binding list -> (string * sort) list -> typ list * typ list list ->
    BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory ->
    BNF_FP_Util.fp_result * local_theory
end;

structure BNF_GFP : BNF_GFP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_Comp
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_GFP_Util
open BNF_GFP_Tactics

datatype wit_tree = Wit_Leaf of int | Wit_Node of (int * int * int list) * wit_tree list;

fun mk_tree_args (I, T) (I', Ts) = (sort_distinct int_ord (I @ I'), T :: Ts);

fun finish Iss m seen i (nwit, I) =
  let
    val treess = map (fn j =>
        if j < m orelse member (op =) seen j then [([j], Wit_Leaf j)]
        else
          map_index (finish Iss m (insert (op =) j seen) j) (nth Iss (j - m))
          |> flat
          |> minimize_wits)
      I;
  in
    map (fn (I, t) => (I, Wit_Node ((i - m, nwit, filter (fn i => i < m) I), t)))
      (fold_rev (map_product mk_tree_args) treess [([], [])])
    |> minimize_wits
  end;

fun tree_to_ctor_wit vars _ _ (Wit_Leaf j) = ([j], nth vars j)
  | tree_to_ctor_wit vars ctors witss (Wit_Node ((i, nwit, I), subtrees)) =
     (I, nth ctors i $ (Term.list_comb (snd (nth (nth witss i) nwit),
       map (snd o tree_to_ctor_wit vars ctors witss) subtrees)));

fun tree_to_coind_wits _ (Wit_Leaf _) = []
  | tree_to_coind_wits lwitss (Wit_Node ((i, nwit, I), subtrees)) =
     ((i, I), nth (nth lwitss i) nwit) :: maps (tree_to_coind_wits lwitss) subtrees;

(*all BNFs have the same lives*)
fun construct_gfp mixfixes map_bs rel_bs pred_bs set_bss0 bs resBs (resDs, Dss) bnfs absT_infos
    lthy =
  let
    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    val live = live_of_bnf (hd bnfs);
    val n = length bnfs; (*active*)
    val ks = 1 upto n;
    val m = live - n; (*passive, if 0 don't generate a new BNF*)
    val ls = 1 upto m;

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
    val ((((((passiveAs, activeAs), passiveBs), activeBs), passiveCs), activeCs), idxT) = names_lthy
      |> variant_tfrees passives
      ||>> mk_TFrees n
      ||>> variant_tfrees passives
      ||>> mk_TFrees n
      ||>> mk_TFrees m
      ||>> mk_TFrees n
      ||> fst o mk_TFrees 1
      ||> the_single;

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
    val ATs = map HOLogic.mk_setT passiveAs;
    val BTs = map HOLogic.mk_setT activeAs;
    val B'Ts = map HOLogic.mk_setT activeBs;
    val B''Ts = map HOLogic.mk_setT activeCs;
    val sTs = map2 (fn T => fn U => T --> U) activeAs FTsAs;
    val s'Ts = map2 (fn T => fn U => T --> U) activeBs FTsBs;
    val s''Ts = map2 (fn T => fn U => T --> U) activeCs FTsCs;
    val fTs = map2 (fn T => fn U => T --> U) activeAs activeBs;
    val self_fTs = map (fn T => T --> T) activeAs;
    val gTs = map2 (fn T => fn U => T --> U) activeBs activeCs;
    val all_gTs = map2 (fn T => fn U => T --> U) allBs allCs';
    val RTs = map2 (fn T => fn U => HOLogic.mk_prodT (T, U)) activeAs activeBs;
    val sRTs = map2 (fn T => fn U => HOLogic.mk_prodT (T, U)) activeAs activeAs;
    val R'Ts = map2 (fn T => fn U => HOLogic.mk_prodT (T, U)) activeBs activeCs;
    val setsRTs = map HOLogic.mk_setT sRTs;
    val setRTs = map HOLogic.mk_setT RTs;
    val all_sbisT = HOLogic.mk_tupleT setsRTs;
    val setR'Ts = map HOLogic.mk_setT R'Ts;
    val FRTs = mk_FTs (passiveAs @ RTs);

    (* terms *)
    val mapsAsAs = @{map 4} mk_map_of_bnf Dss Ass Ass bnfs;
    val mapsAsBs = @{map 4} mk_map_of_bnf Dss Ass Bss bnfs;
    val mapsBsCs' = @{map 4} mk_map_of_bnf Dss Bss Css' bnfs;
    val mapsAsCs' = @{map 4} mk_map_of_bnf Dss Ass Css' bnfs;
    val map_fsts = @{map 4} mk_map_of_bnf Dss (replicate n (passiveAs @ RTs)) Ass bnfs;
    val map_snds = @{map 4} mk_map_of_bnf Dss (replicate n (passiveAs @ RTs)) Bss bnfs;
    fun mk_setss Ts = @{map 3} mk_sets_of_bnf (map (replicate live) Dss)
      (map (replicate live) (replicate n Ts)) bnfs;
    val setssAs = mk_setss allAs;
    val setssAs' = transpose setssAs;
    val bis_setss = mk_setss (passiveAs @ RTs);
    val relsAsBs = @{map 4} mk_rel_of_bnf Dss Ass Bss bnfs;
    val bds = @{map 3} mk_bd_of_bnf Dss Ass bnfs;
    val sum_bd = Library.foldr1 (uncurry mk_csum) bds;
    val sum_bdT = fst (dest_relT (fastype_of sum_bd));
    val (sum_bdT_params, sum_bdT_params') = `(map TFree) (Term.add_tfreesT sum_bdT []);

    val ((((((((((zs, zs'), Bs), ss), fs), self_fs), all_gs), xFs), yFs), yFs_copy), _) =
      lthy
      |> mk_Frees' "b" activeAs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" self_fTs
      ||>> mk_Frees "g" all_gTs
      ||>> mk_Frees "x" FTsAs
      ||>> mk_Frees "y" FTsBs
      ||>> mk_Frees "y" FTsBs;

    val passive_UNIVs = map HOLogic.mk_UNIV passiveAs;
    val passive_eqs = map HOLogic.eq_const passiveAs;
    val active_UNIVs = map HOLogic.mk_UNIV activeAs;
    val passive_ids = map HOLogic.id_const passiveAs;
    val active_ids = map HOLogic.id_const activeAs;
    val fsts = map fst_const RTs;
    val snds = map snd_const RTs;

    (* thms *)
    val bd_card_orders = map bd_card_order_of_bnf bnfs;
    val bd_card_order = hd bd_card_orders
    val bd_Card_orders = map bd_Card_order_of_bnf bnfs;
    val bd_Card_order = hd bd_Card_orders;
    val bd_Cinfinites = map bd_Cinfinite_of_bnf bnfs;
    val bd_Cinfinite = hd bd_Cinfinites;
    val in_monos = map in_mono_of_bnf bnfs;
    val map_comp0s = map map_comp0_of_bnf bnfs;
    val sym_map_comps = map mk_sym map_comp0s;
    val map_comps = map map_comp_of_bnf bnfs;
    val map_cong0s = map map_cong0_of_bnf bnfs;
    val map_id0s = map map_id0_of_bnf bnfs;
    val map_ids = map map_id_of_bnf bnfs;
    val set_bdss = map set_bd_of_bnf bnfs;
    val set_mapss = map set_map_of_bnf bnfs;
    val rel_congs = map rel_cong0_of_bnf bnfs;
    val rel_converseps = map rel_conversep_of_bnf bnfs;
    val rel_Grps = map rel_Grp_of_bnf bnfs;
    val le_rel_OOs = map le_rel_OO_of_bnf bnfs;
    val in_rels = map in_rel_of_bnf bnfs;

    val timer = time (timer "Extracted terms & thms");

    (* derived thms *)

    (*map g1 ... gm g(m+1) ... g(m+n) (map id ... id f(m+1) ... f(m+n) x) =
      map g1 ... gm (g(m+1) o f(m+1)) ... (g(m+n) o f(m+n)) x*)
    fun mk_map_comp_id x mapAsBs mapBsCs mapAsCs map_comp0 =
      let
        val lhs = Term.list_comb (mapBsCs, all_gs) $
          (Term.list_comb (mapAsBs, passive_ids @ fs) $ x);
        val rhs =
          Term.list_comb (mapAsCs, take m all_gs @ map HOLogic.mk_comp (drop m all_gs ~~ fs)) $ x;
        val goal = mk_Trueprop_eq (lhs, rhs);
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_map_comp_id_tac ctxt map_comp0)
        |> Thm.close_derivation \<^here>
      end;

    val map_comp_id_thms = @{map 5} mk_map_comp_id xFs mapsAsBs mapsBsCs' mapsAsCs' map_comps;

    (*forall a : set(m+1) x. f(m+1) a = a; ...; forall a : set(m+n) x. f(m+n) a = a ==>
      map id ... id f(m+1) ... f(m+n) x = x*)
    fun mk_map_cong0L x mapAsAs sets map_cong0 map_id =
      let
        fun mk_prem set f z z' =
          HOLogic.mk_Trueprop
            (mk_Ball (set $ x) (Term.absfree z' (HOLogic.mk_eq (f $ z, z))));
        val prems = @{map 4} mk_prem (drop m sets) self_fs zs zs';
        val goal = mk_Trueprop_eq (Term.list_comb (mapAsAs, passive_ids @ self_fs) $ x, x);
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, goal))
          (fn {context = ctxt, prems = _} => mk_map_cong0L_tac ctxt m map_cong0 map_id)
        |> Thm.close_derivation \<^here>
      end;

    val map_cong0L_thms = @{map 5} mk_map_cong0L xFs mapsAsAs setssAs map_cong0s map_ids;
    val in_mono'_thms = map (fn thm =>
      (thm OF (replicate m subset_refl)) RS @{thm set_mp}) in_monos;

    val map_arg_cong_thms =
      let
        val prems = map2 (curry mk_Trueprop_eq) yFs yFs_copy;
        val maps = map (fn mapx => Term.list_comb (mapx, all_gs)) mapsBsCs';
        val concls =
          @{map 3} (fn x => fn y => fn mapx => mk_Trueprop_eq (mapx $ x, mapx $ y))
            yFs yFs_copy maps;
        val goals = map2 (fn prem => fn concl => Logic.mk_implies (prem, concl)) prems concls;
      in
        map (fn goal =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            (hyp_subst_tac ctxt THEN' rtac ctxt refl) 1))
          |> Thm.close_derivation \<^here>)
        goals
      end;

    val timer = time (timer "Derived simple theorems");

    (* coalgebra *)

    val coalg_bind = mk_internal_b (coN ^ algN) ;
    val coalg_def_bind = (Thm.def_binding coalg_bind, []);

    (*forall i = 1 ... n: (\<forall>x \<in> Bi. si \<in> Fi_in UNIV .. UNIV B1 ... Bn)*)
    val coalg_spec =
      let
        val ins = @{map 3} mk_in (replicate n (passive_UNIVs @ Bs)) setssAs FTsAs;
        fun mk_coalg_conjunct B s X z z' =
          mk_Ball B (Term.absfree z' (HOLogic.mk_mem (s $ z, X)));

        val rhs = Library.foldr1 HOLogic.mk_conj (@{map 5} mk_coalg_conjunct Bs ss ins zs zs')
      in
        fold_rev (Term.absfree o Term.dest_Free) (Bs @ ss) rhs
      end;

    val ((coalg_free, (_, coalg_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((coalg_bind, NoSyn), (coalg_def_bind, coalg_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val coalg = fst (Term.dest_Const (Morphism.term phi coalg_free));
    val coalg_def = mk_unabs_def (2 * n) (HOLogic.mk_obj_eq (Morphism.thm phi coalg_def_free));

    fun mk_coalg Bs ss =
      let
        val args = Bs @ ss;
        val Ts = map fastype_of args;
        val coalgT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (coalg, coalgT), args)
      end;

    val((((((zs, zs'), Bs), B's), ss), s's), _) =
      lthy
      |> mk_Frees' "b" activeAs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "s'" s'Ts;

    val coalg_prem = HOLogic.mk_Trueprop (mk_coalg Bs ss);

    val coalg_in_thms = map (fn i =>
      coalg_def RS iffD1 RS mk_conjunctN n i RS bspec) ks

    val coalg_set_thmss =
      let
        val coalg_prem = HOLogic.mk_Trueprop (mk_coalg Bs ss);
        fun mk_prem x B = mk_Trueprop_mem (x, B);
        fun mk_concl s x B set = HOLogic.mk_Trueprop (mk_leq (set $ (s $ x)) B);
        val prems = map2 mk_prem zs Bs;
        val conclss = @{map 3} (fn s => fn x => fn sets => map2 (mk_concl s x) Bs (drop m sets))
          ss zs setssAs;
        val goalss = map2 (fn prem => fn concls => map (fn concl =>
          Logic.list_implies (coalg_prem :: [prem], concl)) concls) prems conclss;
      in
        map (fn goals => map (fn goal =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            mk_coalg_set_tac ctxt coalg_def))
          |> Thm.close_derivation \<^here>)
        goals) goalss
      end;

    fun mk_tcoalg BTs = mk_coalg (map HOLogic.mk_UNIV BTs);

    val tcoalg_thm =
      let
        val goal = HOLogic.mk_Trueprop (mk_tcoalg activeAs ss);
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => (rtac ctxt (coalg_def RS iffD2) 1 THEN CONJ_WRAP
            (K (EVERY' [rtac ctxt ballI, rtac ctxt CollectI,
              CONJ_WRAP' (K (EVERY' [rtac ctxt @{thm subset_UNIV}])) allAs] 1)) ss))
        |> Thm.close_derivation \<^here>
      end;

    val timer = time (timer "Coalgebra definition & thms");

    (* morphism *)

    val mor_bind = mk_internal_b morN;
    val mor_def_bind = (Thm.def_binding mor_bind, []);

    (*fbetw) forall i = 1 ... n: (\<forall>x \<in> Bi. fi x \<in> B'i)*)
    (*mor) forall i = 1 ... n: (\<forall>x \<in> Bi.
       Fi_map id ... id f1 ... fn (si x) = si' (fi x)*)
    val mor_spec =
      let
        fun mk_fbetw f B1 B2 z z' =
          mk_Ball B1 (Term.absfree z' (HOLogic.mk_mem (f $ z, B2)));
        fun mk_mor B mapAsBs f s s' z z' =
          mk_Ball B (Term.absfree z' (HOLogic.mk_eq
            (Term.list_comb (mapAsBs, passive_ids @ fs @ [s $ z]), s' $ (f $ z))));
        val rhs = HOLogic.mk_conj
          (Library.foldr1 HOLogic.mk_conj (@{map 5} mk_fbetw fs Bs B's zs zs'),
           Library.foldr1 HOLogic.mk_conj (@{map 7} mk_mor Bs mapsAsBs fs ss s's zs zs'))
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

    val ((((((((((((((zs, z's), Bs), Bs_copy), B's), B''s), ss), s's), s''s), fs), fs_copy), gs),
        RFs), Rs), _) =
      lthy
      |> mk_Frees "b" activeAs
      ||>> mk_Frees "b" activeBs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "B''" B''Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "s''" s''Ts
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "g" gTs
      ||>> mk_Frees "x" FRTs
      ||>> mk_Frees "R" setRTs;

    val mor_prem = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs);

    val (mor_image_thms, morE_thms) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs);
        fun mk_image_goal f B1 B2 =
          Logic.mk_implies (prem, HOLogic.mk_Trueprop (mk_leq (mk_image f $ B1) B2));
        val image_goals = @{map 3} mk_image_goal fs Bs B's;
        fun mk_elim_goal B mapAsBs f s s' x =
          Logic.list_implies ([prem, mk_Trueprop_mem (x, B)],
            mk_Trueprop_eq (Term.list_comb (mapAsBs, passive_ids @ fs @ [s $ x]), s' $ (f $ x)));
        val elim_goals = @{map 6} mk_elim_goal Bs mapsAsBs fs ss s's zs;
        fun prove goal =
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            mk_mor_elim_tac ctxt mor_def))
          |> Thm.close_derivation \<^here>;
      in
        (map prove image_goals, map prove elim_goals)
      end;

    val mor_image'_thms = map (fn thm => @{thm set_mp} OF [thm, imageI]) mor_image_thms;

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

    val mor_id_thm = mor_incl_thm OF (replicate n subset_refl);

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
          (fn {context = ctxt, prems = _} =>
            mk_mor_comp_tac ctxt mor_def mor_image'_thms morE_thms map_comp_id_thms)
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

    val mor_UNIV_thm =
      let
        fun mk_conjunct mapAsBs f s s' = HOLogic.mk_eq
            (HOLogic.mk_comp (Term.list_comb (mapAsBs, passive_ids @ fs), s),
            HOLogic.mk_comp (s', f));
        val lhs = mk_mor active_UNIVs ss (map HOLogic.mk_UNIV activeBs) s's fs;
        val rhs = Library.foldr1 HOLogic.mk_conj (@{map 4} mk_conjunct mapsAsBs fs ss s's);
        val vars = fold (Variable.add_free_names lthy) [lhs, rhs] [];
      in
        Goal.prove_sorry lthy vars [] (mk_Trueprop_eq (lhs, rhs))
          (fn {context = ctxt, prems = _} => mk_mor_UNIV_tac ctxt morE_thms mor_def)
        |> Thm.close_derivation \<^here>
      end;

    val mor_str_thm =
      let
        val maps = map2 (fn Ds => fn bnf => Term.list_comb
          (mk_map_of_bnf Ds allAs (passiveAs @ FTsAs) bnf, passive_ids @ ss)) Dss bnfs;
        val goal = HOLogic.mk_Trueprop (mk_mor active_UNIVs ss (map HOLogic.mk_UNIV FTsAs) maps ss);
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_mor_str_tac ctxt ks mor_UNIV_thm)
        |> Thm.close_derivation \<^here>
      end;

    val timer = time (timer "Morphism definition & thms");

    (* bisimulation *)

    val bis_bind = mk_internal_b bisN;
    val bis_def_bind = (Thm.def_binding bis_bind, []);

    fun mk_bis_le_conjunct R B1 B2 = mk_leq R (mk_Times (B1, B2));
    val bis_le = Library.foldr1 HOLogic.mk_conj (@{map 3} mk_bis_le_conjunct Rs Bs B's)

    val bis_spec =
      let
        val fst_args = passive_ids @ fsts;
        val snd_args = passive_ids @ snds;
        fun mk_bis R s s' b1 b2 RF map1 map2 sets =
          list_all_free [b1, b2] (HOLogic.mk_imp
            (HOLogic.mk_mem (HOLogic.mk_prod (b1, b2), R),
            mk_Bex (mk_in (passive_UNIVs @ Rs) sets (snd (dest_Free RF)))
              (Term.absfree (dest_Free RF) (HOLogic.mk_conj
                (HOLogic.mk_eq (Term.list_comb (map1, fst_args) $ RF, s $ b1),
                HOLogic.mk_eq (Term.list_comb (map2, snd_args) $ RF, s' $ b2))))));

        val rhs = HOLogic.mk_conj
          (bis_le, Library.foldr1 HOLogic.mk_conj
            (@{map 9} mk_bis Rs ss s's zs z's RFs map_fsts map_snds bis_setss))
      in
        fold_rev (Term.absfree o Term.dest_Free) (Bs @ ss @ B's @ s's @ Rs) rhs
      end;

    val ((bis_free, (_, bis_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((bis_bind, NoSyn), (bis_def_bind, bis_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val bis = fst (Term.dest_Const (Morphism.term phi bis_free));
    val bis_def = mk_unabs_def (5 * n) (HOLogic.mk_obj_eq (Morphism.thm phi bis_def_free));

    fun mk_bis Bs1 ss1 Bs2 ss2 Rs =
      let
        val args = Bs1 @ ss1 @ Bs2 @ ss2 @ Rs;
        val Ts = map fastype_of args;
        val bisT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (bis, bisT), args)
      end;

    val (((((((((((((((((zs, z's), Bs), B's), B''s), ss), s's), s''s), fs), (Rtuple, Rtuple')), Rs),
        Rs_copy), R's), sRs), (idx, idx')), Idx), Ris), _) =
      lthy
      |> mk_Frees "b" activeAs
      ||>> mk_Frees "b" activeBs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "B''" B''Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "s''" s''Ts
      ||>> mk_Frees "f" fTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "Rtuple") all_sbisT
      ||>> mk_Frees "R" setRTs
      ||>> mk_Frees "R" setRTs
      ||>> mk_Frees "R'" setR'Ts
      ||>> mk_Frees "R" setsRTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "i") idxT
      ||>> yield_singleton (mk_Frees "I") (HOLogic.mk_setT idxT)
      ||>> mk_Frees "Ri" (map (fn T => idxT --> T) setRTs);

    val bis_cong_thm =
      let
        val prems = map HOLogic.mk_Trueprop
         (mk_bis Bs ss B's s's Rs :: map2 (curry HOLogic.mk_eq) Rs_copy Rs)
        val concl = HOLogic.mk_Trueprop (mk_bis Bs ss B's s's Rs_copy);
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => (hyp_subst_tac ctxt THEN' assume_tac ctxt) 1)
        |> Thm.close_derivation \<^here>
      end;

    val bis_rel_thm =
      let
        fun mk_conjunct R s s' b1 b2 rel =
          list_all_free [b1, b2] (HOLogic.mk_imp
            (HOLogic.mk_mem (HOLogic.mk_prod (b1, b2), R),
            Term.list_comb (rel, passive_eqs @ map mk_in_rel Rs) $ (s $ b1) $ (s' $ b2)));

        val rhs = HOLogic.mk_conj
          (bis_le, Library.foldr1 HOLogic.mk_conj
            (@{map 6} mk_conjunct Rs ss s's zs z's relsAsBs))
        val goal = mk_Trueprop_eq (mk_bis Bs ss B's s's Rs, rhs);
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_bis_rel_tac ctxt m bis_def in_rels map_comps
            map_cong0s set_mapss)
        |> Thm.close_derivation \<^here>
      end;

    val bis_converse_thm =
      let
        val goal = Logic.mk_implies (HOLogic.mk_Trueprop (mk_bis Bs ss B's s's Rs),
          HOLogic.mk_Trueprop (mk_bis B's s's Bs ss (map mk_converse Rs)));
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_bis_converse_tac ctxt m bis_rel_thm rel_congs
            rel_converseps)
        |> Thm.close_derivation \<^here>
      end;

    val bis_O_thm =
      let
        val prems =
          [HOLogic.mk_Trueprop (mk_bis Bs ss B's s's Rs),
           HOLogic.mk_Trueprop (mk_bis B's s's B''s s''s R's)];
        val concl =
          HOLogic.mk_Trueprop (mk_bis Bs ss B''s s''s (map2 (curry mk_rel_comp) Rs R's));
        val vars = fold (Variable.add_free_names lthy) (concl :: prems) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, concl))
          (fn {context = ctxt, prems = _} => mk_bis_O_tac ctxt m bis_rel_thm rel_congs le_rel_OOs)
        |> Thm.close_derivation \<^here>
      end;

    val bis_Gr_thm =
      let
        val concl = HOLogic.mk_Trueprop (mk_bis Bs ss B's s's (map2 mk_Gr Bs fs));
        val vars = fold (Variable.add_free_names lthy) ([coalg_prem, mor_prem, concl]) [];
      in
        Goal.prove_sorry lthy vars [] (Logic.list_implies ([coalg_prem, mor_prem], concl))
          (fn {context = ctxt, prems = _} => mk_bis_Gr_tac ctxt bis_rel_thm rel_Grps mor_image_thms
            morE_thms coalg_in_thms)
        |> Thm.close_derivation \<^here>
      end;

    val bis_image2_thm = bis_cong_thm OF
      ((bis_O_thm OF [bis_Gr_thm RS bis_converse_thm, bis_Gr_thm]) ::
      replicate n @{thm image2_Gr});

    val bis_Id_on_thm = bis_cong_thm OF ((mor_id_thm RSN (2, bis_Gr_thm)) ::
      replicate n @{thm Id_on_Gr});

    val bis_Union_thm =
      let
        val prem =
          HOLogic.mk_Trueprop (mk_Ball Idx
            (Term.absfree idx' (mk_bis Bs ss B's s's (map (fn R => R $ idx) Ris))));
        val concl =
          HOLogic.mk_Trueprop (mk_bis Bs ss B's s's (map (mk_UNION Idx) Ris));
        val vars = fold (Variable.add_free_names lthy) [prem, concl] [];
      in
        Goal.prove_sorry lthy vars [] (Logic.mk_implies (prem, concl))
          (fn {context = ctxt, prems = _} => mk_bis_Union_tac ctxt bis_def in_mono'_thms)
        |> Thm.close_derivation \<^here>
      end;

    (* self-bisimulation *)

    fun mk_sbis Bs ss Rs = mk_bis Bs ss Bs ss Rs;

    (* largest self-bisimulation *)

    val lsbis_binds = mk_internal_bs lsbisN;
    fun lsbis_bind i = nth lsbis_binds (i - 1);
    val lsbis_def_bind = rpair [] o Thm.def_binding o lsbis_bind;

    val all_sbis = HOLogic.mk_Collect (fst Rtuple', snd Rtuple', list_exists_free sRs
      (HOLogic.mk_conj (HOLogic.mk_eq (Rtuple, HOLogic.mk_tuple sRs), mk_sbis Bs ss sRs)));

    fun lsbis_spec i =
      fold_rev (Term.absfree o Term.dest_Free) (Bs @ ss)
        (mk_UNION all_sbis (Term.absfree Rtuple' (mk_nthN n Rtuple i)));

    val ((lsbis_frees, (_, lsbis_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i => Local_Theory.define
        ((lsbis_bind i, NoSyn), (lsbis_def_bind i, lsbis_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val lsbis_defs = map (fn def =>
      mk_unabs_def (2 * n) (HOLogic.mk_obj_eq (Morphism.thm phi def))) lsbis_def_frees;
    val lsbiss = map (fst o Term.dest_Const o Morphism.term phi) lsbis_frees;

    fun mk_lsbis Bs ss i =
      let
        val args = Bs @ ss;
        val Ts = map fastype_of args;
        val RT = mk_relT (`I (HOLogic.dest_setT (fastype_of (nth Bs (i - 1)))));
        val lsbisT = Library.foldr (op -->) (Ts, RT);
      in
        Term.list_comb (Const (nth lsbiss (i - 1), lsbisT), args)
      end;

    val (((((zs, zs'), Bs), ss), sRs), _) =
      lthy
      |> mk_Frees' "b" activeAs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "R" setsRTs;

    val sbis_prem = HOLogic.mk_Trueprop (mk_sbis Bs ss sRs);
    val coalg_prem = HOLogic.mk_Trueprop (mk_coalg Bs ss);

    val sbis_lsbis_thm =
      let
        val goal = HOLogic.mk_Trueprop (mk_sbis Bs ss (map (mk_lsbis Bs ss) ks));
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} =>
            mk_sbis_lsbis_tac ctxt lsbis_defs bis_Union_thm bis_cong_thm)
        |> Thm.close_derivation \<^here>
      end;

    val lsbis_incl_thms = map (fn i => sbis_lsbis_thm RS
      (bis_def RS iffD1 RS conjunct1 RS mk_conjunctN n i)) ks;
    val lsbisE_thms = map (fn i => (mk_specN 2 (sbis_lsbis_thm RS
      (bis_def RS iffD1 RS conjunct2 RS mk_conjunctN n i))) RS mp) ks;

    val incl_lsbis_thms =
      let
        fun mk_concl i R = HOLogic.mk_Trueprop (mk_leq R (mk_lsbis Bs ss i));
        val goals = map2 (fn i => fn R => Logic.mk_implies (sbis_prem, mk_concl i R)) ks sRs;
      in
        @{map 3} (fn goal => fn i => fn def =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            mk_incl_lsbis_tac ctxt n i def))
          |> Thm.close_derivation \<^here>)
        goals ks lsbis_defs
      end;

    val equiv_lsbis_thms =
      let
        fun mk_concl i B = HOLogic.mk_Trueprop (mk_equiv B (mk_lsbis Bs ss i));
        val goals = map2 (fn i => fn B => Logic.mk_implies (coalg_prem, mk_concl i B)) ks Bs;
      in
        @{map 3} (fn goal => fn l_incl => fn incl_l =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal
            (fn {context = ctxt, prems = _} => mk_equiv_lsbis_tac ctxt sbis_lsbis_thm l_incl incl_l
              bis_Id_on_thm bis_converse_thm bis_O_thm)
          |> Thm.close_derivation \<^here>))
        goals lsbis_incl_thms incl_lsbis_thms
      end;

    val timer = time (timer "Bisimulations");

    (* bounds *)

    val (lthy, sbd, sbdT,
      sbd_card_order, sbd_Cinfinite, sbd_Card_order, set_sbdss) =
      if n = 1
      then (lthy, sum_bd, sum_bdT, bd_card_order, bd_Cinfinite, bd_Card_order, set_bdss)
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
          val Abs_sbdT_bij = mk_Abs_bij_thm lthy Abs_sbdT_inj (#Abs_cases sbdT_loc_info);

          val sum_Cinfinite = mk_sum_Cinfinite bd_Cinfinites;
          val sum_Card_order = sum_Cinfinite RS conjunct2;
          val sum_card_order = mk_sum_card_order bd_card_orders;

          val sbd_ordIso = @{thm ssubst_Pair_rhs} OF
            [@{thm dir_image} OF [Abs_sbdT_inj, sum_Card_order], sbd_def];
          val sbd_card_order = @{thm iffD2[OF arg_cong[of _ _ card_order]]} OF
            [sbd_def, @{thm card_order_dir_image} OF [Abs_sbdT_bij, sum_card_order]];
          val sbd_Cinfinite = @{thm Cinfinite_cong} OF [sbd_ordIso, sum_Cinfinite];
          val sbd_Card_order = sbd_Cinfinite RS conjunct2;

          fun mk_set_sbd i bd_Card_order bds =
            map (fn thm => @{thm ordLeq_ordIso_trans} OF
              [bd_Card_order RS mk_ordLeq_csum n i thm, sbd_ordIso]) bds;
          val set_sbdss = @{map 3} mk_set_sbd ks bd_Card_orders set_bdss;
       in
         (lthy, sbd, sbdT, sbd_card_order, sbd_Cinfinite, sbd_Card_order, set_sbdss)
       end;

    val sbdTs = replicate n sbdT;
    val sum_sbdT = mk_sumTN sbdTs;
    val sum_sbd_listT = HOLogic.listT sum_sbdT;
    val sum_sbd_list_setT = HOLogic.mk_setT sum_sbd_listT;
    val bdTs = passiveAs @ replicate n sbdT;
    val to_sbd_maps = @{map 4} mk_map_of_bnf Dss Ass (replicate n bdTs) bnfs;
    val bdFTs = mk_FTs bdTs;
    val sbdFT = mk_sumTN bdFTs;
    val treeT = HOLogic.mk_prodT (sum_sbd_list_setT, sum_sbd_listT --> sbdFT);
    val treeQT = HOLogic.mk_setT treeT;
    val treeTs = passiveAs @ replicate n treeT;
    val treeQTs = passiveAs @ replicate n treeQT;
    val treeFTs = mk_FTs treeTs;
    val tree_maps = @{map 4} mk_map_of_bnf Dss (replicate n bdTs) (replicate n treeTs) bnfs;
    val final_maps = @{map 4} mk_map_of_bnf Dss (replicate n treeTs) (replicate n treeQTs) bnfs;
    val isNode_setss = mk_setss (passiveAs @ replicate n sbdT);

    val root = HOLogic.mk_set sum_sbd_listT [HOLogic.mk_list sum_sbdT []];
    val Zero = HOLogic.mk_tuple (map (fn U => absdummy U root) activeAs);
    val Lev_recT = fastype_of Zero;

    val Nil = HOLogic.mk_tuple (@{map 3} (fn i => fn z => fn z'=>
      Term.absfree z' (mk_InN activeAs z i)) ks zs zs');
    val rv_recT = fastype_of Nil;

    val (((((((((((((((zs, zs'), zs_copy), ss), (nat, nat')),
        (sumx, sumx')), (kks, kks')), (kl, kl')), (kl_copy, kl'_copy)), (Kl, Kl')), (lab, lab')),
        (Kl_lab, Kl_lab')), xs), (Lev_rec, Lev_rec')), (rv_rec, rv_rec')), _) =
      lthy
      |> mk_Frees' "b" activeAs
      ||>> mk_Frees "b" activeAs
      ||>> mk_Frees "s" sTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "n") HOLogic.natT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "sumx") sum_sbdT
      ||>> mk_Frees' "k" sbdTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "kl") sum_sbd_listT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "kl") sum_sbd_listT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "Kl") sum_sbd_list_setT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "lab") (sum_sbd_listT --> sbdFT)
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "Kl_lab") treeT
      ||>> mk_Frees "x" bdFTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "rec") Lev_recT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "rec") rv_recT;

    val (k, k') = (hd kks, hd kks')

    val timer = time (timer "Bounds");

    (* tree coalgebra *)

    val isNode_binds = mk_internal_bs isNodeN;
    fun isNode_bind i = nth isNode_binds (i - 1);
    val isNode_def_bind = rpair [] o Thm.def_binding o isNode_bind;

    val isNodeT =
      Library.foldr (op -->) (map fastype_of [Kl, lab, kl], HOLogic.boolT);

    val Succs = @{map 3} (fn i => fn k => fn k' =>
      HOLogic.mk_Collect (fst k', snd k', HOLogic.mk_mem (mk_InN sbdTs k i, mk_Succ Kl kl)))
      ks kks kks';

    fun isNode_spec sets x i =
      let
        val active_sets = drop m (map (fn set => set $ x) sets);
        val rhs = list_exists_free [x]
          (Library.foldr1 HOLogic.mk_conj (HOLogic.mk_eq (lab $ kl, mk_InN bdFTs x i) ::
          map2 (curry HOLogic.mk_eq) active_sets Succs));
      in
        fold_rev (Term.absfree o Term.dest_Free) [Kl, lab, kl] rhs
      end;

    val ((isNode_frees, (_, isNode_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> @{fold_map 3} (fn i => fn x => fn sets => Local_Theory.define
        ((isNode_bind i, NoSyn), (isNode_def_bind i, isNode_spec sets x i)))
        ks xs isNode_setss
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val isNode_defs = map (fn def =>
      mk_unabs_def 3 (HOLogic.mk_obj_eq (Morphism.thm phi def))) isNode_def_frees;
    val isNodes = map (fst o Term.dest_Const o Morphism.term phi) isNode_frees;

    fun mk_isNode kl i =
      Term.list_comb (Const (nth isNodes (i - 1), isNodeT), [Kl, lab, kl]);

    val isTree =
      let
        val empty = HOLogic.mk_mem (HOLogic.mk_list sum_sbdT [], Kl);

        val tree = mk_Ball Kl (Term.absfree kl'
          (Library.foldr1 HOLogic.mk_conj (@{map 4} (fn Succ => fn i => fn k => fn k' =>
            mk_Ball Succ (Term.absfree k' (mk_isNode
              (mk_append (kl, HOLogic.mk_list sum_sbdT [mk_InN sbdTs k i])) i)))
          Succs ks kks kks')));
      in
        HOLogic.mk_conj (empty, tree)
      end;

    val carT_binds = mk_internal_bs carTN;
    fun carT_bind i = nth carT_binds (i - 1);
    val carT_def_bind = rpair [] o Thm.def_binding o carT_bind;

    fun carT_spec i =
      HOLogic.mk_Collect (fst Kl_lab', snd Kl_lab', list_exists_free [Kl, lab]
        (HOLogic.mk_conj (HOLogic.mk_eq (Kl_lab, HOLogic.mk_prod (Kl, lab)),
          HOLogic.mk_conj (isTree, mk_isNode (HOLogic.mk_list sum_sbdT []) i))));

    val ((carT_frees, (_, carT_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i =>
        Local_Theory.define ((carT_bind i, NoSyn), (carT_def_bind i, carT_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val carT_defs = map (fn def => HOLogic.mk_obj_eq (Morphism.thm phi def)) carT_def_frees;
    val carTs = map (fst o Term.dest_Const o Morphism.term phi) carT_frees;

    fun mk_carT i = Const (nth carTs (i - 1), HOLogic.mk_setT treeT);

    val strT_binds = mk_internal_bs strTN;
    fun strT_bind i = nth strT_binds (i - 1);
    val strT_def_bind = rpair [] o Thm.def_binding o strT_bind;

    fun strT_spec mapFT FT i =
      let
        fun mk_f i k k' =
          let val in_k = mk_InN sbdTs k i;
          in Term.absfree k' (HOLogic.mk_prod (mk_Shift Kl in_k, mk_shift lab in_k)) end;

        val f = Term.list_comb (mapFT, passive_ids @ @{map 3} mk_f ks kks kks');
        val (fTs1, fTs2) = apsnd tl (chop (i - 1) (map (fn T => T --> FT) bdFTs));
        val fs = map mk_undefined fTs1 @ (f :: map mk_undefined fTs2);
      in
        HOLogic.mk_case_prod (Term.absfree Kl' (Term.absfree lab'
          (mk_case_sumN fs $ (lab $ HOLogic.mk_list sum_sbdT []))))
      end;

    val ((strT_frees, (_, strT_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> @{fold_map 3} (fn i => fn mapFT => fn FT => Local_Theory.define
        ((strT_bind i, NoSyn), (strT_def_bind i, strT_spec mapFT FT i)))
        ks tree_maps treeFTs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val strT_defs = map (fn def =>
        trans OF [HOLogic.mk_obj_eq (Morphism.thm phi def) RS fun_cong, @{thm prod.case}])
      strT_def_frees;
    val strTs = map (fst o Term.dest_Const o Morphism.term phi) strT_frees;

    fun mk_strT FT i = Const (nth strTs (i - 1), treeT --> FT);

    val carTAs = map mk_carT ks;
    val strTAs = map2 mk_strT treeFTs ks;

    val coalgT_thm =
      Goal.prove_sorry lthy [] [] (HOLogic.mk_Trueprop (mk_coalg carTAs strTAs))
        (fn {context = ctxt, prems = _} => mk_coalgT_tac ctxt m
          (coalg_def :: isNode_defs @ carT_defs) strT_defs set_mapss)
      |> Thm.close_derivation \<^here>;

    val timer = time (timer "Tree coalgebra");

    fun mk_to_sbd s x i i' =
      mk_toCard (nth (nth setssAs (i - 1)) (m + i' - 1) $ (s $ x)) sbd;
    fun mk_from_sbd s x i i' =
      mk_fromCard (nth (nth setssAs (i - 1)) (m + i' - 1) $ (s $ x)) sbd;

    fun mk_to_sbd_thmss thm = map (map (fn set_sbd =>
      thm OF [set_sbd, sbd_Card_order]) o drop m) set_sbdss;

    val to_sbd_inj_thmss = mk_to_sbd_thmss @{thm toCard_inj};
    val from_to_sbd_thmss = mk_to_sbd_thmss @{thm fromCard_toCard};

    val Lev_bind = mk_internal_b LevN;
    val Lev_def_bind = rpair [] (Thm.def_binding Lev_bind);

    val Lev_spec =
      let
        fun mk_Suc i s setsAs a a' =
          let
            val sets = drop m setsAs;
            fun mk_set i' set b =
              let
                val Cons = HOLogic.mk_eq (kl_copy,
                  mk_Cons (mk_InN sbdTs (mk_to_sbd s a i i' $ b) i') kl)
                val b_set = HOLogic.mk_mem (b, set $ (s $ a));
                val kl_rec = HOLogic.mk_mem (kl, mk_nthN n Lev_rec i' $ b);
              in
                HOLogic.mk_Collect (fst kl'_copy, snd kl'_copy, list_exists_free [b, kl]
                  (HOLogic.mk_conj (Cons, HOLogic.mk_conj (b_set, kl_rec))))
              end;
          in
            Term.absfree a' (Library.foldl1 mk_union (@{map 3} mk_set ks sets zs_copy))
          end;

        val Suc = Term.absdummy HOLogic.natT (Term.absfree Lev_rec'
          (HOLogic.mk_tuple (@{map 5} mk_Suc ks ss setssAs zs zs')));

        val rhs = mk_rec_nat Zero Suc;
      in
        fold_rev (Term.absfree o Term.dest_Free) ss rhs
      end;

    val ((Lev_free, (_, Lev_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((Lev_bind, NoSyn), (Lev_def_bind, Lev_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val Lev_def = mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi Lev_def_free));
    val Lev = fst (Term.dest_Const (Morphism.term phi Lev_free));

    fun mk_Lev ss nat i =
      let
        val Ts = map fastype_of ss;
        val LevT = Library.foldr (op -->) (Ts, HOLogic.natT -->
          HOLogic.mk_tupleT (map (fn U => domain_type U --> sum_sbd_list_setT) Ts));
      in
        mk_nthN n (Term.list_comb (Const (Lev, LevT), ss) $ nat) i
      end;

    val Lev_0s = flat (mk_rec_simps n @{thm rec_nat_0_imp} [Lev_def]);
    val Lev_Sucs = flat (mk_rec_simps n @{thm rec_nat_Suc_imp} [Lev_def]);

    val rv_bind = mk_internal_b rvN;
    val rv_def_bind = rpair [] (Thm.def_binding rv_bind);

    val rv_spec =
      let
        fun mk_Cons i s b b' =
          let
            fun mk_case i' =
              Term.absfree k' (mk_nthN n rv_rec i' $ (mk_from_sbd s b i i' $ k));
          in
            Term.absfree b' (mk_case_sumN (map mk_case ks) $ sumx)
          end;

        val Cons = Term.absfree sumx' (Term.absdummy sum_sbd_listT (Term.absfree rv_rec'
          (HOLogic.mk_tuple (@{map 4} mk_Cons ks ss zs zs'))));

        val rhs = mk_rec_list Nil Cons;
      in
        fold_rev (Term.absfree o Term.dest_Free) ss rhs
      end;

    val ((rv_free, (_, rv_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((rv_bind, NoSyn), (rv_def_bind, rv_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val rv_def = mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi rv_def_free));
    val rv = fst (Term.dest_Const (Morphism.term phi rv_free));

    fun mk_rv ss kl i =
      let
        val Ts = map fastype_of ss;
        val As = map domain_type Ts;
        val rvT = Library.foldr (op -->) (Ts, fastype_of kl -->
          HOLogic.mk_tupleT (map (fn U => U --> mk_sumTN As) As));
      in
        mk_nthN n (Term.list_comb (Const (rv, rvT), ss) $ kl) i
      end;

    val rv_Nils = flat (mk_rec_simps n @{thm rec_list_Nil_imp} [rv_def]);
    val rv_Conss = flat (mk_rec_simps n @{thm rec_list_Cons_imp} [rv_def]);

    val beh_binds = mk_internal_bs behN;
    fun beh_bind i = nth beh_binds (i - 1);
    val beh_def_bind = rpair [] o Thm.def_binding o beh_bind;

    fun beh_spec i z =
      let
        fun mk_case i to_sbd_map s k k' =
          Term.absfree k' (mk_InN bdFTs
            (Term.list_comb (to_sbd_map, passive_ids @ map (mk_to_sbd s k i) ks) $ (s $ k)) i);

        val Lab = Term.absfree kl'
          (mk_case_sumN (@{map 5} mk_case ks to_sbd_maps ss zs zs') $ (mk_rv ss kl i $ z));

        val rhs = HOLogic.mk_prod (mk_UNION (HOLogic.mk_UNIV HOLogic.natT)
          (Term.absfree nat' (mk_Lev ss nat i $ z)), Lab);
      in
        fold_rev (Term.absfree o Term.dest_Free) (ss @ [z]) rhs
      end;

    val ((beh_frees, (_, beh_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> @{fold_map 2} (fn i => fn z =>
        Local_Theory.define ((beh_bind i, NoSyn), (beh_def_bind i, beh_spec i z))) ks zs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val beh_defs = map (fn def =>
      mk_unabs_def (n + 1) (HOLogic.mk_obj_eq (Morphism.thm phi def))) beh_def_frees;
    val behs = map (fst o Term.dest_Const o Morphism.term phi) beh_frees;

    fun mk_beh ss i =
      let
        val Ts = map fastype_of ss;
        val behT = Library.foldr (op -->) (Ts, nth activeAs (i - 1) --> treeT);
      in
        Term.list_comb (Const (nth behs (i - 1), behT), ss)
      end;

    val ((((((zs, zs_copy), zs_copy2), ss), (nat, nat')), (kl, kl')), _) =
      lthy
      |> mk_Frees "b" activeAs
      ||>> mk_Frees "b" activeAs
      ||>> mk_Frees "b" activeAs
      ||>> mk_Frees "s" sTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "n") HOLogic.natT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "kl") sum_sbd_listT;

    val (length_Lev_thms, length_Lev'_thms) =
      let
        fun mk_conjunct i z = HOLogic.mk_imp (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z),
          HOLogic.mk_eq (mk_size kl, nat));
        val goal = list_all_free (kl :: zs)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));
        val vars = Variable.add_free_names lthy goal [];

        val cts = map (SOME o Thm.cterm_of lthy) [Term.absfree nat' goal, nat];

        val length_Lev =
          Goal.prove_sorry lthy vars [] (HOLogic.mk_Trueprop goal)
            (fn {context = ctxt, prems = _} => mk_length_Lev_tac ctxt cts Lev_0s Lev_Sucs)
          |> Thm.close_derivation \<^here>;

        val length_Lev' = mk_specN (n + 1) length_Lev;
        val length_Levs = map (fn i => length_Lev' RS mk_conjunctN n i RS mp) ks;

        fun mk_goal i z = Logic.mk_implies
            (mk_Trueprop_mem (kl, mk_Lev ss nat i $ z),
            mk_Trueprop_mem (kl, mk_Lev ss (mk_size kl) i $ z));
        val goals = map2 mk_goal ks zs;

        val length_Levs' =
          map2 (fn goal => fn length_Lev =>
            Variable.add_free_names lthy goal []
            |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_length_Lev'_tac ctxt length_Lev))
            |> Thm.close_derivation \<^here>)
          goals length_Levs;
      in
        (length_Levs, length_Levs')
      end;

    val rv_last_thmss =
      let
        fun mk_conjunct i z i' z_copy = list_exists_free [z_copy]
          (HOLogic.mk_eq
            (mk_rv ss (mk_append (kl, HOLogic.mk_list sum_sbdT [mk_InN sbdTs k i'])) i $ z,
            mk_InN activeAs z_copy i'));
        val goal = list_all_free (k :: zs)
          (Library.foldr1 HOLogic.mk_conj (map2 (fn i => fn z =>
            Library.foldr1 HOLogic.mk_conj
              (map2 (mk_conjunct i z) ks zs_copy)) ks zs));
        val vars = Variable.add_free_names lthy goal [];

        val cTs = [SOME (Thm.ctyp_of lthy sum_sbdT)];
        val cts = map (SOME o Thm.cterm_of lthy) [Term.absfree kl' goal, kl];

        val rv_last =
          Goal.prove_sorry lthy vars [] (HOLogic.mk_Trueprop goal)
            (fn {context = ctxt, prems = _} => mk_rv_last_tac ctxt cTs cts rv_Nils rv_Conss)
          |> Thm.close_derivation \<^here>;

        val rv_last' = mk_specN (n + 1) rv_last;
      in
        map (fn i => map (fn i' => rv_last' RS mk_conjunctN n i RS mk_conjunctN n i') ks) ks
      end;

    val set_Lev_thmsss =
      let
        fun mk_conjunct i z =
          let
            fun mk_conjunct' i' sets s z' =
              let
                fun mk_conjunct'' i'' set z'' = HOLogic.mk_imp
                  (HOLogic.mk_mem (z'', set $ (s $ z')),
                    HOLogic.mk_mem (mk_append (kl,
                      HOLogic.mk_list sum_sbdT [mk_InN sbdTs (mk_to_sbd s z' i' i'' $ z'') i'']),
                      mk_Lev ss (HOLogic.mk_Suc nat) i $ z));
              in
                HOLogic.mk_imp (HOLogic.mk_eq (mk_rv ss kl i $ z, mk_InN activeAs z' i'),
                  (Library.foldr1 HOLogic.mk_conj
                    (@{map 3} mk_conjunct'' ks (drop m sets) zs_copy2)))
              end;
          in
            HOLogic.mk_imp (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z),
              Library.foldr1 HOLogic.mk_conj (@{map 4} mk_conjunct' ks setssAs ss zs_copy))
          end;

        val goal = list_all_free (kl :: zs @ zs_copy @ zs_copy2)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));
        val vars = Variable.add_free_names lthy goal [];

        val cts = map (SOME o Thm.cterm_of lthy) [Term.absfree nat' goal, nat];

        val set_Lev =
          Goal.prove_sorry lthy vars [] (HOLogic.mk_Trueprop goal)
            (fn {context = ctxt, prems = _} =>
              mk_set_Lev_tac ctxt cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbd_thmss)
          |> Thm.close_derivation \<^here>;

        val set_Lev' = mk_specN (3 * n + 1) set_Lev;
      in
        map (fn i => map (fn i' => map (fn i'' => set_Lev' RS
          mk_conjunctN n i RS mp RS
          mk_conjunctN n i' RS mp RS
          mk_conjunctN n i'' RS mp) ks) ks) ks
      end;

    val set_image_Lev_thmsss =
      let
        fun mk_conjunct i z =
          let
            fun mk_conjunct' i' sets =
              let
                fun mk_conjunct'' i'' set s z'' = HOLogic.mk_imp
                  (HOLogic.mk_eq (mk_rv ss kl i $ z, mk_InN activeAs z'' i''),
                  HOLogic.mk_mem (k, mk_image (mk_to_sbd s z'' i'' i') $ (set $ (s $ z''))));
              in
                HOLogic.mk_imp (HOLogic.mk_mem
                  (mk_append (kl, HOLogic.mk_list sum_sbdT [mk_InN sbdTs k i']),
                    mk_Lev ss (HOLogic.mk_Suc nat) i $ z),
                  (Library.foldr1 HOLogic.mk_conj (@{map 4} mk_conjunct'' ks sets ss zs_copy)))
              end;
          in
            HOLogic.mk_imp (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z),
              Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct' ks (drop m setssAs')))
          end;

        val goal = list_all_free (kl :: k :: zs @ zs_copy)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));
        val vars = Variable.add_free_names lthy goal [];

        val cts = map (SOME o Thm.cterm_of lthy) [Term.absfree nat' goal, nat];

        val set_image_Lev =
          Goal.prove_sorry lthy vars [] (HOLogic.mk_Trueprop goal)
            (fn {context = ctxt, prems = _} =>
              mk_set_image_Lev_tac ctxt cts Lev_0s Lev_Sucs rv_Nils rv_Conss
                from_to_sbd_thmss to_sbd_inj_thmss)
          |> Thm.close_derivation \<^here>;

        val set_image_Lev' = mk_specN (2 * n + 2) set_image_Lev;
      in
        map (fn i => map (fn i' => map (fn i'' => set_image_Lev' RS
          mk_conjunctN n i RS mp RS
          mk_conjunctN n i'' RS mp RS
          mk_conjunctN n i' RS mp) ks) ks) ks
      end;

    val mor_beh_thm =
      let
        val goal = HOLogic.mk_Trueprop (mk_mor active_UNIVs ss carTAs strTAs (map (mk_beh ss) ks));
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_mor_beh_tac ctxt m mor_def mor_cong_thm
            beh_defs carT_defs strT_defs isNode_defs
            to_sbd_inj_thmss from_to_sbd_thmss Lev_0s Lev_Sucs rv_Nils rv_Conss
            length_Lev_thms length_Lev'_thms rv_last_thmss set_Lev_thmsss
            set_image_Lev_thmsss set_mapss map_comp_id_thms map_cong0s)
        |> Thm.close_derivation \<^here>
      end;

    val timer = time (timer "Behavioral morphism");

    val lsbisAs = map (mk_lsbis carTAs strTAs) ks;

    fun mk_str_final i =
      mk_univ (HOLogic.mk_comp (Term.list_comb (nth final_maps (i - 1),
        passive_ids @ map mk_proj lsbisAs), nth strTAs (i - 1)));

    val car_finals = map2 mk_quotient carTAs lsbisAs;
    val str_finals = map mk_str_final ks;

    val coalgT_set_thmss = map (map (fn thm => coalgT_thm RS thm)) coalg_set_thmss;
    val equiv_LSBIS_thms = map (fn thm => coalgT_thm RS thm) equiv_lsbis_thms;

    val congruent_str_final_thms =
      let
        fun mk_goal R final_map strT =
          HOLogic.mk_Trueprop (mk_congruent R (HOLogic.mk_comp
            (Term.list_comb (final_map, passive_ids @ map mk_proj lsbisAs), strT)));

        val goals = @{map 3} mk_goal lsbisAs final_maps strTAs;
      in
        @{map 4} (fn goal => fn lsbisE => fn map_comp_id => fn map_cong0 =>
          Goal.prove_sorry lthy [] [] goal
            (fn {context = ctxt, prems = _} => mk_congruent_str_final_tac ctxt m lsbisE map_comp_id
              map_cong0 equiv_LSBIS_thms)
          |> Thm.close_derivation \<^here>)
        goals lsbisE_thms map_comp_id_thms map_cong0s
      end;

    val coalg_final_thm = Goal.prove_sorry lthy [] []
      (HOLogic.mk_Trueprop (mk_coalg car_finals str_finals))
      (fn {context = ctxt, prems = _} => mk_coalg_final_tac ctxt m coalg_def
        congruent_str_final_thms equiv_LSBIS_thms set_mapss coalgT_set_thmss)
      |> Thm.close_derivation \<^here>;

    val mor_T_final_thm = Goal.prove_sorry lthy [] []
      (HOLogic.mk_Trueprop (mk_mor carTAs strTAs car_finals str_finals (map mk_proj lsbisAs)))
      (fn {context = ctxt, prems = _} => mk_mor_T_final_tac ctxt mor_def congruent_str_final_thms
        equiv_LSBIS_thms)
      |> Thm.close_derivation \<^here>;

    val mor_final_thm = mor_comp_thm OF [mor_beh_thm, mor_T_final_thm];
    val in_car_final_thms = map (fn thm => thm OF [mor_final_thm, UNIV_I]) mor_image'_thms;

    val timer = time (timer "Final coalgebra");

    val ((T_names, (T_glob_infos, T_loc_infos)), lthy) =
      lthy
      |> @{fold_map 4} (fn b => fn mx => fn car_final => fn in_car_final =>
          typedef (b, params, mx) car_final NONE
            (fn ctxt => EVERY' [rtac ctxt exI, rtac ctxt in_car_final] 1))
        bs mixfixes car_finals in_car_final_thms
      |>> apsnd split_list o split_list;

    val Ts = map (fn name => Type (name, params')) T_names;
    fun mk_Ts passive = map (Term.typ_subst_atomic (passiveAs ~~ passive)) Ts;
    val Ts' = mk_Ts passiveBs;
    val Rep_Ts = map2 (fn info => fn T => Const (#Rep_name info, T --> treeQT)) T_glob_infos Ts;
    val Abs_Ts = map2 (fn info => fn T => Const (#Abs_name info, treeQT --> T)) T_glob_infos Ts;

    val Reps = map #Rep T_loc_infos;
    val Rep_injects = map #Rep_inject T_loc_infos;
    val Abs_inverses = map #Abs_inverse T_loc_infos;

    val timer = time (timer "THE TYPEDEFs & Rep/Abs thms");

    val UNIVs = map HOLogic.mk_UNIV Ts;
    val FTs = mk_FTs (passiveAs @ Ts);
    val FTs_setss = mk_setss (passiveAs @ Ts);
    val map_FTs = map2 (fn Ds => mk_map_of_bnf Ds treeQTs (passiveAs @ Ts)) Dss bnfs;
    val unfold_fTs = map2 (curry op -->) activeAs Ts;

    val emptys = map (fn T => HOLogic.mk_set T []) passiveAs;
    val Zeros = map (fn empty =>
     HOLogic.mk_tuple (map (fn U => absdummy U empty) Ts)) emptys;
    val hrecTs = map fastype_of Zeros;

    val (((zs, ss), (Jzs, Jzs')), _) =
      lthy
      |> mk_Frees "b" activeAs
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees' "z" Ts;

    fun dtor_bind i = nth external_bs (i - 1) |> Binding.prefix_name (dtorN ^ "_");
    val dtor_def_bind = rpair [] o Binding.concealed o Thm.def_binding o dtor_bind;

    fun dtor_spec rep str map_FT Jz Jz' =
      Term.absfree Jz'
        (Term.list_comb (map_FT, map HOLogic.id_const passiveAs @ Abs_Ts) $ (str $ (rep $ Jz)));

    val ((dtor_frees, (_, dtor_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> @{fold_map 6} (fn i => fn rep => fn str => fn mapx => fn Jz => fn Jz' =>
        Local_Theory.define ((dtor_bind i, NoSyn),
          (dtor_def_bind i, dtor_spec rep str mapx Jz Jz')))
        ks Rep_Ts str_finals map_FTs Jzs Jzs'
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_dtors passive =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ (mk_params passive)) o
        Morphism.term phi) dtor_frees;
    val dtors = mk_dtors passiveAs;
    val dtor's = mk_dtors passiveBs;
    val dtor_defs =
      map (fn def => HOLogic.mk_obj_eq (Morphism.thm phi def) RS fun_cong) dtor_def_frees;

    val coalg_final_set_thmss = map (map (fn thm => coalg_final_thm RS thm)) coalg_set_thmss;
    val (mor_Rep_thm, mor_Abs_thm) =
      let
        val mor_Rep =
          Goal.prove_sorry lthy [] []
            (HOLogic.mk_Trueprop (mk_mor UNIVs dtors car_finals str_finals Rep_Ts))
            (fn {context = ctxt, prems = _} => mk_mor_Rep_tac ctxt (mor_def :: dtor_defs) Reps
              Abs_inverses coalg_final_set_thmss map_comp_id_thms map_cong0L_thms)
          |> Thm.close_derivation \<^here>;

        val mor_Abs =
          Goal.prove_sorry lthy [] []
            (HOLogic.mk_Trueprop (mk_mor car_finals str_finals UNIVs dtors Abs_Ts))
            (fn {context = ctxt, prems = _} => mk_mor_Abs_tac ctxt (mor_def :: dtor_defs)
              Abs_inverses)
          |> Thm.close_derivation \<^here>;
      in
        (mor_Rep, mor_Abs)
      end;

    val timer = time (timer "dtor definitions & thms");

    fun unfold_bind i = nth external_bs (i - 1) |> Binding.prefix_name (dtor_unfoldN ^ "_");
    val unfold_def_bind = rpair [] o Binding.concealed o Thm.def_binding o unfold_bind;

    fun unfold_spec abs f z = fold_rev (Term.absfree o Term.dest_Free) (ss @ [z]) (abs $ (f $ z));

    val ((unfold_frees, (_, unfold_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> @{fold_map 4} (fn i => fn abs => fn f => fn z =>
        Local_Theory.define ((unfold_bind i, NoSyn), (unfold_def_bind i, unfold_spec abs f z)))
          ks Abs_Ts (map (fn i => HOLogic.mk_comp
            (mk_proj (nth lsbisAs (i - 1)), mk_beh ss i)) ks) zs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val unfolds = map (Morphism.term phi) unfold_frees;
    val unfold_names = map (fst o dest_Const) unfolds;
    fun mk_unfolds passives actives =
      @{map 3} (fn name => fn T => fn active =>
        Const (name, Library.foldr (op -->)
          (map2 (curry op -->) actives (mk_FTs (passives @ actives)), active --> T)))
      unfold_names (mk_Ts passives) actives;
    fun mk_unfold Ts ss i = Term.list_comb (Const (nth unfold_names (i - 1), Library.foldr (op -->)
      (map fastype_of ss, domain_type (fastype_of (nth ss (i - 1))) --> nth Ts (i - 1))), ss);
    val unfold_defs = map (fn def =>
      mk_unabs_def (n + 1) (HOLogic.mk_obj_eq (Morphism.thm phi def))) unfold_def_frees;

    val (((ss, TRs), unfold_fs), _) =
      lthy
      |> mk_Frees "s" sTs
      ||>> mk_Frees "r" (map (mk_relT o `I) Ts)
      ||>> mk_Frees "f" unfold_fTs;

    val mor_unfold_thm =
      let
        val Abs_inverses' = map2 (curry op RS) in_car_final_thms Abs_inverses;
        val morEs' = map (fn thm => (thm OF [mor_final_thm, UNIV_I]) RS sym) morE_thms;
        val goal = HOLogic.mk_Trueprop (mk_mor active_UNIVs ss UNIVs dtors (map (mk_unfold Ts ss) ks));
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_mor_unfold_tac ctxt m mor_UNIV_thm dtor_defs
            unfold_defs Abs_inverses' morEs' map_comp_id_thms map_cong0s)
        |> Thm.close_derivation \<^here>
      end;
    val dtor_unfold_thms = map (fn thm => (thm OF [mor_unfold_thm, UNIV_I]) RS sym) morE_thms;

    val (raw_coind_thms, raw_coind_thm) =
      let
        val prem = HOLogic.mk_Trueprop (mk_sbis UNIVs dtors TRs);
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 (fn R => fn T => mk_leq R (Id_const T)) TRs Ts));
        val vars = fold (Variable.add_free_names lthy) [prem, concl] [];
      in
        `split_conj_thm (Goal.prove_sorry lthy vars [] (Logic.mk_implies (prem, concl))
          (fn {context = ctxt, prems = _} => mk_raw_coind_tac ctxt bis_def bis_cong_thm bis_O_thm
            bis_converse_thm bis_Gr_thm tcoalg_thm coalgT_thm mor_T_final_thm sbis_lsbis_thm
            lsbis_incl_thms incl_lsbis_thms equiv_LSBIS_thms mor_Rep_thm Rep_injects)
          |> Thm.close_derivation \<^here>)
      end;

    val (unfold_unique_mor_thms, unfold_unique_mor_thm) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor active_UNIVs ss UNIVs dtors unfold_fs);
        fun mk_fun_eq f i = HOLogic.mk_eq (f, mk_unfold Ts ss i);
        val unique = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 mk_fun_eq unfold_fs ks));
        val vars = fold (Variable.add_free_names lthy) [prem, unique] [];

        val bis_thm = tcoalg_thm RSN (2, tcoalg_thm RS bis_image2_thm);
        val mor_thm = mor_comp_thm OF [mor_final_thm, mor_Abs_thm];

        val unique_mor = Goal.prove_sorry lthy vars [] (Logic.mk_implies (prem, unique))
          (fn {context = ctxt, prems = _} => mk_unfold_unique_mor_tac ctxt raw_coind_thms
            bis_thm mor_thm unfold_defs)
          |> Thm.close_derivation \<^here>;
      in
        `split_conj_thm unique_mor
      end;

    val (dtor_unfold_unique_thms, dtor_unfold_unique_thm) = `split_conj_thm (split_conj_prems n
      (mor_UNIV_thm RS iffD2 RS unfold_unique_mor_thm));

    val unfold_dtor_thms = map (fn thm => mor_id_thm RS thm RS sym) unfold_unique_mor_thms;

    val unfold_o_dtor_thms =
      let
        val mor = mor_comp_thm OF [mor_str_thm, mor_unfold_thm];
      in
        map2 (fn unique => fn unfold_ctor =>
          trans OF [mor RS unique, unfold_ctor]) unfold_unique_mor_thms unfold_dtor_thms
      end;

    val timer = time (timer "unfold definitions & thms");

    val map_dtors = map2 (fn Ds => fn bnf =>
      Term.list_comb (mk_map_of_bnf Ds (passiveAs @ Ts) (passiveAs @ FTs) bnf,
        map HOLogic.id_const passiveAs @ dtors)) Dss bnfs;

    fun ctor_bind i = nth external_bs (i - 1) |> Binding.prefix_name (ctorN ^ "_");
    val ctor_def_bind = rpair [] o Binding.concealed o Thm.def_binding o ctor_bind;

    fun ctor_spec i = mk_unfold Ts map_dtors i;

    val ((ctor_frees, (_, ctor_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i =>
        Local_Theory.define ((ctor_bind i, NoSyn), (ctor_def_bind i, ctor_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_ctors params =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ params) o Morphism.term phi)
        ctor_frees;
    val ctors = mk_ctors params';
    val ctor_defs = map (fn def => HOLogic.mk_obj_eq (Morphism.thm phi def)) ctor_def_frees;

    val ctor_o_dtor_thms = map2 (Local_Defs.fold lthy o single) ctor_defs unfold_o_dtor_thms;

    val dtor_o_ctor_thms =
      let
        fun mk_goal dtor ctor FT =
         mk_Trueprop_eq (HOLogic.mk_comp (dtor, ctor), HOLogic.id_const FT);
        val goals = @{map 3} mk_goal dtors ctors FTs;
      in
        @{map 5} (fn goal => fn ctor_def => fn unfold => fn map_comp_id => fn map_cong0L =>
          Goal.prove_sorry lthy [] [] goal
            (fn {context = ctxt, prems = _} => mk_dtor_o_ctor_tac ctxt ctor_def unfold map_comp_id
              map_cong0L unfold_o_dtor_thms)
          |> Thm.close_derivation \<^here>)
          goals ctor_defs dtor_unfold_thms map_comp_id_thms map_cong0L_thms
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

    val timer = time (timer "ctor definitions & thms");

    val (((((Jzs, Jzs_copy), Jzs1), Jzs2), phis), _) =
      lthy
      |> mk_Frees "z" Ts
      ||>> mk_Frees "z'" Ts
      ||>> mk_Frees "z1" Ts
      ||>> mk_Frees "z2" Ts
      ||>> mk_Frees "P" (map2 mk_pred2T Ts Ts);

    val (coinduct_params, dtor_coinduct_thm) =
      let
        val rels = map (Term.subst_atomic_types ((activeAs ~~ Ts) @ (activeBs ~~ Ts))) relsAsBs;

        fun mk_concl phi z1 z2 = HOLogic.mk_imp (phi $ z1 $ z2, HOLogic.mk_eq (z1, z2));
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (@{map 3} mk_concl phis Jzs1 Jzs2));

        fun mk_rel_prem phi dtor rel Jz Jz_copy =
          let
            val concl = Term.list_comb (rel, passive_eqs @ phis) $
              (dtor $ Jz) $ (dtor $ Jz_copy);
          in
            HOLogic.mk_Trueprop
              (list_all_free [Jz, Jz_copy] (HOLogic.mk_imp (phi $ Jz $ Jz_copy, concl)))
          end;

        val rel_prems = @{map 5} mk_rel_prem phis dtors rels Jzs Jzs_copy;
        val dtor_coinduct_goal = Logic.list_implies (rel_prems, concl);

        val dtor_coinduct =
          Variable.add_free_names lthy dtor_coinduct_goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] dtor_coinduct_goal
            (fn {context = ctxt, prems = _} => mk_dtor_coinduct_tac ctxt m raw_coind_thm bis_rel_thm
              rel_congs))
          |> Thm.close_derivation \<^here>;
      in
        (rev (Term.add_tfrees dtor_coinduct_goal []), dtor_coinduct)
      end;

    val timer = time (timer "coinduction");

    fun mk_dtor_map_DEADID_thm dtor_inject map_id0 =
      trans OF [iffD2 OF [dtor_inject, id_apply], map_id0 RS sym];

    fun mk_dtor_map_unique_DEADID_thm () =
      let
        val (funs, algs) =
          HOLogic.conjuncts (HOLogic.dest_Trueprop (Thm.concl_of dtor_unfold_unique_thm))
          |> map_split HOLogic.dest_eq
          ||>  snd o strip_comb o hd
          |> @{apply 2} (map (fst o dest_Var));
        fun mk_fun_insts T ix = Thm.cterm_of lthy (Var (ix, T --> T));
        val theta =
          (funs ~~ @{map 2} mk_fun_insts Ts funs) @ (algs ~~ map (Thm.cterm_of lthy) dtors);
        val dtor_unfold_dtors = (dtor_unfold_unique_thm OF
          map (fn thm => mk_trans (thm RS @{thm arg_cong2[of _ _ _ _ "(\<circ>)", OF _ refl]})
            @{thm trans[OF id_o o_id[symmetric]]}) map_id0s)
          |> split_conj_thm |> map mk_sym;
      in
        infer_instantiate lthy theta dtor_unfold_unique_thm
        |> Morphism.thm (Local_Theory.target_morphism lthy)
        |> unfold_thms lthy dtor_unfold_dtors
        |> (fn thm => thm OF replicate n sym)
      end;
(*
thm trans[OF x.dtor_unfold_unique x.dtor_unfold_unique[symmetric,
  OF trans[OF arg_cong2[of _ _ _ _ "(o)", OF pre_x.map_id0 refl] trans[OF id_o o_id[symmetric]]]],
  OF sym]
*)

    fun mk_dtor_Jrel_DEADID_thm dtor_inject bnf =
      trans OF [rel_eq_of_bnf bnf RS @{thm predicate2_eqD}, dtor_inject] RS sym;

    val JphiTs = map2 mk_pred2T passiveAs passiveBs;
    val Jpsi1Ts = map2 mk_pred2T passiveAs passiveCs;
    val Jpsi2Ts = map2 mk_pred2T passiveCs passiveBs;
    val prodTsTs' = map2 (curry HOLogic.mk_prodT) Ts Ts';
    val fstsTsTs' = map fst_const prodTsTs';
    val sndsTsTs' = map snd_const prodTsTs';
    val activephiTs = map2 mk_pred2T activeAs activeBs;
    val activeJphiTs = map2 mk_pred2T Ts Ts';

    val rels = map2 (fn Ds => mk_rel_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;

    val ((((Jzs, Jz's), Jphis), activeJphis), _) =
      lthy
      |> mk_Frees "z" Ts
      ||>> mk_Frees "y" Ts'
      ||>> mk_Frees "R" JphiTs
      ||>> mk_Frees "JR" activeJphiTs;

    fun mk_Jrel_DEADID_coinduct_thm () =
      mk_xtor_rel_co_induct_thm Greatest_FP rels activeJphis (map HOLogic.eq_const Ts) Jphis
        Jzs Jz's dtors dtor's (fn {context = ctxt, prems} =>
          (unfold_thms_tac ctxt @{thms le_fun_def le_bool_def all_simps(1,2)[symmetric]} THEN
          REPEAT_DETERM (rtac ctxt allI 1) THEN rtac ctxt (dtor_coinduct_thm OF prems) 1)) lthy;

    (*register new codatatypes as BNFs*)
    val (timer, Jbnfs, (dtor_Jmap_o_thms, dtor_Jmap_thms), dtor_Jmap_unique_thm, dtor_Jset_thmss',
      dtor_Jrel_thms, Jrel_coinduct_thm, Jbnf_notes, dtor_Jset_induct_thms, lthy) =
      if m = 0 then
        (timer, replicate n DEADID_bnf,
        map_split (`(mk_pointfree2 lthy)) (map2 mk_dtor_map_DEADID_thm dtor_inject_thms map_ids),
        mk_dtor_map_unique_DEADID_thm (),
        replicate n [],
        map2 mk_dtor_Jrel_DEADID_thm dtor_inject_thms bnfs,
        mk_Jrel_DEADID_coinduct_thm (), [], [], lthy)
      else let
        val fTs = map2 (curry op -->) passiveAs passiveBs;
        val gTs = map2 (curry op -->) passiveBs passiveCs;
        val uTs = map2 (curry op -->) Ts Ts';
        val (((((nat, nat'), (Jzs, Jzs')), (hrecs, hrecs')), (fs, fs')), _) =
          lthy
          |> yield_singleton (apfst (op ~~) oo mk_Frees' "n") HOLogic.natT
          ||>> mk_Frees' "z" Ts
          ||>> mk_Frees' "rec" hrecTs
          ||>> mk_Frees' "f" fTs;

        val map_FTFT's = map2 (fn Ds =>
          mk_map_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;

        fun mk_maps ATs BTs Ts mk_T =
          map2 (fn Ds => mk_map_of_bnf Ds (ATs @ Ts) (BTs @ map mk_T Ts)) Dss bnfs;
        fun mk_Fmap mk_const fs Ts Fmap = Term.list_comb (Fmap, fs @ map mk_const Ts);
        fun mk_map mk_const mk_T Ts fs Ts' dtors mk_maps =
          mk_unfold Ts' (map2 (fn dtor => fn Fmap =>
            HOLogic.mk_comp (mk_Fmap mk_const fs Ts Fmap, dtor)) dtors (mk_maps Ts mk_T));
        val mk_map_id = mk_map HOLogic.id_const I;
        val mk_mapsAB = mk_maps passiveAs passiveBs;
        val fs_maps = map (mk_map_id Ts fs Ts' dtors mk_mapsAB) ks;

        val set_bss =
          map (flat o map2 (fn B => fn b =>
            if member (op =) resDs (TFree B) then [] else [b]) resBs) set_bss0;

        fun col_bind j = mk_internal_b (colN ^ (if m = 1 then "" else string_of_int j));
        val col_def_bind = rpair [] o Thm.def_binding o col_bind;

        fun col_spec j Zero hrec hrec' =
          let
            fun mk_Suc dtor sets z z' =
              let
                val (set, sets) = apfst (fn xs => nth xs (j - 1)) (chop m sets);
                fun mk_UN set k = mk_UNION (set $ (dtor $ z)) (mk_nthN n hrec k);
              in
                Term.absfree z'
                  (mk_union (set $ (dtor $ z), Library.foldl1 mk_union (map2 mk_UN sets ks)))
              end;

            val Suc = Term.absdummy HOLogic.natT (Term.absfree hrec'
              (HOLogic.mk_tuple (@{map 4} mk_Suc dtors FTs_setss Jzs Jzs')));
          in
            mk_rec_nat Zero Suc
          end;

        val ((col_frees, (_, col_def_frees)), (lthy, lthy_old)) =
          lthy
          |> (snd o Local_Theory.begin_nested)
          |> @{fold_map 4} (fn j => fn Zero => fn hrec => fn hrec' => Local_Theory.define
            ((col_bind j, NoSyn), (col_def_bind j, col_spec j Zero hrec hrec')))
            ls Zeros hrecs hrecs'
          |>> apsnd split_list o split_list
          ||> `Local_Theory.end_nested;

        val phi = Proof_Context.export_morphism lthy_old lthy;

        val col_defs = map (fn def => HOLogic.mk_obj_eq (Morphism.thm phi def)) col_def_frees;
        val cols = map (fst o Term.dest_Const o Morphism.term phi) col_frees;

        fun mk_col Ts nat i j T =
          let
            val hrecT = HOLogic.mk_tupleT (map (fn U => U --> HOLogic.mk_setT T) Ts)
            val colT = HOLogic.natT --> hrecT;
          in
            mk_nthN n (Term.list_comb (Const (nth cols (j - 1), colT), [nat])) i
          end;

        val col_0ss = mk_rec_simps n @{thm rec_nat_0_imp} col_defs;
        val col_Sucss = mk_rec_simps n @{thm rec_nat_Suc_imp} col_defs;
        val col_0ss' = transpose col_0ss;
        val col_Sucss' = transpose col_Sucss;

        fun mk_set Ts i j T =
          Abs (Name.uu, nth Ts (i - 1), mk_UNION (HOLogic.mk_UNIV HOLogic.natT)
            (Term.absfree nat' (mk_col Ts nat i j T $ Bound 1)));

        val setss = map (fn i => map2 (mk_set Ts i) ls passiveAs) ks;

        val (Jbnf_consts, lthy) =
          @{fold_map 8} (fn b => fn map_b => fn rel_b => fn pred_b => fn set_bs => fn mapx =>
              fn sets => fn T => fn lthy =>
            define_bnf_consts Hardly_Inline (user_policy Note_Some lthy) false (SOME deads)
              map_b rel_b pred_b set_bs
              (((((((b, T), fold_rev Term.absfree fs' mapx), sets), sbd),
                [Const (\<^const_name>\<open>undefined\<close>, T)]), NONE), NONE) lthy)
          bs map_bs rel_bs pred_bs set_bss fs_maps setss Ts lthy;

        val (_, Jconsts, Jconst_defs, mk_Jconsts) = @{split_list 4} Jbnf_consts;
        val (_, Jsetss, Jbds_Ds, _, _, _) = @{split_list 6} Jconsts;
        val (Jmap_defs, Jset_defss, Jbd_defs, _, Jrel_defs, Jpred_defs) =
          @{split_list 6} Jconst_defs;
        val (mk_Jmaps_Ds, mk_Jt_Ds, _, mk_Jrels_Ds, mk_Jpreds_Ds, _, _) =
          @{split_list 7} mk_Jconsts;

        val Jrel_unabs_defs = map (fn def => mk_unabs_def m (HOLogic.mk_obj_eq def)) Jrel_defs;
        val Jpred_unabs_defs = map (fn def => mk_unabs_def m (HOLogic.mk_obj_eq def)) Jpred_defs;
        val Jset_defs = flat Jset_defss;

        fun mk_Jmaps As Bs = map (fn mk => mk deads As Bs) mk_Jmaps_Ds;
        fun mk_Jsetss As = map2 (fn mk => fn Jsets => map (mk deads As) Jsets) mk_Jt_Ds Jsetss;
        val Jbds = map2 (fn mk => mk deads passiveAs) mk_Jt_Ds Jbds_Ds;
        fun mk_Jrels As Bs = map (fn mk => mk deads As Bs) mk_Jrels_Ds;
        fun mk_Jpreds As = map (fn mk => mk deads As) mk_Jpreds_Ds;

        val Jmaps = mk_Jmaps passiveAs passiveBs;
        val (Jsetss_by_range, Jsetss_by_bnf) = `transpose (mk_Jsetss passiveAs);

        val timer = time (timer "bnf constants for the new datatypes");

        val ((((((((((((((((((((ys, ys'), (nat, nat')), (Jzs, Jzs')), Jz's), Jzs_copy), Jz's_copy),
            dtor_set_induct_phiss), Jphis), Jpsi1s), Jpsi2s), activeJphis), fs), fs_copy), gs), us),
            (Jys, Jys')), (Jys_copy, Jys'_copy)), (ys_copy, ys'_copy)), Kss), names_lthy) =
          lthy
          |> mk_Frees' "y" passiveAs
          ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "n") HOLogic.natT
          ||>> mk_Frees' "z" Ts
          ||>> mk_Frees "y" Ts'
          ||>> mk_Frees "z'" Ts
          ||>> mk_Frees "y'" Ts'
          ||>> mk_Freess "P" (map (fn A => map (mk_pred2T A) Ts) passiveAs)
          ||>> mk_Frees "R" JphiTs
          ||>> mk_Frees "R" Jpsi1Ts
          ||>> mk_Frees "Q" Jpsi2Ts
          ||>> mk_Frees "JR" activeJphiTs
          ||>> mk_Frees "f" fTs
          ||>> mk_Frees "f" fTs
          ||>> mk_Frees "g" gTs
          ||>> mk_Frees "u" uTs
          ||>> mk_Frees' "b" Ts'
          ||>> mk_Frees' "b" Ts'
          ||>> mk_Frees' "y" passiveAs
          ||>> mk_Freess "K" (map (fn AT => map (fn T => T --> AT) Ts) ATs);

        val fs_Jmaps = map (fn m => Term.list_comb (m, fs)) Jmaps;
        val fs_copy_Jmaps = map (fn m => Term.list_comb (m, fs_copy)) Jmaps;
        val gs_Jmaps = map (fn m => Term.list_comb (m, gs)) (mk_Jmaps passiveBs passiveCs);
        val fgs_Jmaps = map (fn m => Term.list_comb (m, map2 (curry HOLogic.mk_comp) gs fs))
          (mk_Jmaps passiveAs passiveCs);

        val (dtor_Jmap_thms, Jmap_thms) =
          let
            fun mk_goal fs_Jmap map dtor dtor' = mk_Trueprop_eq (HOLogic.mk_comp (dtor', fs_Jmap),
              HOLogic.mk_comp (Term.list_comb (map, fs @ fs_Jmaps), dtor));
            val goals = @{map 4} mk_goal fs_Jmaps map_FTFT's dtors dtor's;
            val maps =
              @{map 5} (fn goal => fn unfold => fn map_comp => fn map_cong0 => fn map_arg_cong =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Jmap_defs THEN
                     mk_map_tac ctxt m n map_arg_cong unfold map_comp map_cong0))
                |> Thm.close_derivation \<^here>)
              goals dtor_unfold_thms map_comps map_cong0s map_arg_cong_thms;
          in
            map_split (fn thm => (thm RS @{thm comp_eq_dest}, thm)) maps
          end;

        val (dtor_Jmap_unique_thms, dtor_Jmap_unique_thm) =
          let
            fun mk_prem u map dtor dtor' =
              mk_Trueprop_eq (HOLogic.mk_comp (dtor', u),
                HOLogic.mk_comp (Term.list_comb (map, fs @ us), dtor));
            val prems = @{map 4} mk_prem us map_FTFT's dtors dtor's;
            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map2 (curry HOLogic.mk_eq) us fs_Jmaps));
            val vars = fold (Variable.add_free_names lthy) (goal :: prems) [];
          in
            `split_conj_thm (Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, goal))
              (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Jmap_defs THEN
                mk_dtor_map_unique_tac ctxt dtor_unfold_unique_thm sym_map_comps)
            |> Thm.close_derivation \<^here>)
          end;

        val Jmap_comp0_thms =
          let
            val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
              (@{map 3} (fn fmap => fn gmap => fn fgmap =>
                 HOLogic.mk_eq (HOLogic.mk_comp (gmap, fmap), fgmap))
              fs_Jmaps gs_Jmaps fgs_Jmaps))
            val vars = Variable.add_free_names lthy goal [];
          in
            split_conj_thm (Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                mk_map_comp0_tac ctxt Jmap_thms map_comp0s dtor_Jmap_unique_thm)
              |> Thm.close_derivation \<^here>)
          end;

        val timer = time (timer "map functions for the new codatatypes");

        val Jset_minimal_thms =
          let
            fun mk_passive_prem set dtor x K =
              Logic.all x (HOLogic.mk_Trueprop (mk_leq (set $ (dtor $ x)) (K $ x)));

            fun mk_active_prem dtor x1 K1 set x2 K2 =
              fold_rev Logic.all [x1, x2]
                (Logic.mk_implies (mk_Trueprop_mem (x2, set $ (dtor $ x1)),
                  HOLogic.mk_Trueprop (mk_leq (K2 $ x2) (K1 $ x1))));

            val premss = map2 (fn j => fn Ks =>
              @{map 4} mk_passive_prem (map (fn xs => nth xs (j - 1)) FTs_setss) dtors Jzs Ks @
                flat (@{map 4} (fn sets => fn s => fn x1 => fn K1 =>
                  @{map 3} (mk_active_prem s x1 K1) (drop m sets) Jzs_copy Ks) FTs_setss dtors Jzs Ks))
              ls Kss;

            val col_minimal_thms =
              let
                fun mk_conjunct j T i K x = mk_leq (mk_col Ts nat i j T $ x) (K $ x);
                fun mk_concl j T Ks = list_all_free Jzs
                  (Library.foldr1 HOLogic.mk_conj (@{map 3} (mk_conjunct j T) ks Ks Jzs));
                val concls = @{map 3} mk_concl ls passiveAs Kss;

                val goals = map2 (fn prems => fn concl =>
                  Logic.list_implies (prems, HOLogic.mk_Trueprop concl)) premss concls

                val ctss =
                  map (fn phi => map (SOME o Thm.cterm_of lthy) [Term.absfree nat' phi, nat]) concls;
              in
                @{map 4} (fn goal => fn cts => fn col_0s => fn col_Sucs =>
                  Variable.add_free_names lthy goal []
                  |> (fn vars => Goal.prove_sorry lthy vars [] goal
                    (fn {context = ctxt, prems = _} => mk_col_minimal_tac ctxt m cts col_0s
                      col_Sucs))
                  |> Thm.close_derivation \<^here>)
                goals ctss col_0ss' col_Sucss'
              end;

            fun mk_conjunct set K x = mk_leq (set $ x) (K $ x);
            fun mk_concl sets Ks = Library.foldr1 HOLogic.mk_conj (@{map 3} mk_conjunct sets Ks Jzs);
            val concls = map2 mk_concl Jsetss_by_range Kss;

            val goals = map2 (fn prems => fn concl =>
              Logic.list_implies (prems, HOLogic.mk_Trueprop concl)) premss concls;
          in
            map2 (fn goal => fn col_minimal =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Jset_defs THEN
                  mk_Jset_minimal_tac ctxt n col_minimal))
              |> Thm.close_derivation \<^here>)
            goals col_minimal_thms
          end;

        val (dtor_Jset_incl_thmss, dtor_set_Jset_incl_thmsss) =
          let
            fun mk_set_incl_Jset dtor x set Jset =
              HOLogic.mk_Trueprop (mk_leq (set $ (dtor $ x)) (Jset $ x));

            fun mk_set_Jset_incl_Jset dtor x y set Jset1 Jset2 =
              Logic.mk_implies (mk_Trueprop_mem (x, set $ (dtor $ y)),
                HOLogic.mk_Trueprop (mk_leq (Jset1 $ x) (Jset2 $ y)));

            val set_incl_Jset_goalss =
              @{map 4} (fn dtor => fn x => fn sets => fn Jsets =>
                map2 (mk_set_incl_Jset dtor x) (take m sets) Jsets)
              dtors Jzs FTs_setss Jsetss_by_bnf;

            (*x(k) : F(i)set(m+k) (dtor(i) y(i)) ==> J(k)set(j) x(k) <= J(i)set(j) y(i)*)
            val set_Jset_incl_Jset_goalsss =
              @{map 4} (fn dtori => fn yi => fn sets => fn Jsetsi =>
                @{map 3} (fn xk => fn set => fn Jsetsk =>
                  map2 (mk_set_Jset_incl_Jset dtori xk yi set) Jsetsk Jsetsi)
                Jzs_copy (drop m sets) Jsetss_by_bnf)
              dtors Jzs FTs_setss Jsetss_by_bnf;
          in
            (map2 (fn goals => fn rec_Sucs =>
              map2 (fn goal => fn rec_Suc =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Jset_defs THEN
                    mk_set_incl_Jset_tac ctxt rec_Suc))
                |> Thm.close_derivation \<^here>)
              goals rec_Sucs)
            set_incl_Jset_goalss col_Sucss,
            map2 (fn goalss => fn rec_Sucs =>
              map2 (fn k => fn goals =>
                map2 (fn goal => fn rec_Suc =>
                  Variable.add_free_names lthy goal []
                  |> (fn vars => Goal.prove_sorry lthy vars [] goal
                    (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Jset_defs THEN
                      mk_set_Jset_incl_Jset_tac ctxt n rec_Suc k))
                  |> Thm.close_derivation \<^here>)
                goals rec_Sucs)
              ks goalss)
            set_Jset_incl_Jset_goalsss col_Sucss)
          end;

        val set_incl_Jset_thmss' = transpose dtor_Jset_incl_thmss;
        val set_Jset_incl_Jset_thmsss' = transpose (map transpose dtor_set_Jset_incl_thmsss);
        val set_Jset_thmss = map (map (fn thm => thm RS @{thm set_mp})) dtor_Jset_incl_thmss;
        val set_Jset_Jset_thmsss = map (map (map (fn thm => thm RS @{thm set_mp})))
          dtor_set_Jset_incl_thmsss;
        val set_Jset_thmss' = transpose set_Jset_thmss;
        val set_Jset_Jset_thmsss' = transpose (map transpose set_Jset_Jset_thmsss);

        val dtor_Jset_induct_thms =
          let
            val incls =
              maps (map (fn thm => thm RS @{thm subset_Collect_iff})) dtor_Jset_incl_thmss @
                @{thms subset_Collect_iff[OF subset_refl]};

            val cTs = map (SOME o Thm.ctyp_of lthy) params';
            fun mk_induct_tinst phis jsets y y' =
              @{map 4} (fn phi => fn jset => fn Jz => fn Jz' =>
                SOME (Thm.cterm_of lthy (Term.absfree Jz' (HOLogic.mk_Collect (fst y', snd y',
                  HOLogic.mk_conj (HOLogic.mk_mem (y, jset $ Jz), phi $ y $ Jz))))))
              phis jsets Jzs Jzs';
          in
            @{map 6} (fn set_minimal => fn set_set_inclss => fn jsets => fn y => fn y' => fn phis =>
              ((set_minimal
                |> Thm.instantiate' cTs (mk_induct_tinst phis jsets y y')
                |> unfold_thms lthy incls) OF
                (replicate n ballI @
                  maps (map (fn thm => thm RS @{thm subset_CollectI})) set_set_inclss))
              |> singleton (Proof_Context.export names_lthy lthy)
              |> rule_by_tactic lthy (ALLGOALS (TRY o etac lthy asm_rl)))
            Jset_minimal_thms set_Jset_incl_Jset_thmsss' Jsetss_by_range ys ys' dtor_set_induct_phiss
          end;

        val (dtor_Jset_thmss', dtor_Jset_thmss) =
          let
            fun mk_simp_goal relate pas_set act_sets sets dtor z set =
              relate (set $ z, mk_union (pas_set $ (dtor $ z),
                 Library.foldl1 mk_union
                   (map2 (fn X => mk_UNION (X $ (dtor $ z))) act_sets sets)));
            fun mk_goals eq =
              map2 (fn i => fn sets =>
                @{map 4} (fn Fsets =>
                  mk_simp_goal eq (nth Fsets (i - 1)) (drop m Fsets) sets)
                FTs_setss dtors Jzs sets)
              ls Jsetss_by_range;

            val le_goals = map (HOLogic.mk_Trueprop o Library.foldr1 HOLogic.mk_conj)
              (mk_goals (uncurry mk_leq));
            val set_le_thmss = map split_conj_thm
              (@{map 4} (fn goal => fn Jset_minimal => fn set_Jsets => fn set_Jset_Jsetss =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} =>
                    mk_set_le_tac ctxt n Jset_minimal set_Jsets set_Jset_Jsetss))
                |> Thm.close_derivation \<^here>)
              le_goals Jset_minimal_thms set_Jset_thmss' set_Jset_Jset_thmsss');

            val ge_goalss = map (map HOLogic.mk_Trueprop) (mk_goals (uncurry mk_leq o swap));
            val set_ge_thmss =
              @{map 3} (@{map 3} (fn goal => fn set_incl_Jset => fn set_Jset_incl_Jsets =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} =>
                    mk_set_ge_tac ctxt n set_incl_Jset set_Jset_incl_Jsets))
                |> Thm.close_derivation \<^here>))
              ge_goalss set_incl_Jset_thmss' set_Jset_incl_Jset_thmsss'
          in
            map2 (map2 (fn le => fn ge => equalityI OF [le, ge])) set_le_thmss set_ge_thmss
            |> `transpose
          end;

        val timer = time (timer "set functions for the new codatatypes");

        val colss = map2 (fn j => fn T =>
          map (fn i => mk_col Ts nat i j T) ks) ls passiveAs;
        val colss' = map2 (fn j => fn T =>
          map (fn i => mk_col Ts' nat i j T) ks) ls passiveBs;

        val col_natural_thmss =
          let
            fun mk_col_natural f map z col col' =
              HOLogic.mk_eq (mk_image f $ (col $ z), col' $ (map $ z));

            fun mk_goal f cols cols' = list_all_free Jzs (Library.foldr1 HOLogic.mk_conj
              (@{map 4} (mk_col_natural f) fs_Jmaps Jzs cols cols'));

            val goals = @{map 3} mk_goal fs colss colss';

            val ctss =
              map (fn phi => map (SOME o Thm.cterm_of lthy) [Term.absfree nat' phi, nat]) goals;

            val thms =
              @{map 4} (fn goal => fn cts => fn rec_0s => fn rec_Sucs =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] (HOLogic.mk_Trueprop goal)
                  (fn {context = ctxt, prems = _} => mk_col_natural_tac ctxt cts rec_0s rec_Sucs
                    dtor_Jmap_thms set_mapss))
                |> Thm.close_derivation \<^here>)
              goals ctss col_0ss' col_Sucss';
          in
            map (split_conj_thm o mk_specN n) thms
          end;

        val col_bd_thmss =
          let
            fun mk_col_bd z col bd = mk_ordLeq (mk_card_of (col $ z)) bd;

            fun mk_goal bds cols = list_all_free Jzs (Library.foldr1 HOLogic.mk_conj
              (@{map 3} mk_col_bd Jzs cols bds));

            val goals = map (mk_goal Jbds) colss;

            val ctss = map (fn phi => map (SOME o Thm.cterm_of lthy) [Term.absfree nat' phi, nat])
              (map (mk_goal (replicate n sbd)) colss);

            val thms =
              @{map 5} (fn j => fn goal => fn cts => fn rec_0s => fn rec_Sucs =>
                Variable.add_free_names lthy goal []
                |> (fn vars => Goal.prove_sorry lthy vars [] (HOLogic.mk_Trueprop goal)
                  (fn {context = ctxt, prems = _} => unfold_thms_tac ctxt Jbd_defs THEN
                    mk_col_bd_tac ctxt m j cts rec_0s rec_Sucs sbd_Card_order sbd_Cinfinite set_sbdss))
                |> Thm.close_derivation \<^here>)
              ls goals ctss col_0ss' col_Sucss';
          in
            map (split_conj_thm o mk_specN n) thms
          end;

        val map_cong0_thms =
          let
            val cTs = map (SOME o Thm.ctyp_of lthy o
              Term.typ_subst_atomic (passiveAs ~~ passiveBs) o TFree) coinduct_params;

            fun mk_prem z set f g y y' =
              mk_Ball (set $ z) (Term.absfree y' (HOLogic.mk_eq (f $ y, g $ y)));

            fun mk_prems sets z =
              Library.foldr1 HOLogic.mk_conj (@{map 5} (mk_prem z) sets fs fs_copy ys ys')

            fun mk_map_cong0 sets z fmap gmap =
              HOLogic.mk_imp (mk_prems sets z, HOLogic.mk_eq (fmap $ z, gmap $ z));

            fun mk_coind_body sets (x, T) z fmap gmap y y_copy =
              HOLogic.mk_conj
                (HOLogic.mk_mem (z, HOLogic.mk_Collect (x, T, mk_prems sets z)),
                  HOLogic.mk_conj (HOLogic.mk_eq (y, fmap $ z),
                    HOLogic.mk_eq (y_copy, gmap $ z)))

            fun mk_cphi sets (z' as (x, T)) z fmap gmap y' y y'_copy y_copy =
              HOLogic.mk_exists (x, T, mk_coind_body sets z' z fmap gmap y y_copy)
              |> Term.absfree y'_copy
              |> Term.absfree y'
              |> Thm.cterm_of lthy;

            val cphis = @{map 9} mk_cphi
              Jsetss_by_bnf Jzs' Jzs fs_Jmaps fs_copy_Jmaps Jys' Jys Jys'_copy Jys_copy;

            val coinduct = Thm.instantiate' cTs (map SOME cphis) dtor_coinduct_thm;

            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (@{map 4} mk_map_cong0 Jsetss_by_bnf Jzs fs_Jmaps fs_copy_Jmaps));
            val vars = Variable.add_free_names lthy goal [];

            val thm =
              Goal.prove_sorry lthy vars [] goal
                (fn {context = ctxt, prems = _} => mk_mcong_tac ctxt m (rtac ctxt coinduct) map_comps
                  dtor_Jmap_thms map_cong0s
                  set_mapss set_Jset_thmss set_Jset_Jset_thmsss in_rels)
              |> Thm.close_derivation \<^here>;
          in
            split_conj_thm thm
          end;

        val in_Jrels = map (fn def => trans OF [def, @{thm OO_Grp_alt}] RS @{thm predicate2_eqD})
            Jrel_unabs_defs;

        val Jrels = mk_Jrels passiveAs passiveBs;
        val Jpreds = mk_Jpreds passiveAs;
        val Jrelphis = map (fn rel => Term.list_comb (rel, Jphis)) Jrels;
        val relphis = map (fn rel => Term.list_comb (rel, Jphis @ Jrelphis)) rels;
        val Jrelpsi1s = map (fn rel => Term.list_comb (rel, Jpsi1s)) (mk_Jrels passiveAs passiveCs);
        val Jrelpsi2s = map (fn rel => Term.list_comb (rel, Jpsi2s)) (mk_Jrels passiveCs passiveBs);
        val Jrelpsi12s = map (fn rel =>
            Term.list_comb (rel, map2 (curry mk_rel_compp) Jpsi1s Jpsi2s)) Jrels;

        val dtor_Jrel_thms =
          let
            fun mk_goal Jz Jz' dtor dtor' Jrelphi relphi =
              mk_Trueprop_eq (Jrelphi $ Jz $ Jz', relphi $ (dtor $ Jz) $ (dtor' $ Jz'));
            val goals = @{map 6} mk_goal Jzs Jz's dtors dtor's Jrelphis relphis;
          in
            @{map 12} (fn i => fn goal => fn in_rel => fn map_comp0 => fn map_cong0 =>
              fn dtor_map => fn dtor_sets => fn dtor_inject => fn dtor_ctor =>
              fn set_map0s => fn dtor_set_incls => fn dtor_set_set_inclss =>
              Variable.add_free_names lthy goal []
              |> (fn vars => Goal.prove_sorry lthy vars [] goal
                (fn {context = ctxt, prems = _} =>
                  mk_dtor_rel_tac ctxt in_Jrels i in_rel map_comp0 map_cong0 dtor_map dtor_sets
                    dtor_inject dtor_ctor set_map0s dtor_set_incls dtor_set_set_inclss))
              |> Thm.close_derivation \<^here>)
            ks goals in_rels map_comps map_cong0s dtor_Jmap_thms dtor_Jset_thmss'
              dtor_inject_thms dtor_ctor_thms set_mapss dtor_Jset_incl_thmss
              dtor_set_Jset_incl_thmsss
          end;

      val passiveABs = map2 (curry HOLogic.mk_prodT) passiveAs passiveBs;
      val zip_ranTs = passiveABs @ prodTsTs';
      val allJphis = Jphis @ activeJphis;
      val zipFTs = mk_FTs zip_ranTs;
      val zipTs = @{map 3} (fn T => fn T' => fn FT => T --> T' --> FT) Ts Ts' zipFTs;
      val zip_zTs = mk_Ts passiveABs;
      val (((zips, (abs, abs')), (zip_zs, zip_zs')), _) =
        names_lthy
        |> mk_Frees "zip" zipTs
        ||>> mk_Frees' "ab" passiveABs
        ||>> mk_Frees' "z" zip_zTs;

      val Iphi_sets =
        map2 (fn phi => fn T => HOLogic.Collect_const T $ HOLogic.mk_case_prod phi) allJphis zip_ranTs;
      val in_phis = map2 (mk_in Iphi_sets) (mk_setss zip_ranTs) zipFTs;
      val fstABs = map fst_const passiveABs;
      val all_fsts = fstABs @ fstsTsTs';
      val map_all_fsts = map2 (fn Ds => fn bnf =>
        Term.list_comb (mk_map_of_bnf Ds zip_ranTs (passiveAs @ Ts) bnf, all_fsts)) Dss bnfs;
      val Jmap_fsts = map2 (fn map => fn T => if m = 0 then HOLogic.id_const T
        else Term.list_comb (map, fstABs)) (mk_Jmaps passiveABs passiveAs) Ts;

      val sndABs = map snd_const passiveABs;
      val all_snds = sndABs @ sndsTsTs';
      val map_all_snds = map2 (fn Ds => fn bnf =>
        Term.list_comb (mk_map_of_bnf Ds zip_ranTs (passiveBs @ Ts') bnf, all_snds)) Dss bnfs;
      val Jmap_snds = map2 (fn map => fn T => if m = 0 then HOLogic.id_const T
        else Term.list_comb (map, sndABs)) (mk_Jmaps passiveABs passiveBs) Ts;
      val zip_unfolds = map (mk_unfold zip_zTs (map HOLogic.mk_case_prod zips)) ks;
      val zip_setss = mk_Jsetss passiveABs |> transpose;

      fun Jrel_coinduct_tac {context = ctxt, prems = CIHs} =
        let
          fun mk_helper_prem phi in_phi zip x y map map' dtor dtor' =
            let
              val zipxy = zip $ x $ y;
            in
              HOLogic.mk_Trueprop (list_all_free [x, y]
                (HOLogic.mk_imp (phi $ x $ y, HOLogic.mk_conj (HOLogic.mk_mem (zipxy, in_phi),
                  HOLogic.mk_conj (HOLogic.mk_eq (map $ zipxy, dtor $ x),
                    HOLogic.mk_eq (map' $ zipxy, dtor' $ y))))))
            end;
          val helper_prems = @{map 9} mk_helper_prem
            activeJphis in_phis zips Jzs Jz's map_all_fsts map_all_snds dtors dtor's;
          fun mk_helper_coind_phi fst phi x alt y map zip_unfold =
            list_exists_free [if fst then y else x] (HOLogic.mk_conj (phi $ x $ y,
              HOLogic.mk_eq (alt, map $ (zip_unfold $ HOLogic.mk_prod (x, y)))))
          val coind1_phis = @{map 6} (mk_helper_coind_phi true)
            activeJphis Jzs Jzs_copy Jz's Jmap_fsts zip_unfolds;
          val coind2_phis = @{map 6} (mk_helper_coind_phi false)
              activeJphis Jzs Jz's_copy Jz's Jmap_snds zip_unfolds;
          fun mk_cts zs z's phis =
            @{map 3} (fn z => fn z' => fn phi =>
              SOME (Thm.cterm_of lthy (fold_rev (Term.absfree o Term.dest_Free) [z', z] phi)))
            zs z's phis @
            map (SOME o Thm.cterm_of lthy) (splice z's zs);
          val cts1 = mk_cts Jzs Jzs_copy coind1_phis;
          val cts2 = mk_cts Jz's Jz's_copy coind2_phis;

          fun mk_helper_coind_concl z alt coind_phi =
            HOLogic.mk_imp (coind_phi, HOLogic.mk_eq (alt, z));
          val helper_coind1_concl =
            HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
              (@{map 3} mk_helper_coind_concl Jzs Jzs_copy coind1_phis));
          val helper_coind2_concl =
            HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
              (@{map 3} mk_helper_coind_concl Jz's Jz's_copy coind2_phis));

          fun mk_helper_coind_thms fst concl cts =
            let
              val vars = fold (Variable.add_free_names lthy) (concl :: helper_prems) [];
            in
              Goal.prove_sorry lthy vars [] (Logic.list_implies (helper_prems, concl))
                (fn {context = ctxt, prems = _} =>
                  mk_rel_coinduct_coind_tac ctxt fst m
                    (infer_instantiate' ctxt cts dtor_coinduct_thm) ks map_comps map_cong0s
                    map_arg_cong_thms set_mapss dtor_unfold_thms dtor_Jmap_thms in_rels)
              |> Thm.close_derivation \<^here>
              |> split_conj_thm
            end;

          val helper_coind1_thms = mk_helper_coind_thms true helper_coind1_concl cts1;
          val helper_coind2_thms = mk_helper_coind_thms false helper_coind2_concl cts2;

          fun mk_helper_ind_phi phi ab fst snd z active_phi x y zip_unfold =
            list_all_free [x, y] (HOLogic.mk_imp
              (HOLogic.mk_conj (active_phi $ x $ y,
                 HOLogic.mk_eq (z, zip_unfold $ HOLogic.mk_prod (x, y))),
              phi $ (fst $ ab) $ (snd $ ab)));
          val helper_ind_phiss =
            @{map 4} (fn Jphi => fn ab => fn fst => fn snd =>
              @{map 5} (mk_helper_ind_phi Jphi ab fst snd)
              zip_zs activeJphis Jzs Jz's zip_unfolds)
            Jphis abs fstABs sndABs;
          val ctss = map2 (fn ab' => fn phis =>
              map2 (fn z' => fn phi =>
                SOME (Thm.cterm_of lthy (Term.absfree ab' (Term.absfree z' phi))))
              zip_zs' phis @
              map (SOME o Thm.cterm_of lthy) zip_zs)
            abs' helper_ind_phiss;
          fun mk_helper_ind_concl ab' z ind_phi set =
            mk_Ball (set $ z) (Term.absfree ab' ind_phi);

          val mk_helper_ind_concls =
            @{map 3} (fn ab' => fn ind_phis => fn zip_sets =>
              @{map 3} (mk_helper_ind_concl ab') zip_zs ind_phis zip_sets)
            abs' helper_ind_phiss zip_setss
            |> map (HOLogic.mk_Trueprop o Library.foldr1 HOLogic.mk_conj);

          val helper_ind_thmss = if m = 0 then replicate n [] else
            @{map 4} (fn concl => fn j => fn set_induct => fn cts =>
              fold (Variable.add_free_names lthy) (concl :: helper_prems) []
              |> (fn vars => Goal.prove_sorry lthy vars [] (Logic.list_implies (helper_prems, concl))
                (fn {context = ctxt, prems = _} =>
                  mk_rel_coinduct_ind_tac ctxt m ks
                    dtor_unfold_thms set_mapss j (infer_instantiate' ctxt cts set_induct)))
              |> Thm.close_derivation \<^here>
              |> split_conj_thm)
            mk_helper_ind_concls ls dtor_Jset_induct_thms ctss
            |> transpose;
        in
          mk_rel_coinduct_tac ctxt CIHs in_rels in_Jrels
            helper_ind_thmss helper_coind1_thms helper_coind2_thms
        end;

      val Jrel_coinduct_thm =
        mk_xtor_rel_co_induct_thm Greatest_FP rels activeJphis Jrels Jphis Jzs Jz's dtors dtor's
          Jrel_coinduct_tac lthy;

        val le_Jrel_OO_thm =
          let
            fun mk_le_Jrel_OO Jrelpsi1 Jrelpsi2 Jrelpsi12 =
              mk_leq (mk_rel_compp (Jrelpsi1, Jrelpsi2)) Jrelpsi12;
            val goals = @{map 3} mk_le_Jrel_OO Jrelpsi1s Jrelpsi2s Jrelpsi12s;

            val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj goals);
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_le_rel_OO_tac ctxt Jrel_coinduct_thm dtor_Jrel_thms le_rel_OOs)
            |> Thm.close_derivation \<^here>
          end;

        val timer = time (timer "helpers for BNF properties");

        fun close_wit I wit = (I, fold_rev Term.absfree (map (nth ys') I) wit);

        val all_unitTs = replicate live HOLogic.unitT;
        val unitTs = replicate n HOLogic.unitT;
        val unit_funs = replicate n (Term.absdummy HOLogic.unitT HOLogic.unit);
        fun mk_map_args I =
          map (fn i =>
            if member (op =) I i then Term.absdummy HOLogic.unitT (nth ys i)
            else mk_undefined (HOLogic.unitT --> nth passiveAs i))
          (0 upto (m - 1));

        fun mk_nat_wit Ds bnf (I, wit) () =
          let
            val passiveI = filter (fn i => i < m) I;
            val map_args = mk_map_args passiveI;
          in
            Term.absdummy HOLogic.unitT (Term.list_comb
              (mk_map_of_bnf Ds all_unitTs (passiveAs @ unitTs) bnf, map_args @ unit_funs) $ wit)
          end;

        fun mk_dummy_wit Ds bnf I =
          let
            val map_args = mk_map_args I;
          in
            Term.absdummy HOLogic.unitT (Term.list_comb
              (mk_map_of_bnf Ds all_unitTs (passiveAs @ unitTs) bnf, map_args @ unit_funs) $
              mk_undefined (mk_T_of_bnf Ds all_unitTs bnf))
          end;

        val nat_witss =
          map2 (fn Ds => fn bnf => mk_wits_of_bnf (replicate (nwits_of_bnf bnf) Ds)
            (replicate (nwits_of_bnf bnf) (replicate live HOLogic.unitT)) bnf
            |> map (fn (I, wit) =>
              (I, Lazy.lazy (mk_nat_wit Ds bnf (I, Term.list_comb (wit, map (K HOLogic.unit) I))))))
          Dss bnfs;

        val nat_wit_thmss = map2 (curry op ~~) nat_witss (map wit_thmss_of_bnf bnfs)

        val Iss = map (map fst) nat_witss;

        fun filter_wits (I, wit) =
          let val J = filter (fn i => i < m) I;
          in (J, (length J < length I, wit)) end;

        val wit_treess = map_index (fn (i, Is) =>
          map_index (finish Iss m [i+m] (i+m)) Is) Iss
          |> map (minimize_wits o map filter_wits o minimize_wits o flat);

        val coind_wit_argsss =
          map (map (tree_to_coind_wits nat_wit_thmss o snd o snd) o filter (fst o snd)) wit_treess;

        val nonredundant_coind_wit_argsss =
          fold (fn i => fn argsss =>
            nth_map (i - 1) (filter_out (fn xs =>
              exists (fn ys =>
                let
                  val xs' = (map (fst o fst) xs, snd (fst (hd xs)));
                  val ys' = (map (fst o fst) ys, snd (fst (hd ys)));
                in
                  eq_pair (subset (op =)) (eq_set (op =)) (xs', ys') andalso not (fst xs' = fst ys')
                end)
              (flat argsss)))
            argsss)
          ks coind_wit_argsss;

        fun prepare_args args =
          let
            val I = snd (fst (hd args));
            val (dummys, args') =
              map_split (fn i =>
                (case find_first (fn arg => fst (fst arg) = i - 1) args of
                  SOME (_, ((_, wit), thms)) => (NONE, (Lazy.force wit, thms))
                | NONE =>
                  (SOME (i - 1), (mk_dummy_wit (nth Dss (i - 1)) (nth bnfs (i - 1)) I, []))))
              ks;
          in
            ((I, dummys), apsnd flat (split_list args'))
          end;

        fun mk_coind_wits ((I, dummys), (args, thms)) =
          ((I, dummys), (map (fn i => mk_unfold Ts args i $ HOLogic.unit) ks, thms));

        val coind_witss =
          maps (map (mk_coind_wits o prepare_args)) nonredundant_coind_wit_argsss;

        val witss = map2 (fn Ds => fn bnf => mk_wits_of_bnf
          (replicate (nwits_of_bnf bnf) Ds)
          (replicate (nwits_of_bnf bnf) (passiveAs @ Ts)) bnf) Dss bnfs;

        val ctor_witss =
          map (map (uncurry close_wit o tree_to_ctor_wit ys ctors witss o snd o snd) o
            filter_out (fst o snd)) wit_treess;

        fun mk_coind_wit_thms ((I, dummys), (wits, wit_thms)) =
          let
            fun mk_goal sets y y_copy y'_copy j =
              let
                fun mk_conjunct set z dummy wit =
                  mk_Ball (set $ z) (Term.absfree y'_copy
                    (if dummy = NONE orelse member (op =) I (j - 1) then
                      HOLogic.mk_imp (HOLogic.mk_eq (z, wit),
                        if member (op =) I (j - 1) then HOLogic.mk_eq (y_copy, y)
                        else \<^term>\<open>False\<close>)
                    else \<^term>\<open>True\<close>));
              in
                HOLogic.mk_Trueprop
                  (Library.foldr1 HOLogic.mk_conj (@{map 4} mk_conjunct sets Jzs dummys wits))
              end;
            val goals = @{map 5} mk_goal Jsetss_by_range ys ys_copy ys'_copy ls;
          in
            map2 (fn goal => fn induct =>
              Variable.add_free_names lthy goal []
              |> (fn vars => Goal.prove_sorry lthy vars [] goal
                (fn {context = ctxt, prems = _} => mk_coind_wit_tac ctxt induct dtor_unfold_thms
                  (flat set_mapss) wit_thms))
              |> Thm.close_derivation \<^here>)
            goals dtor_Jset_induct_thms
            |> map split_conj_thm
            |> transpose
            |> map (map_filter (try (fn thm => thm RS bspec RS mp)))
            |> curry op ~~ (map_index Library.I (map (close_wit I) wits))
            |> filter (fn (_, thms) => length thms = m)
          end;

        val coind_wit_thms = maps mk_coind_wit_thms coind_witss;

        val (wit_thmss, all_witss) =
          fold (fn ((i, wit), thms) => fn witss =>
            nth_map i (fn (thms', wits) => (thms @ thms', wit :: wits)) witss)
          coind_wit_thms (map (pair []) ctor_witss)
          |> map (apsnd (map snd o minimize_wits))
          |> split_list;

        val timer = time (timer "witnesses");

        val map_id0_tacs =
          map2 (fn thm => fn thm' => fn ctxt =>
            mk_map_id0_tac ctxt Jmap_thms thm thm')
          dtor_unfold_unique_thms unfold_dtor_thms;
        val map_comp0_tacs = map (fn thm => fn ctxt => rtac ctxt (thm RS sym) 1) Jmap_comp0_thms;
        val map_cong0_tacs = map (fn thm => fn ctxt => mk_map_cong0_tac ctxt m thm) map_cong0_thms;
        val set_map0_tacss =
          map (map (fn col => fn ctxt =>
            unfold_thms_tac ctxt Jset_defs THEN mk_set_map0_tac ctxt col))
          (transpose col_natural_thmss);

        val Jbd_card_orders = map (fn def => Local_Defs.fold lthy [def] sbd_card_order) Jbd_defs;
        val Jbd_Cinfinites = map (fn def => Local_Defs.fold lthy [def] sbd_Cinfinite) Jbd_defs;

        val bd_co_tacs = map (fn thm => fn ctxt => rtac ctxt thm 1) Jbd_card_orders;
        val bd_cinf_tacs = map (fn thm => fn ctxt => rtac ctxt (thm RS conjunct1) 1) Jbd_Cinfinites;

        val set_bd_tacss =
          map2 (fn Cinf => map (fn col => fn ctxt =>
            unfold_thms_tac ctxt Jset_defs THEN mk_set_bd_tac ctxt Cinf col))
          Jbd_Cinfinites (transpose col_bd_thmss);

        val le_rel_OO_tacs = map (fn i => fn ctxt =>
          rtac ctxt (le_Jrel_OO_thm RS mk_conjunctN n i) 1) ks;

        val rel_OO_Grp_tacs = map (fn def => fn ctxt => rtac ctxt def 1) Jrel_unabs_defs;

        val pred_set_tacs = map (fn def => fn ctxt => rtac ctxt def 1) Jpred_unabs_defs;

        val tacss = @{map 10} zip_axioms map_id0_tacs map_comp0_tacs map_cong0_tacs set_map0_tacss
          bd_co_tacs bd_cinf_tacs set_bd_tacss le_rel_OO_tacs rel_OO_Grp_tacs pred_set_tacs;

        fun wit_tac thms ctxt =
          mk_wit_tac ctxt n dtor_ctor_thms (flat dtor_Jset_thmss) (maps wit_thms_of_bnf bnfs) thms;

        val (Jbnfs, lthy) =
          @{fold_map 7} (fn tacs => fn map_b => fn rel_b => fn pred_b => fn set_bs => fn wit_thms =>
              fn consts =>
            bnf_def Hardly_Inline (user_policy Note_Some) false I tacs (wit_tac wit_thms)
              (SOME deads) map_b rel_b pred_b set_bs consts)
          tacss map_bs rel_bs pred_bs set_bss wit_thmss
          (((((((replicate n Binding.empty ~~ Ts) ~~ Jmaps) ~~ Jsetss_by_bnf) ~~ Jbds) ~~
            all_witss) ~~ map SOME Jrels) ~~ map SOME Jpreds)
          lthy;

        val timer = time (timer "registered new codatatypes as BNFs");

        val ls' = if m = 1 then [0] else ls;

        val Jbnf_common_notes =
          map2 (fn i => fn thm => (mk_dtor_set_inductN i, [thm])) ls' dtor_Jset_induct_thms
          |> map (fn (thmN, thms) =>
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

        val Jbnf_notes =
          [(dtor_mapN, map single dtor_Jmap_thms),
          (dtor_map_uniqueN, map single dtor_Jmap_unique_thms),
          (dtor_relN, map single dtor_Jrel_thms),
          (dtor_set_inclN, dtor_Jset_incl_thmss),
          (dtor_set_set_inclN, map flat dtor_set_Jset_incl_thmsss)] @
          map2 (fn i => fn thms => (mk_dtor_setN i, map single thms)) ls' dtor_Jset_thmss
          |> maps (fn (thmN, thmss) =>
            map2 (fn b => fn thms =>
              ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
            bs thmss)
      in
        (timer, Jbnfs, (Jmap_thms, dtor_Jmap_thms), dtor_Jmap_unique_thm, dtor_Jset_thmss',
          dtor_Jrel_thms, Jrel_coinduct_thm, Jbnf_common_notes @ Jbnf_notes, dtor_Jset_induct_thms,
          lthy)
      end;

    val ((Jphis, activephis), _) =
      lthy
      |> mk_Frees "R" JphiTs
      ||>> mk_Frees "S" activephiTs;

    val dtor_unfold_o_Jmap_thms = mk_xtor_co_iter_o_map_thms Greatest_FP false m
      dtor_unfold_unique_thm dtor_Jmap_o_thms (map (mk_pointfree2 lthy) dtor_unfold_thms)
      sym_map_comps map_cong0s;

    val rels = map2 (fn Ds => mk_rel_of_bnf Ds allAs allBs') Dss bnfs;
    val Jrels = if m = 0 then map HOLogic.eq_const Ts
      else map (mk_rel_of_bnf deads passiveAs passiveBs) Jbnfs;

    val dtor_unfold_transfer_thms =
      mk_xtor_co_iter_transfer_thms Greatest_FP rels activephis activephis Jrels Jphis
        (mk_unfolds passiveAs activeAs) (mk_unfolds passiveBs activeBs)
        (fn {context = ctxt, prems = _} => mk_unfold_transfer_tac ctxt m Jrel_coinduct_thm
          (map map_transfer_of_bnf bnfs) dtor_unfold_thms)
        lthy;

    val timer = time (timer "relator coinduction");

    fun mk_Ts As = map (typ_subst_atomic (passiveAs ~~ As)) Ts;
    val export = map (Morphism.term (Local_Theory.target_morphism lthy))
    val ((corecs, (dtor_corec_thms, dtor_corec_unique_thm, dtor_corec_o_Jmap_thms,
        dtor_corec_transfer_thms)), lthy) = lthy
      |> derive_xtor_co_recs Greatest_FP external_bs mk_Ts (Dss, resDs) bnfs
        (export dtors) (export unfolds)
        dtor_unfold_unique_thm dtor_unfold_thms dtor_unfold_transfer_thms
        dtor_Jmap_thms dtor_Jrel_thms (replicate n NONE);

    val timer = time (timer "recursor");

    val common_notes =
      [(dtor_coinductN, [dtor_coinduct_thm]),
      (dtor_rel_coinductN, [Jrel_coinduct_thm])]
      |> map (fn (thmN, thms) =>
        ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

    val notes =
      [(ctor_dtorN, ctor_dtor_thms),
      (ctor_exhaustN, ctor_exhaust_thms),
      (ctor_injectN, ctor_inject_thms),
      (dtor_ctorN, dtor_ctor_thms),
      (dtor_exhaustN, dtor_exhaust_thms),
      (dtor_injectN, dtor_inject_thms),
      (dtor_unfoldN, dtor_unfold_thms),
      (dtor_unfold_o_mapN, dtor_unfold_o_Jmap_thms),
      (dtor_unfold_transferN, dtor_unfold_transfer_thms),
      (dtor_unfold_uniqueN, dtor_unfold_unique_thms)]
      |> map (apsnd (map single))
      |> maps (fn (thmN, thmss) =>
        map2 (fn b => fn thms =>
          ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
        bs thmss);

    val lthy' = lthy |> internals ? snd o Local_Theory.notes (common_notes @ notes @ Jbnf_notes);

    val fp_res =
      {Ts = Ts, bnfs = Jbnfs, pre_bnfs = bnfs, absT_infos = absT_infos,
       ctors = ctors, dtors = dtors, xtor_un_folds = unfolds, xtor_co_recs = export corecs,
       xtor_co_induct = dtor_coinduct_thm, dtor_ctors = dtor_ctor_thms, ctor_dtors = ctor_dtor_thms,
       ctor_injects = ctor_inject_thms, dtor_injects = dtor_inject_thms, xtor_maps = dtor_Jmap_thms,
       xtor_map_unique = dtor_Jmap_unique_thm, xtor_setss = dtor_Jset_thmss',
       xtor_rels = dtor_Jrel_thms, xtor_un_fold_thms = dtor_unfold_thms,
       xtor_co_rec_thms = dtor_corec_thms, xtor_un_fold_unique = dtor_unfold_unique_thm,
       xtor_co_rec_unique = dtor_corec_unique_thm,
       xtor_un_fold_o_maps = dtor_unfold_o_Jmap_thms,
       xtor_co_rec_o_maps = dtor_corec_o_Jmap_thms,
       xtor_un_fold_transfers = dtor_unfold_transfer_thms,
       xtor_co_rec_transfers = dtor_corec_transfer_thms, xtor_rel_co_induct = Jrel_coinduct_thm,
       dtor_set_inducts = dtor_Jset_induct_thms};
  in
    timer; (fp_res, lthy')
  end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>codatatype\<close> "define coinductive datatypes"
    (parse_co_datatype_cmd Greatest_FP construct_gfp);

end;
