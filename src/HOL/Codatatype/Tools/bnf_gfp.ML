(*  Title:      HOL/Codatatype/Tools/bnf_gfp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Codatatype construction.
*)

signature BNF_GFP =
sig
  val bnf_gfp: binding list -> typ list list -> BNF_Def.BNF list -> Proof.context -> Proof.context
end;

structure BNF_GFP : BNF_GFP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_FP_Util
open BNF_GFP_Util
open BNF_GFP_Tactics

datatype wit_tree = Leaf of int | Node of (int * int * int list) * wit_tree list;

fun mk_tree_args (I, T) (I', Ts) = (sort_distinct int_ord (I @ I'), T :: Ts);

fun finish Iss m seen i (nwit, I) =
  let
    val treess = map (fn j =>
        if j < m orelse member (op =) seen j then [([j], Leaf j)]
        else
          map_index (finish Iss m (insert (op =) j seen) j) (nth Iss (j - m))
          |> flat
          |> minimize_wits)
      I;
  in
    map (fn (I, t) => (I, Node ((i - m, nwit, filter (fn i => i < m) I), t)))
      (fold_rev (map_product mk_tree_args) treess [([], [])])
    |> minimize_wits
  end;

fun tree_to_fld_wit vars _ _ (Leaf j) = ([j], nth vars j)
  | tree_to_fld_wit vars flds witss (Node ((i, nwit, I), subtrees)) =
     (I, nth flds i $ (Term.list_comb (snd (nth (nth witss i) nwit),
       map (snd o tree_to_fld_wit vars flds witss) subtrees)));

fun tree_to_coind_wits _ (Leaf j) = []
  | tree_to_coind_wits lwitss (Node ((i, nwit, I), subtrees)) =
     ((i, I), nth (nth lwitss i) nwit) :: maps (tree_to_coind_wits lwitss) subtrees;

(*all bnfs have the same lives*)
fun bnf_gfp bs Dss_insts bnfs lthy =
  let
    val timer = time (Timer.startRealTimer ());

    val live = live_of_bnf (hd bnfs);
    val n = length bnfs; (*active*)
    val ks = 1 upto n;
    val m = live - n (*passive, if 0 don't generate a new bnf*);
    val ls = 1 upto m;
    val b = Binding.name (fold_rev (fn b => fn s => Binding.name_of b ^ s) bs "");

    fun note thmN thms = snd o Local_Theory.note
      ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms);
    fun notes thmN thmss = fold2 (fn b => fn thms => snd o Local_Theory.note
      ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms)) bs thmss;

    (* TODO: check if m, n etc are sane *)

    val Dss = map (fn Ds => map TFree (fold Term.add_tfreesT Ds [])) Dss_insts;
    val deads = distinct (op =) (flat Dss);
    val names_lthy = fold Variable.declare_typ deads lthy;

    (* tvars *)
    val ((((((((passiveAs, activeAs), allAs)), (passiveBs, activeBs)),
      (passiveCs, activeCs)), passiveXs), passiveYs), idxT) = names_lthy
      |> mk_TFrees live
      |> apfst (`(chop m))
      ||> mk_TFrees live
      ||>> apfst (chop m)
      ||> mk_TFrees live
      ||>> apfst (chop m)
      ||>> mk_TFrees m
      ||>> mk_TFrees m
      ||> fst o mk_TFrees 1
      ||> the_single;

    val Ass = replicate n allAs;
    val allBs = passiveAs @ activeBs;
    val Bss = replicate n allBs;
    val allCs = passiveAs @ activeCs;
    val allCs' = passiveBs @ activeCs;
    val Css' = replicate n allCs';

    (* typs *)
    fun mk_FTs Ts = map2 (fn Ds => mk_T_of_bnf Ds Ts) Dss bnfs;
    val (params, params') = `(map dest_TFree) (deads @ passiveAs);
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
    val all_fTs = map2 (fn T => fn U => T --> U) allAs allBs;
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
    val sumBsAs = map2 (curry mk_sumT) activeBs activeAs;
    val sumFTs = mk_FTs (passiveAs @ sumBsAs);
    val sum_sTs = map2 (fn T => fn U => T --> U) activeAs sumFTs;

    (* terms *)
    val mapsAsAs = map4 mk_map_of_bnf Dss Ass Ass bnfs;
    val mapsAsBs = map4 mk_map_of_bnf Dss Ass Bss bnfs;
    val mapsBsCs' = map4 mk_map_of_bnf Dss Bss Css' bnfs;
    val mapsAsCs' = map4 mk_map_of_bnf Dss Ass Css' bnfs;
    val map_Inls = map4 mk_map_of_bnf Dss Bss (replicate n (passiveAs @ sumBsAs)) bnfs;
    val map_Inls_rev = map4 mk_map_of_bnf Dss (replicate n (passiveAs @ sumBsAs)) Bss bnfs;
    val map_fsts = map4 mk_map_of_bnf Dss (replicate n (passiveAs @ RTs)) Ass bnfs;
    val map_snds = map4 mk_map_of_bnf Dss (replicate n (passiveAs @ RTs)) Bss bnfs;
    fun mk_setss Ts = map3 mk_sets_of_bnf (map (replicate live) Dss)
      (map (replicate live) (replicate n Ts)) bnfs;
    val setssAs = mk_setss allAs;
    val setssAs' = transpose setssAs;
    val bis_setss = mk_setss (passiveAs @ RTs);
    val relsAsBs = map4 mk_rel_of_bnf Dss Ass Bss bnfs;
    val bds = map3 mk_bd_of_bnf Dss Ass bnfs;
    val sum_bd = Library.foldr1 (uncurry mk_csum) bds;
    val sum_bdT = fst (dest_relT (fastype_of sum_bd));
    val witss = map wits_of_bnf bnfs;

    val emptys = map (fn T => HOLogic.mk_set T []) passiveAs;
    val Zeros = map (fn empty =>
     HOLogic.mk_tuple (map (fn U => absdummy U empty) activeAs)) emptys;
    val hrecTs = map fastype_of Zeros;
    val hsetTs = map (fn hrecT => Library.foldr (op -->) (sTs, HOLogic.natT --> hrecT)) hrecTs;

    val (((((((((((((((((((((((((((((((((((zs, zs'), zs_copy), zs_copy2),
      z's), As), As_copy), Bs), Bs_copy), B's), B''s), ss), sum_ss), s's), s''s), fs), fs_copy),
      self_fs), all_fs), gs), all_gs), xFs), xFs_copy), RFs), (Rtuple, Rtuple')), (hrecs, hrecs')),
      (nat, nat')), Rs), Rs_copy), R's), sRs), (idx, idx')), Idx), Ris), Kss),
      names_lthy) = lthy
      |> mk_Frees' "b" activeAs
      ||>> mk_Frees "b" activeAs
      ||>> mk_Frees "b" activeAs
      ||>> mk_Frees "b" activeBs
      ||>> mk_Frees "A" ATs
      ||>> mk_Frees "A" ATs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "B''" B''Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "sums" sum_sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "s''" s''Ts
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" self_fTs
      ||>> mk_Frees "f" all_fTs
      ||>> mk_Frees "g" gTs
      ||>> mk_Frees "g" all_gTs
      ||>> mk_Frees "x" FTsAs
      ||>> mk_Frees "x" FTsAs
      ||>> mk_Frees "x" FRTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "Rtuple") all_sbisT
      ||>> mk_Frees' "rec" hrecTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "n") HOLogic.natT
      ||>> mk_Frees "R" setRTs
      ||>> mk_Frees "R" setRTs
      ||>> mk_Frees "R'" setR'Ts
      ||>> mk_Frees "R" setsRTs
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "i") idxT
      ||>> yield_singleton (mk_Frees "I") (HOLogic.mk_setT idxT)
      ||>> mk_Frees "Ri" (map (fn T => idxT --> T) setRTs)
      ||>> mk_Freess "K" (map (fn AT => map (fn T => T --> AT) activeAs) ATs);

    val passive_UNIVs = map HOLogic.mk_UNIV passiveAs;
    val passive_diags = map mk_diag As;
    val active_UNIVs = map HOLogic.mk_UNIV activeAs;
    val sum_UNIVs = map HOLogic.mk_UNIV sumBsAs;
    val passive_ids = map HOLogic.id_const passiveAs;
    val active_ids = map HOLogic.id_const activeAs;
    val Inls = map2 Inl_const activeBs activeAs;
    val fsts = map fst_const RTs;
    val snds = map snd_const RTs;

    (* thms *)
    val bd_card_orders = map bd_card_order_of_bnf bnfs;
    val bd_card_order = hd bd_card_orders
    val bd_Card_orders = map bd_Card_order_of_bnf bnfs;
    val bd_Card_order = hd bd_Card_orders;
    val bd_Cinfinites = map bd_Cinfinite_of_bnf bnfs;
    val bd_Cinfinite = hd bd_Cinfinites;
    val bd_Cnotzeros = map bd_Cnotzero_of_bnf bnfs;
    val bd_Cnotzero = hd bd_Cnotzeros;
    val in_bds = map in_bd_of_bnf bnfs;
    val in_monos = map in_mono_of_bnf bnfs;
    val map_comps = map map_comp_of_bnf bnfs;
    val map_comp's = map map_comp'_of_bnf bnfs;
    val map_congs = map map_cong_of_bnf bnfs;
    val map_id's = map map_id'_of_bnf bnfs;
    val pred_defs = map pred_def_of_bnf bnfs;
    val rel_congs = map rel_cong_of_bnf bnfs;
    val rel_converses = map rel_converse_of_bnf bnfs;
    val rel_defs = map rel_def_of_bnf bnfs;
    val rel_Grs = map rel_Gr_of_bnf bnfs;
    val rel_Ids = map rel_Id_of_bnf bnfs;
    val rel_monos = map rel_mono_of_bnf bnfs;
    val rel_Os = map rel_O_of_bnf bnfs;
    val map_wpulls = map map_wpull_of_bnf bnfs;
    val set_bdss = map set_bd_of_bnf bnfs;
    val set_natural'ss = map set_natural'_of_bnf bnfs;

    val timer = time (timer "Extracted terms & thms");

    (* derived thms *)

    (*map g1 ... gm g(m+1) ... g(m+n) (map id ... id f(m+1) ... f(m+n) x)=
      map g1 ... gm (g(m+1) o f(m+1)) ... (g(m+n) o f(m+n)) x*)
    fun mk_map_comp_id x mapAsBs mapBsCs mapAsCs map_comp =
      let
        val lhs = Term.list_comb (mapBsCs, all_gs) $
          (Term.list_comb (mapAsBs, passive_ids @ fs) $ x);
        val rhs =
          Term.list_comb (mapAsCs, take m all_gs @ map HOLogic.mk_comp (drop m all_gs ~~ fs)) $ x;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (x :: fs @ all_gs) (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))))
          (K (mk_map_comp_id_tac map_comp))
      end;

    val map_comp_id_thms = map5 mk_map_comp_id xFs mapsAsBs mapsBsCs' mapsAsCs' map_comp's;

    (*forall a : set(m+1) x. f(m+1) a = a; ...; forall a : set(m+n) x. f(m+n) a = a ==>
      map id ... id f(m+1) ... f(m+n) x = x*)
    fun mk_map_congL x mapAsAs sets map_cong map_id' =
      let
        fun mk_prem set f z z' =
          HOLogic.mk_Trueprop
            (mk_Ball (set $ x) (Term.absfree z' (HOLogic.mk_eq (f $ z, z))));
        val prems = map4 mk_prem (drop m sets) self_fs zs zs';
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
         (Term.list_comb (mapAsAs, passive_ids @ self_fs) $ x, x))
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (x :: self_fs) (Logic.list_implies (prems, goal)))
          (K (mk_map_congL_tac m map_cong map_id'))
      end;

    val map_congL_thms = map5 mk_map_congL xFs mapsAsAs setssAs map_congs map_id's;
    val in_mono'_thms = map (fn thm =>
      (thm OF (replicate m subset_refl)) RS @{thm set_mp}) in_monos;
    val in_cong'_thms = map (fn bnf => in_cong_of_bnf bnf OF (replicate m refl)) bnfs;

    val map_arg_cong_thms =
      let
        val prems = map2 (fn x => fn y =>
          HOLogic.mk_Trueprop (HOLogic.mk_eq (x, y))) xFs xFs_copy;
        val maps = map (fn map => Term.list_comb (map, all_fs)) mapsAsBs;
        val concls = map3 (fn x => fn y => fn map =>
          HOLogic.mk_Trueprop (HOLogic.mk_eq (map $ x, map $ y))) xFs xFs_copy maps;
        val goals =
          map4 (fn prem => fn concl => fn x => fn y =>
            fold_rev Logic.all (x :: y :: all_fs) (Logic.mk_implies (prem, concl)))
          prems concls xFs xFs_copy;
      in
        map (fn goal => Skip_Proof.prove lthy [] [] goal
          (K ((hyp_subst_tac THEN' rtac refl) 1))) goals
      end;

    val timer = time (timer "Derived simple theorems");

    (* coalgebra *)

    val coalg_bind = Binding.suffix_name ("_" ^ coN ^ algN) b;
    val coalg_name = Binding.name_of coalg_bind;
    val coalg_def_bind = (Thm.def_binding coalg_bind, []);

    (*forall i = 1 ... n: (\<forall>x \<in> Bi. si \<in> Fi_in A1 .. Am B1 ... Bn)*)
    val coalg_spec =
      let
        val coalgT = Library.foldr (op -->) (ATs @ BTs @ sTs, HOLogic.boolT);

        val ins = map3 mk_in (replicate n (As @ Bs)) setssAs FTsAs;
        fun mk_coalg_conjunct B s X z z' =
          mk_Ball B (Term.absfree z' (HOLogic.mk_mem (s $ z, X)));

        val lhs = Term.list_comb (Free (coalg_name, coalgT), As @ Bs @ ss);
        val rhs = Library.foldr1 HOLogic.mk_conj (map5 mk_coalg_conjunct Bs ss ins zs zs')
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((coalg_free, (_, coalg_def_free)), (lthy, lthy_old)) =
        lthy
        |> Specification.definition (SOME (coalg_bind, NONE, NoSyn), (coalg_def_bind, coalg_spec))
        ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    val coalg = fst (Term.dest_Const (Morphism.term phi coalg_free));
    val coalg_def = Morphism.thm phi coalg_def_free;

    fun mk_coalg As Bs ss =
      let
        val args = As @ Bs @ ss;
        val Ts = map fastype_of args;
        val coalgT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (coalg, coalgT), args)
      end;

    val coalg_prem = HOLogic.mk_Trueprop (mk_coalg As Bs ss);

    val coalg_in_thms = map (fn i =>
      coalg_def RS @{thm subst[of _ _ "%x. x"]} RS mk_conjunctN n i RS bspec) ks

    val coalg_set_thmss =
      let
        val coalg_prem = HOLogic.mk_Trueprop (mk_coalg As Bs ss);
        fun mk_prem x B = HOLogic.mk_Trueprop (HOLogic.mk_mem (x, B));
        fun mk_concl s x B set = HOLogic.mk_Trueprop (mk_subset (set $ (s $ x)) B);
        val prems = map2 mk_prem zs Bs;
        val conclss = map3 (fn s => fn x => fn sets => map2 (mk_concl s x) (As @ Bs) sets)
          ss zs setssAs;
        val goalss = map3 (fn x => fn prem => fn concls => map (fn concl =>
          fold_rev Logic.all (x :: As @ Bs @ ss)
            (Logic.list_implies (coalg_prem :: [prem], concl))) concls) zs prems conclss;
      in
        map (fn goals => map (fn goal => Skip_Proof.prove lthy [] [] goal
          (K (mk_coalg_set_tac coalg_def))) goals) goalss
      end;

    val coalg_set_thmss' = transpose coalg_set_thmss;

    fun mk_tcoalg ATs BTs = mk_coalg (map HOLogic.mk_UNIV ATs) (map HOLogic.mk_UNIV BTs);

    val tcoalg_thm =
      let
        val goal = fold_rev Logic.all ss
          (HOLogic.mk_Trueprop (mk_tcoalg passiveAs activeAs ss))
      in
        Skip_Proof.prove lthy [] [] goal
          (K (stac coalg_def 1 THEN CONJ_WRAP
            (K (EVERY' [rtac ballI, rtac CollectI,
              CONJ_WRAP' (K (EVERY' [rtac @{thm subset_UNIV}])) allAs] 1)) ss))
      end;

    val timer = time (timer "Coalgebra definition & thms");

    (* morphism *)

    val mor_bind = Binding.suffix_name ("_" ^ morN) b;
    val mor_name = Binding.name_of mor_bind;
    val mor_def_bind = (Thm.def_binding mor_bind, []);

    (*fbetw) forall i = 1 ... n: (\<forall>x \<in> Bi. fi x \<in> B'i)*)
    (*mor) forall i = 1 ... n: (\<forall>x \<in> Bi.
       Fi_map id ... id f1 ... fn (si x) = si' (fi x)*)
    val mor_spec =
      let
        val morT = Library.foldr (op -->) (BTs @ sTs @ B'Ts @ s'Ts @ fTs, HOLogic.boolT);

        fun mk_fbetw f B1 B2 z z' =
          mk_Ball B1 (Term.absfree z' (HOLogic.mk_mem (f $ z, B2)));
        fun mk_mor B mapAsBs f s s' z z' =
          mk_Ball B (Term.absfree z' (HOLogic.mk_eq
            (Term.list_comb (mapAsBs, passive_ids @ fs @ [s $ z]), s' $ (f $ z))));
        val lhs = Term.list_comb (Free (mor_name, morT), Bs @ ss @ B's @ s's @ fs);
        val rhs = HOLogic.mk_conj
          (Library.foldr1 HOLogic.mk_conj (map5 mk_fbetw fs Bs B's zs zs'),
           Library.foldr1 HOLogic.mk_conj (map7 mk_mor Bs mapsAsBs fs ss s's zs zs'))
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((mor_free, (_, mor_def_free)), (lthy, lthy_old)) =
        lthy
        |> Specification.definition (SOME (mor_bind, NONE, NoSyn), (mor_def_bind, mor_spec))
        ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    val mor = fst (Term.dest_Const (Morphism.term phi mor_free));
    val mor_def = Morphism.thm phi mor_def_free;

    fun mk_mor Bs1 ss1 Bs2 ss2 fs =
      let
        val args = Bs1 @ ss1 @ Bs2 @ ss2 @ fs;
        val Ts = map fastype_of (Bs1 @ ss1 @ Bs2 @ ss2 @ fs);
        val morT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (mor, morT), args)
      end;

    val mor_prem = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs);

    val (mor_image_thms, morE_thms) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs);
        fun mk_image_goal f B1 B2 = fold_rev Logic.all (Bs @ ss @ B's @ s's @ fs)
          (Logic.mk_implies (prem, HOLogic.mk_Trueprop (mk_subset (mk_image f $ B1) B2)));
        val image_goals = map3 mk_image_goal fs Bs B's;
        fun mk_elim_goal B mapAsBs f s s' x =
          fold_rev Logic.all (x :: Bs @ ss @ B's @ s's @ fs)
            (Logic.list_implies ([prem, HOLogic.mk_Trueprop (HOLogic.mk_mem (x, B))],
              HOLogic.mk_Trueprop (HOLogic.mk_eq
               (Term.list_comb (mapAsBs, passive_ids @ fs @ [s $ x]), s' $ (f $ x)))));
        val elim_goals = map6 mk_elim_goal Bs mapsAsBs fs ss s's zs;
        fun prove goal =
          Skip_Proof.prove lthy [] [] goal (K (mk_mor_elim_tac mor_def));
      in
        (map prove image_goals, map prove elim_goals)
      end;

    val mor_image'_thms = map (fn thm => @{thm set_mp} OF [thm, imageI]) mor_image_thms;

    val mor_incl_thm =
      let
        val prems = map2 (HOLogic.mk_Trueprop oo mk_subset) Bs Bs_copy;
        val concl = HOLogic.mk_Trueprop (mk_mor Bs ss Bs_copy ss active_ids);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ Bs_copy) (Logic.list_implies (prems, concl)))
          (K (mk_mor_incl_tac mor_def map_id's))
      end;

    val mor_id_thm = mor_incl_thm OF (replicate n subset_refl);

    val mor_comp_thm =
      let
        val prems =
          [HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs),
           HOLogic.mk_Trueprop (mk_mor B's s's B''s s''s gs)];
        val concl =
          HOLogic.mk_Trueprop (mk_mor Bs ss B''s s''s (map2 (curry HOLogic.mk_comp) gs fs));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ s's @ B''s @ s''s @ fs @ gs)
            (Logic.list_implies (prems, concl)))
          (K (mk_mor_comp_tac mor_def mor_image'_thms morE_thms map_comp_id_thms))
      end;

    val mor_cong_thm =
      let
        val prems = map HOLogic.mk_Trueprop
         (map2 (curry HOLogic.mk_eq) fs_copy fs @ [mk_mor Bs ss B's s's fs])
        val concl = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs_copy);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ s's @ fs @ fs_copy)
            (Logic.list_implies (prems, concl)))
          (K ((hyp_subst_tac THEN' atac) 1))
      end;

    val mor_UNIV_thm =
      let
        fun mk_conjunct mapAsBs f s s' = HOLogic.mk_eq
            (HOLogic.mk_comp (Term.list_comb (mapAsBs, passive_ids @ fs), s),
            HOLogic.mk_comp (s', f));
        val lhs = mk_mor active_UNIVs ss (map HOLogic.mk_UNIV activeBs) s's fs;
        val rhs = Library.foldr1 HOLogic.mk_conj (map4 mk_conjunct mapsAsBs fs ss s's);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (ss @ s's @ fs) (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))))
          (K (mk_mor_UNIV_tac morE_thms mor_def))
      end;

    val mor_str_thm =
      let
        val maps = map2 (fn Ds => fn bnf => Term.list_comb
          (mk_map_of_bnf Ds allAs (passiveAs @ FTsAs) bnf, passive_ids @ ss)) Dss bnfs;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all ss (HOLogic.mk_Trueprop
            (mk_mor active_UNIVs ss (map HOLogic.mk_UNIV FTsAs) maps ss)))
          (K (mk_mor_str_tac ks mor_UNIV_thm))
      end;

    val mor_sum_case_thm =
      let
        val maps = map3 (fn s => fn sum_s => fn map =>
          mk_sum_case (HOLogic.mk_comp (Term.list_comb (map, passive_ids @ Inls), s)) sum_s)
          s's sum_ss map_Inls;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (s's @ sum_ss) (HOLogic.mk_Trueprop
            (mk_mor (map HOLogic.mk_UNIV activeBs) s's sum_UNIVs maps Inls)))
          (K (mk_mor_sum_case_tac ks mor_UNIV_thm))
      end;

    val timer = time (timer "Morphism definition & thms");

    fun hset_rec_bind j = Binding.suffix_name ("_" ^ hset_recN ^ (if m = 1 then "" else
      string_of_int j)) b;
    val hset_rec_name = Binding.name_of o hset_rec_bind;
    val hset_rec_def_bind = rpair [] o Thm.def_binding o hset_rec_bind;

    fun hset_rec_spec j Zero hsetT hrec hrec' =
      let
        fun mk_Suc s setsAs z z' =
          let
            val (set, sets) = apfst (fn xs => nth xs (j - 1)) (chop m setsAs);
            fun mk_UN set k = mk_UNION (set $ (s $ z)) (mk_nthN n hrec k);
          in
            Term.absfree z'
              (mk_union (set $ (s $ z), Library.foldl1 mk_union (map2 mk_UN sets ks)))
          end;

        val Suc = Term.absdummy HOLogic.natT (Term.absfree hrec'
          (HOLogic.mk_tuple (map4 mk_Suc ss setssAs zs zs')));

        val lhs = Term.list_comb (Free (hset_rec_name j, hsetT), ss);
        val rhs = mk_nat_rec Zero Suc;
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((hset_rec_frees, (_, hset_rec_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map5 (fn j => fn Zero => fn hsetT => fn hrec => fn hrec' => Specification.definition
        (SOME (hset_rec_bind j, NONE, NoSyn),
          (hset_rec_def_bind j, hset_rec_spec j Zero hsetT hrec hrec')))
        ls Zeros hsetTs hrecs hrecs'
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val hset_rec_defs = map (Morphism.thm phi) hset_rec_def_frees;
    val hset_recs = map (fst o Term.dest_Const o Morphism.term phi) hset_rec_frees;

    fun mk_hset_rec ss nat i j T =
      let
        val args = ss @ [nat];
        val Ts = map fastype_of ss;
        val bTs = map domain_type Ts;
        val hrecT = HOLogic.mk_tupleT (map (fn U => U --> HOLogic.mk_setT T) bTs)
        val hset_recT = Library.foldr (op -->) (Ts, HOLogic.natT --> hrecT);
      in
        mk_nthN n (Term.list_comb (Const (nth hset_recs (j - 1), hset_recT), args)) i
      end;

    val hset_rec_0ss = mk_rec_simps n @{thm nat_rec_0} hset_rec_defs;
    val hset_rec_Sucss = mk_rec_simps n @{thm nat_rec_Suc} hset_rec_defs;
    val hset_rec_0ss' = transpose hset_rec_0ss;
    val hset_rec_Sucss' = transpose hset_rec_Sucss;

    fun hset_bind i j = Binding.suffix_name ("_" ^ hsetN ^
      (if m = 1 then "" else string_of_int j)) (nth bs (i - 1));
    val hset_name = Binding.name_of oo hset_bind;
    val hset_def_bind = rpair [] o Thm.def_binding oo hset_bind;

    fun hset_spec i j =
      let
        val U = nth activeAs (i - 1);
        val z = nth zs (i - 1);
        val T = nth passiveAs (j - 1);
        val setT = HOLogic.mk_setT T;
        val hsetT = Library.foldr (op -->) (sTs, U --> setT);

        val lhs = Term.list_comb (Free (hset_name i j, hsetT), ss @ [z]);
        val rhs = mk_UNION (HOLogic.mk_UNIV HOLogic.natT)
          (Term.absfree nat' (mk_hset_rec ss nat i j T $ z));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((hset_frees, (_, hset_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map (fn i => fold_map (fn j => Specification.definition
        (SOME (hset_bind i j, NONE, NoSyn), (hset_def_bind i j, hset_spec i j))) ls) ks
      |>> map (apsnd split_list o split_list)
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val hset_defss = map (map (Morphism.thm phi)) hset_def_frees;
    val hset_defss' = transpose hset_defss;
    val hset_namess = map (map (fst o Term.dest_Const o Morphism.term phi)) hset_frees;

    fun mk_hset ss i j T =
      let
        val Ts = map fastype_of ss;
        val bTs = map domain_type Ts;
        val hsetT = Library.foldr (op -->) (Ts, nth bTs (i - 1) --> HOLogic.mk_setT T);
      in
        Term.list_comb (Const (nth (nth hset_namess (i - 1)) (j - 1), hsetT), ss)
      end;

    val hsetssAs = map (fn i => map2 (mk_hset ss i) ls passiveAs) ks;

    val (set_incl_hset_thmss, set_hset_incl_hset_thmsss) =
      let
        fun mk_set_incl_hset s x set hset = fold_rev Logic.all (x :: ss)
          (HOLogic.mk_Trueprop (mk_subset (set $ (s $ x)) (hset $ x)));

        fun mk_set_hset_incl_hset s x y set hset1 hset2 =
          fold_rev Logic.all (x :: y :: ss)
            (Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (x, set $ (s $ y))),
            HOLogic.mk_Trueprop (mk_subset (hset1 $ x) (hset2 $ y))));

        val set_incl_hset_goalss =
          map4 (fn s => fn x => fn sets => fn hsets =>
            map2 (mk_set_incl_hset s x) (take m sets) hsets)
          ss zs setssAs hsetssAs;

        (*xk : F(i)set(m+k) (si yi) ==> F(k)_hset(j) s1 ... sn xk <= F(i)_hset(j) s1 ... sn yi*)
        val set_hset_incl_hset_goalsss =
          map4 (fn si => fn yi => fn sets => fn hsetsi =>
            map3 (fn xk => fn set => fn hsetsk =>
              map2 (mk_set_hset_incl_hset si xk yi set) hsetsk hsetsi)
            zs_copy (drop m sets) hsetssAs)
          ss zs setssAs hsetssAs;
      in
        (map3 (fn goals => fn defs => fn rec_Sucs =>
          map3 (fn goal => fn def => fn rec_Suc =>
            Skip_Proof.prove lthy [] [] goal
              (K (mk_set_incl_hset_tac def rec_Suc)))
          goals defs rec_Sucs)
        set_incl_hset_goalss hset_defss hset_rec_Sucss,
        map3 (fn goalss => fn defsi => fn rec_Sucs =>
          map3 (fn k => fn goals => fn defsk =>
            map4 (fn goal => fn defk => fn defi => fn rec_Suc =>
              Skip_Proof.prove lthy [] [] goal
                (K (mk_set_hset_incl_hset_tac n [defk, defi] rec_Suc k)))
            goals defsk defsi rec_Sucs)
          ks goalss hset_defss)
        set_hset_incl_hset_goalsss hset_defss hset_rec_Sucss)
      end;

    val set_incl_hset_thmss' = transpose set_incl_hset_thmss;
    val set_hset_incl_hset_thmsss' = transpose (map transpose set_hset_incl_hset_thmsss);
    val set_hset_incl_hset_thmsss'' = map transpose set_hset_incl_hset_thmsss';
    val set_hset_thmss = map (map (fn thm => thm RS @{thm set_mp})) set_incl_hset_thmss;
    val set_hset_hset_thmsss = map (map (map (fn thm => thm RS @{thm set_mp})))
      set_hset_incl_hset_thmsss;
    val set_hset_thmss' = transpose set_hset_thmss;
    val set_hset_hset_thmsss' = transpose (map transpose set_hset_hset_thmsss);

    val set_incl_hin_thmss =
      let
        fun mk_set_incl_hin s x hsets1 set hsets2 T =
          fold_rev Logic.all (x :: ss @ As)
            (Logic.list_implies
              (map2 (fn hset => fn A => HOLogic.mk_Trueprop (mk_subset (hset $ x) A)) hsets1 As,
              HOLogic.mk_Trueprop (mk_subset (set $ (s $ x)) (mk_in As hsets2 T))));

        val set_incl_hin_goalss =
          map4 (fn s => fn x => fn sets => fn hsets =>
            map3 (mk_set_incl_hin s x hsets) (drop m sets) hsetssAs activeAs)
          ss zs setssAs hsetssAs;
      in
        map2 (map2 (fn goal => fn thms =>
          Skip_Proof.prove lthy [] [] goal (K (mk_set_incl_hin_tac thms))))
        set_incl_hin_goalss set_hset_incl_hset_thmsss
      end;

    val hset_minimal_thms =
      let
        fun mk_passive_prem set s x K =
          Logic.all x (HOLogic.mk_Trueprop (mk_subset (set $ (s $ x)) (K $ x)));

        fun mk_active_prem s x1 K1 set x2 K2 =
          fold_rev Logic.all [x1, x2]
            (Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (x2, set $ (s $ x1))),
              HOLogic.mk_Trueprop (mk_subset (K2 $ x2) (K1 $ x1))));

        val premss = map2 (fn j => fn Ks =>
          map4 mk_passive_prem (map (fn xs => nth xs (j - 1)) setssAs) ss zs Ks @
            flat (map4 (fn sets => fn s => fn x1 => fn K1 =>
              map3 (mk_active_prem s x1 K1) (drop m sets) zs_copy Ks) setssAs ss zs Ks))
          ls Kss;

        val hset_rec_minimal_thms =
          let
            fun mk_conjunct j T i K x = mk_subset (mk_hset_rec ss nat i j T $ x) (K $ x);
            fun mk_concl j T Ks = list_all_free zs
              (Library.foldr1 HOLogic.mk_conj (map3 (mk_conjunct j T) ks Ks zs));
            val concls = map3 mk_concl ls passiveAs Kss;

            val goals = map2 (fn prems => fn concl =>
              Logic.list_implies (prems, HOLogic.mk_Trueprop concl)) premss concls

            val ctss =
              map (fn phi => map (SOME o certify lthy) [Term.absfree nat' phi, nat]) concls;
          in
            map4 (fn goal => fn cts => fn hset_rec_0s => fn hset_rec_Sucs =>
              singleton (Proof_Context.export names_lthy lthy)
                (Skip_Proof.prove lthy [] [] goal
                  (mk_hset_rec_minimal_tac m cts hset_rec_0s hset_rec_Sucs)))
            goals ctss hset_rec_0ss' hset_rec_Sucss'
          end;

        fun mk_conjunct j T i K x = mk_subset (mk_hset ss i j T $ x) (K $ x);
        fun mk_concl j T Ks = Library.foldr1 HOLogic.mk_conj (map3 (mk_conjunct j T) ks Ks zs);
        val concls = map3 mk_concl ls passiveAs Kss;

        val goals = map3 (fn Ks => fn prems => fn concl =>
          fold_rev Logic.all (Ks @ ss @ zs)
            (Logic.list_implies (prems, HOLogic.mk_Trueprop concl))) Kss premss concls;
      in
        map3 (fn goal => fn hset_defs => fn hset_rec_minimal =>
          Skip_Proof.prove lthy [] [] goal
            (mk_hset_minimal_tac n hset_defs hset_rec_minimal))
        goals hset_defss' hset_rec_minimal_thms
      end;

    val mor_hset_thmss =
      let
        val mor_hset_rec_thms =
          let
            fun mk_conjunct j T i f x B =
              HOLogic.mk_imp (HOLogic.mk_mem (x, B), HOLogic.mk_eq
               (mk_hset_rec s's nat i j T $ (f $ x), mk_hset_rec ss nat i j T $ x));

            fun mk_concl j T = list_all_free zs
              (Library.foldr1 HOLogic.mk_conj (map4 (mk_conjunct j T) ks fs zs Bs));
            val concls = map2 mk_concl ls passiveAs;

            val ctss =
              map (fn phi => map (SOME o certify lthy) [Term.absfree nat' phi, nat]) concls;

            val goals = map (fn concl =>
              Logic.list_implies ([coalg_prem, mor_prem], HOLogic.mk_Trueprop concl)) concls;
          in
            map5 (fn j => fn goal => fn cts => fn hset_rec_0s => fn hset_rec_Sucs =>
              singleton (Proof_Context.export names_lthy lthy)
                (Skip_Proof.prove lthy [] [] goal
                  (K (mk_mor_hset_rec_tac m n cts j hset_rec_0s hset_rec_Sucs
                    morE_thms set_natural'ss coalg_set_thmss))))
            ls goals ctss hset_rec_0ss' hset_rec_Sucss'
          end;

        val mor_hset_rec_thmss = map (fn thm => map (fn i =>
          mk_specN n thm RS mk_conjunctN n i RS mp) ks) mor_hset_rec_thms;

        fun mk_prem x B = HOLogic.mk_Trueprop (HOLogic.mk_mem (x, B));

        fun mk_concl j T i f x = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (mk_hset s's i j T $ (f $ x), mk_hset ss i j T $ x));

        val goalss = map2 (fn j => fn T => map4 (fn i => fn f => fn x => fn B =>
          fold_rev Logic.all (x :: As @ Bs @ ss @ B's @ s's @ fs)
            (Logic.list_implies ([coalg_prem, mor_prem,
              mk_prem x B], mk_concl j T i f x))) ks fs zs Bs) ls passiveAs;
      in
        map3 (map3 (fn goal => fn hset_def => fn mor_hset_rec =>
          Skip_Proof.prove lthy [] [] goal
            (K (mk_mor_hset_tac hset_def mor_hset_rec))))
        goalss hset_defss' mor_hset_rec_thmss
      end;

    val timer = time (timer "Hereditary sets");

    (* bisimulation *)

    val bis_bind = Binding.suffix_name ("_" ^ bisN) b;
    val bis_name = Binding.name_of bis_bind;
    val bis_def_bind = (Thm.def_binding bis_bind, []);

    fun mk_bis_le_conjunct R B1 B2 = mk_subset R (mk_Times (B1, B2));
    val bis_le = Library.foldr1 HOLogic.mk_conj (map3 mk_bis_le_conjunct Rs Bs B's)

    val bis_spec =
      let
        val bisT = Library.foldr (op -->) (ATs @ BTs @ sTs @ B'Ts @ s'Ts @ setRTs, HOLogic.boolT);

        val fst_args = passive_ids @ fsts;
        val snd_args = passive_ids @ snds;
        fun mk_bis R s s' b1 b2 RF map1 map2 sets =
          list_all_free [b1, b2] (HOLogic.mk_imp
            (HOLogic.mk_mem (HOLogic.mk_prod (b1, b2), R),
            mk_Bex (mk_in (As @ Rs) sets (snd (dest_Free RF))) (Term.absfree (dest_Free RF)
              (HOLogic.mk_conj
                (HOLogic.mk_eq (Term.list_comb (map1, fst_args) $ RF, s $ b1),
                HOLogic.mk_eq (Term.list_comb (map2, snd_args) $ RF, s' $ b2))))));

        val lhs = Term.list_comb (Free (bis_name, bisT), As @ Bs @ ss @ B's @ s's @ Rs);
        val rhs = HOLogic.mk_conj
          (bis_le, Library.foldr1 HOLogic.mk_conj
            (map9 mk_bis Rs ss s's zs z's RFs map_fsts map_snds bis_setss))
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((bis_free, (_, bis_def_free)), (lthy, lthy_old)) =
        lthy
        |> Specification.definition (SOME (bis_bind, NONE, NoSyn), (bis_def_bind, bis_spec))
        ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    val bis = fst (Term.dest_Const (Morphism.term phi bis_free));
    val bis_def = Morphism.thm phi bis_def_free;

    fun mk_bis As Bs1 ss1 Bs2 ss2 Rs =
      let
        val args = As @ Bs1 @ ss1 @ Bs2 @ ss2 @ Rs;
        val Ts = map fastype_of args;
        val bisT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (bis, bisT), args)
      end;

    val bis_cong_thm =
      let
        val prems = map HOLogic.mk_Trueprop
         (mk_bis As Bs ss B's s's Rs :: map2 (curry HOLogic.mk_eq) Rs_copy Rs)
        val concl = HOLogic.mk_Trueprop (mk_bis As Bs ss B's s's Rs_copy);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (As @ Bs @ ss @ B's @ s's @ Rs @ Rs_copy)
            (Logic.list_implies (prems, concl)))
          (K ((hyp_subst_tac THEN' atac) 1))
      end;

    val bis_rel_thm =
      let
        fun mk_conjunct R s s' b1 b2 rel =
          list_all_free [b1, b2] (HOLogic.mk_imp
            (HOLogic.mk_mem (HOLogic.mk_prod (b1, b2), R),
            HOLogic.mk_mem (HOLogic.mk_prod (s $ b1, s' $ b2),
              Term.list_comb (rel, passive_diags @ Rs))));

        val rhs = HOLogic.mk_conj
          (bis_le, Library.foldr1 HOLogic.mk_conj
            (map6 mk_conjunct Rs ss s's zs z's relsAsBs))
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (As @ Bs @ ss @ B's @ s's @ Rs)
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_bis As Bs ss B's s's Rs, rhs))))
          (K (mk_bis_rel_tac m bis_def rel_defs map_comp's map_congs set_natural'ss))
      end;

    val bis_converse_thm =
      Skip_Proof.prove lthy [] []
        (fold_rev Logic.all (As @ Bs @ ss @ B's @ s's @ Rs)
          (Logic.mk_implies
            (HOLogic.mk_Trueprop (mk_bis As Bs ss B's s's Rs),
            HOLogic.mk_Trueprop (mk_bis As B's s's Bs ss (map mk_converse Rs)))))
      (K (mk_bis_converse_tac m bis_rel_thm rel_congs rel_converses));

    val bis_O_thm =
      let
        val prems =
          [HOLogic.mk_Trueprop (mk_bis As Bs ss B's s's Rs),
           HOLogic.mk_Trueprop (mk_bis As B's s's B''s s''s R's)];
        val concl =
          HOLogic.mk_Trueprop (mk_bis As Bs ss B''s s''s (map2 (curry mk_rel_comp) Rs R's));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (As @ Bs @ ss @ B's @ s's @ B''s @ s''s @ Rs @ R's)
            (Logic.list_implies (prems, concl)))
          (K (mk_bis_O_tac m bis_rel_thm rel_congs rel_Os))
      end;

    val bis_Gr_thm =
      let
        val concl =
          HOLogic.mk_Trueprop (mk_bis As Bs ss B's s's (map2 mk_Gr Bs fs));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (As @ Bs @ ss @ B's @ s's @ fs)
            (Logic.list_implies ([coalg_prem, mor_prem], concl)))
          (mk_bis_Gr_tac bis_rel_thm rel_Grs mor_image_thms morE_thms coalg_in_thms)
      end;

    val bis_image2_thm = bis_cong_thm OF
      ((bis_O_thm OF [bis_Gr_thm RS bis_converse_thm, bis_Gr_thm]) ::
      replicate n @{thm image2_Gr});

    val bis_diag_thm = bis_cong_thm OF ((mor_id_thm RSN (2, bis_Gr_thm)) ::
      replicate n @{thm diag_Gr});

    val bis_Union_thm =
      let
        val prem =
          HOLogic.mk_Trueprop (mk_Ball Idx
            (Term.absfree idx' (mk_bis As Bs ss B's s's (map (fn R => R $ idx) Ris))));
        val concl =
          HOLogic.mk_Trueprop (mk_bis As Bs ss B's s's (map (mk_UNION Idx) Ris));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Idx :: As @ Bs @ ss @ B's @ s's @ Ris)
            (Logic.mk_implies (prem, concl)))
          (mk_bis_Union_tac bis_def in_mono'_thms)
      end;

    (* self-bisimulation *)

    fun mk_sbis As Bs ss Rs = mk_bis As Bs ss Bs ss Rs;

    val sbis_prem = HOLogic.mk_Trueprop (mk_sbis As Bs ss sRs);

    (* largest self-bisimulation *)

    fun lsbis_bind i = Binding.suffix_name ("_" ^ lsbisN ^ (if n = 1 then "" else
      string_of_int i)) b;
    val lsbis_name = Binding.name_of o lsbis_bind;
    val lsbis_def_bind = rpair [] o Thm.def_binding o lsbis_bind;

    val all_sbis = HOLogic.mk_Collect (fst Rtuple', snd Rtuple', list_exists_free sRs
      (HOLogic.mk_conj (HOLogic.mk_eq (Rtuple, HOLogic.mk_tuple sRs), mk_sbis As Bs ss sRs)));

    fun lsbis_spec i RT =
      let
        fun mk_lsbisT RT =
          Library.foldr (op -->) (map fastype_of (As @ Bs @ ss), RT);
        val lhs = Term.list_comb (Free (lsbis_name i, mk_lsbisT RT), As @ Bs @ ss);
        val rhs = mk_UNION all_sbis (Term.absfree Rtuple' (mk_nthN n Rtuple i));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((lsbis_frees, (_, lsbis_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map2 (fn i => fn RT => Specification.definition
        (SOME (lsbis_bind i, NONE, NoSyn), (lsbis_def_bind i, lsbis_spec i RT))) ks setsRTs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val lsbis_defs = map (Morphism.thm phi) lsbis_def_frees;
    val lsbiss = map (fst o Term.dest_Const o Morphism.term phi) lsbis_frees;

    fun mk_lsbis As Bs ss i =
      let
        val args = As @ Bs @ ss;
        val Ts = map fastype_of args;
        val RT = mk_relT (`I (HOLogic.dest_setT (fastype_of (nth Bs (i - 1)))));
        val lsbisT = Library.foldr (op -->) (Ts, RT);
      in
        Term.list_comb (Const (nth lsbiss (i - 1), lsbisT), args)
      end;

    val sbis_lsbis_thm =
      Skip_Proof.prove lthy [] []
        (fold_rev Logic.all (As @ Bs @ ss)
          (HOLogic.mk_Trueprop (mk_sbis As Bs ss (map (mk_lsbis As Bs ss) ks))))
        (K (mk_sbis_lsbis_tac lsbis_defs bis_Union_thm bis_cong_thm));

    val lsbis_incl_thms = map (fn i => sbis_lsbis_thm RS
      (bis_def RS @{thm subst[of _ _ "%x. x"]} RS conjunct1 RS mk_conjunctN n i)) ks;
    val lsbisE_thms = map (fn i => (mk_specN 2 (sbis_lsbis_thm RS
      (bis_def RS @{thm subst[of _ _ "%x. x"]} RS conjunct2 RS mk_conjunctN n i))) RS mp) ks;

    val incl_lsbis_thms =
      let
        fun mk_concl i R = HOLogic.mk_Trueprop (mk_subset R (mk_lsbis As Bs ss i));
        val goals = map2 (fn i => fn R => fold_rev Logic.all (As @ Bs @ ss @ sRs)
          (Logic.mk_implies (sbis_prem, mk_concl i R))) ks sRs;
      in
        map3 (fn goal => fn i => fn def => Skip_Proof.prove lthy [] [] goal
          (K (mk_incl_lsbis_tac n i def))) goals ks lsbis_defs
      end;

    val equiv_lsbis_thms =
      let
        fun mk_concl i B = HOLogic.mk_Trueprop (mk_equiv B (mk_lsbis As Bs ss i));
        val goals = map2 (fn i => fn B => fold_rev Logic.all (As @ Bs @ ss)
          (Logic.mk_implies (coalg_prem, mk_concl i B))) ks Bs;
      in
        map3 (fn goal => fn l_incl => fn incl_l =>
          Skip_Proof.prove lthy [] [] goal
            (K (mk_equiv_lsbis_tac sbis_lsbis_thm l_incl incl_l
              bis_diag_thm bis_converse_thm bis_O_thm)))
        goals lsbis_incl_thms incl_lsbis_thms
      end;

    val timer = time (timer "Bisimulations");

    (* bounds *)

    val (lthy, sbd, sbdT,
      sbd_card_order, sbd_Cinfinite, sbd_Cnotzero, sbd_Card_order, set_sbdss, in_sbds) =
      if n = 1
      then (lthy, sum_bd, sum_bdT,
        bd_card_order, bd_Cinfinite, bd_Cnotzero, bd_Card_order, set_bdss, in_bds)
      else
        let
          val sbdT_bind = Binding.suffix_name ("_" ^ sum_bdTN) b;

          val ((sbdT_name, (sbdT_glob_info, sbdT_loc_info)), lthy) =
            typedef true NONE (sbdT_bind, params, NoSyn)
              (HOLogic.mk_UNIV sum_bdT) NONE (EVERY' [rtac exI, rtac UNIV_I] 1) lthy;

          val sbdT = Type (sbdT_name, params');
          val Abs_sbdT = Const (#Abs_name sbdT_glob_info, sum_bdT --> sbdT);

          val sbd_bind = Binding.suffix_name ("_" ^ sum_bdN) b;
          val sbd_name = Binding.name_of sbd_bind;
          val sbd_def_bind = (Thm.def_binding sbd_bind, []);

          val sbd_spec = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (Free (sbd_name, mk_relT (`I sbdT)), mk_dir_image sum_bd Abs_sbdT));

          val ((sbd_free, (_, sbd_def_free)), (lthy, lthy_old)) =
            lthy
            |> Specification.definition (SOME (sbd_bind, NONE, NoSyn), (sbd_def_bind, sbd_spec))
            ||> `Local_Theory.restore;

          (*transforms defined frees into consts*)
          val phi = Proof_Context.export_morphism lthy_old lthy;

          val sbd_def = Morphism.thm phi sbd_def_free;
          val sbd = Const (fst (Term.dest_Const (Morphism.term phi sbd_free)), mk_relT (`I sbdT));

          val sbdT_set_def = the (#set_def sbdT_loc_info);
          val sbdT_Abs_inject = #Abs_inject sbdT_loc_info;
          val sbdT_Abs_cases = #Abs_cases sbdT_loc_info;

          val Abs_sbdT_inj = mk_Abs_inj_thm sbdT_set_def sbdT_Abs_inject;
          val Abs_sbdT_bij = mk_Abs_bij_thm lthy sbdT_set_def sbdT_Abs_inject sbdT_Abs_cases;

          fun mk_sum_Cinfinite [thm] = thm
            | mk_sum_Cinfinite (thm :: thms) =
              @{thm Cinfinite_csum_strong} OF [thm, mk_sum_Cinfinite thms];

          val sum_Cinfinite = mk_sum_Cinfinite bd_Cinfinites;
          val sum_Card_order = sum_Cinfinite RS conjunct2;

          fun mk_sum_card_order [thm] = thm
            | mk_sum_card_order (thm :: thms) =
              @{thm card_order_csum} OF [thm, mk_sum_card_order thms];

          val sum_card_order = mk_sum_card_order bd_card_orders;

          val sbd_ordIso = Local_Defs.fold lthy [sbd_def]
            (@{thm dir_image} OF [Abs_sbdT_inj, sum_Card_order]);
          val sbd_card_order =  Local_Defs.fold lthy [sbd_def]
            (@{thm card_order_dir_image} OF [Abs_sbdT_bij, sum_card_order]);
          val sbd_Cinfinite = @{thm Cinfinite_cong} OF [sbd_ordIso, sum_Cinfinite];
          val sbd_Cnotzero = sbd_Cinfinite RS @{thm Cinfinite_Cnotzero};
          val sbd_Card_order = sbd_Cinfinite RS conjunct2;

          fun mk_set_sbd i bd_Card_order bds =
            map (fn thm => @{thm ordLeq_ordIso_trans} OF
              [bd_Card_order RS mk_ordLeq_csum n i thm, sbd_ordIso]) bds;
          val set_sbdss = map3 mk_set_sbd ks bd_Card_orders set_bdss;

          fun mk_in_sbd i Co Cnz bd =
            Cnz RS ((@{thm ordLeq_ordIso_trans} OF
              [(Co RS mk_ordLeq_csum n i (Co RS @{thm ordLeq_refl})), sbd_ordIso]) RS
              (bd RS @{thm ordLeq_transitive[OF _
                cexp_mono2_Cnotzero[OF _ csum_Cnotzero2[OF ctwo_Cnotzero]]]}));
          val in_sbds = map4 mk_in_sbd ks bd_Card_orders bd_Cnotzeros in_bds;
       in
         (lthy, sbd, sbdT,
           sbd_card_order, sbd_Cinfinite, sbd_Cnotzero, sbd_Card_order, set_sbdss, in_sbds)
       end;

    fun mk_sbd_sbd 1 = sbd_Card_order RS @{thm ordIso_refl}
      | mk_sbd_sbd n = @{thm csum_absorb1} OF
          [sbd_Cinfinite, mk_sbd_sbd (n - 1) RS @{thm ordIso_imp_ordLeq}];

    val sbd_sbd_thm = mk_sbd_sbd n;

    val sbdTs = replicate n sbdT;
    val sum_sbd = Library.foldr1 (uncurry mk_csum) (replicate n sbd);
    val sum_sbdT = mk_sumTN sbdTs;
    val sum_sbd_listT = HOLogic.listT sum_sbdT;
    val sum_sbd_list_setT = HOLogic.mk_setT sum_sbd_listT;
    val bdTs = passiveAs @ replicate n sbdT;
    val to_sbd_maps = map4 mk_map_of_bnf Dss Ass (replicate n bdTs) bnfs;
    val bdFTs = mk_FTs bdTs;
    val sbdFT = mk_sumTN bdFTs;
    val treeT = HOLogic.mk_prodT (sum_sbd_list_setT, sum_sbd_listT --> sbdFT);
    val treeQT = HOLogic.mk_setT treeT;
    val treeTs = passiveAs @ replicate n treeT;
    val treeQTs = passiveAs @ replicate n treeQT;
    val treeFTs = mk_FTs treeTs;
    val tree_maps = map4 mk_map_of_bnf Dss (replicate n bdTs) (replicate n treeTs) bnfs;
    val final_maps = map4 mk_map_of_bnf Dss (replicate n treeTs) (replicate n treeQTs) bnfs;
    val tree_setss = mk_setss treeTs;
    val isNode_setss = mk_setss (passiveAs @ replicate n sbdT);

    val root = HOLogic.mk_set sum_sbd_listT [HOLogic.mk_list sum_sbdT []];
    val Zero = HOLogic.mk_tuple (map (fn U => absdummy U root) activeAs);
    val Lev_recT = fastype_of Zero;
    val LevT = Library.foldr (op -->) (sTs, HOLogic.natT --> Lev_recT);

    val Nil = HOLogic.mk_tuple (map3 (fn i => fn z => fn z'=>
      Term.absfree z' (mk_InN activeAs z i)) ks zs zs');
    val rv_recT = fastype_of Nil;
    val rvT = Library.foldr (op -->) (sTs, sum_sbd_listT --> rv_recT);

    val (((((((((((sumx, sumx'), (kks, kks')), (kl, kl')), (kl_copy, kl'_copy)), (Kl, Kl')),
      (lab, lab')), (Kl_lab, Kl_lab')), xs), (Lev_rec, Lev_rec')), (rv_rec, rv_rec')),
      names_lthy) = names_lthy
      |> yield_singleton (apfst (op ~~) oo mk_Frees' "sumx") sum_sbdT
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

    fun isNode_bind i = Binding.suffix_name ("_" ^ isNodeN ^ (if n = 1 then "" else
      string_of_int i)) b;
    val isNode_name = Binding.name_of o isNode_bind;
    val isNode_def_bind = rpair [] o Thm.def_binding o isNode_bind;

    val isNodeT =
      Library.foldr (op -->) (map fastype_of (As @ [Kl, lab, kl]), HOLogic.boolT);

    val Succs = map3 (fn i => fn k => fn k' =>
      HOLogic.mk_Collect (fst k', snd k', HOLogic.mk_mem (mk_InN sbdTs k i, mk_Succ Kl kl)))
      ks kks kks';

    fun isNode_spec sets x i =
      let
        val (passive_sets, active_sets) = chop m (map (fn set => set $ x) sets);
        val lhs = Term.list_comb (Free (isNode_name i, isNodeT), As @ [Kl, lab, kl]);
        val rhs = list_exists_free [x]
          (Library.foldr1 HOLogic.mk_conj (HOLogic.mk_eq (lab $ kl, mk_InN bdFTs x i) ::
          map2 mk_subset passive_sets As @ map2 (curry HOLogic.mk_eq) active_sets Succs));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((isNode_frees, (_, isNode_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map3 (fn i => fn x => fn sets => Specification.definition
        (SOME (isNode_bind i, NONE, NoSyn), (isNode_def_bind i, isNode_spec sets x i)))
        ks xs isNode_setss
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val isNode_defs = map (Morphism.thm phi) isNode_def_frees;
    val isNodes = map (fst o Term.dest_Const o Morphism.term phi) isNode_frees;

    fun mk_isNode As kl i =
      Term.list_comb (Const (nth isNodes (i - 1), isNodeT), As @ [Kl, lab, kl]);

    val isTree =
      let
        val empty = HOLogic.mk_mem (HOLogic.mk_list sum_sbdT [], Kl);
        val Field = mk_subset Kl (mk_Field (mk_clists sum_sbd));
        val prefCl = mk_prefCl Kl;

        val tree = mk_Ball Kl (Term.absfree kl'
          (HOLogic.mk_conj
            (Library.foldr1 HOLogic.mk_disj (map (mk_isNode As kl) ks),
            Library.foldr1 HOLogic.mk_conj (map4 (fn Succ => fn i => fn k => fn k' =>
              mk_Ball Succ (Term.absfree k' (mk_isNode As
                (mk_append (kl, HOLogic.mk_list sum_sbdT [mk_InN sbdTs k i])) i)))
            Succs ks kks kks'))));

        val undef = list_all_free [kl] (HOLogic.mk_imp
          (HOLogic.mk_not (HOLogic.mk_mem (kl, Kl)),
          HOLogic.mk_eq (lab $ kl, mk_undefined sbdFT)));
      in
        Library.foldr1 HOLogic.mk_conj [empty, Field, prefCl, tree, undef]
      end;

    fun carT_bind i = Binding.suffix_name ("_" ^ carTN ^ (if n = 1 then "" else
      string_of_int i)) b;
    val carT_name = Binding.name_of o carT_bind;
    val carT_def_bind = rpair [] o Thm.def_binding o carT_bind;

    fun carT_spec i =
      let
        val carTT = Library.foldr (op -->) (ATs, HOLogic.mk_setT treeT);

        val lhs = Term.list_comb (Free (carT_name i, carTT), As);
        val rhs = HOLogic.mk_Collect (fst Kl_lab', snd Kl_lab', list_exists_free [Kl, lab]
          (HOLogic.mk_conj (HOLogic.mk_eq (Kl_lab, HOLogic.mk_prod (Kl, lab)),
            HOLogic.mk_conj (isTree, mk_isNode As (HOLogic.mk_list sum_sbdT []) i))));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((carT_frees, (_, carT_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map (fn i => Specification.definition
        (SOME (carT_bind i, NONE, NoSyn), (carT_def_bind i, carT_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val carT_defs = map (Morphism.thm phi) carT_def_frees;
    val carTs = map (fst o Term.dest_Const o Morphism.term phi) carT_frees;

    fun mk_carT As i = Term.list_comb
      (Const (nth carTs (i - 1),
         Library.foldr (op -->) (map fastype_of As, HOLogic.mk_setT treeT)), As);

    fun strT_bind i = Binding.suffix_name ("_" ^ strTN ^ (if n = 1 then "" else
      string_of_int i)) b;
    val strT_name = Binding.name_of o strT_bind;
    val strT_def_bind = rpair [] o Thm.def_binding o strT_bind;

    fun strT_spec mapFT FT i =
      let
        val strTT = treeT --> FT;

        fun mk_f i k k' =
          let val in_k = mk_InN sbdTs k i;
          in Term.absfree k' (HOLogic.mk_prod (mk_Shift Kl in_k, mk_shift lab in_k)) end;

        val f = Term.list_comb (mapFT, passive_ids @ map3 mk_f ks kks kks');
        val (fTs1, fTs2) = apsnd tl (chop (i - 1) (map (fn T => T --> FT) bdFTs));
        val fs = map mk_undefined fTs1 @ (f :: map mk_undefined fTs2);
        val lhs = Free (strT_name i, strTT);
        val rhs = HOLogic.mk_split (Term.absfree Kl' (Term.absfree lab'
          (mk_sum_caseN fs $ (lab $ HOLogic.mk_list sum_sbdT []))));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((strT_frees, (_, strT_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map3 (fn i => fn mapFT => fn FT => Specification.definition
        (SOME (strT_bind i, NONE, NoSyn), (strT_def_bind i, strT_spec mapFT FT i)))
        ks tree_maps treeFTs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val strT_defs = map ((fn def => trans OF [def RS fun_cong, @{thm prod.cases}]) o
      Morphism.thm phi) strT_def_frees;
    val strTs = map (fst o Term.dest_Const o Morphism.term phi) strT_frees;

    fun mk_strT FT i = Const (nth strTs (i - 1), treeT --> FT);

    val carTAs = map (mk_carT As) ks;
    val carTAs_copy = map (mk_carT As_copy) ks;
    val strTAs = map2 mk_strT treeFTs ks;
    val hset_strTss = map (fn i => map2 (mk_hset strTAs i) ls passiveAs) ks;

    val coalgT_thm =
      Skip_Proof.prove lthy [] []
        (fold_rev Logic.all As (HOLogic.mk_Trueprop (mk_coalg As carTAs strTAs)))
        (mk_coalgT_tac m (coalg_def :: isNode_defs @ carT_defs) strT_defs set_natural'ss);

    val card_of_carT_thms =
      let
        val lhs = mk_card_of
          (HOLogic.mk_Collect (fst Kl_lab', snd Kl_lab', list_exists_free [Kl, lab]
            (HOLogic.mk_conj (HOLogic.mk_eq (Kl_lab, HOLogic.mk_prod (Kl, lab)), isTree))));
        val rhs = mk_cexp
          (if m = 0 then ctwo else
            (mk_csum (Library.foldr1 (uncurry mk_csum) (map mk_card_of As)) ctwo))
            (mk_cexp sbd sbd);
        val card_of_carT =
          Skip_Proof.prove lthy [] []
            (fold_rev Logic.all As (HOLogic.mk_Trueprop (mk_ordLeq lhs rhs)))
            (K (mk_card_of_carT_tac m isNode_defs sbd_sbd_thm
              sbd_card_order sbd_Card_order sbd_Cinfinite sbd_Cnotzero in_sbds))
      in
        map (fn def => @{thm ordLeq_transitive[OF
          card_of_mono1[OF ord_eq_le_trans[OF _ Collect_restrict']]]} OF [def, card_of_carT])
        carT_defs
      end;

    val carT_set_thmss =
      let
        val Kl_lab = HOLogic.mk_prod (Kl, lab);
        fun mk_goal carT strT set k i =
          fold_rev Logic.all (sumx :: Kl :: lab :: k :: kl :: As)
            (Logic.list_implies (map HOLogic.mk_Trueprop
              [HOLogic.mk_mem (Kl_lab, carT), HOLogic.mk_mem (mk_Cons sumx kl, Kl),
              HOLogic.mk_eq (sumx, mk_InN sbdTs k i)],
            HOLogic.mk_Trueprop (HOLogic.mk_mem
              (HOLogic.mk_prod (mk_Shift Kl sumx, mk_shift lab sumx),
              set $ (strT $ Kl_lab)))));

        val goalss = map3 (fn carT => fn strT => fn sets =>
          map3 (mk_goal carT strT) (drop m sets) kks ks) carTAs strTAs tree_setss;
      in
        map6 (fn i => fn goals =>
            fn carT_def => fn strT_def => fn isNode_def => fn set_naturals =>
          map2 (fn goal => fn set_natural =>
            Skip_Proof.prove lthy [] [] goal
            (mk_carT_set_tac n i carT_def strT_def isNode_def set_natural))
          goals (drop m set_naturals))
        ks goalss carT_defs strT_defs isNode_defs set_natural'ss
      end;

    val carT_set_thmss' = transpose carT_set_thmss;

    val isNode_hset_thmss =
      let
        val Kl_lab = HOLogic.mk_prod (Kl, lab);
        fun mk_Kl_lab carT = HOLogic.mk_mem (Kl_lab, carT);

        val strT_hset_thmsss =
          let
            val strT_hset_thms =
              let
                fun mk_lab_kl i x = HOLogic.mk_eq (lab $ kl, mk_InN bdFTs x i);

                fun mk_inner_conjunct j T i x set i' carT =
                  HOLogic.mk_imp (HOLogic.mk_conj (mk_Kl_lab carT, mk_lab_kl i x),
                    mk_subset (set $ x) (mk_hset strTAs i' j T $ Kl_lab));

                fun mk_conjunct j T i x set =
                  Library.foldr1 HOLogic.mk_conj (map2 (mk_inner_conjunct j T i x set) ks carTAs);

                fun mk_concl j T = list_all_free (Kl :: lab :: xs @ As)
                  (HOLogic.mk_imp (HOLogic.mk_mem (kl, Kl),
                    Library.foldr1 HOLogic.mk_conj (map3 (mk_conjunct j T)
                      ks xs (map (fn xs => nth xs (j - 1)) isNode_setss))));
                val concls = map2 mk_concl ls passiveAs;

                val cTs = [SOME (certifyT lthy sum_sbdT)];
                val arg_cong_cTs = map (SOME o certifyT lthy) treeFTs;
                val ctss =
                  map (fn phi => map (SOME o certify lthy) [Term.absfree kl' phi, kl]) concls;

                val goals = map HOLogic.mk_Trueprop concls;
              in
                map5 (fn j => fn goal => fn cts => fn set_incl_hsets => fn set_hset_incl_hsetss =>
                  singleton (Proof_Context.export names_lthy lthy)
                    (Skip_Proof.prove lthy [] [] goal
                      (K (mk_strT_hset_tac n m j arg_cong_cTs cTs cts
                        carT_defs strT_defs isNode_defs
                        set_incl_hsets set_hset_incl_hsetss coalg_set_thmss' carT_set_thmss'
                        coalgT_thm set_natural'ss))))
                ls goals ctss set_incl_hset_thmss' set_hset_incl_hset_thmsss''
              end;

            val strT_hset'_thms = map (fn thm => mk_specN (2 + n + m) thm RS mp) strT_hset_thms;
          in
            map (fn thm => map (fn i => map (fn i' =>
              thm RS mk_conjunctN n i RS mk_conjunctN n i' RS mp) ks) ks) strT_hset'_thms
          end;

        val carT_prems = map (fn carT =>
          HOLogic.mk_Trueprop (HOLogic.mk_mem (Kl_lab, carT))) carTAs_copy;
        val prem = HOLogic.mk_Trueprop (HOLogic.mk_mem (kl, Kl));
        val in_prems = map (fn hsets =>
          HOLogic.mk_Trueprop (HOLogic.mk_mem (Kl_lab, mk_in As hsets treeT))) hset_strTss;
        val isNode_premss = replicate n (map (HOLogic.mk_Trueprop o mk_isNode As_copy kl) ks);
        val conclss = replicate n (map (HOLogic.mk_Trueprop o mk_isNode As kl) ks);
      in
        map5 (fn carT_prem => fn isNode_prems => fn in_prem => fn concls => fn strT_hset_thmss =>
          map4 (fn isNode_prem => fn concl => fn isNode_def => fn strT_hset_thms =>
            Skip_Proof.prove lthy [] []
            (fold_rev Logic.all (Kl :: lab :: kl :: As @ As_copy)
              (Logic.list_implies ([carT_prem, prem, isNode_prem, in_prem], concl)))
            (mk_isNode_hset_tac n isNode_def strT_hset_thms))
          isNode_prems concls isNode_defs
          (if m = 0 then replicate n [] else transpose strT_hset_thmss))
        carT_prems isNode_premss in_prems conclss
        (if m = 0 then replicate n [] else transpose (map transpose strT_hset_thmsss))
      end;

    val timer = time (timer "Tree coalgebra");

    fun mk_to_sbd s x i i' =
      mk_toCard (nth (nth setssAs (i - 1)) (m + i' - 1) $ (s $ x)) sbd;
    fun mk_from_sbd s x i i' =
      mk_fromCard (nth (nth setssAs (i - 1)) (m + i' - 1) $ (s $ x)) sbd;

    fun mk_to_sbd_thmss thm = map (map (fn set_sbd =>
      thm OF [set_sbd, sbd_Card_order]) o drop m) set_sbdss;

    val to_sbd_inj_thmss = mk_to_sbd_thmss @{thm toCard_inj};
    val to_sbd_thmss = mk_to_sbd_thmss @{thm toCard};
    val from_to_sbd_thmss = mk_to_sbd_thmss @{thm fromCard_toCard};

    val Lev_bind = Binding.suffix_name ("_" ^ LevN) b;
    val Lev_name = Binding.name_of Lev_bind;
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
            Term.absfree a' (Library.foldl1 mk_union (map3 mk_set ks sets zs_copy))
          end;

        val Suc = Term.absdummy HOLogic.natT (Term.absfree Lev_rec'
          (HOLogic.mk_tuple (map5 mk_Suc ks ss setssAs zs zs')));

        val lhs = Term.list_comb (Free (Lev_name, LevT), ss);
        val rhs = mk_nat_rec Zero Suc;
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((Lev_free, (_, Lev_def_free)), (lthy, lthy_old)) =
      lthy
      |> Specification.definition (SOME (Lev_bind, NONE, NoSyn), (Lev_def_bind, Lev_spec))
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val Lev_def = Morphism.thm phi Lev_def_free;
    val Lev = fst (Term.dest_Const (Morphism.term phi Lev_free));

    fun mk_Lev ss nat i =
      let
        val Ts = map fastype_of ss;
        val LevT = Library.foldr (op -->) (Ts, HOLogic.natT -->
          HOLogic.mk_tupleT (map (fn U => domain_type U --> sum_sbd_list_setT) Ts));
      in
        mk_nthN n (Term.list_comb (Const (Lev, LevT), ss) $ nat) i
      end;

    val Lev_0s = flat (mk_rec_simps n @{thm nat_rec_0} [Lev_def]);
    val Lev_Sucs = flat (mk_rec_simps n @{thm nat_rec_Suc} [Lev_def]);

    val rv_bind = Binding.suffix_name ("_" ^ rvN) b;
    val rv_name = Binding.name_of rv_bind;
    val rv_def_bind = rpair [] (Thm.def_binding rv_bind);

    val rv_spec =
      let
        fun mk_Cons i s b b' =
          let
            fun mk_case i' =
              Term.absfree k' (mk_nthN n rv_rec i' $ (mk_from_sbd s b i i' $ k));
          in
            Term.absfree b' (mk_sum_caseN (map mk_case ks) $ sumx)
          end;

        val Cons = Term.absfree sumx' (Term.absdummy sum_sbd_listT (Term.absfree rv_rec'
          (HOLogic.mk_tuple (map4 mk_Cons ks ss zs zs'))));

        val lhs = Term.list_comb (Free (rv_name, rvT), ss);
        val rhs = mk_list_rec Nil Cons;
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((rv_free, (_, rv_def_free)), (lthy, lthy_old)) =
      lthy
      |> Specification.definition (SOME (rv_bind, NONE, NoSyn), (rv_def_bind, rv_spec))
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val rv_def = Morphism.thm phi rv_def_free;
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

    val rv_Nils = flat (mk_rec_simps n @{thm list_rec_Nil} [rv_def]);
    val rv_Conss = flat (mk_rec_simps n @{thm list_rec_Cons} [rv_def]);

    fun beh_bind i = Binding.suffix_name ("_" ^ behN ^ (if n = 1 then "" else
      string_of_int i)) b;
    val beh_name = Binding.name_of o beh_bind;
    val beh_def_bind = rpair [] o Thm.def_binding o beh_bind;

    fun beh_spec i z =
      let
        val mk_behT = Library.foldr (op -->) (map fastype_of (ss @ [z]), treeT);

        fun mk_case i to_sbd_map s k k' =
          Term.absfree k' (mk_InN bdFTs
            (Term.list_comb (to_sbd_map, passive_ids @ map (mk_to_sbd s k i) ks) $ (s $ k)) i);

        val Lab = Term.absfree kl' (mk_If
          (HOLogic.mk_mem (kl, mk_Lev ss (mk_size kl) i $ z))
          (mk_sum_caseN (map5 mk_case ks to_sbd_maps ss zs zs') $ (mk_rv ss kl i $ z))
          (mk_undefined sbdFT));

        val lhs = Term.list_comb (Free (beh_name i, mk_behT), ss) $ z;
        val rhs = HOLogic.mk_prod (mk_UNION (HOLogic.mk_UNIV HOLogic.natT)
          (Term.absfree nat' (mk_Lev ss nat i $ z)), Lab);
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((beh_frees, (_, beh_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map2 (fn i => fn z => Specification.definition
        (SOME (beh_bind i, NONE, NoSyn), (beh_def_bind i, beh_spec i z))) ks zs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;

    val beh_defs = map (Morphism.thm phi) beh_def_frees;
    val behs = map (fst o Term.dest_Const o Morphism.term phi) beh_frees;

    fun mk_beh ss i =
      let
        val Ts = map fastype_of ss;
        val behT = Library.foldr (op -->) (Ts, nth activeAs (i - 1) --> treeT);
      in
        Term.list_comb (Const (nth behs (i - 1), behT), ss)
      end;

    val Lev_sbd_thms =
      let
        fun mk_conjunct i z = mk_subset (mk_Lev ss nat i $ z) (mk_Field (mk_clists sum_sbd));
        val goal = list_all_free zs
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));

        val cts = map (SOME o certify lthy) [Term.absfree nat' goal, nat];

        val Lev_sbd = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
            (K (mk_Lev_sbd_tac cts Lev_0s Lev_Sucs to_sbd_thmss)));

        val Lev_sbd' = mk_specN n Lev_sbd;
      in
        map (fn i => Lev_sbd' RS mk_conjunctN n i) ks
      end;

    val (length_Lev_thms, length_Lev'_thms) =
      let
        fun mk_conjunct i z = HOLogic.mk_imp (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z),
          HOLogic.mk_eq (mk_size kl, nat));
        val goal = list_all_free (kl :: zs)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));

        val cts = map (SOME o certify lthy) [Term.absfree nat' goal, nat];

        val length_Lev = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
            (K (mk_length_Lev_tac cts Lev_0s Lev_Sucs)));

        val length_Lev' = mk_specN (n + 1) length_Lev;
        val length_Levs = map (fn i => length_Lev' RS mk_conjunctN n i RS mp) ks;

        fun mk_goal i z = fold_rev Logic.all (z :: kl :: nat :: ss) (Logic.mk_implies
            (HOLogic.mk_Trueprop (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z)),
            HOLogic.mk_Trueprop (HOLogic.mk_mem (kl, mk_Lev ss (mk_size kl) i $ z))));
        val goals = map2 mk_goal ks zs;

        val length_Levs' = map2 (fn goal => fn length_Lev =>
          Skip_Proof.prove lthy [] [] goal
            (K (mk_length_Lev'_tac length_Lev))) goals length_Levs;
      in
        (length_Levs, length_Levs')
      end;

    val prefCl_Lev_thms =
      let
        fun mk_conjunct i z = HOLogic.mk_imp
          (HOLogic.mk_conj (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z), mk_subset kl_copy kl),
          HOLogic.mk_mem (kl_copy, mk_Lev ss (mk_size kl_copy) i $ z));
        val goal = list_all_free (kl :: kl_copy :: zs)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));

        val cts = map (SOME o certify lthy) [Term.absfree nat' goal, nat];

        val prefCl_Lev = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
            (K (mk_prefCl_Lev_tac cts Lev_0s Lev_Sucs)));

        val prefCl_Lev' = mk_specN (n + 2) prefCl_Lev;
      in
        map (fn i => prefCl_Lev' RS mk_conjunctN n i RS mp) ks
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

        val cTs = [SOME (certifyT lthy sum_sbdT)];
        val cts = map (SOME o certify lthy) [Term.absfree kl' goal, kl];

        val rv_last = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
            (K (mk_rv_last_tac cTs cts rv_Nils rv_Conss)));

        val rv_last' = mk_specN (n + 1) rv_last;
      in
        map (fn i => map (fn i' => rv_last' RS mk_conjunctN n i RS mk_conjunctN n i') ks) ks
      end;

    val set_rv_Lev_thmsss = if m = 0 then replicate n (replicate n []) else
      let
        fun mk_case s sets z z_free = Term.absfree z_free (Library.foldr1 HOLogic.mk_conj
          (map2 (fn set => fn A => mk_subset (set $ (s $ z)) A) (take m sets) As));

        fun mk_conjunct i z B = HOLogic.mk_imp
          (HOLogic.mk_conj (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z), HOLogic.mk_mem (z, B)),
          mk_sum_caseN (map4 mk_case ss setssAs zs zs') $ (mk_rv ss kl i $ z));

        val goal = list_all_free (kl :: zs)
          (Library.foldr1 HOLogic.mk_conj (map3 mk_conjunct ks zs Bs));

        val cts = map (SOME o certify lthy) [Term.absfree nat' goal, nat];

        val set_rv_Lev = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] []
            (Logic.mk_implies (coalg_prem, HOLogic.mk_Trueprop goal))
            (K (mk_set_rv_Lev_tac m cts Lev_0s Lev_Sucs rv_Nils rv_Conss
              coalg_set_thmss from_to_sbd_thmss)));

        val set_rv_Lev' = mk_specN (n + 1) set_rv_Lev;
      in
        map (fn i => map (fn i' =>
          split_conj_thm (if n = 1 then set_rv_Lev' RS mk_conjunctN n i RS mp
            else set_rv_Lev' RS mk_conjunctN n i RS mp RSN
              (2, @{thm sum_case_cong} RS @{thm subst[of _ _ "%x. x"]}) RS
              (mk_sum_casesN n i' RS @{thm subst[of _ _ "%x. x"]}))) ks) ks
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
                  (Library.foldr1 HOLogic.mk_conj (map3 mk_conjunct'' ks (drop m sets) zs_copy2)))
              end;
          in
            HOLogic.mk_imp (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z),
              Library.foldr1 HOLogic.mk_conj (map4 mk_conjunct' ks setssAs ss zs_copy))
          end;

        val goal = list_all_free (kl :: zs @ zs_copy @ zs_copy2)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));

        val cts = map (SOME o certify lthy) [Term.absfree nat' goal, nat];

        val set_Lev = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
            (K (mk_set_Lev_tac cts Lev_0s Lev_Sucs rv_Nils rv_Conss from_to_sbd_thmss)));

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
                  (Library.foldr1 HOLogic.mk_conj (map4 mk_conjunct'' ks sets ss zs_copy)))
              end;
          in
            HOLogic.mk_imp (HOLogic.mk_mem (kl, mk_Lev ss nat i $ z),
              Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct' ks (drop m setssAs')))
          end;

        val goal = list_all_free (kl :: k :: zs @ zs_copy)
          (Library.foldr1 HOLogic.mk_conj (map2 mk_conjunct ks zs));

        val cts = map (SOME o certify lthy) [Term.absfree nat' goal, nat];

        val set_image_Lev = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
            (K (mk_set_image_Lev_tac cts Lev_0s Lev_Sucs rv_Nils rv_Conss
              from_to_sbd_thmss to_sbd_inj_thmss)));

        val set_image_Lev' = mk_specN (2 * n + 2) set_image_Lev;
      in
        map (fn i => map (fn i' => map (fn i'' => set_image_Lev' RS
          mk_conjunctN n i RS mp RS
          mk_conjunctN n i'' RS mp RS
          mk_conjunctN n i' RS mp) ks) ks) ks
      end;

    val mor_beh_thm =
      Skip_Proof.prove lthy [] []
        (fold_rev Logic.all (As @ Bs @ ss) (Logic.mk_implies (coalg_prem,
          HOLogic.mk_Trueprop (mk_mor Bs ss carTAs strTAs (map (mk_beh ss) ks)))))
        (mk_mor_beh_tac m mor_def mor_cong_thm
          beh_defs carT_defs strT_defs isNode_defs
          to_sbd_inj_thmss from_to_sbd_thmss Lev_0s Lev_Sucs rv_Nils rv_Conss Lev_sbd_thms
          length_Lev_thms length_Lev'_thms prefCl_Lev_thms rv_last_thmss
          set_rv_Lev_thmsss set_Lev_thmsss set_image_Lev_thmsss
          set_natural'ss coalg_set_thmss map_comp_id_thms map_congs map_arg_cong_thms);

    val timer = time (timer "Behavioral morphism");

    fun mk_LSBIS As i = mk_lsbis As (map (mk_carT As) ks) strTAs i;
    fun mk_car_final As i =
      mk_quotient (mk_carT As i) (mk_LSBIS As i);
    fun mk_str_final As i =
      mk_univ (HOLogic.mk_comp (Term.list_comb (nth final_maps (i - 1),
        passive_ids @ map (mk_proj o mk_LSBIS As) ks), nth strTAs (i - 1)));

    val car_finalAs = map (mk_car_final As) ks;
    val str_finalAs = map (mk_str_final As) ks;
    val car_finals = map (mk_car_final passive_UNIVs) ks;
    val str_finals = map (mk_str_final passive_UNIVs) ks;

    val coalgT_set_thmss = map (map (fn thm => coalgT_thm RS thm)) coalg_set_thmss;
    val equiv_LSBIS_thms = map (fn thm => coalgT_thm RS thm) equiv_lsbis_thms;

    val congruent_str_final_thms =
      let
        fun mk_goal R final_map strT =
          fold_rev Logic.all As (HOLogic.mk_Trueprop
            (mk_congruent R (HOLogic.mk_comp
              (Term.list_comb (final_map, passive_ids @ map (mk_proj o mk_LSBIS As) ks), strT))));

        val goals = map3 mk_goal (map (mk_LSBIS As) ks) final_maps strTAs;
      in
        map4 (fn goal => fn lsbisE => fn map_comp_id => fn map_cong =>
          Skip_Proof.prove lthy [] [] goal
            (K (mk_congruent_str_final_tac m lsbisE map_comp_id map_cong equiv_LSBIS_thms)))
        goals lsbisE_thms map_comp_id_thms map_congs
      end;

    val coalg_final_thm = Skip_Proof.prove lthy [] [] (fold_rev Logic.all As
      (HOLogic.mk_Trueprop (mk_coalg As car_finalAs str_finalAs)))
      (K (mk_coalg_final_tac m coalg_def congruent_str_final_thms equiv_LSBIS_thms
        set_natural'ss coalgT_set_thmss));

    val mor_T_final_thm = Skip_Proof.prove lthy [] [] (fold_rev Logic.all As
      (HOLogic.mk_Trueprop (mk_mor carTAs strTAs car_finalAs str_finalAs
        (map (mk_proj o mk_LSBIS As) ks))))
      (K (mk_mor_T_final_tac mor_def congruent_str_final_thms equiv_LSBIS_thms));

    val mor_final_thm = mor_comp_thm OF [mor_beh_thm, mor_T_final_thm];
    val in_car_final_thms = map (fn mor_image' => mor_image' OF
      [tcoalg_thm RS mor_final_thm, UNIV_I]) mor_image'_thms;

    val timer = time (timer "Final coalgebra");

    val ((T_names, (T_glob_infos, T_loc_infos)), lthy) =
      lthy
      |> fold_map3 (fn b => fn car_final => fn in_car_final =>
        typedef false NONE (b, params, NoSyn) car_final NONE
          (EVERY' [rtac exI, rtac in_car_final] 1)) bs car_finals in_car_final_thms
      |>> apsnd split_list o split_list;

    val Ts = map (fn name => Type (name, params')) T_names;
    fun mk_Ts passive = map (Term.typ_subst_atomic (passiveAs ~~ passive)) Ts;
    val Ts' = mk_Ts passiveBs;
    val Ts'' = mk_Ts passiveCs;
    val Rep_Ts = map2 (fn info => fn T => Const (#Rep_name info, T --> treeQT)) T_glob_infos Ts;
    val Abs_Ts = map2 (fn info => fn T => Const (#Abs_name info, treeQT --> T)) T_glob_infos Ts;

    val Reps = map #Rep T_loc_infos;
    val Rep_injects = map #Rep_inject T_loc_infos;
    val Rep_inverses = map #Rep_inverse T_loc_infos;
    val Abs_inverses = map #Abs_inverse T_loc_infos;

    val timer = time (timer "THE TYPEDEFs & Rep/Abs thms");

    val UNIVs = map HOLogic.mk_UNIV Ts;
    val FTs = mk_FTs (passiveAs @ Ts);
    val FTs' = mk_FTs (passiveBs @ Ts);
    val prodTs = map (HOLogic.mk_prodT o `I) Ts;
    val prodFTs = mk_FTs (passiveAs @ prodTs);
    val FTs_setss = mk_setss (passiveAs @ Ts);
    val FTs'_setss = mk_setss (passiveBs @ Ts);
    val prodFT_setss = mk_setss (passiveAs @ prodTs);
    val map_FTs = map2 (fn Ds => mk_map_of_bnf Ds treeQTs (passiveAs @ Ts)) Dss bnfs;
    val map_FT_nths = map2 (fn Ds =>
      mk_map_of_bnf Ds (passiveAs @ prodTs) (passiveAs @ Ts)) Dss bnfs;
    val fstsTs = map fst_const prodTs;
    val sndsTs = map snd_const prodTs;
    val unfTs = map2 (curry (op -->)) Ts FTs;
    val fldTs = map2 (curry (op -->)) FTs Ts;
    val coiter_fTs = map2 (curry op -->) activeAs Ts;
    val corec_sTs = map (Term.typ_subst_atomic (activeBs ~~ Ts)) sum_sTs;
    val corec_maps = map (Term.subst_atomic_types (activeBs ~~ Ts)) map_Inls;
    val corec_maps_rev = map (Term.subst_atomic_types (activeBs ~~ Ts)) map_Inls_rev;
    val corec_Inls = map (Term.subst_atomic_types (activeBs ~~ Ts)) Inls;

    val (((((((((((((Jzs, Jzs'), (Jz's, Jz's')), Jzs_copy), Jzs1), Jzs2), Jpairs),
      FJzs), TRs), coiter_fs), coiter_fs_copy), corec_ss), phis), names_lthy) = names_lthy
      |> mk_Frees' "z" Ts
      ||>> mk_Frees' "z" Ts'
      ||>> mk_Frees "z" Ts
      ||>> mk_Frees "z1" Ts
      ||>> mk_Frees "z2" Ts
      ||>> mk_Frees "j" (map2 (curry HOLogic.mk_prodT) Ts Ts')
      ||>> mk_Frees "x" prodFTs
      ||>> mk_Frees "R" (map (mk_relT o `I) Ts)
      ||>> mk_Frees "f" coiter_fTs
      ||>> mk_Frees "g" coiter_fTs
      ||>> mk_Frees "s" corec_sTs
      ||>> mk_Frees "phi" (map (fn T => T --> T --> HOLogic.boolT) Ts);

    fun unf_bind i = Binding.suffix_name ("_" ^ unfN) (nth bs (i - 1));
    val unf_name = Binding.name_of o unf_bind;
    val unf_def_bind = rpair [] o Thm.def_binding o unf_bind;

    fun unf_spec i rep str map_FT unfT Jz Jz' =
      let
        val lhs = Free (unf_name i, unfT);
        val rhs = Term.absfree Jz'
          (Term.list_comb (map_FT, map HOLogic.id_const passiveAs @ Abs_Ts) $
            (str $ (rep $ Jz)));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((unf_frees, (_, unf_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map7 (fn i => fn rep => fn str => fn map => fn unfT => fn Jz => fn Jz' =>
        Specification.definition
          (SOME (unf_bind i, NONE, NoSyn), (unf_def_bind i, unf_spec i rep str map unfT Jz Jz')))
          ks Rep_Ts str_finals map_FTs unfTs Jzs Jzs'
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_unfs passive =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ (deads @ passive)) o
        Morphism.term phi) unf_frees;
    val unfs = mk_unfs passiveAs;
    val unf's = mk_unfs passiveBs;
    val unf_defs = map ((fn thm => thm RS fun_cong) o Morphism.thm phi) unf_def_frees;

    val coalg_final_set_thmss = map (map (fn thm => coalg_final_thm RS thm)) coalg_set_thmss;
    val (mor_Rep_thm, mor_Abs_thm) =
      let
        val mor_Rep =
          Skip_Proof.prove lthy [] []
            (HOLogic.mk_Trueprop (mk_mor UNIVs unfs car_finals str_finals Rep_Ts))
            (mk_mor_Rep_tac m (mor_def :: unf_defs) Reps Abs_inverses coalg_final_set_thmss
              map_comp_id_thms map_congL_thms);

        val mor_Abs =
          Skip_Proof.prove lthy [] []
            (HOLogic.mk_Trueprop (mk_mor car_finals str_finals UNIVs unfs Abs_Ts))
            (mk_mor_Abs_tac (mor_def :: unf_defs) Abs_inverses);
      in
        (mor_Rep, mor_Abs)
      end;

    val timer = time (timer "unf definitions & thms");

    fun coiter_bind i = Binding.suffix_name ("_" ^ coN ^ iterN) (nth bs (i - 1));
    val coiter_name = Binding.name_of o coiter_bind;
    val coiter_def_bind = rpair [] o Thm.def_binding o coiter_bind;

    fun coiter_spec i T AT abs f z z' =
      let
        val coiterT = Library.foldr (op -->) (sTs, AT --> T);

        val lhs = Term.list_comb (Free (coiter_name i, coiterT), ss);
        val rhs = Term.absfree z' (abs $ (f $ z));
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((coiter_frees, (_, coiter_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map7 (fn i => fn T => fn AT => fn abs => fn f => fn z => fn z' =>
        Specification.definition
          (SOME (coiter_bind i, NONE, NoSyn), (coiter_def_bind i, coiter_spec i T AT abs f z z')))
          ks Ts activeAs Abs_Ts (map (fn i => HOLogic.mk_comp
            (mk_proj (mk_LSBIS passive_UNIVs i), mk_beh ss i)) ks) zs zs'
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    val coiters = map (fst o dest_Const o Morphism.term phi) coiter_frees;
    fun mk_coiter Ts ss i = Term.list_comb (Const (nth coiters (i - 1), Library.foldr (op -->)
      (map fastype_of ss, domain_type (fastype_of (nth ss (i - 1))) --> nth Ts (i - 1))), ss);
    val coiter_defs = map ((fn thm => thm RS fun_cong) o Morphism.thm phi) coiter_def_frees;

    val mor_coiter_thm =
      let
        val Abs_inverses' = map2 (curry op RS) in_car_final_thms Abs_inverses;
        val morEs' = map (fn thm =>
          (thm OF [tcoalg_thm RS mor_final_thm, UNIV_I]) RS sym) morE_thms;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all ss
            (HOLogic.mk_Trueprop (mk_mor active_UNIVs ss UNIVs unfs (map (mk_coiter Ts ss) ks))))
          (K (mk_mor_coiter_tac m mor_UNIV_thm unf_defs coiter_defs Abs_inverses' morEs'
            map_comp_id_thms map_congs))
      end;
    val coiter_thms = map (fn thm => (thm OF [mor_coiter_thm, UNIV_I]) RS sym) morE_thms;

    val (raw_coind_thms, raw_coind_thm) =
      let
        val prem = HOLogic.mk_Trueprop (mk_sbis passive_UNIVs UNIVs unfs TRs);
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 (fn R => fn T => mk_subset R (Id_const T)) TRs Ts));
        val goal = fold_rev Logic.all TRs (Logic.mk_implies (prem, concl));
      in
        `split_conj_thm (Skip_Proof.prove lthy [] [] goal
          (K (mk_raw_coind_tac bis_def bis_cong_thm bis_O_thm bis_converse_thm bis_Gr_thm
            tcoalg_thm coalgT_thm mor_T_final_thm sbis_lsbis_thm
            lsbis_incl_thms incl_lsbis_thms equiv_LSBIS_thms mor_Rep_thm Rep_injects)))
      end;

    val unique_mor_thms =
      let
        val prems = [HOLogic.mk_Trueprop (mk_coalg passive_UNIVs Bs ss), HOLogic.mk_Trueprop
          (HOLogic.mk_conj (mk_mor Bs ss UNIVs unfs coiter_fs,
            mk_mor Bs ss UNIVs unfs coiter_fs_copy))];
        fun mk_fun_eq B f g z = HOLogic.mk_imp
          (HOLogic.mk_mem (z, B), HOLogic.mk_eq (f $ z, g $ z));
        val unique = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map4 mk_fun_eq Bs coiter_fs coiter_fs_copy zs));

        val unique_mor = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ coiter_fs @ coiter_fs_copy @ zs)
            (Logic.list_implies (prems, unique)))
          (K (mk_unique_mor_tac raw_coind_thms bis_image2_thm));
      in
        map (fn thm => conjI RSN (2, thm RS mp)) (split_conj_thm unique_mor)
      end;

    val (coiter_unique_mor_thms, coiter_unique_mor_thm) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor active_UNIVs ss UNIVs unfs coiter_fs);
        fun mk_fun_eq f i = HOLogic.mk_eq (f, mk_coiter Ts ss i);
        val unique = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 mk_fun_eq coiter_fs ks));

        val bis_thm = tcoalg_thm RSN (2, tcoalg_thm RS bis_image2_thm);
        val mor_thm = mor_comp_thm OF [tcoalg_thm RS mor_final_thm, mor_Abs_thm];

        val unique_mor = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (ss @ coiter_fs) (Logic.mk_implies (prem, unique)))
          (K (mk_coiter_unique_mor_tac raw_coind_thms bis_thm mor_thm coiter_defs));
      in
        `split_conj_thm unique_mor
      end;

    val (coiter_unique_thms, coiter_unique_thm) = `split_conj_thm (split_conj_prems n
      (mor_UNIV_thm RS @{thm ssubst[of _ _ "%x. x"]} RS coiter_unique_mor_thm));

    val coiter_unf_thms = map (fn thm => mor_id_thm RS thm RS sym) coiter_unique_mor_thms;

    val coiter_o_unf_thms =
      let
        val mor = mor_comp_thm OF [mor_str_thm, mor_coiter_thm];
      in
        map2 (fn unique => fn coiter_fld =>
          trans OF [mor RS unique, coiter_fld]) coiter_unique_mor_thms coiter_unf_thms
      end;

    val timer = time (timer "coiter definitions & thms");

    val map_unfs = map2 (fn Ds => fn bnf =>
      Term.list_comb (mk_map_of_bnf Ds (passiveAs @ Ts) (passiveAs @ FTs) bnf,
        map HOLogic.id_const passiveAs @ unfs)) Dss bnfs;

    fun fld_bind i = Binding.suffix_name ("_" ^ fldN) (nth bs (i - 1));
    val fld_name = Binding.name_of o fld_bind;
    val fld_def_bind = rpair [] o Thm.def_binding o fld_bind;

    fun fld_spec i fldT =
      let
        val lhs = Free (fld_name i, fldT);
        val rhs = mk_coiter Ts map_unfs i;
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((fld_frees, (_, fld_def_frees)), (lthy, lthy_old)) =
        lthy
        |> fold_map2 (fn i => fn fldT =>
          Specification.definition
            (SOME (fld_bind i, NONE, NoSyn), (fld_def_bind i, fld_spec i fldT))) ks fldTs
        |>> apsnd split_list o split_list
        ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_flds params =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ params) o Morphism.term phi)
        fld_frees;
    val flds = mk_flds params';
    val fld_defs = map (Morphism.thm phi) fld_def_frees;

    val fld_o_unf_thms = map2 (Local_Defs.fold lthy o single) fld_defs coiter_o_unf_thms;

    val unf_o_fld_thms =
      let
        fun mk_goal unf fld FT =
          HOLogic.mk_Trueprop (HOLogic.mk_eq (HOLogic.mk_comp (unf, fld), HOLogic.id_const FT));
        val goals = map3 mk_goal unfs flds FTs;
      in
        map5 (fn goal => fn fld_def => fn coiter => fn map_comp_id => fn map_congL =>
          Skip_Proof.prove lthy [] [] goal
            (mk_unf_o_fld_tac fld_def coiter map_comp_id map_congL coiter_o_unf_thms))
          goals fld_defs coiter_thms map_comp_id_thms map_congL_thms
      end;

    val unf_fld_thms = map (fn thm => thm RS @{thm pointfree_idE}) unf_o_fld_thms;
    val fld_unf_thms = map (fn thm => thm RS @{thm pointfree_idE}) fld_o_unf_thms;

    val bij_unf_thms =
      map2 (fn thm1 => fn thm2 => @{thm o_bij} OF [thm1, thm2]) fld_o_unf_thms unf_o_fld_thms;
    val inj_unf_thms = map (fn thm => thm RS @{thm bij_is_inj}) bij_unf_thms;
    val surj_unf_thms = map (fn thm => thm RS @{thm bij_is_surj}) bij_unf_thms;
    val unf_nchotomy_thms = map (fn thm => thm RS @{thm surjD}) surj_unf_thms;
    val unf_inject_thms = map (fn thm => thm RS @{thm inj_eq}) inj_unf_thms;
    val unf_exhaust_thms = map (fn thm => thm RS exE) unf_nchotomy_thms;

    val bij_fld_thms =
      map2 (fn thm1 => fn thm2 => @{thm o_bij} OF [thm1, thm2]) unf_o_fld_thms fld_o_unf_thms;
    val inj_fld_thms = map (fn thm => thm RS @{thm bij_is_inj}) bij_fld_thms;
    val surj_fld_thms = map (fn thm => thm RS @{thm bij_is_surj}) bij_fld_thms;
    val fld_nchotomy_thms = map (fn thm => thm RS @{thm surjD}) surj_fld_thms;
    val fld_inject_thms = map (fn thm => thm RS @{thm inj_eq}) inj_fld_thms;
    val fld_exhaust_thms = map (fn thm => thm RS exE) fld_nchotomy_thms;

    val fld_coiter_thms = map3 (fn unf_inject => fn coiter => fn unf_fld =>
      iffD1 OF [unf_inject, trans  OF [coiter, unf_fld RS sym]])
      unf_inject_thms coiter_thms unf_fld_thms;

    val timer = time (timer "fld definitions & thms");

    val corec_Inl_sum_thms =
      let
        val mor = mor_comp_thm OF [mor_sum_case_thm, mor_coiter_thm];
      in
        map2 (fn unique => fn coiter_unf =>
          trans OF [mor RS unique, coiter_unf]) coiter_unique_mor_thms coiter_unf_thms
      end;

    fun corec_bind i = Binding.suffix_name ("_" ^ coN ^ recN) (nth bs (i - 1));
    val corec_name = Binding.name_of o corec_bind;
    val corec_def_bind = rpair [] o Thm.def_binding o corec_bind;

    fun corec_spec i T AT =
      let
        val corecT = Library.foldr (op -->) (corec_sTs, AT --> T);
        val maps = map3 (fn unf => fn sum_s => fn map => mk_sum_case
            (HOLogic.mk_comp (Term.list_comb (map, passive_ids @ corec_Inls), unf)) sum_s)
          unfs corec_ss corec_maps;

        val lhs = Term.list_comb (Free (corec_name i, corecT), corec_ss);
        val rhs = HOLogic.mk_comp (mk_coiter Ts maps i, Inr_const T AT);
      in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
      end;

    val ((corec_frees, (_, corec_def_frees)), (lthy, lthy_old)) =
        lthy
        |> fold_map3 (fn i => fn T => fn AT =>
          Specification.definition
            (SOME (corec_bind i, NONE, NoSyn), (corec_def_bind i, corec_spec i T AT)))
            ks Ts activeAs
        |>> apsnd split_list o split_list
        ||> `Local_Theory.restore;

    (*transforms defined frees into consts*)
    val phi = Proof_Context.export_morphism lthy_old lthy;
    val corecs = map (fst o dest_Const o Morphism.term phi) corec_frees;
    fun mk_corec ss i = Term.list_comb (Const (nth corecs (i - 1), Library.foldr (op -->)
      (map fastype_of ss, domain_type (fastype_of (nth ss (i - 1))) --> nth Ts (i - 1))), ss);
    val corec_defs = map (Morphism.thm phi) corec_def_frees;

    val sum_cases =
      map2 (fn T => fn i => mk_sum_case (HOLogic.id_const T) (mk_corec corec_ss i)) Ts ks;
    val corec_thms =
      let
        fun mk_goal i corec_s corec_map unf z =
          let
            val lhs = unf $ (mk_corec corec_ss i $ z);
            val rhs = Term.list_comb (corec_map, passive_ids @ sum_cases) $ (corec_s $ z);
          in
            fold_rev Logic.all (z :: corec_ss) (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
          end;
        val goals = map5 mk_goal ks corec_ss corec_maps_rev unfs zs;
      in
        map3 (fn goal => fn coiter => fn map_cong =>
          Skip_Proof.prove lthy [] [] goal
            (mk_corec_tac m corec_defs coiter map_cong corec_Inl_sum_thms))
          goals coiter_thms map_congs
      end;

    val timer = time (timer "corec definitions & thms");

    val (unf_coinduct_thm, coinduct_params, rel_coinduct_thm, pred_coinduct_thm,
         unf_coinduct_upto_thm, rel_coinduct_upto_thm, pred_coinduct_upto_thm) =
      let
        val zs = Jzs1 @ Jzs2;
        val frees = phis @ zs;

        fun mk_Ids Id = if Id then map Id_const passiveAs else map mk_diag passive_UNIVs;

        fun mk_phi upto_eq phi z1 z2 = if upto_eq
          then Term.absfree (dest_Free z1) (Term.absfree (dest_Free z2)
            (HOLogic.mk_disj (phi $ z1 $ z2, HOLogic.mk_eq (z1, z2))))
          else phi;

        fun phi_rels upto_eq = map4 (fn phi => fn T => fn z1 => fn z2 =>
          HOLogic.Collect_const (HOLogic.mk_prodT (T, T)) $
            HOLogic.mk_split (mk_phi upto_eq phi z1 z2)) phis Ts Jzs1 Jzs2;

        val rels = map (Term.subst_atomic_types ((activeAs ~~ Ts) @ (activeBs ~~ Ts))) relsAsBs;

        fun mk_concl phi z1 z2 = HOLogic.mk_imp (phi $ z1 $ z2, HOLogic.mk_eq (z1, z2));
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map3 mk_concl phis Jzs1 Jzs2));

        fun mk_rel_prem upto_eq phi unf rel Jz Jz_copy =
          let
            val concl = HOLogic.mk_mem (HOLogic.mk_tuple [unf $ Jz, unf $ Jz_copy],
              Term.list_comb (rel, mk_Ids upto_eq @ phi_rels upto_eq));
          in
            HOLogic.mk_Trueprop
              (list_all_free [Jz, Jz_copy] (HOLogic.mk_imp (phi $ Jz $ Jz_copy, concl)))
          end;

        val rel_prems = map5 (mk_rel_prem false) phis unfs rels Jzs Jzs_copy;
        val rel_upto_prems = map5 (mk_rel_prem true) phis unfs rels Jzs Jzs_copy;

        val rel_coinduct_goal = fold_rev Logic.all frees (Logic.list_implies (rel_prems, concl));
        val coinduct_params = rev (Term.add_tfrees rel_coinduct_goal []);

        val rel_coinduct = Local_Defs.unfold lthy @{thms diag_UNIV}
          (Skip_Proof.prove lthy [] [] rel_coinduct_goal
            (K (mk_rel_coinduct_tac ks raw_coind_thm bis_rel_thm)));

        fun mk_unf_prem upto_eq phi unf map_nth sets Jz Jz_copy FJz =
          let
            val xs = [Jz, Jz_copy];

            fun mk_map_conjunct nths x =
              HOLogic.mk_eq (Term.list_comb (map_nth, passive_ids @ nths) $ FJz, unf $ x);

            fun mk_set_conjunct set phi z1 z2 =
              list_all_free [z1, z2]
                (HOLogic.mk_imp (HOLogic.mk_mem (HOLogic.mk_prod (z1, z2), set $ FJz),
                  mk_phi upto_eq phi z1 z2 $ z1 $ z2));

            val concl = list_exists_free [FJz] (HOLogic.mk_conj
              (Library.foldr1 HOLogic.mk_conj (map2 mk_map_conjunct [fstsTs, sndsTs] xs),
              Library.foldr1 HOLogic.mk_conj
                (map4 mk_set_conjunct (drop m sets) phis Jzs1 Jzs2)));
          in
            fold_rev Logic.all xs (Logic.mk_implies
              (HOLogic.mk_Trueprop (Term.list_comb (phi, xs)), HOLogic.mk_Trueprop concl))
          end;

        fun mk_unf_prems upto_eq =
          map7 (mk_unf_prem upto_eq) phis unfs map_FT_nths prodFT_setss Jzs Jzs_copy FJzs

        val unf_prems = mk_unf_prems false;
        val unf_upto_prems = mk_unf_prems true;

        val unf_coinduct_goal = fold_rev Logic.all frees (Logic.list_implies (unf_prems, concl));
        val unf_coinduct = Skip_Proof.prove lthy [] [] unf_coinduct_goal
          (K (mk_unf_coinduct_tac m ks raw_coind_thm bis_def));

        val cTs = map (SOME o certifyT lthy o TFree) coinduct_params;
        val cts = map3 (SOME o certify lthy ooo mk_phi true) phis Jzs1 Jzs2;

        val rel_coinduct_upto = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] []
            (fold_rev Logic.all zs (Logic.list_implies (rel_upto_prems, concl)))
            (K (mk_rel_coinduct_upto_tac m cTs cts rel_coinduct rel_monos rel_Ids)));

        val unf_coinduct_upto = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] []
            (fold_rev Logic.all zs (Logic.list_implies (unf_upto_prems, concl)))
            (K (mk_unf_coinduct_upto_tac ks cTs cts unf_coinduct bis_def
              (tcoalg_thm RS bis_diag_thm))));

        val pred_coinduct = rel_coinduct
          |> Local_Defs.unfold lthy @{thms Id_def'}
          |> Local_Defs.fold lthy pred_defs;
        val pred_coinduct_upto = rel_coinduct_upto
          |> Local_Defs.unfold lthy @{thms Id_def'}
          |> Local_Defs.fold lthy pred_defs;
      in
        (unf_coinduct, rev (Term.add_tfrees unf_coinduct_goal []), rel_coinduct, pred_coinduct,
         unf_coinduct_upto, rel_coinduct_upto, pred_coinduct_upto)
      end;

    val timer = time (timer "coinduction");

    (*register new codatatypes as BNFs*)
    val lthy = if m = 0 then lthy else
      let
        val fTs = map2 (curry op -->) passiveAs passiveBs;
        val gTs = map2 (curry op -->) passiveBs passiveCs;
        val f1Ts = map2 (curry op -->) passiveAs passiveYs;
        val f2Ts = map2 (curry op -->) passiveBs passiveYs;
        val p1Ts = map2 (curry op -->) passiveXs passiveAs;
        val p2Ts = map2 (curry op -->) passiveXs passiveBs;
        val pTs = map2 (curry op -->) passiveXs passiveCs;
        val uTs = map2 (curry op -->) Ts Ts';
        val JRTs = map2 (curry mk_relT) passiveAs passiveBs;
        val JphiTs = map2 (fn T => fn U => T --> U --> HOLogic.boolT) passiveAs passiveBs;
        val prodTs = map2 (curry HOLogic.mk_prodT) Ts Ts';
        val B1Ts = map HOLogic.mk_setT passiveAs;
        val B2Ts = map HOLogic.mk_setT passiveBs;
        val AXTs = map HOLogic.mk_setT passiveXs;
        val XTs = mk_Ts passiveXs;
        val YTs = mk_Ts passiveYs;

        val (((((((((((((((((((((fs, fs'), (fs_copy, fs'_copy)), (gs, gs')), us),
          (Jys, Jys')), (Jys_copy, Jys'_copy)), set_induct_phiss), JRs), Jphis),
          B1s), B2s), AXs), Xs), f1s), f2s), p1s), p2s), ps), (ys, ys')), (ys_copy, ys'_copy)),
          names_lthy) = names_lthy
          |> mk_Frees' "f" fTs
          ||>> mk_Frees' "f" fTs
          ||>> mk_Frees' "g" gTs
          ||>> mk_Frees "u" uTs
          ||>> mk_Frees' "b" Ts'
          ||>> mk_Frees' "b" Ts'
          ||>> mk_Freess "phi" (map (fn T => map (fn U => T --> U --> HOLogic.boolT) Ts) passiveAs)
          ||>> mk_Frees "R" JRTs
          ||>> mk_Frees "phi" JphiTs
          ||>> mk_Frees "B1" B1Ts
          ||>> mk_Frees "B2" B2Ts
          ||>> mk_Frees "A" AXTs
          ||>> mk_Frees "x" XTs
          ||>> mk_Frees "f1" f1Ts
          ||>> mk_Frees "f2" f2Ts
          ||>> mk_Frees "p1" p1Ts
          ||>> mk_Frees "p2" p2Ts
          ||>> mk_Frees "p" pTs
          ||>> mk_Frees' "y" passiveAs
          ||>> mk_Frees' "y" passiveAs;

        val map_FTFT's = map2 (fn Ds =>
          mk_map_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;

        fun mk_maps ATs BTs Ts mk_T =
          map2 (fn Ds => mk_map_of_bnf Ds (ATs @ Ts) (BTs @ map mk_T Ts)) Dss bnfs;
        fun mk_Fmap mk_const fs Ts Fmap = Term.list_comb (Fmap, fs @ map mk_const Ts);
        fun mk_map mk_const mk_T Ts fs Ts' unfs mk_maps =
          mk_coiter Ts' (map2 (fn unf => fn Fmap =>
            HOLogic.mk_comp (mk_Fmap mk_const fs Ts Fmap, unf)) unfs (mk_maps Ts mk_T));
        val mk_map_id = mk_map HOLogic.id_const I;
        val mk_mapsAB = mk_maps passiveAs passiveBs;
        val mk_mapsBC = mk_maps passiveBs passiveCs;
        val mk_mapsAC = mk_maps passiveAs passiveCs;
        val mk_mapsAY = mk_maps passiveAs passiveYs;
        val mk_mapsBY = mk_maps passiveBs passiveYs;
        val mk_mapsXA = mk_maps passiveXs passiveAs;
        val mk_mapsXB = mk_maps passiveXs passiveBs;
        val mk_mapsXC = mk_maps passiveXs passiveCs;
        val fs_maps = map (mk_map_id Ts fs Ts' unfs mk_mapsAB) ks;
        val fs_copy_maps = map (mk_map_id Ts fs_copy Ts' unfs mk_mapsAB) ks;
        val gs_maps = map (mk_map_id Ts' gs Ts'' unf's mk_mapsBC) ks;
        val fgs_maps =
          map (mk_map_id Ts (map2 (curry HOLogic.mk_comp) gs fs) Ts'' unfs mk_mapsAC) ks;
        val Xunfs = mk_unfs passiveXs;
        val UNIV's = map HOLogic.mk_UNIV Ts';
        val CUNIVs = map HOLogic.mk_UNIV passiveCs;
        val UNIV''s = map HOLogic.mk_UNIV Ts'';
        val fstsTsTs' = map fst_const prodTs;
        val sndsTsTs' = map snd_const prodTs;
        val unf''s = mk_unfs passiveCs;
        val f1s_maps = map (mk_map_id Ts f1s YTs unfs mk_mapsAY) ks;
        val f2s_maps = map (mk_map_id Ts' f2s YTs unf's mk_mapsBY) ks;
        val pid_maps = map (mk_map_id XTs ps Ts'' Xunfs mk_mapsXC) ks;
        val pfst_Fmaps =
          map (mk_Fmap fst_const p1s prodTs) (mk_mapsXA prodTs (fst o HOLogic.dest_prodT));
        val psnd_Fmaps =
          map (mk_Fmap snd_const p2s prodTs) (mk_mapsXB prodTs (snd o HOLogic.dest_prodT));
        val p1id_Fmaps = map (mk_Fmap HOLogic.id_const p1s prodTs) (mk_mapsXA prodTs I);
        val p2id_Fmaps = map (mk_Fmap HOLogic.id_const p2s prodTs) (mk_mapsXB prodTs I);
        val pid_Fmaps = map (mk_Fmap HOLogic.id_const ps prodTs) (mk_mapsXC prodTs I);

        val (map_simp_thms, map_thms) =
          let
            fun mk_goal fs_map map unf unf' = fold_rev Logic.all fs
              (HOLogic.mk_Trueprop (HOLogic.mk_eq (HOLogic.mk_comp (unf', fs_map),
                HOLogic.mk_comp (Term.list_comb (map, fs @ fs_maps), unf))));
            val goals = map4 mk_goal fs_maps map_FTFT's unfs unf's;
            val cTs = map (SOME o certifyT lthy) FTs';
            val maps = map5 (fn goal => fn cT => fn coiter => fn map_comp' => fn map_cong =>
              Skip_Proof.prove lthy [] [] goal
                (K (mk_map_tac m n cT coiter map_comp' map_cong)))
              goals cTs coiter_thms map_comp's map_congs;
          in
            map_split (fn thm => (thm RS @{thm pointfreeE}, thm)) maps
          end;

        val map_comp_thms =
          let
            val goal = fold_rev Logic.all (fs @ gs)
              (HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map3 (fn fmap => fn gmap => fn fgmap =>
                   HOLogic.mk_eq (HOLogic.mk_comp (gmap, fmap), fgmap))
                fs_maps gs_maps fgs_maps)))
          in
            split_conj_thm (Skip_Proof.prove lthy [] [] goal
              (K (mk_map_comp_tac m n map_thms map_comps map_congs coiter_unique_thm)))
          end;

        val (map_unique_thms, map_unique_thm) =
          let
            fun mk_prem u map unf unf' =
              HOLogic.mk_Trueprop (HOLogic.mk_eq (HOLogic.mk_comp (unf', u),
                HOLogic.mk_comp (Term.list_comb (map, fs @ us), unf)));
            val prems = map4 mk_prem us map_FTFT's unfs unf's;
            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map2 (curry HOLogic.mk_eq) us fs_maps));
            val unique = Skip_Proof.prove lthy [] []
              (fold_rev Logic.all (us @ fs) (Logic.list_implies (prems, goal)))
              (mk_map_unique_tac coiter_unique_thm map_comps);
          in
            `split_conj_thm unique
          end;

        val timer = time (timer "map functions for the new codatatypes");

        val bd = mk_ccexp sbd sbd;

        val timer = time (timer "bounds for the new codatatypes");

        fun mk_set_Ts T = passiveAs @ replicate n (HOLogic.mk_setT T);
        val setsss = map (mk_setss o mk_set_Ts) passiveAs;
        val map_setss = map (fn T => map2 (fn Ds =>
          mk_map_of_bnf Ds (passiveAs @ Ts) (mk_set_Ts T)) Dss bnfs) passiveAs;

        val setss_by_bnf = map (fn i => map2 (mk_hset unfs i) ls passiveAs) ks;
        val setss_by_bnf' = map (fn i => map2 (mk_hset unf's i) ls passiveBs) ks;
        val setss_by_range = transpose setss_by_bnf;

        val set_simp_thmss =
          let
            fun mk_simp_goal relate pas_set act_sets sets unf z set =
              relate (set $ z, mk_union (pas_set $ (unf $ z),
                 Library.foldl1 mk_union
                   (map2 (fn X => mk_UNION (X $ (unf $ z))) act_sets sets)));
            fun mk_goals eq =
              map2 (fn i => fn sets =>
                map4 (fn Fsets =>
                  mk_simp_goal eq (nth Fsets (i - 1)) (drop m Fsets) sets)
                FTs_setss unfs Jzs sets)
              ls setss_by_range;

            val le_goals = map
              (fold_rev Logic.all Jzs o HOLogic.mk_Trueprop o Library.foldr1 HOLogic.mk_conj)
              (mk_goals (uncurry mk_subset));
            val set_le_thmss = map split_conj_thm
              (map4 (fn goal => fn hset_minimal => fn set_hsets => fn set_hset_hsetss =>
                Skip_Proof.prove lthy [] [] goal
                  (K (mk_set_le_tac n hset_minimal set_hsets set_hset_hsetss)))
              le_goals hset_minimal_thms set_hset_thmss' set_hset_hset_thmsss');

            val simp_goalss = map (map2 (fn z => fn goal =>
                Logic.all z (HOLogic.mk_Trueprop goal)) Jzs)
              (mk_goals HOLogic.mk_eq);
          in
            map4 (map4 (fn goal => fn set_le => fn set_incl_hset => fn set_hset_incl_hsets =>
              Skip_Proof.prove lthy [] [] goal
                (K (mk_set_simp_tac n set_le set_incl_hset set_hset_incl_hsets))))
            simp_goalss set_le_thmss set_incl_hset_thmss' set_hset_incl_hset_thmsss'
          end;

        val timer = time (timer "set functions for the new codatatypes");

        val colss = map2 (fn j => fn T =>
          map (fn i => mk_hset_rec unfs nat i j T) ks) ls passiveAs;
        val colss' = map2 (fn j => fn T =>
          map (fn i => mk_hset_rec unf's nat i j T) ks) ls passiveBs;
        val Xcolss = map2 (fn j => fn T =>
          map (fn i => mk_hset_rec Xunfs nat i j T) ks) ls passiveXs;

        val col_natural_thmss =
          let
            fun mk_col_natural f map z col col' =
              HOLogic.mk_eq (mk_image f $ (col $ z), col' $ (map $ z));

            fun mk_goal f cols cols' = list_all_free Jzs (Library.foldr1 HOLogic.mk_conj
              (map4 (mk_col_natural f) fs_maps Jzs cols cols'));

            val goals = map3 mk_goal fs colss colss';

            val ctss =
              map (fn phi => map (SOME o certify lthy) [Term.absfree nat' phi, nat]) goals;

            val thms = map4 (fn goal => fn cts => fn rec_0s => fn rec_Sucs =>
              singleton (Proof_Context.export names_lthy lthy)
                (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
                  (mk_col_natural_tac cts rec_0s rec_Sucs map_simp_thms set_natural'ss)))
              goals ctss hset_rec_0ss' hset_rec_Sucss';
          in
            map (split_conj_thm o mk_specN n) thms
          end;

        val col_bd_thmss =
          let
            fun mk_col_bd z col = mk_ordLeq (mk_card_of (col $ z)) sbd;

            fun mk_goal cols = list_all_free Jzs (Library.foldr1 HOLogic.mk_conj
              (map2 mk_col_bd Jzs cols));

            val goals = map mk_goal colss;

            val ctss =
              map (fn phi => map (SOME o certify lthy) [Term.absfree nat' phi, nat]) goals;

            val thms = map5 (fn j => fn goal => fn cts => fn rec_0s => fn rec_Sucs =>
              singleton (Proof_Context.export names_lthy lthy)
                (Skip_Proof.prove lthy [] [] (HOLogic.mk_Trueprop goal)
                  (K (mk_col_bd_tac m j cts rec_0s rec_Sucs
                    sbd_Card_order sbd_Cinfinite set_sbdss))))
              ls goals ctss hset_rec_0ss' hset_rec_Sucss';
          in
            map (split_conj_thm o mk_specN n) thms
          end;

        val map_cong_thms =
          let
            val cTs = map (SOME o certifyT lthy o
              Term.typ_subst_atomic (passiveAs ~~ passiveBs) o TFree) coinduct_params;

            fun mk_prem z set f g y y' =
              mk_Ball (set $ z) (Term.absfree y' (HOLogic.mk_eq (f $ y, g $ y)));

            fun mk_prems sets z =
              Library.foldr1 HOLogic.mk_conj (map5 (mk_prem z) sets fs fs_copy ys ys')

            fun mk_map_cong sets z fmap gmap =
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
              |> certify lthy;

            val cphis =
              map9 mk_cphi setss_by_bnf Jzs' Jzs fs_maps fs_copy_maps Jys' Jys Jys'_copy Jys_copy;

            val coinduct = Drule.instantiate' cTs (map SOME cphis) unf_coinduct_thm;

            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map4 mk_map_cong setss_by_bnf Jzs fs_maps fs_copy_maps));

            val thm = singleton (Proof_Context.export names_lthy lthy)
              (Skip_Proof.prove lthy [] [] goal
              (K (mk_mcong_tac m (rtac coinduct) map_comp's map_simp_thms map_congs set_natural'ss
              set_hset_thmss set_hset_hset_thmsss)))
          in
            split_conj_thm thm
          end;

        val B1_ins = map2 (mk_in B1s) setss_by_bnf Ts;
        val B2_ins = map2 (mk_in B2s) setss_by_bnf' Ts';
        val thePulls = map4 mk_thePull B1_ins B2_ins f1s_maps f2s_maps;
        val thePullTs = passiveXs @ map2 (curry HOLogic.mk_prodT) Ts Ts';
        val thePull_ins = map2 (mk_in (AXs @ thePulls)) (mk_setss thePullTs) (mk_FTs thePullTs);
        val pickFs = map5 mk_pickWP thePull_ins pfst_Fmaps psnd_Fmaps
          (map2 (curry (op $)) unfs Jzs) (map2 (curry (op $)) unf's Jz's);
        val pickF_ss = map3 (fn pickF => fn z => fn z' =>
          HOLogic.mk_split (Term.absfree z (Term.absfree z' pickF))) pickFs Jzs' Jz's';
        val picks = map (mk_coiter XTs pickF_ss) ks;

        val wpull_prem = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map8 mk_wpull AXs B1s B2s f1s f2s (replicate m NONE) p1s p2s));

        val map_eq_thms = map2 (fn simp => fn diff => box_equals OF [diff RS iffD2, simp, simp])
          map_simp_thms unf_inject_thms;
        val map_wpull_thms = map (fn thm => thm OF
          (replicate m asm_rl @ replicate n @{thm wpull_thePull})) map_wpulls;
        val pickWP_assms_tacs =
          map3 mk_pickWP_assms_tac set_incl_hset_thmss set_incl_hin_thmss map_eq_thms;

        val coalg_thePull_thm =
          let
            val coalg = HOLogic.mk_Trueprop
              (mk_coalg CUNIVs thePulls (map2 (curry HOLogic.mk_comp) pid_Fmaps pickF_ss));
            val goal = fold_rev Logic.all (AXs @ B1s @ B2s @ f1s @ f2s @ p1s @ p2s @ ps)
              (Logic.mk_implies (wpull_prem, coalg));
          in
            Skip_Proof.prove lthy [] [] goal (mk_coalg_thePull_tac m coalg_def map_wpull_thms
              set_natural'ss pickWP_assms_tacs)
          end;

        val (mor_thePull_fst_thm, mor_thePull_snd_thm, mor_thePull_pick_thm) =
          let
            val mor_fst = HOLogic.mk_Trueprop
              (mk_mor thePulls (map2 (curry HOLogic.mk_comp) p1id_Fmaps pickF_ss)
                UNIVs unfs fstsTsTs');
            val mor_snd = HOLogic.mk_Trueprop
              (mk_mor thePulls (map2 (curry HOLogic.mk_comp) p2id_Fmaps pickF_ss)
                UNIV's unf's sndsTsTs');
            val mor_pick = HOLogic.mk_Trueprop
              (mk_mor thePulls (map2 (curry HOLogic.mk_comp) pid_Fmaps pickF_ss)
                UNIV''s unf''s (map2 (curry HOLogic.mk_comp) pid_maps picks));

            val goal_fst = fold_rev Logic.all (AXs @ B1s @ B2s @ f1s @ f2s @ p1s @ p2s)
              (Logic.mk_implies (wpull_prem, mor_fst));
            val goal_snd = fold_rev Logic.all (AXs @ B1s @ B2s @ f1s @ f2s @ p1s @ p2s)
              (Logic.mk_implies (wpull_prem, mor_snd));
            val goal_pick = fold_rev Logic.all (AXs @ B1s @ B2s @ f1s @ f2s @ p1s @ p2s @ ps)
              (Logic.mk_implies (wpull_prem, mor_pick));
          in
            (Skip_Proof.prove lthy [] [] goal_fst (mk_mor_thePull_fst_tac m mor_def map_wpull_thms
              map_comp's pickWP_assms_tacs),
            Skip_Proof.prove lthy [] [] goal_snd (mk_mor_thePull_snd_tac m mor_def map_wpull_thms
              map_comp's pickWP_assms_tacs),
            Skip_Proof.prove lthy [] [] goal_pick (mk_mor_thePull_pick_tac mor_def coiter_thms
              map_comp's))
          end;

        val pick_col_thmss =
          let
            fun mk_conjunct AX Jpair pick thePull col =
              HOLogic.mk_imp (HOLogic.mk_mem (Jpair, thePull), mk_subset (col $ (pick $ Jpair)) AX);

            fun mk_concl AX cols =
              list_all_free Jpairs (Library.foldr1 HOLogic.mk_conj
                (map4 (mk_conjunct AX) Jpairs picks thePulls cols));

            val concls = map2 mk_concl AXs Xcolss;

            val ctss =
              map (fn phi => map (SOME o certify lthy) [Term.absfree nat' phi, nat]) concls;

            val goals =
              map (fn concl => Logic.mk_implies (wpull_prem, HOLogic.mk_Trueprop concl)) concls;

            val thms = map5 (fn j => fn goal => fn cts => fn rec_0s => fn rec_Sucs =>
              singleton (Proof_Context.export names_lthy lthy) (Skip_Proof.prove lthy [] [] goal
                (mk_pick_col_tac m j cts rec_0s rec_Sucs coiter_thms set_natural'ss map_wpull_thms
                  pickWP_assms_tacs)))
              ls goals ctss hset_rec_0ss' hset_rec_Sucss';
          in
            map (map (fn thm => thm RS mp) o split_conj_thm o mk_specN n) thms
          end;

        val timer = time (timer "helpers for BNF properties");

        val map_id_tacs = map2 (K oo mk_map_id_tac map_thms) coiter_unique_thms coiter_unf_thms;
        val map_comp_tacs = map (fn thm => K (rtac (thm RS sym) 1)) map_comp_thms;
        val map_cong_tacs = map (mk_map_cong_tac m) map_cong_thms;
        val set_nat_tacss =
          map2 (map2 (K oo mk_set_natural_tac)) hset_defss (transpose col_natural_thmss);

        val bd_co_tacs = replicate n (K (mk_bd_card_order_tac sbd_card_order));
        val bd_cinf_tacs = replicate n (K (mk_bd_cinfinite_tac sbd_Cinfinite));

        val set_bd_tacss =
          map2 (map2 (K oo mk_set_bd_tac sbd_Cinfinite)) hset_defss (transpose col_bd_thmss);

        val in_bd_tacs = map7 (fn i => fn isNode_hsets => fn carT_def =>
            fn card_of_carT => fn mor_image => fn Rep_inverse => fn mor_hsets =>
          K (mk_in_bd_tac (nth isNode_hsets (i - 1)) isNode_hsets carT_def
            card_of_carT mor_image Rep_inverse mor_hsets
            sbd_Cnotzero sbd_Card_order mor_Rep_thm coalgT_thm mor_T_final_thm tcoalg_thm))
          ks isNode_hset_thmss carT_defs card_of_carT_thms
          mor_image'_thms Rep_inverses (transpose mor_hset_thmss);

        val map_wpull_tacs =
          map3 (K ooo mk_wpull_tac m coalg_thePull_thm mor_thePull_fst_thm mor_thePull_snd_thm
            mor_thePull_pick_thm) unique_mor_thms (transpose pick_col_thmss) hset_defss;

        val tacss = map9 mk_tactics map_id_tacs map_comp_tacs map_cong_tacs set_nat_tacss bd_co_tacs
          bd_cinf_tacs set_bd_tacss in_bd_tacs map_wpull_tacs;

        val (hset_unf_incl_thmss, hset_hset_unf_incl_thmsss, hset_induct_thms) =
          let
            fun tinst_of unf =
              map (SOME o certify lthy) (unf :: remove (op =) unf unfs);
            fun tinst_of' unf = case tinst_of unf of t :: ts => t :: NONE :: ts;
            val Tinst = map (pairself (certifyT lthy))
              (map Logic.varifyT_global (deads @ allAs) ~~ (deads @ passiveAs @ Ts));
            val set_incl_thmss =
              map2 (fn unf => map (singleton (Proof_Context.export names_lthy lthy) o
                Drule.instantiate' [] (tinst_of' unf) o
                Thm.instantiate (Tinst, []) o Drule.zero_var_indexes))
              unfs set_incl_hset_thmss;

            val tinst = interleave (map (SOME o certify lthy) unfs) (replicate n NONE)
            val set_minimal_thms =
              map (Drule.instantiate' [] tinst o Thm.instantiate (Tinst, []) o
                Drule.zero_var_indexes)
              hset_minimal_thms;

            val set_set_incl_thmsss =
              map2 (fn unf => map (map (singleton (Proof_Context.export names_lthy lthy) o
                Drule.instantiate' [] (NONE :: tinst_of' unf) o
                Thm.instantiate (Tinst, []) o Drule.zero_var_indexes)))
              unfs set_hset_incl_hset_thmsss;

            val set_set_incl_thmsss' = transpose (map transpose set_set_incl_thmsss);

            val incls =
              maps (map (fn thm => thm RS @{thm subset_Collect_iff})) set_incl_thmss @
                @{thms subset_Collect_iff[OF subset_refl]};

            fun mk_induct_tinst phis jsets y y' =
              map4 (fn phi => fn jset => fn Jz => fn Jz' =>
                SOME (certify lthy (Term.absfree Jz' (HOLogic.mk_Collect (fst y', snd y',
                  HOLogic.mk_conj (HOLogic.mk_mem (y, jset $ Jz), phi $ y $ Jz))))))
              phis jsets Jzs Jzs';
            val set_induct_thms =
              map6 (fn set_minimal => fn set_set_inclss => fn jsets => fn y => fn y' => fn phis =>
                ((set_minimal
                  |> Drule.instantiate' [] (mk_induct_tinst phis jsets y y')
                  |> Local_Defs.unfold lthy incls) OF
                  (replicate n ballI @
                    maps (map (fn thm => thm RS @{thm subset_CollectI})) set_set_inclss))
                |> singleton (Proof_Context.export names_lthy lthy)
                |> rule_by_tactic lthy (ALLGOALS (TRY o etac asm_rl)))
              set_minimal_thms set_set_incl_thmsss' setss_by_range ys ys' set_induct_phiss
          in
            (set_incl_thmss, set_set_incl_thmsss, set_induct_thms)
          end;

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
          map3 (fn i => fn Ds => fn bnf => mk_wits_of_bnf (replicate (nwits_of_bnf bnf) Ds)
            (replicate (nwits_of_bnf bnf) (replicate live HOLogic.unitT)) bnf
            |> map (fn (I, wit) =>
              (I, Lazy.lazy (mk_nat_wit Ds bnf (I, Term.list_comb (wit, map (K HOLogic.unit) I))))))
          ks Dss bnfs;

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
          ((I, dummys), (map (fn i => mk_coiter Ts args i $ HOLogic.unit) ks, thms));

        val coind_witss =
          maps (map (mk_coind_wits o prepare_args)) nonredundant_coind_wit_argsss;

        val _ = (warning o PolyML.makestring) (map length coind_wit_argsss)
        val _ = (warning o PolyML.makestring) (map length nonredundant_coind_wit_argsss)

        fun mk_coind_wit_thms ((I, dummys), (wits, wit_thms)) =
          let
            fun mk_goal sets y y_copy y'_copy j =
              let
                fun mk_conjunct set z dummy wit =
                  mk_Ball (set $ z) (Term.absfree y'_copy
                    (if dummy = NONE orelse member (op =) I (j - 1) then
                      HOLogic.mk_imp (HOLogic.mk_eq (z, wit),
                        if member (op =) I (j - 1) then HOLogic.mk_eq (y_copy, y)
                        else @{term False})
                    else @{term True}));
              in
                fold_rev Logic.all (map (nth ys) I @ Jzs) (HOLogic.mk_Trueprop
                  (Library.foldr1 HOLogic.mk_conj (map4 mk_conjunct sets Jzs dummys wits)))
              end;
            val goals = map5 mk_goal setss_by_range ys ys_copy ys'_copy ls;
          in
            map2 (fn goal => fn induct =>
              Skip_Proof.prove lthy [] [] goal
               (mk_coind_wit_tac induct coiter_thms (flat set_natural'ss) wit_thms))
            goals hset_induct_thms
            |> map split_conj_thm
            |> transpose
            |> map (map_filter (try (fn thm => thm RS bspec RS mp)))
            |> curry op ~~ (map_index Library.I (map (close_wit I) wits))
            |> filter (fn (_, thms) => length thms = m)
          end;

        val coind_wit_thms = maps mk_coind_wit_thms coind_witss;

        val witss = map2 (fn Ds => fn bnf => mk_wits_of_bnf
          (replicate (nwits_of_bnf bnf) Ds)
          (replicate (nwits_of_bnf bnf) (passiveAs @ Ts)) bnf) Dss bnfs;

        val fld_witss =
          map (map (uncurry close_wit o tree_to_fld_wit ys flds witss o snd o snd) o
            filter_out (fst o snd)) wit_treess;

        val all_witss =
          fold (fn ((i, wit), thms) => fn witss =>
            nth_map i (fn (thms', wits) => (thms @ thms', wit :: wits)) witss)
          coind_wit_thms (map (pair []) fld_witss)
          |> map (apsnd (map snd o minimize_wits));

        val wit_tac = mk_wit_tac n unf_fld_thms (flat set_simp_thmss) (maps wit_thms_of_bnf bnfs);

        val (Jbnfs, lthy) =
          fold_map6 (fn tacs => fn b => fn map => fn sets => fn T => fn (thms, wits) =>
            bnf_def Dont_Inline user_policy I tacs (wit_tac thms) (SOME deads)
              ((((b, fold_rev Term.absfree fs' map), sets), absdummy T bd), wits))
          tacss bs fs_maps setss_by_bnf Ts all_witss lthy;

        val fold_maps = Local_Defs.fold lthy (map (fn bnf =>
          mk_unabs_def m (map_def_of_bnf bnf RS @{thm meta_eq_to_obj_eq})) Jbnfs);

        val fold_sets = Local_Defs.fold lthy (maps (fn bnf =>
         map (fn thm => thm RS @{thm meta_eq_to_obj_eq}) (set_defs_of_bnf bnf)) Jbnfs);

        val timer = time (timer "registered new codatatypes as BNFs");

        val set_incl_thmss = map (map fold_sets) hset_unf_incl_thmss;
        val set_set_incl_thmsss = map (map (map fold_sets)) hset_hset_unf_incl_thmsss;
        val set_induct_thms = map fold_sets hset_induct_thms;

        val rels = map2 (fn Ds => mk_rel_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;
        val Jrels = map (mk_rel_of_bnf deads passiveAs passiveBs) Jbnfs;
        val preds = map2 (fn Ds => mk_pred_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;
        val Jpreds = map (mk_pred_of_bnf deads passiveAs passiveBs) Jbnfs;

        val JrelRs = map (fn Jrel => Term.list_comb (Jrel, JRs)) Jrels;
        val relRs = map (fn rel => Term.list_comb (rel, JRs @ JrelRs)) rels;
        val Jpredphis = map (fn Jrel => Term.list_comb (Jrel, Jphis)) Jpreds;
        val predphis = map (fn rel => Term.list_comb (rel, Jphis @ Jpredphis)) preds;

        val in_rels = map in_rel_of_bnf bnfs;
        val in_Jrels = map in_rel_of_bnf Jbnfs;
        val Jpred_defs =
          map (Drule.abs_def o (fn thm => thm RS @{thm eq_reflection}) o pred_def_of_bnf) Jbnfs;

        val folded_map_simp_thms = map fold_maps map_simp_thms;
        val folded_set_simp_thmss = map (map fold_sets) set_simp_thmss;
        val folded_set_simp_thmss' = transpose folded_set_simp_thmss;

        val Jrel_unfold_thms =
          let
            fun mk_goal Jz Jz' unf unf' JrelR relR = fold_rev Logic.all (Jz :: Jz' :: JRs)
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (HOLogic.mk_mem (HOLogic.mk_prod (Jz, Jz'), JrelR),
                  HOLogic.mk_mem (HOLogic.mk_prod (unf $ Jz, unf' $ Jz'), relR))));
            val goals = map6 mk_goal Jzs Jz's unfs unf's JrelRs relRs;
          in
            map12 (fn i => fn goal => fn in_rel => fn map_comp => fn map_cong =>
              fn map_simp => fn set_simps => fn unf_inject => fn unf_fld =>
              fn set_naturals => fn set_incls => fn set_set_inclss =>
              Skip_Proof.prove lthy [] [] goal
               (K (mk_rel_unfold_tac in_Jrels i in_rel map_comp map_cong map_simp set_simps
                 unf_inject unf_fld set_naturals set_incls set_set_inclss)))
            ks goals in_rels map_comp's map_congs folded_map_simp_thms folded_set_simp_thmss'
              unf_inject_thms unf_fld_thms set_natural'ss set_incl_thmss set_set_incl_thmsss
          end;

        val Jpred_unfold_thms =
          let
            fun mk_goal Jz Jz' unf unf' Jpredphi predphi = fold_rev Logic.all (Jz :: Jz' :: Jphis)
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (Jpredphi $ Jz $ Jz', predphi $ (unf $ Jz) $ (unf' $ Jz'))));
            val goals = map6 mk_goal Jzs Jz's unfs unf's Jpredphis predphis;
          in
            map3 (fn goal => fn pred_def => fn Jrel_unfold =>
              Skip_Proof.prove lthy [] [] goal (mk_pred_unfold_tac pred_def Jpred_defs Jrel_unfold))
            goals pred_defs Jrel_unfold_thms
          end;

        val timer = time (timer "additional properties");

        val ls' = if m = 1 then [0] else ls;
      in
        lthy
        |> note map_uniqueN [fold_maps map_unique_thm]
        |> notes map_simpsN (map single folded_map_simp_thms)
        |> fold2 (fn i => notes (mk_set_simpsN i) o map single) ls' folded_set_simp_thmss
        |> notes set_inclN set_incl_thmss
        |> notes set_set_inclN (map flat set_set_incl_thmsss) (* nicer names? *)
        |> fold2 (fn i => note (mk_set_inductN i) o single) ls' set_induct_thms
        |> notes rel_unfoldN (map single Jrel_unfold_thms)
        |> notes pred_unfoldN (map single Jpred_unfold_thms)
      end;
  in
    lthy
    |> notes coiterN (map single coiter_thms)
    |> notes coiter_uniqueN (map single coiter_unique_thms)
    |> notes corecN (map single corec_thms)
    |> notes unf_fldN (map single unf_fld_thms)
    |> notes fld_unfN (map single fld_unf_thms)
    |> notes unf_injectN (map single unf_inject_thms)
    |> notes unf_exhaustN (map single unf_exhaust_thms)
    |> notes fld_injectN (map single fld_inject_thms)
    |> notes fld_exhaustN (map single fld_exhaust_thms)
    |> notes fld_coiterN (map single fld_coiter_thms)
    |> note unf_coinductN [unf_coinduct_thm]
    |> note rel_coinductN [rel_coinduct_thm]
    |> note pred_coinductN [pred_coinduct_thm]
    |> note unf_coinduct_uptoN [unf_coinduct_upto_thm]
    |> note rel_coinduct_uptoN [rel_coinduct_upto_thm]
    |> note pred_coinduct_uptoN [pred_coinduct_upto_thm]
  end;

val _ =
  Outer_Syntax.local_theory @{command_spec "codata_raw"} "greatest fixed points for BNF equations"
    (Parse.and_list1
      ((Parse.binding --| Parse.$$$ ":") -- (Parse.typ --| Parse.$$$ "=" -- Parse.typ)) >>
      (fp_bnf_cmd bnf_gfp o apsnd split_list o split_list));

end;
