(*  Title:      HOL/BNF/Tools/bnf_lfp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Datatype construction.
*)

signature BNF_LFP =
sig
  val bnf_lfp: mixfix list -> (string * sort) list option -> binding list ->
    typ list * typ list list -> BNF_Def.BNF list -> local_theory ->
    (term list * term list * term list * term list * term list * thm * thm list * thm list *
      thm list * thm list * thm list) * local_theory
end;

structure BNF_LFP : BNF_LFP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_FP
open BNF_FP_Sugar
open BNF_LFP_Util
open BNF_LFP_Tactics

(*all BNFs have the same lives*)
fun bnf_lfp mixfixes resBs bs (resDs, Dss) bnfs lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val live = live_of_bnf (hd bnfs);
    val n = length bnfs; (*active*)
    val ks = 1 upto n;
    val m = live - n; (*passive, if 0 don't generate a new BNF*)
    val b = Binding.name (mk_common_name (map Binding.name_of bs));

    (* TODO: check if m, n, etc., are sane *)

    val deads = fold (union (op =)) Dss resDs;
    val names_lthy = fold Variable.declare_typ deads lthy;

    (* tvars *)
    val (((((((passiveAs, activeAs), allAs)), (passiveBs, activeBs)),
      activeCs), passiveXs), passiveYs) = names_lthy
      |> mk_TFrees live
      |> apfst (`(chop m))
      ||> mk_TFrees live
      ||>> apfst (chop m)
      ||>> mk_TFrees n
      ||>> mk_TFrees m
      ||> fst o mk_TFrees m;

    val Ass = replicate n allAs;
    val allBs = passiveAs @ activeBs;
    val Bss = replicate n allBs;
    val allCs = passiveAs @ activeCs;
    val allCs' = passiveBs @ activeCs;
    val Css' = replicate n allCs';

    (* typs *)
    val dead_poss =
      (case resBs of
        NONE => map SOME deads @ replicate m NONE
      | SOME Ts => map (fn T => if member (op =) deads (TFree T) then SOME (TFree T) else NONE) Ts);
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
    val sTs = map2 (curry (op -->)) FTsAs activeAs;
    val s'Ts = map2 (curry (op -->)) FTsBs activeBs;
    val s''Ts = map2 (curry (op -->)) FTsCs activeCs;
    val fTs = map2 (curry (op -->)) activeAs activeBs;
    val inv_fTs = map2 (curry (op -->)) activeBs activeAs;
    val self_fTs = map2 (curry (op -->)) activeAs activeAs;
    val gTs = map2 (curry (op -->)) activeBs activeCs;
    val all_gTs = map2 (curry (op -->)) allBs allCs';
    val prodBsAs = map2 (curry HOLogic.mk_prodT) activeBs activeAs;
    val prodFTs = mk_FTs (passiveAs @ prodBsAs);
    val prod_sTs = map2 (curry (op -->)) prodFTs activeAs;

    (* terms *)
    val mapsAsAs = map4 mk_map_of_bnf Dss Ass Ass bnfs;
    val mapsAsBs = map4 mk_map_of_bnf Dss Ass Bss bnfs;
    val mapsBsAs = map4 mk_map_of_bnf Dss Bss Ass bnfs;
    val mapsBsCs' = map4 mk_map_of_bnf Dss Bss Css' bnfs;
    val mapsAsCs' = map4 mk_map_of_bnf Dss Ass Css' bnfs;
    val map_fsts = map4 mk_map_of_bnf Dss (replicate n (passiveAs @ prodBsAs)) Bss bnfs;
    val map_fsts_rev = map4 mk_map_of_bnf Dss Bss (replicate n (passiveAs @ prodBsAs)) bnfs;
    fun mk_setss Ts = map3 mk_sets_of_bnf (map (replicate live) Dss)
      (map (replicate live) (replicate n Ts)) bnfs;
    val setssAs = mk_setss allAs;
    val bds = map3 mk_bd_of_bnf Dss Ass bnfs;
    val witss = map wits_of_bnf bnfs;

    val (((((((((((((((((((zs, zs'), As), Bs), Bs_copy), B's), B''s), ss), prod_ss), s's), s''s),
      fs), fs_copy), inv_fs), self_fs), gs), all_gs), (xFs, xFs')), (yFs, yFs')),
      names_lthy) = lthy
      |> mk_Frees' "z" activeAs
      ||>> mk_Frees "A" ATs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B" BTs
      ||>> mk_Frees "B'" B'Ts
      ||>> mk_Frees "B''" B''Ts
      ||>> mk_Frees "s" sTs
      ||>> mk_Frees "prods" prod_sTs
      ||>> mk_Frees "s'" s'Ts
      ||>> mk_Frees "s''" s''Ts
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "f" inv_fTs
      ||>> mk_Frees "f" self_fTs
      ||>> mk_Frees "g" gTs
      ||>> mk_Frees "g" all_gTs
      ||>> mk_Frees' "x" FTsAs
      ||>> mk_Frees' "y" FTsBs;

    val passive_UNIVs = map HOLogic.mk_UNIV passiveAs;
    val active_UNIVs = map HOLogic.mk_UNIV activeAs;
    val prod_UNIVs = map HOLogic.mk_UNIV prodBsAs;
    val passive_ids = map HOLogic.id_const passiveAs;
    val active_ids = map HOLogic.id_const activeAs;
    val fsts = map fst_const prodBsAs;

    (* thms *)
    val bd_card_orders = map bd_card_order_of_bnf bnfs;
    val bd_Card_orders = map bd_Card_order_of_bnf bnfs;
    val bd_Card_order = hd bd_Card_orders;
    val bd_Cinfinite = bd_Cinfinite_of_bnf (hd bnfs);
    val bd_Cnotzeros = map bd_Cnotzero_of_bnf bnfs;
    val bd_Cnotzero = hd bd_Cnotzeros;
    val in_bds = map in_bd_of_bnf bnfs;
    val map_comp's = map map_comp'_of_bnf bnfs;
    val map_congs = map map_cong_of_bnf bnfs;
    val map_ids = map map_id_of_bnf bnfs;
    val map_id's = map map_id'_of_bnf bnfs;
    val map_wpulls = map map_wpull_of_bnf bnfs;
    val set_bdss = map set_bd_of_bnf bnfs;
    val set_natural'ss = map set_natural'_of_bnf bnfs;

    val timer = time (timer "Extracted terms & thms");

    (* nonemptiness check *)
    fun new_wit X wit = subset (op =) (#I wit, (0 upto m - 1) @ map snd X);

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
      | i :: _ => error ("Cannot define empty datatype " ^ quote (Binding.name_of (nth bs (i - m)))));

    val wit_thms = flat (map2 (fn bnf => fn (j, _) => nth (wit_thmss_of_bnf bnf) j) bnfs reachable);

    val timer = time (timer "Checked nonemptiness");

    (* derived thms *)

    (*map g1 ... gm g(m+1) ... g(m+n) (map id ... id f(m+1) ... f(m+n) x)=
      map g1 ... gm (g(m+1) o f(m+1)) ... (g(m+n) o f(m+n)) x*)
    fun mk_map_comp_id x mapAsBs mapBsCs mapAsCs map_comp =
      let
        val lhs = Term.list_comb (mapBsCs, all_gs) $
          (Term.list_comb (mapAsBs, passive_ids @ fs) $ x);
        val rhs = Term.list_comb (mapAsCs,
          take m all_gs @ map HOLogic.mk_comp (drop m all_gs ~~ fs)) $ x;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (x :: fs @ all_gs) (mk_Trueprop_eq (lhs, rhs)))
          (K (mk_map_comp_id_tac map_comp))
        |> Thm.close_derivation
      end;

    val map_comp_id_thms = map5 mk_map_comp_id xFs mapsAsBs mapsBsCs' mapsAsCs' map_comp's;

    (*forall a : set(m+1) x. f(m+1) a = a; ...; forall a : set(m+n) x. f(m+n) a = a ==>
      map id ... id f(m+1) ... f(m+n) x = x*)
    fun mk_map_congL x mapAsAs sets map_cong map_id' =
      let
        fun mk_prem set f z z' = HOLogic.mk_Trueprop
          (mk_Ball (set $ x) (Term.absfree z' (HOLogic.mk_eq (f $ z, z))));
        val prems = map4 mk_prem (drop m sets) self_fs zs zs';
        val goal = mk_Trueprop_eq (Term.list_comb (mapAsAs, passive_ids @ self_fs) $ x, x);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (x :: self_fs) (Logic.list_implies (prems, goal)))
          (K (mk_map_congL_tac m map_cong map_id'))
        |> Thm.close_derivation
      end;

    val map_congL_thms = map5 mk_map_congL xFs mapsAsAs setssAs map_congs map_id's;
    val in_mono'_thms = map (fn bnf => in_mono_of_bnf bnf OF (replicate m subset_refl)) bnfs
    val in_cong'_thms = map (fn bnf => in_cong_of_bnf bnf OF (replicate m refl)) bnfs

    val timer = time (timer "Derived simple theorems");

    (* algebra *)

    val alg_bind = Binding.suffix_name ("_" ^ algN) b;
    val alg_name = Binding.name_of alg_bind;
    val alg_def_bind = (Thm.def_binding alg_bind, []);

    (*forall i = 1 ... n: (\<forall>x \<in> Fi_in A1 .. Am B1 ... Bn. si x \<in> Bi)*)
    val alg_spec =
      let
        val algT = Library.foldr (op -->) (ATs @ BTs @ sTs, HOLogic.boolT);

        val ins = map3 mk_in (replicate n (As @ Bs)) setssAs FTsAs;
        fun mk_alg_conjunct B s X x x' =
          mk_Ball X (Term.absfree x' (HOLogic.mk_mem (s $ x, B)));

        val lhs = Term.list_comb (Free (alg_name, algT), As @ Bs @ ss);
        val rhs = Library.foldr1 HOLogic.mk_conj (map5 mk_alg_conjunct Bs ss ins xFs xFs')
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((alg_free, (_, alg_def_free)), (lthy, lthy_old)) =
        lthy
        |> Specification.definition (SOME (alg_bind, NONE, NoSyn), (alg_def_bind, alg_spec))
        ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val alg = fst (Term.dest_Const (Morphism.term phi alg_free));
    val alg_def = Morphism.thm phi alg_def_free;

    fun mk_alg As Bs ss =
      let
        val args = As @ Bs @ ss;
        val Ts = map fastype_of args;
        val algT = Library.foldr (op -->) (Ts, HOLogic.boolT);
      in
        Term.list_comb (Const (alg, algT), args)
      end;

    val alg_set_thms =
      let
        val alg_prem = HOLogic.mk_Trueprop (mk_alg As Bs ss);
        fun mk_prem x set B = HOLogic.mk_Trueprop (mk_subset (set $ x) B);
        fun mk_concl s x B = HOLogic.mk_Trueprop (HOLogic.mk_mem (s $ x, B));
        val premss = map2 ((fn x => fn sets =>  map2 (mk_prem x) sets (As @ Bs))) xFs setssAs;
        val concls = map3 mk_concl ss xFs Bs;
        val goals = map3 (fn x => fn prems => fn concl =>
          fold_rev Logic.all (x :: As @ Bs @ ss)
            (Logic.list_implies (alg_prem :: prems, concl))) xFs premss concls;
      in
        map (fn goal =>
          Skip_Proof.prove lthy [] [] goal (K (mk_alg_set_tac alg_def)) |> Thm.close_derivation)
        goals
      end;

    fun mk_talg ATs BTs = mk_alg (map HOLogic.mk_UNIV ATs) (map HOLogic.mk_UNIV BTs);

    val talg_thm =
      let
        val goal = fold_rev Logic.all ss
          (HOLogic.mk_Trueprop (mk_talg passiveAs activeAs ss))
      in
        Skip_Proof.prove lthy [] [] goal
          (K (stac alg_def 1 THEN CONJ_WRAP (K (EVERY' [rtac ballI, rtac UNIV_I] 1)) ss))
        |> Thm.close_derivation
      end;

    val timer = time (timer "Algebra definition & thms");

    val alg_not_empty_thms =
      let
        val alg_prem =
          HOLogic.mk_Trueprop (mk_alg passive_UNIVs Bs ss);
        val concls = map (HOLogic.mk_Trueprop o mk_not_empty) Bs;
        val goals =
          map (fn concl =>
            fold_rev Logic.all (Bs @ ss) (Logic.mk_implies (alg_prem, concl))) concls;
      in
        map2 (fn goal => fn alg_set =>
          Skip_Proof.prove lthy [] []
            goal (K (mk_alg_not_empty_tac alg_set alg_set_thms wit_thms))
          |> Thm.close_derivation)
        goals alg_set_thms
      end;

    val timer = time (timer "Proved nonemptiness");

    (* morphism *)

    val mor_bind = Binding.suffix_name ("_" ^ morN) b;
    val mor_name = Binding.name_of mor_bind;
    val mor_def_bind = (Thm.def_binding mor_bind, []);

    (*fbetw) forall i = 1 ... n: (\<forall>x \<in> Bi. f x \<in> B'i)*)
    (*mor) forall i = 1 ... n: (\<forall>x \<in> Fi_in UNIV ... UNIV B1 ... Bn.
       f (s1 x) = s1' (Fi_map id ... id f1 ... fn x))*)
    val mor_spec =
      let
        val morT = Library.foldr (op -->) (BTs @ sTs @ B'Ts @ s'Ts @ fTs, HOLogic.boolT);

        fun mk_fbetw f B1 B2 z z' =
          mk_Ball B1 (Term.absfree z' (HOLogic.mk_mem (f $ z, B2)));
        fun mk_mor sets mapAsBs f s s' T x x' =
          mk_Ball (mk_in (passive_UNIVs @ Bs) sets T)
            (Term.absfree x' (HOLogic.mk_eq (f $ (s $ x), s' $
              (Term.list_comb (mapAsBs, passive_ids @ fs) $ x))));
        val lhs = Term.list_comb (Free (mor_name, morT), Bs @ ss @ B's @ s's @ fs);
        val rhs = HOLogic.mk_conj
          (Library.foldr1 HOLogic.mk_conj (map5 mk_fbetw fs Bs B's zs zs'),
          Library.foldr1 HOLogic.mk_conj
            (map8 mk_mor setssAs mapsAsBs fs ss s's FTsAs xFs xFs'))
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((mor_free, (_, mor_def_free)), (lthy, lthy_old)) =
        lthy
        |> Specification.definition (SOME (mor_bind, NONE, NoSyn), (mor_def_bind, mor_spec))
        ||> `Local_Theory.restore;

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

    val (mor_image_thms, morE_thms) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor Bs ss B's s's fs);
        fun mk_image_goal f B1 B2 = fold_rev Logic.all (Bs @ ss @ B's @ s's @ fs)
          (Logic.mk_implies (prem, HOLogic.mk_Trueprop (mk_subset (mk_image f $ B1) B2)));
        val image_goals = map3 mk_image_goal fs Bs B's;
        fun mk_elim_prem sets x T = HOLogic.mk_Trueprop
          (HOLogic.mk_mem (x, mk_in (passive_UNIVs @ Bs) sets T));
        fun mk_elim_goal sets mapAsBs f s s' x T =
          fold_rev Logic.all (x :: Bs @ ss @ B's @ s's @ fs)
            (Logic.list_implies ([prem, mk_elim_prem sets x T],
              mk_Trueprop_eq (f $ (s $ x), s' $ Term.list_comb (mapAsBs, passive_ids @ fs @ [x]))));
        val elim_goals = map7 mk_elim_goal setssAs mapsAsBs fs ss s's xFs FTsAs;
        fun prove goal =
          Skip_Proof.prove lthy [] [] goal (K (mk_mor_elim_tac mor_def)) |> Thm.close_derivation;
      in
        (map prove image_goals, map prove elim_goals)
      end;

    val mor_incl_thm =
      let
        val prems = map2 (HOLogic.mk_Trueprop oo mk_subset) Bs Bs_copy;
        val concl = HOLogic.mk_Trueprop (mk_mor Bs ss Bs_copy ss active_ids);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ Bs_copy) (Logic.list_implies (prems, concl)))
          (K (mk_mor_incl_tac mor_def map_id's))
        |> Thm.close_derivation
      end;

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
          (K (mk_mor_comp_tac mor_def set_natural'ss map_comp_id_thms))
        |> Thm.close_derivation
      end;

    val mor_inv_thm =
      let
        fun mk_inv_prem f inv_f B B' = HOLogic.mk_conj (mk_subset (mk_image inv_f $ B') B,
          HOLogic.mk_conj (mk_inver inv_f f B, mk_inver f inv_f B'));
        val prems = map HOLogic.mk_Trueprop
          ([mk_mor Bs ss B's s's fs,
          mk_alg passive_UNIVs Bs ss,
          mk_alg passive_UNIVs B's s's] @
          map4 mk_inv_prem fs inv_fs Bs B's);
        val concl = HOLogic.mk_Trueprop (mk_mor B's s's Bs ss inv_fs);
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ s's @ fs @ inv_fs)
            (Logic.list_implies (prems, concl)))
          (K (mk_mor_inv_tac alg_def mor_def
            set_natural'ss morE_thms map_comp_id_thms map_congL_thms))
        |> Thm.close_derivation
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
        |> Thm.close_derivation
      end;

    val mor_str_thm =
      let
        val maps = map2 (fn Ds => fn bnf => Term.list_comb
          (mk_map_of_bnf Ds (passiveAs @ FTsAs) allAs bnf, passive_ids @ ss)) Dss bnfs;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all ss (HOLogic.mk_Trueprop
            (mk_mor (map HOLogic.mk_UNIV FTsAs) maps active_UNIVs ss ss)))
          (K (mk_mor_str_tac ks mor_def))
        |> Thm.close_derivation
      end;

    val mor_convol_thm =
      let
        val maps = map3 (fn s => fn prod_s => fn mapx =>
          mk_convol (HOLogic.mk_comp (s, Term.list_comb (mapx, passive_ids @ fsts)), prod_s))
          s's prod_ss map_fsts;
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (s's @ prod_ss) (HOLogic.mk_Trueprop
            (mk_mor prod_UNIVs maps (map HOLogic.mk_UNIV activeBs) s's fsts)))
          (K (mk_mor_convol_tac ks mor_def))
        |> Thm.close_derivation
      end;

    val mor_UNIV_thm =
      let
        fun mk_conjunct mapAsBs f s s' = HOLogic.mk_eq
            (HOLogic.mk_comp (f, s),
            HOLogic.mk_comp (s', Term.list_comb (mapAsBs, passive_ids @ fs)));
        val lhs = mk_mor active_UNIVs ss (map HOLogic.mk_UNIV activeBs) s's fs;
        val rhs = Library.foldr1 HOLogic.mk_conj (map4 mk_conjunct mapsAsBs fs ss s's);
      in
        Skip_Proof.prove lthy [] [] (fold_rev Logic.all (ss @ s's @ fs) (mk_Trueprop_eq (lhs, rhs)))
          (K (mk_mor_UNIV_tac m morE_thms mor_def))
        |> Thm.close_derivation
      end;

    val timer = time (timer "Morphism definition & thms");

    (* isomorphism *)

    (*mor Bs1 ss1 Bs2 ss2 fs \<and> (\<exists>gs. mor Bs2 ss2 Bs1 ss1 fs \<and>
       forall i = 1 ... n. (inver gs[i] fs[i] Bs1[i] \<and> inver fs[i] gs[i] Bs2[i]))*)
    fun mk_iso Bs1 ss1 Bs2 ss2 fs gs =
      let
        val ex_inv_mor = list_exists_free gs
          (HOLogic.mk_conj (mk_mor Bs2 ss2 Bs1 ss1 gs,
            Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_conj)
              (map3 mk_inver gs fs Bs1) (map3 mk_inver fs gs Bs2))));
      in
        HOLogic.mk_conj (mk_mor Bs1 ss1 Bs2 ss2 fs, ex_inv_mor)
      end;

    val iso_alt_thm =
      let
        val prems = map HOLogic.mk_Trueprop
         [mk_alg passive_UNIVs Bs ss,
         mk_alg passive_UNIVs B's s's]
        val concl = mk_Trueprop_eq (mk_iso Bs ss B's s's fs inv_fs,
          HOLogic.mk_conj (mk_mor Bs ss B's s's fs,
            Library.foldr1 HOLogic.mk_conj (map3 mk_bij_betw fs Bs B's)));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ s's @ fs) (Logic.list_implies (prems, concl)))
          (K (mk_iso_alt_tac mor_image_thms mor_inv_thm))
        |> Thm.close_derivation
      end;

    val timer = time (timer "Isomorphism definition & thms");

    (* algebra copies *)

    val (copy_alg_thm, ex_copy_alg_thm) =
      let
        val prems = map HOLogic.mk_Trueprop
         (mk_alg passive_UNIVs Bs ss :: map3 mk_bij_betw inv_fs B's Bs);
        val inver_prems = map HOLogic.mk_Trueprop
          (map3 mk_inver inv_fs fs Bs @ map3 mk_inver fs inv_fs B's);
        val all_prems = prems @ inver_prems;
        fun mk_s f s mapT y y' = Term.absfree y' (f $ (s $
          (Term.list_comb (mapT, passive_ids @ inv_fs) $ y)));

        val alg = HOLogic.mk_Trueprop
          (mk_alg passive_UNIVs B's (map5 mk_s fs ss mapsBsAs yFs yFs'));
        val copy_str_thm = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ inv_fs @ fs)
            (Logic.list_implies (all_prems, alg)))
          (K (mk_copy_str_tac set_natural'ss alg_def alg_set_thms))
          |> Thm.close_derivation;

        val iso = HOLogic.mk_Trueprop
          (mk_iso B's (map5 mk_s fs ss mapsBsAs yFs yFs') Bs ss inv_fs fs_copy);
        val copy_alg_thm = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ inv_fs @ fs)
            (Logic.list_implies (all_prems, iso)))
          (K (mk_copy_alg_tac set_natural'ss alg_set_thms mor_def iso_alt_thm copy_str_thm))
          |> Thm.close_derivation;

        val ex = HOLogic.mk_Trueprop
          (list_exists_free s's
            (HOLogic.mk_conj (mk_alg passive_UNIVs B's s's,
              mk_iso B's s's Bs ss inv_fs fs_copy)));
        val ex_copy_alg_thm = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss @ B's @ inv_fs @ fs)
             (Logic.list_implies (prems, ex)))
          (K (mk_ex_copy_alg_tac n copy_str_thm copy_alg_thm))
          |> Thm.close_derivation;
      in
        (copy_alg_thm, ex_copy_alg_thm)
      end;

    val timer = time (timer "Copy thms");


    (* bounds *)

    val sum_Card_order = if n = 1 then bd_Card_order else @{thm Card_order_csum};
    val sum_Cnotzero = if n = 1 then bd_Cnotzero else bd_Cnotzero RS @{thm csum_Cnotzero1};
    val sum_Cinfinite = if n = 1 then bd_Cinfinite else bd_Cinfinite RS @{thm Cinfinite_csum1};
    fun mk_set_bd_sums i bd_Card_order bds =
      if n = 1 then bds
      else map (fn thm => bd_Card_order RS mk_ordLeq_csum n i thm) bds;
    val set_bd_sumss = map3 mk_set_bd_sums ks bd_Card_orders set_bdss;

    fun mk_in_bd_sum i Co Cnz bd =
      if n = 1 then bd
      else Cnz RS ((Co RS mk_ordLeq_csum n i (Co RS @{thm ordLeq_refl})) RS
        (bd RS @{thm ordLeq_transitive[OF _
          cexp_mono2_Cnotzero[OF _ csum_Cnotzero2[OF ctwo_Cnotzero]]]}));
    val in_bd_sums = map4 mk_in_bd_sum ks bd_Card_orders bd_Cnotzeros in_bds;

    val sum_bd = Library.foldr1 (uncurry mk_csum) bds;
    val suc_bd = mk_cardSuc sum_bd;
    val field_suc_bd = mk_Field suc_bd;
    val suc_bdT = fst (dest_relT (fastype_of suc_bd));
    fun mk_Asuc_bd [] = mk_cexp ctwo suc_bd
      | mk_Asuc_bd As =
        mk_cexp (mk_csum (Library.foldr1 (uncurry mk_csum) (map mk_card_of As)) ctwo) suc_bd;

    val suc_bd_Card_order = if n = 1 then bd_Card_order RS @{thm cardSuc_Card_order}
      else @{thm cardSuc_Card_order[OF Card_order_csum]};
    val suc_bd_Cinfinite = if n = 1 then bd_Cinfinite RS @{thm Cinfinite_cardSuc}
      else bd_Cinfinite RS @{thm Cinfinite_cardSuc[OF Cinfinite_csum1]};
    val suc_bd_Cnotzero = suc_bd_Cinfinite RS @{thm Cinfinite_Cnotzero};
    val suc_bd_worel = suc_bd_Card_order RS @{thm Card_order_wo_rel}
    val basis_Asuc = if m = 0 then @{thm ordLeq_refl[OF Card_order_ctwo]}
        else @{thm ordLeq_csum2[OF Card_order_ctwo]};
    val Asuc_bd_Cinfinite = suc_bd_Cinfinite RS (basis_Asuc RS @{thm Cinfinite_cexp});
    val Asuc_bd_Cnotzero = Asuc_bd_Cinfinite RS @{thm Cinfinite_Cnotzero};

    val suc_bd_Asuc_bd = @{thm ordLess_ordLeq_trans[OF
      ordLess_ctwo_cexp
      cexp_mono1_Cnotzero[OF _ ctwo_Cnotzero]]} OF
      [suc_bd_Card_order, basis_Asuc, suc_bd_Card_order];

    val Asuc_bdT = fst (dest_relT (fastype_of (mk_Asuc_bd As)));
    val II_BTs = replicate n (HOLogic.mk_setT Asuc_bdT);
    val II_sTs = map2 (fn Ds => fn bnf =>
      mk_T_of_bnf Ds (passiveAs @ replicate n Asuc_bdT) bnf --> Asuc_bdT) Dss bnfs;

    val (((((((idxs, Asi_name), (idx, idx')), (jdx, jdx')), II_Bs), II_ss), Asuc_fs),
      names_lthy) = names_lthy
      |> mk_Frees "i" (replicate n suc_bdT)
      ||>> (fn ctxt => apfst the_single (mk_fresh_names ctxt 1 "Asi"))
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "i") suc_bdT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "j") suc_bdT
      ||>> mk_Frees "IIB" II_BTs
      ||>> mk_Frees "IIs" II_sTs
      ||>> mk_Frees "f" (map (fn T => Asuc_bdT --> T) activeAs);

    val suc_bd_limit_thm =
      let
        val prem = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map (fn idx => HOLogic.mk_mem (idx, field_suc_bd)) idxs));
        fun mk_conjunct idx = HOLogic.mk_conj (mk_not_eq idx jdx,
          HOLogic.mk_mem (HOLogic.mk_prod (idx, jdx), suc_bd));
        val concl = HOLogic.mk_Trueprop (mk_Bex field_suc_bd
          (Term.absfree jdx' (Library.foldr1 HOLogic.mk_conj (map mk_conjunct idxs))));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all idxs (Logic.list_implies ([prem], concl)))
          (K (mk_bd_limit_tac n suc_bd_Cinfinite))
        |> Thm.close_derivation
      end;

    val timer = time (timer "Bounds");


    (* minimal algebra *)

    fun mk_minG Asi i k = mk_UNION (mk_underS suc_bd $ i)
      (Term.absfree jdx' (mk_nthN n (Asi $ jdx) k));

    fun mk_minH_component As Asi i sets Ts s k =
      HOLogic.mk_binop @{const_name "sup"}
      (mk_minG Asi i k, mk_image s $ mk_in (As @ map (mk_minG Asi i) ks) sets Ts);

    fun mk_min_algs As ss =
      let
        val BTs = map (range_type o fastype_of) ss;
        val Ts = map (HOLogic.dest_setT o fastype_of) As @ BTs;
        val (Asi, Asi') = `Free (Asi_name, suc_bdT -->
          Library.foldr1 HOLogic.mk_prodT (map HOLogic.mk_setT BTs));
      in
         mk_worec suc_bd (Term.absfree Asi' (Term.absfree idx' (HOLogic.mk_tuple
           (map4 (mk_minH_component As Asi idx) (mk_setss Ts) (mk_FTs Ts) ss ks))))
      end;

    val (min_algs_thms, min_algs_mono_thms, card_of_min_algs_thm, least_min_algs_thm) =
      let
        val i_field = HOLogic.mk_mem (idx, field_suc_bd);
        val min_algs = mk_min_algs As ss;
        val min_algss = map (fn k => mk_nthN n (min_algs $ idx) k) ks;

        val concl = HOLogic.mk_Trueprop
          (HOLogic.mk_eq (min_algs $ idx, HOLogic.mk_tuple
            (map4 (mk_minH_component As min_algs idx) setssAs FTsAs ss ks)));
        val goal = fold_rev Logic.all (idx :: As @ ss)
          (Logic.mk_implies (HOLogic.mk_Trueprop i_field, concl));

        val min_algs_thm = Skip_Proof.prove lthy [] [] goal
          (K (mk_min_algs_tac suc_bd_worel in_cong'_thms))
          |> Thm.close_derivation;

        val min_algs_thms = map (fn k => min_algs_thm RS mk_nthI n k) ks;

        fun mk_mono_goal min_alg =
          fold_rev Logic.all (As @ ss) (HOLogic.mk_Trueprop (mk_relChain suc_bd
            (Term.absfree idx' min_alg)));

        val monos =
          map2 (fn goal => fn min_algs =>
            Skip_Proof.prove lthy [] [] goal (K (mk_min_algs_mono_tac min_algs))
            |> Thm.close_derivation)
          (map mk_mono_goal min_algss) min_algs_thms;

        val Asuc_bd = mk_Asuc_bd As;

        fun mk_card_conjunct min_alg = mk_ordLeq (mk_card_of min_alg) Asuc_bd;
        val card_conjunction = Library.foldr1 HOLogic.mk_conj (map mk_card_conjunct min_algss);
        val card_cT = certifyT lthy suc_bdT;
        val card_ct = certify lthy (Term.absfree idx' card_conjunction);

        val card_of = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] []
            (HOLogic.mk_Trueprop (HOLogic.mk_imp (i_field, card_conjunction)))
            (K (mk_min_algs_card_of_tac card_cT card_ct
              m suc_bd_worel min_algs_thms in_bd_sums
              sum_Card_order sum_Cnotzero suc_bd_Card_order suc_bd_Cinfinite suc_bd_Cnotzero
              suc_bd_Asuc_bd Asuc_bd_Cinfinite Asuc_bd_Cnotzero)))
          |> Thm.close_derivation;

        val least_prem = HOLogic.mk_Trueprop (mk_alg As Bs ss);
        val least_conjunction = Library.foldr1 HOLogic.mk_conj (map2 mk_subset min_algss Bs);
        val least_cT = certifyT lthy suc_bdT;
        val least_ct = certify lthy (Term.absfree idx' least_conjunction);

        val least = singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] []
            (Logic.mk_implies (least_prem,
              HOLogic.mk_Trueprop (HOLogic.mk_imp (i_field, least_conjunction))))
            (K (mk_min_algs_least_tac least_cT least_ct
              suc_bd_worel min_algs_thms alg_set_thms)))
          |> Thm.close_derivation;
      in
        (min_algs_thms, monos, card_of, least)
      end;

    val timer = time (timer "min_algs definition & thms");

    fun min_alg_bind i = Binding.suffix_name
      ("_" ^ min_algN ^ (if n = 1 then "" else string_of_int i)) b;
    val min_alg_name = Binding.name_of o min_alg_bind;
    val min_alg_def_bind = rpair [] o Thm.def_binding o min_alg_bind;

    fun min_alg_spec i =
      let
        val min_algT =
          Library.foldr (op -->) (ATs @ sTs, HOLogic.mk_setT (nth activeAs (i - 1)));

        val lhs = Term.list_comb (Free (min_alg_name i, min_algT), As @ ss);
        val rhs = mk_UNION (field_suc_bd)
          (Term.absfree idx' (mk_nthN n (mk_min_algs As ss $ idx) i));
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((min_alg_frees, (_, min_alg_def_frees)), (lthy, lthy_old)) =
        lthy
        |> fold_map (fn i => Specification.definition
          (SOME (min_alg_bind i, NONE, NoSyn), (min_alg_def_bind i, min_alg_spec i))) ks
        |>> apsnd split_list o split_list
        ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val min_algs = map (fst o Term.dest_Const o Morphism.term phi) min_alg_frees;
    val min_alg_defs = map (Morphism.thm phi) min_alg_def_frees;

    fun mk_min_alg As ss i =
      let
        val T = HOLogic.mk_setT (range_type (fastype_of (nth ss (i - 1))))
        val args = As @ ss;
        val Ts = map fastype_of args;
        val min_algT = Library.foldr (op -->) (Ts, T);
      in
        Term.list_comb (Const (nth min_algs (i - 1), min_algT), args)
      end;

    val (alg_min_alg_thm, card_of_min_alg_thms, least_min_alg_thms, mor_incl_min_alg_thm) =
      let
        val min_algs = map (mk_min_alg As ss) ks;

        val goal = fold_rev Logic.all (As @ ss) (HOLogic.mk_Trueprop (mk_alg As min_algs ss));
        val alg_min_alg = Skip_Proof.prove lthy [] [] goal
          (K (mk_alg_min_alg_tac m alg_def min_alg_defs suc_bd_limit_thm sum_Cinfinite
            set_bd_sumss min_algs_thms min_algs_mono_thms))
          |> Thm.close_derivation;

        val Asuc_bd = mk_Asuc_bd As;
        fun mk_card_of_thm min_alg def = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (As @ ss)
            (HOLogic.mk_Trueprop (mk_ordLeq (mk_card_of min_alg) Asuc_bd)))
          (K (mk_card_of_min_alg_tac def card_of_min_algs_thm
            suc_bd_Card_order suc_bd_Asuc_bd Asuc_bd_Cinfinite))
          |> Thm.close_derivation;

        val least_prem = HOLogic.mk_Trueprop (mk_alg As Bs ss);
        fun mk_least_thm min_alg B def = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (As @ Bs @ ss)
            (Logic.mk_implies (least_prem, HOLogic.mk_Trueprop (mk_subset min_alg B))))
          (K (mk_least_min_alg_tac def least_min_algs_thm))
          |> Thm.close_derivation;

        val leasts = map3 mk_least_thm min_algs Bs min_alg_defs;

        val incl_prem = HOLogic.mk_Trueprop (mk_alg passive_UNIVs Bs ss);
        val incl_min_algs = map (mk_min_alg passive_UNIVs ss) ks;
        val incl = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss)
            (Logic.mk_implies (incl_prem,
              HOLogic.mk_Trueprop (mk_mor incl_min_algs ss Bs ss active_ids))))
          (K (EVERY' (rtac mor_incl_thm :: map etac leasts) 1))
          |> Thm.close_derivation;
      in
        (alg_min_alg, map2 mk_card_of_thm min_algs min_alg_defs, leasts, incl)
      end;

    val timer = time (timer "Minimal algebra definition & thms");

    val II_repT = HOLogic.mk_prodT (HOLogic.mk_tupleT II_BTs, HOLogic.mk_tupleT II_sTs);
    val IIT_bind = Binding.suffix_name ("_" ^ IITN) b;

    val ((IIT_name, (IIT_glob_info, IIT_loc_info)), lthy) =
      typedef false NONE (IIT_bind, params, NoSyn)
        (HOLogic.mk_UNIV II_repT) NONE (EVERY' [rtac exI, rtac UNIV_I] 1) lthy;

    val IIT = Type (IIT_name, params');
    val Abs_IIT = Const (#Abs_name IIT_glob_info, II_repT --> IIT);
    val Rep_IIT = Const (#Rep_name IIT_glob_info, IIT --> II_repT);
    val Abs_IIT_inverse_thm = UNIV_I RS #Abs_inverse IIT_loc_info;

    val initT = IIT --> Asuc_bdT;
    val active_initTs = replicate n initT;
    val init_FTs = map2 (fn Ds => mk_T_of_bnf Ds (passiveAs @ active_initTs)) Dss bnfs;
    val init_fTs = map (fn T => initT --> T) activeAs;

    val (((((((iidx, iidx'), init_xs), (init_xFs, init_xFs')),
      init_fs), init_fs_copy), init_phis), names_lthy) = names_lthy
      |> yield_singleton (apfst (op ~~) oo mk_Frees' "i") IIT
      ||>> mk_Frees "ix" active_initTs
      ||>> mk_Frees' "x" init_FTs
      ||>> mk_Frees "f" init_fTs
      ||>> mk_Frees "f" init_fTs
      ||>> mk_Frees "P" (replicate n (mk_pred1T initT));

    val II = HOLogic.mk_Collect (fst iidx', IIT, list_exists_free (II_Bs @ II_ss)
      (HOLogic.mk_conj (HOLogic.mk_eq (iidx,
        Abs_IIT $ (HOLogic.mk_prod (HOLogic.mk_tuple II_Bs, HOLogic.mk_tuple II_ss))),
        mk_alg passive_UNIVs II_Bs II_ss)));

    val select_Bs = map (mk_nthN n (HOLogic.mk_fst (Rep_IIT $ iidx))) ks;
    val select_ss = map (mk_nthN n (HOLogic.mk_snd (Rep_IIT $ iidx))) ks;

    fun str_init_bind i = Binding.suffix_name ("_" ^ str_initN ^ (if n = 1 then "" else
      string_of_int i)) b;
    val str_init_name = Binding.name_of o str_init_bind;
    val str_init_def_bind = rpair [] o Thm.def_binding o str_init_bind;

    fun str_init_spec i =
      let
        val T = nth init_FTs (i - 1);
        val init_xF = nth init_xFs (i - 1)
        val select_s = nth select_ss (i - 1);
        val map = mk_map_of_bnf (nth Dss (i - 1))
          (passiveAs @ active_initTs) (passiveAs @ replicate n Asuc_bdT)
          (nth bnfs (i - 1));
        val map_args = passive_ids @ replicate n (mk_rapp iidx Asuc_bdT);
        val str_initT = T --> IIT --> Asuc_bdT;

        val lhs = Term.list_comb (Free (str_init_name i, str_initT), [init_xF, iidx]);
        val rhs = select_s $ (Term.list_comb (map, map_args) $ init_xF);
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((str_init_frees, (_, str_init_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map (fn i => Specification.definition
        (SOME (str_init_bind i, NONE, NoSyn), (str_init_def_bind i, str_init_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val str_inits =
      map (Term.subst_atomic_types (map (`(Morphism.typ phi)) params') o Morphism.term phi)
        str_init_frees;

    val str_init_defs = map (Morphism.thm phi) str_init_def_frees;

    val car_inits = map (mk_min_alg passive_UNIVs str_inits) ks;

    (*TODO: replace with instantiate? (problem: figure out right type instantiation)*)
    val alg_init_thm = Skip_Proof.prove lthy [] []
      (HOLogic.mk_Trueprop (mk_alg passive_UNIVs car_inits str_inits))
      (K (rtac alg_min_alg_thm 1))
      |> Thm.close_derivation;

    val alg_select_thm = Skip_Proof.prove lthy [] []
      (HOLogic.mk_Trueprop (mk_Ball II
        (Term.absfree iidx' (mk_alg passive_UNIVs select_Bs select_ss))))
      (mk_alg_select_tac Abs_IIT_inverse_thm)
      |> Thm.close_derivation;

    val mor_select_thm =
      let
        val alg_prem = HOLogic.mk_Trueprop (mk_alg passive_UNIVs Bs ss);
        val i_prem = HOLogic.mk_Trueprop (HOLogic.mk_mem (iidx, II));
        val mor_prem = HOLogic.mk_Trueprop (mk_mor select_Bs select_ss Bs ss Asuc_fs);
        val prems = [alg_prem, i_prem, mor_prem];
        val concl = HOLogic.mk_Trueprop
          (mk_mor car_inits str_inits Bs ss
            (map (fn f => HOLogic.mk_comp (f, mk_rapp iidx Asuc_bdT)) Asuc_fs));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (iidx :: Bs @ ss @ Asuc_fs) (Logic.list_implies (prems, concl)))
          (K (mk_mor_select_tac mor_def mor_cong_thm mor_comp_thm mor_incl_min_alg_thm alg_def
            alg_select_thm alg_set_thms set_natural'ss str_init_defs))
        |> Thm.close_derivation
      end;

    val (init_ex_mor_thm, init_unique_mor_thms) =
      let
        val prem = HOLogic.mk_Trueprop (mk_alg passive_UNIVs Bs ss);
        val concl = HOLogic.mk_Trueprop
          (list_exists_free init_fs (mk_mor car_inits str_inits Bs ss init_fs));
        val ex_mor = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (Bs @ ss) (Logic.mk_implies (prem, concl)))
          (mk_init_ex_mor_tac Abs_IIT_inverse_thm ex_copy_alg_thm alg_min_alg_thm
            card_of_min_alg_thms mor_comp_thm mor_select_thm mor_incl_min_alg_thm)
          |> Thm.close_derivation;

        val prems = map2 (HOLogic.mk_Trueprop oo curry HOLogic.mk_mem) init_xs car_inits
        val mor_prems = map HOLogic.mk_Trueprop
          [mk_mor car_inits str_inits Bs ss init_fs,
          mk_mor car_inits str_inits Bs ss init_fs_copy];
        fun mk_fun_eq f g x = HOLogic.mk_eq (f $ x, g $ x);
        val unique = HOLogic.mk_Trueprop
          (Library.foldr1 HOLogic.mk_conj (map3 mk_fun_eq init_fs init_fs_copy init_xs));
        val unique_mor = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (init_xs @ Bs @ ss @ init_fs @ init_fs_copy)
            (Logic.list_implies (prems @ mor_prems, unique)))
          (K (mk_init_unique_mor_tac m alg_def alg_init_thm least_min_alg_thms
            in_mono'_thms alg_set_thms morE_thms map_congs))
          |> Thm.close_derivation;
      in
        (ex_mor, split_conj_thm unique_mor)
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
          (map6 mk_conjunct phis str_inits active_init_setss init_ins init_xFs init_xFs')
      end;

    val init_induct_thm =
      let
        val prem = HOLogic.mk_Trueprop (mk_closed init_phis);
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map2 mk_Ball car_inits init_phis));
      in
        Skip_Proof.prove lthy [] []
          (fold_rev Logic.all init_phis (Logic.mk_implies (prem, concl)))
          (K (mk_init_induct_tac m alg_def alg_init_thm least_min_alg_thms alg_set_thms))
        |> Thm.close_derivation
      end;

    val timer = time (timer "Initiality definition & thms");

    val ((T_names, (T_glob_infos, T_loc_infos)), lthy) =
      lthy
      |> fold_map3 (fn b => fn mx => fn car_init => typedef false NONE (b, params, mx) car_init NONE
          (EVERY' [rtac ssubst, rtac @{thm ex_in_conv}, resolve_tac alg_not_empty_thms,
            rtac alg_init_thm] 1)) bs mixfixes car_inits
      |>> apsnd split_list o split_list;

    val Ts = map (fn name => Type (name, params')) T_names;
    fun mk_Ts passive = map (Term.typ_subst_atomic (passiveAs ~~ passive)) Ts;
    val Ts' = mk_Ts passiveBs;
    val Rep_Ts = map2 (fn info => fn T => Const (#Rep_name info, T --> initT)) T_glob_infos Ts;
    val Abs_Ts = map2 (fn info => fn T => Const (#Abs_name info, initT --> T)) T_glob_infos Ts;

    val type_defs = map #type_definition T_loc_infos;
    val Reps = map #Rep T_loc_infos;
    val Rep_casess = map #Rep_cases T_loc_infos;
    val Rep_injects = map #Rep_inject T_loc_infos;
    val Rep_inverses = map #Rep_inverse T_loc_infos;
    val Abs_inverses = map #Abs_inverse T_loc_infos;

    fun mk_inver_thm mk_tac rep abs X thm =
      Skip_Proof.prove lthy [] []
        (HOLogic.mk_Trueprop (mk_inver rep abs X))
        (K (EVERY' [rtac ssubst, rtac @{thm inver_def}, rtac ballI, mk_tac thm] 1))
      |> Thm.close_derivation;

    val inver_Reps = map4 (mk_inver_thm rtac) Abs_Ts Rep_Ts (map HOLogic.mk_UNIV Ts) Rep_inverses;
    val inver_Abss = map4 (mk_inver_thm etac) Rep_Ts Abs_Ts car_inits Abs_inverses;

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
    val rec_sTs = map (Term.typ_subst_atomic (activeBs ~~ Ts)) prod_sTs;
    val rec_maps = map (Term.subst_atomic_types (activeBs ~~ Ts)) map_fsts;
    val rec_maps_rev = map (Term.subst_atomic_types (activeBs ~~ Ts)) map_fsts_rev;
    val rec_fsts = map (Term.subst_atomic_types (activeBs ~~ Ts)) fsts;

    val (((((((((Izs1, Izs1'), (Izs2, Izs2')), (xFs, xFs')), yFs), (AFss, AFss')),
      (fold_f, fold_f')), fs), rec_ss), names_lthy) = names_lthy
      |> mk_Frees' "z1" Ts
      ||>> mk_Frees' "z2" Ts'
      ||>> mk_Frees' "x" FTs
      ||>> mk_Frees "y" FTs'
      ||>> mk_Freess' "z" setFTss
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "f") foldT
      ||>> mk_Frees "f" fTs
      ||>> mk_Frees "s" rec_sTs;

    val Izs = map2 retype_free Ts zs;
    val phis = map2 retype_free (map mk_pred1T Ts) init_phis;
    val phi2s = map2 retype_free (map2 mk_pred2T Ts Ts') init_phis;

    fun ctor_bind i = Binding.suffix_name ("_" ^ ctorN) (nth bs (i - 1));
    val ctor_name = Binding.name_of o ctor_bind;
    val ctor_def_bind = rpair [] o Thm.def_binding o ctor_bind;

    fun ctor_spec i abs str map_FT_init x x' =
      let
        val ctorT = nth FTs (i - 1) --> nth Ts (i - 1);

        val lhs = Free (ctor_name i, ctorT);
        val rhs = Term.absfree x' (abs $ (str $
          (Term.list_comb (map_FT_init, map HOLogic.id_const passiveAs @ Rep_Ts) $ x)));
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((ctor_frees, (_, ctor_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map6 (fn i => fn abs => fn str => fn mapx => fn x => fn x' =>
        Specification.definition
          (SOME (ctor_bind i, NONE, NoSyn), (ctor_def_bind i, ctor_spec i abs str mapx x x')))
          ks Abs_Ts str_inits map_FT_inits xFs xFs'
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_ctors passive =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ (mk_params passive)) o
        Morphism.term phi) ctor_frees;
    val ctors = mk_ctors passiveAs;
    val ctor's = mk_ctors passiveBs;
    val ctor_defs = map (Morphism.thm phi) ctor_def_frees;

    val (mor_Rep_thm, mor_Abs_thm) =
      let
        val copy = alg_init_thm RS copy_alg_thm;
        fun mk_bij inj Rep cases = @{thm bij_betwI'} OF [inj, Rep, cases];
        val bijs = map3 mk_bij Rep_injects Reps Rep_casess;
        val mor_Rep =
          Skip_Proof.prove lthy [] []
            (HOLogic.mk_Trueprop (mk_mor UNIVs ctors car_inits str_inits Rep_Ts))
            (mk_mor_Rep_tac ctor_defs copy bijs inver_Abss inver_Reps)
          |> Thm.close_derivation;

        val inv = mor_inv_thm OF [mor_Rep, talg_thm, alg_init_thm];
        val mor_Abs =
          Skip_Proof.prove lthy [] []
            (HOLogic.mk_Trueprop (mk_mor car_inits str_inits UNIVs ctors Abs_Ts))
            (K (mk_mor_Abs_tac inv inver_Abss inver_Reps))
          |> Thm.close_derivation;
      in
        (mor_Rep, mor_Abs)
      end;

    val timer = time (timer "ctor definitions & thms");

    val fold_fun = Term.absfree fold_f'
      (mk_mor UNIVs ctors active_UNIVs ss (map (mk_nthN n fold_f) ks));
    val foldx = HOLogic.choice_const foldT $ fold_fun;

    fun fold_bind i = Binding.suffix_name ("_" ^ ctor_foldN) (nth bs (i - 1));
    val fold_name = Binding.name_of o fold_bind;
    val fold_def_bind = rpair [] o Thm.def_binding o fold_bind;

    fun fold_spec i T AT =
      let
        val foldT = Library.foldr (op -->) (sTs, T --> AT);

        val lhs = Term.list_comb (Free (fold_name i, foldT), ss);
        val rhs = mk_nthN n foldx i;
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((fold_frees, (_, fold_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map3 (fn i => fn T => fn AT =>
        Specification.definition
          (SOME (fold_bind i, NONE, NoSyn), (fold_def_bind i, fold_spec i T AT)))
          ks Ts activeAs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val folds = map (Morphism.term phi) fold_frees;
    val fold_names = map (fst o dest_Const) folds;
    fun mk_fold Ts ss i = Term.list_comb (Const (nth fold_names (i - 1), Library.foldr (op -->)
      (map fastype_of ss, nth Ts (i - 1) --> range_type (fastype_of (nth ss (i - 1))))), ss);
    val fold_defs = map (Morphism.thm phi) fold_def_frees;

    val mor_fold_thm =
      let
        val ex_mor = talg_thm RS init_ex_mor_thm;
        val mor_cong = mor_cong_thm OF (map (mk_nth_conv n) ks);
        val mor_comp = mor_Rep_thm RS mor_comp_thm;
        val cT = certifyT lthy foldT;
        val ct = certify lthy fold_fun
      in
        singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] []
            (HOLogic.mk_Trueprop (mk_mor UNIVs ctors active_UNIVs ss (map (mk_fold Ts ss) ks)))
            (K (mk_mor_fold_tac cT ct fold_defs ex_mor (mor_comp RS mor_cong))))
        |> Thm.close_derivation
      end;

    val ctor_fold_thms = map (fn morE => rule_by_tactic lthy
      ((rtac CollectI THEN' CONJ_WRAP' (K (rtac @{thm subset_UNIV})) (1 upto m + n)) 1)
      (mor_fold_thm RS morE)) morE_thms;

    val (fold_unique_mor_thms, fold_unique_mor_thm) =
      let
        val prem = HOLogic.mk_Trueprop (mk_mor UNIVs ctors active_UNIVs ss fs);
        fun mk_fun_eq f i = HOLogic.mk_eq (f, mk_fold Ts ss i);
        val unique = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_fun_eq fs ks));
        val unique_mor = Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (ss @ fs) (Logic.mk_implies (prem, unique)))
          (K (mk_fold_unique_mor_tac type_defs init_unique_mor_thms Reps
            mor_comp_thm mor_Abs_thm mor_fold_thm))
          |> Thm.close_derivation;
      in
        `split_conj_thm unique_mor
      end;

    val ctor_fold_unique_thms =
      split_conj_thm (mk_conjIN n RS
        (mor_UNIV_thm RS @{thm ssubst[of _ _ "%x. x"]} RS fold_unique_mor_thm))

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

    fun dtor_bind i = Binding.suffix_name ("_" ^ dtorN) (nth bs (i - 1));
    val dtor_name = Binding.name_of o dtor_bind;
    val dtor_def_bind = rpair [] o Thm.def_binding o dtor_bind;

    fun dtor_spec i FT T =
      let
        val dtorT = T --> FT;

        val lhs = Free (dtor_name i, dtorT);
        val rhs = mk_fold Ts map_ctors i;
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((dtor_frees, (_, dtor_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map3 (fn i => fn FT => fn T =>
        Specification.definition
          (SOME (dtor_bind i, NONE, NoSyn), (dtor_def_bind i, dtor_spec i FT T))) ks FTs Ts
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    fun mk_dtors params =
      map (Term.subst_atomic_types (map (Morphism.typ phi) params' ~~ params) o Morphism.term phi)
        dtor_frees;
    val dtors = mk_dtors params';
    val dtor_defs = map (Morphism.thm phi) dtor_def_frees;

    val ctor_o_dtor_thms = map2 (fold_thms lthy o single) dtor_defs ctor_o_fold_thms;

    val dtor_o_ctor_thms =
      let
        fun mk_goal dtor ctor FT =
          mk_Trueprop_eq (HOLogic.mk_comp (dtor, ctor), HOLogic.id_const FT);
        val goals = map3 mk_goal dtors ctors FTs;
      in
        map5 (fn goal => fn dtor_def => fn foldx => fn map_comp_id => fn map_congL =>
          Skip_Proof.prove lthy [] [] goal
            (K (mk_dtor_o_ctor_tac dtor_def foldx map_comp_id map_congL ctor_o_fold_thms))
          |> Thm.close_derivation)
        goals dtor_defs ctor_fold_thms map_comp_id_thms map_congL_thms
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

    val fst_rec_pair_thms =
      let
        val mor = mor_comp_thm OF [mor_fold_thm, mor_convol_thm];
      in
        map2 (fn unique => fn fold_ctor =>
          trans OF [mor RS unique, fold_ctor]) fold_unique_mor_thms fold_ctor_thms
      end;

    fun rec_bind i = Binding.suffix_name ("_" ^ ctor_recN) (nth bs (i - 1));
    val rec_name = Binding.name_of o rec_bind;
    val rec_def_bind = rpair [] o Thm.def_binding o rec_bind;

    fun rec_spec i T AT =
      let
        val recT = Library.foldr (op -->) (rec_sTs, T --> AT);
        val maps = map3 (fn ctor => fn prod_s => fn mapx =>
          mk_convol (HOLogic.mk_comp (ctor, Term.list_comb (mapx, passive_ids @ rec_fsts)), prod_s))
          ctors rec_ss rec_maps;

        val lhs = Term.list_comb (Free (rec_name i, recT), rec_ss);
        val rhs = HOLogic.mk_comp (snd_const (HOLogic.mk_prodT (T, AT)), mk_fold Ts maps i);
      in
        mk_Trueprop_eq (lhs, rhs)
      end;

    val ((rec_frees, (_, rec_def_frees)), (lthy, lthy_old)) =
      lthy
      |> fold_map3 (fn i => fn T => fn AT =>
        Specification.definition
          (SOME (rec_bind i, NONE, NoSyn), (rec_def_bind i, rec_spec i T AT)))
          ks Ts activeAs
      |>> apsnd split_list o split_list
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val recs = map (Morphism.term phi) rec_frees;
    val rec_names = map (fst o dest_Const) recs;
    fun mk_rec ss i = Term.list_comb (Const (nth rec_names (i - 1), Library.foldr (op -->)
      (map fastype_of ss, nth Ts (i - 1) --> range_type (fastype_of (nth ss (i - 1))))), ss);
    val rec_defs = map (Morphism.thm phi) rec_def_frees;

    val convols = map2 (fn T => fn i => mk_convol (HOLogic.id_const T, mk_rec rec_ss i)) Ts ks;
    val ctor_rec_thms =
      let
        fun mk_goal i rec_s rec_map ctor x =
          let
            val lhs = mk_rec rec_ss i $ (ctor $ x);
            val rhs = rec_s $ (Term.list_comb (rec_map, passive_ids @ convols) $ x);
          in
            fold_rev Logic.all (x :: rec_ss) (mk_Trueprop_eq (lhs, rhs))
          end;
        val goals = map5 mk_goal ks rec_ss rec_maps_rev ctors xFs;
      in
        map2 (fn goal => fn foldx =>
          Skip_Proof.prove lthy [] [] goal (mk_rec_tac rec_defs foldx fst_rec_pair_thms)
          |> Thm.close_derivation)
        goals ctor_fold_thms
      end;

    val timer = time (timer "rec definitions & thms");

    val (ctor_induct_thm, induct_params) =
      let
        fun mk_prem phi ctor sets x =
          let
            fun mk_IH phi set z =
              let
                val prem = HOLogic.mk_Trueprop (HOLogic.mk_mem (z, set $ x));
                val concl = HOLogic.mk_Trueprop (phi $ z);
              in
                Logic.all z (Logic.mk_implies (prem, concl))
              end;

            val IHs = map3 mk_IH phis (drop m sets) Izs;
            val concl = HOLogic.mk_Trueprop (phi $ (ctor $ x));
          in
            Logic.all x (Logic.list_implies (IHs, concl))
          end;

        val prems = map4 mk_prem phis ctors FTs_setss xFs;

        fun mk_concl phi z = phi $ z;
        val concl =
          HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_concl phis Izs));

        val goal = Logic.list_implies (prems, concl);
      in
        (Skip_Proof.prove lthy [] []
          (fold_rev Logic.all (phis @ Izs) goal)
          (K (mk_ctor_induct_tac m set_natural'ss init_induct_thm morE_thms mor_Abs_thm
            Rep_inverses Abs_inverses Reps))
        |> Thm.close_derivation,
        rev (Term.add_tfrees goal []))
      end;

    val cTs = map (SOME o certifyT lthy o TFree) induct_params;

    val weak_ctor_induct_thms =
      let fun insts i = (replicate (i - 1) TrueI) @ (@{thm asm_rl} :: replicate (n - i) TrueI);
      in map (fn i => (ctor_induct_thm OF insts i) RS mk_conjunctN n i) ks end;

    val (ctor_induct2_thm, induct2_params) =
      let
        fun mk_prem phi ctor ctor' sets sets' x y =
          let
            fun mk_IH phi set set' z1 z2 =
              let
                val prem1 = HOLogic.mk_Trueprop (HOLogic.mk_mem (z1, (set $ x)));
                val prem2 = HOLogic.mk_Trueprop (HOLogic.mk_mem (z2, (set' $ y)));
                val concl = HOLogic.mk_Trueprop (phi $ z1 $ z2);
              in
                fold_rev Logic.all [z1, z2] (Logic.list_implies ([prem1, prem2], concl))
              end;

            val IHs = map5 mk_IH phi2s (drop m sets) (drop m sets') Izs1 Izs2;
            val concl = HOLogic.mk_Trueprop (phi $ (ctor $ x) $ (ctor' $ y));
          in
            fold_rev Logic.all [x, y] (Logic.list_implies (IHs, concl))
          end;

        val prems = map7 mk_prem phi2s ctors ctor's FTs_setss FTs'_setss xFs yFs;

        fun mk_concl phi z1 z2 = phi $ z1 $ z2;
        val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
          (map3 mk_concl phi2s Izs1 Izs2));
        fun mk_t phi (z1, z1') (z2, z2') =
          Term.absfree z1' (HOLogic.mk_all (fst z2', snd z2', phi $ z1 $ z2));
        val cts = map3 (SOME o certify lthy ooo mk_t) phi2s (Izs1 ~~ Izs1') (Izs2 ~~ Izs2');
        val goal = Logic.list_implies (prems, concl);
      in
        (singleton (Proof_Context.export names_lthy lthy)
          (Skip_Proof.prove lthy [] [] goal
            (mk_ctor_induct2_tac cTs cts ctor_induct_thm weak_ctor_induct_thms))
          |> Thm.close_derivation,
        rev (Term.add_tfrees goal []))
      end;

    val timer = time (timer "induction");

    (*register new datatypes as BNFs*)
    val (Irels, lthy) = if m = 0 then ([], lthy) else
      let
        val fTs = map2 (curry op -->) passiveAs passiveBs;
        val f1Ts = map2 (curry op -->) passiveAs passiveYs;
        val f2Ts = map2 (curry op -->) passiveBs passiveYs;
        val p1Ts = map2 (curry op -->) passiveXs passiveAs;
        val p2Ts = map2 (curry op -->) passiveXs passiveBs;
        val uTs = map2 (curry op -->) Ts Ts';
        val B1Ts = map HOLogic.mk_setT passiveAs;
        val B2Ts = map HOLogic.mk_setT passiveBs;
        val AXTs = map HOLogic.mk_setT passiveXs;
        val XTs = mk_Ts passiveXs;
        val YTs = mk_Ts passiveYs;
        val IRTs = map2 (curry mk_relT) passiveAs passiveBs;
        val IphiTs = map2 mk_pred2T passiveAs passiveBs;

        val (((((((((((((((fs, fs'), fs_copy), us),
          B1s), B2s), AXs), (xs, xs')), f1s), f2s), p1s), p2s), (ys, ys')), IRs), Iphis),
          names_lthy) = names_lthy
          |> mk_Frees' "f" fTs
          ||>> mk_Frees "f" fTs
          ||>> mk_Frees "u" uTs
          ||>> mk_Frees "B1" B1Ts
          ||>> mk_Frees "B2" B2Ts
          ||>> mk_Frees "A" AXTs
          ||>> mk_Frees' "x" XTs
          ||>> mk_Frees "f1" f1Ts
          ||>> mk_Frees "f2" f2Ts
          ||>> mk_Frees "p1" p1Ts
          ||>> mk_Frees "p2" p2Ts
          ||>> mk_Frees' "y" passiveAs
          ||>> mk_Frees "S" IRTs
          ||>> mk_Frees "R" IphiTs;

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
        val fs_copy_maps = map (mk_map Ts fs_copy Ts' ctor's pmapsABT') ks;
        val Yctors = mk_ctors passiveYs;
        val f1s_maps = map (mk_map Ts f1s YTs Yctors (mk_passive_maps passiveAs passiveYs)) ks;
        val f2s_maps = map (mk_map Ts' f2s YTs Yctors (mk_passive_maps passiveBs passiveYs)) ks;
        val p1s_maps = map (mk_map XTs p1s Ts ctors (mk_passive_maps passiveXs passiveAs)) ks;
        val p2s_maps = map (mk_map XTs p2s Ts' ctor's (mk_passive_maps passiveXs passiveBs)) ks;

        val ctor_map_thms =
          let
            fun mk_goal fs_map map ctor ctor' = fold_rev Logic.all fs
              (mk_Trueprop_eq (HOLogic.mk_comp (fs_map, ctor),
                HOLogic.mk_comp (ctor', Term.list_comb (map, fs @ fs_maps))));
            val goals = map4 mk_goal fs_maps map_FTFT's ctors ctor's;
            val maps =
              map4 (fn goal => fn foldx => fn map_comp_id => fn map_cong =>
                Skip_Proof.prove lthy [] [] goal (K (mk_map_tac m n foldx map_comp_id map_cong))
                |> Thm.close_derivation)
              goals ctor_fold_thms map_comp_id_thms map_congs;
          in
            map (fn thm => thm RS @{thm pointfreeE}) maps
          end;

        val (ctor_map_unique_thms, ctor_map_unique_thm) =
          let
            fun mk_prem u map ctor ctor' =
              mk_Trueprop_eq (HOLogic.mk_comp (u, ctor),
                HOLogic.mk_comp (ctor', Term.list_comb (map, fs @ us)));
            val prems = map4 mk_prem us map_FTFT's ctors ctor's;
            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map2 (curry HOLogic.mk_eq) us fs_maps));
            val unique = Skip_Proof.prove lthy [] []
              (fold_rev Logic.all (us @ fs) (Logic.list_implies (prems, goal)))
              (K (mk_ctor_map_unique_tac m mor_def fold_unique_mor_thm map_comp_id_thms map_congs))
              |> Thm.close_derivation;
          in
            `split_conj_thm unique
          end;

        val timer = time (timer "map functions for the new datatypes");

        val bd = mk_cpow sum_bd;
        val bd_Cinfinite = sum_Cinfinite RS @{thm Cinfinite_cpow};
        fun mk_cpow_bd thm = @{thm ordLeq_transitive} OF
          [thm, sum_Card_order RS @{thm cpow_greater_eq}];
        val set_bd_cpowss = map (map mk_cpow_bd) set_bd_sumss;

        val timer = time (timer "bounds for the new datatypes");

        val ls = 1 upto m;
        val setsss = map (mk_setss o mk_set_Ts) passiveAs;
        val map_setss = map (fn T => map2 (fn Ds =>
          mk_map_of_bnf Ds (passiveAs @ Ts) (mk_set_Ts T)) Dss bnfs) passiveAs;

        fun mk_col l T z z' sets =
          let
            fun mk_UN set = mk_Union T $ (set $ z);
          in
            Term.absfree z'
              (mk_union (nth sets (l - 1) $ z,
                Library.foldl1 mk_union (map mk_UN (drop m sets))))
          end;

        val colss = map5 (fn l => fn T => map3 (mk_col l T)) ls passiveAs AFss AFss' setsss;
        val setss_by_range = map (fn cols => map (mk_fold Ts cols) ks) colss;
        val setss_by_bnf = transpose setss_by_range;

        val set_simp_thmss =
          let
            fun mk_goal sets ctor set col map =
              mk_Trueprop_eq (HOLogic.mk_comp (set, ctor),
                HOLogic.mk_comp (col, Term.list_comb (map, passive_ids @ sets)));
            val goalss =
              map3 (fn sets => map4 (mk_goal sets) ctors sets) setss_by_range colss map_setss;
            val setss = map (map2 (fn foldx => fn goal =>
              Skip_Proof.prove lthy [] [] goal (K (mk_set_tac foldx)) |> Thm.close_derivation)
              ctor_fold_thms) goalss;

            fun mk_simp_goal pas_set act_sets sets ctor z set =
              Logic.all z (mk_Trueprop_eq (set $ (ctor $ z),
                mk_union (pas_set $ z,
                  Library.foldl1 mk_union (map2 (fn X => mk_UNION (X $ z)) act_sets sets))));
            val simp_goalss =
              map2 (fn i => fn sets =>
                map4 (fn Fsets => mk_simp_goal (nth Fsets (i - 1)) (drop m Fsets) sets)
                  FTs_setss ctors xFs sets)
                ls setss_by_range;

            val ctor_setss = map3 (fn i => map3 (fn set_nats => fn goal => fn set =>
                Skip_Proof.prove lthy [] [] goal
                  (K (mk_set_simp_tac set (nth set_nats (i - 1)) (drop m set_nats)))
                |> Thm.close_derivation)
              set_natural'ss) ls simp_goalss setss;
          in
            ctor_setss
          end;

        fun mk_set_thms set_simp = (@{thm xt1(3)} OF [set_simp, @{thm Un_upper1}]) ::
          map (fn i => (@{thm xt1(3)} OF [set_simp, @{thm Un_upper2}]) RS
            (mk_Un_upper n i RS subset_trans) RSN
            (2, @{thm UN_upper} RS subset_trans))
            (1 upto n);
        val Fset_set_thmsss = transpose (map (map mk_set_thms) set_simp_thmss);

        val timer = time (timer "set functions for the new datatypes");

        val cxs = map (SOME o certify lthy) Izs;
        val setss_by_bnf' =
          map (map (Term.subst_atomic_types (passiveAs ~~ passiveBs))) setss_by_bnf;
        val setss_by_range' = transpose setss_by_bnf';

        val set_natural_thmss =
          let
            fun mk_set_natural f map z set set' =
              HOLogic.mk_eq (mk_image f $ (set $ z), set' $ (map $ z));

            fun mk_cphi f map z set set' = certify lthy
              (Term.absfree (dest_Free z) (mk_set_natural f map z set set'));

            val csetss = map (map (certify lthy)) setss_by_range';

            val cphiss = map3 (fn f => fn sets => fn sets' =>
              (map4 (mk_cphi f) fs_maps Izs sets sets')) fs setss_by_range setss_by_range';

            val inducts = map (fn cphis =>
              Drule.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm) cphiss;

            val goals =
              map3 (fn f => fn sets => fn sets' =>
                HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                  (map4 (mk_set_natural f) fs_maps Izs sets sets')))
                  fs setss_by_range setss_by_range';

            fun mk_tac induct = mk_set_nat_tac m (rtac induct) set_natural'ss ctor_map_thms;
            val thms =
              map5 (fn goal => fn csets => fn ctor_sets => fn induct => fn i =>
                singleton (Proof_Context.export names_lthy lthy)
                  (Skip_Proof.prove lthy [] [] goal (mk_tac induct csets ctor_sets i))
                |> Thm.close_derivation)
              goals csetss set_simp_thmss inducts ls;
          in
            map split_conj_thm thms
          end;

        val set_bd_thmss =
          let
            fun mk_set_bd z set = mk_ordLeq (mk_card_of (set $ z)) bd;

            fun mk_cphi z set = certify lthy (Term.absfree (dest_Free z) (mk_set_bd z set));

            val cphiss = map (map2 mk_cphi Izs) setss_by_range;

            val inducts = map (fn cphis =>
              Drule.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm) cphiss;

            val goals =
              map (fn sets =>
                HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                  (map2 mk_set_bd Izs sets))) setss_by_range;

            fun mk_tac induct = mk_set_bd_tac m (rtac induct) bd_Cinfinite set_bd_cpowss;
            val thms =
              map4 (fn goal => fn ctor_sets => fn induct => fn i =>
                singleton (Proof_Context.export names_lthy lthy)
                  (Skip_Proof.prove lthy [] [] goal (mk_tac induct ctor_sets i))
                |> Thm.close_derivation)
              goals set_simp_thmss inducts ls;
          in
            map split_conj_thm thms
          end;

        val map_cong_thms =
          let
            fun mk_prem z set f g y y' =
              mk_Ball (set $ z) (Term.absfree y' (HOLogic.mk_eq (f $ y, g $ y)));

            fun mk_map_cong sets z fmap gmap =
              HOLogic.mk_imp
                (Library.foldr1 HOLogic.mk_conj (map5 (mk_prem z) sets fs fs_copy ys ys'),
                HOLogic.mk_eq (fmap $ z, gmap $ z));

            fun mk_cphi sets z fmap gmap =
              certify lthy (Term.absfree (dest_Free z) (mk_map_cong sets z fmap gmap));

            val cphis = map4 mk_cphi setss_by_bnf Izs fs_maps fs_copy_maps;

            val induct = Drule.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm;

            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map4 mk_map_cong setss_by_bnf Izs fs_maps fs_copy_maps));

            val thm = singleton (Proof_Context.export names_lthy lthy)
              (Skip_Proof.prove lthy [] [] goal
              (mk_mcong_tac (rtac induct) Fset_set_thmsss map_congs ctor_map_thms))
              |> Thm.close_derivation;
          in
            split_conj_thm thm
          end;

        val in_incl_min_alg_thms =
          let
            fun mk_prem z sets =
              HOLogic.mk_mem (z, mk_in As sets (fastype_of z));

            fun mk_incl z sets i =
              HOLogic.mk_imp (mk_prem z sets, HOLogic.mk_mem (z, mk_min_alg As ctors i));

            fun mk_cphi z sets i =
              certify lthy (Term.absfree (dest_Free z) (mk_incl z sets i));

            val cphis = map3 mk_cphi Izs setss_by_bnf ks;

            val induct = Drule.instantiate' cTs (map SOME cphis @ cxs) ctor_induct_thm;

            val goal =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map3 mk_incl Izs setss_by_bnf ks));

            val thm = singleton (Proof_Context.export names_lthy lthy)
              (Skip_Proof.prove lthy [] [] goal
              (mk_incl_min_alg_tac (rtac induct) Fset_set_thmsss alg_set_thms alg_min_alg_thm))
              |> Thm.close_derivation;
          in
            split_conj_thm thm
          end;

        val Xsetss = map (map (Term.subst_atomic_types (passiveAs ~~ passiveXs))) setss_by_bnf;

        val map_wpull_thms =
          let
            val cTs = map (SOME o certifyT lthy o TFree) induct2_params;
            val cxs = map (SOME o certify lthy) (interleave Izs1 Izs2);

            fun mk_prem z1 z2 sets1 sets2 map1 map2 =
              HOLogic.mk_conj
                (HOLogic.mk_mem (z1, mk_in B1s sets1 (fastype_of z1)),
                HOLogic.mk_conj
                  (HOLogic.mk_mem (z2, mk_in B2s sets2 (fastype_of z2)),
                  HOLogic.mk_eq (map1 $ z1, map2 $ z2)));

            val prems = map6 mk_prem Izs1 Izs2 setss_by_bnf setss_by_bnf' f1s_maps f2s_maps;

            fun mk_concl z1 z2 sets map1 map2 T x x' =
              mk_Bex (mk_in AXs sets T) (Term.absfree x'
                (HOLogic.mk_conj (HOLogic.mk_eq (map1 $ x, z1), HOLogic.mk_eq (map2 $ x, z2))));

            val concls = map8 mk_concl Izs1 Izs2 Xsetss p1s_maps p2s_maps XTs xs xs';

            val goals = map2 (curry HOLogic.mk_imp) prems concls;

            fun mk_cphi z1 z2 goal = certify lthy (Term.absfree z1 (Term.absfree z2 goal));

            val cphis = map3 mk_cphi Izs1' Izs2' goals;

            val induct = Drule.instantiate' cTs (map SOME cphis @ cxs) ctor_induct2_thm;

            val goal = Logic.list_implies (map HOLogic.mk_Trueprop
                (map8 mk_wpull AXs B1s B2s f1s f2s (replicate m NONE) p1s p2s),
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj goals));

            val thm = singleton (Proof_Context.export names_lthy lthy)
              (Skip_Proof.prove lthy [] [] goal
              (K (mk_lfp_map_wpull_tac m (rtac induct) map_wpulls ctor_map_thms
                (transpose set_simp_thmss) Fset_set_thmsss ctor_inject_thms)))
              |> Thm.close_derivation;
          in
            split_conj_thm thm
          end;

        val timer = time (timer "helpers for BNF properties");

        val map_id_tacs = map (K o mk_map_id_tac map_ids) ctor_map_unique_thms;
        val map_comp_tacs =
          map2 (K oo mk_map_comp_tac map_comp's ctor_map_thms) ctor_map_unique_thms ks;
        val map_cong_tacs = map (mk_map_cong_tac m) map_cong_thms;
        val set_nat_tacss = map (map (K o mk_set_natural_tac)) (transpose set_natural_thmss);
        val bd_co_tacs = replicate n (K (mk_bd_card_order_tac bd_card_orders));
        val bd_cinf_tacs = replicate n (K (rtac (bd_Cinfinite RS conjunct1) 1));
        val set_bd_tacss = map (map (fn thm => K (rtac thm 1))) (transpose set_bd_thmss);
        val in_bd_tacs = map2 (K oo mk_in_bd_tac sum_Card_order suc_bd_Cnotzero)
          in_incl_min_alg_thms card_of_min_alg_thms;
        val map_wpull_tacs = map (K o mk_wpull_tac) map_wpull_thms;

        val srel_O_Gr_tacs = replicate n (simple_srel_O_Gr_tac o #context);

        val tacss = map10 zip_axioms map_id_tacs map_comp_tacs map_cong_tacs set_nat_tacss
          bd_co_tacs bd_cinf_tacs set_bd_tacss in_bd_tacs map_wpull_tacs srel_O_Gr_tacs;

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
            map3 (fn ctor => fn i => map close_wit o minimize_wits o maps (mk_wit witss ctor i))
              ctors (0 upto n - 1) witss
          end;

        fun wit_tac _ = mk_wit_tac n (flat set_simp_thmss) (maps wit_thms_of_bnf bnfs);

        val (Ibnfs, lthy) =
          fold_map6 (fn tacs => fn b => fn mapx => fn sets => fn T => fn wits => fn lthy =>
            bnf_def Dont_Inline (user_policy Note_Some) I tacs wit_tac (SOME deads)
              (((((b, fold_rev Term.absfree fs' mapx), sets), absdummy T bd), wits), NONE) lthy
            |> register_bnf (Local_Theory.full_name lthy b))
          tacss bs fs_maps setss_by_bnf Ts ctor_witss lthy;

        val fold_maps = fold_thms lthy (map (fn bnf =>
          mk_unabs_def m (map_def_of_bnf bnf RS @{thm meta_eq_to_obj_eq})) Ibnfs);

        val fold_sets = fold_thms lthy (maps (fn bnf =>
          map (fn thm => thm RS @{thm meta_eq_to_obj_eq}) (set_defs_of_bnf bnf)) Ibnfs);

        val timer = time (timer "registered new datatypes as BNFs");

        val srels = map2 (fn Ds => mk_srel_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;
        val Isrels = map (mk_srel_of_bnf deads passiveAs passiveBs) Ibnfs;
        val rels = map2 (fn Ds => mk_rel_of_bnf Ds (passiveAs @ Ts) (passiveBs @ Ts')) Dss bnfs;
        val Irels = map (mk_rel_of_bnf deads passiveAs passiveBs) Ibnfs;

        val IsrelRs = map (fn Isrel => Term.list_comb (Isrel, IRs)) Isrels;
        val srelRs = map (fn srel => Term.list_comb (srel, IRs @ IsrelRs)) srels;
        val Irelphis = map (fn Isrel => Term.list_comb (Isrel, Iphis)) Irels;
        val relphis = map (fn srel => Term.list_comb (srel, Iphis @ Irelphis)) rels;

        val in_srels = map in_srel_of_bnf bnfs;
        val in_Isrels = map in_srel_of_bnf Ibnfs;
        val srel_defs = map srel_def_of_bnf bnfs;
        val Isrel_defs = map srel_def_of_bnf Ibnfs;
        val Irel_defs = map rel_def_of_bnf Ibnfs;

        val ctor_set_incl_thmss = map (map (fold_sets o hd)) Fset_set_thmsss;
        val ctor_set_set_incl_thmsss = map (transpose o map (map fold_sets o tl)) Fset_set_thmsss;
        val folded_ctor_map_thms = map fold_maps ctor_map_thms;
        val folded_set_simp_thmss = map (map fold_sets) set_simp_thmss;
        val folded_set_simp_thmss' = transpose folded_set_simp_thmss;

        val ctor_Isrel_thms =
          let
            fun mk_goal xF yF ctor ctor' IsrelR srelR = fold_rev Logic.all (xF :: yF :: IRs)
              (mk_Trueprop_eq (HOLogic.mk_mem (HOLogic.mk_prod (ctor $ xF, ctor' $ yF), IsrelR),
                  HOLogic.mk_mem (HOLogic.mk_prod (xF, yF), srelR)));
            val goals = map6 mk_goal xFs yFs ctors ctor's IsrelRs srelRs;
          in
            map12 (fn i => fn goal => fn in_srel => fn map_comp => fn map_cong =>
              fn ctor_map => fn ctor_sets => fn ctor_inject => fn ctor_dtor =>
              fn set_naturals => fn ctor_set_incls => fn ctor_set_set_inclss =>
              Skip_Proof.prove lthy [] [] goal
               (K (mk_ctor_srel_tac in_Isrels i in_srel map_comp map_cong ctor_map ctor_sets
                 ctor_inject ctor_dtor set_naturals ctor_set_incls ctor_set_set_inclss))
              |> Thm.close_derivation)
            ks goals in_srels map_comp's map_congs folded_ctor_map_thms folded_set_simp_thmss'
              ctor_inject_thms ctor_dtor_thms set_natural'ss ctor_set_incl_thmss
              ctor_set_set_incl_thmsss
          end;

        val ctor_Irel_thms =
          let
            fun mk_goal xF yF ctor ctor' Ipredphi predphi = fold_rev Logic.all (xF :: yF :: Iphis)
              (mk_Trueprop_eq (Ipredphi $ (ctor $ xF) $ (ctor' $ yF), predphi $ xF $ yF));
            val goals = map6 mk_goal xFs yFs ctors ctor's Irelphis relphis;
          in
            map3 (fn goal => fn srel_def => fn ctor_Isrel =>
              Skip_Proof.prove lthy [] [] goal
                (mk_ctor_or_dtor_rel_tac srel_def Irel_defs Isrel_defs ctor_Isrel)
              |> Thm.close_derivation)
            goals srel_defs ctor_Isrel_thms
          end;

        val timer = time (timer "additional properties");

        val ls' = if m = 1 then [0] else ls

        val Ibnf_common_notes =
          [(ctor_map_uniqueN, [fold_maps ctor_map_unique_thm])]
          |> map (fn (thmN, thms) =>
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

        val Ibnf_notes =
          [(ctor_mapN, map single folded_ctor_map_thms),
          (ctor_relN, map single ctor_Irel_thms),
          (ctor_srelN, map single ctor_Isrel_thms),
          (ctor_set_inclN, ctor_set_incl_thmss),
          (ctor_set_set_inclN, map flat ctor_set_set_incl_thmsss)] @
          map2 (fn i => fn thms => (mk_ctor_setsN i, map single thms)) ls' folded_set_simp_thmss
          |> maps (fn (thmN, thmss) =>
            map2 (fn b => fn thms =>
              ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
            bs thmss)
      in
        timer; (Irels, lthy |> Local_Theory.notes (Ibnf_common_notes @ Ibnf_notes) |> snd)
      end;

      val common_notes =
        [(ctor_inductN, [ctor_induct_thm]),
        (ctor_induct2N, [ctor_induct2_thm])]
        |> map (fn (thmN, thms) =>
          ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));

      val notes =
        [(ctor_dtorN, ctor_dtor_thms),
        (ctor_exhaustN, ctor_exhaust_thms),
        (ctor_fold_uniqueN, ctor_fold_unique_thms),
        (ctor_foldsN, ctor_fold_thms),
        (ctor_injectN, ctor_inject_thms),
        (ctor_recsN, ctor_rec_thms),
        (dtor_ctorN, dtor_ctor_thms),
        (dtor_exhaustN, dtor_exhaust_thms),
        (dtor_injectN, dtor_inject_thms)]
        |> map (apsnd (map single))
        |> maps (fn (thmN, thmss) =>
          map2 (fn b => fn thms =>
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
          bs thmss)
  in
    ((dtors, ctors, Irels, folds, recs, ctor_induct_thm, dtor_ctor_thms, ctor_dtor_thms,
      ctor_inject_thms, ctor_fold_thms, ctor_rec_thms),
     lthy |> Local_Theory.notes (common_notes @ notes) |> snd)
  end;

val _ =
  Outer_Syntax.local_theory @{command_spec "data_raw"}
    "define BNF-based inductive datatypes (low-level)"
    (Parse.and_list1
      ((Parse.binding --| @{keyword ":"}) -- (Parse.typ --| @{keyword "="} -- Parse.typ)) >>
      (snd oo fp_bnf_cmd bnf_lfp o apsnd split_list o split_list));

val _ =
  Outer_Syntax.local_theory @{command_spec "data"} "define BNF-based inductive datatypes"
    (parse_datatype_cmd true bnf_lfp);

end;
