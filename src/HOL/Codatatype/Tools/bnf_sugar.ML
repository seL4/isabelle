(*  Title:      HOL/Codatatype/Tools/bnf_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar on top of a BNF.
*)

signature BNF_SUGAR =
sig
end;

structure BNF_Sugar : BNF_SUGAR =
struct

open BNF_Util
open BNF_FP_Util
open BNF_Sugar_Tactics

val case_congN = "case_cong"
val case_discsN = "case_discs"
val casesN = "cases"
val ctr_selsN = "ctr_sels"
val disc_disjointN = "disc_disjoint"
val disc_exhaustN = "disc_exhaust"
val discsN = "discs"
val distinctN = "distinct"
val selsN = "sels"
val splitN = "split"
val split_asmN = "split_asm"
val weak_case_cong_thmsN = "weak_case_cong"

fun mk_half_pairs [] = []
  | mk_half_pairs (x :: xs) = fold_rev (cons o pair x) xs (mk_half_pairs xs);

fun index_of_half_row _ 0 = 0
  | index_of_half_row n j = index_of_half_row n (j - 1) + n - j;

fun index_of_half_cell n j k = index_of_half_row n j + k - (j + 1);

val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun eta_expand_caseof_arg f xs = fold_rev Term.lambda xs (Term.list_comb (f, xs));

fun prepare_sugar prep_term (((raw_ctrs, raw_caseof), disc_names), sel_namess) no_defs_lthy =
  let
    (* TODO: sanity checks on arguments *)

    (* TODO: normalize types of constructors w.r.t. each other *)

    val ctrs0 = map (prep_term no_defs_lthy) raw_ctrs;
    val caseof0 = prep_term no_defs_lthy raw_caseof;

    val n = length ctrs0;
    val ks = 1 upto n;

    val (T_name, As0) = dest_Type (body_type (fastype_of (hd ctrs0)));
    val b = Binding.qualified_name T_name;

    val (As, B) =
      no_defs_lthy
      |> mk_TFrees (length As0)
      ||> the_single o fst o mk_TFrees 1;

    fun mk_undef T Ts = Const (@{const_name undefined}, Ts ---> T);

    fun mk_ctr Ts ctr =
      let val Ts0 = snd (dest_Type (body_type (fastype_of ctr))) in
        Term.subst_atomic_types (Ts0 ~~ Ts) ctr
      end;

    fun mk_caseof Ts T =
      let val (binders, body) = strip_type (fastype_of caseof0) in
        Term.subst_atomic_types ((body, T) :: (snd (dest_Type (List.last binders)) ~~ Ts)) caseof0
      end;

    val T = Type (T_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val ms = map length ctr_Tss;

    val caseofB = mk_caseof As B;
    val caseofB_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    val (((((((xss, yss), fs), gs), (v, v')), w), p), names_lthy) = no_defs_lthy |>
      mk_Freess "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" caseofB_Ts
      ||>> mk_Frees "g" caseofB_Ts
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") T
      ||>> yield_singleton (mk_Frees "w") T
      ||>> yield_singleton (mk_Frees "P") HOLogic.boolT;

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;

    val eta_fs = map2 eta_expand_caseof_arg fs xss;
    val eta_gs = map2 eta_expand_caseof_arg gs xss;

    val exist_xs_v_eq_ctrs =
      map2 (fn xctr => fn xs => list_exists_free xs (HOLogic.mk_eq (v, xctr))) xctrs xss;

    fun mk_sel_caseof_args k xs x T =
      map2 (fn Ts => fn i => if i = k then fold_rev Term.lambda xs x else mk_undef T Ts) ctr_Tss ks;

    fun disc_spec b exist_xs_v_eq_ctr =
      mk_Trueprop_eq (Free (Binding.name_of b, T --> HOLogic.boolT) $ v, exist_xs_v_eq_ctr);

    fun sel_spec b x xs k =
      let val T' = fastype_of x in
        mk_Trueprop_eq (Free (Binding.name_of b, T --> T') $ v,
          Term.list_comb (mk_caseof As T', mk_sel_caseof_args k xs x T') $ v)
      end;

    val (((raw_discs, (_, raw_disc_defs)), (raw_selss, (_, raw_sel_defss))), (lthy', lthy)) =
      no_defs_lthy
      |> apfst (apsnd split_list o split_list) o fold_map2 (fn b => fn exist_xs_v_eq_ctr =>
        Specification.definition (SOME (b, NONE, NoSyn),
          ((Thm.def_binding b, []), disc_spec b exist_xs_v_eq_ctr))) disc_names exist_xs_v_eq_ctrs
      ||>> apfst (apsnd split_list o split_list) o fold_map3 (fn bs => fn xs => fn k =>
        apfst (apsnd split_list o split_list) o fold_map2 (fn b => fn x =>
          Specification.definition (SOME (b, NONE, NoSyn),
            ((Thm.def_binding b, []), sel_spec b x xs k))) bs xs) sel_namess xss ks
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts (and more)*)
    val phi = Proof_Context.export_morphism lthy lthy';

    val disc_defs = map (Morphism.thm phi) raw_disc_defs;
    val sel_defss = map (map (Morphism.thm phi)) raw_sel_defss;

    val discs0 = map (Morphism.term phi) raw_discs;
    val selss0 = map (map (Morphism.term phi)) raw_selss;

    fun mk_disc_or_sel Ts t =
      Term.subst_atomic_types (snd (dest_Type (domain_type (fastype_of t))) ~~ Ts) t;

    val discs = map (mk_disc_or_sel As) discs0;
    val selss = map (map (mk_disc_or_sel As)) selss0;

    fun mk_imp_p Qs = Logic.list_implies (Qs, HOLogic.mk_Trueprop p);

    val goal_exhaust =
      let fun mk_prem xctr xs = fold_rev Logic.all xs (mk_imp_p [mk_Trueprop_eq (v, xctr)]) in
        mk_imp_p (map2 mk_prem xctrs xss)
      end;

    val goal_injects =
      let
        fun mk_goal _ _ [] [] = NONE
          | mk_goal xctr yctr xs ys =
            SOME (mk_Trueprop_eq (HOLogic.mk_eq (xctr, yctr),
              Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys)));
      in
        map_filter I (map4 mk_goal xctrs yctrs xss yss)
      end;

    val goal_half_distincts =
      map (HOLogic.mk_Trueprop o HOLogic.mk_not o HOLogic.mk_eq) (mk_half_pairs xctrs);

    val goal_cases =
      let
        val lhs0 = Term.list_comb (caseofB, eta_fs);
        fun mk_goal xctr xs f = mk_Trueprop_eq (lhs0 $ xctr, Term.list_comb (f, xs));
      in
        map3 mk_goal xctrs xss fs
      end;

    val goals = [[goal_exhaust], goal_injects, goal_half_distincts, goal_cases];

    fun after_qed thmss lthy =
      let
        val [[exhaust_thm], inject_thms, half_distinct_thms, case_thms] = thmss;

        val exhaust_thm' =
          let val Tinst = map (pairself (certifyT lthy)) (map Logic.varifyT_global As ~~ As) in
            Drule.instantiate' [] [SOME (certify lthy v)]
              (Thm.instantiate (Tinst, []) (Drule.zero_var_indexes exhaust_thm))
          end;

        val other_half_distinct_thms = map (fn thm => thm RS not_sym) half_distinct_thms;

        val nchotomy_thm =
          let
            val goal =
              HOLogic.mk_Trueprop (HOLogic.mk_all (fst v', snd v',
                Library.foldr1 HOLogic.mk_disj exist_xs_v_eq_ctrs));
          in
            Skip_Proof.prove lthy [] [] goal (fn _ => mk_nchotomy_tac n exhaust_thm)
          end;

        val sel_thmss =
          let
            fun mk_thm k xs goal_case case_thm x sel_def =
              let
                val T = fastype_of x;
                val cTs =
                  map ((fn T' => certifyT lthy (if T' = B then T else T')) o TFree)
                    (rev (Term.add_tfrees goal_case []));
                val cxs = map (certify lthy) (mk_sel_caseof_args k xs x T);
              in
                Local_Defs.fold lthy [sel_def]
                  (Drule.instantiate' (map SOME cTs) (map SOME cxs) case_thm)
              end;
            fun mk_thms k xs goal_case case_thm sel_defs =
              map2 (mk_thm k xs goal_case case_thm) xs sel_defs;
          in
            map5 mk_thms ks xss goal_cases case_thms sel_defss
          end;

        val discD_thms = map (fn def => def RS iffD1) disc_defs;
        val discI_thms =
          map2 (fn m => fn def => funpow m (fn thm => exI RS thm) (def RS iffD2)) ms disc_defs;
        val not_disc_thms =
          map2 (fn m => fn def => funpow m (fn thm => allI RS thm)
                  (Local_Defs.unfold lthy @{thms not_ex} (def RS @{thm ssubst[of _ _ Not]})))
            ms disc_defs;

        val disc_thms =
          let
            fun get_distinct_thm k k' =
              if k > k' then nth half_distinct_thms (index_of_half_cell n (k' - 1) (k - 1))
              else nth other_half_distinct_thms (index_of_half_cell n (k' - 1) (k' - 1))
            fun mk_thm ((k, discI), not_disc) k' =
              if k = k' then refl RS discI else get_distinct_thm k k' RS not_disc;
          in
            map_product mk_thm (ks ~~ discI_thms ~~ not_disc_thms) ks
          end;

        val disc_disjoint_thms =
          let
            fun get_disc_thm k k' = nth disc_thms ((k' - 1) * n + (k - 1));
            fun mk_goal ((_, disc), (_, disc')) =
              Logic.all v (Logic.mk_implies (HOLogic.mk_Trueprop (disc $ v),
                HOLogic.mk_Trueprop (HOLogic.mk_not (disc' $ v))));
            fun prove tac goal = Skip_Proof.prove lthy [] [] goal (K tac);

            val bundles = ks ~~ ms ~~ discD_thms ~~ discs;
            val half_pairs = mk_half_pairs bundles;

            val goal_halves = map mk_goal half_pairs;
            val half_thms =
              map2 (fn ((((k, m), discD), _), (((k', _), _), _)) =>
                prove (mk_half_disc_disjoint_tac m discD (get_disc_thm k k')))
              half_pairs goal_halves;

            val goal_other_halves = map (mk_goal o swap) half_pairs;
            val other_half_thms =
              map2 (prove o mk_other_half_disc_disjoint_tac) half_thms goal_other_halves;
          in
            half_thms @ other_half_thms
          end;

        val disc_exhaust_thm =
          let
            fun mk_prem disc = mk_imp_p [HOLogic.mk_Trueprop (disc $ v)];
            val goal = fold Logic.all [p, v] (mk_imp_p (map mk_prem discs));
          in
            Skip_Proof.prove lthy [] [] goal (fn _ => mk_disc_exhaust_tac n exhaust_thm discI_thms)
          end;

        val ctr_sel_thms =
          let
            fun mk_goal ctr disc sels =
              Logic.all v (Logic.mk_implies (HOLogic.mk_Trueprop (disc $ v),
                mk_Trueprop_eq ((null sels ? swap)
                  (Term.list_comb (ctr, map (fn sel => sel $ v) sels), v))));
            val goals = map3 mk_goal ctrs discs selss;
          in
            map4 (fn goal => fn m => fn discD => fn sel_thms =>
              Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                mk_ctr_sel_tac ctxt m discD sel_thms))
              goals ms discD_thms sel_thmss
          end;

        val case_disc_thm =
          let
            fun mk_core f sels = Term.list_comb (f, map (fn sel => sel $ v) sels);
            fun mk_rhs _ [f] [sels] = mk_core f sels
              | mk_rhs (disc :: discs) (f :: fs) (sels :: selss) =
                Const (@{const_name If}, HOLogic.boolT --> B --> B --> B) $
                  (disc $ v) $ mk_core f sels $ mk_rhs discs fs selss;

            val lhs = Term.list_comb (caseofB, eta_fs) $ v;
            val rhs = mk_rhs discs fs selss;
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
              mk_case_disc_tac ctxt exhaust_thm' case_thms disc_thms sel_thmss)
            |> singleton (Proof_Context.export names_lthy lthy)
          end;

        val (case_cong_thm, weak_case_cong_thm) =
          let
            fun mk_prem xctr xs f g =
              fold_rev Logic.all xs (Logic.mk_implies (mk_Trueprop_eq (v, xctr),
                mk_Trueprop_eq (f, g)));
            fun mk_caseof_term fs = Term.list_comb (caseofB, fs);

            val v_eq_w = mk_Trueprop_eq (v, w);
            val caseof_fs = mk_caseof_term eta_fs;
            val caseof_gs = mk_caseof_term eta_gs;

            val goal =
              Logic.list_implies (v_eq_w :: map4 mk_prem xctrs xss fs gs,
                 mk_Trueprop_eq (caseof_fs $ v, caseof_gs $ w));
            val goal_weak =
              Logic.mk_implies (v_eq_w, mk_Trueprop_eq (caseof_fs $ v, caseof_fs $ w));
          in
            (Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
               mk_case_cong_tac ctxt exhaust_thm' case_thms),
             Skip_Proof.prove lthy [] [] goal_weak (K (etac arg_cong 1)))
            |> pairself (singleton (Proof_Context.export names_lthy lthy))
          end;

        val split_thms = [];

        val split_asm_thms = [];

        (* case syntax *)

        fun note thmN thms =
          snd o Local_Theory.note
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms);
      in
        lthy
        |> note case_congN [case_cong_thm]
        |> note case_discsN [case_disc_thm]
        |> note casesN case_thms
        |> note ctr_selsN ctr_sel_thms
        |> note discsN disc_thms
        |> note disc_disjointN disc_disjoint_thms
        |> note disc_exhaustN [disc_exhaust_thm]
        |> note distinctN (half_distinct_thms @ other_half_distinct_thms)
        |> note exhaustN [exhaust_thm]
        |> note injectN inject_thms
        |> note nchotomyN [nchotomy_thm]
        |> note selsN (flat sel_thmss)
        |> note splitN split_thms
        |> note split_asmN split_asm_thms
        |> note weak_case_cong_thmsN [weak_case_cong_thm]
      end;
  in
    (goals, after_qed, lthy')
  end;

val parse_binding_list = Parse.$$$ "[" |--  Parse.list Parse.binding --| Parse.$$$ "]";

val bnf_sugar_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE after_qed (map (map (rpair [])) goalss) lthy) oo
  prepare_sugar Syntax.read_term;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "bnf_sugar"} "adds sugar on top of a BNF"
    (((Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") -- Parse.term --
      parse_binding_list -- (Parse.$$$ "[" |-- Parse.list parse_binding_list --| Parse.$$$ "]"))
      >> bnf_sugar_cmd);

end;
