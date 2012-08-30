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
val distinctN = "distinct"
val disc_exhaustN = "disc_exhaust"
val selsN = "sels"
val splitN = "split"
val split_asmN = "split_asm"
val weak_case_cong_thmsN = "weak_case_cong"

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
      let
        val Ts0 = snd (dest_Type (body_type (fastype_of ctr)));
      in
        Term.subst_atomic_types (Ts0 ~~ Ts) ctr
      end;

    fun mk_caseof T =
      let
        val (binders, body) = strip_type (fastype_of caseof0);
      in
        Term.subst_atomic_types ((body, T) :: (snd (dest_Type (List.last binders)) ~~ As)) caseof0
      end;

    val T = Type (T_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val caseofB = mk_caseof B;
    val caseofB_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    val (((((xss, yss), fs), (v, v')), p), _) = no_defs_lthy |>
      mk_Freess "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" caseofB_Ts
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") T
      ||>> yield_singleton (mk_Frees "P") HOLogic.boolT;

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;
    val eta_fs = map2 (fn f => fn xs => fold_rev Term.lambda xs (Term.list_comb (f, xs))) fs xss;

    val exist_xs_v_eq_ctrs =
      map2 (fn xctr => fn xs => list_exists_free xs (HOLogic.mk_eq (v, xctr))) xctrs xss;

    fun mk_caseof_args k xs x T =
      map2 (fn Ts => fn i => if i = k then fold_rev Term.lambda xs x else mk_undef T Ts) ctr_Tss ks;

    fun disc_spec b exist_xs_v_eq_ctr =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (Free (Binding.name_of b, T --> HOLogic.boolT) $ v,
        exist_xs_v_eq_ctr));

    fun sel_spec b x xs xctr k =
      let val T' = fastype_of x in
        HOLogic.mk_Trueprop (HOLogic.mk_eq (Free (Binding.name_of b, T --> T') $ v,
            Term.list_comb (mk_caseof T', mk_caseof_args k xs x T') $ v))
      end;

    val (((discs0, (_, disc_defs0)), (selss0, (_, sel_defss0))), (lthy', lthy)) =
      no_defs_lthy
      |> apfst (apsnd split_list o split_list) o fold_map2 (fn b => fn exist_xs_v_eq_ctr =>
        Specification.definition (SOME (b, NONE, NoSyn),
          ((Thm.def_binding b, []), disc_spec b exist_xs_v_eq_ctr))) disc_names exist_xs_v_eq_ctrs
      ||>> apfst (apsnd split_list o split_list) o fold_map4 (fn bs => fn xs => fn xctr => fn k =>
        apfst (apsnd split_list o split_list) o fold_map2 (fn b => fn x =>
          Specification.definition (SOME (b, NONE, NoSyn),
            ((Thm.def_binding b, []), sel_spec b x xs xctr k))) bs xs) sel_namess xss xctrs
            ks
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts (and more)*)
    val phi = Proof_Context.export_morphism lthy lthy';

    val disc_defs = map (Morphism.thm phi) disc_defs0;
    val sel_defss = map (map (Morphism.thm phi)) sel_defss0;

    val discs = map (Morphism.term phi) discs0;
    val selss = map (map (Morphism.term phi)) selss0;

    val goal_exhaust =
      let
        fun mk_imp_p Q = Logic.list_implies (Q, HOLogic.mk_Trueprop p);
        fun mk_prem xctr xs =
          fold_rev Logic.all xs (mk_imp_p [HOLogic.mk_Trueprop (HOLogic.mk_eq (v, xctr))]);
      in
        mk_imp_p (map2 mk_prem xctrs xss)
      end;

    val goal_injects =
      let
        fun mk_goal _ _ [] [] = NONE
          | mk_goal xctr yctr xs ys =
            SOME (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (HOLogic.mk_eq (xctr, yctr),
               Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys))));
      in
        map_filter I (map4 mk_goal xctrs yctrs xss yss)
      end;

    val goal_half_distincts =
      let
        fun mk_goal t u = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (t, u)));
        fun mk_goals [] = []
          | mk_goals (t :: ts) = fold_rev (cons o mk_goal t) ts (mk_goals ts);
      in
        mk_goals xctrs
      end;

    val goal_cases =
      let
        val lhs0 = Term.list_comb (caseofB, eta_fs);
        fun mk_goal k xctr xs f =
          HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs0 $ xctr, Term.list_comb (f, xs)))
          |> tap (tracing o prefix "HERE: " o PolyML.makestring)(*###*);
      in
        map4 mk_goal ks xctrs xss fs
      end;

    val goals = [[goal_exhaust], goal_injects, goal_half_distincts, goal_cases];

    fun after_qed thmss lthy =
      let
        val [[exhaust_thm], inject_thms, half_distinct_thms, case_thms] = thmss;

        val other_half_distinct_thms = map (fn thm => thm RS not_sym) half_distinct_thms;

        val nchotomy_thm =
          let
            val goal =
              HOLogic.mk_Trueprop (HOLogic.mk_all (fst v', snd v',
                   Library.foldr1 HOLogic.mk_disj exist_xs_v_eq_ctrs));
          in
            Skip_Proof.prove lthy [] [] goal (fn _ => mk_nchotomy_tac n exhaust_thm)
          end;

        val sel_thms =
          let
            fun mk_thm k xs goal_case case_thm x sel sel_def =
              let
                val T = fastype_of x;
                val cTs =
                  map ((fn T' => certifyT lthy (if T' = B then T else T')) o TFree)
                    (rev (Term.add_tfrees goal_case []));
                val cxs = map (certify lthy) (mk_caseof_args k xs x T);
              in
                Local_Defs.fold lthy [sel_def]
                  (Drule.instantiate' (map SOME cTs) (map SOME cxs) case_thm)
              end;
            fun mk_thms k xs goal_case case_thm sels sel_defs =
              map3 (mk_thm k xs goal_case case_thm) xs sels sel_defs;
          in
            flat (map6 mk_thms ks xss goal_cases case_thms selss sel_defss)
          end;

        val disc_thms = [];

        val disc_disjoint_thms = [];

        val disc_exhaust_thms = [];

        val ctr_sel_thms = [];

        val case_disc_thms = [];

        val case_cong_thm = TrueI;

        val weak_case_cong_thms = TrueI;

        val split_thms = [];

        val split_asm_thms = [];

        (* case syntax *)

        fun note thmN thms =
          snd o Local_Theory.note
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms);
      in
        lthy
        |> note case_congN [case_cong_thm]
        |> note case_discsN case_disc_thms
        |> note casesN case_thms
        |> note ctr_selsN ctr_sel_thms
        |> note disc_disjointN disc_disjoint_thms
        |> note disc_exhaustN disc_exhaust_thms
        |> note distinctN (half_distinct_thms @ other_half_distinct_thms)
        |> note exhaustN [exhaust_thm]
        |> note injectN inject_thms
        |> note nchotomyN [nchotomy_thm]
        |> note selsN sel_thms
        |> note splitN split_thms
        |> note split_asmN split_asm_thms
        |> note weak_case_cong_thmsN [weak_case_cong_thms]
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
