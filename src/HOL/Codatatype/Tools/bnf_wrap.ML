(*  Title:      HOL/Codatatype/Tools/bnf_wrap.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Wrapping existing datatypes.
*)

signature BNF_WRAP =
sig
end;

structure BNF_Wrap : BNF_WRAP =
struct

open BNF_Util
open BNF_FP_Util
open BNF_Wrap_Tactics

val is_N = "is_";
val un_N = "un_";
fun mk_un_N 1 1 suf = un_N ^ suf
  | mk_un_N _ l suf = un_N ^ suf ^ string_of_int l;

val case_congN = "case_cong";
val case_discsN = "case_discs";
val casesN = "cases";
val ctr_selsN = "ctr_sels";
val disc_exclusN = "disc_exclus";
val disc_exhaustN = "disc_exhaust";
val discsN = "discs";
val distinctN = "distinct";
val selsN = "sels";
val splitN = "split";
val split_asmN = "split_asm";
val weak_case_cong_thmsN = "weak_case_cong";

val default_name = @{binding _};

fun pad_list x n xs = xs @ replicate (n - length xs) x;

fun mk_half_pairss' _ [] = []
  | mk_half_pairss' indent (y :: ys) =
    indent @ fold_rev (cons o single o pair y) ys (mk_half_pairss' ([] :: indent) ys);

fun mk_half_pairss ys = mk_half_pairss' [[]] ys;

val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun mk_undef T Ts = Const (@{const_name undefined}, Ts ---> T);

fun eta_expand_caseof_arg xs f_xs = fold_rev Term.lambda xs f_xs;

fun name_of_ctr t =
  case head_of t of
    Const (s, _) => s
  | Free (s, _) => s
  | _ => error "Cannot extract name of constructor";

fun prepare_wrap prep_term ((raw_ctrs, raw_caseof), (raw_disc_names, raw_sel_namess))
  no_defs_lthy =
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

    fun mk_ctr Ts ctr =
      let val Ts0 = snd (dest_Type (body_type (fastype_of ctr))) in
        Term.subst_atomic_types (Ts0 ~~ Ts) ctr
      end;

    val T = Type (T_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val ms = map length ctr_Tss;

    val disc_names =
      pad_list default_name n raw_disc_names
      |> map2 (fn ctr => fn disc =>
        if Binding.eq_name (disc, default_name) then
          Binding.name (prefix is_N (Long_Name.base_name (name_of_ctr ctr)))
        else
          disc) ctrs0;

    val sel_namess =
      pad_list [] n raw_sel_namess
      |> map3 (fn ctr => fn m => map2 (fn l => fn sel =>
        if Binding.eq_name (sel, default_name) then
          Binding.name (mk_un_N m l (Long_Name.base_name (name_of_ctr ctr)))
        else
          sel) (1 upto m) o pad_list default_name m) ctrs0 ms;

    fun mk_caseof Ts T =
      let val (binders, body) = strip_type (fastype_of caseof0) in
        Term.subst_atomic_types ((body, T) :: (snd (dest_Type (List.last binders)) ~~ Ts)) caseof0
      end;

    val caseofB = mk_caseof As B;
    val caseofB_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    fun mk_caseofB_term eta_fs = Term.list_comb (caseofB, eta_fs);

    val (((((((xss, yss), fs), gs), (v, v')), w), (p, p')), names_lthy) = no_defs_lthy |>
      mk_Freess "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" caseofB_Ts
      ||>> mk_Frees "g" caseofB_Ts
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") T
      ||>> yield_singleton (mk_Frees "w") T
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "P") HOLogic.boolT;

    val q = Free (fst p', B --> HOLogic.boolT);

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;

    val xfs = map2 (curry Term.list_comb) fs xss;
    val xgs = map2 (curry Term.list_comb) gs xss;

    val eta_fs = map2 eta_expand_caseof_arg xss xfs;
    val eta_gs = map2 eta_expand_caseof_arg xss xgs;

    val caseofB_fs = Term.list_comb (caseofB, eta_fs);

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

    val goal_injectss =
      let
        fun mk_goal _ _ [] [] = []
          | mk_goal xctr yctr xs ys =
            [mk_Trueprop_eq (HOLogic.mk_eq (xctr, yctr),
              Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys))];
      in
        map4 mk_goal xctrs yctrs xss yss
      end;

    val goal_half_distinctss =
      map (map (HOLogic.mk_Trueprop o HOLogic.mk_not o HOLogic.mk_eq)) (mk_half_pairss xctrs);

    val goal_cases = map2 (fn xctr => fn xf => mk_Trueprop_eq (caseofB_fs $ xctr, xf)) xctrs xfs;

    val goals = [goal_exhaust] :: goal_injectss @ goal_half_distinctss @ [goal_cases];

    fun after_qed thmss lthy =
      let
        val ([exhaust_thm], (inject_thmss, (half_distinct_thmss, [case_thms]))) =
          (hd thmss, apsnd (chop (n * n)) (chop n (tl thmss)));

        val exhaust_thm' =
          let val Tinst = map (pairself (certifyT lthy)) (map Logic.varifyT_global As ~~ As) in
            Drule.instantiate' [] [SOME (certify lthy v)]
              (Thm.instantiate (Tinst, []) (Drule.zero_var_indexes exhaust_thm))
          end;

        val other_half_distinct_thmss = map (map (fn thm => thm RS not_sym)) half_distinct_thmss;

        val (distinct_thmsss', distinct_thmsss) =
          map2 (map2 append) (Library.chop_groups n half_distinct_thmss)
            (transpose (Library.chop_groups n other_half_distinct_thmss))
          |> `transpose;
        val distinct_thms = interleave (flat half_distinct_thmss) (flat other_half_distinct_thmss);

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

        val (disc_thmss', disc_thmss) =
          let
            fun mk_thm discI _ [] = refl RS discI
              | mk_thm _ not_disc [distinct] = distinct RS not_disc;
            fun mk_thms discI not_disc distinctss = map (mk_thm discI not_disc) distinctss;
          in
            map3 mk_thms discI_thms not_disc_thms distinct_thmsss'
            |> `transpose
          end;

        val disc_exclus_thms =
          let
            fun mk_goal ((_, disc), (_, disc')) =
              Logic.all v (Logic.mk_implies (HOLogic.mk_Trueprop (disc $ v),
                HOLogic.mk_Trueprop (HOLogic.mk_not (disc' $ v))));
            fun prove tac goal = Skip_Proof.prove lthy [] [] goal (K tac);

            val bundles = ms ~~ discD_thms ~~ discs;
            val half_pairss = mk_half_pairss bundles;

            val goal_halvess = map (map mk_goal) half_pairss;
            val half_thmss =
              map3 (fn [] => K (K [])
                     | [(((m, discD), _), _)] => fn disc_thm => fn [goal] =>
                [prove (mk_half_disc_exclus_tac m discD disc_thm) goal])
              half_pairss (flat disc_thmss') goal_halvess;

            val goal_other_halvess = map (map (mk_goal o swap)) half_pairss;
            val other_half_thmss =
              map2 (map2 (prove o mk_other_half_disc_exclus_tac)) half_thmss goal_other_halvess;
          in
            interleave (flat half_thmss) (flat other_half_thmss)
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
            val goal = mk_Trueprop_eq (caseofB_fs $ v, mk_rhs discs fs selss);
          in
            Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
              mk_case_disc_tac ctxt exhaust_thm' case_thms disc_thmss' sel_thmss)
            |> singleton (Proof_Context.export names_lthy lthy)
          end;

        val (case_cong_thm, weak_case_cong_thm) =
          let
            fun mk_prem xctr xs f g =
              fold_rev Logic.all xs (Logic.mk_implies (mk_Trueprop_eq (w, xctr),
                mk_Trueprop_eq (f, g)));

            val v_eq_w = mk_Trueprop_eq (v, w);
            val caseof_fs = mk_caseofB_term eta_fs;
            val caseof_gs = mk_caseofB_term eta_gs;

            val goal =
              Logic.list_implies (v_eq_w :: map4 mk_prem xctrs xss fs gs,
                 mk_Trueprop_eq (caseof_fs $ v, caseof_gs $ w));
            val goal_weak =
              Logic.mk_implies (v_eq_w, mk_Trueprop_eq (caseof_fs $ v, caseof_fs $ w));
          in
            (Skip_Proof.prove lthy [] [] goal (fn _ => mk_case_cong_tac exhaust_thm' case_thms),
             Skip_Proof.prove lthy [] [] goal_weak (K (etac arg_cong 1)))
            |> pairself (singleton (Proof_Context.export names_lthy lthy))
          end;

        val (split_thm, split_asm_thm) =
          let
            fun mk_conjunct xctr xs f_xs =
              list_all_free xs (HOLogic.mk_imp (HOLogic.mk_eq (v, xctr), q $ f_xs));
            fun mk_disjunct xctr xs f_xs =
              list_exists_free xs (HOLogic.mk_conj (HOLogic.mk_eq (v, xctr),
                HOLogic.mk_not (q $ f_xs)));

            val lhs = q $ (mk_caseofB_term eta_fs $ v);

            val goal =
              mk_Trueprop_eq (lhs, Library.foldr1 HOLogic.mk_conj (map3 mk_conjunct xctrs xss xfs));
            val goal_asm =
              mk_Trueprop_eq (lhs, HOLogic.mk_not (Library.foldr1 HOLogic.mk_disj
                (map3 mk_disjunct xctrs xss xfs)));

            val split_thm =
              Skip_Proof.prove lthy [] [] goal
                (fn _ => mk_split_tac exhaust_thm' case_thms inject_thmss distinct_thmsss)
              |> singleton (Proof_Context.export names_lthy lthy)
            val split_asm_thm =
              Skip_Proof.prove lthy [] [] goal_asm (fn {context = ctxt, ...} =>
                mk_split_asm_tac ctxt split_thm)
              |> singleton (Proof_Context.export names_lthy lthy)
          in
            (split_thm, split_asm_thm)
          end;

        (* TODO: case syntax *)
        (* TODO: attributes (simp, case_names, etc.) *)

        val notes =
          [(case_congN, [case_cong_thm]),
           (case_discsN, [case_disc_thm]),
           (casesN, case_thms),
           (ctr_selsN, ctr_sel_thms),
           (discsN, (flat disc_thmss)),
           (disc_exclusN, disc_exclus_thms),
           (disc_exhaustN, [disc_exhaust_thm]),
           (distinctN, distinct_thms),
           (exhaustN, [exhaust_thm]),
           (injectN, (flat inject_thmss)),
           (nchotomyN, [nchotomy_thm]),
           (selsN, (flat sel_thmss)),
           (splitN, [split_thm]),
           (split_asmN, [split_asm_thm]),
           (weak_case_cong_thmsN, [weak_case_cong_thm])]
          |> map (fn (thmN, thms) =>
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));
      in
        lthy |> Local_Theory.notes notes |> snd
      end;
  in
    (goals, after_qed, lthy')
  end;

val parse_bindings = Parse.$$$ "[" |--  Parse.list Parse.binding --| Parse.$$$ "]";

val parse_bindingss = Parse.$$$ "[" |-- Parse.list parse_bindings --| Parse.$$$ "]";

val wrap_data_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE after_qed (map (map (rpair [])) goalss) lthy) oo
  prepare_wrap Syntax.read_term;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "wrap_data"} "wraps an existing datatype"
    (((Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") -- Parse.term --
      Scan.optional (parse_bindings -- Scan.optional parse_bindingss []) ([], []))
     >> wrap_data_cmd);

end;
