(*  Title:      HOL/Codatatype/Tools/bnf_wrap.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Wrapping existing datatypes.
*)

signature BNF_WRAP =
sig
  val no_binder: binding
  val mk_half_pairss: 'a list -> ('a * 'a) list list
  val wrap_data: ({prems: thm list, context: Proof.context} -> tactic) list list ->
    (term list * term) * (binding list * binding list list) -> local_theory -> local_theory
end;

structure BNF_Wrap : BNF_WRAP =
struct

open BNF_Util
open BNF_Wrap_Tactics

val is_N = "is_";
val un_N = "un_";
fun mk_un_N 1 1 suf = un_N ^ suf
  | mk_un_N _ l suf = un_N ^ suf ^ string_of_int l;

val case_congN = "case_cong";
val case_eqN = "case_eq";
val casesN = "cases";
val collapseN = "collapse";
val disc_excludeN = "disc_exclude";
val disc_exhaustN = "disc_exhaust";
val discsN = "discs";
val distinctN = "distinct";
val exhaustN = "exhaust";
val injectN = "inject";
val nchotomyN = "nchotomy";
val selsN = "sels";
val splitN = "split";
val split_asmN = "split_asm";
val weak_case_cong_thmsN = "weak_case_cong";

val no_binder = @{binding ""};
val fallback_binder = @{binding _};

fun pad_list x n xs = xs @ replicate (n - length xs) x;

fun mk_half_pairss' _ [] = []
  | mk_half_pairss' indent (y :: ys) =
    indent @ fold_rev (cons o single o pair y) ys (mk_half_pairss' ([] :: indent) ys);

fun mk_half_pairss ys = mk_half_pairss' [[]] ys;

(* TODO: provide a way to have a different default value, e.g. "tl Nil = Nil" *)
fun mk_undef T Ts = Const (@{const_name undefined}, Ts ---> T);

fun eta_expand_case_arg xs f_xs = fold_rev Term.lambda xs f_xs;

fun name_of_ctr t =
  case head_of t of
    Const (s, _) => s
  | Free (s, _) => s
  | _ => error "Cannot extract name of constructor";

fun prepare_wrap_data prep_term ((raw_ctrs, raw_case), (raw_disc_binders, raw_sel_binderss))
  no_defs_lthy =
  let
    (* TODO: sanity checks on arguments *)
    (* TODO: attributes (simp, case_names, etc.) *)
    (* TODO: case syntax *)
    (* TODO: integration with function package ("size") *)

    val ctrs0 = map (prep_term no_defs_lthy) raw_ctrs;
    val case0 = prep_term no_defs_lthy raw_case;

    val n = length ctrs0;
    val ks = 1 upto n;

    val _ = if n > 0 then () else error "No constructors specified";

    val Type (T_name, As0) = body_type (fastype_of (hd ctrs0));
    val b = Binding.qualified_name T_name;

    val (As, B) =
      no_defs_lthy
      |> mk_TFrees (length As0)
      ||> the_single o fst o mk_TFrees 1;

    fun mk_ctr Ts ctr =
      let val Type (_, Ts0) = body_type (fastype_of ctr) in
        Term.subst_atomic_types (Ts0 ~~ Ts) ctr
      end;

    val T = Type (T_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val ms = map length ctr_Tss;

    val raw_disc_binders' = pad_list no_binder n raw_disc_binders;

    fun can_really_rely_on_disc k =
      not (Binding.eq_name (nth raw_disc_binders' (k - 1), no_binder)) orelse nth ms (k - 1) = 0;
    fun can_rely_on_disc k =
      can_really_rely_on_disc k orelse (k = 1 andalso not (can_really_rely_on_disc 2));
    fun can_omit_disc_binder k m =
      n = 1 orelse m = 0 orelse (n = 2 andalso can_rely_on_disc (3 - k));

    val fallback_disc_binder = Binding.name o prefix is_N o Long_Name.base_name o name_of_ctr;

    val disc_binders =
      raw_disc_binders'
      |> map4 (fn k => fn m => fn ctr => fn disc =>
        if Binding.eq_name (disc, no_binder) then
          if can_omit_disc_binder k m then NONE else SOME (fallback_disc_binder ctr)
        else if Binding.eq_name (disc, fallback_binder) then
          SOME (fallback_disc_binder ctr)
        else
          SOME disc) ks ms ctrs0;

    val no_discs = map is_none disc_binders;
    val no_discs_at_all = forall I no_discs;

    fun fallback_sel_binder m l = Binding.name o mk_un_N m l o Long_Name.base_name o name_of_ctr;

    val sel_binderss =
      pad_list [] n raw_sel_binderss
      |> map3 (fn ctr => fn m => map2 (fn l => fn sel =>
        if Binding.eq_name (sel, no_binder) orelse Binding.eq_name (sel, fallback_binder) then
          fallback_sel_binder m l ctr
        else
          sel) (1 upto m) o pad_list no_binder m) ctrs0 ms;

    fun mk_case Ts T =
      let
        val (binders, body) = strip_type (fastype_of case0)
        val Type (_, Ts0) = List.last binders
      in Term.subst_atomic_types ((body, T) :: (Ts0 ~~ Ts)) case0 end;

    val caseB = mk_case As B;
    val caseB_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    fun mk_caseB_term eta_fs = Term.list_comb (caseB, eta_fs);

    val (((((((xss, yss), fs), gs), (v, v')), w), (p, p')), names_lthy) = no_defs_lthy |>
      mk_Freess "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" caseB_Ts
      ||>> mk_Frees "g" caseB_Ts
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") T
      ||>> yield_singleton (mk_Frees "w") T
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "P") HOLogic.boolT;

    val q = Free (fst p', B --> HOLogic.boolT);

    fun mk_v_eq_v () = HOLogic.mk_eq (v, v);

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;

    val xfs = map2 (curry Term.list_comb) fs xss;
    val xgs = map2 (curry Term.list_comb) gs xss;

    val eta_fs = map2 eta_expand_case_arg xss xfs;
    val eta_gs = map2 eta_expand_case_arg xss xgs;

    val caseB_fs = Term.list_comb (caseB, eta_fs);

    val exist_xs_v_eq_ctrs =
      map2 (fn xctr => fn xs => list_exists_free xs (HOLogic.mk_eq (v, xctr))) xctrs xss;

    fun mk_sel_case_args k xs x T =
      map2 (fn Ts => fn i => if i = k then fold_rev Term.lambda xs x else mk_undef T Ts) ctr_Tss ks;

    fun disc_free b = Free (Binding.name_of b, T --> HOLogic.boolT);

    fun disc_spec b exist_xs_v_eq_ctr = mk_Trueprop_eq (disc_free b $ v, exist_xs_v_eq_ctr);

    fun alternate_disc_lhs k =
      HOLogic.mk_not
        (case nth disc_binders (k - 1) of
          NONE => nth exist_xs_v_eq_ctrs (k - 1)
        | SOME b => disc_free b $ v);

    fun alternate_disc k =
      if n = 2 then Term.lambda v (alternate_disc_lhs (3 - k)) else error "Cannot use \"*\" here"

    fun sel_spec b x xs k =
      let val T' = fastype_of x in
        mk_Trueprop_eq (Free (Binding.name_of b, T --> T') $ v,
          Term.list_comb (mk_case As T', mk_sel_case_args k xs x T') $ v)
      end;

    val missing_unique_disc_def = TrueI; (*arbitrary marker*)
    val missing_alternate_disc_def = FalseE; (*arbitrary marker*)

    (* TODO: Allow use of same selector for several constructors *)
    (* TODO: Allow use of same name for datatype and for constructor, e.g. "data L = L" *)

    val (((raw_discs, raw_disc_defs), (raw_selss, raw_sel_defss)), (lthy', lthy)) =
      no_defs_lthy
      |> apfst split_list o fold_map4 (fn k => fn m => fn exist_xs_v_eq_ctr =>
        fn NONE =>
           if n = 1 then pair (Term.lambda v (mk_v_eq_v ()), missing_unique_disc_def)
           else if m = 0 then pair (Term.lambda v exist_xs_v_eq_ctr, refl)
           else pair (alternate_disc k, missing_alternate_disc_def)
         | SOME b => Specification.definition (SOME (b, NONE, NoSyn),
             ((Thm.def_binding b, []), disc_spec b exist_xs_v_eq_ctr)) #>> apsnd snd)
        ks ms exist_xs_v_eq_ctrs disc_binders
      ||>> apfst split_list o fold_map3 (fn bs => fn xs => fn k => apfst split_list o
          fold_map2 (fn b => fn x => Specification.definition (SOME (b, NONE, NoSyn),
            ((Thm.def_binding b, []), sel_spec b x xs k)) #>> apsnd snd) bs xs) sel_binderss xss ks
      ||> `Local_Theory.restore;

    (*transforms defined frees into consts (and more)*)
    val phi = Proof_Context.export_morphism lthy lthy';

    val disc_defs = map (Morphism.thm phi) raw_disc_defs;
    val sel_defss = map (map (Morphism.thm phi)) raw_sel_defss;

    val discs0 = map (Morphism.term phi) raw_discs;
    val selss0 = map (map (Morphism.term phi)) raw_selss;

    fun mk_disc_or_sel Ts t =
      Term.subst_atomic_types (snd (Term.dest_Type (domain_type (fastype_of t))) ~~ Ts) t;

    val discs = map (mk_disc_or_sel As) discs0;
    val selss = map (map (mk_disc_or_sel As)) selss0;

    fun mk_imp_p Qs = Logic.list_implies (Qs, HOLogic.mk_Trueprop p);

    val goal_exhaust =
      let fun mk_prem xctr xs = fold_rev Logic.all xs (mk_imp_p [mk_Trueprop_eq (v, xctr)]) in
        fold_rev Logic.all [p, v] (mk_imp_p (map2 mk_prem xctrs xss))
      end;

    val goal_injectss =
      let
        fun mk_goal _ _ [] [] = []
          | mk_goal xctr yctr xs ys =
            [fold_rev Logic.all (xs @ ys) (mk_Trueprop_eq (HOLogic.mk_eq (xctr, yctr),
              Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys)))];
      in
        map4 mk_goal xctrs yctrs xss yss
      end;

    val goal_half_distinctss =
      let
        fun mk_goal ((xs, t), (xs', t')) =
          fold_rev Logic.all (xs @ xs')
            (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (t, t'))));
      in
        map (map mk_goal) (mk_half_pairss (xss ~~ xctrs))
      end;

    val goal_cases =
      map3 (fn xs => fn xctr => fn xf =>
        fold_rev Logic.all (fs @ xs) (mk_Trueprop_eq (caseB_fs $ xctr, xf))) xss xctrs xfs;

    val goalss = [goal_exhaust] :: goal_injectss @ goal_half_distinctss @ [goal_cases];

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
                val cxs = map (certify lthy) (mk_sel_case_args k xs x T);
              in
                Local_Defs.fold lthy [sel_def]
                  (Drule.instantiate' (map SOME cTs) (map SOME cxs) case_thm)
              end;
            fun mk_thms k xs goal_case case_thm sel_defs =
              map2 (mk_thm k xs (strip_all_body goal_case) case_thm) xs sel_defs;
          in
            map5 mk_thms ks xss goal_cases case_thms sel_defss
          end;

        fun mk_unique_disc_def () =
          let
            val m = the_single ms;
            val goal = mk_Trueprop_eq (mk_v_eq_v (), the_single exist_xs_v_eq_ctrs);
          in
            Skip_Proof.prove lthy [] [] goal (fn _ => mk_unique_disc_def_tac m exhaust_thm')
            |> singleton (Proof_Context.export names_lthy lthy)
            |> Thm.close_derivation
          end;

        fun mk_alternate_disc_def k =
          let
            val goal =
              mk_Trueprop_eq (Morphism.term phi (alternate_disc_lhs (3 - k)),
                nth exist_xs_v_eq_ctrs (k - 1));
          in
            Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
              mk_alternate_disc_def_tac ctxt k (nth disc_defs (2 - k)) (nth distinct_thms (2 - k))
                exhaust_thm')
            |> singleton (Proof_Context.export names_lthy lthy)
            |> Thm.close_derivation
          end;

        val has_alternate_disc_def =
          exists (fn def => Thm.eq_thm_prop (def, missing_alternate_disc_def)) disc_defs;

        val disc_defs' =
          map2 (fn k => fn def =>
            if Thm.eq_thm_prop (def, missing_unique_disc_def) then mk_unique_disc_def ()
            else if Thm.eq_thm_prop (def, missing_alternate_disc_def) then mk_alternate_disc_def k
            else def)
          ks disc_defs;

        val discD_thms = map (fn def => def RS iffD1) disc_defs';
        val discI_thms =
          map2 (fn m => fn def => funpow m (fn thm => exI RS thm) (def RS iffD2)) ms disc_defs';
        val not_discI_thms =
          map2 (fn m => fn def => funpow m (fn thm => allI RS thm)
            (Local_Defs.unfold lthy @{thms not_ex} (def RS @{thm ssubst[of _ _ Not]})))
          ms disc_defs';

        val (disc_thmss', disc_thmss) =
          let
            fun mk_thm discI _ [] = refl RS discI
              | mk_thm _ not_discI [distinct] = distinct RS not_discI;
            fun mk_thms discI not_discI distinctss = map (mk_thm discI not_discI) distinctss;
          in
            map3 mk_thms discI_thms not_discI_thms distinct_thmsss' |> `transpose
          end;

        val disc_thms = flat (map2 (fn true => K [] | false => I) no_discs disc_thmss);

        val disc_exclude_thms =
          if has_alternate_disc_def then
            []
          else
            let
              fun mk_goal [] = []
                | mk_goal [((_, true), (_, true))] = []
                | mk_goal [(((_, disc), _), ((_, disc'), _))] =
                  [Logic.all v (Logic.mk_implies (HOLogic.mk_Trueprop (betapply (disc, v)),
                     HOLogic.mk_Trueprop (HOLogic.mk_not (betapply (disc', v)))))];
              fun prove tac goal = Skip_Proof.prove lthy [] [] goal (K tac);

              val bundles = ms ~~ discD_thms ~~ discs ~~ no_discs;
              val half_pairss = mk_half_pairss bundles;

              val goal_halvess = map mk_goal half_pairss;
              val half_thmss =
                map3 (fn [] => K (K []) | [goal] => fn [((((m, discD), _), _), _)] => fn disc_thm =>
                  [prove (mk_half_disc_exclude_tac m discD disc_thm) goal])
                goal_halvess half_pairss (flat disc_thmss');

              val goal_other_halvess = map (mk_goal o map swap) half_pairss;
              val other_half_thmss =
                map2 (map2 (prove o mk_other_half_disc_exclude_tac)) half_thmss goal_other_halvess;
            in
              interleave (flat half_thmss) (flat other_half_thmss)
            end;

        val disc_exhaust_thms =
          if has_alternate_disc_def orelse no_discs_at_all then
            []
          else
            let
              fun mk_prem disc = mk_imp_p [HOLogic.mk_Trueprop (betapply (disc, v))];
              val goal = fold_rev Logic.all [p, v] (mk_imp_p (map mk_prem discs));
            in
              [Skip_Proof.prove lthy [] [] goal (fn _ =>
                 mk_disc_exhaust_tac n exhaust_thm discI_thms)]
            end;

        val collapse_thms =
          let
            fun mk_goal ctr disc sels =
              let
                val prem = HOLogic.mk_Trueprop (betapply (disc, v));
                val concl =
                  mk_Trueprop_eq ((null sels ? swap)
                    (Term.list_comb (ctr, map (fn sel => sel $ v) sels), v));
              in
                if prem aconv concl then NONE
                else SOME (Logic.all v (Logic.mk_implies (prem, concl)))
              end;
            val goals = map3 mk_goal ctrs discs selss;
          in
            map4 (fn m => fn discD => fn sel_thms => Option.map (fn goal =>
              Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                mk_collapse_tac ctxt m discD sel_thms)
              |> perhaps (try (fn thm => refl RS thm)))) ms discD_thms sel_thmss goals
            |> map_filter I
          end;

        val case_eq_thm =
          let
            fun mk_core f sels = Term.list_comb (f, map (fn sel => sel $ v) sels);
            fun mk_rhs _ [f] [sels] = mk_core f sels
              | mk_rhs (disc :: discs) (f :: fs) (sels :: selss) =
                Const (@{const_name If}, HOLogic.boolT --> B --> B --> B) $
                  betapply (disc, v) $ mk_core f sels $ mk_rhs discs fs selss;
            val goal = mk_Trueprop_eq (caseB_fs $ v, mk_rhs discs fs selss);
          in
            Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
              mk_case_eq_tac ctxt n exhaust_thm' case_thms disc_thmss' sel_thmss)
            |> singleton (Proof_Context.export names_lthy lthy)
          end;

        val (case_cong_thm, weak_case_cong_thm) =
          let
            fun mk_prem xctr xs f g =
              fold_rev Logic.all xs (Logic.mk_implies (mk_Trueprop_eq (w, xctr),
                mk_Trueprop_eq (f, g)));

            val v_eq_w = mk_Trueprop_eq (v, w);
            val case_fs = mk_caseB_term eta_fs;
            val case_gs = mk_caseB_term eta_gs;

            val goal =
              Logic.list_implies (v_eq_w :: map4 mk_prem xctrs xss fs gs,
                 mk_Trueprop_eq (case_fs $ v, case_gs $ w));
            val goal_weak = Logic.mk_implies (v_eq_w, mk_Trueprop_eq (case_fs $ v, case_fs $ w));
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

            val lhs = q $ (mk_caseB_term eta_fs $ v);

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

        val notes =
          [(case_congN, [case_cong_thm]),
           (case_eqN, [case_eq_thm]),
           (casesN, case_thms),
           (collapseN, collapse_thms),
           (discsN, disc_thms),
           (disc_excludeN, disc_exclude_thms),
           (disc_exhaustN, disc_exhaust_thms),
           (distinctN, distinct_thms),
           (exhaustN, [exhaust_thm]),
           (injectN, flat inject_thmss),
           (nchotomyN, [nchotomy_thm]),
           (selsN, flat sel_thmss),
           (splitN, [split_thm]),
           (split_asmN, [split_asm_thm]),
           (weak_case_cong_thmsN, [weak_case_cong_thm])]
          |> filter_out (null o snd)
          |> map (fn (thmN, thms) =>
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]));
      in
        lthy |> Local_Theory.notes notes |> snd
      end;
  in
    (goalss, after_qed, lthy')
  end;

fun wrap_data tacss = (fn (goalss, after_qed, lthy) =>
  map2 (map2 (Skip_Proof.prove lthy [] [])) goalss tacss
  |> (fn thms => after_qed thms lthy)) oo
  prepare_wrap_data (K I) (* FIXME? (singleton o Type_Infer_Context.infer_types) *)

val parse_bindings = Parse.$$$ "[" |-- Parse.list Parse.binding --| Parse.$$$ "]";
val parse_bindingss = Parse.$$$ "[" |-- Parse.list parse_bindings --| Parse.$$$ "]";

val wrap_data_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE after_qed (map (map (rpair [])) goalss) lthy) oo
  prepare_wrap_data Syntax.read_term;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "wrap_data"} "wraps an existing datatype"
    (((Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") -- Parse.term --
      Scan.optional (parse_bindings -- Scan.optional parse_bindingss []) ([], []))
     >> wrap_data_cmd);

end;
