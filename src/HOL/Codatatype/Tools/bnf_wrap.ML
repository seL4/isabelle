(*  Title:      HOL/Codatatype/Tools/bnf_wrap.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Wrapping existing datatypes.
*)

signature BNF_WRAP =
sig
  val no_binding: binding
  val mk_half_pairss: 'a list -> ('a * 'a) list list
  val mk_ctr: typ list -> term -> term
  val wrap_datatype: ({prems: thm list, context: Proof.context} -> tactic) list list ->
    ((bool * term list) * term) *
      (binding list * (binding list list * (binding * term) list list)) -> local_theory ->
    (term list list * thm list * thm list list) * local_theory
  val parse_wrap_options: bool parser
  val parse_bound_term: (binding * string) parser
end;

structure BNF_Wrap : BNF_WRAP =
struct

open BNF_Util
open BNF_Wrap_Tactics

val isN = "is_";
val unN = "un_";
fun mk_unN 1 1 suf = unN ^ suf
  | mk_unN _ l suf = unN ^ suf ^ string_of_int l;

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

val no_binding = @{binding ""};
val std_binding = @{binding _};

val induct_simp_attrs = @{attributes [induct_simp]};
val cong_attrs = @{attributes [cong]};
val iff_attrs = @{attributes [iff]};
val safe_elim_attrs = @{attributes [elim!]};
val simp_attrs = @{attributes [simp]};

fun pad_list x n xs = xs @ replicate (n - length xs) x;

fun unflat_lookup eq ys zs = map (map (fn x => nth zs (find_index (curry eq x) ys)));

fun mk_half_pairss' _ [] = []
  | mk_half_pairss' indent (y :: ys) =
    indent @ fold_rev (cons o single o pair y) ys (mk_half_pairss' ([] :: indent) ys);

fun mk_half_pairss ys = mk_half_pairss' [[]] ys;

fun mk_undefined T = Const (@{const_name undefined}, T);

fun mk_ctr Ts ctr =
  let val Type (_, Ts0) = body_type (fastype_of ctr) in
    Term.subst_atomic_types (Ts0 ~~ Ts) ctr
  end;

fun eta_expand_case_arg xs f_xs = fold_rev Term.lambda xs f_xs;

fun base_name_of_ctr c =
  Long_Name.base_name (case head_of c of
      Const (s, _) => s
    | Free (s, _) => s
    | _ => error "Cannot extract name of constructor");

fun prepare_wrap_datatype prep_term (((no_dests, raw_ctrs), raw_case),
    (raw_disc_bindings, (raw_sel_bindingss, raw_sel_defaultss))) no_defs_lthy =
  let
    (* TODO: sanity checks on arguments *)
    (* TODO: attributes (simp, case_names, etc.) *)
    (* TODO: case syntax *)
    (* TODO: integration with function package ("size") *)

    val n = length raw_ctrs;
    val ks = 1 upto n;

    val _ = if n > 0 then () else error "No constructors specified";

    val ctrs0 = map (prep_term no_defs_lthy) raw_ctrs;
    val case0 = prep_term no_defs_lthy raw_case;
    val sel_defaultss =
      pad_list [] n (map (map (apsnd (prep_term no_defs_lthy))) raw_sel_defaultss);

    val Type (dataT_name, As0) = body_type (fastype_of (hd ctrs0));
    val data_b = Binding.qualified_name dataT_name;

    val (As, B) =
      no_defs_lthy
      |> mk_TFrees' (map Type.sort_of_atyp As0)
      ||> the_single o fst o mk_TFrees 1;

    val dataT = Type (dataT_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val ms = map length ctr_Tss;

    val raw_disc_bindings' = pad_list no_binding n raw_disc_bindings;

    fun can_really_rely_on_disc k =
      not (Binding.eq_name (nth raw_disc_bindings' (k - 1), no_binding)) orelse nth ms (k - 1) = 0;
    fun can_rely_on_disc k =
      can_really_rely_on_disc k orelse (k = 1 andalso not (can_really_rely_on_disc 2));
    fun can_omit_disc_binding k m =
      n = 1 orelse m = 0 orelse (n = 2 andalso can_rely_on_disc (3 - k));

    val std_disc_binding =
      Binding.qualify false (Binding.name_of data_b) o Binding.name o prefix isN o base_name_of_ctr;

    val disc_bindings =
      raw_disc_bindings'
      |> map4 (fn k => fn m => fn ctr => fn disc =>
        Option.map (Binding.qualify false (Binding.name_of data_b))
          (if Binding.eq_name (disc, no_binding) then
             if can_omit_disc_binding k m then NONE else SOME (std_disc_binding ctr)
           else if Binding.eq_name (disc, std_binding) then
             SOME (std_disc_binding ctr)
           else
             SOME disc)) ks ms ctrs0;

    val no_discs = map is_none disc_bindings;
    val no_discs_at_all = forall I no_discs;

    fun std_sel_binding m l = Binding.name o mk_unN m l o base_name_of_ctr;

    val sel_bindingss =
      pad_list [] n raw_sel_bindingss
      |> map3 (fn ctr => fn m => map2 (fn l => fn sel =>
        Binding.qualify false (Binding.name_of data_b)
          (if Binding.eq_name (sel, no_binding) orelse Binding.eq_name (sel, std_binding) then
            std_sel_binding m l ctr
          else
            sel)) (1 upto m) o pad_list no_binding m) ctrs0 ms;

    fun mk_case Ts T =
      let
        val (bindings, body) = strip_type (fastype_of case0)
        val Type (_, Ts0) = List.last bindings
      in Term.subst_atomic_types ((body, T) :: (Ts0 ~~ Ts)) case0 end;

    val casex = mk_case As B;
    val case_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    val ((((((((xss, xss'), yss), fs), gs), (v, v')), w), (p, p')), names_lthy) = no_defs_lthy |>
      mk_Freess' "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" case_Ts
      ||>> mk_Frees "g" case_Ts
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") dataT
      ||>> yield_singleton (mk_Frees "w") dataT
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "P") HOLogic.boolT;

    val q = Free (fst p', B --> HOLogic.boolT);

    fun ap_v t = t $ v;
    fun mk_v_eq_v () = HOLogic.mk_eq (v, v);

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;

    val xfs = map2 (curry Term.list_comb) fs xss;
    val xgs = map2 (curry Term.list_comb) gs xss;

    val eta_fs = map2 eta_expand_case_arg xss xfs;
    val eta_gs = map2 eta_expand_case_arg xss xgs;

    val fcase = Term.list_comb (casex, eta_fs);
    val gcase = Term.list_comb (casex, eta_gs);

    val exist_xs_v_eq_ctrs =
      map2 (fn xctr => fn xs => list_exists_free xs (HOLogic.mk_eq (v, xctr))) xctrs xss;

    val unique_disc_no_def = TrueI; (*arbitrary marker*)
    val alternate_disc_no_def = FalseE; (*arbitrary marker*)

    fun alternate_disc_lhs get_disc k =
      HOLogic.mk_not
        (case nth disc_bindings (k - 1) of
          NONE => nth exist_xs_v_eq_ctrs (k - 1)
        | SOME b => get_disc b (k - 1) $ v);

    val (all_sels_distinct, discs, selss, disc_defs, sel_defs, sel_defss, lthy') =
      if no_dests then
        (true, [], [], [], [], [], no_defs_lthy)
      else
        let
          fun disc_free b = Free (Binding.name_of b, dataT --> HOLogic.boolT);

          fun disc_spec b exist_xs_v_eq_ctr = mk_Trueprop_eq (disc_free b $ v, exist_xs_v_eq_ctr);

          fun alternate_disc k = Term.lambda v (alternate_disc_lhs (K o disc_free) (3 - k));

          fun mk_default T t =
            let
              val Ts0 = map TFree (Term.add_tfreesT (fastype_of t) []);
              val Ts = map TFree (Term.add_tfreesT T []);
            in Term.subst_atomic_types (Ts0 ~~ Ts) t end;

          fun mk_sel_case_args b proto_sels T =
            map2 (fn Ts => fn k =>
              (case AList.lookup (op =) proto_sels k of
                NONE =>
                (case AList.lookup Binding.eq_name (rev (nth sel_defaultss (k - 1))) b of
                  NONE => fold_rev (Term.lambda o curry Free Name.uu) Ts (mk_undefined T)
                | SOME t => mk_default (Ts ---> T) t)
              | SOME (xs, x) => fold_rev Term.lambda xs x)) ctr_Tss ks;

          fun sel_spec b proto_sels =
            let
              val _ =
                (case duplicates (op =) (map fst proto_sels) of
                   k :: _ => error ("Duplicate selector name " ^ quote (Binding.name_of b) ^
                     " for constructor " ^
                     quote (Syntax.string_of_term no_defs_lthy (nth ctrs (k - 1))))
                 | [] => ())
              val T =
                (case distinct (op =) (map (fastype_of o snd o snd) proto_sels) of
                  [T] => T
                | T :: T' :: _ => error ("Inconsistent range type for selector " ^
                    quote (Binding.name_of b) ^ ": " ^ quote (Syntax.string_of_typ no_defs_lthy T) ^
                    " vs. " ^ quote (Syntax.string_of_typ no_defs_lthy T')));
            in
              mk_Trueprop_eq (Free (Binding.name_of b, dataT --> T) $ v,
                Term.list_comb (mk_case As T, mk_sel_case_args b proto_sels T) $ v)
            end;

          val sel_bindings = flat sel_bindingss;
          val uniq_sel_bindings = distinct Binding.eq_name sel_bindings;
          val all_sels_distinct = (length uniq_sel_bindings = length sel_bindings);

          val sel_binding_index =
            if all_sels_distinct then 1 upto length sel_bindings
            else map (fn b => find_index (curry Binding.eq_name b) uniq_sel_bindings) sel_bindings;

          val proto_sels = flat (map3 (fn k => fn xs => map (fn x => (k, (xs, x)))) ks xss xss);
          val sel_infos =
            AList.group (op =) (sel_binding_index ~~ proto_sels)
            |> sort (int_ord o pairself fst)
            |> map snd |> curry (op ~~) uniq_sel_bindings;
          val sel_bindings = map fst sel_infos;

          fun unflat_selss xs = unflat_lookup Binding.eq_name sel_bindings xs sel_bindingss;

          val (((raw_discs, raw_disc_defs), (raw_sels, raw_sel_defs)), (lthy', lthy)) =
            no_defs_lthy
            |> apfst split_list o fold_map4 (fn k => fn m => fn exist_xs_v_eq_ctr =>
              fn NONE =>
                 if n = 1 then pair (Term.lambda v (mk_v_eq_v ()), unique_disc_no_def)
                 else if m = 0 then pair (Term.lambda v exist_xs_v_eq_ctr, refl)
                 else pair (alternate_disc k, alternate_disc_no_def)
               | SOME b => Specification.definition (SOME (b, NONE, NoSyn),
                   ((Thm.def_binding b, []), disc_spec b exist_xs_v_eq_ctr)) #>> apsnd snd)
              ks ms exist_xs_v_eq_ctrs disc_bindings
            ||>> apfst split_list o fold_map (fn (b, proto_sels) =>
              Specification.definition (SOME (b, NONE, NoSyn),
                ((Thm.def_binding b, []), sel_spec b proto_sels)) #>> apsnd snd) sel_infos
            ||> `Local_Theory.restore;

          val phi = Proof_Context.export_morphism lthy lthy';

          val disc_defs = map (Morphism.thm phi) raw_disc_defs;
          val sel_defs = map (Morphism.thm phi) raw_sel_defs;
          val sel_defss = unflat_selss sel_defs;

          val discs0 = map (Morphism.term phi) raw_discs;
          val selss0 = unflat_selss (map (Morphism.term phi) raw_sels);

          fun mk_disc_or_sel Ts c =
            Term.subst_atomic_types (snd (Term.dest_Type (domain_type (fastype_of c))) ~~ Ts) c;

          val discs = map (mk_disc_or_sel As) discs0;
          val selss = map (map (mk_disc_or_sel As)) selss0;
        in
          (all_sels_distinct, discs, selss, disc_defs, sel_defs, sel_defss, lthy')
        end;

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
        fun mk_goal ((xs, xc), (xs', xc')) =
          fold_rev Logic.all (xs @ xs')
            (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (xc, xc'))));
      in
        map (map mk_goal) (mk_half_pairss (xss ~~ xctrs))
      end;

    val goal_cases =
      map3 (fn xs => fn xctr => fn xf =>
        fold_rev Logic.all (fs @ xs) (mk_Trueprop_eq (fcase $ xctr, xf))) xss xctrs xfs;

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

        val exhaust_cases = map base_name_of_ctr ctrs;

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

        val (all_sel_thms, sel_thmss, disc_thms, discI_thms, disc_exclude_thms, disc_exhaust_thms,
             collapse_thms, case_eq_thms) =
          if no_dests then
            ([], [], [], [], [], [], [], [])
          else
            let
              fun make_sel_thm xs' case_thm sel_def =
                zero_var_indexes (Drule.gen_all (Drule.rename_bvars' (map (SOME o fst) xs')
                    (Drule.forall_intr_vars (case_thm RS (sel_def RS trans)))));

              fun has_undefined_rhs thm =
                (case snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (prop_of thm))) of
                  Const (@{const_name undefined}, _) => true
                | _ => false);

              val sel_thmss = map3 (map oo make_sel_thm) xss' case_thms sel_defss;

              val all_sel_thms =
                (if all_sels_distinct andalso forall null sel_defaultss then
                   flat sel_thmss
                 else
                   map_product (fn s => fn (xs', c) => make_sel_thm xs' c s) sel_defs
                     (xss' ~~ case_thms))
                |> filter_out has_undefined_rhs;

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
                    mk_Trueprop_eq (alternate_disc_lhs (K (nth discs)) (3 - k),
                      nth exist_xs_v_eq_ctrs (k - 1));
                in
                  Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                    mk_alternate_disc_def_tac ctxt k (nth disc_defs (2 - k))
                      (nth distinct_thms (2 - k)) exhaust_thm')
                  |> singleton (Proof_Context.export names_lthy lthy)
                  |> Thm.close_derivation
                end;

              val has_alternate_disc_def =
                exists (fn def => Thm.eq_thm_prop (def, alternate_disc_no_def)) disc_defs;

              val disc_defs' =
                map2 (fn k => fn def =>
                  if Thm.eq_thm_prop (def, unique_disc_no_def) then mk_unique_disc_def ()
                  else if Thm.eq_thm_prop (def, alternate_disc_no_def) then mk_alternate_disc_def k
                  else def) ks disc_defs;

              val discD_thms = map (fn def => def RS iffD1) disc_defs';
              val discI_thms =
                map2 (fn m => fn def => funpow m (fn thm => exI RS thm) (def RS iffD2)) ms
                  disc_defs';
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

                    val infos = ms ~~ discD_thms ~~ discs ~~ no_discs;
                    val half_pairss = mk_half_pairss infos;

                    val goal_halvess = map mk_goal half_pairss;
                    val half_thmss =
                      map3 (fn [] => K (K []) | [goal] => fn [((((m, discD), _), _), _)] =>
                          fn disc_thm => [prove (mk_half_disc_exclude_tac m discD disc_thm) goal])
                        goal_halvess half_pairss (flat disc_thmss');

                    val goal_other_halvess = map (mk_goal o map swap) half_pairss;
                    val other_half_thmss =
                      map2 (map2 (prove o mk_other_half_disc_exclude_tac)) half_thmss
                        goal_other_halvess;
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
                if no_dests then
                  []
                else
                  let
                    fun mk_goal ctr disc sels =
                      let
                        val prem = HOLogic.mk_Trueprop (betapply (disc, v));
                        val concl =
                          mk_Trueprop_eq ((null sels ? swap)
                            (Term.list_comb (ctr, map ap_v sels), v));
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

              val case_eq_thms =
                if no_dests then
                  []
                else
                  let
                    fun mk_body f sels = Term.list_comb (f, map ap_v sels);
                    val goal =
                      mk_Trueprop_eq (fcase $ v, mk_IfN B (map ap_v discs) (map2 mk_body fs selss));
                  in
                    [Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                      mk_case_eq_tac ctxt n exhaust_thm' case_thms disc_thmss' sel_thmss)]
                    |> Proof_Context.export names_lthy lthy
                  end;
            in
              (all_sel_thms, sel_thmss, disc_thms, discI_thms, disc_exclude_thms, disc_exhaust_thms,
               collapse_thms, case_eq_thms)
            end;

        val (case_cong_thm, weak_case_cong_thm) =
          let
            fun mk_prem xctr xs f g =
              fold_rev Logic.all xs (Logic.mk_implies (mk_Trueprop_eq (w, xctr),
                mk_Trueprop_eq (f, g)));

            val v_eq_w = mk_Trueprop_eq (v, w);

            val goal =
              Logic.list_implies (v_eq_w :: map4 mk_prem xctrs xss fs gs,
                 mk_Trueprop_eq (fcase $ v, gcase $ w));
            val goal_weak = Logic.mk_implies (v_eq_w, mk_Trueprop_eq (fcase $ v, fcase $ w));
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

            val lhs = q $ (fcase $ v);

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

        val cases_type_attr = Attrib.internal (K (Induct.cases_type dataT_name));
        val exhaust_case_names_attr = Attrib.internal (K (Rule_Cases.case_names exhaust_cases));

        val notes =
          [(case_congN, [case_cong_thm], []),
           (case_eqN, case_eq_thms, []),
           (casesN, case_thms, simp_attrs),
           (collapseN, collapse_thms, simp_attrs),
           (discsN, disc_thms, simp_attrs),
           (disc_excludeN, disc_exclude_thms, []),
           (disc_exhaustN, disc_exhaust_thms, [exhaust_case_names_attr]),
           (distinctN, distinct_thms, simp_attrs @ induct_simp_attrs),
           (exhaustN, [exhaust_thm], [exhaust_case_names_attr, cases_type_attr]),
           (injectN, flat inject_thmss, iff_attrs @ induct_simp_attrs),
           (nchotomyN, [nchotomy_thm], []),
           (selsN, all_sel_thms, simp_attrs),
           (splitN, [split_thm], []),
           (split_asmN, [split_asm_thm], []),
           (weak_case_cong_thmsN, [weak_case_cong_thm], cong_attrs)]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true (Binding.name_of data_b) (Binding.name thmN), attrs),
             [(thms, [])]));

        val notes' =
          [(map (fn th => th RS notE) distinct_thms, safe_elim_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));
      in
        ((selss, discI_thms, sel_thmss), lthy |> Local_Theory.notes (notes' @ notes) |> snd)
      end;
  in
    (goalss, after_qed, lthy')
  end;

fun wrap_datatype tacss = (fn (goalss, after_qed, lthy) =>
  map2 (map2 (Skip_Proof.prove lthy [] [])) goalss tacss
  |> (fn thms => after_qed thms lthy)) oo prepare_wrap_datatype (K I);

val wrap_datatype_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE (snd oo after_qed) (map (map (rpair [])) goalss) lthy) oo
  prepare_wrap_datatype Syntax.read_term;

fun parse_bracket_list parser = @{keyword "["} |-- Parse.list parser --|  @{keyword "]"};

val parse_bindings = parse_bracket_list Parse.binding;
val parse_bindingss = parse_bracket_list parse_bindings;

val parse_bound_term = (Parse.binding --| @{keyword ":"}) -- Parse.term;
val parse_bound_terms = parse_bracket_list parse_bound_term;
val parse_bound_termss = parse_bracket_list parse_bound_terms;

val parse_wrap_options =
  Scan.optional (@{keyword "("} |-- (@{keyword "no_dests"} >> K true) --| @{keyword ")"}) false;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "wrap_data"} "wraps an existing datatype"
    ((parse_wrap_options -- (@{keyword "["} |-- Parse.list Parse.term --| @{keyword "]"}) --
      Parse.term -- Scan.optional (parse_bindings -- Scan.optional (parse_bindingss --
        Scan.optional parse_bound_termss []) ([], [])) ([], ([], [])))
     >> wrap_datatype_cmd);

end;
