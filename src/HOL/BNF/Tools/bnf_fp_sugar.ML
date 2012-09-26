(*  Title:      HOL/BNF/Tools/bnf_fp_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugared datatype and codatatype constructions.
*)

signature BNF_FP_SUGAR =
sig
  val datatypes: bool ->
    (mixfix list -> (string * sort) list option -> binding list -> typ list * typ list list ->
      BNF_Def.BNF list -> local_theory -> BNF_FP.fp_result * local_theory) ->
    bool * ((((typ * sort) list * binding) * mixfix) * ((((binding * binding) *
      (binding * typ) list) * (binding * term) list) * mixfix) list) list ->
    local_theory -> local_theory
  val parse_datatype_cmd: bool ->
    (mixfix list -> (string * sort) list option -> binding list -> typ list * typ list list ->
      BNF_Def.BNF list -> local_theory -> BNF_FP.fp_result * local_theory) ->
    (local_theory -> local_theory) parser
end;

structure BNF_FP_Sugar : BNF_FP_SUGAR =
struct

open BNF_Util
open BNF_Wrap
open BNF_Def
open BNF_FP
open BNF_FP_Sugar_Tactics

val mp_conj = @{thm mp_conj};

val simp_attrs = @{attributes [simp]};
val code_simp_attrs = Code.add_default_eqn_attrib :: simp_attrs;

fun split_list4 xs = (map #1 xs, map #2 xs, map #3 xs, map #4 xs);

fun resort_tfree S (TFree (s, _)) = TFree (s, S);

fun typ_subst inst (T as Type (s, Ts)) =
    (case AList.lookup (op =) inst T of
      NONE => Type (s, map (typ_subst inst) Ts)
    | SOME T' => T')
  | typ_subst inst T = the_default T (AList.lookup (op =) inst T);

fun variant_types ss Ss ctxt =
  let
    val (tfrees, _) =
      fold_map2 (fn s => fn S => Name.variant s #> apfst (rpair S)) ss Ss (Variable.names_of ctxt);
    val ctxt' = fold (Variable.declare_constraints o Logic.mk_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;

val lists_bmoc = fold (fn xs => fn t => Term.list_comb (t, xs));

fun mk_tupled_fun x f xs = HOLogic.tupled_lambda x (Term.list_comb (f, xs));
fun mk_uncurried_fun f xs = mk_tupled_fun (HOLogic.mk_tuple xs) f xs;
fun mk_uncurried2_fun f xss =
  mk_tupled_fun (HOLogic.mk_tuple (map HOLogic.mk_tuple xss)) f (flat xss);

fun mk_flip (x, Type (_, [T1, Type (_, [T2, T3])])) =
  Abs ("x", T1, Abs ("y", T2, Var (x, T2 --> T1 --> T3) $ Bound 0 $ Bound 1));

fun flip_rels lthy n thm =
  let
    val Rs = Term.add_vars (prop_of thm) [];
    val Rs' = rev (drop (length Rs - n) Rs);
    val cRs = map (fn f => (certify lthy (Var f), certify lthy (mk_flip f))) Rs';
  in
    Drule.cterm_instantiate cRs thm
  end;

fun mk_ctor_or_dtor get_T Ts t =
  let val Type (_, Ts0) = get_T (fastype_of t) in
    Term.subst_atomic_types (Ts0 ~~ Ts) t
  end;

val mk_ctor = mk_ctor_or_dtor range_type;
val mk_dtor = mk_ctor_or_dtor domain_type;

fun mk_rec_like lfp Ts Us t =
  let
    val (bindings, body) = strip_type (fastype_of t);
    val (f_Us, prebody) = split_last bindings;
    val Type (_, Ts0) = if lfp then prebody else body;
    val Us0 = distinct (op =) (map (if lfp then body_type else domain_type) f_Us);
  in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_map live Ts Us t =
  let val (Type (_, Ts0), Type (_, Us0)) = strip_typeN (live + 1) (fastype_of t) |>> List.last in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_rel live Ts Us t =
  let val [Type (_, Ts0), Type (_, Us0)] = binder_types (snd (strip_typeN live (fastype_of t))) in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun liveness_of_fp_bnf n bnf =
  (case T_of_bnf bnf of
    Type (_, Ts) => map (not o member (op =) (deads_of_bnf bnf)) Ts
  | _ => replicate n false);

fun tick u f = Term.lambda u (HOLogic.mk_prod (u, f $ u));

fun tack z_name (c, u) f =
  let val z = Free (z_name, mk_sumT (fastype_of u, fastype_of c)) in
    Term.lambda z (mk_sum_case (Term.lambda u u, Term.lambda c (f $ c)) $ z)
  end;

fun cannot_merge_types () = error "Mutually recursive types must have the same type parameters";

fun merge_type_arg T T' = if T = T' then T else cannot_merge_types ();

fun merge_type_args (As, As') =
  if length As = length As' then map2 merge_type_arg As As' else cannot_merge_types ();

fun is_triv_implies thm =
  op aconv (Logic.dest_implies (Thm.prop_of thm))
  handle TERM _ => false;

fun reassoc_conjs thm =
  reassoc_conjs (thm RS @{thm conj_assoc[THEN iffD1]})
  handle THM _ => thm;

fun type_args_constrained_of (((cAs, _), _), _) = cAs;
fun type_binding_of (((_, b), _), _) = b;
fun mixfix_of ((_, mx), _) = mx;
fun ctr_specs_of (_, ctr_specs) = ctr_specs;

fun disc_of ((((disc, _), _), _), _) = disc;
fun ctr_of ((((_, ctr), _), _), _) = ctr;
fun args_of (((_, args), _), _) = args;
fun defaults_of ((_, ds), _) = ds;
fun ctr_mixfix_of (_, mx) = mx;

fun define_datatypes prepare_constraint prepare_typ prepare_term lfp construct_fp (no_dests, specs)
    no_defs_lthy0 =
  let
    (* TODO: sanity checks on arguments *)
    (* TODO: integration with function package ("size") *)

    val _ = if not lfp andalso no_dests then error "Cannot define destructor-less codatatypes"
      else ();

    val nn = length specs;
    val fp_bs = map type_binding_of specs;
    val fp_b_names = map Binding.name_of fp_bs;
    val fp_common_name = mk_common_name fp_b_names;

    fun prepare_type_arg (ty, c) =
      let val TFree (s, _) = prepare_typ no_defs_lthy0 ty in
        TFree (s, prepare_constraint no_defs_lthy0 c)
      end;

    val Ass0 = map (map prepare_type_arg o type_args_constrained_of) specs;
    val unsorted_Ass0 = map (map (resort_tfree HOLogic.typeS)) Ass0;
    val unsorted_As = Library.foldr1 merge_type_args unsorted_Ass0;

    val (((Bs0, Cs), Xs), no_defs_lthy) =
      no_defs_lthy0
      |> fold (Variable.declare_typ o resort_tfree dummyS) unsorted_As
      |> mk_TFrees (length unsorted_As)
      ||>> mk_TFrees nn
      ||>> apfst (map TFree) o
        variant_types (map (prefix "'") fp_b_names) (replicate nn HOLogic.typeS);

    (* TODO: cleaner handling of fake contexts, without "background_theory" *)
    (*the "perhaps o try" below helps gracefully handles the case where the new type is defined in a
      locale and shadows an existing global type*)
    val fake_thy =
      Theory.copy #> fold (fn spec => perhaps (try (Sign.add_type no_defs_lthy
        (type_binding_of spec, length (type_args_constrained_of spec), mixfix_of spec)))) specs;
    val fake_lthy = Proof_Context.background_theory fake_thy no_defs_lthy;

    fun mk_fake_T b =
      Type (fst (Term.dest_Type (Proof_Context.read_type_name fake_lthy true (Binding.name_of b))),
        unsorted_As);

    val fake_Ts = map mk_fake_T fp_bs;

    val mixfixes = map mixfix_of specs;

    val _ = (case duplicates Binding.eq_name fp_bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val ctr_specss = map ctr_specs_of specs;

    val disc_bindingss = map (map disc_of) ctr_specss;
    val ctr_bindingss =
      map2 (fn fp_b_name => map (Binding.qualify false fp_b_name o ctr_of)) fp_b_names ctr_specss;
    val ctr_argsss = map (map args_of) ctr_specss;
    val ctr_mixfixess = map (map ctr_mixfix_of) ctr_specss;

    val sel_bindingsss = map (map (map fst)) ctr_argsss;
    val fake_ctr_Tsss0 = map (map (map (prepare_typ fake_lthy o snd))) ctr_argsss;
    val raw_sel_defaultsss = map (map defaults_of) ctr_specss;

    val (As :: _) :: fake_ctr_Tsss =
      burrow (burrow (Syntax.check_typs fake_lthy)) (Ass0 :: fake_ctr_Tsss0);

    val _ = (case duplicates (op =) unsorted_As of [] => ()
      | A :: _ => error ("Duplicate type parameter " ^
          quote (Syntax.string_of_typ no_defs_lthy A)));

    val rhs_As' = fold (fold (fold Term.add_tfreesT)) fake_ctr_Tsss [];
    val _ = (case subtract (op =) (map dest_TFree As) rhs_As' of
        [] => ()
      | A' :: _ => error ("Extra type variable on right-hand side: " ^
          quote (Syntax.string_of_typ no_defs_lthy (TFree A'))));

    fun eq_fpT_check (T as Type (s, Us)) (Type (s', Us')) =
        s = s' andalso (Us = Us' orelse error ("Illegal occurrence of recursive type " ^
          quote (Syntax.string_of_typ fake_lthy T)))
      | eq_fpT_check _ _ = false;

    fun freeze_fp (T as Type (s, Us)) =
        (case find_index (eq_fpT_check T) fake_Ts of
          ~1 => Type (s, map freeze_fp Us)
        | kk => nth Xs kk)
      | freeze_fp T = T;

    val ctr_TsssXs = map (map (map freeze_fp)) fake_ctr_Tsss;
    val ctr_sum_prod_TsXs = map (mk_sumTN_balanced o map HOLogic.mk_tupleT) ctr_TsssXs;

    val fp_eqs =
      map dest_TFree Xs ~~ map (Term.typ_subst_atomic (As ~~ unsorted_As)) ctr_sum_prod_TsXs;

    (* TODO: clean up list *)
    val (pre_bnfs, ((fp_bnfs as any_fp_bnf :: _, dtors0, ctors0, fp_folds0, fp_recs0, fp_induct,
           fp_strong_induct, dtor_ctors, ctor_dtors, ctor_injects, fp_map_thms, fp_set_thmss,
           fp_rel_thms, fp_fold_thms, fp_rec_thms), lthy)) =
      fp_bnf construct_fp fp_bs mixfixes (map dest_TFree unsorted_As) fp_eqs no_defs_lthy0;

    val timer = time (Timer.startRealTimer ());

    fun add_nesty_bnf_names Us =
      let
        fun add (Type (s, Ts)) ss =
            let val (needs, ss') = fold_map add Ts ss in
              if exists I needs then (true, insert (op =) s ss') else (false, ss')
            end
          | add T ss = (member (op =) Us T, ss);
      in snd oo add end;

    fun nesty_bnfs Us =
      map_filter (bnf_of lthy) (fold (fold (fold (add_nesty_bnf_names Us))) ctr_TsssXs []);

    val nesting_bnfs = nesty_bnfs As;
    val nested_bnfs = nesty_bnfs Xs;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val pre_rel_defs = map rel_def_of_bnf pre_bnfs;
    val nested_set_natural's = maps set_natural'_of_bnf nested_bnfs;
    val nesting_map_ids = map map_id_of_bnf nesting_bnfs;
    val nesting_set_natural's = maps set_natural'_of_bnf nesting_bnfs;

    val live = live_of_bnf any_fp_bnf;

    val Bs =
      map3 (fn alive => fn A as TFree (_, S) => fn B => if alive then resort_tfree S B else A)
        (liveness_of_fp_bnf (length As) any_fp_bnf) As Bs0;

    val B_ify = Term.typ_subst_atomic (As ~~ Bs);

    val ctors = map (mk_ctor As) ctors0;
    val dtors = map (mk_dtor As) dtors0;

    val fpTs = map (domain_type o fastype_of) dtors;

    val exists_fp_subtype = exists_subtype (member (op =) fpTs);

    val ctr_Tsss = map (map (map (Term.typ_subst_atomic (Xs ~~ fpTs)))) ctr_TsssXs;
    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;
    val Css = map2 replicate ns Cs;

    val fp_folds as any_fp_fold :: _ = map (mk_rec_like lfp As Cs) fp_folds0;
    val fp_recs as any_fp_rec :: _ = map (mk_rec_like lfp As Cs) fp_recs0;

    val fp_fold_fun_Ts = fst (split_last (binder_types (fastype_of any_fp_fold)));
    val fp_rec_fun_Ts = fst (split_last (binder_types (fastype_of any_fp_rec)));

    val (((fold_only as (gss, _, _), rec_only as (hss, _, _)),
          (zs, cs, cpss, unfold_only as ((pgss, crgsss), _), corec_only as ((phss, cshsss), _))),
         names_lthy0) =
      if lfp then
        let
          val y_Tsss =
            map3 (fn n => fn ms => map2 dest_tupleT ms o dest_sumTN_balanced n o domain_type)
              ns mss fp_fold_fun_Ts;
          val g_Tss = map2 (map2 (curry (op --->))) y_Tsss Css;

          val ((gss, ysss), lthy) =
            lthy
            |> mk_Freess "f" g_Tss
            ||>> mk_Freesss "x" y_Tsss;
          val yssss = map (map (map single)) ysss;

          fun dest_rec_prodT (T as Type (@{type_name prod}, Us as [_, U])) =
              if member (op =) Cs U then Us else [T]
            | dest_rec_prodT T = [T];

          val z_Tssss =
            map3 (fn n => fn ms => map2 (map dest_rec_prodT oo dest_tupleT) ms o
              dest_sumTN_balanced n o domain_type) ns mss fp_rec_fun_Ts;
          val h_Tss = map2 (map2 (fold_rev (curry (op --->)))) z_Tssss Css;

          val hss = map2 (map2 retype_free) h_Tss gss;
          val zssss_hd = map2 (map2 (map2 (retype_free o hd))) z_Tssss ysss;
          val (zssss_tl, lthy) =
            lthy
            |> mk_Freessss "y" (map (map (map tl)) z_Tssss);
          val zssss = map2 (map2 (map2 cons)) zssss_hd zssss_tl;
        in
          ((((gss, g_Tss, yssss), (hss, h_Tss, zssss)),
            ([], [], [], (([], []), ([], [])), (([], []), ([], [])))), lthy)
        end
      else
        let
          (*avoid "'a itself" arguments in coiterators and corecursors*)
          val mss' =  map (fn [0] => [1] | ms => ms) mss;

          val p_Tss = map2 (fn n => replicate (Int.max (0, n - 1)) o mk_pred1T) ns Cs;

          fun flat_predss_getterss qss fss = maps (op @) (qss ~~ fss);

          fun flat_preds_predsss_gettersss [] [qss] [fss] = flat_predss_getterss qss fss
            | flat_preds_predsss_gettersss (p :: ps) (qss :: qsss) (fss :: fsss) =
              p :: flat_predss_getterss qss fss @ flat_preds_predsss_gettersss ps qsss fsss;

          fun mk_types maybe_dest_sumT fun_Ts =
            let
              val f_sum_prod_Ts = map range_type fun_Ts;
              val f_prod_Tss = map2 dest_sumTN_balanced ns f_sum_prod_Ts;
              val f_Tssss =
                map3 (fn C => map2 (map (map (curry (op -->) C) o maybe_dest_sumT) oo dest_tupleT))
                  Cs mss' f_prod_Tss;
              val q_Tssss =
                map (map (map (fn [_] => [] | [_, C] => [mk_pred1T (domain_type C)]))) f_Tssss;
              val pf_Tss = map3 flat_preds_predsss_gettersss p_Tss q_Tssss f_Tssss;
            in (q_Tssss, f_sum_prod_Ts, f_Tssss, pf_Tss) end;

          val (r_Tssss, g_sum_prod_Ts, g_Tssss, pg_Tss) = mk_types single fp_fold_fun_Ts;

          val ((((Free (z, _), cs), pss), gssss), lthy) =
            lthy
            |> yield_singleton (mk_Frees "z") dummyT
            ||>> mk_Frees "a" Cs
            ||>> mk_Freess "p" p_Tss
            ||>> mk_Freessss "g" g_Tssss;
          val rssss = map (map (map (fn [] => []))) r_Tssss;

          fun dest_corec_sumT (T as Type (@{type_name sum}, Us as [_, U])) =
              if member (op =) Cs U then Us else [T]
            | dest_corec_sumT T = [T];

          val (s_Tssss, h_sum_prod_Ts, h_Tssss, ph_Tss) = mk_types dest_corec_sumT fp_rec_fun_Ts;

          val hssss_hd = map2 (map2 (map2 (fn T :: _ => fn [g] => retype_free T g))) h_Tssss gssss;
          val ((sssss, hssss_tl), lthy) =
            lthy
            |> mk_Freessss "q" s_Tssss
            ||>> mk_Freessss "h" (map (map (map tl)) h_Tssss);
          val hssss = map2 (map2 (map2 cons)) hssss_hd hssss_tl;

          val cpss = map2 (fn c => map (fn p => p $ c)) cs pss;

          fun mk_preds_getters_join [] [cf] = cf
            | mk_preds_getters_join [cq] [cf, cf'] =
              mk_If cq (mk_Inl (fastype_of cf') cf) (mk_Inr (fastype_of cf) cf');

          fun mk_terms qssss fssss =
            let
              val pfss = map3 flat_preds_predsss_gettersss pss qssss fssss;
              val cqssss = map2 (fn c => map (map (map (fn f => f $ c)))) cs qssss;
              val cfssss = map2 (fn c => map (map (map (fn f => f $ c)))) cs fssss;
              val cqfsss = map2 (map2 (map2 mk_preds_getters_join)) cqssss cfssss;
            in (pfss, cqfsss) end;
        in
          (((([], [], []), ([], [], [])),
            ([z], cs, cpss, (mk_terms rssss gssss, (g_sum_prod_Ts, pg_Tss)),
             (mk_terms sssss hssss, (h_sum_prod_Ts, ph_Tss)))), lthy)
        end;

    fun define_ctrs_case_for_type (((((((((((((((((((((((((fp_bnf, fp_b), fpT), C), ctor), dtor),
            fp_fold), fp_rec), ctor_dtor), dtor_ctor), ctor_inject), pre_map_def), pre_set_defs),
          pre_rel_def), fp_map_thm), fp_set_thms), fp_rel_thm), n), ks), ms), ctr_bindings),
        ctr_mixfixes), ctr_Tss), disc_bindings), sel_bindingss), raw_sel_defaultss) no_defs_lthy =
      let
        val fp_b_name = Binding.name_of fp_b;

        val dtorT = domain_type (fastype_of ctor);
        val ctr_prod_Ts = map HOLogic.mk_tupleT ctr_Tss;
        val ctr_sum_prod_T = mk_sumTN_balanced ctr_prod_Ts;
        val case_Ts = map (fn Ts => Ts ---> C) ctr_Tss;

        val (((((w, fs), xss), yss), u'), names_lthy) =
          no_defs_lthy
          |> yield_singleton (mk_Frees "w") dtorT
          ||>> mk_Frees "f" case_Ts
          ||>> mk_Freess "x" ctr_Tss
          ||>> mk_Freess "y" (map (map B_ify) ctr_Tss)
          ||>> yield_singleton Variable.variant_fixes fp_b_name;

        val u = Free (u', fpT);

        val tuple_xs = map HOLogic.mk_tuple xss;
        val tuple_ys = map HOLogic.mk_tuple yss;

        val ctr_rhss =
          map3 (fn k => fn xs => fn tuple_x => fold_rev Term.lambda xs (ctor $
            mk_InN_balanced ctr_sum_prod_T n tuple_x k)) ks xss tuple_xs;

        val case_binding = Binding.suffix_name ("_" ^ caseN) fp_b;

        val case_rhs =
          fold_rev Term.lambda (fs @ [u])
            (mk_sum_caseN_balanced (map2 mk_uncurried_fun fs xss) $ (dtor $ u));

        val ((raw_case :: raw_ctrs, raw_case_def :: raw_ctr_defs), (lthy', lthy)) = no_defs_lthy
          |> apfst split_list o fold_map3 (fn b => fn mx => fn rhs =>
              Local_Theory.define ((b, mx), ((Thm.def_binding b, []), rhs)) #>> apsnd snd)
            (case_binding :: ctr_bindings) (NoSyn :: ctr_mixfixes) (case_rhs :: ctr_rhss)
          ||> `Local_Theory.restore;

        val phi = Proof_Context.export_morphism lthy lthy';

        val ctr_defs = map (Morphism.thm phi) raw_ctr_defs;
        val ctr_defs' =
          map2 (fn m => fn def => mk_unabs_def m (def RS meta_eq_to_obj_eq)) ms ctr_defs;
        val case_def = Morphism.thm phi raw_case_def;

        val ctrs0 = map (Morphism.term phi) raw_ctrs;
        val casex0 = Morphism.term phi raw_case;

        val ctrs = map (mk_ctr As) ctrs0;

        fun wrap lthy =
          let
            fun exhaust_tac {context = ctxt, ...} =
              let
                val ctor_iff_dtor_thm =
                  let
                    val goal =
                      fold_rev Logic.all [w, u]
                        (mk_Trueprop_eq (HOLogic.mk_eq (u, ctor $ w), HOLogic.mk_eq (dtor $ u, w)));
                  in
                    Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                      mk_ctor_iff_dtor_tac ctxt (map (SOME o certifyT lthy) [dtorT, fpT])
                        (certify lthy ctor) (certify lthy dtor) ctor_dtor dtor_ctor)
                    |> Thm.close_derivation
                    |> Morphism.thm phi
                  end;

                val sumEN_thm' =
                  unfold_thms lthy @{thms all_unit_eq}
                    (Drule.instantiate' (map (SOME o certifyT lthy) ctr_prod_Ts) []
                       (mk_sumEN_balanced n))
                  |> Morphism.thm phi;
              in
                mk_exhaust_tac ctxt n ctr_defs ctor_iff_dtor_thm sumEN_thm'
              end;

            val inject_tacss =
              map2 (fn 0 => K [] | _ => fn ctr_def => [fn {context = ctxt, ...} =>
                  mk_inject_tac ctxt ctr_def ctor_inject]) ms ctr_defs;

            val half_distinct_tacss =
              map (map (fn (def, def') => fn {context = ctxt, ...} =>
                mk_half_distinct_tac ctxt ctor_inject [def, def'])) (mk_half_pairss (`I ctr_defs));

            val case_tacs =
              map3 (fn k => fn m => fn ctr_def => fn {context = ctxt, ...} =>
                mk_case_tac ctxt n k m case_def ctr_def dtor_ctor) ks ms ctr_defs;

            val tacss = [exhaust_tac] :: inject_tacss @ half_distinct_tacss @ [case_tacs];

            val sel_defaultss = map (map (apsnd (prepare_term lthy))) raw_sel_defaultss
          in
            wrap_datatype tacss (((no_dests, ctrs0), casex0), (disc_bindings, (sel_bindingss,
              sel_defaultss))) lthy
          end;

        fun derive_maps_sets_rels (wrap_res, lthy) =
          let
            val rel_flip = rel_flip_of_bnf fp_bnf;
            val nones = replicate live NONE;

            val ctor_cong =
              if lfp then Drule.dummy_thm
              else cterm_instantiate_pos [NONE, NONE, SOME (certify lthy ctor)] arg_cong;

            fun mk_cIn ify =
              certify lthy o (not lfp ? curry (op $) (map_types ify ctor)) oo
              mk_InN_balanced (ify ctr_sum_prod_T) n;

            val cxIns = map2 (mk_cIn I) tuple_xs ks;
            val cyIns = map2 (mk_cIn B_ify) tuple_ys ks;

            fun mk_map_thm ctr_def' xs cxIn =
              fold_thms lthy [ctr_def']
                (unfold_thms lthy (pre_map_def ::
                     (if lfp then [] else [ctor_dtor, dtor_ctor]) @ sum_prod_thms_map)
                   (cterm_instantiate_pos (nones @ [SOME cxIn])
                      (if lfp then fp_map_thm else fp_map_thm RS ctor_cong)))
              |> singleton (Proof_Context.export names_lthy no_defs_lthy);

            fun mk_set_thm fp_set_thm ctr_def' xs cxIn =
              fold_thms lthy [ctr_def']
                (unfold_thms lthy (pre_set_defs @ nested_set_natural's @ nesting_set_natural's @
                     (if lfp then [] else [dtor_ctor]) @ sum_prod_thms_set)
                   (cterm_instantiate_pos [SOME cxIn] fp_set_thm))
              |> singleton (Proof_Context.export names_lthy no_defs_lthy);

            fun mk_set_thms fp_set_thm = map3 (mk_set_thm fp_set_thm) ctr_defs' xss cxIns;

            val map_thms = map3 mk_map_thm ctr_defs' xss cxIns;
            val set_thmss = map mk_set_thms fp_set_thms;

            val rel_infos = (ctr_defs' ~~ xss ~~ cxIns, ctr_defs' ~~ yss ~~ cyIns);

            fun mk_rel_thm postproc ctr_defs' xs cxIn ys cyIn =
              fold_thms lthy ctr_defs'
                 (unfold_thms lthy (pre_rel_def :: (if lfp then [] else [dtor_ctor]) @
                      sum_prod_thms_rel)
                    (cterm_instantiate_pos (nones @ [SOME cxIn, SOME cyIn]) fp_rel_thm))
              |> postproc
              |> singleton (Proof_Context.export names_lthy no_defs_lthy);

            fun mk_rel_inject_thm (((ctr_def', xs), cxIn), ((_, ys), cyIn)) =
              mk_rel_thm (unfold_thms lthy @{thms eq_sym_Unity_conv}) [ctr_def'] xs cxIn ys cyIn;

            val rel_inject_thms = map mk_rel_inject_thm (op ~~ rel_infos);

            fun mk_half_rel_distinct_thm (((xctr_def', xs), cxIn), ((yctr_def', ys), cyIn)) =
              mk_rel_thm (fn thm => thm RS @{thm eq_False[THEN iffD1]}) [xctr_def', yctr_def']
                xs cxIn ys cyIn;

            fun mk_other_half_rel_distinct_thm thm =
              flip_rels lthy live thm RS (rel_flip RS sym RS @{thm arg_cong[of _ _ Not]} RS iffD2);

            val half_rel_distinct_thmss =
              map (map mk_half_rel_distinct_thm) (mk_half_pairss rel_infos);
            val other_half_rel_distinct_thmss =
              map (map mk_other_half_rel_distinct_thm) half_rel_distinct_thmss;
            val (rel_distinct_thms, _) =
              join_halves n half_rel_distinct_thmss other_half_rel_distinct_thmss;

            val notes =
              [(mapN, map_thms, code_simp_attrs),
               (rel_distinctN, rel_distinct_thms, code_simp_attrs),
               (rel_injectN, rel_inject_thms, code_simp_attrs),
               (setsN, flat set_thmss, code_simp_attrs)]
              |> filter_out (null o #2)
              |> map (fn (thmN, thms, attrs) =>
                ((Binding.qualify true fp_b_name (Binding.name thmN), attrs), [(thms, [])]));
          in
            (wrap_res, lthy |> Local_Theory.notes notes |> snd)
          end;

        fun define_fold_rec no_defs_lthy =
          let
            val fpT_to_C = fpT --> C;

            fun generate_rec_like (suf, fp_rec_like, (fss, f_Tss, xssss)) =
              let
                val res_T = fold_rev (curry (op --->)) f_Tss fpT_to_C;
                val binding = Binding.suffix_name ("_" ^ suf) fp_b;
                val spec =
                  mk_Trueprop_eq (lists_bmoc fss (Free (Binding.name_of binding, res_T)),
                    Term.list_comb (fp_rec_like,
                      map2 (mk_sum_caseN_balanced oo map2 mk_uncurried2_fun) fss xssss));
              in (binding, spec) end;

            val rec_like_infos =
              [(foldN, fp_fold, fold_only),
               (recN, fp_rec, rec_only)];

            val (bindings, specs) = map generate_rec_like rec_like_infos |> split_list;

            val ((csts, defs), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) bindings specs
              ||> `Local_Theory.restore;

            val phi = Proof_Context.export_morphism lthy lthy';

            val [fold_def, rec_def] = map (Morphism.thm phi) defs;

            val [foldx, recx] = map (mk_rec_like lfp As Cs o Morphism.term phi) csts;
          in
            ((foldx, recx, fold_def, rec_def), lthy)
          end;

        fun define_unfold_corec no_defs_lthy =
          let
            val B_to_fpT = C --> fpT;

            fun mk_preds_getterss_join c n cps sum_prod_T cqfss =
              Term.lambda c (mk_IfN sum_prod_T cps
                (map2 (mk_InN_balanced sum_prod_T n) (map HOLogic.mk_tuple cqfss) (1 upto n)));

            fun generate_corec_like (suf, fp_rec_like, ((pfss, cqfsss), (f_sum_prod_Ts,
                pf_Tss))) =
              let
                val res_T = fold_rev (curry (op --->)) pf_Tss B_to_fpT;
                val binding = Binding.suffix_name ("_" ^ suf) fp_b;
                val spec =
                  mk_Trueprop_eq (lists_bmoc pfss (Free (Binding.name_of binding, res_T)),
                    Term.list_comb (fp_rec_like,
                      map5 mk_preds_getterss_join cs ns cpss f_sum_prod_Ts cqfsss));
              in (binding, spec) end;

            val corec_like_infos =
              [(unfoldN, fp_fold, unfold_only),
               (corecN, fp_rec, corec_only)];

            val (bindings, specs) = map generate_corec_like corec_like_infos |> split_list;

            val ((csts, defs), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) bindings specs
              ||> `Local_Theory.restore;

            val phi = Proof_Context.export_morphism lthy lthy';

            val [unfold_def, corec_def] = map (Morphism.thm phi) defs;

            val [unfold, corec] = map (mk_rec_like lfp As Cs o Morphism.term phi) csts;
          in
            ((unfold, corec, unfold_def, corec_def), lthy)
          end;

        val define_rec_likes = if lfp then define_fold_rec else define_unfold_corec;

        fun massage_res ((wrap_res, rec_like_res), lthy) =
          (((ctrs, xss, ctr_defs, wrap_res), rec_like_res), lthy);
      in
        (wrap #> (live > 0 ? derive_maps_sets_rels) ##>> define_rec_likes #> massage_res, lthy')
      end;

    fun wrap_types_and_more (wrap_types_and_mores, lthy) =
      fold_map I wrap_types_and_mores lthy
      |>> apsnd split_list4 o apfst split_list4 o split_list;

    fun build_map build_arg (Type (s, Ts)) (Type (_, Us)) =
      let
        val bnf = the (bnf_of lthy s);
        val live = live_of_bnf bnf;
        val mapx = mk_map live Ts Us (map_of_bnf bnf);
        val TUs' = map dest_funT (fst (strip_typeN live (fastype_of mapx)));
      in Term.list_comb (mapx, map build_arg TUs') end;

    (* TODO: Add map, sets, rel simps *)
    val mk_simp_thmss =
      map3 (fn (_, _, _, injects, distincts, cases, _, _, _) => fn rec_likes => fn fold_likes =>
        injects @ distincts @ cases @ rec_likes @ fold_likes);

    fun derive_induct_fold_rec_thms_for_types (((ctrss, xsss, ctr_defss, wrap_ress), (folds, recs,
        fold_defs, rec_defs)), lthy) =
      let
        val (((ps, ps'), us'), names_lthy) =
          lthy
          |> mk_Frees' "P" (map mk_pred1T fpTs)
          ||>> Variable.variant_fixes fp_b_names;

        val us = map2 (curry Free) us' fpTs;

        fun mk_sets_nested bnf =
          let
            val Type (T_name, Us) = T_of_bnf bnf;
            val lives = lives_of_bnf bnf;
            val sets = sets_of_bnf bnf;
            fun mk_set U =
              (case find_index (curry (op =) U) lives of
                ~1 => Term.dummy
              | i => nth sets i);
          in
            (T_name, map mk_set Us)
          end;

        val setss_nested = map mk_sets_nested nested_bnfs;

        val (induct_thms, induct_thm) =
          let
            fun mk_set Ts t =
              let val Type (_, Ts0) = domain_type (fastype_of t) in
                Term.subst_atomic_types (Ts0 ~~ Ts) t
              end;

            fun mk_raw_prem_prems names_lthy (x as Free (s, T as Type (T_name, Ts0))) =
                (case find_index (curry (op =) T) fpTs of
                  ~1 =>
                  (case AList.lookup (op =) setss_nested T_name of
                    NONE => []
                  | SOME raw_sets0 =>
                    let
                      val (Ts, raw_sets) =
                        split_list (filter (exists_fp_subtype o fst) (Ts0 ~~ raw_sets0));
                      val sets = map (mk_set Ts0) raw_sets;
                      val (ys, names_lthy') = names_lthy |> mk_Frees s Ts;
                      val xysets = map (pair x) (ys ~~ sets);
                      val ppremss = map (mk_raw_prem_prems names_lthy') ys;
                    in
                      flat (map2 (map o apfst o cons) xysets ppremss)
                    end)
                | kk => [([], (kk + 1, x))])
              | mk_raw_prem_prems _ _ = [];

            fun close_prem_prem xs t =
              fold_rev Logic.all (map Free (drop (nn + length xs)
                (rev (Term.add_frees t (map dest_Free xs @ ps'))))) t;

            fun mk_prem_prem xs (xysets, (j, x)) =
              close_prem_prem xs (Logic.list_implies (map (fn (x', (y, set)) =>
                  HOLogic.mk_Trueprop (HOLogic.mk_mem (y, set $ x'))) xysets,
                HOLogic.mk_Trueprop (nth ps (j - 1) $ x)));

            fun mk_raw_prem phi ctr ctr_Ts =
              let
                val (xs, names_lthy') = names_lthy |> mk_Frees "x" ctr_Ts;
                val pprems = maps (mk_raw_prem_prems names_lthy') xs;
              in (xs, pprems, HOLogic.mk_Trueprop (phi $ Term.list_comb (ctr, xs))) end;

            fun mk_prem (xs, raw_pprems, concl) =
              fold_rev Logic.all xs (Logic.list_implies (map (mk_prem_prem xs) raw_pprems, concl));

            val raw_premss = map3 (map2 o mk_raw_prem) ps ctrss ctr_Tsss;

            val goal =
              Library.foldr (Logic.list_implies o apfst (map mk_prem)) (raw_premss,
                HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 (curry (op $)) ps us)));

            val kksss = map (map (map (fst o snd) o #2)) raw_premss;

            val ctor_induct' = fp_induct OF (map mk_sumEN_tupled_balanced mss);

            val thm =
              Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                mk_induct_tac ctxt nn ns mss kksss (flat ctr_defss) ctor_induct'
                  nested_set_natural's pre_set_defss)
              |> singleton (Proof_Context.export names_lthy lthy)
              |> Thm.close_derivation;
          in
            `(conj_dests nn) thm
          end;

        (* TODO: Generate nicer names in case of clashes *)
        val induct_cases = Datatype_Prop.indexify_names (maps (map base_name_of_ctr) ctrss);

        val (fold_thmss, rec_thmss) =
          let
            val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;
            val gfolds = map (lists_bmoc gss) folds;
            val hrecs = map (lists_bmoc hss) recs;

            fun mk_goal fss frec_like xctr f xs fxs =
              fold_rev (fold_rev Logic.all) (xs :: fss)
                (mk_Trueprop_eq (frec_like $ xctr, Term.list_comb (f, fxs)));

            fun build_rec_like frec_likes maybe_tick (T, U) =
              if T = U then
                id_const T
              else
                (case find_index (curry (op =) T) fpTs of
                  ~1 => build_map (build_rec_like frec_likes maybe_tick) T U
                | kk => maybe_tick (nth us kk) (nth frec_likes kk));

            fun mk_U maybe_mk_prodT =
              typ_subst (map2 (fn fpT => fn C => (fpT, maybe_mk_prodT fpT C)) fpTs Cs);

            fun intr_rec_likes frec_likes maybe_cons maybe_tick maybe_mk_prodT (x as Free (_, T)) =
              if member (op =) fpTs T then
                maybe_cons x [build_rec_like frec_likes (K I) (T, mk_U (K I) T) $ x]
              else if exists_fp_subtype T then
                [build_rec_like frec_likes maybe_tick (T, mk_U maybe_mk_prodT T) $ x]
              else
                [x];

            val gxsss = map (map (maps (intr_rec_likes gfolds (K I) (K I) (K I)))) xsss;
            val hxsss =
              map (map (maps (intr_rec_likes hrecs cons tick (curry HOLogic.mk_prodT)))) xsss;

            val fold_goalss = map5 (map4 o mk_goal gss) gfolds xctrss gss xsss gxsss;
            val rec_goalss = map5 (map4 o mk_goal hss) hrecs xctrss hss xsss hxsss;

            val fold_tacss =
              map2 (map o mk_rec_like_tac pre_map_defs nesting_map_ids fold_defs) fp_fold_thms
                ctr_defss;
            val rec_tacss =
              map2 (map o mk_rec_like_tac pre_map_defs nesting_map_ids rec_defs) fp_rec_thms
                ctr_defss;

            fun prove goal tac =
              Skip_Proof.prove lthy [] [] goal (tac o #context)
              |> Thm.close_derivation;
          in
            (map2 (map2 prove) fold_goalss fold_tacss, map2 (map2 prove) rec_goalss rec_tacss)
          end;

        val simp_thmss = mk_simp_thmss wrap_ress rec_thmss fold_thmss;

        val induct_case_names_attr = Attrib.internal (K (Rule_Cases.case_names induct_cases));
        fun induct_type_attr T_name = Attrib.internal (K (Induct.induct_type T_name));

        val common_notes =
          (if nn > 1 then [(inductN, [induct_thm], [induct_case_names_attr])] else [])
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true fp_common_name (Binding.name thmN), attrs), [(thms, [])]));

        val notes =
          [(inductN, map single induct_thms,
            fn T_name => [induct_case_names_attr, induct_type_attr T_name]),
           (foldN, fold_thmss, K (code_simp_attrs)),
           (recN, rec_thmss, K (code_simp_attrs)),
           (simpsN, simp_thmss, K [])]
          |> maps (fn (thmN, thmss, attrs) =>
            map3 (fn b => fn Type (T_name, _) => fn thms =>
              ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), attrs T_name),
                [(thms, [])])) fp_bs fpTs thmss);
      in
        lthy |> Local_Theory.notes (common_notes @ notes) |> snd
      end;

    fun derive_coinduct_unfold_corec_thms_for_types (((ctrss, _, ctr_defss, wrap_ress), (unfolds,
        corecs, unfold_defs, corec_defs)), lthy) =
      let
        val nesting_rel_eqs = map rel_eq_of_bnf nesting_bnfs;

        val discss = map (map (mk_disc_or_sel As) o #1) wrap_ress;
        val selsss = map (map (map (mk_disc_or_sel As)) o #2) wrap_ress;
        val exhaust_thms = map #3 wrap_ress;
        val disc_thmsss = map #7 wrap_ress;
        val discIss = map #8 wrap_ress;
        val sel_thmsss = map #9 wrap_ress;

        val (((rs, us'), vs'), names_lthy) =
          lthy
          |> mk_Frees "R" (map (fn T => mk_pred2T T T) fpTs)
          ||>> Variable.variant_fixes fp_b_names
          ||>> Variable.variant_fixes (map (suffix "'") fp_b_names);

        val us = map2 (curry Free) us' fpTs;
        val udiscss = map2 (map o rapp) us discss;
        val uselsss = map2 (map o map o rapp) us selsss;

        val vs = map2 (curry Free) vs' fpTs;
        val vdiscss = map2 (map o rapp) vs discss;
        val vselsss = map2 (map o map o rapp) vs selsss;

        val ((coinduct_thms, coinduct_thm), (strong_coinduct_thms, strong_coinduct_thm)) =
          let
            val uvrs = map3 (fn r => fn u => fn v => r $ u $ v) rs us vs;
            val uv_eqs = map2 (curry HOLogic.mk_eq) us vs;
            val strong_rs =
              map4 (fn u => fn v => fn uvr => fn uv_eq =>
                fold_rev Term.lambda [u, v] (HOLogic.mk_disj (uvr, uv_eq))) us vs uvrs uv_eqs;

            fun build_rel_step build_arg (Type (s, Ts)) =
              let
                val bnf = the (bnf_of lthy s);
                val live = live_of_bnf bnf;
                val rel = mk_rel live Ts Ts (rel_of_bnf bnf);
                val Ts' = map domain_type (fst (strip_typeN live (fastype_of rel)));
              in Term.list_comb (rel, map build_arg Ts') end;

            fun build_rel rs' T =
              (case find_index (curry (op =) T) fpTs of
                ~1 =>
                if exists_fp_subtype T then build_rel_step (build_rel rs') T
                else HOLogic.eq_const T
              | kk => nth rs' kk);

            fun build_rel_app rs' usel vsel =
              fold rapp [usel, vsel] (build_rel rs' (fastype_of usel));

            fun mk_prem_ctr_concls rs' n k udisc usels vdisc vsels =
              (if k = n then [] else [HOLogic.mk_eq (udisc, vdisc)]) @
              (if null usels then
                 []
               else
                 [Library.foldr HOLogic.mk_imp (if n = 1 then [] else [udisc, vdisc],
                    Library.foldr1 HOLogic.mk_conj (map2 (build_rel_app rs') usels vsels))]);

            fun mk_prem_concl rs' n udiscs uselss vdiscs vselss =
              Library.foldr1 HOLogic.mk_conj
                (flat (map5 (mk_prem_ctr_concls rs' n) (1 upto n) udiscs uselss vdiscs vselss))
              handle List.Empty => @{term True};

            fun mk_prem rs' uvr u v n udiscs uselss vdiscs vselss =
              fold_rev Logic.all [u, v] (Logic.mk_implies (HOLogic.mk_Trueprop uvr,
                HOLogic.mk_Trueprop (mk_prem_concl rs' n udiscs uselss vdiscs vselss)));

            val concl =
              HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map3 (fn uvr => fn u => fn v => HOLogic.mk_imp (uvr, HOLogic.mk_eq (u, v)))
                   uvrs us vs));

            fun mk_goal rs' =
              Logic.list_implies (map8 (mk_prem rs') uvrs us vs ns udiscss uselsss vdiscss vselsss,
                concl);

            val goal = mk_goal rs;
            val strong_goal = mk_goal strong_rs;

            fun prove dtor_coinduct' goal =
              Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                mk_coinduct_tac ctxt nesting_rel_eqs nn ns dtor_coinduct' pre_rel_defs dtor_ctors
                  exhaust_thms ctr_defss disc_thmsss sel_thmsss)
              |> singleton (Proof_Context.export names_lthy lthy)
              |> Thm.close_derivation;

            fun postproc nn thm =
              Thm.permute_prems 0 nn
                (if nn = 1 then thm RS mp
                 else funpow nn (fn thm => reassoc_conjs (thm RS mp_conj)) thm)
              |> Drule.zero_var_indexes
              |> `(conj_dests nn);
          in
            (postproc nn (prove fp_induct goal), postproc nn (prove fp_strong_induct strong_goal))
          end;

        fun mk_maybe_not pos = not pos ? HOLogic.mk_not;

        val z = the_single zs;
        val gunfolds = map (lists_bmoc pgss) unfolds;
        val hcorecs = map (lists_bmoc phss) corecs;

        val (unfold_thmss, corec_thmss, safe_unfold_thmss, safe_corec_thmss) =
          let
            fun mk_goal pfss c cps fcorec_like n k ctr m cfs' =
              fold_rev (fold_rev Logic.all) ([c] :: pfss)
                (Logic.list_implies (seq_conds (HOLogic.mk_Trueprop oo mk_maybe_not) n k cps,
                   mk_Trueprop_eq (fcorec_like $ c, Term.list_comb (ctr, take m cfs'))));

            fun build_corec_like fcorec_likes maybe_tack (T, U) =
              if T = U then
                id_const T
              else
                (case find_index (curry (op =) U) fpTs of
                  ~1 => build_map (build_corec_like fcorec_likes maybe_tack) T U
                | kk => maybe_tack (nth cs kk, nth us kk) (nth fcorec_likes kk));

            fun mk_U maybe_mk_sumT =
              typ_subst (map2 (fn C => fn fpT => (maybe_mk_sumT fpT C, fpT)) Cs fpTs);

            fun intr_corec_likes fcorec_likes maybe_mk_sumT maybe_tack cqf =
              let val T = fastype_of cqf in
                if exists_subtype (member (op =) Cs) T then
                  build_corec_like fcorec_likes maybe_tack (T, mk_U maybe_mk_sumT T) $ cqf
                else
                  cqf
              end;

            val crgsss' = map (map (map (intr_corec_likes gunfolds (K I) (K I)))) crgsss;
            val cshsss' =
              map (map (map (intr_corec_likes hcorecs (curry mk_sumT) (tack z)))) cshsss;

            val unfold_goalss =
              map8 (map4 oooo mk_goal pgss) cs cpss gunfolds ns kss ctrss mss crgsss';
            val corec_goalss =
              map8 (map4 oooo mk_goal phss) cs cpss hcorecs ns kss ctrss mss cshsss';

            val unfold_tacss =
              map3 (map oo mk_corec_like_tac unfold_defs nesting_map_ids) fp_fold_thms pre_map_defs
                ctr_defss;
            val corec_tacss =
              map3 (map oo mk_corec_like_tac corec_defs nesting_map_ids) fp_rec_thms pre_map_defs
                ctr_defss;

            fun prove goal tac =
              Skip_Proof.prove lthy [] [] goal (tac o #context) |> Thm.close_derivation;

            val unfold_thmss = map2 (map2 prove) unfold_goalss unfold_tacss;
            val corec_thmss =
              map2 (map2 prove) corec_goalss corec_tacss
              |> map (map (unfold_thms lthy @{thms sum_case_if}));

            val unfold_safesss = map2 (map2 (map2 (curry (op =)))) crgsss' crgsss;
            val corec_safesss = map2 (map2 (map2 (curry (op =)))) cshsss' cshsss;

            val filter_safesss =
              map2 (map_filter (fn (safes, thm) => if forall I safes then SOME thm else NONE) oo
                curry (op ~~));

            val safe_unfold_thmss = filter_safesss unfold_safesss unfold_thmss;
            val safe_corec_thmss = filter_safesss corec_safesss corec_thmss;
          in
            (unfold_thmss, corec_thmss, safe_unfold_thmss, safe_corec_thmss)
          end;

        val (disc_unfold_iff_thmss, disc_corec_iff_thmss) =
          let
            fun mk_goal c cps fcorec_like n k disc =
              mk_Trueprop_eq (disc $ (fcorec_like $ c),
                if n = 1 then @{const True}
                else Library.foldr1 HOLogic.mk_conj (seq_conds mk_maybe_not n k cps));

            val unfold_goalss = map6 (map2 oooo mk_goal) cs cpss gunfolds ns kss discss;
            val corec_goalss = map6 (map2 oooo mk_goal) cs cpss hcorecs ns kss discss;

            fun mk_case_split' cp =
              Drule.instantiate' [] [SOME (certify lthy cp)] @{thm case_split};

            val case_splitss' = map (map mk_case_split') cpss;

            val unfold_tacss =
              map3 (map oo mk_disc_corec_like_iff_tac) case_splitss' unfold_thmss disc_thmsss;
            val corec_tacss =
              map3 (map oo mk_disc_corec_like_iff_tac) case_splitss' corec_thmss disc_thmsss;

            fun prove goal tac =
              Skip_Proof.prove lthy [] [] goal (tac o #context)
              |> singleton (Proof_Context.export names_lthy0 no_defs_lthy)
              |> Thm.close_derivation;

            fun proves [_] [_] = []
              | proves goals tacs = map2 prove goals tacs;
          in
            (map2 proves unfold_goalss unfold_tacss,
             map2 proves corec_goalss corec_tacss)
          end;

        fun mk_disc_corec_like_thms corec_likes discIs =
          map (op RS) (filter_out (is_triv_implies o snd) (corec_likes ~~ discIs));

        val disc_unfold_thmss = map2 mk_disc_corec_like_thms unfold_thmss discIss;
        val disc_corec_thmss = map2 mk_disc_corec_like_thms corec_thmss discIss;

        fun mk_sel_corec_like_thm corec_like_thm sel sel_thm =
          let
            val (domT, ranT) = dest_funT (fastype_of sel);
            val arg_cong' =
              Drule.instantiate' (map (SOME o certifyT lthy) [domT, ranT])
                [NONE, NONE, SOME (certify lthy sel)] arg_cong
              |> Thm.varifyT_global;
            val sel_thm' = sel_thm RSN (2, trans);
          in
            corec_like_thm RS arg_cong' RS sel_thm'
          end;

        fun mk_sel_corec_like_thms corec_likess =
          map3 (map3 (map2 o mk_sel_corec_like_thm)) corec_likess selsss sel_thmsss |> map flat;

        val sel_unfold_thmss = mk_sel_corec_like_thms unfold_thmss;
        val sel_corec_thmss = mk_sel_corec_like_thms corec_thmss;

        fun flat_corec_like_thms corec_likes disc_corec_likes sel_corec_likes =
          corec_likes @ disc_corec_likes @ sel_corec_likes;

        val simp_thmss =
          mk_simp_thmss wrap_ress
            (map3 flat_corec_like_thms safe_corec_thmss disc_corec_thmss sel_corec_thmss)
            (map3 flat_corec_like_thms safe_unfold_thmss disc_unfold_thmss sel_unfold_thmss);

        val anonymous_notes =
          [(flat safe_unfold_thmss @ flat safe_corec_thmss, simp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val common_notes =
          (if nn > 1 then
             (* FIXME: attribs *)
             [(coinductN, [coinduct_thm], []),
              (strong_coinductN, [strong_coinduct_thm], [])]
           else
             [])
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true fp_common_name (Binding.name thmN), attrs), [(thms, [])]));

        val notes =
          [(coinductN, map single coinduct_thms, []), (* FIXME: attribs *)
           (corecN, corec_thmss, []),
           (disc_corecN, disc_corec_thmss, simp_attrs),
           (disc_corec_iffN, disc_corec_iff_thmss, simp_attrs),
           (disc_unfoldN, disc_unfold_thmss, simp_attrs),
           (disc_unfold_iffN, disc_unfold_iff_thmss, simp_attrs),
           (sel_corecN, sel_corec_thmss, simp_attrs),
           (sel_unfoldN, sel_unfold_thmss, simp_attrs),
           (simpsN, simp_thmss, []),
           (strong_coinductN, map single strong_coinduct_thms, []), (* FIXME: attribs *)
           (unfoldN, unfold_thmss, [])]
          |> maps (fn (thmN, thmss, attrs) =>
            map_filter (fn (_, []) => NONE | (b, thms) =>
              SOME ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), attrs),
                [(thms, [])])) (fp_bs ~~ thmss));
      in
        lthy |> Local_Theory.notes (anonymous_notes @ common_notes @ notes) |> snd
      end;

    val lthy' = lthy
      |> fold_map define_ctrs_case_for_type (fp_bnfs ~~ fp_bs ~~ fpTs ~~ Cs ~~ ctors ~~ dtors ~~
        fp_folds ~~ fp_recs ~~ ctor_dtors ~~ dtor_ctors ~~ ctor_injects ~~ pre_map_defs ~~
        pre_set_defss ~~ pre_rel_defs ~~ fp_map_thms ~~ fp_set_thmss ~~ fp_rel_thms ~~ ns ~~ kss ~~
        mss ~~ ctr_bindingss ~~ ctr_mixfixess ~~ ctr_Tsss ~~ disc_bindingss ~~ sel_bindingsss ~~
        raw_sel_defaultsss)
      |> wrap_types_and_more
      |> (if lfp then derive_induct_fold_rec_thms_for_types
          else derive_coinduct_unfold_corec_thms_for_types);

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      (if lfp then "" else "co") ^ "datatype"));
  in
    timer; lthy'
  end;

val datatypes = define_datatypes (K I) (K I) (K I);

val datatype_cmd = define_datatypes Typedecl.read_constraint Syntax.parse_typ Syntax.read_term;

val parse_ctr_arg =
  @{keyword "("} |-- parse_binding_colon -- Parse.typ --| @{keyword ")"} ||
  (Parse.typ >> pair Binding.empty);

val parse_defaults =
  @{keyword "("} |-- @{keyword "defaults"} |-- Scan.repeat parse_bound_term --| @{keyword ")"};

val parse_single_spec =
  Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword "="} |-- Parse.enum1 "|" (parse_opt_binding_colon -- Parse.binding --
    Scan.repeat parse_ctr_arg -- Scan.optional parse_defaults [] -- Parse.opt_mixfix));

val parse_datatype = parse_wrap_options -- Parse.and_list1 parse_single_spec;

fun parse_datatype_cmd lfp construct_fp = parse_datatype >> datatype_cmd lfp construct_fp;

end;
