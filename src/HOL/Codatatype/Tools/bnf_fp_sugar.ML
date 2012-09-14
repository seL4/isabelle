(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar for constructing LFPs and GFPs.
*)

signature BNF_FP_SUGAR =
sig
  val datatyp: bool ->
    (mixfix list -> (string * sort) list option -> binding list -> typ list * typ list list ->
      BNF_Def.BNF list -> local_theory ->
      (term list * term list * term list * term list * thm * thm list * thm list * thm list *
         thm list * thm list) * local_theory) ->
    bool * ((((typ * sort) list * binding) * mixfix) * ((((binding * binding) *
      (binding * typ) list) * (binding * term) list) * mixfix) list) list ->
    local_theory -> local_theory
  val parse_datatype_cmd: bool ->
    (mixfix list -> (string * sort) list option -> binding list -> typ list * typ list list ->
      BNF_Def.BNF list -> local_theory ->
      (term list * term list * term list * term list * thm * thm list * thm list * thm list *
         thm list * thm list) * local_theory) ->
    (local_theory -> local_theory) parser
end;

structure BNF_FP_Sugar : BNF_FP_SUGAR =
struct

open BNF_Util
open BNF_Wrap
open BNF_Def
open BNF_FP_Util
open BNF_FP_Sugar_Tactics

val simp_attrs = @{attributes [simp]};

fun split_list11 xs =
  (map #1 xs, map #2 xs, map #3 xs, map #4 xs, map #5 xs, map #6 xs, map #7 xs, map #8 xs,
   map #9 xs, map #10 xs, map #11 xs);

fun strip_map_type (Type (@{type_name fun}, [T as Type _, T'])) = strip_map_type T' |>> cons T
  | strip_map_type T = ([], T);

fun resort_tfree S (TFree (s, _)) = TFree (s, S);

fun typ_subst inst (T as Type (s, Ts)) =
    (case AList.lookup (op =) inst T of
      NONE => Type (s, map (typ_subst inst) Ts)
    | SOME T' => T')
  | typ_subst inst T = the_default T (AList.lookup (op =) inst T);

val lists_bmoc = fold (fn xs => fn t => Term.list_comb (t, xs));

fun mk_id T = Const (@{const_name id}, T --> T);

fun mk_tupled_fun x f xs = HOLogic.tupled_lambda x (Term.list_comb (f, xs));
fun mk_uncurried_fun f xs = mk_tupled_fun (HOLogic.mk_tuple xs) f xs;
fun mk_uncurried2_fun f xss =
  mk_tupled_fun (HOLogic.mk_tuple (map HOLogic.mk_tuple xss)) f (flat xss);

fun tick v f = Term.lambda v (HOLogic.mk_prod (v, f $ v));

fun tack z_name (c, v) f =
  let val z = Free (z_name, mk_sumT (fastype_of v, fastype_of c)) in
    Term.lambda z (mk_sum_case (Term.lambda v v, Term.lambda c (f $ c)) $ z)
  end;

fun cannot_merge_types () = error "Mutually recursive types must have the same type parameters";

fun merge_type_arg T T' = if T = T' then T else cannot_merge_types ();

fun merge_type_args (As, As') =
  if length As = length As' then map2 merge_type_arg As As' else cannot_merge_types ();

fun type_args_constrained_of (((cAs, _), _), _) = cAs;
fun type_binding_of (((_, b), _), _) = b;
fun mixfix_of ((_, mx), _) = mx;
fun ctr_specs_of (_, ctr_specs) = ctr_specs;

fun disc_of ((((disc, _), _), _), _) = disc;
fun ctr_of ((((_, ctr), _), _), _) = ctr;
fun args_of (((_, args), _), _) = args;
fun defaults_of ((_, ds), _) = ds;
fun ctr_mixfix_of (_, mx) = mx;

fun define_datatype prepare_constraint prepare_typ prepare_term lfp construct (no_dests, specs)
    no_defs_lthy0 =
  let
    (* TODO: sanity checks on arguments *)

    val _ = if not lfp andalso no_dests then error "Cannot define destructor-less codatatypes"
      else ();

    val N = length specs;
    val fp_bs = map type_binding_of specs;
    val fp_common_name = mk_common_name fp_bs;

    fun prepare_type_arg (ty, c) =
      let val TFree (s, _) = prepare_typ no_defs_lthy0 ty in
        TFree (s, prepare_constraint no_defs_lthy0 c)
      end;

    val Ass0 = map (map prepare_type_arg o type_args_constrained_of) specs;
    val unsorted_Ass0 = map (map (resort_tfree HOLogic.typeS)) Ass0;
    val unsorted_As = Library.foldr1 merge_type_args unsorted_Ass0;

    val (((Bs, Cs), vs'), no_defs_lthy) =
      no_defs_lthy0
      |> fold (Variable.declare_typ o resort_tfree dummyS) unsorted_As
      |> mk_TFrees N
      ||>> mk_TFrees N
      ||>> Variable.variant_fixes (map Binding.name_of fp_bs);

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
      map2 (fn fp_b => map (Binding.qualify false (Binding.name_of fp_b) o ctr_of))
        fp_bs ctr_specss;
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

    fun eq_fpT (T as Type (s, Us)) (Type (s', Us')) =
        s = s' andalso (Us = Us' orelse error ("Illegal occurrence of recursive type " ^
          quote (Syntax.string_of_typ fake_lthy T)))
      | eq_fpT _ _ = false;

    fun freeze_fp (T as Type (s, Us)) =
        (case find_index (eq_fpT T) fake_Ts of ~1 => Type (s, map freeze_fp Us) | j => nth Bs j)
      | freeze_fp T = T;

    val ctr_TsssBs = map (map (map freeze_fp)) fake_ctr_Tsss;
    val ctr_sum_prod_TsBs = map (mk_sumTN_balanced o map HOLogic.mk_tupleT) ctr_TsssBs;

    val fp_eqs =
      map dest_TFree Bs ~~ map (Term.typ_subst_atomic (As ~~ unsorted_As)) ctr_sum_prod_TsBs;

    val (pre_bnfs, ((unfs0, flds0, fp_iters0, fp_recs0, fp_induct, unf_flds, fld_unfs, fld_injects,
        fp_iter_thms, fp_rec_thms), lthy)) =
      fp_bnf construct fp_bs mixfixes (map dest_TFree unsorted_As) fp_eqs no_defs_lthy0;

    fun add_nesty_bnf_names Us =
      let
        fun add (Type (s, Ts)) ss =
            let val (needs, ss') = fold_map add Ts ss in
              if exists I needs then (true, insert (op =) s ss') else (false, ss')
            end
          | add T ss = (member (op =) Us T, ss);
      in snd oo add end;

    fun nesty_bnfs Us =
      map_filter (bnf_of lthy) (fold (fold (fold (add_nesty_bnf_names Us))) ctr_TsssBs []);

    val nesting_bnfs = nesty_bnfs As;
    val nested_bnfs = nesty_bnfs Bs;

    val timer = time (Timer.startRealTimer ());

    fun mk_unf_or_fld get_T Ts t =
      let val Type (_, Ts0) = get_T (fastype_of t) in
        Term.subst_atomic_types (Ts0 ~~ Ts) t
      end;

    val mk_unf = mk_unf_or_fld domain_type;
    val mk_fld = mk_unf_or_fld range_type;

    val unfs = map (mk_unf As) unfs0;
    val flds = map (mk_fld As) flds0;

    val fpTs = map (domain_type o fastype_of) unfs;

    val exists_fp_subtype = exists_subtype (member (op =) fpTs);

    val vs = map2 (curry Free) vs' fpTs;

    val ctr_Tsss = map (map (map (Term.typ_subst_atomic (Bs ~~ fpTs)))) ctr_TsssBs;
    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;
    val Css = map2 replicate ns Cs;

    fun mk_iter_like Ts Us t =
      let
        val (bindings, body) = strip_type (fastype_of t);
        val (f_Us, prebody) = split_last bindings;
        val Type (_, Ts0) = if lfp then prebody else body;
        val Us0 = distinct (op =) (map (if lfp then body_type else domain_type) f_Us);
      in
        Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
      end;

    val fp_iters as fp_iter1 :: _ = map (mk_iter_like As Cs) fp_iters0;
    val fp_recs as fp_rec1 :: _ = map (mk_iter_like As Cs) fp_recs0;

    val fp_iter_fun_Ts = fst (split_last (binder_types (fastype_of fp_iter1)));
    val fp_rec_fun_Ts = fst (split_last (binder_types (fastype_of fp_rec1)));

    val ((iter_only as (gss, _, _), rec_only as (hss, _, _)),
         (zs, cs, cpss, coiter_only as ((pgss, crgsss), _), corec_only as ((phss, cshsss), _))) =
      if lfp then
        let
          val y_Tsss =
            map3 (fn n => fn ms => map2 dest_tupleT ms o dest_sumTN_balanced n o domain_type)
              ns mss fp_iter_fun_Ts;
          val g_Tss = map2 (map2 (curry (op --->))) y_Tsss Css;

          val ((gss, ysss), _) =
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
          val (zssss_tl, _) =
            lthy
            |> mk_Freessss "y" (map (map (map tl)) z_Tssss);
          val zssss = map2 (map2 (map2 cons)) zssss_hd zssss_tl;
        in
          (((gss, g_Tss, yssss), (hss, h_Tss, zssss)),
           ([], [], [], (([], []), ([], [])), (([], []), ([], []))))
        end
      else
        let
          (*avoid "'a itself" arguments in coiterators and corecursors*)
          val mss' =  map (fn [0] => [1] | ms => ms) mss;

          val p_Tss = map2 (fn n => replicate (Int.max (0, n - 1)) o mk_predT) ns Cs;

          fun zip_predss_getterss qss fss = maps (op @) (qss ~~ fss);

          fun zip_preds_predsss_gettersss [] [qss] [fss] = zip_predss_getterss qss fss
            | zip_preds_predsss_gettersss (p :: ps) (qss :: qsss) (fss :: fsss) =
              p :: zip_predss_getterss qss fss @ zip_preds_predsss_gettersss ps qsss fsss;

          fun mk_types maybe_dest_sumT fun_Ts =
            let
              val f_sum_prod_Ts = map range_type fun_Ts;
              val f_prod_Tss = map2 dest_sumTN_balanced ns f_sum_prod_Ts;
              val f_Tssss =
                map3 (fn C => map2 (map (map (curry (op -->) C) o maybe_dest_sumT) oo dest_tupleT))
                  Cs mss' f_prod_Tss;
              val q_Tssss =
                map (map (map (fn [_] => [] | [_, C] => [mk_predT (domain_type C)]))) f_Tssss;
              val pf_Tss = map3 zip_preds_predsss_gettersss p_Tss q_Tssss f_Tssss;
            in (q_Tssss, f_sum_prod_Ts, f_Tssss, pf_Tss) end;

          val (r_Tssss, g_sum_prod_Ts, g_Tssss, pg_Tss) = mk_types single fp_iter_fun_Ts;

          val ((((Free (z, _), cs), pss), gssss), _) =
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
          val ((sssss, hssss_tl), _) =
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
              val pfss = map3 zip_preds_predsss_gettersss pss qssss fssss;
              val cqssss = map2 (fn c => map (map (map (fn f => f $ c)))) cs qssss;
              val cfssss = map2 (fn c => map (map (map (fn f => f $ c)))) cs fssss;
              val cqfsss = map2 (map2 (map2 mk_preds_getters_join)) cqssss cfssss;
            in (pfss, cqfsss) end;
        in
          ((([], [], []), ([], [], [])),
           ([z], cs, cpss, (mk_terms rssss gssss, (g_sum_prod_Ts, pg_Tss)),
            (mk_terms sssss hssss, (h_sum_prod_Ts, ph_Tss))))
        end;

    fun define_ctrs_case_for_type (((((((((((((((((((fp_b, fpT), C), v), fld), unf), fp_iter),
          fp_rec), fld_unf), unf_fld), fld_inject), n), ks), ms), ctr_bindings), ctr_mixfixes),
        ctr_Tss), disc_bindings), sel_bindingss), raw_sel_defaultss) no_defs_lthy =
      let
        val unfT = domain_type (fastype_of fld);
        val ctr_prod_Ts = map HOLogic.mk_tupleT ctr_Tss;
        val ctr_sum_prod_T = mk_sumTN_balanced ctr_prod_Ts;
        val case_Ts = map (fn Ts => Ts ---> C) ctr_Tss;

        val (((u, fs), xss), _) =
          no_defs_lthy
          |> yield_singleton (mk_Frees "u") unfT
          ||>> mk_Frees "f" case_Ts
          ||>> mk_Freess "x" ctr_Tss;

        val ctr_rhss =
          map2 (fn k => fn xs => fold_rev Term.lambda xs (fld $
            mk_InN_balanced ctr_sum_prod_T n (HOLogic.mk_tuple xs) k)) ks xss;

        val case_binding = Binding.suffix_name ("_" ^ caseN) fp_b;

        val case_rhs =
          fold_rev Term.lambda (fs @ [v])
            (mk_sum_caseN_balanced (map2 mk_uncurried_fun fs xss) $ (unf $ v));

        val ((raw_case :: raw_ctrs, raw_case_def :: raw_ctr_defs), (lthy', lthy)) = no_defs_lthy
          |> apfst split_list o fold_map3 (fn b => fn mx => fn rhs =>
              Local_Theory.define ((b, mx), ((Thm.def_binding b, []), rhs)) #>> apsnd snd)
            (case_binding :: ctr_bindings) (NoSyn :: ctr_mixfixes) (case_rhs :: ctr_rhss)
          ||> `Local_Theory.restore;

        val phi = Proof_Context.export_morphism lthy lthy';

        val ctr_defs = map (Morphism.thm phi) raw_ctr_defs;
        val case_def = Morphism.thm phi raw_case_def;

        val ctrs0 = map (Morphism.term phi) raw_ctrs;
        val casex0 = Morphism.term phi raw_case;

        val ctrs = map (mk_ctr As) ctrs0;

        fun exhaust_tac {context = ctxt, ...} =
          let
            val fld_iff_unf_thm =
              let
                val goal =
                  fold_rev Logic.all [u, v]
                    (mk_Trueprop_eq (HOLogic.mk_eq (v, fld $ u), HOLogic.mk_eq (unf $ v, u)));
              in
                Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                  mk_fld_iff_unf_tac ctxt (map (SOME o certifyT lthy) [unfT, fpT])
                    (certify lthy fld) (certify lthy unf) fld_unf unf_fld)
                |> Thm.close_derivation
                |> Morphism.thm phi
              end;

            val sumEN_thm' =
              Local_Defs.unfold lthy @{thms all_unit_eq}
                (Drule.instantiate' (map (SOME o certifyT lthy) ctr_prod_Ts) []
                   (mk_sumEN_balanced n))
              |> Morphism.thm phi;
          in
            mk_exhaust_tac ctxt n ctr_defs fld_iff_unf_thm sumEN_thm'
          end;

        val inject_tacss =
          map2 (fn 0 => K [] | _ => fn ctr_def => [fn {context = ctxt, ...} =>
              mk_inject_tac ctxt ctr_def fld_inject]) ms ctr_defs;

        val half_distinct_tacss =
          map (map (fn (def, def') => fn {context = ctxt, ...} =>
            mk_half_distinct_tac ctxt fld_inject [def, def'])) (mk_half_pairss ctr_defs);

        val case_tacs =
          map3 (fn k => fn m => fn ctr_def => fn {context = ctxt, ...} =>
            mk_case_tac ctxt n k m case_def ctr_def unf_fld) ks ms ctr_defs;

        val tacss = [exhaust_tac] :: inject_tacss @ half_distinct_tacss @ [case_tacs];

        fun define_iter_rec ((selss0, discIs, sel_thmss), no_defs_lthy) =
          let
            val fpT_to_C = fpT --> C;

            fun generate_iter_like (suf, fp_iter_like, (fss, f_Tss, xssss)) =
              let
                val res_T = fold_rev (curry (op --->)) f_Tss fpT_to_C;
                val binding = Binding.suffix_name ("_" ^ suf) fp_b;
                val spec =
                  mk_Trueprop_eq (lists_bmoc fss (Free (Binding.name_of binding, res_T)),
                    Term.list_comb (fp_iter_like,
                      map2 (mk_sum_caseN_balanced oo map2 mk_uncurried2_fun) fss xssss));
              in (binding, spec) end;

            val iter_like_infos =
              [(iterN, fp_iter, iter_only),
               (recN, fp_rec, rec_only)];

            val (bindings, specs) = map generate_iter_like iter_like_infos |> split_list;

            val ((csts, defs), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) bindings specs
              ||> `Local_Theory.restore;

            val phi = Proof_Context.export_morphism lthy lthy';

            val [iter_def, rec_def] = map (Morphism.thm phi) defs;

            val [iter, recx] = map (mk_iter_like As Cs o Morphism.term phi) csts;
          in
            ((ctrs, selss0, iter, recx, v, xss, ctr_defs, discIs, sel_thmss, iter_def, rec_def),
             lthy)
          end;

        fun define_coiter_corec ((selss0, discIs, sel_thmss), no_defs_lthy) =
          let
            val B_to_fpT = C --> fpT;

            fun mk_preds_getterss_join c n cps sum_prod_T cqfss =
              Term.lambda c (mk_IfN sum_prod_T cps
                (map2 (mk_InN_balanced sum_prod_T n) (map HOLogic.mk_tuple cqfss) (1 upto n)));

            fun generate_coiter_like (suf, fp_iter_like, ((pfss, cqfsss), (f_sum_prod_Ts,
                pf_Tss))) =
              let
                val res_T = fold_rev (curry (op --->)) pf_Tss B_to_fpT;
                val binding = Binding.suffix_name ("_" ^ suf) fp_b;
                val spec =
                  mk_Trueprop_eq (lists_bmoc pfss (Free (Binding.name_of binding, res_T)),
                    Term.list_comb (fp_iter_like,
                      map5 mk_preds_getterss_join cs ns cpss f_sum_prod_Ts cqfsss));
              in (binding, spec) end;

            val coiter_like_infos =
              [(coiterN, fp_iter, coiter_only),
               (corecN, fp_rec, corec_only)];

            val (bindings, specs) = map generate_coiter_like coiter_like_infos |> split_list;

            val ((csts, defs), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) bindings specs
              ||> `Local_Theory.restore;

            val phi = Proof_Context.export_morphism lthy lthy';

            val [coiter_def, corec_def] = map (Morphism.thm phi) defs;

            val [coiter, corec] = map (mk_iter_like As Cs o Morphism.term phi) csts;
          in
            ((ctrs, selss0, coiter, corec, v, xss, ctr_defs, discIs, sel_thmss, coiter_def,
              corec_def), lthy)
          end;

        fun wrap lthy =
          let val sel_defaultss = map (map (apsnd (prepare_term lthy))) raw_sel_defaultss in
            wrap_datatype tacss (((no_dests, ctrs0), casex0), (disc_bindings, (sel_bindingss,
              sel_defaultss))) lthy
          end;

        val define_iter_likes = if lfp then define_iter_rec else define_coiter_corec;
      in
        ((wrap, define_iter_likes), lthy')
      end;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val nesting_map_ids = map map_id_of_bnf nesting_bnfs;

    fun mk_map Ts Us t =
      let val (Type (_, Ts0), Type (_, Us0)) = strip_map_type (fastype_of t) |>> List.last in
        Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
      end;

    fun build_map build_arg (Type (s, Ts)) (Type (_, Us)) =
      let
        val map0 = map_of_bnf (the (bnf_of lthy s));
        val mapx = mk_map Ts Us map0;
        val TUs = map dest_funT (fst (split_last (fst (strip_map_type (fastype_of mapx)))));
        val args = map build_arg TUs;
      in Term.list_comb (mapx, args) end;

    fun derive_induct_iter_rec_thms_for_types ((ctrss, _, iters, recs, vs, xsss, ctr_defss, _, _,
        iter_defs, rec_defs), lthy) =
      let
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
            val ((phis, phis'), names_lthy) =
              lthy
              |> mk_Frees' "P" (map mk_predT fpTs);

            fun mk_set Ts t =
              let val Type (_, Ts0) = domain_type (fastype_of t) in
                Term.subst_atomic_types (Ts0 ~~ Ts) t
              end;

            fun mk_prem_prems names_lthy (x as Free (s, T as Type (T_name, Ts0))) =
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
                      val heads =
                        map2 (fn y => fn set => HOLogic.mk_Trueprop (HOLogic.mk_mem (y, set $ x)))
                          ys sets;
                      val bodies = flat (map (mk_prem_prems names_lthy') ys);
                    in
                      map2 (curry Logic.mk_implies) heads bodies
                    end)
                | i => [HOLogic.mk_Trueprop (nth phis i $ x)])
              | mk_prem_prems _ _ = [];

            fun close_prem_prem (Free x') t =
              fold_rev Logic.all (map Free (drop (N + 1) (rev (Term.add_frees t (x' :: phis'))))) t;

            fun mk_prem phi ctr ctr_Ts =
              let
                val (xs, names_lthy') = names_lthy |> mk_Frees "x" ctr_Ts;
                val prem_prems =
                  maps (fn x => map (close_prem_prem x) (mk_prem_prems names_lthy' x)) xs;
              in
                fold_rev Logic.all xs
                  (Logic.list_implies (prem_prems,
                     HOLogic.mk_Trueprop (phi $ Term.list_comb (ctr, xs))))
              end;

            val goal =
              fold_rev (fold_rev Logic.all) [phis, vs]
                (Library.foldr Logic.list_implies (map3 (map2 o mk_prem) phis ctrss ctr_Tsss,
                   HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                     (map2 (curry (op $)) phis vs))));

            val induct_thm =
              Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
                mk_induct_tac ctxt);
          in
            `(conj_dests N) induct_thm
          end;

        val (iter_thmss, rec_thmss) =
          let
            val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;
            val giters = map (lists_bmoc gss) iters;
            val hrecs = map (lists_bmoc hss) recs;

            fun mk_goal_iter_like fss fiter_like xctr f xs fxs =
              fold_rev (fold_rev Logic.all) (xs :: fss)
                (mk_Trueprop_eq (fiter_like $ xctr, Term.list_comb (f, fxs)));

            fun build_call fiter_likes maybe_tick (T, U) =
              if T = U then
                mk_id T
              else
                (case find_index (curry (op =) T) fpTs of
                  ~1 => build_map (build_call fiter_likes maybe_tick) T U
                | j => maybe_tick (nth vs j) (nth fiter_likes j));

            fun mk_U maybe_mk_prodT =
              typ_subst (map2 (fn fpT => fn C => (fpT, maybe_mk_prodT fpT C)) fpTs Cs);

            fun intr_calls fiter_likes maybe_cons maybe_tick maybe_mk_prodT (x as Free (_, T)) =
              if member (op =) fpTs T then
                maybe_cons x [build_call fiter_likes (K I) (T, mk_U (K I) T) $ x]
              else if exists_fp_subtype T then
                [build_call fiter_likes maybe_tick (T, mk_U maybe_mk_prodT T) $ x]
              else
                [x];

            val gxsss = map (map (maps (intr_calls giters (K I) (K I) (K I)))) xsss;
            val hxsss = map (map (maps (intr_calls hrecs cons tick (curry HOLogic.mk_prodT)))) xsss;

            val goal_iterss = map5 (map4 o mk_goal_iter_like gss) giters xctrss gss xsss gxsss;
            val goal_recss = map5 (map4 o mk_goal_iter_like hss) hrecs xctrss hss xsss hxsss;

            val iter_tacss =
              map2 (map o mk_iter_like_tac pre_map_defs nesting_map_ids iter_defs) fp_iter_thms
                ctr_defss;
            val rec_tacss =
              map2 (map o mk_iter_like_tac pre_map_defs nesting_map_ids rec_defs) fp_rec_thms
                ctr_defss;
          in
            (map2 (map2 (fn goal => fn tac => Skip_Proof.prove lthy [] [] goal (tac o #context)))
               goal_iterss iter_tacss,
             map2 (map2 (fn goal => fn tac => Skip_Proof.prove lthy [] [] goal (tac o #context)))
               goal_recss rec_tacss)
          end;

        val common_notes =
          (if N > 1 then [(inductN, [induct_thm], [])] (* FIXME: attribs *) else [])
          |> map (fn (thmN, thms, attrs) =>
              ((Binding.qualify true fp_common_name (Binding.name thmN), attrs), [(thms, [])]));

        val notes =
          [(inductN, map single induct_thms, []), (* FIXME: attribs *)
           (itersN, iter_thmss, simp_attrs),
           (recsN, rec_thmss, Code.add_default_eqn_attrib :: simp_attrs)]
          |> maps (fn (thmN, thmss, attrs) =>
            map2 (fn b => fn thms =>
              ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), attrs),
                [(thms, [])])) fp_bs thmss);
      in
        lthy |> Local_Theory.notes (common_notes @ notes) |> snd
      end;

    fun derive_coinduct_coiter_corec_thms_for_types ((ctrss, selsss, coiters, corecs, vs, _,
        ctr_defss, discIss, sel_thmsss, coiter_defs, corec_defs), lthy) =
      let
        val (coinduct_thms, coinduct_thm) =
          let
            val coinduct_thm = fp_induct;
          in
            `(conj_dests N) coinduct_thm
          end;

        val (coiter_thmss, corec_thmss) =
          let
            val z = the_single zs;
            val gcoiters = map (lists_bmoc pgss) coiters;
            val hcorecs = map (lists_bmoc phss) corecs;

            fun mk_goal_cond pos = HOLogic.mk_Trueprop o (not pos ? HOLogic.mk_not);

            fun mk_goal_coiter_like pfss c cps fcoiter_like n k ctr m cfs' =
              fold_rev (fold_rev Logic.all) ([c] :: pfss)
                (Logic.list_implies (seq_conds mk_goal_cond n k cps,
                   mk_Trueprop_eq (fcoiter_like $ c, Term.list_comb (ctr, take m cfs'))));

            fun build_call fiter_likes maybe_tack (T, U) =
              if T = U then
                mk_id T
              else
                (case find_index (curry (op =) U) fpTs of
                  ~1 => build_map (build_call fiter_likes maybe_tack) T U
                | j => maybe_tack (nth cs j, nth vs j) (nth fiter_likes j));

            fun mk_U maybe_mk_sumT =
              typ_subst (map2 (fn C => fn fpT => (maybe_mk_sumT fpT C, fpT)) Cs fpTs);

            fun intr_calls fiter_likes maybe_mk_sumT maybe_tack cqf =
              let val T = fastype_of cqf in
                if exists_subtype (member (op =) Cs) T then
                  build_call fiter_likes maybe_tack (T, mk_U maybe_mk_sumT T) $ cqf
                else
                  cqf
              end;

            val crgsss' = map (map (map (intr_calls gcoiters (K I) (K I)))) crgsss;
            val cshsss' = map (map (map (intr_calls hcorecs (curry mk_sumT) (tack z)))) cshsss;

            val goal_coiterss =
              map8 (map4 oooo mk_goal_coiter_like pgss) cs cpss gcoiters ns kss ctrss mss crgsss';
            val goal_corecss =
              map8 (map4 oooo mk_goal_coiter_like phss) cs cpss hcorecs ns kss ctrss mss cshsss';

            val coiter_tacss =
              map3 (map oo mk_coiter_like_tac coiter_defs nesting_map_ids) fp_iter_thms pre_map_defs
                ctr_defss;
            val corec_tacss =
              map3 (map oo mk_coiter_like_tac corec_defs nesting_map_ids) fp_rec_thms pre_map_defs
                ctr_defss;
          in
            (map2 (map2 (fn goal => fn tac =>
                 Skip_Proof.prove lthy [] [] goal (tac o #context) |> Thm.close_derivation))
               goal_coiterss coiter_tacss,
             map2 (map2 (fn goal => fn tac =>
                 Skip_Proof.prove lthy [] [] goal (tac o #context)
                 |> Local_Defs.unfold lthy @{thms sum_case_if} |> Thm.close_derivation))
               goal_corecss corec_tacss)
          end;

        fun mk_disc_coiter_like_thms [_] = K []
          | mk_disc_coiter_like_thms thms = map2 (curry (op RS)) thms;

        val disc_coiter_thmss = map2 mk_disc_coiter_like_thms coiter_thmss discIss;
        val disc_corec_thmss = map2 mk_disc_coiter_like_thms corec_thmss discIss;

        fun mk_sel_coiter_like_thm coiter_like_thm sel0 sel_thm =
          let
            val (domT, ranT) = dest_funT (fastype_of sel0);
            val arg_cong' =
              Drule.instantiate' (map (SOME o certifyT lthy) [domT, ranT])
                [NONE, NONE, SOME (certify lthy sel0)] arg_cong
              |> Thm.varifyT_global;
            val sel_thm' = sel_thm RSN (2, trans);
          in
            coiter_like_thm RS arg_cong' RS sel_thm'
          end;

        val sel_coiter_thmsss =
          map3 (map3 (map2 o mk_sel_coiter_like_thm)) coiter_thmss selsss sel_thmsss;
        val sel_corec_thmsss =
          map3 (map3 (map2 o mk_sel_coiter_like_thm)) corec_thmss selsss sel_thmsss;

        val common_notes =
          (if N > 1 then [(coinductN, [coinduct_thm], [])] (* FIXME: attribs *) else [])
          |> map (fn (thmN, thms, attrs) =>
              ((Binding.qualify true fp_common_name (Binding.name thmN), attrs), [(thms, [])]));

        val notes =
          [(coinductN, map single coinduct_thms, []), (* FIXME: attribs *)
           (coitersN, coiter_thmss, []),
           (disc_coitersN, disc_coiter_thmss, []),
           (sel_coitersN, map flat sel_coiter_thmsss, []),
           (corecsN, corec_thmss, []),
           (disc_corecsN, disc_corec_thmss, []),
           (sel_corecsN, map flat sel_corec_thmsss, [])]
          |> maps (fn (thmN, thmss, attrs) =>
            map_filter (fn (_, []) => NONE | (b, thms) =>
              SOME ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), attrs),
                [(thms, [])])) (fp_bs ~~ thmss));
      in
        lthy |> Local_Theory.notes (common_notes @ notes) |> snd
      end;

    fun wrap_types_and_define_iter_likes ((wraps, define_iter_likess), lthy) =
      fold_map2 (curry (op o)) define_iter_likess wraps lthy |>> split_list11

    val lthy' = lthy
      |> fold_map define_ctrs_case_for_type (fp_bs ~~ fpTs ~~ Cs ~~ vs ~~ flds ~~ unfs ~~
        fp_iters ~~ fp_recs ~~ fld_unfs ~~ unf_flds ~~ fld_injects ~~ ns ~~ kss ~~ mss ~~
        ctr_bindingss ~~ ctr_mixfixess ~~ ctr_Tsss ~~ disc_bindingss ~~ sel_bindingsss ~~
        raw_sel_defaultsss)
      |>> split_list |> wrap_types_and_define_iter_likes
      |> (if lfp then derive_induct_iter_rec_thms_for_types
          else derive_coinduct_coiter_corec_thms_for_types);

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      (if lfp then "" else "co") ^ "datatype"));
  in
    timer; lthy'
  end;

val datatyp = define_datatype (K I) (K I) (K I);

val datatype_cmd = define_datatype Typedecl.read_constraint Syntax.parse_typ Syntax.read_term;

val parse_binding_colon = Parse.binding --| @{keyword ":"};
val parse_opt_binding_colon = Scan.optional parse_binding_colon no_binding;

val parse_ctr_arg =
  @{keyword "("} |-- parse_binding_colon -- Parse.typ --| @{keyword ")"} ||
  (Parse.typ >> pair no_binding);

val parse_defaults =
  @{keyword "("} |-- @{keyword "defaults"} |-- Scan.repeat parse_bound_term --| @{keyword ")"};

val parse_single_spec =
  Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword "="} |-- Parse.enum1 "|" (parse_opt_binding_colon -- Parse.binding --
    Scan.repeat parse_ctr_arg -- Scan.optional parse_defaults [] -- Parse.opt_mixfix));

val parse_datatype = parse_wrap_options -- Parse.and_list1 parse_single_spec;

fun parse_datatype_cmd lfp construct = parse_datatype >> datatype_cmd lfp construct;

end;
