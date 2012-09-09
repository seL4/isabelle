(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar for constructing LFPs and GFPs.
*)

signature BNF_FP_SUGAR =
sig
  (* TODO: programmatic interface *)
end;

structure BNF_FP_Sugar : BNF_FP_SUGAR =
struct

open BNF_Util
open BNF_Wrap
open BNF_Def
open BNF_FP_Util
open BNF_LFP
open BNF_GFP
open BNF_FP_Sugar_Tactics

val caseN = "case";
val coitersN = "coiters";
val corecsN = "corecs";
val itersN = "iters";
val recsN = "recs";

fun split_list8 xs =
  (map #1 xs, map #2 xs, map #3 xs, map #4 xs, map #5 xs, map #6 xs, map #7 xs, map #8 xs);

fun strip_map_type (Type (@{type_name fun}, [T as Type _, T'])) = strip_map_type T' |>> cons T
  | strip_map_type T = ([], T);

fun typ_subst inst (T as Type (s, Ts)) =
    (case AList.lookup (op =) inst T of
      NONE => Type (s, map (typ_subst inst) Ts)
    | SOME T' => T')
  | typ_subst inst T = the_default T (AList.lookup (op =) inst T);

fun retype_free (Free (s, _)) T = Free (s, T);

val lists_bmoc = fold (fn xs => fn t => Term.list_comb (t, xs))

fun mk_tupled_fun x f xs = HOLogic.tupled_lambda x (Term.list_comb (f, xs));
fun mk_uncurried_fun f xs = mk_tupled_fun (HOLogic.mk_tuple xs) f xs;
fun mk_uncurried2_fun f xss =
  mk_tupled_fun (HOLogic.mk_tuple (map HOLogic.mk_tuple xss)) f (flat xss);

fun tick v f = Term.lambda v (HOLogic.mk_prod (v, f $ v));

fun tack z_name (c, v) f =
  let val z = Free (z_name, mk_sumT (fastype_of v, fastype_of c)) in
    Term.lambda z (mk_sum_case (Term.lambda v v) (Term.lambda c (f $ c)) $ z)
  end;

fun cannot_merge_types () = error "Mutually recursive types must have the same type parameters";

fun merge_type_arg_constrained ctxt (T, c) (T', c') =
  if T = T' then
    (case (c, c') of
      (_, NONE) => (T, c)
    | (NONE, _) => (T, c')
    | _ =>
      if c = c' then
        (T, c)
      else
        error ("Inconsistent sort constraints for type variable " ^
          quote (Syntax.string_of_typ ctxt T)))
  else
    cannot_merge_types ();

fun merge_type_args_constrained ctxt (cAs, cAs') =
  if length cAs = length cAs' then map2 (merge_type_arg_constrained ctxt) cAs cAs'
  else cannot_merge_types ();

fun type_args_constrained_of (((cAs, _), _), _) = cAs;
val type_args_of = map fst o type_args_constrained_of;
fun type_binder_of (((_, b), _), _) = b;
fun mixfix_of ((_, mx), _) = mx;
fun ctr_specs_of (_, ctr_specs) = ctr_specs;

fun disc_of (((disc, _), _), _) = disc;
fun ctr_of (((_, ctr), _), _) = ctr;
fun args_of ((_, args), _) = args;
fun ctr_mixfix_of (_, mx) = mx;

fun prepare_datatype prepare_typ lfp specs fake_lthy no_defs_lthy =
  let
    val constrained_As =
      map (map (apfst (prepare_typ fake_lthy)) o type_args_constrained_of) specs
      |> Library.foldr1 (merge_type_args_constrained no_defs_lthy);
    val As = map fst constrained_As;
    val As' = map dest_TFree As;

    val _ = (case duplicates (op =) As of [] => ()
      | A :: _ => error ("Duplicate type parameter " ^
          quote (Syntax.string_of_typ no_defs_lthy A)));

    (* TODO: use sort constraints on type args *)

    val N = length specs;

    fun mk_fake_T b =
      Type (fst (Term.dest_Type (Proof_Context.read_type_name fake_lthy true (Binding.name_of b))),
        As);

    val bs = map type_binder_of specs;
    val fakeTs = map mk_fake_T bs;

    val mixfixes = map mixfix_of specs;

    val _ = (case duplicates Binding.eq_name bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val ctr_specss = map ctr_specs_of specs;

    val disc_binderss = map (map disc_of) ctr_specss;
    val ctr_binderss = map (map ctr_of) ctr_specss;
    val ctr_argsss = map (map args_of) ctr_specss;
    val ctr_mixfixess = map (map ctr_mixfix_of) ctr_specss;

    val sel_bindersss = map (map (map fst)) ctr_argsss;
    val fake_ctr_Tsss = map (map (map (prepare_typ fake_lthy o snd))) ctr_argsss;

    val rhs_As' = fold (fold (fold Term.add_tfreesT)) fake_ctr_Tsss [];
    val _ = (case subtract (op =) As' rhs_As' of
        [] => ()
      | A' :: _ => error ("Extra type variables on rhs: " ^
          quote (Syntax.string_of_typ no_defs_lthy (TFree A'))));

    val ((Cs, Xs), _) =
      no_defs_lthy
      |> fold (fold (fn s => Variable.declare_typ (TFree (s, dummyS))) o type_args_of) specs
      |> mk_TFrees N
      ||>> mk_TFrees N;

    fun eq_fpT (T as Type (s, Us)) (Type (s', Us')) =
        s = s' andalso (Us = Us' orelse error ("Illegal occurrence of recursive type " ^
          quote (Syntax.string_of_typ fake_lthy T)))
      | eq_fpT _ _ = false;

    fun freeze_fp (T as Type (s, Us)) =
        (case find_index (eq_fpT T) fakeTs of ~1 => Type (s, map freeze_fp Us) | j => nth Xs j)
      | freeze_fp T = T;

    val ctr_TsssXs = map (map (map freeze_fp)) fake_ctr_Tsss;
    val sum_prod_TsXs = map (mk_sumTN o map HOLogic.mk_tupleT) ctr_TsssXs;

    val eqs = map dest_TFree Xs ~~ sum_prod_TsXs;

    val (pre_bnfs, ((unfs0, flds0, fp_iters0, fp_recs0, unf_flds, fld_unfs, fld_injects,
        fp_iter_thms, fp_rec_thms), lthy)) =
      fp_bnf (if lfp then bnf_lfp else bnf_gfp) bs mixfixes As' eqs no_defs_lthy;

    val add_nested_bnf_names =
      let
        fun add (Type (s, Ts)) ss =
            let val (needs, ss') = fold_map add Ts ss in
              if exists I needs then (true, insert (op =) s ss') else (false, ss')
            end
          | add T ss = (member (op =) As T, ss);
      in snd oo add end;

    val nested_bnfs =
      map_filter (bnf_of lthy o Long_Name.base_name)
        (fold (fold (fold add_nested_bnf_names)) ctr_TsssXs []);

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

    val ctr_Tsss = map (map (map (Term.typ_subst_atomic (Xs ~~ fpTs)))) ctr_TsssXs;
    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;
    val Css = map2 replicate ns Cs;

    fun mk_iter_like Ts Us t =
      let
        val (binders, body) = strip_type (fastype_of t);
        val (f_Us, prebody) = split_last binders;
        val Type (_, Ts0) = if lfp then prebody else body;
        val Us0 = distinct (op =) (map (if lfp then body_type else domain_type) f_Us);
      in
        Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
      end;

    val fp_iters as fp_iter1 :: _ = map (mk_iter_like As Cs) fp_iters0;
    val fp_recs as fp_rec1 :: _ = map (mk_iter_like As Cs) fp_recs0;

    val fp_iter_fun_Ts = fst (split_last (binder_types (fastype_of fp_iter1)));
    val fp_rec_fun_Ts = fst (split_last (binder_types (fastype_of fp_rec1)));

    fun dest_rec_pair (T as Type (@{type_name prod}, Us as [_, U])) =
        if member (op =) Cs U then Us else [T]
      | dest_rec_pair T = [T];

    val ((iter_only as (gss, g_Tss, yssss), rec_only as (hss, h_Tss, zssss)),
         (zs, cs, cpss, p_Tss, coiter_only as ((pgss, cgsss), g_sum_prod_Ts, g_prod_Tss, g_Tsss),
          corec_only as ((phss, chsss), h_sum_prod_Ts, h_prod_Tss, h_Tsss))) =
      if lfp then
        let
          val y_Tsss =
            map3 (fn n => fn ms => map2 dest_tupleT ms o dest_sumTN n o domain_type)
              ns mss fp_iter_fun_Ts;
          val g_Tss = map2 (map2 (curry (op --->))) y_Tsss Css;

          val ((gss, ysss), _) =
            lthy
            |> mk_Freess "f" g_Tss
            ||>> mk_Freesss "x" y_Tsss;

          val z_Tssss =
            map3 (fn n => fn ms => map2 (map dest_rec_pair oo dest_tupleT) ms o dest_sumTN n
              o domain_type) ns mss fp_rec_fun_Ts;
          val h_Tss = map2 (map2 (fold_rev (curry (op --->)))) z_Tssss Css;

          val hss = map2 (map2 retype_free) gss h_Tss;
          val (zssss, _) =
            lthy
            |> mk_Freessss "x" z_Tssss;
        in
          (((gss, g_Tss, map (map (map single)) ysss), (hss, h_Tss, zssss)),
           ([], [], [], [], (([], []), [], [], []), (([], []), [], [], [])))
        end
      else
        let
          (*avoid "'a itself" arguments in coiterators and corecursors*)
          val mss' =  map (fn [0] => [1] | ms => ms) mss;

          val p_Tss =
            map2 (fn C => fn n => replicate (Int.max (0, n - 1)) (C --> HOLogic.boolT)) Cs ns;

          fun popescu_zip [] [fs] = fs
            | popescu_zip (p :: ps) (fs :: fss) = p :: fs @ popescu_zip ps fss;

          fun mk_types fun_Ts =
            let
              val f_sum_prod_Ts = map range_type fun_Ts;
              val f_prod_Tss = map2 dest_sumTN ns f_sum_prod_Ts;
              val f_Tsss =
                map3 (fn C => map2 (map (curry (op -->) C) oo dest_tupleT)) Cs mss' f_prod_Tss;
              val pf_Tss = map2 popescu_zip p_Tss f_Tsss
            in (f_sum_prod_Ts, f_prod_Tss, f_Tsss, pf_Tss) end;

          val (g_sum_prod_Ts, g_prod_Tss, g_Tsss, pg_Tss) = mk_types fp_iter_fun_Ts;
          val (h_sum_prod_Ts, h_prod_Tss, h_Tsss, ph_Tss) = mk_types fp_rec_fun_Ts;

          val ((((Free (z, _), cs), pss), gsss), _) =
            lthy
            |> yield_singleton (mk_Frees "z") dummyT
            ||>> mk_Frees "a" Cs
            ||>> mk_Freess "p" p_Tss
            ||>> mk_Freesss "g" g_Tsss;

          val hsss = map2 (map2 (map2 retype_free)) gsss h_Tsss;

          val cpss = map2 (fn c => map (fn p => p $ c)) cs pss;

          fun mk_terms fsss =
            let
              val pfss = map2 popescu_zip pss fsss;
              val cfsss = map2 (fn c => map (map (fn f => f $ c))) cs fsss
            in (pfss, cfsss) end;
        in
          ((([], [], []), ([], [], [])),
           ([z], cs, cpss, p_Tss, (mk_terms gsss, g_sum_prod_Ts, g_prod_Tss, pg_Tss),
            (mk_terms hsss, h_sum_prod_Ts, h_prod_Tss, ph_Tss)))
        end;

    fun pour_some_sugar_on_type (((((((((((((((((b, fpT), C), fld), unf), fp_iter), fp_rec),
          fld_unf), unf_fld), fld_inject), n), ks), ms), ctr_binders), ctr_mixfixes), ctr_Tss),
        disc_binders), sel_binderss) no_defs_lthy =
      let
        val unfT = domain_type (fastype_of fld);
        val ctr_prod_Ts = map HOLogic.mk_tupleT ctr_Tss;
        val case_Ts = map (fn Ts => Ts ---> C) ctr_Tss;

        val ((((u, v), fs), xss), _) =
          no_defs_lthy
          |> yield_singleton (mk_Frees "u") unfT
          ||>> yield_singleton (mk_Frees "v") fpT
          ||>> mk_Frees "f" case_Ts
          ||>> mk_Freess "x" ctr_Tss;

        val ctr_rhss =
          map2 (fn k => fn xs =>
            fold_rev Term.lambda xs (fld $ mk_InN ctr_prod_Ts (HOLogic.mk_tuple xs) k)) ks xss;

        val case_binder = Binding.suffix_name ("_" ^ caseN) b;

        val case_rhs =
          fold_rev Term.lambda (fs @ [v]) (mk_sum_caseN (map2 mk_uncurried_fun fs xss) $ (unf $ v));

        val ((raw_case :: raw_ctrs, raw_case_def :: raw_ctr_defs), (lthy', lthy)) = no_defs_lthy
          |> apfst split_list o fold_map3 (fn b => fn mx => fn rhs =>
               Local_Theory.define ((b, mx), ((Thm.def_binding b, []), rhs)) #>> apsnd snd)
             (case_binder :: ctr_binders) (NoSyn :: ctr_mixfixes) (case_rhs :: ctr_rhss)
          ||> `Local_Theory.restore;

        (*transforms defined frees into consts (and more)*)
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
                (Drule.instantiate' (map (SOME o certifyT lthy) ctr_prod_Ts) [] (mk_sumEN n))
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

        fun some_lfp_sugar no_defs_lthy =
          let
            val fpT_to_C = fpT --> C;

            fun generate_iter_like (suf, fp_iter_like, (fss, f_Tss, xssss)) =
              let
                val res_T = fold_rev (curry (op --->)) f_Tss fpT_to_C;

                val binder = Binding.suffix_name ("_" ^ suf) b;

                val spec =
                  mk_Trueprop_eq (lists_bmoc fss (Free (Binding.name_of binder, res_T)),
                    Term.list_comb (fp_iter_like,
                      map2 (mk_sum_caseN oo map2 mk_uncurried2_fun) fss xssss));
              in (binder, spec) end;

            val iter_likes =
              [(iterN, fp_iter, iter_only),
               (recN, fp_rec, rec_only)];

            val (binders, specs) = map generate_iter_like iter_likes |> split_list;

            val ((csts, defs), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) binders specs
              ||> `Local_Theory.restore;

            (*transforms defined frees into consts (and more)*)
            val phi = Proof_Context.export_morphism lthy lthy';

            val [iter_def, rec_def] = map (Morphism.thm phi) defs;

            val [iter, recx] = map (mk_iter_like As Cs o Morphism.term phi) csts;
          in
            ((ctrs, iter, recx, v, xss, ctr_defs, iter_def, rec_def), lthy)
          end;

        fun some_gfp_sugar no_defs_lthy =
          let
            val B_to_fpT = C --> fpT;

            fun generate_coiter_like (suf, fp_iter_like, ((pfss, cfsss), f_sum_prod_Ts, f_prod_Tss,
                pf_Tss)) =
              let
                val res_T = fold_rev (curry (op --->)) pf_Tss B_to_fpT;

                val binder = Binding.suffix_name ("_" ^ suf) b;

                fun mk_popescu_join c n cps sum_prod_T prod_Ts cfss =
                  Term.lambda c (mk_IfN sum_prod_T cps
                    (map2 (mk_InN prod_Ts) (map HOLogic.mk_tuple cfss) (1 upto n)));

                val spec =
                  mk_Trueprop_eq (lists_bmoc pfss (Free (Binding.name_of binder, res_T)),
                    Term.list_comb (fp_iter_like,
                      map6 mk_popescu_join cs ns cpss f_sum_prod_Ts f_prod_Tss cfsss));
              in (binder, spec) end;

            val coiter_likes =
              [(coiterN, fp_iter, coiter_only),
               (corecN, fp_rec, corec_only)];

            val (binders, specs) = map generate_coiter_like coiter_likes |> split_list;

            val ((csts, defs), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) binders specs
              ||> `Local_Theory.restore;

            (*transforms defined frees into consts (and more)*)
            val phi = Proof_Context.export_morphism lthy lthy';

            val [coiter_def, corec_def] = map (Morphism.thm phi) defs;

            val [coiter, corec] = map (mk_iter_like As Cs o Morphism.term phi) csts;
          in
            ((ctrs, coiter, corec, v, xss, ctr_defs, coiter_def, corec_def), lthy)
          end;
      in
        wrap_datatype tacss ((ctrs0, casex0), (disc_binders, sel_binderss)) lthy'
        |> (if lfp then some_lfp_sugar else some_gfp_sugar)
      end;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val map_ids = map map_id_of_bnf nested_bnfs;

    fun mk_map Ts Us t =
      let val (Type (_, Ts0), Type (_, Us0)) = strip_map_type (fastype_of t) |>> List.last in
        Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
      end;

    fun pour_more_sugar_on_lfps ((ctrss, iters, recs, vs, xsss, ctr_defss, iter_defs, rec_defs),
        lthy) =
      let
        val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;
        val giters = map (lists_bmoc gss) iters;
        val hrecs = map (lists_bmoc hss) recs;

        val (iter_thmss, rec_thmss) =
          let
            fun mk_goal_iter_like fss fiter_like xctr f xs fxs =
              fold_rev (fold_rev Logic.all) (xs :: fss)
                (mk_Trueprop_eq (fiter_like $ xctr, Term.list_comb (f, fxs)));

            fun build_call fiter_likes maybe_tick =
              let
                fun build (T, U) =
                  if T = U then
                    Const (@{const_name id}, T --> T)
                  else
                    (case (find_index (curry (op =) T) fpTs, (T, U)) of
                      (~1, (Type (s, Ts), Type (_, Us))) =>
                      let
                        val map0 = map_of_bnf (the (bnf_of lthy (Long_Name.base_name s)));
                        val mapx = mk_map Ts Us map0;
                        val TUs =
                          map dest_funT (fst (split_last (fst (strip_map_type (fastype_of mapx)))));
                        val args = map build TUs;
                      in Term.list_comb (mapx, args) end
                    | (j, _) => maybe_tick (nth vs j) (nth fiter_likes j))
              in build end;

            fun mk_U maybe_prodT =
              typ_subst (map2 (fn fpT => fn C => (fpT, maybe_prodT fpT C)) fpTs Cs);

            fun repair_calls fiter_likes maybe_cons maybe_tick maybe_prodT (x as Free (_, T)) =
              if member (op =) fpTs T then
                maybe_cons x [build_call fiter_likes (K I) (T, mk_U (K I) T) $ x]
              else if exists_subtype (member (op =) fpTs) T then
                [build_call fiter_likes maybe_tick (T, mk_U maybe_prodT T) $ x]
              else
                [x];

            val gxsss = map (map (maps (repair_calls giters (K I) (K I) (K I)))) xsss;
            val hxsss =
              map (map (maps (repair_calls hrecs cons tick (curry HOLogic.mk_prodT)))) xsss;

            val goal_iterss = map5 (map4 o mk_goal_iter_like gss) giters xctrss gss xsss gxsss;
            val goal_recss = map5 (map4 o mk_goal_iter_like hss) hrecs xctrss hss xsss hxsss;

            val iter_tacss =
              map2 (map o mk_iter_like_tac pre_map_defs map_ids iter_defs) fp_iter_thms ctr_defss;
            val rec_tacss =
              map2 (map o mk_iter_like_tac pre_map_defs map_ids rec_defs) fp_rec_thms ctr_defss;
          in
            (map2 (map2 (fn goal => fn tac => Skip_Proof.prove lthy [] [] goal (tac o #context)))
               goal_iterss iter_tacss,
             map2 (map2 (fn goal => fn tac => Skip_Proof.prove lthy [] [] goal (tac o #context)))
               goal_recss rec_tacss)
          end;

        val notes =
          [(itersN, iter_thmss),
           (recsN, rec_thmss)]
          |> maps (fn (thmN, thmss) =>
            map2 (fn b => fn thms =>
                ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
              bs thmss);
      in
        lthy |> Local_Theory.notes notes |> snd
      end;

    fun pour_more_sugar_on_gfps ((ctrss, coiters, corecs, vs, xsss, ctr_defss, coiter_defs,
        corec_defs), lthy) =
      let
        val z = the_single zs;

        val gcoiters = map (lists_bmoc pgss) coiters;
        val hcorecs = map (lists_bmoc phss) corecs;

        val (coiter_thmss, corec_thmss) =
          let
            fun mk_goal_cond pos = HOLogic.mk_Trueprop o (not pos ? HOLogic.mk_not);

            fun mk_goal_coiter_like pfss c cps fcoiter_like n k ctr cfs' =
              fold_rev (fold_rev Logic.all) ([c] :: pfss)
                (Logic.list_implies (seq_conds mk_goal_cond n k cps,
                   mk_Trueprop_eq (fcoiter_like $ c, Term.list_comb (ctr, cfs'))));

            fun build_call fiter_likes maybe_tack =
              let
                fun build (T, U) =
                  if T = U then
                    Const (@{const_name id}, T --> T)
                  else
                    (case (find_index (curry (op =) U) fpTs, (T, U)) of
                      (~1, (Type (s, Ts), Type (_, Us))) =>
                      let
                        val map0 = map_of_bnf (the (bnf_of lthy (Long_Name.base_name s)));
                        val mapx = mk_map Ts Us map0;
                        val TUs =
                          map dest_funT (fst (split_last (fst (strip_map_type (fastype_of mapx)))));
                        val args = map build TUs;
                      in Term.list_comb (mapx, args) end
                    | (j, _) => maybe_tack (nth cs j, nth vs j) (nth fiter_likes j))
              in build end;

            fun mk_U maybe_sumT =
              typ_subst (map2 (fn C => fn fpT => (maybe_sumT fpT C, fpT)) Cs fpTs);

            fun repair_calls fiter_likes maybe_sumT maybe_tack
                (cf as Free (_, Type (_, [_, T])) $ _) =
              if exists_subtype (member (op =) Cs) T then
                build_call fiter_likes maybe_tack (T, mk_U maybe_sumT T) $ cf
              else
                cf;

            val cgsss = map (map (map (repair_calls gcoiters (K I) (K I)))) cgsss;
            val chsss = map (map (map (repair_calls hcorecs (curry mk_sumT) (tack z)))) chsss;

            val goal_coiterss =
              map7 (map3 oooo mk_goal_coiter_like pgss) cs cpss gcoiters ns kss ctrss cgsss;
            val goal_corecss =
              map7 (map3 oooo mk_goal_coiter_like phss) cs cpss hcorecs ns kss ctrss chsss;

            val coiter_tacss =
              map3 (map oo mk_coiter_like_tac coiter_defs map_ids) fp_iter_thms pre_map_defs
                ctr_defss;
            val corec_tacss =
              map3 (map oo mk_coiter_like_tac corec_defs map_ids) fp_rec_thms pre_map_defs
                ctr_defss;
          in
            (map2 (map2 (fn goal => fn tac => Skip_Proof.prove lthy [] [] goal (tac o #context)))
               goal_coiterss coiter_tacss,
             map2 (map2 (fn goal => fn tac => Skip_Proof.prove lthy [] [] goal (tac o #context)))
               goal_corecss corec_tacss)
          end;

        val notes =
          [(coitersN, coiter_thmss),
           (corecsN, corec_thmss)]
          |> maps (fn (thmN, thmss) =>
            map2 (fn b => fn thms =>
                ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
              bs thmss);
      in
        lthy |> Local_Theory.notes notes |> snd
      end;

    val lthy' = lthy
      |> fold_map pour_some_sugar_on_type (bs ~~ fpTs ~~ Cs ~~ flds ~~ unfs ~~ fp_iters ~~
        fp_recs ~~ fld_unfs ~~ unf_flds ~~ fld_injects ~~ ns ~~ kss ~~ mss ~~ ctr_binderss ~~
        ctr_mixfixess ~~ ctr_Tsss ~~ disc_binderss ~~ sel_bindersss)
      |>> split_list8
      |> (if lfp then pour_more_sugar_on_lfps else pour_more_sugar_on_gfps);

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      (if lfp then "" else "co") ^ "datatype"));
  in
    (timer; lthy')
  end;

fun datatype_cmd info specs lthy =
  let
    (* TODO: cleaner handling of fake contexts, without "background_theory" *)
    (*the "perhaps o try" below helps gracefully handles the case where the new type is defined in a
      locale and shadows an existing global type*)
    val fake_thy = Theory.copy
      #> fold (fn spec => perhaps (try (Sign.add_type lthy
        (type_binder_of spec, length (type_args_constrained_of spec), mixfix_of spec)))) specs;
    val fake_lthy = Proof_Context.background_theory fake_thy lthy;
  in
    prepare_datatype Syntax.read_typ info specs fake_lthy lthy
  end;

val parse_opt_binding_colon = Scan.optional (Parse.binding --| Parse.$$$ ":") no_binder

val parse_ctr_arg =
  Parse.$$$ "(" |-- parse_opt_binding_colon -- Parse.typ --| Parse.$$$ ")" ||
  (Parse.typ >> pair no_binder);

val parse_single_spec =
  Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword "="} |-- Parse.enum1 "|" (parse_opt_binding_colon -- Parse.binding --
    Scan.repeat parse_ctr_arg -- Parse.opt_mixfix));

val _ =
  Outer_Syntax.local_theory @{command_spec "data"} "define BNF-based inductive datatypes"
    (Parse.and_list1 parse_single_spec >> datatype_cmd true);

val _ =
  Outer_Syntax.local_theory @{command_spec "codata"} "define BNF-based coinductive datatypes"
    (Parse.and_list1 parse_single_spec >> datatype_cmd false);

end;
