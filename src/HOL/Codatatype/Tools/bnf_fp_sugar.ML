(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar for constructing LFPs and GFPs.
*)

signature BNF_FP_SUGAR =
sig
end;

structure BNF_FP_Sugar : BNF_FP_SUGAR =
struct

open BNF_Util
open BNF_Wrap
open BNF_FP_Util
open BNF_LFP
open BNF_GFP
open BNF_FP_Sugar_Tactics

val caseN = "case";
val itersN = "iters";
val recsN = "recs";

fun retype_free (Free (s, _)) T = Free (s, T);

fun flat_list_comb (f, xss) = fold (fn xs => fn t => Term.list_comb (t, xs)) xss f

fun mk_tupled_fun x f xs = HOLogic.tupled_lambda x (Term.list_comb (f, xs));
fun mk_uncurried_fun f xs = mk_tupled_fun (HOLogic.mk_tuple xs) f xs;
fun mk_uncurried2_fun f xss =
  mk_tupled_fun (HOLogic.mk_tuple (map HOLogic.mk_tuple xss)) f (flat xss);

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

fun prepare_datatype prepare_typ gfp specs fake_lthy lthy =
  let
    val constrained_As =
      map (map (apfst (prepare_typ fake_lthy)) o type_args_constrained_of) specs
      |> Library.foldr1 (merge_type_args_constrained lthy);
    val As = map fst constrained_As;
    val As' = map dest_TFree As;

    val _ = (case duplicates (op =) As of [] => ()
      | A :: _ => error ("Duplicate type parameter " ^ quote (Syntax.string_of_typ lthy A)));

    (* TODO: use sort constraints on type args *)

    val N = length specs;

    fun mk_fake_T b =
      Type (fst (Term.dest_Type (Proof_Context.read_type_name fake_lthy true (Binding.name_of b))),
        As);

    val bs = map type_binder_of specs;
    val fake_Ts = map mk_fake_T bs;

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
          quote (Syntax.string_of_typ lthy (TFree A'))));

    val ((Cs, Xs), _) =
      lthy
      |> fold (fold (fn s => Variable.declare_typ (TFree (s, dummyS))) o type_args_of) specs
      |> mk_TFrees N
      ||>> mk_TFrees N;

    fun is_same_fpT (T as Type (s, Us)) (Type (s', Us')) =
        s = s' andalso (Us = Us' orelse error ("Illegal occurrence of recursive type " ^
          quote (Syntax.string_of_typ fake_lthy T)))
      | is_same_fpT _ _ = false;

    fun freeze_fpXs (T as Type (s, Us)) =
        (case find_index (is_same_fpT T) fake_Ts of
          ~1 => Type (s, map freeze_fpXs Us)
        | i => nth Xs i)
      | freeze_fpXs T = T;

    val ctr_TsssXs = map (map (map freeze_fpXs)) fake_ctr_Tsss;
    val sum_prod_TsXs = map (mk_sumTN o map HOLogic.mk_tupleT) ctr_TsssXs;

    val eqs = map dest_TFree Xs ~~ sum_prod_TsXs;

    val ((raw_unfs, raw_flds, raw_fp_iters, raw_fp_recs, unf_flds, fld_unfs, fld_injects), lthy') =
      fp_bnf (if gfp then bnf_gfp else bnf_lfp) bs mixfixes As' eqs lthy;

    val timer = time (Timer.startRealTimer ());

    fun mk_unf_or_fld get_T Ts t =
      let val Type (_, Ts0) = get_T (fastype_of t) in
        Term.subst_atomic_types (Ts0 ~~ Ts) t
      end;

    val mk_unf = mk_unf_or_fld domain_type;
    val mk_fld = mk_unf_or_fld range_type;

    val unfs = map (mk_unf As) raw_unfs;
    val flds = map (mk_fld As) raw_flds;

    val fpTs = map (domain_type o fastype_of) unfs;
    val ctr_Tsss = map (map (map (Term.typ_subst_atomic (Xs ~~ fpTs)))) ctr_TsssXs;

    fun mk_fp_iter_or_rec Ts Us c =
      let
        val (binders, body) = strip_type (fastype_of c);
        val Type (_, Ts0) = if gfp then body else List.last binders;
        val Us0 = map (if gfp then domain_type else body_type) (fst (split_last binders));
      in
        Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) c
      end;

    val fp_iters = map (mk_fp_iter_or_rec As Cs) raw_fp_iters;
    val fp_recs = map (mk_fp_iter_or_rec As Cs) raw_fp_recs;

    fun pour_sugar_on_type ((((((((((((((b, fpT), C), fld), unf), fp_iter), fp_rec), fld_unf),
          unf_fld), fld_inject), ctr_binders), ctr_mixfixes), ctr_Tss), disc_binders), sel_binderss)
        no_defs_lthy =
      let
        val n = length ctr_Tss;
        val ks = 1 upto n;
        val ms = map length ctr_Tss;

        val unfT = domain_type (fastype_of fld);
        val prod_Ts = map HOLogic.mk_tupleT ctr_Tss;
        val case_Ts = map (fn Ts => Ts ---> C) ctr_Tss;

        val ((((u, v), fs), xss), _) =
          lthy
          |> yield_singleton (mk_Frees "u") unfT
          ||>> yield_singleton (mk_Frees "v") fpT
          ||>> mk_Frees "f" case_Ts
          ||>> mk_Freess "x" ctr_Tss;

        val ctr_rhss =
          map2 (fn k => fn xs =>
            fold_rev Term.lambda xs (fld $ mk_InN prod_Ts (HOLogic.mk_tuple xs) k)) ks xss;

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

        val ctrs = map (Morphism.term phi) raw_ctrs;
        val casex = Morphism.term phi raw_case;

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
                (Drule.instantiate' (map (SOME o certifyT lthy) prod_Ts) [] (mk_sumEN n))
              |> Morphism.thm phi;
          in
            mk_exhaust_tac ctxt n ctr_defs fld_iff_unf_thm sumEN_thm'
          end;

        val inject_tacss =
          map2 (fn 0 => K []
                 | _ => fn ctr_def => [fn {context = ctxt, ...} =>
                     mk_inject_tac ctxt ctr_def fld_inject])
            ms ctr_defs;

        val half_distinct_tacss =
          map (map (fn (def, def') => fn {context = ctxt, ...} =>
            mk_half_distinct_tac ctxt fld_inject [def, def'])) (mk_half_pairss ctr_defs);

        val case_tacs =
          map3 (fn k => fn m => fn ctr_def => fn {context = ctxt, ...} =>
            mk_case_tac ctxt n k m case_def ctr_def unf_fld) ks ms ctr_defs;

        val tacss = [exhaust_tac] :: inject_tacss @ half_distinct_tacss @ [case_tacs];

        (* (co)iterators, (co)recursors, (co)induction *)

        val is_fpT = member (op =) fpTs;

        val ns = map length ctr_Tsss;
        val mss = map (map length) ctr_Tsss;
        val Css = map2 replicate ns Cs;

        fun dest_rec_pair (T as Type (@{type_name prod}, Us as [_, U])) =
            if member (op =) Cs U then Us else [T]
          | dest_rec_pair T = [T];

        fun sugar_datatype no_defs_lthy =
          let
            val fp_y_Ts = map domain_type (fst (split_last (binder_types (fastype_of fp_iter))));
            val y_prod_Tss = map2 dest_sumTN ns fp_y_Ts;
            val y_Tsss = map2 (map2 dest_tupleT) mss y_prod_Tss;
            val g_Tss = map2 (map2 (curry (op --->))) y_Tsss Css;
            val iter_T = flat g_Tss ---> fpT --> C;

            val fp_z_Ts = map domain_type (fst (split_last (binder_types (fastype_of fp_rec))));
            val z_prod_Tss = map2 dest_sumTN ns fp_z_Ts;
            val z_Tsss = map2 (map2 dest_tupleT) mss z_prod_Tss;
            val z_Tssss = map (map (map dest_rec_pair)) z_Tsss;
            val h_Tss = map2 (map2 (fold_rev (curry (op --->)))) z_Tssss Css;
            val rec_T = flat h_Tss ---> fpT --> C;

            val ((gss, ysss), _) =
              no_defs_lthy
              |> mk_Freess "f" g_Tss
              ||>> mk_Freesss "x" y_Tsss;

            val hss = map2 (map2 retype_free) gss h_Tss;
            val (zssss, _) =
              no_defs_lthy
              |> mk_Freessss "x" z_Tssss;

            val iter_binder = Binding.suffix_name ("_" ^ iterN) b;
            val rec_binder = Binding.suffix_name ("_" ^ recN) b;

            val iter_free = Free (Binding.name_of iter_binder, iter_T);
            val rec_free = Free (Binding.name_of rec_binder, rec_T);

            val iter_spec =
              mk_Trueprop_eq (flat_list_comb (iter_free, gss),
                Term.list_comb (fp_iter, map2 (mk_sum_caseN oo map2 mk_uncurried_fun) gss ysss));
            val rec_spec =
              mk_Trueprop_eq (flat_list_comb (rec_free, hss),
                Term.list_comb (fp_rec, map2 (mk_sum_caseN oo map2 mk_uncurried2_fun) hss zssss));

            val (([raw_iter, raw_rec], [raw_iter_def, raw_rec_def]), (lthy', lthy)) = no_defs_lthy
              |> apfst split_list o fold_map2 (fn b => fn spec =>
                Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
                #>> apsnd snd) [iter_binder, rec_binder] [iter_spec, rec_spec]
              ||> `Local_Theory.restore;

            (*transforms defined frees into consts (and more)*)
            val phi = Proof_Context.export_morphism lthy lthy';

            val iter_def = Morphism.thm phi raw_iter_def;
            val rec_def = Morphism.thm phi raw_rec_def;

            val iter = Morphism.term phi raw_iter;
            val recx = Morphism.term phi raw_rec;
          in
            ([[ctrs], [[iter]], [[recx]], xss, gss, hss], lthy)
          end;

        fun sugar_codatatype no_defs_lthy = ([], no_defs_lthy);
      in
        wrap_datatype tacss ((ctrs, casex), (disc_binders, sel_binderss)) lthy'
        |> (if gfp then sugar_codatatype else sugar_datatype)
      end;

    fun pour_more_sugar_on_datatypes ([[ctrss], [[iters]], [[recs]], xsss, gsss, hsss], lthy) =
      let
        val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;
        val giters = map2 (curry flat_list_comb) iters gsss;
        val hrecs = map2 (curry flat_list_comb) recs hsss;

        val (iter_thmss, rec_thmss) =
          let
            fun mk_goal_iter_or_rec fc xctr =
              mk_Trueprop_eq (fc $ xctr, fc $ xctr);

            val goal_iterss = map2 (fn giter => map (mk_goal_iter_or_rec giter)) giters xctrss;
            val goal_recss = [];
            val iter_tacss = []; (* ### map (map mk_iter_or_rec_tac); (* needs ctr_def, iter_def, fld_iter *) *)
            val rec_tacss = [];
          in
            (map2 (map2 (Skip_Proof.prove lthy [] [])) goal_iterss iter_tacss,
             map2 (map2 (Skip_Proof.prove lthy [] [])) goal_recss rec_tacss)
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

    val lthy'' = lthy'
      |> fold_map pour_sugar_on_type (bs ~~ fpTs ~~ Cs ~~ flds ~~ unfs ~~ fp_iters ~~ fp_recs ~~
        fld_unfs ~~ unf_flds ~~ fld_injects ~~ ctr_binderss ~~ ctr_mixfixess ~~ ctr_Tsss ~~
        disc_binderss ~~ sel_bindersss)
      |> (if gfp then snd else pour_more_sugar_on_datatypes o apfst transpose);

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      (if gfp then "co" else "") ^ "datatype"));
  in
    (timer; lthy'')
  end;

fun datatype_cmd info specs lthy =
  let
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
    (Parse.and_list1 parse_single_spec >> datatype_cmd false);

val _ =
  Outer_Syntax.local_theory @{command_spec "codata"} "define BNF-based coinductive datatypes"
    (Parse.and_list1 parse_single_spec >> datatype_cmd true);

end;
