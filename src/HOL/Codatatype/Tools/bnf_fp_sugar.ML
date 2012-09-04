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
fun mixfix_of_typ ((_, mx), _) = mx;
fun ctr_specs_of (_, ctr_specs) = ctr_specs;

fun disc_of (((disc, _), _), _) = disc;
fun ctr_of (((_, ctr), _), _) = ctr;
fun args_of ((_, args), _) = args;
fun mixfix_of_ctr (_, mx) = mx;

val lfp_info = bnf_lfp;
val gfp_info = bnf_gfp;

fun prepare_data prepare_typ construct specs fake_lthy lthy =
  let
    val constrained_As =
      map (map (apfst (prepare_typ fake_lthy)) o type_args_constrained_of) specs
      |> Library.foldr1 (merge_type_args_constrained lthy);
    val As = map fst constrained_As;

    val _ = (case duplicates (op =) As of [] => ()
      | T :: _ => error ("Duplicate type parameter " ^ quote (Syntax.string_of_typ lthy T)));

    (* TODO: check that no type variables occur in the rhss that's not in the lhss *)
    (* TODO: use sort constraints on type args *)

    val N = length specs;

    fun mk_T b =
      Type (fst (Term.dest_Type (Proof_Context.read_type_name fake_lthy true (Binding.name_of b))),
        As);

    val bs = map type_binder_of specs;
    val Ts = map mk_T bs;

    val mixfixes = map mixfix_of_typ specs;

    val _ = (case duplicates Binding.eq_name bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val ctr_specss = map ctr_specs_of specs;

    val disc_binderss = map (map disc_of) ctr_specss;
    val ctr_binderss = map (map ctr_of) ctr_specss;
    val ctr_argsss = map (map args_of) ctr_specss;
    val ctr_mixfixess = map (map mixfix_of_ctr) ctr_specss;

    val sel_bindersss = map (map (map fst)) ctr_argsss;
    val ctr_Tsss = map (map (map (prepare_typ fake_lthy o snd))) ctr_argsss;

    val (Bs, C) =
      lthy
      |> fold (fold (fn s => Variable.declare_typ (TFree (s, dummyS))) o type_args_of) specs
      |> mk_TFrees N
      ||> the_single o fst o mk_TFrees 1;

    fun freeze_rec (T as Type (s, Ts')) =
        (case find_index (curry (op =) T) Ts of
          ~1 => Type (s, map freeze_rec Ts')
        | i => nth Bs i)
      | freeze_rec T = T;

    val ctr_TsssBs = map (map (map freeze_rec)) ctr_Tsss;
    val sum_prod_TsBs = map (mk_sumTN o map HOLogic.mk_tupleT) ctr_TsssBs;

    val eqs = map dest_TFree Bs ~~ sum_prod_TsBs;

    val ((raw_unfs, raw_flds, unf_flds, fld_unfs, fld_injects), lthy') =
      fp_bnf construct bs eqs lthy;

    fun mk_unf_or_fld get_foldedT Ts t =
      let val Type (_, Ts0) = get_foldedT (fastype_of t) in
        Term.subst_atomic_types (Ts0 ~~ Ts) t
      end;

    val mk_unf = mk_unf_or_fld domain_type;
    val mk_fld = mk_unf_or_fld range_type;

    val unfs = map (mk_unf As) raw_unfs;
    val flds = map (mk_fld As) raw_flds;

    fun wrap_type ((((((((((b, T), fld), unf), fld_unf), unf_fld), fld_inject), ctr_binders),
        ctr_Tss), disc_binders), sel_binderss) no_defs_lthy =
      let
        val n = length ctr_binders;
        val ks = 1 upto n;
        val ms = map length ctr_Tss;

        val unf_T = domain_type (fastype_of fld);
        val prod_Ts = map HOLogic.mk_tupleT ctr_Tss;
        val caseC_Ts = map (fn Ts => Ts ---> C) ctr_Tss;

        val ((((fs, u), v), xss), _) =
          lthy
          |> mk_Frees "f" caseC_Ts
          ||>> yield_singleton (mk_Frees "u") unf_T
          ||>> yield_singleton (mk_Frees "v") T
          ||>> mk_Freess "x" ctr_Tss;

        val uncurried_fs =
          map2 (fn f => fn xs =>
            HOLogic.tupled_lambda (HOLogic.mk_tuple xs) (Term.list_comb (f, xs))) fs xss;

        val ctr_rhss =
          map2 (fn k => fn xs =>
            fold_rev Term.lambda xs (fld $ mk_InN prod_Ts (HOLogic.mk_tuple xs) k)) ks xss;

        val case_binder = Binding.suffix_name ("_" ^ caseN) b;

        val case_rhs = fold_rev Term.lambda (fs @ [v]) (mk_sum_caseN uncurried_fs $ (unf $ v));

        val (((raw_ctrs, raw_ctr_defs), (raw_case, raw_case_def)), (lthy', lthy)) = no_defs_lthy
          |> apfst split_list o fold_map2 (fn b => fn rhs =>
               Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), rhs)) #>> apsnd snd)
             ctr_binders ctr_rhss
          ||>> (Local_Theory.define ((case_binder, NoSyn), ((Thm.def_binding case_binder, []),
             case_rhs)) #>> apsnd snd)
          ||> `Local_Theory.restore;

        (*transforms defined frees into consts (and more)*)
        val phi = Proof_Context.export_morphism lthy lthy';

        val ctr_defs = map (Morphism.thm phi) raw_ctr_defs;
        val case_def = Morphism.thm phi raw_case_def;

        val ctrs = map (Morphism.term phi) raw_ctrs;
        val casex = Morphism.term phi raw_case;

        val fld_iff_unf_thm =
          let
            val goal =
              fold_rev Logic.all [u, v]
                (mk_Trueprop_eq (HOLogic.mk_eq (v, fld $ u), HOLogic.mk_eq (unf $ v, u)));
          in
            Skip_Proof.prove lthy [] [] goal (fn {context = ctxt, ...} =>
              mk_fld_iff_unf_tac ctxt (map (SOME o certifyT lthy) [unf_T, T]) (certify lthy fld)
                (certify lthy unf) fld_unf unf_fld)
            |> Thm.close_derivation
          end;

        val sumEN_thm = mk_sumEN n;
        val sumEN_thm' =
          let val cTs = map (SOME o certifyT lthy) prod_Ts in
            Local_Defs.unfold lthy @{thms all_unit_eq} (Drule.instantiate' cTs [] sumEN_thm)
          end;

        fun exhaust_tac {context = ctxt, ...} =
          mk_exhaust_tac ctxt n ms ctr_defs fld_iff_unf_thm sumEN_thm';

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
      in
        wrap_data tacss ((ctrs, casex), (disc_binders, sel_binderss)) lthy'
      end;
  in
    lthy'
    |> fold wrap_type (bs ~~ Ts ~~ flds ~~ unfs ~~ fld_unfs ~~ unf_flds ~~ fld_injects ~~
      ctr_binderss ~~ ctr_Tsss ~~ disc_binderss ~~ sel_bindersss)
  end;

fun data_cmd info specs lthy =
  let
    val fake_lthy =
      Proof_Context.theory_of lthy
      |> Theory.copy
      |> Sign.add_types_global (map (fn spec =>
        (type_binder_of spec, length (type_args_constrained_of spec), mixfix_of_typ spec)) specs)
      |> Proof_Context.init_global
  in
    prepare_data Syntax.read_typ info specs fake_lthy lthy
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
    (Parse.and_list1 parse_single_spec >> data_cmd lfp_info);

val _ =
  Outer_Syntax.local_theory @{command_spec "codata"} "define BNF-based coinductive datatypes"
    (Parse.and_list1 parse_single_spec >> data_cmd gfp_info);

end;
