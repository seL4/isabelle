(*  Title:      HOL/Tools/BNF/bnf_fp_def_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2012, 2013, 2014

Sugared datatype and codatatype constructions.
*)

signature BNF_FP_DEF_SUGAR =
sig
  type fp_sugar =
    {T: typ,
     BT: typ,
     X: typ,
     fp: BNF_Util.fp_kind,
     fp_res_index: int,
     fp_res: BNF_FP_Util.fp_result,
     pre_bnf: BNF_Def.bnf,
     absT_info: BNF_Comp.absT_info,
     fp_nesting_bnfs: BNF_Def.bnf list,
     live_nesting_bnfs: BNF_Def.bnf list,
     ctrXs_Tss: typ list list,
     ctr_defs: thm list,
     ctr_sugar: Ctr_Sugar.ctr_sugar,
     co_rec: term,
     co_rec_def: thm,
     maps: thm list,
     common_co_inducts: thm list,
     co_inducts: thm list,
     co_rec_thms: thm list,
     co_rec_discs: thm list,
     co_rec_selss: thm list list,
     rel_injects: thm list,
     rel_distincts: thm list};

  val morph_fp_sugar: morphism -> fp_sugar -> fp_sugar
  val transfer_fp_sugar: theory -> fp_sugar -> fp_sugar
  val fp_sugar_of: Proof.context -> string -> fp_sugar option
  val fp_sugar_of_global: theory -> string -> fp_sugar option
  val fp_sugars_of: Proof.context -> fp_sugar list
  val fp_sugars_of_global: theory -> fp_sugar list
  val fp_sugars_interpretation: string -> (fp_sugar list -> theory -> theory) ->
    (fp_sugar list -> local_theory -> local_theory)-> theory -> theory
  val interpret_fp_sugars: (string -> bool) -> fp_sugar list -> local_theory -> local_theory
  val register_fp_sugars_raw: fp_sugar list -> local_theory -> local_theory
  val register_fp_sugars: (string -> bool) -> fp_sugar list -> local_theory -> local_theory

  val co_induct_of: 'a list -> 'a
  val strong_co_induct_of: 'a list -> 'a

  val flat_corec_preds_predsss_gettersss: 'a list -> 'a list list list -> 'a list list list ->
    'a list
  val liveness_of_fp_bnf: int -> BNF_Def.bnf -> bool list
  val nesting_bnfs: Proof.context -> typ list list list -> typ list -> BNF_Def.bnf list

  type lfp_sugar_thms = (thm list * thm * Token.src list) * (thm list list * Token.src list)

  val morph_lfp_sugar_thms: morphism -> lfp_sugar_thms -> lfp_sugar_thms
  val transfer_lfp_sugar_thms: theory -> lfp_sugar_thms -> lfp_sugar_thms

  type gfp_sugar_thms =
    ((thm list * thm) list * (Token.src list * Token.src list))
    * thm list list
    * thm list list
    * (thm list list * Token.src list)
    * (thm list list list * Token.src list)

  val morph_gfp_sugar_thms: morphism -> gfp_sugar_thms -> gfp_sugar_thms
  val transfer_gfp_sugar_thms: theory -> gfp_sugar_thms -> gfp_sugar_thms

  val mk_co_recs_prelims: BNF_Util.fp_kind -> typ list list list -> typ list -> typ list ->
     typ list -> typ list -> int list -> int list list -> term list -> Proof.context ->
     (term list
      * (typ list list * typ list list list list * term list list * term list list list list) option
      * (string * term list * term list list
         * ((term list list * term list list list) * typ list)) option)
     * Proof.context
  val repair_nullary_single_ctr: typ list list -> typ list list
  val mk_corec_p_pred_types: typ list -> int list -> typ list list
  val mk_corec_fun_arg_types: typ list list list -> typ list -> typ list -> typ list -> int list ->
    int list list -> term ->
    typ list list
    * (typ list list list list * typ list list list * typ list list list list * typ list)
  val define_co_rec_as: BNF_Util.fp_kind -> typ list -> typ -> binding -> term -> local_theory ->
    (term * thm) * local_theory
  val define_rec:
    typ list list * typ list list list list * term list list * term list list list list ->
    (string -> binding) -> typ list -> typ list -> term list -> term -> Proof.context ->
    (term * thm) * Proof.context
  val define_corec: 'a * term list * term list list
      * ((term list list * term list list list) * typ list) -> (string -> binding) -> 'b list ->
    typ list -> term list -> term -> local_theory -> (term * thm) * local_theory
  val mk_induct_attrs: term list list -> Token.src list
  val mk_coinduct_attrs: typ list -> term list list -> term list list -> int list list ->
    Token.src list * Token.src list
  val derive_induct_recs_thms_for_types: (string -> bool) -> BNF_Def.bnf list ->
     ('a * typ list list list list * term list list * 'b) option -> thm -> thm list ->
     BNF_Def.bnf list -> BNF_Def.bnf list -> typ list -> typ list -> typ list ->
     typ list list list -> thm list -> thm list -> thm list -> term list list -> thm list list ->
     term list -> thm list -> Proof.context -> lfp_sugar_thms
  val derive_coinduct_corecs_thms_for_types: BNF_Def.bnf list ->
    string * term list * term list list * ((term list list * term list list list) * typ list) ->
    thm -> thm list -> thm list -> thm list -> BNF_Def.bnf list -> typ list -> typ list ->
    typ list -> typ list list list -> int list list -> int list list -> int list -> thm list ->
    thm list -> (thm -> thm) -> thm list list -> Ctr_Sugar.ctr_sugar list -> term list ->
    thm list -> (thm list -> thm list) -> Proof.context -> gfp_sugar_thms

  val co_datatypes: BNF_Util.fp_kind -> (mixfix list -> binding list -> binding list ->
      binding list list -> binding list -> (string * sort) list -> typ list * typ list list ->
      BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory ->
      BNF_FP_Util.fp_result * local_theory) ->
    Ctr_Sugar.ctr_options
    * ((((((binding option * (typ * sort)) list * binding) * mixfix)
         * ((binding, binding * typ) Ctr_Sugar.ctr_spec * mixfix) list) * (binding * binding))
       * term list) list ->
    local_theory -> local_theory
  val parse_co_datatype_cmd: BNF_Util.fp_kind -> (mixfix list -> binding list -> binding list ->
      binding list list -> binding list -> (string * sort) list -> typ list * typ list list ->
      BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory ->
      BNF_FP_Util.fp_result * local_theory) ->
    (local_theory -> local_theory) parser
end;

structure BNF_FP_Def_Sugar : BNF_FP_DEF_SUGAR =
struct

open Ctr_Sugar
open BNF_FP_Rec_Sugar_Util
open BNF_Util
open BNF_Comp
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar_Tactics

val EqN = "Eq_";

val case_transferN = "case_transfer";
val ctr_transferN = "ctr_transfer";
val disc_transferN = "disc_transfer";
val corec_codeN = "corec_code";
val map_disc_iffN = "map_disc_iff";
val map_selN = "map_sel";
val set_casesN = "set_cases";
val set_introsN = "set_intros";
val set_inductN = "set_induct";
val set_selN = "set_sel";

type fp_sugar =
  {T: typ,
   BT: typ,
   X: typ,
   fp: fp_kind,
   fp_res_index: int,
   fp_res: fp_result,
   pre_bnf: bnf,
   absT_info: absT_info,
   fp_nesting_bnfs: bnf list,
   live_nesting_bnfs: bnf list,
   ctrXs_Tss: typ list list,
   ctr_defs: thm list,
   ctr_sugar: Ctr_Sugar.ctr_sugar,
   co_rec: term,
   co_rec_def: thm,
   maps: thm list,
   common_co_inducts: thm list,
   co_inducts: thm list,
   co_rec_thms: thm list,
   co_rec_discs: thm list,
   co_rec_selss: thm list list,
   rel_injects: thm list,
   rel_distincts: thm list};

fun morph_fp_sugar phi ({T, BT, X, fp, fp_res, fp_res_index, pre_bnf, absT_info, fp_nesting_bnfs,
    live_nesting_bnfs, ctrXs_Tss, ctr_defs, ctr_sugar, co_rec, co_rec_def, maps, common_co_inducts,
    co_inducts, co_rec_thms, co_rec_discs, co_rec_selss, rel_injects, rel_distincts} : fp_sugar) =
  {T = Morphism.typ phi T,
   BT = Morphism.typ phi BT,
   X = Morphism.typ phi X,
   fp = fp,
   fp_res = morph_fp_result phi fp_res,
   fp_res_index = fp_res_index,
   pre_bnf = morph_bnf phi pre_bnf,
   absT_info = morph_absT_info phi absT_info,
   fp_nesting_bnfs = map (morph_bnf phi) fp_nesting_bnfs,
   live_nesting_bnfs = map (morph_bnf phi) live_nesting_bnfs,
   ctrXs_Tss = map (map (Morphism.typ phi)) ctrXs_Tss,
   ctr_defs = map (Morphism.thm phi) ctr_defs,
   ctr_sugar = morph_ctr_sugar phi ctr_sugar,
   co_rec = Morphism.term phi co_rec,
   co_rec_def = Morphism.thm phi co_rec_def,
   maps = map (Morphism.thm phi) maps,
   common_co_inducts = map (Morphism.thm phi) common_co_inducts,
   co_inducts = map (Morphism.thm phi) co_inducts,
   co_rec_thms = map (Morphism.thm phi) co_rec_thms,
   co_rec_discs = map (Morphism.thm phi) co_rec_discs,
   co_rec_selss = map (map (Morphism.thm phi)) co_rec_selss,
   rel_injects = map (Morphism.thm phi) rel_injects,
   rel_distincts = map (Morphism.thm phi) rel_distincts};

val transfer_fp_sugar = morph_fp_sugar o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = fp_sugar Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun fp_sugar_of_generic context =
  Option.map (transfer_fp_sugar (Context.theory_of context)) o Symtab.lookup (Data.get context)

fun fp_sugars_of_generic context =
  Symtab.fold (cons o transfer_fp_sugar (Context.theory_of context) o snd) (Data.get context) [];

val fp_sugar_of = fp_sugar_of_generic o Context.Proof;
val fp_sugar_of_global = fp_sugar_of_generic o Context.Theory;

val fp_sugars_of = fp_sugars_of_generic o Context.Proof;
val fp_sugars_of_global = fp_sugars_of_generic o Context.Theory;

fun co_induct_of (i :: _) = i;
fun strong_co_induct_of [_, s] = s;

structure FP_Sugar_Interpretation = Local_Interpretation
(
  type T = fp_sugar list;
  val eq: T * T -> bool = op = o pairself (map #T);
);

fun with_transfer_fp_sugars g fp_sugars thy = g (map (transfer_fp_sugar thy) fp_sugars) thy;

fun fp_sugars_interpretation name =
  FP_Sugar_Interpretation.interpretation name o with_transfer_fp_sugars;

val interpret_fp_sugars = FP_Sugar_Interpretation.data;

fun register_fp_sugars_raw fp_sugars =
  fold (fn fp_sugar as {T = Type (s, _), ...} =>
      Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Data.map (Symtab.update (s, morph_fp_sugar phi fp_sugar))))
    fp_sugars;

fun register_fp_sugars plugins fp_sugars =
  register_fp_sugars_raw fp_sugars #> interpret_fp_sugars plugins fp_sugars;

fun interpret_bnfs_register_fp_sugars plugins Ts BTs Xs fp pre_bnfs absT_infos fp_nesting_bnfs
    live_nesting_bnfs fp_res ctrXs_Tsss ctr_defss ctr_sugars co_recs co_rec_defs mapss
    common_co_inducts co_inductss co_rec_thmss co_rec_discss co_rec_selsss rel_injectss
    rel_distinctss noted =
  let
    val fp_sugars =
      map_index (fn (kk, T) =>
        {T = T, BT = nth BTs kk, X = nth Xs kk, fp = fp, fp_res = fp_res, fp_res_index = kk,
         pre_bnf = nth pre_bnfs kk, absT_info = nth absT_infos kk,
         fp_nesting_bnfs = fp_nesting_bnfs, live_nesting_bnfs = live_nesting_bnfs,
         ctrXs_Tss = nth ctrXs_Tsss kk, ctr_defs = nth ctr_defss kk, ctr_sugar = nth ctr_sugars kk,
         co_rec = nth co_recs kk, co_rec_def = nth co_rec_defs kk, maps = nth mapss kk,
         common_co_inducts = common_co_inducts, co_inducts = nth co_inductss kk,
         co_rec_thms = nth co_rec_thmss kk, co_rec_discs = nth co_rec_discss kk,
         co_rec_selss = nth co_rec_selsss kk, rel_injects = nth rel_injectss kk,
         rel_distincts = nth rel_distinctss kk}
        |> morph_fp_sugar (substitute_noted_thm noted)) Ts;
  in
    register_fp_sugars_raw fp_sugars
    #> fold (interpret_bnf plugins) (#bnfs fp_res)
    #> interpret_fp_sugars plugins fp_sugars
  end;

fun quasi_unambiguous_case_names names =
  let
    val ps = map (`Long_Name.base_name) names;
    val dups = Library.duplicates (op =) (map fst ps);
    fun underscore s =
      let val ss = space_explode Long_Name.separator s in
        space_implode "_" (drop (length ss - 2) ss)
      end;
  in
    map (fn (base, full) => if member (op =) dups base then underscore full else base) ps
    |> Name.variant_list []
  end;

fun zipper_map f =
  let
    fun zed _ [] = []
      | zed xs (y :: ys) = f (xs, y, ys) :: zed (xs @ [y]) ys
  in zed [] end;

fun uncurry_thm 0 thm = thm
  | uncurry_thm 1 thm = thm
  | uncurry_thm n thm = rotate_prems ~1 (uncurry_thm (n - 1) (rotate_prems 1 (conjI RS thm)));

fun choose_binary_fun fs AB =
  find_first (fastype_of #> binder_types #> (fn [A, B] => AB = (A, B))) fs;
fun build_binary_fun_app fs t u =
  Option.map (rapp u o rapp t) (choose_binary_fun fs (fastype_of t, fastype_of u));

fun build_the_rel rel_table ctxt Rs Ts A B =
  build_rel rel_table ctxt Ts (the o choose_binary_fun Rs) (A, B);
fun build_rel_app ctxt Rs Ts t u =
  build_the_rel [] ctxt Rs Ts (fastype_of t) (fastype_of u) $ t $ u;

fun mk_parametricity_goal ctxt Rs t u =
  let val prem = build_the_rel [] ctxt Rs [] (fastype_of t) (fastype_of u) in
    HOLogic.mk_Trueprop (prem $ t $ u)
  end;

val name_of_set = name_of_const "set function" domain_type;

val mp_conj = @{thm mp_conj};

val fundefcong_attrs = @{attributes [fundef_cong]};
val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};

val lists_bmoc = fold (fn xs => fn t => Term.list_comb (t, xs));

fun flat_corec_predss_getterss qss gss = maps (op @) (qss ~~ gss);

fun flat_corec_preds_predsss_gettersss [] [qss] [gss] = flat_corec_predss_getterss qss gss
  | flat_corec_preds_predsss_gettersss (p :: ps) (qss :: qsss) (gss :: gsss) =
    p :: flat_corec_predss_getterss qss gss @ flat_corec_preds_predsss_gettersss ps qsss gsss;

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

fun mk_xtor_co_recs thy fp fpTs Cs ts0 =
  let
    val nn = length fpTs;
    val (fpTs0, Cs0) =
      map ((fp = Greatest_FP ? swap) o dest_funT o snd o strip_typeN nn o fastype_of) ts0
      |> split_list;
    val rho = tvar_subst thy (fpTs0 @ Cs0) (fpTs @ Cs);
  in
    map (Term.subst_TVars rho) ts0
  end;

fun mk_set Ts t =
  subst_nonatomic_types (snd (Term.dest_Type (domain_type (fastype_of t))) ~~ Ts) t;

fun liveness_of_fp_bnf n bnf =
  (case T_of_bnf bnf of
    Type (_, Ts) => map (not o member (op =) (deads_of_bnf bnf)) Ts
  | _ => replicate n false);

fun cannot_merge_types fp =
  error ("Mutually " ^ co_prefix fp ^ "recursive types must have the same type parameters");

fun merge_type_arg fp T T' = if T = T' then T else cannot_merge_types fp;

fun merge_type_args fp (As, As') =
  if length As = length As' then map2 (merge_type_arg fp) As As' else cannot_merge_types fp;

fun type_args_named_constrained_of_spec (((((ncAs, _), _), _), _), _) = ncAs;
fun type_binding_of_spec (((((_, b), _), _), _), _) = b;
fun mixfix_of_spec ((((_, mx), _), _), _) = mx;
fun mixfixed_ctr_specs_of_spec (((_, mx_ctr_specs), _), _) = mx_ctr_specs;
fun map_binding_of_spec ((_, (b, _)), _) = b;
fun rel_binding_of_spec ((_, (_, b)), _) = b;
fun sel_default_eqs_of_spec (_, ts) = ts;

fun add_nesting_bnf_names Us =
  let
    fun add (Type (s, Ts)) ss =
        let val (needs, ss') = fold_map add Ts ss in
          if exists I needs then (true, insert (op =) s ss') else (false, ss')
        end
      | add T ss = (member (op =) Us T, ss);
  in snd oo add end;

fun nesting_bnfs ctxt ctr_Tsss Us =
  map_filter (bnf_of ctxt) (fold (fold (fold (add_nesting_bnf_names Us))) ctr_Tsss []);

fun indexify proj xs f p = f (find_index (curry (op =) (proj p)) xs) p;

fun massage_simple_notes base =
  filter_out (null o #2)
  #> map (fn (thmN, thms, f_attrs) =>
    ((Binding.qualify true base (Binding.name thmN), []),
     map_index (fn (i, thm) => ([thm], f_attrs i)) thms));

fun massage_multi_notes b_names Ts =
  maps (fn (thmN, thmss, attrs) =>
    map3 (fn b_name => fn Type (T_name, _) => fn thms =>
        ((Binding.qualify true b_name (Binding.name thmN), attrs T_name), [(thms, [])]))
      b_names Ts thmss)
  #> filter_out (null o fst o hd o snd);

fun derive_map_set_rel_thms plugins fp live As Bs abs_inverses ctr_defs' fp_nesting_set_maps
    live_nesting_map_id0s live_nesting_set_maps live_nesting_rel_eqs fp_b_name fp_bnf fpT ctor
    ctor_dtor dtor_ctor pre_map_def pre_set_defs pre_rel_def fp_map_thm fp_set_thms fp_rel_thm
    ctr_Tss abs
    ({casex, case_thms, discs, selss, ctrs, exhaust, exhaust_discs, disc_thmss, sel_thmss, injects,
      distincts, distinct_discsss, ...} : ctr_sugar)
    lthy =
  if live = 0 then
    (([], [], [], []), lthy)
  else
    let
      val n = length ctr_Tss;
      val ks = 1 upto n;
      val ms = map length ctr_Tss;

      val B_ify = Term.typ_subst_atomic (As ~~ Bs);

      val fpBT = B_ify fpT;
      val live_AsBs = filter (op <>) (As ~~ Bs);
      val fTs = map (op -->) live_AsBs;

      val (((((((([C, E], xss), yss), fs), Rs), ta), tb), thesis), names_lthy) = lthy
        |> mk_TFrees 2
        ||>> mk_Freess "x" ctr_Tss
        ||>> mk_Freess "y" (map (map B_ify) ctr_Tss)
        ||>> mk_Frees "f" fTs
        ||>> mk_Frees "R" (map (uncurry mk_pred2T) live_AsBs)
        ||>> yield_singleton (mk_Frees "a") fpT
        ||>> yield_singleton (mk_Frees "b") fpBT
        ||>> apfst HOLogic.mk_Trueprop o yield_singleton (mk_Frees "thesis") HOLogic.boolT;

      val mapx = mk_map live As Bs (map_of_bnf fp_bnf);
      val ctrAs = map (mk_ctr As) ctrs;
      val ctrBs = map (mk_ctr Bs) ctrs;
      val relAsBs = mk_rel live As Bs (rel_of_bnf fp_bnf);
      val setAs = map (mk_set As) (sets_of_bnf fp_bnf);
      val discAs = map (mk_disc_or_sel As) discs;
      val discBs = map (mk_disc_or_sel Bs) discs;
      val selAss = map (map (mk_disc_or_sel As)) selss;
      val discAs_selAss = flat (map2 (map o pair) discAs selAss);

      val ctor_cong =
        if fp = Least_FP then
          Drule.dummy_thm
        else
          let val ctor' = mk_ctor Bs ctor in
            cterm_instantiate_pos [NONE, NONE, SOME (certify lthy ctor')] arg_cong
          end;

      fun mk_cIn ctor k xs =
        let val absT = domain_type (fastype_of ctor) in
          mk_absumprod absT abs n k xs
          |> fp = Greatest_FP ? curry (op $) ctor
          |> certify lthy
        end;

      val cxIns = map2 (mk_cIn ctor) ks xss;
      val cyIns = map2 (mk_cIn (Term.map_types B_ify ctor)) ks yss;

      fun mk_map_thm ctr_def' cxIn =
        fold_thms lthy [ctr_def']
          (unfold_thms lthy (o_apply :: pre_map_def ::
               (if fp = Least_FP then [] else [dtor_ctor]) @ sumprod_thms_map @ abs_inverses)
             (cterm_instantiate_pos (map (SOME o certify lthy) fs @ [SOME cxIn])
                (if fp = Least_FP then fp_map_thm
                 else fp_map_thm RS ctor_cong RS (ctor_dtor RS sym RS trans))))
        |> singleton (Proof_Context.export names_lthy lthy);

      fun mk_set0_thm fp_set_thm ctr_def' cxIn =
        fold_thms lthy [ctr_def']
          (unfold_thms lthy (pre_set_defs @ fp_nesting_set_maps @ live_nesting_set_maps @
               (if fp = Least_FP then [] else [dtor_ctor]) @ basic_sumprod_thms_set @
               @{thms UN_Un sup_assoc[THEN sym]} @ abs_inverses)
             (cterm_instantiate_pos [SOME cxIn] fp_set_thm))
        |> singleton (Proof_Context.export names_lthy lthy);

      fun mk_set0_thms fp_set_thm = map2 (mk_set0_thm fp_set_thm) ctr_defs' cxIns;

      val map_thms = map2 mk_map_thm ctr_defs' cxIns;
      val set0_thmss = map mk_set0_thms fp_set_thms;
      val set0_thms = flat set0_thmss;
      val set_thms = set0_thms
        |> map (unfold_thms lthy @{thms insert_is_Un[THEN sym] Un_empty_left Un_insert_left});

      val rel_infos = (ctr_defs' ~~ cxIns, ctr_defs' ~~ cyIns);

      fun mk_rel_thm postproc ctr_defs' cxIn cyIn =
        fold_thms lthy ctr_defs'
          (unfold_thms lthy (pre_rel_def :: abs_inverses @
               (if fp = Least_FP then [] else [dtor_ctor]) @ sumprod_thms_rel @
               @{thms vimage2p_def sum.inject sum.distinct(1)[THEN eq_False[THEN iffD2]]})
             (cterm_instantiate_pos (map (SOME o certify lthy) Rs @ [SOME cxIn, SOME cyIn])
                fp_rel_thm))
        |> postproc
        |> singleton (Proof_Context.export names_lthy lthy);

      fun mk_rel_inject_thm ((ctr_def', cxIn), (_, cyIn)) =
        mk_rel_thm (unfold_thms lthy @{thms eq_sym_Unity_conv}) [ctr_def'] cxIn cyIn;

      fun mk_rel_intro_thm m thm =
        uncurry_thm m (thm RS iffD2) handle THM _ => thm;

      fun mk_half_rel_distinct_thm ((xctr_def', cxIn), (yctr_def', cyIn)) =
        mk_rel_thm (fn thm => thm RS @{thm eq_False[THEN iffD1]}) [xctr_def', yctr_def'] cxIn cyIn;

      val rel_flip = rel_flip_of_bnf fp_bnf;

      fun mk_other_half_rel_distinct_thm thm =
        flip_rels lthy live thm RS (rel_flip RS sym RS @{thm arg_cong[of _ _ Not]} RS iffD2);

      val rel_inject_thms = map mk_rel_inject_thm (op ~~ rel_infos);
      val rel_intro_thms = map2 mk_rel_intro_thm ms rel_inject_thms;

      val half_rel_distinct_thmss = map (map mk_half_rel_distinct_thm) (mk_half_pairss rel_infos);
      val other_half_rel_distinct_thmss =
        map (map mk_other_half_rel_distinct_thm) half_rel_distinct_thmss;
      val (rel_distinct_thms, _) =
        join_halves n half_rel_distinct_thmss other_half_rel_distinct_thmss;

      val rel_eq_thms =
        map (fn thm => thm RS @{thm eq_False[THEN iffD2]}) rel_distinct_thms @
        map2 (fn thm => fn 0 => thm RS @{thm eq_True[THEN iffD2]} | _ => thm) rel_inject_thms ms;

      val ctr_transfer_thms =
        let val goals = map2 (mk_parametricity_goal names_lthy Rs) ctrAs ctrBs in
          Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced goals)
            (fn {context = ctxt, prems = _} =>
               mk_ctr_transfer_tac ctxt rel_intro_thms live_nesting_rel_eqs)
          |> Conjunction.elim_balanced (length goals)
          |> Proof_Context.export names_lthy lthy
          |> map Thm.close_derivation
        end;

      val (set_cases_thms, set_cases_attrss) =
        let
          fun mk_prems assms elem t ctxt =
            (case fastype_of t of
              Type (type_name, xs) =>
              (case bnf_of ctxt type_name of
                NONE => ([], ctxt)
              | SOME bnf =>
                apfst flat (fold_map (fn set => fn ctxt =>
                  let
                    val T = HOLogic.dest_setT (range_type (fastype_of set));
                    val new_var = not (T = fastype_of elem);
                    val (x, ctxt') =
                      if new_var then yield_singleton (mk_Frees "x") T ctxt else (elem, ctxt);
                  in
                    mk_prems (mk_Trueprop_mem (x, set $ t) :: assms) elem x ctxt'
                    |>> map (new_var ? Logic.all x)
                  end) (map (mk_set xs) (sets_of_bnf bnf)) ctxt))
            | T =>
              rpair ctxt
                (if T = fastype_of elem then [fold (curry Logic.mk_implies) assms thesis] else []));
        in
          split_list (map (fn set =>
            let
              val A = HOLogic.dest_setT (range_type (fastype_of set));
              val (elem, names_lthy) = yield_singleton (mk_Frees "e") A names_lthy;
              val premss =
                map (fn ctr =>
                  let
                    val (args, names_lthy) =
                      mk_Frees "z" (binder_types (fastype_of ctr)) names_lthy;
                  in
                    flat (zipper_map (fn (prev_args, arg, next_args) =>
                      let
                        val (args_with_elem, args_without_elem) =
                          if fastype_of arg = A then
                            (prev_args @ [elem] @ next_args, prev_args @ next_args)
                          else
                            `I (prev_args @ [arg] @ next_args);
                      in
                        mk_prems [mk_Trueprop_eq (ta, Term.list_comb (ctr, args_with_elem))]
                          elem arg names_lthy
                        |> fst
                        |> map (fold_rev Logic.all args_without_elem)
                      end) args)
                  end) ctrAs;
              val goal = Logic.mk_implies (mk_Trueprop_mem (elem, set $ ta), thesis);
              val thm =
                Goal.prove_sorry lthy [] (flat premss) goal (fn {context = ctxt, prems} =>
                  mk_set_cases_tac ctxt (certify ctxt ta) prems exhaust set_thms)
                |> singleton (Proof_Context.export names_lthy lthy)
                |> Thm.close_derivation
                |> rotate_prems ~1;

              val consumes_attr = Attrib.internal (K (Rule_Cases.consumes 1));
              val cases_set_attr =
                Attrib.internal (K (Induct.cases_pred (name_of_set set)));
            in
              (* TODO: @{attributes [elim?]} *)
              (thm, [consumes_attr, cases_set_attr])
            end) setAs)
        end;

      val set_intros_thms =
        let
          fun mk_goals A setA ctr_args t ctxt =
            (case fastype_of t of
              Type (type_name, innerTs) =>
              (case bnf_of ctxt type_name of
                NONE => ([], ctxt)
              | SOME bnf =>
                apfst flat (fold_map (fn set => fn ctxt =>
                  let
                    val T = HOLogic.dest_setT (range_type (fastype_of set));
                    val (x, ctxt') = yield_singleton (mk_Frees "x") T ctxt;
                    val assm = mk_Trueprop_mem (x, set $ t);
                  in
                    apfst (map (Logic.mk_implies o pair assm)) (mk_goals A setA ctr_args x ctxt')
                  end) (map (mk_set innerTs) (sets_of_bnf bnf)) ctxt))
            | T => (if T = A then [mk_Trueprop_mem (t, setA $ ctr_args)] else [], ctxt));

          val (goals, names_lthy) =
            apfst flat (fold_map (fn set => fn ctxt =>
              let val A = HOLogic.dest_setT (range_type (fastype_of set)) in
                apfst flat (fold_map (fn ctr => fn ctxt =>
                  let
                    val (args, ctxt') = mk_Frees "a" (binder_types (fastype_of ctr)) ctxt;
                    val ctr_args = Term.list_comb (ctr, args);
                  in
                    apfst flat (fold_map (mk_goals A set ctr_args) args ctxt')
                  end) ctrAs ctxt)
              end) setAs lthy);
        in
          if null goals then []
          else
            Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced goals)
              (fn {context = ctxt, prems = _} => mk_set_intros_tac ctxt set0_thms)
            |> Conjunction.elim_balanced (length goals)
            |> Proof_Context.export names_lthy lthy
            |> map Thm.close_derivation
        end;

      val rel_sel_thms =
        let
          val selBss = map (map (mk_disc_or_sel Bs)) selss;
          val n = length discAs;

          fun mk_conjunct n k discA selAs discB selBs =
            (if k = n then [] else [HOLogic.mk_eq (discA $ ta, discB $ tb)]) @
            (if null selAs then
               []
             else
                [Library.foldr HOLogic.mk_imp
                   (if n = 1 then [] else [discA $ ta, discB $ tb],
                    Library.foldr1 HOLogic.mk_conj (map2 (build_rel_app names_lthy Rs [])
                      (map (rapp ta) selAs) (map (rapp tb) selBs)))]);

          val goals =
            if n = 0 then
              []
            else
              [mk_Trueprop_eq (build_rel_app names_lthy Rs [] ta tb,
                 (case flat (map5 (mk_conjunct n) (1 upto n) discAs selAss discBs selBss) of
                   [] => @{term True}
                 | conjuncts => Library.foldr1 HOLogic.mk_conj conjuncts))];

          fun prove goal =
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_rel_sel_tac ctxt (certify ctxt ta) (certify ctxt tb) exhaust (flat disc_thmss)
                (flat sel_thmss) rel_inject_thms distincts rel_distinct_thms live_nesting_rel_eqs)
            |> singleton (Proof_Context.export names_lthy lthy)
            |> Thm.close_derivation;
        in
          map prove goals
        end;

      val (rel_cases_thm, rel_cases_attrs) =
        let
          val rel_Rs_a_b = list_comb (relAsBs, Rs) $ ta $ tb;
          val ctrBs = map (mk_ctr Bs) ctrs;

          fun mk_assms ctrA ctrB ctxt =
            let
              val argA_Ts = binder_types (fastype_of ctrA);
              val argB_Ts = binder_types (fastype_of ctrB);
              val ((argAs, argBs), names_ctxt) =  ctxt
                |> mk_Frees "x" argA_Ts
                ||>> mk_Frees "y" argB_Ts;
              val ctrA_args = list_comb (ctrA, argAs);
              val ctrB_args = list_comb (ctrB, argBs);
            in
              (fold_rev Logic.all (argAs @ argBs) (Logic.list_implies
                 (mk_Trueprop_eq (ta, ctrA_args) :: mk_Trueprop_eq (tb, ctrB_args) ::
                    map2 (HOLogic.mk_Trueprop oo build_rel_app lthy Rs []) argAs argBs,
                  thesis)),
               names_ctxt)
            end;

          val (assms, names_lthy) = fold_map2 mk_assms ctrAs ctrBs names_lthy;
          val goal = Logic.list_implies (HOLogic.mk_Trueprop rel_Rs_a_b :: assms, thesis);
          val thm =
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_rel_cases_tac ctxt (certify ctxt ta) (certify ctxt tb) exhaust injects
                rel_inject_thms distincts rel_distinct_thms live_nesting_rel_eqs)
            |> singleton (Proof_Context.export names_lthy lthy)
            |> Thm.close_derivation;

          val ctr_names = quasi_unambiguous_case_names (map name_of_ctr ctrAs);
          val case_names_attr = Attrib.internal (K (Rule_Cases.case_names ctr_names));
          val consumes_attr = Attrib.internal (K (Rule_Cases.consumes 1));
          val cases_pred_attr = Attrib.internal o K o Induct.cases_pred;
        in
          (thm, [consumes_attr, case_names_attr, cases_pred_attr ""])
        end;

      val case_transfer_thms =
        let
          val (R, names_lthy) = yield_singleton (mk_Frees "R") (mk_pred2T C E) names_lthy;

          val caseA = mk_case As C casex;
          val caseB = mk_case Bs E casex;
          val goal = mk_parametricity_goal names_lthy (R :: Rs) caseA caseB;
        in
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
            mk_case_transfer_tac ctxt rel_cases_thm case_thms)
          |> singleton (Proof_Context.export names_lthy lthy)
          |> Thm.close_derivation
        end;

      val disc_transfer_thms =
        let val goals = map2 (mk_parametricity_goal names_lthy Rs) discAs discBs in
          if null goals then
            []
          else
            Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced goals)
              (K (mk_disc_transfer_tac (the_single rel_sel_thms) (the_single exhaust_discs)
                 (flat (flat distinct_discsss))))
            |> Conjunction.elim_balanced (length goals)
            |> Proof_Context.export names_lthy lthy
            |> map Thm.close_derivation
        end;

      val map_disc_iff_thms =
        let
          val discsB = map (mk_disc_or_sel Bs) discs;
          val discsA_t = map (fn disc1 => Term.betapply (disc1, ta)) discAs;

          fun mk_goal (discA_t, discB) =
            if head_of discA_t aconv HOLogic.Not orelse is_refl_bool discA_t then
              NONE
            else
              SOME (mk_Trueprop_eq (betapply (discB, (Term.list_comb (mapx, fs) $ ta)), discA_t));

          val goals = map_filter mk_goal (discsA_t ~~ discsB);
        in
          if null goals then
            []
          else
            Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced goals)
              (fn {context = ctxt, prems = _} =>
                 mk_map_disc_iff_tac ctxt (certify ctxt ta) exhaust (flat disc_thmss)
                   map_thms)
            |> Conjunction.elim_balanced (length goals)
            |> Proof_Context.export names_lthy lthy
            |> map Thm.close_derivation
        end;

      val map_sel_thms =
        let
          fun mk_goal (discA, selA) =
            let
              val prem = Term.betapply (discA, ta);
              val selB = mk_disc_or_sel Bs selA;
              val lhs = selB $ (Term.list_comb (mapx, fs) $ ta);
              val lhsT = fastype_of lhs;
              val map_rhsT =
                map_atyps (perhaps (AList.lookup (op =) (map swap live_AsBs))) lhsT;
              val map_rhs = build_map lthy []
                (the o (AList.lookup (op =) (live_AsBs ~~ fs))) (map_rhsT, lhsT);
              val rhs = (case map_rhs of
                  Const (@{const_name id}, _) => selA $ ta
                | _ => map_rhs $ (selA $ ta));
              val concl = mk_Trueprop_eq (lhs, rhs);
            in
              if is_refl_bool prem then concl
              else Logic.mk_implies (HOLogic.mk_Trueprop prem, concl)
            end;

          val goals = map mk_goal discAs_selAss;
        in
          if null goals then
            []
          else
            Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced goals)
              (fn {context = ctxt, prems = _} =>
                 mk_map_sel_tac ctxt (certify ctxt ta) exhaust (flat disc_thmss) map_thms
                   (flat sel_thmss) live_nesting_map_id0s)
            |> Conjunction.elim_balanced (length goals)
            |> Proof_Context.export names_lthy lthy
            |> map Thm.close_derivation
        end;

      val set_sel_thms =
        let
          fun mk_goal discA selA setA ctxt =
            let
              val prem = Term.betapply (discA, ta);
              val sel_rangeT = range_type (fastype_of selA);
              val A = HOLogic.dest_setT (range_type (fastype_of setA));

              fun travese_nested_types t ctxt =
                (case fastype_of t of
                  Type (type_name, innerTs) =>
                  (case bnf_of ctxt type_name of
                    NONE => ([], ctxt)
                  | SOME bnf =>
                    let
                      fun seq_assm a set ctxt =
                        let
                          val T = HOLogic.dest_setT (range_type (fastype_of set));
                          val (x, ctxt') = yield_singleton (mk_Frees "x") T ctxt;
                          val assm = mk_Trueprop_mem (x, set $ a);
                        in
                          travese_nested_types x ctxt'
                          |>> map (Logic.mk_implies o pair assm)
                        end;
                    in
                      fold_map (seq_assm t o mk_set innerTs) (sets_of_bnf bnf) ctxt
                      |>> flat
                    end)
                | T =>
                  if T = A then ([mk_Trueprop_mem (t, setA $ ta)], ctxt) else ([], ctxt));

              val (concls, ctxt') =
                if sel_rangeT = A then ([mk_Trueprop_mem (selA $ ta, setA $ ta)], ctxt)
                else travese_nested_types (selA $ ta) ctxt;
            in
              if exists_subtype_in [A] sel_rangeT then
                if is_refl_bool prem then (concls, ctxt')
                else (map (Logic.mk_implies o pair (HOLogic.mk_Trueprop prem)) concls, ctxt')
              else
                ([], ctxt)
            end;
          val (goals, names_lthy) = apfst (flat o flat) (fold_map (fn (disc, sel) =>
            fold_map (mk_goal disc sel) setAs) discAs_selAss names_lthy);
        in
          if null goals then
            []
          else
            Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced goals)
              (fn {context = ctxt, prems = _} =>
                 mk_set_sel_tac ctxt (certify ctxt ta) exhaust (flat disc_thmss) (flat sel_thmss)
                   set0_thms)
            |> Conjunction.elim_balanced (length goals)
            |> Proof_Context.export names_lthy lthy
            |> map Thm.close_derivation
        end;

      val code_attrs = if plugins code_plugin then [Code.add_default_eqn_attrib] else [];

      val anonymous_notes =
        [(rel_eq_thms, code_attrs @ nitpicksimp_attrs)]
        |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

      val notes =
        [(case_transferN, [case_transfer_thms], K []),
         (ctr_transferN, ctr_transfer_thms, K []),
         (disc_transferN, disc_transfer_thms, K []),
         (mapN, map_thms, K (code_attrs @ nitpicksimp_attrs @ simp_attrs)),
         (map_disc_iffN, map_disc_iff_thms, K simp_attrs),
         (map_selN, map_sel_thms, K []),
         (rel_casesN, [rel_cases_thm], K rel_cases_attrs),
         (rel_distinctN, rel_distinct_thms, K simp_attrs),
         (rel_injectN, rel_inject_thms, K simp_attrs),
         (rel_introsN, rel_intro_thms, K []),
         (rel_selN, rel_sel_thms, K []),
         (setN, set_thms, K (code_attrs @ nitpicksimp_attrs @ simp_attrs)),
         (set_casesN, set_cases_thms, nth set_cases_attrss),
         (set_introsN, set_intros_thms, K []),
         (set_selN, set_sel_thms, K [])]
        |> massage_simple_notes fp_b_name;

      val (noted, lthy') =
        lthy
        |> Spec_Rules.add Spec_Rules.Equational (`(single o lhs_head_of o hd) map_thms)
        |> fp = Least_FP
          ? Spec_Rules.add Spec_Rules.Equational (`(single o lhs_head_of o hd) rel_eq_thms)
        |> Spec_Rules.add Spec_Rules.Equational (`(single o lhs_head_of o hd) set0_thms)
        |> Local_Theory.notes (anonymous_notes @ notes);

      val subst = Morphism.thm (substitute_noted_thm noted);
    in
      ((map subst map_thms, map subst rel_inject_thms, map subst rel_distinct_thms,
        map (map subst) set0_thmss), lthy')
    end;

type lfp_sugar_thms = (thm list * thm * Token.src list) * (thm list list * Token.src list);

fun morph_lfp_sugar_thms phi ((inducts, induct, induct_attrs), (recss, rec_attrs)) =
  ((map (Morphism.thm phi) inducts, Morphism.thm phi induct, induct_attrs),
   (map (map (Morphism.thm phi)) recss, rec_attrs)) : lfp_sugar_thms;

val transfer_lfp_sugar_thms = morph_lfp_sugar_thms o Morphism.transfer_morphism;

type gfp_sugar_thms =
  ((thm list * thm) list * (Token.src list * Token.src list))
  * thm list list
  * thm list list
  * (thm list list * Token.src list)
  * (thm list list list * Token.src list);

fun morph_gfp_sugar_thms phi ((coinducts_pairs, coinduct_attrs_pair),
    corecss, corec_discss, (corec_disc_iffss, corec_disc_iff_attrs),
    (corec_selsss, corec_sel_attrs)) =
  ((map (apfst (map (Morphism.thm phi)) o apsnd (Morphism.thm phi)) coinducts_pairs,
    coinduct_attrs_pair),
   map (map (Morphism.thm phi)) corecss,
   map (map (Morphism.thm phi)) corec_discss,
   (map (map (Morphism.thm phi)) corec_disc_iffss, corec_disc_iff_attrs),
   (map (map (map (Morphism.thm phi))) corec_selsss, corec_sel_attrs)) : gfp_sugar_thms;

val transfer_gfp_sugar_thms = morph_gfp_sugar_thms o Morphism.transfer_morphism;

fun unzip_recT (Type (@{type_name prod}, _)) T = [T]
  | unzip_recT _ (Type (@{type_name prod}, Ts)) = Ts
  | unzip_recT _ T = [T];

fun mk_recs_args_types ctr_Tsss Cs absTs repTs ns mss ctor_rec_fun_Ts lthy =
  let
    val Css = map2 replicate ns Cs;
    val x_Tssss =
      map6 (fn absT => fn repT => fn n => fn ms => fn ctr_Tss => fn ctor_rec_fun_T =>
          map2 (map2 unzip_recT)
            ctr_Tss (dest_absumprodT absT repT n ms (domain_type ctor_rec_fun_T)))
        absTs repTs ns mss ctr_Tsss ctor_rec_fun_Ts;

    val x_Tsss' = map (map flat_rec_arg_args) x_Tssss;
    val f_Tss = map2 (map2 (curry (op --->))) x_Tsss' Css;

    val ((fss, xssss), lthy) =
      lthy
      |> mk_Freess "f" f_Tss
      ||>> mk_Freessss "x" x_Tssss;
  in
    ((f_Tss, x_Tssss, fss, xssss), lthy)
  end;

fun unzip_corecT (Type (@{type_name sum}, _)) T = [T]
  | unzip_corecT _ (Type (@{type_name sum}, Ts)) = Ts
  | unzip_corecT _ T = [T];

(*avoid "'a itself" arguments in corecursors*)
fun repair_nullary_single_ctr [[]] = [[HOLogic.unitT]]
  | repair_nullary_single_ctr Tss = Tss;

fun mk_corec_fun_arg_types0 ctr_Tsss Cs absTs repTs ns mss fun_Ts =
  let
    val ctr_Tsss' = map repair_nullary_single_ctr ctr_Tsss;
    val g_absTs = map range_type fun_Ts;
    val g_Tsss = map repair_nullary_single_ctr (map5 dest_absumprodT absTs repTs ns mss g_absTs);
    val g_Tssss = map3 (fn C => map2 (map2 (map (curry (op -->) C) oo unzip_corecT)))
      Cs ctr_Tsss' g_Tsss;
    val q_Tssss = map (map (map (fn [_] => [] | [_, T] => [mk_pred1T (domain_type T)]))) g_Tssss;
  in
    (q_Tssss, g_Tsss, g_Tssss, g_absTs)
  end;

fun mk_corec_p_pred_types Cs ns = map2 (fn n => replicate (Int.max (0, n - 1)) o mk_pred1T) ns Cs;

fun mk_corec_fun_arg_types ctr_Tsss Cs absTs repTs ns mss dtor_corec =
  (mk_corec_p_pred_types Cs ns,
   mk_corec_fun_arg_types0 ctr_Tsss Cs absTs repTs ns mss
     (binder_fun_types (fastype_of dtor_corec)));

fun mk_corecs_args_types ctr_Tsss Cs absTs repTs ns mss dtor_corec_fun_Ts lthy =
  let
    val p_Tss = mk_corec_p_pred_types Cs ns;

    val (q_Tssss, g_Tsss, g_Tssss, corec_types) =
      mk_corec_fun_arg_types0 ctr_Tsss Cs absTs repTs ns mss dtor_corec_fun_Ts;

    val (((((Free (x, _), cs), pss), qssss), gssss), lthy) =
      lthy
      |> yield_singleton (mk_Frees "x") dummyT
      ||>> mk_Frees "a" Cs
      ||>> mk_Freess "p" p_Tss
      ||>> mk_Freessss "q" q_Tssss
      ||>> mk_Freessss "g" g_Tssss;

    val cpss = map2 (map o rapp) cs pss;

    fun build_sum_inj mk_inj = build_map lthy [] (uncurry mk_inj o dest_sumT o snd);

    fun build_dtor_corec_arg _ [] [cg] = cg
      | build_dtor_corec_arg T [cq] [cg, cg'] =
        mk_If cq (build_sum_inj Inl_const (fastype_of cg, T) $ cg)
          (build_sum_inj Inr_const (fastype_of cg', T) $ cg');

    val pgss = map3 flat_corec_preds_predsss_gettersss pss qssss gssss;
    val cqssss = map2 (map o map o map o rapp) cs qssss;
    val cgssss = map2 (map o map o map o rapp) cs gssss;
    val cqgsss = map3 (map3 (map3 build_dtor_corec_arg)) g_Tsss cqssss cgssss;
  in
    ((x, cs, cpss, ((pgss, cqgsss), corec_types)), lthy)
  end;

fun mk_co_recs_prelims fp ctr_Tsss fpTs Cs absTs repTs ns mss xtor_co_recs0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val (xtor_co_rec_fun_Ts, xtor_co_recs) =
      mk_xtor_co_recs thy fp fpTs Cs xtor_co_recs0 |> `(binder_fun_types o fastype_of o hd);

    val ((recs_args_types, corecs_args_types), lthy') =
      if fp = Least_FP then
        mk_recs_args_types ctr_Tsss Cs absTs repTs ns mss xtor_co_rec_fun_Ts lthy
        |>> (rpair NONE o SOME)
      else
        mk_corecs_args_types ctr_Tsss Cs absTs repTs ns mss xtor_co_rec_fun_Ts lthy
        |>> (pair NONE o SOME);
  in
    ((xtor_co_recs, recs_args_types, corecs_args_types), lthy')
  end;

fun mk_preds_getterss_join c cps absT abs cqgss =
  let
    val n = length cqgss;
    val ts = map2 (mk_absumprod absT abs n) (1 upto n) cqgss;
  in
    Term.lambda c (mk_IfN absT cps ts)
  end;

fun define_co_rec_as fp Cs fpT b rhs lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val maybe_conceal_def_binding = Thm.def_binding
      #> not (Config.get lthy0 bnf_note_all) ? Binding.conceal;

    val ((cst, (_, def)), (lthy', lthy)) = lthy0
      |> Local_Theory.define ((b, NoSyn), ((maybe_conceal_def_binding b, []), rhs))
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy lthy';

    val cst' = mk_co_rec thy fp Cs fpT (Morphism.term phi cst);
    val def' = Morphism.thm phi def;
  in
    ((cst', def'), lthy')
  end;

fun define_rec (_, _, fss, xssss) mk_binding fpTs Cs reps ctor_rec =
  let
    val nn = length fpTs;
    val (ctor_rec_absTs, fpT) = strip_typeN nn (fastype_of ctor_rec)
      |>> map domain_type ||> domain_type;
  in
    define_co_rec_as Least_FP Cs fpT (mk_binding recN)
      (fold_rev (fold_rev Term.lambda) fss (Term.list_comb (ctor_rec,
         map4 (fn ctor_rec_absT => fn rep => fn fs => fn xsss =>
             mk_case_absumprod ctor_rec_absT rep fs (map (map HOLogic.mk_tuple) xsss)
               (map flat_rec_arg_args xsss))
           ctor_rec_absTs reps fss xssss)))
  end;

fun define_corec (_, cs, cpss, ((pgss, cqgsss), f_absTs)) mk_binding fpTs Cs abss dtor_corec =
  let
    val nn = length fpTs;
    val fpT = range_type (snd (strip_typeN nn (fastype_of dtor_corec)));
  in
    define_co_rec_as Greatest_FP Cs fpT (mk_binding corecN)
      (fold_rev (fold_rev Term.lambda) pgss (Term.list_comb (dtor_corec,
         map5 mk_preds_getterss_join cs cpss f_absTs abss cqgsss)))
  end;

fun postproc_co_induct lthy nn prop prop_conj =
  Drule.zero_var_indexes
  #> `(conj_dests nn)
  #>> map (fn thm => Thm.permute_prems 0 (~1) (thm RS prop))
  ##> (fn thm => Thm.permute_prems 0 (~nn)
    (if nn = 1 then thm RS prop
     else funpow nn (fn thm => unfold_thms lthy @{thms conj_assoc} (thm RS prop_conj)) thm));

fun mk_induct_attrs ctrss =
  let
    val induct_cases = quasi_unambiguous_case_names (maps (map name_of_ctr) ctrss);
    val induct_case_names_attr = Attrib.internal (K (Rule_Cases.case_names induct_cases));
  in
    [induct_case_names_attr]
  end;

fun derive_rel_induct_thms_for_types lthy fpA_Ts As Bs ctrAss ctrAs_Tsss exhausts ctor_rel_induct
    ctor_defss ctor_injects pre_rel_defs abs_inverses live_nesting_rel_eqs =
  let
    val B_ify = typ_subst_nonatomic (As ~~ Bs);
    val fpB_Ts = map B_ify fpA_Ts;
    val ctrBs_Tsss = map (map (map B_ify)) ctrAs_Tsss;
    val ctrBss = map (map (subst_nonatomic_types (As ~~ Bs))) ctrAss;

    val ((((Rs, IRs), ctrAsss), ctrBsss), names_lthy) = lthy
      |> mk_Frees "R" (map2 mk_pred2T As Bs)
      ||>> mk_Frees "IR" (map2 mk_pred2T fpA_Ts fpB_Ts)
      ||>> mk_Freesss "a" ctrAs_Tsss
      ||>> mk_Freesss "b" ctrBs_Tsss;

    val prems =
      let
        fun mk_prem ctrA ctrB argAs argBs =
          fold_rev Logic.all (argAs @ argBs) (fold_rev (curry Logic.mk_implies)
            (map2 (HOLogic.mk_Trueprop oo build_rel_app names_lthy (Rs @ IRs) fpA_Ts) argAs argBs)
            (HOLogic.mk_Trueprop (build_rel_app names_lthy (Rs @ IRs) fpA_Ts
              (Term.list_comb (ctrA, argAs)) (Term.list_comb (ctrB, argBs)))));
      in
        flat (map4 (map4 mk_prem) ctrAss ctrBss ctrAsss ctrBsss)
      end;

    val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_leq
      (map2 (build_the_rel [] lthy (Rs @ IRs) []) fpA_Ts fpB_Ts) IRs));

    val rel_induct0_thm =
      Goal.prove_sorry lthy [] prems goal (fn {context = ctxt, prems} =>
        mk_rel_induct0_tac ctxt ctor_rel_induct prems (map (certify ctxt) IRs) exhausts ctor_defss
          ctor_injects pre_rel_defs abs_inverses live_nesting_rel_eqs)
      |> singleton (Proof_Context.export names_lthy lthy)
      |> Thm.close_derivation;
  in
    (postproc_co_induct lthy (length fpA_Ts) @{thm predicate2D} @{thm predicate2D_conj}
       rel_induct0_thm,
     mk_induct_attrs ctrAss)
  end;

fun derive_induct_recs_thms_for_types plugins pre_bnfs rec_args_typess ctor_induct ctor_rec_thms
    live_nesting_bnfs fp_nesting_bnfs fpTs Cs Xs ctrXs_Tsss fp_abs_inverses fp_type_definitions
    abs_inverses ctrss ctr_defss recs rec_defs lthy =
  let
    val ctr_Tsss = map (map (binder_types o fastype_of)) ctrss;

    val nn = length pre_bnfs;
    val ns = map length ctr_Tsss;
    val mss = map (map length) ctr_Tsss;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val fp_nesting_map_ident0s = map map_ident0_of_bnf fp_nesting_bnfs;
    val fp_nesting_set_maps = maps set_map_of_bnf fp_nesting_bnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val ((((ps, ps'), xsss), us'), names_lthy) =
      lthy
      |> mk_Frees' "P" (map mk_pred1T fpTs)
      ||>> mk_Freesss "x" ctr_Tsss
      ||>> Variable.variant_fixes fp_b_names;

    val us = map2 (curry Free) us' fpTs;

    fun mk_sets bnf =
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

    val setss_fp_nesting = map mk_sets fp_nesting_bnfs;

    val (induct_thms, induct_thm) =
      let
        fun mk_raw_prem_prems _ (x as Free (_, Type _)) (X as TFree _) =
            [([], (find_index (curry (op =) X) Xs + 1, x))]
          | mk_raw_prem_prems names_lthy (x as Free (s, Type (T_name, Ts0))) (Type (_, Xs_Ts0)) =
            (case AList.lookup (op =) setss_fp_nesting T_name of
              NONE => []
            | SOME raw_sets0 =>
              let
                val (Xs_Ts, (Ts, raw_sets)) =
                  filter (exists_subtype_in Xs o fst) (Xs_Ts0 ~~ (Ts0 ~~ raw_sets0))
                  |> split_list ||> split_list;
                val sets = map (mk_set Ts0) raw_sets;
                val (ys, names_lthy') = names_lthy |> mk_Frees s Ts;
                val xysets = map (pair x) (ys ~~ sets);
                val ppremss = map2 (mk_raw_prem_prems names_lthy') ys Xs_Ts;
              in
                flat (map2 (map o apfst o cons) xysets ppremss)
              end)
          | mk_raw_prem_prems _ _ _ = [];

        fun close_prem_prem xs t =
          fold_rev Logic.all (map Free (drop (nn + length xs)
            (rev (Term.add_frees t (map dest_Free xs @ ps'))))) t;

        fun mk_prem_prem xs (xysets, (j, x)) =
          close_prem_prem xs (Logic.list_implies (map (fn (x', (y, set)) =>
              mk_Trueprop_mem (y, set $ x')) xysets,
            HOLogic.mk_Trueprop (nth ps (j - 1) $ x)));

        fun mk_raw_prem phi ctr ctr_Ts ctrXs_Ts =
          let
            val (xs, names_lthy') = names_lthy |> mk_Frees "x" ctr_Ts;
            val pprems = flat (map2 (mk_raw_prem_prems names_lthy') xs ctrXs_Ts);
          in (xs, pprems, HOLogic.mk_Trueprop (phi $ Term.list_comb (ctr, xs))) end;

        fun mk_prem (xs, raw_pprems, concl) =
          fold_rev Logic.all xs (Logic.list_implies (map (mk_prem_prem xs) raw_pprems, concl));

        val raw_premss = map4 (map3 o mk_raw_prem) ps ctrss ctr_Tsss ctrXs_Tsss;

        val goal =
          Library.foldr (Logic.list_implies o apfst (map mk_prem)) (raw_premss,
            HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 (curry (op $)) ps us)));

        val kksss = map (map (map (fst o snd) o #2)) raw_premss;

        val ctor_induct' = ctor_induct OF (map2 mk_absumprodE fp_type_definitions mss);

        val thm =
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
            mk_induct_tac ctxt nn ns mss kksss (flat ctr_defss) ctor_induct' fp_abs_inverses
              abs_inverses fp_nesting_set_maps pre_set_defss)
          |> singleton (Proof_Context.export names_lthy lthy);
      in
        `(conj_dests nn) thm
      end;

    val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;

    fun mk_rec_thmss (_, x_Tssss, fss, _) recs rec_defs ctor_rec_thms =
      let
        val frecs = map (lists_bmoc fss) recs;

        fun mk_goal frec xctr f xs fxs =
          fold_rev (fold_rev Logic.all) (xs :: fss)
            (mk_Trueprop_eq (frec $ xctr, Term.list_comb (f, fxs)));

        fun maybe_tick (T, U) u f =
          if try (fst o HOLogic.dest_prodT) U = SOME T then
            Term.lambda u (HOLogic.mk_prod (u, f $ u))
          else
            f;

        fun build_rec (x as Free (_, T)) U =
          if T = U then
            x
          else
            build_map lthy [] (indexify (perhaps (try (snd o HOLogic.dest_prodT)) o snd) Cs
              (fn kk => fn TU => maybe_tick TU (nth us kk) (nth frecs kk))) (T, U) $ x;

        val fxsss = map2 (map2 (flat_rec_arg_args oo map2 (map o build_rec))) xsss x_Tssss;
        val goalss = map5 (map4 o mk_goal) frecs xctrss fss xsss fxsss;

        val tacss = map4 (map ooo
              mk_rec_tac pre_map_defs (fp_nesting_map_ident0s @ live_nesting_map_ident0s) rec_defs)
            ctor_rec_thms fp_abs_inverses abs_inverses ctr_defss;

        fun prove goal tac =
          Goal.prove_sorry lthy [] [] goal (tac o #context)
          |> Thm.close_derivation;
      in
        map2 (map2 prove) goalss tacss
      end;

    val rec_thmss = mk_rec_thmss (the rec_args_typess) recs rec_defs ctor_rec_thms;

    val code_attrs = if plugins code_plugin then [Code.add_default_eqn_attrib] else [];
  in
    ((induct_thms, induct_thm, mk_induct_attrs ctrss),
     (rec_thmss, code_attrs @ nitpicksimp_attrs @ simp_attrs))
  end;

fun mk_coinduct_attrs fpTs ctrss discss mss =
  let
    val nn = length fpTs;
    val fp_b_names = map base_name_of_typ fpTs;

    fun mk_coinduct_concls ms discs ctrs =
      let
        fun mk_disc_concl disc = [name_of_disc disc];
        fun mk_ctr_concl 0 _ = []
          | mk_ctr_concl _ ctr = [name_of_ctr ctr];
        val disc_concls = map mk_disc_concl (fst (split_last discs)) @ [[]];
        val ctr_concls = map2 mk_ctr_concl ms ctrs;
      in
        flat (map2 append disc_concls ctr_concls)
      end;

    val coinduct_cases = quasi_unambiguous_case_names (map (prefix EqN) fp_b_names);
    val coinduct_conclss =
      map3 (quasi_unambiguous_case_names ooo mk_coinduct_concls) mss discss ctrss;

    val common_coinduct_consumes_attr = Attrib.internal (K (Rule_Cases.consumes nn));
    val coinduct_consumes_attr = Attrib.internal (K (Rule_Cases.consumes 1));

    val coinduct_case_names_attr = Attrib.internal (K (Rule_Cases.case_names coinduct_cases));
    val coinduct_case_concl_attrs =
      map2 (fn casex => fn concls =>
          Attrib.internal (K (Rule_Cases.case_conclusion (casex, concls))))
        coinduct_cases coinduct_conclss;

    val common_coinduct_attrs =
      common_coinduct_consumes_attr :: coinduct_case_names_attr :: coinduct_case_concl_attrs;
    val coinduct_attrs =
      coinduct_consumes_attr :: coinduct_case_names_attr :: coinduct_case_concl_attrs;
  in
    (coinduct_attrs, common_coinduct_attrs)
  end;

fun derive_rel_coinduct_thm_for_types lthy fpA_Ts ns As Bs mss (ctr_sugars : ctr_sugar list)
    abs_inverses abs_injects ctor_injects dtor_ctors rel_pre_defs ctor_defss dtor_rel_coinduct
    live_nesting_rel_eqs =
  let
    val fpB_Ts = map (typ_subst_nonatomic (As ~~ Bs)) fpA_Ts;

    val (Rs, IRs, fpAs, fpBs, names_lthy) =
      let
        val fp_names = map base_name_of_typ fpA_Ts;
        val ((((Rs, IRs), fpAs_names), fpBs_names), names_lthy) = lthy
          |> mk_Frees "R" (map2 mk_pred2T As Bs)
          ||>> mk_Frees "IR" (map2 mk_pred2T fpA_Ts fpB_Ts)
          ||>> Variable.variant_fixes fp_names
          ||>> Variable.variant_fixes (map (suffix "'") fp_names);
      in
        (Rs, IRs, map2 (curry Free) fpAs_names fpA_Ts, map2 (curry Free) fpBs_names fpB_Ts,
         names_lthy)
      end;

    val ((discA_tss, selA_tsss), (discB_tss, selB_tsss)) =
      let
        val discss = map #discs ctr_sugars;
        val selsss = map #selss ctr_sugars;

        fun mk_discss ts Ts = map2 (map o rapp) ts (map (map (mk_disc_or_sel Ts)) discss);
        fun mk_selsss ts Ts =
          map2 (map o map o rapp) ts (map (map (map (mk_disc_or_sel Ts))) selsss);
      in
        ((mk_discss fpAs As, mk_selsss fpAs As),
         (mk_discss fpBs Bs, mk_selsss fpBs Bs))
      end;

    val prems =
      let
        fun mk_prem_ctr_concls n k discA_t selA_ts discB_t selB_ts =
          (if k = n then [] else [HOLogic.mk_eq (discA_t, discB_t)]) @
          (case (selA_ts, selB_ts) of
            ([], []) => []
          | (_ :: _, _ :: _) =>
            [Library.foldr HOLogic.mk_imp
              (if n = 1 then [] else [discA_t, discB_t],
               Library.foldr1 HOLogic.mk_conj
                 (map2 (build_rel_app lthy (Rs @ IRs) fpA_Ts) selA_ts selB_ts))]);

        fun mk_prem_concl n discA_ts selA_tss discB_ts selB_tss =
          Library.foldr1 HOLogic.mk_conj (flat (map5 (mk_prem_ctr_concls n)
            (1 upto n) discA_ts selA_tss discB_ts selB_tss))
          handle List.Empty => @{term True};

        fun mk_prem IR tA tB n discA_ts selA_tss discB_ts selB_tss =
          fold_rev Logic.all [tA, tB] (Logic.mk_implies (HOLogic.mk_Trueprop (IR $ tA $ tB),
            HOLogic.mk_Trueprop (mk_prem_concl n discA_ts selA_tss discB_ts selB_tss)));
      in
        map8 mk_prem IRs fpAs fpBs ns discA_tss selA_tsss discB_tss selB_tsss
      end;

    val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 mk_leq
      IRs (map2 (build_the_rel [] lthy (Rs @ IRs) []) fpA_Ts fpB_Ts)));

    val rel_coinduct0_thm =
      Goal.prove_sorry lthy [] prems goal (fn {context = ctxt, prems} =>
        mk_rel_coinduct0_tac ctxt dtor_rel_coinduct (map (certify ctxt) IRs) prems
          (map #exhaust ctr_sugars) (map (flat o #disc_thmss) ctr_sugars)
          (map (flat o #sel_thmss) ctr_sugars) ctor_defss dtor_ctors ctor_injects abs_injects
          rel_pre_defs abs_inverses live_nesting_rel_eqs)
      |> singleton (Proof_Context.export names_lthy lthy)
      |> Thm.close_derivation;
  in
    (postproc_co_induct lthy (length fpA_Ts) @{thm predicate2D} @{thm predicate2D_conj}
       rel_coinduct0_thm,
     mk_coinduct_attrs fpA_Ts (map #ctrs ctr_sugars) (map #discs ctr_sugars) mss)
  end;

fun derive_set_induct_thms_for_types lthy nn fpTs ctrss setss dtor_set_inducts exhausts
    set_pre_defs ctor_defs dtor_ctors Abs_pre_inverses =
  let
    fun mk_prems A Ps ctr_args t ctxt =
      (case fastype_of t of
        Type (type_name, innerTs) =>
        (case bnf_of ctxt type_name of
          NONE => ([], ctxt)
        | SOME bnf =>
          let
            fun seq_assm a set ctxt =
              let
                val X = HOLogic.dest_setT (range_type (fastype_of set));
                val (x, ctxt') = yield_singleton (mk_Frees "x") X ctxt;
                val assm = mk_Trueprop_mem (x, set $ a);
              in
                (case build_binary_fun_app Ps x a of
                  NONE =>
                  mk_prems A Ps ctr_args x ctxt'
                  |>> map (Logic.all x o Logic.mk_implies o pair assm)
                | SOME f =>
                  ([Logic.all x
                      (Logic.mk_implies (assm,
                         Logic.mk_implies (HOLogic.mk_Trueprop f,
                           HOLogic.mk_Trueprop (the (build_binary_fun_app Ps x ctr_args)))))],
                   ctxt'))
              end;
          in
            fold_map (seq_assm t o mk_set innerTs) (sets_of_bnf bnf) ctxt
            |>> flat
          end)
      | T =>
        if T = A then ([HOLogic.mk_Trueprop (the (build_binary_fun_app Ps t ctr_args))], ctxt)
        else ([], ctxt));

    fun mk_prems_for_ctr A Ps ctr ctxt =
      let
        val (args, ctxt') = mk_Frees "z" (binder_types (fastype_of ctr)) ctxt;
      in
        fold_map (mk_prems A Ps (list_comb (ctr, args))) args ctxt'
        |>> map (fold_rev Logic.all args) o flat
        |>> (fn prems => (prems, mk_names (length prems) (name_of_ctr ctr)))
      end;

    fun mk_prems_and_concl_for_type A Ps ((fpT, ctrs), set) ctxt =
      let
        val ((x, fp), ctxt') = ctxt
          |> yield_singleton (mk_Frees "x") A
          ||>> yield_singleton (mk_Frees "a") fpT;
        val concl = mk_Ball (set $ fp) (Term.absfree (dest_Free x)
          (the (build_binary_fun_app Ps x fp)));
      in
        fold_map (mk_prems_for_ctr A Ps) ctrs ctxt'
        |>> split_list
        |>> map_prod flat flat
        |>> apfst (rpair concl)
      end;

    fun mk_thm ctxt fpTs ctrss sets =
      let
        val A = HOLogic.dest_setT (range_type (fastype_of (hd sets)));
        val (Ps, ctxt') = mk_Frees "P" (map (fn fpT => A --> fpT --> HOLogic.boolT) fpTs) ctxt;
        val (((prems, concl), case_names), ctxt'') =
          fold_map (mk_prems_and_concl_for_type A Ps) (fpTs ~~ ctrss ~~ sets) ctxt'
          |>> apfst split_list o split_list
          |>> apfst (apfst flat)
          |>> apfst (apsnd (Library.foldr1 HOLogic.mk_conj))
          |>> apsnd flat;

        val thm =
          Goal.prove_sorry lthy [] prems (HOLogic.mk_Trueprop concl)
            (fn {context = ctxt, prems} =>
               mk_set_induct0_tac ctxt (map (certify ctxt'') Ps) prems dtor_set_inducts exhausts
                 set_pre_defs ctor_defs dtor_ctors Abs_pre_inverses)
          |> singleton (Proof_Context.export ctxt'' ctxt)
          |> Thm.close_derivation;

        val case_names_attr =
          Attrib.internal (K (Rule_Cases.case_names (quasi_unambiguous_case_names case_names)));
        val induct_set_attrs = map (Attrib.internal o K o Induct.induct_pred o name_of_set) sets;
      in
        (thm, case_names_attr :: induct_set_attrs)
      end
    val consumes_attr = Attrib.internal (K (Rule_Cases.consumes 1));
  in
    map (fn Asets =>
      let
        fun massage_thm thm = rotate_prems (~1) (thm RS bspec);
      in
        mk_thm lthy fpTs ctrss Asets |> nn = 1 ? map_prod massage_thm (cons consumes_attr)
      end) (transpose setss)
  end;

fun derive_coinduct_corecs_thms_for_types pre_bnfs (x, cs, cpss, ((pgss, cqgsss), _))
    dtor_coinduct dtor_injects dtor_ctors dtor_corec_thms live_nesting_bnfs fpTs Cs Xs ctrXs_Tsss
    kss mss ns fp_abs_inverses abs_inverses mk_vimage2p ctr_defss (ctr_sugars : ctr_sugar list)
    corecs corec_defs export_args lthy =
  let
    fun mk_ctor_dtor_corec_thm dtor_inject dtor_ctor corec =
      iffD1 OF [dtor_inject, trans OF [corec, dtor_ctor RS sym]];

    val ctor_dtor_corec_thms = map3 mk_ctor_dtor_corec_thm dtor_injects dtor_ctors dtor_corec_thms;

    val nn = length pre_bnfs;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_rel_defs = map rel_def_of_bnf pre_bnfs;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val live_nesting_rel_eqs = map rel_eq_of_bnf live_nesting_bnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val ctrss = map #ctrs ctr_sugars;
    val discss = map #discs ctr_sugars;
    val selsss = map #selss ctr_sugars;
    val exhausts = map #exhaust ctr_sugars;
    val disc_thmsss = map #disc_thmss ctr_sugars;
    val discIss = map #discIs ctr_sugars;
    val sel_thmsss = map #sel_thmss ctr_sugars;

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

    val coinduct_thms_pairs =
      let
        val uvrs = map3 (fn r => fn u => fn v => r $ u $ v) rs us vs;
        val uv_eqs = map2 (curry HOLogic.mk_eq) us vs;
        val strong_rs =
          map4 (fn u => fn v => fn uvr => fn uv_eq =>
            fold_rev Term.lambda [u, v] (HOLogic.mk_disj (uvr, uv_eq))) us vs uvrs uv_eqs;

        fun build_the_rel rs' T Xs_T =
          build_rel [] lthy [] (fn (_, X) => nth rs' (find_index (curry (op =) X) Xs)) (T, Xs_T)
          |> Term.subst_atomic_types (Xs ~~ fpTs);

        fun build_rel_app rs' usel vsel Xs_T =
          fold rapp [usel, vsel] (build_the_rel rs' (fastype_of usel) Xs_T);

        fun mk_prem_ctr_concls rs' n k udisc usels vdisc vsels ctrXs_Ts =
          (if k = n then [] else [HOLogic.mk_eq (udisc, vdisc)]) @
          (if null usels then
             []
           else
             [Library.foldr HOLogic.mk_imp (if n = 1 then [] else [udisc, vdisc],
                Library.foldr1 HOLogic.mk_conj (map3 (build_rel_app rs') usels vsels ctrXs_Ts))]);

        fun mk_prem_concl rs' n udiscs uselss vdiscs vselss ctrXs_Tss =
          Library.foldr1 HOLogic.mk_conj (flat (map6 (mk_prem_ctr_concls rs' n)
            (1 upto n) udiscs uselss vdiscs vselss ctrXs_Tss))
          handle List.Empty => @{term True};

        fun mk_prem rs' uvr u v n udiscs uselss vdiscs vselss ctrXs_Tss =
          fold_rev Logic.all [u, v] (Logic.mk_implies (HOLogic.mk_Trueprop uvr,
            HOLogic.mk_Trueprop (mk_prem_concl rs' n udiscs uselss vdiscs vselss ctrXs_Tss)));

        val concl =
          HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
            (map3 (fn uvr => fn u => fn v => HOLogic.mk_imp (uvr, HOLogic.mk_eq (u, v)))
               uvrs us vs));

        fun mk_goal rs' =
          Logic.list_implies (map9 (mk_prem rs') uvrs us vs ns udiscss uselsss vdiscss vselsss
            ctrXs_Tsss, concl);

        val goals = map mk_goal [rs, strong_rs];

        fun prove dtor_coinduct' goal =
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
            mk_coinduct_tac ctxt live_nesting_rel_eqs nn ns dtor_coinduct' pre_rel_defs
              fp_abs_inverses abs_inverses dtor_ctors exhausts ctr_defss disc_thmsss sel_thmsss)
          |> singleton (Proof_Context.export names_lthy lthy)
          |> Thm.close_derivation;

        val rel_eqs = map rel_eq_of_bnf pre_bnfs;
        val rel_monos = map rel_mono_of_bnf pre_bnfs;
        val dtor_coinducts =
          [dtor_coinduct, mk_coinduct_strong_thm dtor_coinduct rel_eqs rel_monos mk_vimage2p lthy]
      in
        map2 (postproc_co_induct lthy nn mp mp_conj oo prove) dtor_coinducts goals
      end;

    fun mk_maybe_not pos = not pos ? HOLogic.mk_not;

    val gcorecs = map (lists_bmoc pgss) corecs;

    val corec_thmss =
      let
        fun mk_goal c cps gcorec n k ctr m cfs' =
          fold_rev (fold_rev Logic.all) ([c] :: pgss)
            (Logic.list_implies (seq_conds (HOLogic.mk_Trueprop oo mk_maybe_not) n k cps,
               mk_Trueprop_eq (gcorec $ c, Term.list_comb (ctr, take m cfs'))));

        val mk_U = typ_subst_nonatomic (map2 (fn C => fn fpT => (mk_sumT (fpT, C), fpT)) Cs fpTs);

        fun tack (c, u) f =
          let val x' = Free (x, mk_sumT (fastype_of u, fastype_of c)) in
            Term.lambda x' (mk_case_sum (Term.lambda u u, Term.lambda c (f $ c)) $ x')
          end;

        fun build_corec cqg =
          let val T = fastype_of cqg in
            if exists_subtype_in Cs T then
              let val U = mk_U T in
                build_map lthy [] (indexify fst (map2 (curry mk_sumT) fpTs Cs) (fn kk => fn _ =>
                  tack (nth cs kk, nth us kk) (nth gcorecs kk))) (T, U) $ cqg
              end
            else
              cqg
          end;

        val cqgsss' = map (map (map build_corec)) cqgsss;
        val goalss = map8 (map4 oooo mk_goal) cs cpss gcorecs ns kss ctrss mss cqgsss';

        val tacss =
          map4 (map ooo mk_corec_tac corec_defs live_nesting_map_ident0s)
            ctor_dtor_corec_thms pre_map_defs abs_inverses ctr_defss;

        fun prove goal tac =
          Goal.prove_sorry lthy [] [] goal (tac o #context)
          |> Thm.close_derivation;
      in
        map2 (map2 prove) goalss tacss
        |> map (map (unfold_thms lthy @{thms case_sum_if}))
      end;

    val corec_disc_iff_thmss =
      let
        fun mk_goal c cps gcorec n k disc =
          mk_Trueprop_eq (disc $ (gcorec $ c),
            if n = 1 then @{const True}
            else Library.foldr1 HOLogic.mk_conj (seq_conds mk_maybe_not n k cps));

        val goalss = map6 (map2 oooo mk_goal) cs cpss gcorecs ns kss discss;

        fun mk_case_split' cp = Drule.instantiate' [] [SOME (certify lthy cp)] @{thm case_split};

        val case_splitss' = map (map mk_case_split') cpss;

        val tacss = map3 (map oo mk_corec_disc_iff_tac) case_splitss' corec_thmss disc_thmsss;

        fun prove goal tac =
          Goal.prove_sorry lthy [] [] goal (tac o #context)
          |> singleton export_args
          |> singleton (Proof_Context.export names_lthy lthy)
          |> Thm.close_derivation;

        fun proves [_] [_] = []
          | proves goals tacs = map2 prove goals tacs;
      in
        map2 proves goalss tacss
      end;

    fun mk_corec_disc_thms corecs discIs = map (op RS) (corecs ~~ discIs);

    val corec_disc_thmss = map2 mk_corec_disc_thms corec_thmss discIss;

    fun mk_corec_sel_thm corec_thm sel sel_thm =
      let
        val (domT, ranT) = dest_funT (fastype_of sel);
        val arg_cong' =
          Drule.instantiate' (map (SOME o certifyT lthy) [domT, ranT])
            [NONE, NONE, SOME (certify lthy sel)] arg_cong
          |> Thm.varifyT_global;
        val sel_thm' = sel_thm RSN (2, trans);
      in
        corec_thm RS arg_cong' RS sel_thm'
      end;

    fun mk_corec_sel_thms corec_thmss =
      map3 (map3 (map2 o mk_corec_sel_thm)) corec_thmss selsss sel_thmsss;

    val corec_sel_thmsss = mk_corec_sel_thms corec_thmss;
  in
    ((coinduct_thms_pairs,
      mk_coinduct_attrs fpTs (map #ctrs ctr_sugars) (map #discs ctr_sugars) mss),
     corec_thmss,
     corec_disc_thmss,
     (corec_disc_iff_thmss, simp_attrs),
     (corec_sel_thmsss, simp_attrs))
  end;

fun define_co_datatypes prepare_constraint prepare_typ prepare_term fp construct_fp
    ((plugins, discs_sels0), specs) no_defs_lthy0 =
  let
    (* TODO: sanity checks on arguments *)

    val discs_sels = discs_sels0 orelse fp = Greatest_FP;

    val nn = length specs;
    val fp_bs = map type_binding_of_spec specs;
    val fp_b_names = map Binding.name_of fp_bs;
    val fp_common_name = mk_common_name fp_b_names;
    val map_bs = map map_binding_of_spec specs;
    val rel_bs = map rel_binding_of_spec specs;

    fun prepare_type_arg (_, (ty, c)) =
      let val TFree (s, _) = prepare_typ no_defs_lthy0 ty in
        TFree (s, prepare_constraint no_defs_lthy0 c)
      end;

    val Ass0 = map (map prepare_type_arg o type_args_named_constrained_of_spec) specs;
    val unsorted_Ass0 = map (map (resort_tfree_or_tvar @{sort type})) Ass0;
    val unsorted_As = Library.foldr1 (merge_type_args fp) unsorted_Ass0;
    val num_As = length unsorted_As;

    val set_boss = map (map fst o type_args_named_constrained_of_spec) specs;
    val set_bss = map (map (the_default Binding.empty)) set_boss;

    val (((Bs0, Cs), Xs), no_defs_lthy) =
      no_defs_lthy0
      |> fold (Variable.declare_typ o resort_tfree_or_tvar dummyS) unsorted_As
      |> mk_TFrees num_As
      ||>> mk_TFrees nn
      ||>> variant_tfrees fp_b_names;

    fun add_fake_type spec =
      Typedecl.basic_typedecl (type_binding_of_spec spec, num_As, mixfix_of_spec spec);

    val (fake_T_names, fake_lthy) = fold_map add_fake_type specs no_defs_lthy0;

    val qsoty = quote o Syntax.string_of_typ fake_lthy;

    val _ = (case Library.duplicates (op =) unsorted_As of [] => ()
      | A :: _ => error ("Duplicate type parameter " ^ qsoty A ^ " in " ^ co_prefix fp ^
          "datatype specification"));

    val bad_args =
      map (Logic.type_map (singleton (Variable.polymorphic no_defs_lthy0))) unsorted_As
      |> filter_out Term.is_TVar;
    val _ = null bad_args orelse
      error ("Locally fixed type argument " ^ qsoty (hd bad_args) ^ " in " ^ co_prefix fp ^
        "datatype specification");

    val mixfixes = map mixfix_of_spec specs;

    val _ = (case Library.duplicates Binding.eq_name fp_bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val mx_ctr_specss = map mixfixed_ctr_specs_of_spec specs;
    val ctr_specss = map (map fst) mx_ctr_specss;
    val ctr_mixfixess = map (map snd) mx_ctr_specss;

    val disc_bindingss = map (map disc_of_ctr_spec) ctr_specss;
    val ctr_bindingss =
      map2 (fn fp_b_name => map (Binding.qualify false fp_b_name o ctr_of_ctr_spec)) fp_b_names
        ctr_specss;
    val ctr_argsss = map (map args_of_ctr_spec) ctr_specss;

    val sel_bindingsss = map (map (map fst)) ctr_argsss;
    val fake_ctr_Tsss0 = map (map (map (prepare_typ fake_lthy o snd))) ctr_argsss;
    val raw_sel_default_eqss = map sel_default_eqs_of_spec specs;

    val (As :: _) :: fake_ctr_Tsss =
      burrow (burrow (Syntax.check_typs fake_lthy)) (Ass0 :: fake_ctr_Tsss0);
    val As' = map dest_TFree As;

    val rhs_As' = fold (fold (fold Term.add_tfreesT)) fake_ctr_Tsss [];
    val _ = (case subtract (op =) As' rhs_As' of [] => ()
      | extras => error ("Extra type variables on right-hand side: " ^
          commas (map (qsoty o TFree) extras)));

    val fake_Ts = map (fn s => Type (s, As)) fake_T_names;

    fun eq_fpT_check (T as Type (s, Ts)) (T' as Type (s', Ts')) =
        s = s' andalso (Ts = Ts' orelse
          error ("Wrong type arguments in " ^ co_prefix fp ^ "recursive type " ^ qsoty T ^
            " (expected " ^ qsoty T' ^ ")"))
      | eq_fpT_check _ _ = false;

    fun freeze_fp (T as Type (s, Ts)) =
        (case find_index (eq_fpT_check T) fake_Ts of
          ~1 => Type (s, map freeze_fp Ts)
        | kk => nth Xs kk)
      | freeze_fp T = T;

    val unfreeze_fp = Term.typ_subst_atomic (Xs ~~ fake_Ts);

    val ctrXs_Tsss = map (map (map freeze_fp)) fake_ctr_Tsss;
    val ctrXs_repTs = map mk_sumprodT_balanced ctrXs_Tsss;

    val fp_eqs =
      map dest_TFree Xs ~~ map (Term.typ_subst_atomic (As ~~ unsorted_As)) ctrXs_repTs;

    val killed_As =
      map_filter (fn (A, set_bos) => if exists is_none set_bos then SOME A else NONE)
        (unsorted_As ~~ transpose set_boss);

    val ((pre_bnfs, absT_infos), (fp_res as {bnfs = fp_bnfs as any_fp_bnf :: _, ctors = ctors0,
             dtors = dtors0, xtor_co_recs = xtor_co_recs0, xtor_co_induct, dtor_ctors,
             ctor_dtors, ctor_injects, dtor_injects, xtor_map_thms, xtor_set_thmss, xtor_rel_thms,
             xtor_co_rec_thms, rel_xtor_co_induct_thm, dtor_set_induct_thms, ...},
           lthy)) =
      fp_bnf (construct_fp mixfixes map_bs rel_bs set_bss) fp_bs (map dest_TFree unsorted_As)
        (map dest_TFree killed_As) fp_eqs no_defs_lthy0
      handle BAD_DEAD (X, X_backdrop) =>
        (case X_backdrop of
          Type (bad_tc, _) =>
          let
            val fake_T = qsoty (unfreeze_fp X);
            val fake_T_backdrop = qsoty (unfreeze_fp X_backdrop);
            fun register_hint () =
              "\nUse the " ^ quote (fst (fst @{command_spec "bnf"})) ^ " command to register " ^
              quote bad_tc ^ " as a bounded natural functor to allow nested (co)recursion through \
              \it";
          in
            if is_some (bnf_of no_defs_lthy bad_tc) orelse
               is_some (fp_sugar_of no_defs_lthy bad_tc) then
              error ("Inadmissible " ^ co_prefix fp ^ "recursive occurrence of type " ^ fake_T ^
                " in type expression " ^ fake_T_backdrop)
            else if is_some (Old_Datatype_Data.get_info (Proof_Context.theory_of no_defs_lthy)
                bad_tc) then
              error ("Unsupported " ^ co_prefix fp ^ "recursive occurrence of type " ^ fake_T ^
                " via the old-style datatype " ^ quote bad_tc ^ " in type expression " ^
                fake_T_backdrop ^ register_hint ())
            else
              error ("Unsupported " ^ co_prefix fp ^ "recursive occurrence of type " ^ fake_T ^
                " via type constructor " ^ quote bad_tc ^ " in type expression " ^ fake_T_backdrop ^
                register_hint ())
          end);

    val abss = map #abs absT_infos;
    val reps = map #rep absT_infos;
    val absTs = map #absT absT_infos;
    val repTs = map #repT absT_infos;
    val abs_injects = map #abs_inject absT_infos;
    val abs_inverses = map #abs_inverse absT_infos;
    val type_definitions = map #type_definition absT_infos;

    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    val fp_nesting_bnfs = nesting_bnfs lthy ctrXs_Tsss Xs;
    val live_nesting_bnfs = nesting_bnfs lthy ctrXs_Tsss As;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val pre_rel_defs = map rel_def_of_bnf pre_bnfs;
    val fp_nesting_set_maps = maps set_map_of_bnf fp_nesting_bnfs;
    val live_nesting_map_id0s = map map_id0_of_bnf live_nesting_bnfs;
    val live_nesting_set_maps = maps set_map_of_bnf live_nesting_bnfs;
    val live_nesting_rel_eqs = map rel_eq_of_bnf live_nesting_bnfs;

    val live = live_of_bnf any_fp_bnf;
    val _ =
      if live = 0 andalso exists (not o Binding.is_empty) (map_bs @ rel_bs) then
        warning "Map function and relator names ignored"
      else
        ();

    val Bs =
      map3 (fn alive => fn A as TFree (_, S) => fn B =>
          if alive then resort_tfree_or_tvar S B else A)
        (liveness_of_fp_bnf num_As any_fp_bnf) As Bs0;

    val B_ify = Term.typ_subst_atomic (As ~~ Bs);

    val ctors = map (mk_ctor As) ctors0;
    val dtors = map (mk_dtor As) dtors0;

    val fpTs = map (domain_type o fastype_of) dtors;
    val fpBTs = map B_ify fpTs;

    val code_attrs = if plugins code_plugin then [Code.add_default_eqn_attrib] else [];

    val ctr_Tsss = map (map (map (Term.typ_subst_atomic (Xs ~~ fpTs)))) ctrXs_Tsss;
    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;

    val ((xtor_co_recs, recs_args_types, corecs_args_types), lthy') =
      mk_co_recs_prelims fp ctr_Tsss fpTs Cs absTs repTs ns mss xtor_co_recs0 lthy;

    fun define_ctrs_dtrs_for_type (((((((((((((((((((((((((((fp_bnf, fp_b), fpT), ctor), dtor),
              xtor_co_rec), ctor_dtor), dtor_ctor), ctor_inject), pre_map_def), pre_set_defs),
            pre_rel_def), fp_map_thm), fp_set_thms), fp_rel_thm), n), ks), ms), abs),
          abs_inject), abs_inverse), type_definition), ctr_bindings), ctr_mixfixes), ctr_Tss),
        disc_bindings), sel_bindingss), raw_sel_default_eqs) no_defs_lthy =
      let
        val fp_b_name = Binding.name_of fp_b;

        val ctr_absT = domain_type (fastype_of ctor);

        val (((w, xss), u'), _) = no_defs_lthy
          |> yield_singleton (mk_Frees "w") ctr_absT
          ||>> mk_Freess "x" ctr_Tss
          ||>> yield_singleton Variable.variant_fixes fp_b_name;

        val u = Free (u', fpT);

        val ctr_rhss =
          map2 (fn k => fn xs => fold_rev Term.lambda xs (ctor $ mk_absumprod ctr_absT abs n k xs))
            ks xss;

        val maybe_conceal_def_binding = Thm.def_binding
          #> not (Config.get no_defs_lthy bnf_note_all) ? Binding.conceal;

        val ((raw_ctrs, raw_ctr_defs), (lthy', lthy)) = no_defs_lthy
          |> apfst split_list o fold_map3 (fn b => fn mx => fn rhs =>
              Local_Theory.define ((b, mx), ((maybe_conceal_def_binding b, []), rhs)) #>> apsnd snd)
            ctr_bindings ctr_mixfixes ctr_rhss
          ||> `Local_Theory.restore;

        val phi = Proof_Context.export_morphism lthy lthy';

        val ctr_defs = map (Morphism.thm phi) raw_ctr_defs;
        val ctr_defs' =
          map2 (fn m => fn def => mk_unabs_def m (def RS meta_eq_to_obj_eq)) ms ctr_defs;

        val ctrs0 = map (Morphism.term phi) raw_ctrs;
        val ctrs = map (mk_ctr As) ctrs0;

        fun wrap_ctrs lthy =
          let
            fun exhaust_tac {context = ctxt, prems = _} =
              let
                val ctor_iff_dtor_thm =
                  let
                    val goal =
                      fold_rev Logic.all [w, u]
                        (mk_Trueprop_eq (HOLogic.mk_eq (u, ctor $ w), HOLogic.mk_eq (dtor $ u, w)));
                  in
                    Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                      mk_ctor_iff_dtor_tac ctxt (map (SOME o certifyT lthy) [ctr_absT, fpT])
                        (certify lthy ctor) (certify lthy dtor) ctor_dtor dtor_ctor)
                    |> Morphism.thm phi
                    |> Thm.close_derivation
                  end;

                val sumEN_thm' =
                  unfold_thms lthy @{thms unit_all_eq1} (mk_absumprodE type_definition ms)
                  |> Morphism.thm phi;
              in
                mk_exhaust_tac ctxt n ctr_defs ctor_iff_dtor_thm sumEN_thm'
              end;

            val inject_tacss =
              map2 (fn ctr_def => fn 0 => [] | _ => [fn {context = ctxt, ...} =>
                mk_inject_tac ctxt ctr_def ctor_inject abs_inject]) ctr_defs ms;

            val half_distinct_tacss =
              map (map (fn (def, def') => fn {context = ctxt, ...} =>
                  mk_half_distinct_tac ctxt ctor_inject abs_inject [def, def']))
                (mk_half_pairss (`I ctr_defs));

            val tacss = [exhaust_tac] :: inject_tacss @ half_distinct_tacss;

            val sel_Tss = map (map (curry (op -->) fpT)) ctr_Tss;
            val sel_bTs =
              flat sel_bindingss ~~ flat sel_Tss
              |> filter_out (Binding.is_empty o fst)
              |> distinct (Binding.eq_name o pairself fst);
            val sel_default_lthy = fake_local_theory_for_sel_defaults sel_bTs lthy;

            val sel_default_eqs = map (prepare_term sel_default_lthy) raw_sel_default_eqs;

            fun ctr_spec_of disc_b ctr0 sel_bs = ((disc_b, ctr0), sel_bs);
            val ctr_specs = map3 ctr_spec_of disc_bindings ctrs0 sel_bindingss;

            val (ctr_sugar as {case_cong, ...}, lthy') =
              free_constructors tacss ((((plugins, discs_sels), standard_binding), ctr_specs),
                sel_default_eqs) lthy

            val anonymous_notes =
              [([case_cong], fundefcong_attrs)]
              |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));
          in
            (ctr_sugar, lthy' |> Local_Theory.notes anonymous_notes |> snd)
          end;

        fun mk_binding pre = Binding.qualify false fp_b_name (Binding.prefix_name (pre ^ "_") fp_b);

        fun massage_res (((ctr_sugar, maps_sets_rels), co_rec_res), lthy) =
          (((maps_sets_rels, (ctrs, xss, ctr_defs, ctr_sugar)), co_rec_res), lthy);
      in
        (wrap_ctrs
         #> (fn (ctr_sugar, lthy) =>
           derive_map_set_rel_thms plugins fp live As Bs abs_inverses ctr_defs' fp_nesting_set_maps
             live_nesting_map_id0s live_nesting_set_maps live_nesting_rel_eqs fp_b_name fp_bnf fpT
             ctor ctor_dtor dtor_ctor pre_map_def pre_set_defs pre_rel_def fp_map_thm fp_set_thms
             fp_rel_thm ctr_Tss abs ctr_sugar lthy
           |>> pair ctr_sugar)
         ##>>
           (if fp = Least_FP then define_rec (the recs_args_types) mk_binding fpTs Cs reps
           else define_corec (the corecs_args_types) mk_binding fpTs Cs abss) xtor_co_rec
         #> massage_res, lthy')
      end;

    fun wrap_ctrs_derive_map_set_rel_thms_define_co_rec_for_types (wrap_one_etc, lthy) =
      fold_map I wrap_one_etc lthy
      |>> apsnd split_list o apfst (apsnd split_list4 o apfst split_list4 o split_list)
        o split_list;

    fun mk_simp_thms ({injects, distincts, case_thms, ...} : ctr_sugar) co_recs mapsx rel_injects
        rel_distincts setss =
      injects @ distincts @ case_thms @ co_recs @ mapsx @ rel_injects @ rel_distincts @ flat setss;

    fun derive_note_induct_recs_thms_for_types
        ((((mapss, rel_injectss, rel_distinctss, setss), (ctrss, _, ctr_defss, ctr_sugars)),
          (recs, rec_defs)), lthy) =
      let
        val ((induct_thms, induct_thm, induct_attrs), (rec_thmss, rec_attrs)) =
          derive_induct_recs_thms_for_types plugins pre_bnfs recs_args_types xtor_co_induct
            xtor_co_rec_thms live_nesting_bnfs fp_nesting_bnfs fpTs Cs Xs ctrXs_Tsss abs_inverses
            type_definitions abs_inverses ctrss ctr_defss recs rec_defs lthy;

        val induct_type_attr = Attrib.internal o K o Induct.induct_type;
        val induct_pred_attr = Attrib.internal o K o Induct.induct_pred;

        val ((rel_induct_thmss, common_rel_induct_thms),
             (rel_induct_attrs, common_rel_induct_attrs)) =
          if live = 0 then
            ((replicate nn [], []), ([], []))
          else
            let
              val ((rel_induct_thms, common_rel_induct_thm), rel_induct_attrs) =
                derive_rel_induct_thms_for_types lthy fpTs As Bs ctrss ctr_Tsss
                  (map #exhaust ctr_sugars) rel_xtor_co_induct_thm ctr_defss ctor_injects
                  pre_rel_defs abs_inverses live_nesting_rel_eqs;
            in
              ((map single rel_induct_thms, single common_rel_induct_thm),
               (rel_induct_attrs, rel_induct_attrs))
            end;

        val simp_thmss =
          map6 mk_simp_thms ctr_sugars rec_thmss mapss rel_injectss rel_distinctss setss;

        val common_notes =
          (if nn > 1 then
             [(inductN, [induct_thm], K induct_attrs),
              (rel_inductN, common_rel_induct_thms, K common_rel_induct_attrs)]
           else
             [])
          |> massage_simple_notes fp_common_name;

        val notes =
          [(inductN, map single induct_thms, fn T_name => induct_attrs @ [induct_type_attr T_name]),
           (recN, rec_thmss, K rec_attrs),
           (rel_inductN, rel_induct_thmss, K (rel_induct_attrs @ [induct_pred_attr ""])),
           (simpsN, simp_thmss, K [])]
          |> massage_multi_notes fp_b_names fpTs;
      in
        lthy
        |> Spec_Rules.add Spec_Rules.Equational (recs, flat rec_thmss)
        |> Local_Theory.notes (common_notes @ notes)
        (* for "datatype_realizer.ML": *)
        |>> name_noted_thms
          (fst (dest_Type (hd fpTs)) ^ (implode (map (prefix "_") (tl fp_b_names)))) inductN
        |-> interpret_bnfs_register_fp_sugars plugins fpTs fpBTs Xs Least_FP pre_bnfs absT_infos
          fp_nesting_bnfs live_nesting_bnfs fp_res ctrXs_Tsss ctr_defss ctr_sugars recs rec_defs
          mapss [induct_thm] (map single induct_thms) rec_thmss (replicate nn []) (replicate nn [])
          rel_injectss rel_distinctss
      end;

    fun derive_note_coinduct_corecs_thms_for_types
        ((((mapss, rel_injectss, rel_distinctss, setss), (_, _, ctr_defss, ctr_sugars)),
          (corecs, corec_defs)), lthy) =
      let
        val (([(coinduct_thms, coinduct_thm), (coinduct_strong_thms, coinduct_strong_thm)],
              (coinduct_attrs, common_coinduct_attrs)),
             corec_thmss, corec_disc_thmss,
             (corec_disc_iff_thmss, corec_disc_iff_attrs), (corec_sel_thmsss, corec_sel_attrs)) =
          derive_coinduct_corecs_thms_for_types pre_bnfs (the corecs_args_types) xtor_co_induct
            dtor_injects dtor_ctors xtor_co_rec_thms live_nesting_bnfs fpTs Cs Xs ctrXs_Tsss kss mss
            ns abs_inverses abs_inverses I ctr_defss ctr_sugars corecs corec_defs
            (Proof_Context.export lthy' no_defs_lthy) lthy;

        fun distinct_prems ctxt thm =
          Goal.prove (*no sorry*) ctxt [] []
            (thm |> Thm.prop_of |> Logic.strip_horn |>> distinct (op aconv) |> Logic.list_implies)
            (fn _ => HEADGOAL (cut_tac thm THEN' atac) THEN ALLGOALS eq_assume_tac);

        fun eq_ifIN _ [thm] = thm
          | eq_ifIN ctxt (thm :: thms) =
              distinct_prems ctxt (@{thm eq_ifI} OF
                (map (unfold_thms ctxt @{thms atomize_imp[of _ "t = u" for t u]})
                  [thm, eq_ifIN ctxt thms]));

        val corec_code_thms = map (eq_ifIN lthy) corec_thmss;
        val corec_sel_thmss = map flat corec_sel_thmsss;

        val coinduct_type_attr = Attrib.internal o K o Induct.coinduct_type;
        val coinduct_pred_attr = Attrib.internal o K o Induct.coinduct_pred;

        val flat_corec_thms = append oo append;

        val ((rel_coinduct_thmss, common_rel_coinduct_thms),
             (rel_coinduct_attrs, common_rel_coinduct_attrs)) =
          if live = 0 then
            ((replicate nn [], []), ([], []))
          else
            let
              val ((rel_coinduct_thms, common_rel_coinduct_thm),
                   (rel_coinduct_attrs, common_rel_coinduct_attrs)) =
                derive_rel_coinduct_thm_for_types lthy fpTs ns As Bs mss ctr_sugars abs_inverses
                  abs_injects ctor_injects dtor_ctors pre_rel_defs ctr_defss rel_xtor_co_induct_thm
                  live_nesting_rel_eqs;
            in
              ((map single rel_coinduct_thms, single common_rel_coinduct_thm),
               (rel_coinduct_attrs, common_rel_coinduct_attrs))
            end;

        val (set_induct_thms, set_induct_attrss) =
          derive_set_induct_thms_for_types lthy nn fpTs (map #ctrs ctr_sugars)
            (map (map (mk_set As)) (map sets_of_bnf fp_bnfs)) dtor_set_induct_thms
            (map #exhaust ctr_sugars) (flat pre_set_defss) (flat ctr_defss)
            dtor_ctors abs_inverses
          |> split_list;

        val simp_thmss =
          map6 mk_simp_thms ctr_sugars
            (map3 flat_corec_thms corec_disc_thmss corec_disc_iff_thmss corec_sel_thmss)
            mapss rel_injectss rel_distinctss setss;

        val common_notes =
          (set_inductN, set_induct_thms, nth set_induct_attrss) ::
          (if nn > 1 then
            [(coinductN, [coinduct_thm], K common_coinduct_attrs),
             (coinduct_strongN, [coinduct_strong_thm], K common_coinduct_attrs),
             (rel_coinductN, common_rel_coinduct_thms, K common_rel_coinduct_attrs)]
           else [])
          |> massage_simple_notes fp_common_name;

        val notes =
          [(coinductN, map single coinduct_thms,
            fn T_name => coinduct_attrs @ [coinduct_type_attr T_name]),
           (coinduct_strongN, map single coinduct_strong_thms, K coinduct_attrs),
           (corecN, corec_thmss, K []),
           (corec_codeN, map single corec_code_thms, K (code_attrs @ nitpicksimp_attrs)),
           (corec_discN, corec_disc_thmss, K []),
           (corec_disc_iffN, corec_disc_iff_thmss, K corec_disc_iff_attrs),
           (corec_selN, corec_sel_thmss, K corec_sel_attrs),
           (rel_coinductN, rel_coinduct_thmss, K (rel_coinduct_attrs @ [coinduct_pred_attr ""])),
           (simpsN, simp_thmss, K [])]
          |> massage_multi_notes fp_b_names fpTs;
      in
        lthy
        |> fold (curry (Spec_Rules.add Spec_Rules.Equational) corecs)
          [flat corec_sel_thmss, flat corec_thmss]
        |> Local_Theory.notes (common_notes @ notes)
        |-> interpret_bnfs_register_fp_sugars plugins fpTs fpBTs Xs Greatest_FP pre_bnfs absT_infos
          fp_nesting_bnfs live_nesting_bnfs fp_res ctrXs_Tsss ctr_defss ctr_sugars corecs corec_defs
          mapss [coinduct_thm, coinduct_strong_thm]
          (transpose [coinduct_thms, coinduct_strong_thms]) corec_thmss corec_disc_thmss
          corec_sel_thmsss rel_injectss rel_distinctss
      end;

    val lthy'' = lthy'
      |> live > 0 ? fold2 (fn Type (s, _) => fn bnf => register_bnf_raw s bnf) fpTs fp_bnfs
      |> fold_map define_ctrs_dtrs_for_type (fp_bnfs ~~ fp_bs ~~ fpTs ~~ ctors ~~ dtors ~~
        xtor_co_recs ~~ ctor_dtors ~~ dtor_ctors ~~ ctor_injects ~~ pre_map_defs ~~ pre_set_defss ~~
        pre_rel_defs ~~ xtor_map_thms ~~ xtor_set_thmss ~~ xtor_rel_thms ~~ ns ~~ kss ~~ mss ~~
        abss ~~ abs_injects ~~ abs_inverses ~~ type_definitions ~~ ctr_bindingss ~~ ctr_mixfixess ~~
        ctr_Tsss ~~ disc_bindingss ~~ sel_bindingsss ~~ raw_sel_default_eqss)
      |> wrap_ctrs_derive_map_set_rel_thms_define_co_rec_for_types
      |> case_fp fp derive_note_induct_recs_thms_for_types
           derive_note_coinduct_corecs_thms_for_types;

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      co_prefix fp ^ "datatype"));
  in
    timer; lthy''
  end;

fun co_datatypes x = define_co_datatypes (K I) (K I) (K I) x;

fun co_datatype_cmd x =
  define_co_datatypes Typedecl.read_constraint Syntax.parse_typ Syntax.parse_term x;

val parse_ctr_arg =
  @{keyword "("} |-- parse_binding_colon -- Parse.typ --| @{keyword ")"}
  || Parse.typ >> pair Binding.empty;

val parse_ctr_specs =
  Parse.enum1 "|" (parse_ctr_spec Parse.binding parse_ctr_arg -- Parse.opt_mixfix);

val parse_spec =
  parse_type_args_named_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword "="} |-- parse_ctr_specs) -- parse_map_rel_bindings -- parse_sel_default_eqs;

val parse_co_datatype = parse_ctr_options -- Parse.and_list1 parse_spec;

fun parse_co_datatype_cmd fp construct_fp = parse_co_datatype >> co_datatype_cmd fp construct_fp;

val _ = Theory.setup FP_Sugar_Interpretation.init;

end;
