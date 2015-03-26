(*  Title:      HOL/Tools/BNF/bnf_lfp_basic_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Registration of basic types as BNF least fixpoints (datatypes).
*)

structure BNF_LFP_Basic_Sugar : sig end =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Def
open BNF_Comp
open BNF_FP_Rec_Sugar_Util
open BNF_FP_Util
open BNF_FP_Def_Sugar

fun trivial_absT_info_of fpT =
  {absT = fpT, repT = fpT, abs = Const (@{const_name id_bnf}, fpT --> fpT),
   rep = Const (@{const_name id_bnf}, fpT --> fpT),
   abs_inject = @{thm type_definition.Abs_inject[OF type_definition_id_bnf_UNIV UNIV_I UNIV_I]},
   abs_inverse = @{thm type_definition.Abs_inverse[OF type_definition_id_bnf_UNIV UNIV_I]},
   type_definition = @{thm type_definition_id_bnf_UNIV}};

fun the_frozen_ctr_sugar_of ctxt fpT_name =
  the (ctr_sugar_of ctxt fpT_name)
  |> morph_ctr_sugar (Morphism.typ_morphism "BNF" Logic.unvarifyT_global
    $> Morphism.term_morphism "BNF" (Term.map_types Logic.unvarifyT_global));

fun trivial_fp_result_of fp_bnf fpT C xtor_map xtor_sets xtor_rel ctor_rec_o_map xtor_rel_induct =
  let
    val xtors = [Const (@{const_name xtor}, fpT --> fpT)];
    val co_recs = [Const (@{const_name ctor_rec}, (fpT --> C) --> (fpT --> C))];
    val co_rec_thms = [map_id0_of_bnf fp_bnf RS @{thm ctor_rec}];
  in
    {Ts = [fpT], bnfs = [fp_bnf], ctors = xtors, dtors = xtors, xtor_un_folds = co_recs,
     xtor_co_recs = co_recs, xtor_co_induct = @{thm xtor_induct}, dtor_ctors = @{thms xtor_xtor},
     ctor_dtors = @{thms xtor_xtor}, ctor_injects = @{thms xtor_inject},
     dtor_injects = @{thms xtor_inject}, xtor_maps = [xtor_map], xtor_setss = [xtor_sets],
     xtor_rels = [xtor_rel], xtor_un_fold_thms = co_rec_thms, xtor_co_rec_thms = co_rec_thms,
     xtor_co_rec_o_maps = [ctor_rec_o_map], xtor_rel_co_induct = xtor_rel_induct,
     dtor_set_inducts = [], xtor_co_rec_transfers = []}
  end;

fun fp_sugar_of_sum ctxt =
  let
    val fpT as Type (fpT_name, As) = @{typ "'a + 'b"};
    val fpBT = @{typ "'c + 'd"};
    val C = @{typ 'e};
    val X = @{typ 'sum};
    val ctr_Tss = map single As;

    val fp_bnf = the (bnf_of ctxt fpT_name);
    val xtor_map = @{thm xtor_map[of "map_sum f1 f2" for f1 f2]};
    val xtor_sets = @{thms xtor_set[of setl] xtor_set[of setr]};
    val xtor_rel = @{thm xtor_rel[of "rel_sum R1 R2" for R1 R2]};
    val ctor_rec_o_map = @{thm ctor_rec_o_map[of _ "map_sum g1 g2" for g1 g2]};
    val xtor_rel_induct = @{thm xtor_rel_induct[of "rel_sum R1 R2" for R1 R2]};
  in
    {T = fpT,
     BT = fpBT,
     X = X,
     fp = Least_FP,
     fp_res_index = 0,
     fp_res =
       trivial_fp_result_of fp_bnf fpT C xtor_map xtor_sets xtor_rel ctor_rec_o_map xtor_rel_induct,
     pre_bnf = ID_bnf (*wrong*),
     fp_bnf = fp_bnf,
     absT_info = trivial_absT_info_of fpT,
     fp_nesting_bnfs = [],
     live_nesting_bnfs = [],
     fp_ctr_sugar =
       {ctrXs_Tss = ctr_Tss,
        ctr_defs = @{thms Inl_def_alt Inr_def_alt},
        ctr_sugar = the_frozen_ctr_sugar_of ctxt fpT_name,
        ctr_transfers = @{thms Inl_transfer Inr_transfer},
        case_transfers = @{thms case_sum_transfer},
        disc_transfers = @{thms isl_transfer},
        sel_transfers = []},
     fp_bnf_sugar =
       {map_thms = @{thms map_sum.simps},
        map_disc_iffs = @{thms isl_map_sum},
        map_selss = map single @{thms map_sum_sel},
        rel_injects = @{thms rel_sum_simps(1,4)},
        rel_distincts = @{thms rel_sum_simps(2,3)[THEN eq_False[THEN iffD1]]},
        rel_sels = @{thms rel_sum_sel},
        rel_intros = @{thms rel_sum.intros},
        rel_cases = @{thms rel_sum.cases},
        set_thms = @{thms sum_set_simps},
        set_selssss = [[[@{thms set_sum_sel(1)}], [[]]], [[[]], [@{thms set_sum_sel(2)}]]],
        set_introssss = [[[@{thms setl.intros[OF refl]}], [[]]],
          [[[]], [@{thms setr.intros[OF refl]}]]],
        set_cases = @{thms setl.cases[unfolded hypsubst_in_prems]
          setr.cases[unfolded hypsubst_in_prems]}},
     fp_co_induct_sugar =
       {co_rec = Const (@{const_name case_sum}, map (fn Ts => (Ts ---> C)) ctr_Tss ---> fpT --> C),
        common_co_inducts = @{thms sum.induct},
        co_inducts = @{thms sum.induct},
        co_rec_def = @{thm ctor_rec_def_alt[of "case_sum f1 f2" for f1 f2]},
        co_rec_thms = @{thms sum.case},
        co_rec_discs = [],
        co_rec_disc_iffs = [],
        co_rec_selss = [],
        co_rec_codes = [],
        co_rec_transfers = @{thms case_sum_transfer},
        co_rec_o_maps = @{thms case_sum_o_map_sum},
        common_rel_co_inducts = @{thms rel_sum.inducts},
        rel_co_inducts = @{thms rel_sum.induct},
        common_set_inducts = [],
        set_inducts = []}}
  end;

fun fp_sugar_of_prod ctxt =
  let
    val fpT as Type (fpT_name, As) = @{typ "'a * 'b"};
    val fpBT = @{typ "'c * 'd"};
    val C = @{typ 'e};
    val X = @{typ 'prod};
    val ctr_Ts = As;

    val fp_bnf = the (bnf_of ctxt fpT_name);
    val xtor_map = @{thm xtor_map[of "map_prod f1 f2" for f1 f2]};
    val xtor_sets = @{thms xtor_set[of fsts] xtor_set[of snds]};
    val xtor_rel = @{thm xtor_rel[of "rel_prod R1 R2" for R1 R2]};
    val ctor_rec_o_map = @{thm ctor_rec_o_map[of _ "map_prod g1 g2" for g1 g2]};
    val xtor_rel_induct = @{thm xtor_rel_induct[of "rel_prod R1 R2" for R1 R2]};
  in
    {T = fpT,
     BT = fpBT,
     X = X,
     fp = Least_FP,
     fp_res_index = 0,
     fp_res =
       trivial_fp_result_of fp_bnf fpT C xtor_map xtor_sets xtor_rel ctor_rec_o_map xtor_rel_induct,
     pre_bnf = ID_bnf (*wrong*),
     fp_bnf = fp_bnf,
     absT_info = trivial_absT_info_of fpT,
     fp_nesting_bnfs = [],
     live_nesting_bnfs = [],
     fp_ctr_sugar =
       {ctrXs_Tss = [ctr_Ts],
        ctr_defs = @{thms Pair_def_alt},
        ctr_sugar = the_frozen_ctr_sugar_of ctxt fpT_name,
        ctr_transfers = @{thms Pair_transfer},
        case_transfers = @{thms case_prod_transfer},
        disc_transfers = [],
        sel_transfers = @{thms fst_transfer snd_transfer}},
     fp_bnf_sugar =
       {map_thms = @{thms map_prod_simp},
        map_disc_iffs = [],
        map_selss = [@{thms fst_map_prod snd_map_prod}],
        rel_injects = @{thms rel_prod_apply},
        rel_distincts = [],
        rel_sels = @{thms rel_prod_sel},
        rel_intros = @{thms rel_prod.intros},
        rel_cases = @{thms rel_prod.cases},
        set_thms = @{thms prod_set_simps},
        set_selssss = [[[@{thms fsts.intros}, []]], [[[], @{thms snds.intros}]]],
        set_introssss = [[[@{thms fsts.intros[of "(a, b)" for a b, unfolded fst_conv]}, []]],
          [[[], @{thms snds.intros[of "(a, b)" for a b, unfolded snd_conv]}]]],
        set_cases = @{thms fsts.cases[unfolded eq_fst_iff ex_neg_all_pos]
          snds.cases[unfolded eq_snd_iff ex_neg_all_pos]}},
     fp_co_induct_sugar =
       {co_rec = Const (@{const_name case_prod}, (ctr_Ts ---> C) --> fpT --> C),
        common_co_inducts = @{thms prod.induct},
        co_inducts = @{thms prod.induct},
        co_rec_def = @{thm ctor_rec_def_alt[of "case_prod f" for f]},
        co_rec_thms = @{thms prod.case},
        co_rec_discs = [],
        co_rec_disc_iffs = [],
        co_rec_selss = [],
        co_rec_codes = [],
        co_rec_transfers = @{thms case_prod_transfer},
        co_rec_o_maps = @{thms case_prod_o_map_prod},
        common_rel_co_inducts = @{thms rel_prod.inducts},
        rel_co_inducts = @{thms rel_prod.induct},
        common_set_inducts = [],
        set_inducts = []}}
  end;

val _ = Theory.setup (Named_Target.theory_map (fn lthy =>
  fold (BNF_FP_Def_Sugar.register_fp_sugars (K true) o single o (fn f => f lthy))
    [fp_sugar_of_sum, fp_sugar_of_prod] lthy));

end;
