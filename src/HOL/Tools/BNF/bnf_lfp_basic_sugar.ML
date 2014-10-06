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
  {absT = fpT,
   repT = fpT,
   abs = Const (@{const_name id_bnf}, fpT --> fpT),
   rep = Const (@{const_name id_bnf}, fpT --> fpT),
   abs_inject = @{thm type_definition.Abs_inject[OF type_definition_id_bnf_UNIV UNIV_I UNIV_I]},
   abs_inverse = @{thm type_definition.Abs_inverse[OF type_definition_id_bnf_UNIV UNIV_I]},
   type_definition = @{thm type_definition_id_bnf_UNIV}};

fun the_frozen_ctr_sugar_of ctxt fpT_name =
  the (ctr_sugar_of ctxt fpT_name)
  |> morph_ctr_sugar (Morphism.typ_morphism "BNF" Logic.unvarifyT_global
    $> Morphism.term_morphism "BNF" (Term.map_types Logic.unvarifyT_global));

fun trivial_fp_result_of fp_bnf fpT C xtor_map xtor_sets xtor_rel ctor_rec_o_map xtor_rel_induct =
  {Ts = [fpT],
   bnfs = [fp_bnf],
   ctors = [Const (@{const_name xtor}, fpT --> fpT)],
   dtors = [Const (@{const_name xtor}, fpT --> fpT)],
   xtor_co_recs = [Const (@{const_name ctor_rec}, (fpT --> C) --> (fpT --> C))],
   xtor_co_induct = @{thm xtor_induct},
   dtor_ctors = @{thms xtor_xtor},
   ctor_dtors = @{thms xtor_xtor},
   ctor_injects = @{thms xtor_inject},
   dtor_injects = @{thms xtor_inject},
   xtor_map_thms = [xtor_map],
   xtor_set_thmss = [xtor_sets],
   xtor_rel_thms = [xtor_rel],
   xtor_co_rec_thms = [map_id0_of_bnf fp_bnf RS @{thm ctor_rec}],
   xtor_co_rec_o_map_thms = [ctor_rec_o_map],
   rel_xtor_co_induct_thm = xtor_rel_induct,
   dtor_set_induct_thms = [],
   xtor_co_rec_transfer_thms = []};

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
     absT_info = trivial_absT_info_of fpT,
     fp_nesting_bnfs = [],
     live_nesting_bnfs = [],
     fp_ctr_sugar =
       {ctrXs_Tss = ctr_Tss,
        ctr_defs = @{thms Inl_def_alt Inr_def_alt},
        ctr_sugar = the_frozen_ctr_sugar_of ctxt fpT_name},
     fp_bnf_sugar =
       {map_thms = @{thms map_sum.simps},
        map_disc_iffs = [],
        map_sels = [],
        rel_injects = @{thms rel_sum_simps(1,4)},
        rel_distincts = @{thms rel_sum_simps(2,3)[THEN eq_False[THEN iffD1]]},
        rel_sels = [],
        rel_intros = [],
        rel_cases = [],
        set_thms = [],
        set_sels = [],
        set_intros = [],
        set_cases = []},
     fp_co_induct_sugar =
       {co_rec = Const (@{const_name case_sum}, map (fn Ts => (Ts ---> C)) ctr_Tss ---> fpT --> C),
        common_co_inducts = @{thms sum.induct},
        co_inducts = @{thms sum.induct},
        co_rec_def = @{thm ctor_rec_def_alt[of "case_sum f1 f2" for f1 f2]},
        co_rec_thms = @{thms sum.case},
        co_rec_discs = [],
        co_rec_selss = []}}
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
     absT_info = trivial_absT_info_of fpT,
     fp_nesting_bnfs = [],
     live_nesting_bnfs = [],
     fp_ctr_sugar =
       {ctrXs_Tss = [ctr_Ts],
        ctr_defs = @{thms Pair_def_alt},
        ctr_sugar = the_frozen_ctr_sugar_of ctxt fpT_name},
     fp_bnf_sugar =
       {map_thms = @{thms map_prod_simp},
        map_disc_iffs = [],
        map_sels = [],
        rel_injects = @{thms rel_prod_apply},
        rel_distincts = [],
        rel_sels = [],
        rel_intros = [],
        rel_cases = [],
        set_thms = [],
        set_sels = [],
        set_intros = [],
        set_cases = []},
     fp_co_induct_sugar =
       {co_rec = Const (@{const_name case_prod}, (ctr_Ts ---> C) --> fpT --> C),
        common_co_inducts = @{thms prod.induct},
        co_inducts = @{thms prod.induct},
        co_rec_def = @{thm ctor_rec_def_alt[of "case_prod f" for f]},
        co_rec_thms = @{thms prod.case},
        co_rec_discs = [],
        co_rec_selss = []}}
  end;

val _ = Theory.setup (map_local_theory (fn lthy =>
  fold (BNF_FP_Def_Sugar.register_fp_sugars (K true) o single o (fn f => f lthy))
    [fp_sugar_of_sum, fp_sugar_of_prod] lthy));

end;
