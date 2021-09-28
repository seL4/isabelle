(*  Title:      HOL/Tools/BNF/bnf_gfp_grec_sugar.ML
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Dmitriy Traytel, ETH Zürich
    Copyright   2015, 2016

Generalized corecursor sugar ("corec" and friends).
*)

signature BNF_GFP_GREC_SUGAR =
sig
  datatype corec_option =
    Plugins_Option of Proof.context -> Plugin_Name.filter |
    Friend_Option |
    Transfer_Option

  val parse_corec_equation: Proof.context -> term list -> term -> term list * term
  val explore_corec_equation: Proof.context -> bool -> bool -> string -> term ->
    BNF_GFP_Grec_Sugar_Util.s_parse_info -> typ -> term list * term -> term list * term
  val build_corecUU_arg_and_goals: bool -> term -> term list * term -> local_theory ->
    (((thm list * thm list * thm list) * term list) * term) * local_theory
  val derive_eq_corecUU: Proof.context -> BNF_GFP_Grec.corec_info -> term -> term -> thm -> thm
  val derive_unique: Proof.context -> morphism -> term -> BNF_GFP_Grec.corec_info -> string ->
    thm -> thm

  val corec_cmd: bool -> corec_option list -> (binding * string option * mixfix) list * string ->
    local_theory -> local_theory
  val corecursive_cmd: bool -> corec_option list ->
    (binding * string option * mixfix) list * string -> local_theory -> Proof.state
  val friend_of_corec_cmd: (string * string option) * string -> local_theory -> Proof.state
  val coinduction_upto_cmd: string * string -> local_theory -> local_theory
end;

structure BNF_GFP_Grec_Sugar : BNF_GFP_GREC_SUGAR =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Tactics
open BNF_Def
open BNF_Comp
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar
open BNF_GFP_Util
open BNF_GFP_Rec_Sugar
open BNF_FP_Rec_Sugar_Transfer
open BNF_GFP_Grec
open BNF_GFP_Grec_Sugar_Util
open BNF_GFP_Grec_Sugar_Tactics

val cong_N = "cong_";
val baseN = "base";
val reflN = "refl";
val symN = "sym";
val transN = "trans";
val cong_introsN = prefix cong_N "intros";
val codeN = "code";
val coinductN = "coinduct";
val coinduct_uptoN = "coinduct_upto";
val corecN = "corec";
val ctrN = "ctr";
val discN = "disc";
val disc_iffN = "disc_iff";
val eq_algrhoN = "eq_algrho";
val eq_corecUUN = "eq_corecUU";
val friendN = "friend";
val inner_elimN = "inner_elim";
val inner_inductN = "inner_induct";
val inner_simpN = "inner_simp";
val rhoN = "rho";
val selN = "sel";
val uniqueN = "unique";

val inner_fp_suffix = "_inner_fp";

val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};

val unfold_id_thms1 =
  map (fn thm => thm RS eq_reflection) @{thms id_bnf_o o_id_bnf id_apply o_apply} @
  @{thms fst_def[abs_def, symmetric] snd_def[abs_def, symmetric]};

fun unfold_id_bnf_etc lthy =
  let val thy = Proof_Context.theory_of lthy in
    Raw_Simplifier.rewrite_term thy unfold_id_thms1 []
    #> Raw_Simplifier.rewrite_term thy @{thms BNF_Composition.id_bnf_def} []
  end;

datatype corec_option =
  Plugins_Option of Proof.context -> Plugin_Name.filter |
  Friend_Option |
  Transfer_Option;

val corec_option_parser = Parse.group (K "option")
  (Plugin_Name.parse_filter >> Plugins_Option
   || Parse.reserved "friend" >> K Friend_Option
   || Parse.reserved "transfer" >> K Transfer_Option);

type codatatype_extra =
  {case_dtor: thm,
   case_trivial: thm,
   abs_rep_transfers: thm list};

fun morph_codatatype_extra phi ({case_dtor, case_trivial, abs_rep_transfers} : codatatype_extra) =
  {case_dtor = Morphism.thm phi case_dtor, case_trivial = Morphism.thm phi case_trivial,
   abs_rep_transfers = map (Morphism.thm phi) abs_rep_transfers};

val transfer_codatatype_extra = morph_codatatype_extra o Morphism.transfer_morphism;

type coinduct_extra =
  {coinduct: thm,
   coinduct_attrs: Token.src list,
   cong_intro_pairs: (string * thm) list};

fun morph_coinduct_extra phi ({coinduct, coinduct_attrs, cong_intro_pairs} : coinduct_extra) =
  {coinduct = Morphism.thm phi coinduct, coinduct_attrs = coinduct_attrs,
   cong_intro_pairs = map (apsnd (Morphism.thm phi)) cong_intro_pairs};

val transfer_coinduct_extra = morph_coinduct_extra o Morphism.transfer_morphism;

type friend_extra =
  {eq_algrhos: thm list,
   algrho_eqs: thm list};

val empty_friend_extra = {eq_algrhos = [], algrho_eqs = []};

fun merge_friend_extras ({eq_algrhos = eq_algrhos1, algrho_eqs = algrho_eqs1},
    {eq_algrhos = eq_algrhos2, algrho_eqs = algrho_eqs2}) =
  {eq_algrhos = union Thm.eq_thm_prop eq_algrhos1 eq_algrhos2,
   algrho_eqs = union Thm.eq_thm_prop algrho_eqs1 algrho_eqs2};

type corec_sugar_data =
  codatatype_extra Symtab.table * coinduct_extra Symtab.table * friend_extra Symtab.table;

structure Data = Generic_Data
(
  type T = corec_sugar_data;
  val empty = (Symtab.empty, Symtab.empty, Symtab.empty);
  val extend = I;
  fun merge data : T =
    (Symtab.merge (K true) (apply2 #1 data), Symtab.merge (K true) (apply2 #2 data),
     Symtab.join (K merge_friend_extras) (apply2 #3 data));
);

fun register_codatatype_extra fpT_name extra =
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    Data.map (@{apply 3(1)} (Symtab.update (fpT_name, morph_codatatype_extra phi extra))));

fun codatatype_extra_of ctxt =
  Symtab.lookup (#1 (Data.get (Context.Proof ctxt)))
  #> Option.map (transfer_codatatype_extra (Proof_Context.theory_of ctxt));

fun all_codatatype_extras_of ctxt =
  Symtab.dest (#1 (Data.get (Context.Proof ctxt)));

fun register_coinduct_extra fpT_name extra =
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    Data.map (@{apply 3(2)} (Symtab.update (fpT_name, morph_coinduct_extra phi extra))));

fun coinduct_extra_of ctxt =
  Symtab.lookup (#2 (Data.get (Context.Proof ctxt)))
  #> Option.map (transfer_coinduct_extra (Proof_Context.theory_of ctxt));

fun register_friend_extra fun_name eq_algrho algrho_eq =
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    Data.map (@{apply 3(3)} (Symtab.map_default (fun_name, empty_friend_extra)
      (fn {eq_algrhos, algrho_eqs} =>
        {eq_algrhos = Morphism.thm phi eq_algrho :: eq_algrhos,
         algrho_eqs = Morphism.thm phi algrho_eq :: algrho_eqs}))));

fun all_friend_extras_of ctxt =
  Symtab.dest (#3 (Data.get (Context.Proof ctxt)));

fun coinduct_extras_of_generic context =
  corec_infos_of_generic context
  #> map (#corecUU #> dest_Const #> fst #> Symtab.lookup (#2 (Data.get context)) #> the
    #> transfer_coinduct_extra (Context.theory_of context));

fun get_coinduct_uptos fpT_name context =
  coinduct_extras_of_generic context fpT_name |> map #coinduct;
fun get_cong_all_intros fpT_name context =
  coinduct_extras_of_generic context fpT_name |> maps (#cong_intro_pairs #> map snd);
fun get_cong_intros fpT_name name context =
  coinduct_extras_of_generic context fpT_name
  |> map_filter (#cong_intro_pairs #> (fn ps => AList.lookup (op =) ps name));

fun ctr_names_of_fp_name lthy fpT_name =
  fpT_name |> fp_sugar_of lthy |> the |> #fp_ctr_sugar |> #ctr_sugar |> #ctrs
  |> map (Long_Name.base_name o name_of_ctr);

fun register_coinduct_dynamic_base fpT_name lthy =
  let val fp_b = Binding.name (Long_Name.base_name fpT_name) in
    lthy
    |> fold Local_Theory.add_thms_dynamic
      ((mk_fp_binding fp_b coinduct_uptoN, get_coinduct_uptos fpT_name) ::
        map (fn N =>
          let val N = cong_N ^ N in
            (mk_fp_binding fp_b N, get_cong_intros fpT_name N)
          end)
        ([baseN, reflN, symN, transN] @ ctr_names_of_fp_name lthy fpT_name))
    |> Local_Theory.add_thms_dynamic
      (mk_fp_binding fp_b cong_introsN, get_cong_all_intros fpT_name)
  end;

fun register_coinduct_dynamic_friend fpT_name friend_name =
  let
    val fp_b = Binding.name (Long_Name.base_name fpT_name);
    val friend_base_name = cong_N ^ Long_Name.base_name friend_name;
  in
    Local_Theory.add_thms_dynamic
      (mk_fp_binding fp_b friend_base_name, get_cong_intros fpT_name friend_base_name)
  end;

fun derive_case_dtor ctxt fpT_name =
  let
    val thy = Proof_Context.theory_of ctxt;

    val SOME ({fp_res_index, fp_res = {dtors = dtors0, dtor_ctors, ...},
        absT_info = {rep = rep0, abs_inverse, ...},
        fp_ctr_sugar = {ctr_defs, ctr_sugar = {casex, exhaust, case_thms, ...}, ...}, ...}) =
      fp_sugar_of ctxt fpT_name;

    val (f_Ts, Type (_, [fpT as Type (_, As), _])) = strip_fun_type (fastype_of casex);
    val x_Tss = map binder_types f_Ts;

    val (((u, fs), xss), _) = ctxt
      |> yield_singleton (mk_Frees "y") fpT
      ||>> mk_Frees "f" f_Ts
      ||>> mk_Freess "x" x_Tss;

    val dtor0 = nth dtors0 fp_res_index;
    val dtor = mk_dtor As dtor0;

    val u' = dtor $ u;

    val absT = fastype_of u';

    val rep = mk_rep absT rep0;

    val goal = mk_Trueprop_eq (list_comb (casex, fs) $ u,
        mk_case_absumprod absT rep fs xss xss $ u')
      |> Raw_Simplifier.rewrite_term thy @{thms comp_def[THEN eq_reflection]} [];
    val vars = map (fst o dest_Free) (u :: fs);

    val dtor_ctor = nth dtor_ctors fp_res_index;
  in
    Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_case_dtor_tac ctxt u abs_inverse dtor_ctor ctr_defs exhaust case_thms)
    |> Thm.close_derivation \<^here>
  end;

fun derive_case_trivial ctxt fpT_name =
  let
    val SOME {casex, exhaust, case_thms, ...} = ctr_sugar_of ctxt fpT_name;

    val Type (_, As0) = domain_type (body_fun_type (fastype_of casex));

    val (As, _) = ctxt
      |> mk_TFrees' (map Type.sort_of_atyp As0);
    val fpT = Type (fpT_name, As);

    val (var_name, ()) = singleton (Variable.variant_frees ctxt []) ("x", ());
    val var = Free (var_name, fpT);
    val goal = mk_Trueprop_eq (expand_to_ctr_term ctxt fpT var, var);

    val exhaust' = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt var)] exhaust;
  in
    Goal.prove_sorry ctxt [var_name] [] goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (rtac ctxt exhaust') THEN ALLGOALS (hyp_subst_tac ctxt) THEN
      unfold_thms_tac ctxt case_thms THEN ALLGOALS (rtac ctxt refl))
    |> Thm.close_derivation \<^here>
  end;

fun mk_abs_rep_transfers ctxt fpT_name =
  [mk_abs_transfer ctxt fpT_name, mk_rep_transfer ctxt fpT_name]
  handle Fail _ => [];

fun ensure_codatatype_extra fpT_name ctxt =
  (case codatatype_extra_of ctxt fpT_name of
    NONE =>
    let val abs_rep_transfers = mk_abs_rep_transfers ctxt fpT_name in
      ctxt
      |> register_codatatype_extra fpT_name
        {case_dtor = derive_case_dtor ctxt fpT_name,
         case_trivial = derive_case_trivial ctxt fpT_name,
         abs_rep_transfers = abs_rep_transfers}
      |> set_transfer_rule_attrs abs_rep_transfers
    end
  | SOME {abs_rep_transfers, ...} => ctxt |> set_transfer_rule_attrs abs_rep_transfers);

fun setup_base fpT_name =
  register_coinduct_dynamic_base fpT_name
  #> ensure_codatatype_extra fpT_name;

fun is_set ctxt (const_name, T) =
  (case T of
    Type (\<^type_name>\<open>fun\<close>, [Type (fpT_name, _), Type (\<^type_name>\<open>set\<close>, [_])]) =>
    (case bnf_of ctxt fpT_name of
      SOME bnf => exists (fn Const (s, _) => s = const_name | _ => false) (sets_of_bnf bnf)
    | NONE => false)
  | _ => false);

fun case_eq_if_thms_of_term ctxt t =
  let val ctr_sugars = map_filter (ctr_sugar_of_case ctxt o fst) (Term.add_consts t []) in
    maps #case_eq_ifs ctr_sugars
  end;

fun all_algrho_eqs_of ctxt =
  maps (#algrho_eqs o snd) (all_friend_extras_of ctxt);

fun derive_code ctxt inner_fp_simps goal
    {sig_fp_sugars, ssig_fp_sugar, eval, eval_simps, all_algLam_algs, corecUU_thm, ...} fun_t
    fun_def =
  let
    val fun_T = fastype_of fun_t;
    val (arg_Ts, Type (fpT_name, _)) = strip_type fun_T;
    val num_args = length arg_Ts;

    val SOME {pre_bnf, fp_bnf, absT_info, fp_nesting_bnfs, live_nesting_bnfs, fp_ctr_sugar, ...} =
      fp_sugar_of ctxt fpT_name;
    val SOME {case_trivial, ...} = codatatype_extra_of ctxt fpT_name;

    val ctr_sugar = #ctr_sugar fp_ctr_sugar;
    val pre_map_def = map_def_of_bnf pre_bnf;
    val abs_inverse = #abs_inverse absT_info;
    val ctr_defs = #ctr_defs fp_ctr_sugar;
    val case_eq_ifs = #case_eq_ifs ctr_sugar @ case_eq_if_thms_of_term ctxt goal;
    val all_sig_map_thms = maps (#map_thms o #fp_bnf_sugar) sig_fp_sugars;

    val fp_map_ident = map_ident_of_bnf fp_bnf;
    val fpsig_nesting_bnfs = fp_nesting_bnfs @ maps #live_nesting_bnfs sig_fp_sugars;
    val fpsig_nesting_T_names = map (fst o dest_Type o T_of_bnf) fpsig_nesting_bnfs;
    val fpsig_nesting_fp_sugars = map_filter (fp_sugar_of ctxt) fpsig_nesting_T_names;
    val fpsig_nesting_fp_bnf_sugars = map #fp_bnf_sugar fpsig_nesting_fp_sugars;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;
    val ssig_map = map_of_bnf ssig_bnf;
    val fpsig_nesting_maps = map map_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_ident0s = map map_ident0_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_comps = map map_comp_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_thms = maps #map_thms fpsig_nesting_fp_bnf_sugars;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val all_algLam_alg_pointfuls = map (mk_pointful ctxt) all_algLam_algs;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_code_tac ctxt num_args fpsig_nesting_maps ssig_map eval pre_map_def abs_inverse
        fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
        live_nesting_map_ident0s fp_map_ident case_trivial ctr_defs case_eq_ifs corecUU_thm
        all_sig_map_thms ssig_map_thms all_algLam_alg_pointfuls (all_algrho_eqs_of ctxt) eval_simps
        inner_fp_simps fun_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_unique ctxt phi code_goal
    {sig_fp_sugars, ssig_fp_sugar, eval, eval_simps, all_algLam_algs, corecUU_unique, ...} fpT_name
    eq_corecUU =
  let
    val SOME {pre_bnf, fp_bnf, absT_info, fp_nesting_bnfs, live_nesting_bnfs, fp_ctr_sugar, ...} =
      fp_sugar_of ctxt fpT_name;
    val SOME {case_trivial, ...} = codatatype_extra_of ctxt fpT_name;

    val ctr_sugar = #ctr_sugar fp_ctr_sugar;
    val pre_map_def = map_def_of_bnf pre_bnf;
    val abs_inverse = #abs_inverse absT_info;
    val ctr_defs = #ctr_defs fp_ctr_sugar;
    val case_eq_ifs = #case_eq_ifs ctr_sugar @ case_eq_if_thms_of_term ctxt code_goal;
    val all_sig_map_thms = maps (#map_thms o #fp_bnf_sugar) sig_fp_sugars;

    val fp_map_ident = map_ident_of_bnf fp_bnf;
    val fpsig_nesting_bnfs = fp_nesting_bnfs @ maps #live_nesting_bnfs sig_fp_sugars;
    val fpsig_nesting_T_names = map (fst o dest_Type o T_of_bnf) fpsig_nesting_bnfs;
    val fpsig_nesting_fp_sugars = map_filter (fp_sugar_of ctxt) fpsig_nesting_T_names;
    val fpsig_nesting_fp_bnf_sugars = map #fp_bnf_sugar fpsig_nesting_fp_sugars;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;
    val ssig_map = map_of_bnf ssig_bnf;
    val fpsig_nesting_maps = map map_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_ident0s = map map_ident0_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_comps = map map_comp_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_thms = maps #map_thms fpsig_nesting_fp_bnf_sugars;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val all_algLam_alg_pointfuls = map (mk_pointful ctxt) all_algLam_algs;

    val \<^Const_>\<open>Trueprop for \<^Const_>\<open>HOL.eq _ for lhs rhs\<close>\<close> = code_goal;
    val (fun_t, args) = strip_comb lhs;
    val closed_rhs = fold_rev lambda args rhs;

    val fun_T = fastype_of fun_t;
    val num_args = num_binder_types fun_T;

    val f = Free (singleton (Variable.variant_frees ctxt []) ("f", fun_T));

    val is_self_call = curry (op aconv) fun_t;
    val has_self_call = exists_subterm is_self_call;

    fun fify args (t $ u) = fify (u :: args) t $ fify [] u
      | fify _ (Abs (s, T, t)) = Abs (s, T, fify [] t)
      | fify args t = if t = fun_t andalso not (exists has_self_call args) then f else t;

    val goal = Logic.mk_implies (mk_Trueprop_eq (f, fify [] closed_rhs), mk_Trueprop_eq (f, fun_t))
      |> Morphism.term phi;
  in
    Goal.prove_sorry ctxt [fst (dest_Free f)] [] goal (fn {context = ctxt, prems = _} =>
      mk_unique_tac ctxt num_args fpsig_nesting_maps ssig_map eval pre_map_def abs_inverse
        fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
        live_nesting_map_ident0s fp_map_ident case_trivial ctr_defs case_eq_ifs all_sig_map_thms
        ssig_map_thms all_algLam_alg_pointfuls (all_algrho_eqs_of ctxt) eval_simps corecUU_unique
        eq_corecUU)
    |> Thm.close_derivation \<^here>
  end;

fun derive_last_disc ctxt fcT_name =
  let
    val SOME {T = fcT, discs, exhaust, disc_thmss, ...} = ctr_sugar_of ctxt fcT_name;

    val (u, _) = ctxt
      |> yield_singleton (mk_Frees "x") fcT;

    val udiscs = map (rapp u) discs;
    val (not_udiscs, last_udisc) = split_last udiscs
      |>> map HOLogic.mk_not;

    val goal = mk_Trueprop_eq (last_udisc, foldr1 HOLogic.mk_conj not_udiscs);
  in
    Goal.prove_sorry ctxt [fst (dest_Free u)] [] goal (fn {context = ctxt, prems = _} =>
      mk_last_disc_tac ctxt u exhaust (flat disc_thmss))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eq_algrho ctxt {sig_fp_sugars, ssig_fp_sugar, eval, eval_simps, all_algLam_algs,
      corecUU_unique, ...}
    ({algrho = algrho0, dtor_algrho, ...} : friend_info) fun_t k_T code_goal const_transfers rho_def
    eq_corecUU =
  let
    val fun_T = fastype_of fun_t;
    val (arg_Ts, Type (fpT_name, Ts)) = strip_type fun_T;
    val num_args = length arg_Ts;

    val SOME {fp_res_index, fp_res, pre_bnf, fp_bnf, absT_info, fp_nesting_bnfs, live_nesting_bnfs,
        fp_ctr_sugar, ...} =
      fp_sugar_of ctxt fpT_name;
    val SOME {case_dtor, ...} = codatatype_extra_of ctxt fpT_name;

    val fp_nesting_Ts = map T_of_bnf fp_nesting_bnfs;

    fun is_nullary_disc_def (\<^Const>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _
          $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _))) = true
      | is_nullary_disc_def (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _
          $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)) = true
      | is_nullary_disc_def _ = false;

    val dtor_ctor = nth (#dtor_ctors fp_res) fp_res_index;
    val ctor_iff_dtor = #ctor_iff_dtor fp_ctr_sugar;
    val ctr_sugar = #ctr_sugar fp_ctr_sugar;
    val pre_map_def = map_def_of_bnf pre_bnf;
    val abs_inverse = #abs_inverse absT_info;
    val ctr_defs = #ctr_defs fp_ctr_sugar;
    val nullary_disc_defs = filter (is_nullary_disc_def o Thm.prop_of) (#disc_defs ctr_sugar);
    val disc_sel_eq_cases = #disc_eq_cases ctr_sugar @ #sel_defs ctr_sugar;
    val case_eq_ifs = #case_eq_ifs ctr_sugar @ case_eq_if_thms_of_term ctxt code_goal;
    val all_sig_map_thms = maps (#map_thms o #fp_bnf_sugar) sig_fp_sugars;

    fun add_tnameT (Type (s, Ts)) = insert (op =) s #> fold add_tnameT Ts
      | add_tnameT _ = I;

    fun map_disc_sels'_of s =
      (case fp_sugar_of ctxt s of
        SOME {fp_bnf_sugar = {map_disc_iffs, map_selss, ...}, ...} =>
        let
          val map_selss' =
            if length map_selss <= 1 then map_selss
            else map (map (unfold_thms ctxt (no_refl [derive_last_disc ctxt s]))) map_selss;
        in
          map_disc_iffs @ flat map_selss'
        end
      | NONE => []);

    fun mk_const_pointful_natural const_transfer =
      SOME (mk_pointful_natural_from_transfer ctxt const_transfer)
      handle UNNATURAL () => NONE;

    val const_pointful_natural_opts = map mk_const_pointful_natural const_transfers;
    val const_pointful_naturals = map_filter I const_pointful_natural_opts;
    val fp_nesting_k_T_names = fold add_tnameT (k_T :: fp_nesting_Ts) [];
    val fp_nesting_k_map_disc_sels' = maps map_disc_sels'_of fp_nesting_k_T_names;

    val fp_map_ident = map_ident_of_bnf fp_bnf;
    val fpsig_nesting_bnfs = fp_nesting_bnfs @ maps #live_nesting_bnfs sig_fp_sugars;
    val fpsig_nesting_T_names = map (fst o dest_Type o T_of_bnf) fpsig_nesting_bnfs;
    val fpsig_nesting_fp_sugars = map_filter (fp_sugar_of ctxt) fpsig_nesting_T_names;
    val fpsig_nesting_fp_bnf_sugars = map #fp_bnf_sugar fpsig_nesting_fp_sugars;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;
    val ssig_map = map_of_bnf ssig_bnf;
    val fpsig_nesting_maps = map map_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_ident0s = map map_ident0_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_comps = map map_comp_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_thms = maps #map_thms fpsig_nesting_fp_bnf_sugars;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val all_algLam_alg_pointfuls = map (mk_pointful ctxt) all_algLam_algs;

    val ctor = nth (#ctors fp_res) fp_res_index;
    val abs = #abs absT_info;
    val rep = #rep absT_info;
    val algrho = mk_ctr Ts algrho0;

    val goal = mk_Trueprop_eq (fun_t, abs_curried_balanced arg_Ts algrho);

    fun const_of_transfer thm =
      (case Thm.prop_of thm of \<^Const>\<open>Trueprop\<close> $ (_ $ cst $ _) => cst);

    val eq_algrho =
      Goal.prove (*no sorry*) ctxt [] [] goal (fn {context = ctxt, prems = _} =>
        mk_eq_algrho_tac ctxt fpsig_nesting_maps abs rep ctor ssig_map eval pre_map_def abs_inverse
          fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
          live_nesting_map_ident0s fp_map_ident dtor_ctor ctor_iff_dtor ctr_defs nullary_disc_defs
          disc_sel_eq_cases case_dtor case_eq_ifs const_pointful_naturals
          fp_nesting_k_map_disc_sels' rho_def dtor_algrho corecUU_unique eq_corecUU all_sig_map_thms
          ssig_map_thms all_algLam_alg_pointfuls (all_algrho_eqs_of ctxt) eval_simps)
      |> Thm.close_derivation \<^here>
      handle e as ERROR _ =>
        (case filter (is_none o snd) (const_transfers ~~ const_pointful_natural_opts) of
          [] => Exn.reraise e
        | thm_nones =>
          error ("Failed to state naturality property for " ^
            commas (map (Syntax.string_of_term ctxt o const_of_transfer o fst) thm_nones)));

    val algrho_eq = eq_algrho RS (mk_curry_uncurryN_balanced ctxt num_args RS iffD2) RS sym;
  in
    (eq_algrho, algrho_eq)
  end;

fun prime_rho_transfer_goal ctxt fpT_name rho_def goal =
  let
    val thy = Proof_Context.theory_of ctxt;

    val SOME {pre_bnf, ...} = fp_sugar_of ctxt fpT_name;
    val SOME {abs_rep_transfers, ...} = codatatype_extra_of ctxt fpT_name;

    val simps = rel_def_of_bnf pre_bnf :: rho_transfer_simps;
    val fold_rho = unfold_thms ctxt [rho_def RS @{thm symmetric}];

    fun derive_unprimed rho_transfer' =
      Variable.add_free_names ctxt goal []
      |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
        unfold_thms_tac ctxt simps THEN HEADGOAL (rtac ctxt rho_transfer')))
      |> Thm.close_derivation \<^here>;

    val goal' = Raw_Simplifier.rewrite_term thy simps [] goal;
  in
    if null abs_rep_transfers then (goal', derive_unprimed #> fold_rho)
    else (goal, fold_rho)
  end;

fun derive_rho_transfer_folded ctxt fpT_name const_transfers rho_def goal =
  let
    val SOME {pre_bnf, ...} = fp_sugar_of ctxt fpT_name;
    val SOME {abs_rep_transfers, ...} = codatatype_extra_of ctxt fpT_name;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_rho_transfer_tac ctxt (null abs_rep_transfers) (rel_def_of_bnf pre_bnf)
      const_transfers))
    |> unfold_thms ctxt [rho_def RS @{thm symmetric}]
    |> Thm.close_derivation \<^here>
  end;

fun mk_cong_intro_ctr_or_friend_goal ctxt fpT Rcong alg =
  let
    val xy_Ts = binder_types (fastype_of alg);

    val ((xs, ys), _) = ctxt
      |> mk_Frees "x" xy_Ts
      ||>> mk_Frees "y" xy_Ts;

    fun mk_prem xy_T x y =
      build_rel [] ctxt [fpT] [] (fn (T, _) => if T = fpT then Rcong else HOLogic.eq_const T)
        (xy_T, xy_T) $ x $ y;

    val prems = @{map 3} mk_prem xy_Ts xs ys;
    val concl = Rcong $ list_comb (alg, xs) $ list_comb (alg, ys);
  in
    Logic.list_implies (map HOLogic.mk_Trueprop prems, HOLogic.mk_Trueprop concl)
  end;

fun derive_cong_ctr_intros ctxt cong_ctor_intro =
  let
    val \<^Const_>\<open>Pure.imp\<close> $ _ $ (\<^Const_>\<open>Trueprop\<close> $ ((Rcong as _ $ _) $ _ $ (ctor $ _))) =
      Thm.prop_of cong_ctor_intro;

    val fpT as Type (fpT_name, fp_argTs) = range_type (fastype_of ctor);

    val SOME {pre_bnf, absT_info = {abs_inverse, ...},
        fp_ctr_sugar = {ctr_defs, ctr_sugar = {ctrs = ctrs0, ...}, ...}, ...} =
      fp_sugar_of ctxt fpT_name;

    val ctrs = map (mk_ctr fp_argTs) ctrs0;
    val pre_rel_def = rel_def_of_bnf pre_bnf;

    fun prove ctr_def goal =
      Variable.add_free_names ctxt goal []
      |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
        mk_cong_intro_ctr_or_friend_tac ctxt ctr_def [pre_rel_def, abs_inverse] cong_ctor_intro))
      |> Thm.close_derivation \<^here>;

    val goals = map (mk_cong_intro_ctr_or_friend_goal ctxt fpT Rcong) ctrs;
  in
    map2 prove ctr_defs goals
  end;

fun derive_cong_friend_intro ctxt cong_algrho_intro =
  let
    val \<^Const_>\<open>Pure.imp\<close> $ _ $ (\<^Const_>\<open>Trueprop\<close> $ ((Rcong as _ $ _) $ _
        $ ((algrho as Const (algrho_name, _)) $ _))) =
      Thm.prop_of cong_algrho_intro;

    val fpT as Type (_, fp_argTs) = range_type (fastype_of algrho);

    fun has_algrho (\<^Const_>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ rhs)) =
      fst (dest_Const (head_of (strip_abs_body rhs))) = algrho_name;

    val eq_algrho :: _ =
      maps (filter (has_algrho o Thm.prop_of) o #eq_algrhos o snd) (all_friend_extras_of ctxt);

    val \<^Const_>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ friend0 $ _) = Thm.prop_of eq_algrho;
    val friend = mk_ctr fp_argTs friend0;

    val goal = mk_cong_intro_ctr_or_friend_goal ctxt fpT Rcong friend;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_cong_intro_ctr_or_friend_tac ctxt eq_algrho [] cong_algrho_intro))
    |> Thm.close_derivation \<^here>
  end;

fun derive_cong_intros lthy ctr_names friend_names
    ({cong_base, cong_refl, cong_sym, cong_trans, cong_alg_intros, ...} : dtor_coinduct_info) =
  let
    val cong_ctor_intro :: cong_algrho_intros = rev cong_alg_intros;
    val names = map (prefix cong_N) ([baseN, reflN, symN, transN] @ ctr_names @ friend_names);
    val thms = [cong_base, cong_refl, cong_sym, cong_trans] @
      derive_cong_ctr_intros lthy cong_ctor_intro @
      map (derive_cong_friend_intro lthy) cong_algrho_intros;
  in
    names ~~ thms
  end;

fun derive_coinduct ctxt (fpT as Type (fpT_name, fpT_args)) dtor_coinduct =
  let
    val thy = Proof_Context.theory_of ctxt;

    val \<^Const_>\<open>Pure.imp\<close> $ (\<^Const_>\<open>Trueprop\<close> $ (_ $ Abs (_, _, _ $
        Abs (_, _, \<^Const_>\<open>implies\<close> $ _ $ (_ $ (cong0 $ _) $ _ $ _))))) $ _ =
      Thm.prop_of dtor_coinduct;

    val SOME {X as TVar ((X_s, _), _), fp_res = {dtor_ctors, ...}, pre_bnf,
        absT_info = {abs_inverse, ...}, live_nesting_bnfs,
        fp_ctr_sugar = {ctrXs_Tss, ctr_defs,
          ctr_sugar = ctr_sugar0 as {T = Type (_, T0_args), ctrs = ctrs0, discs = discs0, ...},
            ...}, ...} =
      fp_sugar_of ctxt fpT_name;

    val n = length ctrXs_Tss;
    val ms = map length ctrXs_Tss;

    val X' = TVar ((X_s, maxidx_of_typ fpT + 1), \<^sort>\<open>type\<close>);
    val As_rho = tvar_subst thy T0_args fpT_args;
    val substXAT = Term.typ_subst_TVars As_rho o Tsubst X X';
    val substXA = Term.subst_TVars As_rho o substT X X';
    val phi = Morphism.typ_morphism "BNF" substXAT $> Morphism.term_morphism "BNF" substXA;

    fun mk_applied_cong arg =
      enforce_type ctxt domain_type (fastype_of arg) cong0 $ arg;

    val thm = derive_coinduct_thms_for_types ctxt false mk_applied_cong [pre_bnf] dtor_coinduct
        dtor_ctors live_nesting_bnfs [fpT] [substXAT X] [map (map substXAT) ctrXs_Tss] [n]
        [abs_inverse] [abs_inverse] I [ctr_defs] [morph_ctr_sugar phi ctr_sugar0]
      |> map snd |> the_single;
    val (attrs, _) = mk_coinduct_attrs [fpT] [ctrs0] [discs0] [ms];
  in
    (thm, attrs)
  end;

type explore_parameters =
  {bound_Us: typ list,
   bound_Ts: typ list,
   U: typ,
   T: typ};

fun update_UT {bound_Us, bound_Ts, ...} U T =
  {bound_Us = bound_Us, bound_Ts = bound_Ts, U = U, T = T};

fun explore_nested lthy explore {bound_Us, bound_Ts, U, T} t =
  let
    fun build_simple (T, U) =
      if T = U then
        \<^term>\<open>%y. y\<close>
      else
        Bound 0
        |> explore {bound_Us = T :: bound_Us, bound_Ts = T :: bound_Ts, U = U, T = T}
        |> (fn t => Abs (Name.uu, T, t));
  in
    betapply (build_map lthy [] [] build_simple (T, U), t)
  end;

fun add_boundvar t = betapply (incr_boundvars 1 t, Bound 0);

fun explore_fun (arg_U :: arg_Us) explore {bound_Us, bound_Ts, U, T} t =
    let val arg_name = the_default Name.uu (try (fn (Abs (s, _, _)) => s) t) in
      add_boundvar t
      |> explore_fun arg_Us explore
        {bound_Us = arg_U :: bound_Us, bound_Ts = domain_type T :: bound_Ts, U = range_type U,
         T = range_type T}
      |> (fn t => Abs (arg_name, arg_U, t))
    end
  | explore_fun [] explore params t = explore params t;

fun massage_fun explore (params as {T, U, ...}) =
  if can dest_funT T then explore_fun [domain_type U] explore params else explore params;

fun massage_star massages explore =
  let
    fun after_massage massages' t params t' =
      if t aconv t' then massage_any massages' params t else massage_any massages params t'
    and massage_any [] params t = explore params t
      | massage_any (massage :: massages') params t =
        massage (after_massage massages' t) params t;
  in
    massage_any massages
  end;

fun massage_let explore params t =
  (case strip_comb t of
    (Const (\<^const_name>\<open>Let\<close>, _), [_, _]) => unfold_lets_splits t
  | _ => t)
  |> explore params;

fun check_corec_equation ctxt fun_frees (lhs, rhs) =
  let
    val (fun_t, arg_ts) = strip_comb lhs;

    fun check_fun_name () =
      null fun_frees orelse member (op aconv) fun_frees fun_t orelse
      ill_formed_equation_head ctxt [] fun_t;

    fun check_no_other_frees () =
      (case Term.add_frees rhs [] |> map Free |> subtract (op =) (fun_frees @ arg_ts)
          |> find_first (not o Variable.is_fixed ctxt o fst o dest_Free) of
        NONE => ()
      | SOME t => extra_variable_in_rhs ctxt [] t);
  in
    check_duplicate_variables_in_lhs ctxt [] arg_ts;
    check_fun_name ();
    check_all_fun_arg_frees ctxt [] (filter_out is_Var arg_ts);
    check_no_other_frees ()
  end;

fun parse_corec_equation ctxt fun_frees eq =
  let
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (drop_all eq))
      handle TERM _ => ill_formed_equation_lhs_rhs ctxt [eq];

    val _ = check_corec_equation ctxt fun_frees (lhs, rhs);

    val (fun_t, arg_ts) = strip_comb lhs;
    val (arg_Ts, _) = strip_type (fastype_of fun_t);
    val added_Ts = drop (length arg_ts) arg_Ts;
    val free_names = mk_names (length added_Ts) "x" ~~ added_Ts;
    val free_args = Variable.variant_frees ctxt [rhs, lhs] free_names |> map Free;
  in
    (arg_ts @ free_args, list_comb (rhs, free_args))
  end;

fun morph_views phi (code, ctrs, discs, disc_iffs, sels) =
  (Morphism.term phi code, map (Morphism.term phi) ctrs, map (Morphism.term phi) discs,
   map (Morphism.term phi) disc_iffs, map (Morphism.term phi) sels);

fun generate_views ctxt eq fun_t (lhs_free_args, rhs) =
  let
    val lhs = list_comb (fun_t, lhs_free_args);
    val T as Type (T_name, Ts) = fastype_of rhs;
    val SOME {fp_ctr_sugar = {ctr_sugar = {ctrs = ctrs0, discs = discs0, selss = selss0, ...}, ...},
        ...} =
      fp_sugar_of ctxt T_name;
    val ctrs = map (mk_ctr Ts) ctrs0;
    val discs = map (mk_disc_or_sel Ts) discs0;
    val selss = map (map (mk_disc_or_sel Ts)) selss0;

    val code_view = drop_all eq;

    fun can_case_expand t = not (can (dest_ctr ctxt T_name) t);

    fun generate_raw_views conds t raw_views =
      let
        fun analyse (ctr :: ctrs) (disc :: discs) ctr' =
          if ctr = ctr' then
            (conds, disc, ctr)
          else
            analyse ctrs discs ctr';
      in
        (analyse ctrs discs (fst (strip_comb t))) :: raw_views
      end;

    fun generate_disc_views raw_views =
      if length discs = 1 then
        ([], [])
      else
        let
          fun collect_condss_disc condss [] _ = condss
            | collect_condss_disc condss ((conds, disc', _) :: raw_views) disc =
              collect_condss_disc (condss |> disc = disc' ? cons conds) raw_views disc;

          val grouped_disc_views = discs
            |> map (collect_condss_disc [] raw_views)
            |> curry (op ~~) (map (fn disc => disc $ lhs) discs);

          fun mk_disc_iff_props props [] = props
            | mk_disc_iff_props _ ((lhs, \<^Const_>\<open>True\<close>) :: _) = [lhs]
            | mk_disc_iff_props props ((lhs, rhs) :: views) =
              mk_disc_iff_props ((HOLogic.mk_eq (lhs, rhs)) :: props) views;
        in
          (grouped_disc_views
           |> map swap,
           grouped_disc_views
           |> map (apsnd (s_dnf #> mk_conjs))
           |> mk_disc_iff_props []
           |> map (fn eq => ([[]], eq)))
        end;

    fun generate_ctr_views raw_views =
      let
        fun collect_condss_ctr condss [] _ = condss
          | collect_condss_ctr condss ((conds, _, ctr') :: raw_views) ctr =
            collect_condss_ctr (condss |> ctr = ctr' ? cons conds) raw_views ctr;

        fun mk_ctr_eq ctr_sels ctr =
          let
            fun extract_arg n sel _(*bound_Ts*) fun_t arg_ts =
              if ctr = fun_t then
                nth arg_ts n
              else
                let val t = list_comb (fun_t, arg_ts) in
                  if can_case_expand t then
                    sel $ t
                  else
                    Term.dummy_pattern (range_type (fastype_of sel))
                end;
          in
            ctr_sels
            |> map_index (uncurry extract_arg)
            |> map (fn extract => massage_corec_code_rhs ctxt extract [] rhs)
            |> curry list_comb ctr
            |> curry HOLogic.mk_eq lhs
          end;

          fun remove_condss_if_alone [(_, concl)] = [([[]], concl)]
            | remove_condss_if_alone views = views;
      in
        ctrs
        |> `(map (collect_condss_ctr [] raw_views))
        ||> map2 mk_ctr_eq selss
        |> op ~~
        |> filter_out (null o fst)
        |> remove_condss_if_alone
      end;

    fun generate_sel_views raw_views only_one_ctr =
      let
        fun mk_sel_positions sel =
          let
            fun get_sel_position _ [] = NONE
              | get_sel_position i (sel' :: sels) =
                if sel = sel' then SOME i else get_sel_position (i + 1) sels;
          in
            ctrs ~~ map (get_sel_position 0) selss
            |> map_filter (fn (ctr, pos_opt) =>
              if is_some pos_opt then SOME (ctr, the pos_opt) else NONE)
          end;

        fun collect_sel_condss0 condss [] _ = condss
          | collect_sel_condss0 condss ((conds, _, ctr) :: raw_views) sel_positions =
            let val condss' = condss |> is_some (AList.lookup (op =) sel_positions ctr) ? cons conds
            in
              collect_sel_condss0 condss' raw_views sel_positions
            end;

        val collect_sel_condss =
          if only_one_ctr then K [[]] else collect_sel_condss0 [] raw_views;

        fun mk_sel_rhs sel_positions sel =
          let
            val sel_T = range_type (fastype_of sel);

            fun extract_sel_value _(*bound_Ts*) fun_t arg_ts =
              (case AList.lookup (op =) sel_positions fun_t of
                SOME n => nth arg_ts n
              | NONE =>
                let val t = list_comb (fun_t, arg_ts) in
                  if can_case_expand t then
                    sel $ t
                  else
                    Term.dummy_pattern sel_T
                end);
          in
            massage_corec_code_rhs ctxt extract_sel_value [] rhs
          end;

        val ordered_sels = distinct (op =) (flat selss);
        val sel_positionss = map mk_sel_positions ordered_sels;
        val sel_rhss = map2 mk_sel_rhs sel_positionss ordered_sels;
        val sel_lhss = map (rapp lhs o mk_disc_or_sel Ts) ordered_sels;
        val sel_condss = map collect_sel_condss sel_positionss;

        fun is_undefined (Const (\<^const_name>\<open>undefined\<close>, _)) = true
          | is_undefined _ = false;
      in
        sel_condss ~~ (sel_lhss ~~ sel_rhss)
        |> filter_out (is_undefined o snd o snd)
        |> map (apsnd HOLogic.mk_eq)
      end;

    fun mk_atomic_prop fun_args (condss, concl) =
      (Logic.list_all (map dest_Free fun_args, abstract_over_list fun_args
        (Logic.list_implies (map HOLogic.mk_Trueprop (s_dnf condss), HOLogic.mk_Trueprop concl))));

    val raw_views = rhs
      |> massage_let_if_case ctxt (K false) (fn _(*bound_Ts*) => fn t => t
          |> can_case_expand t ? expand_to_ctr_term ctxt T) (K (K ())) (K I) []
      |> (fn expanded_rhs => fold_rev_let_if_case ctxt generate_raw_views [] expanded_rhs [])
      |> rev;
    val (disc_views, disc_iff_views) = generate_disc_views raw_views;
    val ctr_views = generate_ctr_views raw_views;
    val sel_views = generate_sel_views raw_views (length ctr_views = 1);

    val mk_props = filter_out (null o fst) #> map (mk_atomic_prop lhs_free_args);
  in
    (code_view, mk_props ctr_views, mk_props disc_views, mk_props disc_iff_views,
     mk_props sel_views)
  end;

fun find_all_associated_types [] _ = []
  | find_all_associated_types ((Type (_, Ts1), Type (_, Ts2)) :: TTs) T =
    find_all_associated_types ((Ts1 ~~ Ts2) @ TTs) T
  | find_all_associated_types ((T1, T2) :: TTs) T =
    find_all_associated_types TTs T |> T1 = T ? cons T2;

fun as_member_of tab = try dest_Const #> Option.mapPartial (fst #> Symtab.lookup tab);

fun extract_rho_from_equation
    ({ctr_guards, inner_buffer = {Oper, VLeaf, CLeaf, ctr_wrapper, friends}, ...},
     {pattern_ctrs, discs, sels, it, mk_case})
    b version Y preT ssig_T friend_tm (lhs_args, rhs) lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val res_T = fastype_of rhs;
    val YpreT = HOLogic.mk_prodT (Y, preT);

    fun fpT_to new_T T =
      if T = res_T then
        new_T
      else
        (case T of
          Type (s, Ts) => Type (s, map (fpT_to new_T) Ts)
        | _ => T);

    fun build_params bound_Us bound_Ts T =
      {bound_Us = bound_Us, bound_Ts = bound_Ts, U = T, T = T};

    fun typ_before explore {bound_Us, bound_Ts, ...} t =
      explore (build_params bound_Us bound_Ts (fastype_of1 (bound_Ts, t))) t;

    val is_self_call = curry (op aconv) friend_tm;
    val has_self_call = Term.exists_subterm is_self_call;

    fun has_res_T bound_Ts t = fastype_of1 (bound_Ts, t) = res_T;

    fun contains_res_T (Type (s, Ts)) = s = fst (dest_Type res_T) orelse exists contains_res_T Ts
      | contains_res_T _ = false;

    val res_T_lhs_args = filter (exists_type contains_res_T) lhs_args;
    val is_res_T_lhs_arg = member (op =) res_T_lhs_args;

    fun is_constant t =
      not (Term.exists_subterm is_res_T_lhs_arg t orelse has_self_call t orelse loose_bvar (t, 0));
    fun is_nested_type T = T <> res_T andalso T <> YpreT andalso T <> ssig_T;

    val is_valid_case_argumentT = not o member (op =) [Y, ssig_T];

    fun is_same_type_constr (Type (s, _)) (Type (s', _)) = (s = s')
      | is_same_type_constr _ _ = false;

    exception NO_ENCAPSULATION of unit;

    val parametric_consts = Unsynchronized.ref [];

    (* We are assuming that set functions are marked with "[transfer_rule]" (cf. the "transfer"
       plugin). Otherwise, the "eq_algrho" tactic might fail. *)
    fun is_special_parametric_const (x as (s, _)) =
      s = \<^const_name>\<open>id\<close> orelse is_set lthy x;

    fun add_parametric_const s general_T T U =
      let
        fun tupleT_of_funT T =
          let val (Ts, T) = strip_type T in
            mk_tupleT_balanced (Ts @ [T])
          end;

        fun funT_of_tupleT n =
          dest_tupleT_balanced (n + 1)
          #> split_last
          #> op --->;

        val m = num_binder_types general_T;
        val param1_T = Type_Infer.paramify_vars general_T;
        val param2_T = Type_Infer.paramify_vars param1_T;

        val deadfixed_T =
          build_map lthy [] [] (mk_undefined o op -->) (apply2 tupleT_of_funT (param1_T, param2_T))
          |> singleton (Type_Infer_Context.infer_types lthy)
          |> singleton (Type_Infer.fixate lthy false)
          |> type_of
          |> dest_funT
          |-> generalize_types 1
          |> funT_of_tupleT m;

        val j = maxidx_of_typ deadfixed_T + 1;

        fun varifyT (Type (s, Ts)) = Type (s, map varifyT Ts)
          | varifyT (TFree (s, T)) = TVar ((s, j), T)
          | varifyT T = T;

        val dedvarified_T = varifyT deadfixed_T;

        val new_vars = Sign.typ_match thy (dedvarified_T, T) Vartab.empty
          |> Vartab.dest
          |> filter (curry (op =) j o snd o fst)
          |> Vartab.make;

        val deadinstantiated_T = map_atyps (Type.devar new_vars) dedvarified_T;

        val final_T =
          if Sign.typ_instance thy (U, deadinstantiated_T) then deadfixed_T else general_T;
      in
        parametric_consts := insert (op =) (s, final_T) (!parametric_consts)
      end;

    fun encapsulate (params as {U, T, ...}) t =
      if U = T then
        t
      else if T = Y then
        VLeaf $ t
      else if T = res_T then
        CLeaf $ t
      else if T = YpreT then
        it $ t
      else if is_nested_type T andalso is_same_type_constr T U then
        explore_nested lthy encapsulate params t
      else
        raise NO_ENCAPSULATION ();

    fun build_function_after_encapsulation fun_t fun_t' (params as {bound_Us, ...}) arg_ts arg_ts' =
      let
        val arg_Us' = fst (strip_typeN (length arg_ts) (fastype_of1 (bound_Us, fun_t')));

        fun the_or_error arg NONE =
            error ("Illegal argument " ^ quote (Syntax.string_of_term lthy arg) ^
              " to " ^ quote (Syntax.string_of_term lthy fun_t))
          | the_or_error _ (SOME arg') = arg';
      in
        arg_ts'
        |> `(map (curry fastype_of1 bound_Us))
        |>> map2 (update_UT params) arg_Us'
        |> op ~~
        |> map (try (uncurry encapsulate))
        |> map2 the_or_error arg_ts
        |> curry list_comb fun_t'
      end;

    fun rebuild_function_after_exploration old_fn new_fn explore params arg_ts =
      arg_ts
      |> map (typ_before explore params)
      |> build_function_after_encapsulation old_fn new_fn params arg_ts;

    fun update_case Us U casex =
      let
        val Type (T_name, _) = domain_type (snd (strip_fun_type (fastype_of casex)));
        val SOME {fp_ctr_sugar = {ctr_sugar = {T = Type (_, Ts), casex, ...}, ...}, ...} =
          fp_sugar_of lthy T_name;
        val T = body_type (fastype_of casex);
      in
        Term.subst_atomic_types ((T :: Ts) ~~ (U :: Us)) casex
      end;

    fun deduce_according_type default_T [] = default_T
      | deduce_according_type default_T Ts = (case distinct (op =) Ts of
          U :: [] => U
        | _ => fpT_to ssig_T default_T);

    fun massage_if explore_cond explore (params as {bound_Us, bound_Ts, ...}) t =
      (case strip_comb t of
        (const as Const (\<^const_name>\<open>If\<close>, _), obj :: (branches as [_, _])) =>
        (case List.partition Term.is_dummy_pattern (map (explore params) branches) of
          (dummy_branch' :: _, []) => dummy_branch'
        | (_, [branch']) => branch'
        | (_, branches') =>
          let
            val brancheUs = map (curry fastype_of1 bound_Us) branches';
            val U = deduce_according_type (fastype_of1 (bound_Ts, hd branches)) brancheUs;
            val const_obj' = (If_const U, obj)
              ||> explore_cond (update_UT params \<^typ>\<open>bool\<close> \<^typ>\<open>bool\<close>)
              |> op $;
          in
            build_function_after_encapsulation (const $ obj) const_obj' params branches branches'
          end)
      | _ => explore params t);

    fun massage_map explore (params as {bound_Us, bound_Ts, T = Type (T_name, Ts), ...})
          (t as func $ mapped_arg) =
        if is_self_call (head_of func) then
          explore params t
        else
          (case try (dest_map lthy T_name) func of
            SOME (map_tm, fs) =>
            let
              val n = length fs;
              val mapped_arg' = mapped_arg
                |> `(curry fastype_of1 bound_Ts)
                |>> build_params bound_Us bound_Ts
                |-> explore;
            in
              (case fastype_of1 (bound_Us, mapped_arg') of
                Type (U_name, Us0) =>
                if U_name = T_name then
                  let
                    val Us = map (fpT_to ssig_T) Us0;
                    val temporary_map = map_tm
                      |> mk_map n Us Ts;
                    val map_fn_Ts = fastype_of #> strip_fun_type #> fst;
                    val binder_Uss = map_fn_Ts temporary_map
                      |> map (map (fpT_to ssig_T) o binder_types);
                    val fun_paramss = map_fn_Ts (head_of func)
                      |> map (build_params bound_Us bound_Ts);
                    val fs' = fs
                      |> @{map 4} explore_fun binder_Uss (replicate n explore) fun_paramss;
                    val SOME bnf = bnf_of lthy T_name;
                    val Type (_, bnf_Ts) = T_of_bnf bnf;
                    val typ_alist =
                      lives_of_bnf bnf ~~ map (curry fastype_of1 bound_Us #> range_type) fs';
                    val Us' = map2 the_default Us (map (AList.lookup (op =) typ_alist) bnf_Ts);
                    val map_tm' = map_tm |> mk_map n Us Us';
                  in
                    build_function_after_encapsulation func (list_comb (map_tm', fs')) params
                      [mapped_arg] [mapped_arg']
                  end
                else
                  explore params t
              | _ => explore params t)
            end
          | NONE => explore params t)
      | massage_map explore params t = explore params t;

    fun massage_comp explore (params as {bound_Us, ...}) t =
      (case strip_comb t of
        (Const (\<^const_name>\<open>comp\<close>, _), f1 :: f2 :: args) =>
        let
          val args' = map (typ_before explore params) args;
          val f2' = typ_before (explore_fun (map (curry fastype_of1 bound_Us) args') explore) params
            f2;
          val f1' = typ_before (explore_fun [range_type (fastype_of1 (bound_Us, f2'))] explore)
            params f1;
        in
          betapply (f1', list_comb (f2', args'))
        end
      | _ => explore params t);

    fun massage_ctr explore (params as {T = T as Type (s, Ts), bound_Us, ...}) t =
        if T <> res_T then
          (case try (dest_ctr lthy s) t of
            SOME (ctr, args) =>
            let
              val args' = map (typ_before explore params) args;
              val SOME {T = Type (_, ctr_Ts), ...} = ctr_sugar_of lthy s;
              val temp_ctr = mk_ctr ctr_Ts ctr;
              val argUs = map (curry fastype_of1 bound_Us) args';
              val typ_alist = binder_types (fastype_of temp_ctr) ~~ argUs;
              val Us = ctr_Ts
                |> map (find_all_associated_types typ_alist)
                |> map2 deduce_according_type Ts;
              val ctr' = mk_ctr Us ctr;
            in
              build_function_after_encapsulation ctr ctr' params args args'
            end
          | NONE => explore params t)
        else
          explore params t
      | massage_ctr explore params t = explore params t;

    fun const_of [] _ = NONE
      | const_of ((sel as Const (s1, _)) :: r) (const as Const (s2, _)) =
        if s1 = s2 then SOME sel else const_of r const
      | const_of _ _ = NONE;

    fun massage_disc explore (params as {T, bound_Us, bound_Ts, ...}) t =
      (case (strip_comb t, T = \<^typ>\<open>bool\<close>) of
        ((fun_t, arg :: []), true) =>
        let val arg_T = fastype_of1 (bound_Ts, arg) in
          if arg_T <> res_T then
            (case arg_T |> try (fst o dest_Type) |> Option.mapPartial (ctr_sugar_of lthy) of
              SOME {discs, T = Type (_, Ts), ...} =>
              (case const_of discs fun_t of
                SOME disc =>
                let
                  val arg' = arg |> typ_before explore params;
                  val Type (_, Us) = fastype_of1 (bound_Us, arg');
                  val disc' = disc |> Term.subst_TVars (map (fst o dest_TVar) Ts ~~ Us);
                in
                  disc' $ arg'
                end
              | NONE => explore params t)
            | NONE => explore params t)
          else
            explore params t
        end
      | _ => explore params t);

    fun massage_sel explore (params as {bound_Us, bound_Ts, ...}) t =
      let val (fun_t, args) = strip_comb t in
        if args = [] then
          explore params t
        else
          let val T = fastype_of1 (bound_Ts, hd args) in
            (case (Option.mapPartial (ctr_sugar_of lthy) (try (fst o dest_Type) T), T <> res_T) of
              (SOME {selss, T = Type (_, Ts), ...}, true) =>
              (case const_of (flat selss) fun_t of
                SOME sel =>
                let
                  val args' = args |> map (typ_before explore params);
                  val Type (_, Us) = fastype_of1 (bound_Us, hd args');
                  val sel' = sel |> Term.subst_TVars (map (fst o dest_TVar) Ts ~~ Us);
                in
                  build_function_after_encapsulation sel sel' params args args'
                end
              | NONE => explore params t)
            | _ => explore params t)
          end
      end;

    fun massage_equality explore (params as {bound_Us, bound_Ts, ...})
          (t as Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2) =
        let
          val check_is_VLeaf =
            not o (Term.exists_subterm (fn t => t aconv CLeaf orelse t aconv Oper));

          fun try_pattern_matching (fun_t, arg_ts) t =
            (case as_member_of pattern_ctrs fun_t of
              SOME (disc, sels) =>
              let val t' = typ_before explore params t in
                if fastype_of1 (bound_Us, t') = YpreT then
                  let
                    val arg_ts' = map (typ_before explore params) arg_ts;
                    val sels_t' = map (fn sel => betapply (sel, t')) sels;
                    val Ts = map (curry fastype_of1 bound_Us) arg_ts';
                    val Us = map (curry fastype_of1 bound_Us) sels_t';
                    val arg_ts' = map2 encapsulate (map2 (update_UT params) Us Ts) arg_ts';
                  in
                    if forall check_is_VLeaf arg_ts' then
                      SOME (Library.foldl1 HOLogic.mk_conj
                        (betapply (disc, t') :: (map HOLogic.mk_eq (arg_ts' ~~ sels_t'))))
                    else
                      NONE
                  end
                else
                  NONE
              end
            | NONE => NONE);
        in
          (case try_pattern_matching (strip_comb t1) t2 of
            SOME cond => cond
          | NONE => (case try_pattern_matching (strip_comb t2) t1 of
              SOME cond => cond
            | NONE =>
              let
                val T = fastype_of1 (bound_Ts, t1);
                val params' = build_params bound_Us bound_Ts T;
                val t1' = explore params' t1;
                val t2' = explore params' t2;
              in
                if fastype_of1 (bound_Us, t1') = T andalso fastype_of1 (bound_Us, t2') = T then
                  HOLogic.mk_eq (t1', t2')
                else
                  error ("Unsupported condition: " ^ quote (Syntax.string_of_term lthy t))
              end))
        end
      | massage_equality explore params t = explore params t;

    fun infer_types (TVar _) (TVar _) = []
      | infer_types (U as TVar _) T = [(U, T)]
      | infer_types (Type (s', Us)) (Type (s, Ts)) =
        if s' = s then flat (map2 infer_types Us Ts) else []
      | infer_types _ _ = [];

    fun group_by_fst associations [] = associations
      | group_by_fst associations ((a, b) :: r) = group_by_fst (add_association a b associations) r
    and add_association a b [] = [(a, [b])]
      | add_association a b ((c, d) :: r) =
        if a = c then (c, b :: d) :: r
        else (c, d) :: (add_association a b r);

    fun new_TVar known_TVars =
      Name.invent_list (map (fst o fst o dest_TVar) known_TVars) "x" 1
      |> (fn [s] => TVar ((s, 0), []));

    fun instantiate_type inferred_types =
      Term.typ_subst_TVars (map (apfst (fst o dest_TVar)) inferred_types);

    fun chose_unknown_TVar (T as TVar _) = SOME T
      | chose_unknown_TVar (Type (_, Ts)) =
        fold (curry merge_options) (map chose_unknown_TVar Ts) NONE
      | chose_unknown_TVar _ = NONE;

    (* The function under definition might not be defined yet when this is queried. *)
    fun maybe_const_type ctxt (s, T) =
      Sign.const_type (Proof_Context.theory_of ctxt) s |> the_default T;

    fun massage_const polymorphic explore (params as {bound_Us, ...}) t =
      let val (fun_t, arg_ts) = strip_comb t in
        (case fun_t of
          Const (fun_x as (s, fun_T)) =>
          let val general_T = if polymorphic then maybe_const_type lthy fun_x else fun_T in
            if fun_t aconv friend_tm orelse contains_res_T (body_type general_T) orelse
               is_constant t then
              explore params t
            else
              let
                val inferred_types = infer_types general_T fun_T;

                fun prepare_skeleton [] _ = []
                  | prepare_skeleton ((T, U) :: inferred_types) As =
                    let
                      fun schematize_res_T U As =
                        if U = res_T then
                          let val A = new_TVar As in
                            (A, A :: As)
                          end
                        else
                          (case U of
                            Type (s, Us) => fold_map schematize_res_T Us As |>> curry Type s
                          | _ => (U, As));

                      val (U', As') = schematize_res_T U As;
                    in
                      (T, U') :: (prepare_skeleton inferred_types As')
                    end;

                val inferred_types' = prepare_skeleton inferred_types (map fst inferred_types);
                val skeleton_T = instantiate_type inferred_types' general_T;

                fun explore_if_possible (exp_arg as (_, true)) _ = exp_arg
                  | explore_if_possible (exp_arg as (arg, false)) arg_T =
                    if exists (exists_subtype is_TVar) (binder_types arg_T) then exp_arg
                    else (typ_before (explore_fun (binder_types arg_T) explore) params arg, true);

                fun collect_inferred_types [] _ = []
                  | collect_inferred_types ((arg, explored) :: exp_arg_ts) (arg_T :: arg_Ts) =
                    (if explored then infer_types arg_T (fastype_of1 (bound_Us, arg)) else []) @
                    collect_inferred_types exp_arg_ts arg_Ts;

                fun propagate exp_arg_ts skeleton_T =
                  let
                    val arg_gen_Ts = binder_types skeleton_T;
                    val exp_arg_ts = map2 explore_if_possible exp_arg_ts arg_gen_Ts;
                    val inferred_types = collect_inferred_types exp_arg_ts arg_gen_Ts
                      |> group_by_fst []
                      |> map (apsnd (deduce_according_type ssig_T));
                  in
                    (exp_arg_ts, instantiate_type inferred_types skeleton_T)
                  end;

                val remaining_to_be_explored = filter_out snd #> length;

                fun try_exploring_args exp_arg_ts skeleton_T =
                  let
                    val n = remaining_to_be_explored exp_arg_ts;
                    val (exp_arg_ts', skeleton_T') = propagate exp_arg_ts skeleton_T;
                    val n' = remaining_to_be_explored exp_arg_ts';

                    fun try_instantiating A T =
                      try (try_exploring_args exp_arg_ts') (instantiate_type [(A, T)] skeleton_T');
                  in
                    if n' = 0 then
                      SOME (exp_arg_ts', skeleton_T')
                    else if n = n' then
                      if exists_subtype is_TVar skeleton_T' then
                        let val SOME A = chose_unknown_TVar skeleton_T' in
                          (case try_instantiating A ssig_T of
                            SOME result => result
                          | NONE => (case try_instantiating A YpreT of
                              SOME result => result
                            | NONE => (case try_instantiating A res_T of
                                SOME result => result
                              | NONE => NONE)))
                        end
                      else
                        NONE
                    else
                      try_exploring_args exp_arg_ts' skeleton_T'
                  end;
              in
                (case try_exploring_args (map (fn arg => (arg, false)) arg_ts) skeleton_T of
                  SOME (exp_arg_ts, fun_U) =>
                  let
                    val arg_ts' = map fst exp_arg_ts;
                    val fun_t' = Const (s, fun_U);

                    fun finish_off () =
                      let
                        val t' =
                          build_function_after_encapsulation fun_t fun_t' params arg_ts arg_ts';
                      in
                        if can type_of1 (bound_Us, t') then
                          (if fun_T = fun_U orelse is_special_parametric_const (s, fun_T) then ()
                           else add_parametric_const s general_T fun_T fun_U;
                           t')
                        else
                          explore params t
                      end;
                  in
                    if polymorphic then
                      finish_off ()
                    else
                      (case try finish_off () of
                        SOME t' => t'
                      | NONE => explore params t)
                  end
                | NONE => explore params t)
              end
          end
        | _ => explore params t)
      end;

    fun massage_rho explore =
      massage_star [massage_let, massage_if explore_cond, massage_case, massage_fun, massage_comp,
          massage_map, massage_ctr, massage_sel, massage_disc, massage_equality,
          massage_const false, massage_const true]
        explore
    and massage_case explore (params as {bound_Ts, bound_Us, ...}) t =
      (case strip_comb t of
        (casex as Const (case_x as (c, _)), args as _ :: _ :: _) =>
        (case try strip_fun_type (maybe_const_type lthy case_x) of
          SOME (gen_branch_Ts, gen_body_fun_T) =>
          let
            val gen_branch_ms = map num_binder_types gen_branch_Ts;
            val n = length gen_branch_ms;
            val (branches, obj_leftovers) = chop n args;
          in
            if n < length args then
              (case gen_body_fun_T of
                Type (_, [Type (T_name, _), _]) =>
                if case_of lthy T_name = SOME (c, true) then
                  let
                    val brancheTs = binder_fun_types (fastype_of1 (bound_Ts, casex));
                    val obj_leftover_Ts = map (curry fastype_of1 bound_Ts) obj_leftovers;
                    val obj_leftovers' =
                      if is_constant (hd obj_leftovers) then
                        obj_leftovers
                      else
                        (obj_leftover_Ts, obj_leftovers)
                        |>> map (build_params bound_Us bound_Ts)
                        |> op ~~
                        |> map (uncurry explore_inner);
                    val obj_leftoverUs = obj_leftovers' |> map (curry fastype_of1 bound_Us);

                    val _ = is_valid_case_argumentT (hd obj_leftoverUs) orelse
                      error (quote (Syntax.string_of_term lthy (hd obj_leftovers)) ^
                        " is not a valid case argument");

                    val Us = obj_leftoverUs |> hd |> dest_Type |> snd;

                    val branche_binderUss =
                      (if hd obj_leftoverUs = YpreT then mk_case HOLogic.boolT
                       else update_case Us HOLogic.boolT casex)
                      |> fastype_of
                      |> binder_fun_types
                      |> map binder_types;
                    val b_params = map (build_params bound_Us bound_Ts) brancheTs;

                    val branches' = branches
                      |> @{map 4} explore_fun branche_binderUss (replicate n explore) b_params;
                    val brancheUs = map (curry fastype_of1 bound_Us) branches';
                    val U = deduce_according_type (body_type (hd brancheTs))
                      (map body_type brancheUs);
                    val casex' =
                      if hd obj_leftoverUs = YpreT then mk_case U else update_case Us U casex;
                  in
                    build_function_after_encapsulation casex casex' params
                      (branches @ obj_leftovers) (branches' @ obj_leftovers')
                  end
                else
                  explore params t
              | _ => explore params t)
            else
              explore params t
          end
        | NONE => explore params t)
      | _ => explore params t)
    and explore_cond params t =
      if has_self_call t then unexpected_rec_call_in lthy [] t else explore_inner params t
    and explore_inner params t =
      massage_rho explore_inner_general params t
    and explore_inner_general (params as {bound_Us, bound_Ts, T, ...}) t =
      let val (fun_t, arg_ts) = strip_comb t in
        if is_constant t then
          t
        else
          (case (as_member_of discs fun_t,
              length arg_ts = 1 andalso has_res_T bound_Ts (the_single arg_ts)) of
            (SOME disc', true) =>
            let
              val arg' = explore_inner params (the_single arg_ts);
              val arg_U = fastype_of1 (bound_Us, arg');
            in
              if arg_U = res_T then
                fun_t $ arg'
              else if arg_U = YpreT then
                disc' $ arg'
              else
                error ("Discriminator " ^ quote (Syntax.string_of_term lthy fun_t) ^
                  " cannot be applied to non-variable " ^
                  quote (Syntax.string_of_term lthy (hd arg_ts)))
            end
          | _ =>
            (case as_member_of sels fun_t of
              SOME sel' =>
              let
                val arg_ts' = map (explore_inner params) arg_ts;
                val arg_U = fastype_of1 (bound_Us, hd arg_ts');
              in
                if arg_U = res_T then
                  build_function_after_encapsulation fun_t fun_t params arg_ts arg_ts'
                else if arg_U = YpreT then
                  build_function_after_encapsulation fun_t sel' params arg_ts arg_ts'
                else
                  error ("Selector " ^ quote (Syntax.string_of_term lthy fun_t) ^
                    " cannot be applied to non-variable " ^
                    quote (Syntax.string_of_term lthy (hd arg_ts)))
              end
            | NONE =>
              (case as_member_of friends fun_t of
                SOME (_, friend') =>
                rebuild_function_after_exploration fun_t friend' explore_inner params arg_ts
                |> curry (op $) Oper
              | NONE =>
                (case as_member_of ctr_guards fun_t of
                  SOME ctr_guard' =>
                  rebuild_function_after_exploration fun_t ctr_guard' explore_inner params arg_ts
                  |> curry (op $) ctr_wrapper
                  |> curry (op $) Oper
                | NONE =>
                  if is_Bound fun_t then
                    rebuild_function_after_exploration fun_t fun_t explore_inner params arg_ts
                  else if is_Free fun_t then
                    let val fun_t' = map_types (fpT_to YpreT) fun_t in
                      rebuild_function_after_exploration fun_t fun_t' explore_inner params arg_ts
                    end
                  else if T = res_T then
                    error (quote (Syntax.string_of_term lthy fun_t) ^
                      " not polymorphic enough to be applied like this and no friend")
                  else
                    error (quote (Syntax.string_of_term lthy fun_t) ^
                      " not polymorphic enough to be applied like this")))))
      end;

    fun explore_ctr params t =
      massage_rho explore_ctr_general params t
    and explore_ctr_general params t =
      let
        val (fun_t, arg_ts) = strip_comb t;
        val ctr_opt = as_member_of ctr_guards fun_t;
      in
        if is_some ctr_opt then
          rebuild_function_after_exploration fun_t (the ctr_opt) explore_inner params arg_ts
        else
          not_constructor_in_rhs lthy [] fun_t
      end;

    val rho_rhs = rhs
      |> explore_ctr (build_params [] [] (fastype_of rhs))
      |> abs_tuple_balanced (map (map_types (fpT_to YpreT)) lhs_args)
      |> unfold_id_bnf_etc lthy;
  in
    lthy
    |> define_const false b version rhoN rho_rhs
    |>> pair (!parametric_consts, rho_rhs)
  end;

fun mk_rho_parametricity_goal ctxt Y Z preT ssig_T dead_pre_rel dead_k_rel dead_ssig_rel rho_rhs =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val ZpreT = Tsubst Y Z YpreT;
    val ssigZ_T = Tsubst Y Z ssig_T;

    val dead_pre_rel' = Term.subst_atomic_types [(Y, ssig_T), (Z, ssigZ_T)] dead_pre_rel;
    val dead_k_rel' = Term.subst_atomic_types [(Y, YpreT), (Z, ZpreT)] dead_k_rel;

    val (R, _) = ctxt
      |> yield_singleton (mk_Frees "R") (mk_pred2T Y Z);

    val rho_rel = mk_rel_fun (dead_k_rel' $ mk_rel_prod R (dead_pre_rel $ R))
      (dead_pre_rel' $ (dead_ssig_rel $ R));
    val rho_rhsZ = substT Y Z rho_rhs;
  in
    HOLogic.mk_Trueprop (rho_rel $ rho_rhs $ rho_rhsZ)
  end;

fun extract_rho_return_transfer_goals fun_b version dead_pre_bnf dead_k_bnf Y Z preT k_T ssig_T
    ssig_fp_sugar friend_parse_info fun_t parsed_eq lthy =
  let
    fun mk_rel T bnf =
      let
        val ZT = Tsubst Y Z T;
        val rel_T = mk_predT [mk_pred2T Y Z, T, ZT];
      in
        enforce_type lthy I rel_T (rel_of_bnf bnf)
      end;

    val ssig_bnf = #fp_bnf ssig_fp_sugar;

    val (dead_ssig_bnf, lthy') = bnf_kill_all_but 1 ssig_bnf lthy;

    val dead_pre_rel = mk_rel preT dead_pre_bnf;
    val dead_k_rel = mk_rel k_T dead_k_bnf;
    val dead_ssig_rel = mk_rel ssig_T dead_ssig_bnf;

    val (((parametric_consts, rho_rhs), rho_data), lthy'') =
      extract_rho_from_equation friend_parse_info fun_b version Y preT ssig_T fun_t parsed_eq lthy';

    val const_transfer_goals = map (mk_const_transfer_goal lthy'') parametric_consts;

    val rho_transfer_goal =
      mk_rho_parametricity_goal lthy'' Y Z preT ssig_T dead_pre_rel dead_k_rel dead_ssig_rel rho_rhs;
  in
    ((rho_data, (const_transfer_goals, rho_transfer_goal)), lthy'')
  end;

fun explore_corec_equation ctxt could_be_friend friend fun_name fun_free
    {outer_buffer, ctr_guards, inner_buffer} res_T (args, rhs) =
  let
    val is_self_call = curry (op aconv) fun_free;
    val has_self_call = Term.exists_subterm is_self_call;

    val outer_ssig_T = body_type (fastype_of (#Oper outer_buffer));

    fun inner_fp_of (Free (s, _)) =
      Free (s ^ inner_fp_suffix, mk_tupleT_balanced (map fastype_of args) --> outer_ssig_T);

    fun build_params bound_Ts U T =
      {bound_Us = bound_Ts, bound_Ts = bound_Ts, U = U, T = T};

    fun rebuild_function_after_exploration new_fn explore {bound_Ts, ...} arg_ts =
      let
        val binder_types_old_fn = map (curry fastype_of1 bound_Ts) arg_ts;
        val binder_types_new_fn = new_fn
          |> binder_types o (curry fastype_of1 bound_Ts)
          |> take (length binder_types_old_fn);
        val paramss =
          map2 (build_params bound_Ts) binder_types_new_fn binder_types_old_fn;
      in
        map2 explore paramss arg_ts
        |> curry list_comb new_fn
      end;

    fun massage_map_corec explore {bound_Ts, U, T, ...} t =
      let val explore' = explore ooo build_params in
        massage_nested_corec_call ctxt has_self_call explore' explore' bound_Ts U T t
      end;

    fun massage_comp explore params t =
      (case strip_comb t of
        (Const (\<^const_name>\<open>comp\<close>, _), f1 :: f2 :: args) =>
        explore params (betapply (f1, (betapplys (f2, args))))
      | _ => explore params t);

    fun massage_fun explore (params as {bound_Us, bound_Ts, U, T}) t =
      if can dest_funT T then
        let
          val arg_T = domain_type T;
          val arg_name = the_default Name.uu (try (fn (Abs (s, _, _)) => s) t);
        in
          add_boundvar t
          |> explore {bound_Us = arg_T :: bound_Us, bound_Ts = arg_T :: bound_Ts,
             U = range_type U, T = range_type T}
          |> (fn t => Abs (arg_name, arg_T, t))
        end
      else
        explore params t

    fun massage_let_if_case_corec explore {bound_Ts, U, T, ...} t =
      massage_let_if_case ctxt has_self_call (fn bound_Ts => explore (build_params bound_Ts U T))
        (K (unexpected_corec_call_in ctxt [t])) (K (unsupported_case_around_corec_call ctxt [t]))
        bound_Ts t;

    val massage_map_let_if_case =
      massage_star [massage_map_corec, massage_fun, massage_comp, massage_let_if_case_corec];

    fun explore_arg _ t =
      if has_self_call t then
        error (quote (Syntax.string_of_term ctxt t) ^ " contains a nested corecursive call" ^
          (if could_be_friend then " (try specifying \"(friend)\")" else ""))
      else
        t;

    fun explore_inner params t =
      massage_map_let_if_case explore_inner_general params t
    and explore_inner_general (params as {bound_Ts, T, ...}) t =
      if T = res_T then
        let val (f_t, arg_ts) = strip_comb t in
          if has_self_call t then
            (case as_member_of (#friends inner_buffer) f_t of
              SOME (_, friend') =>
              rebuild_function_after_exploration friend' explore_inner params arg_ts
              |> curry (op $) (#Oper inner_buffer)
            | NONE =>
              (case as_member_of ctr_guards f_t of
                SOME ctr_guard' =>
                rebuild_function_after_exploration ctr_guard' explore_inner params arg_ts
                |> curry (op $) (#ctr_wrapper inner_buffer)
                |> curry (op $) (#Oper inner_buffer)
              | NONE =>
                if is_self_call f_t then
                  if friend andalso exists has_self_call arg_ts then
                    (case Symtab.lookup (#friends inner_buffer) fun_name of
                      SOME (_, friend') =>
                      rebuild_function_after_exploration friend' explore_inner params arg_ts
                      |> curry (op $) (#Oper inner_buffer))
                  else
                    let val arg_Ts = binder_types (fastype_of1 (bound_Ts, f_t)) in
                      map2 explore_arg (map2 (update_UT params) arg_Ts arg_Ts) arg_ts
                      |> mk_tuple1_balanced bound_Ts
                      |> curry (op $) (#VLeaf inner_buffer)
                    end
                else
                  error (quote (Syntax.string_of_term ctxt f_t) ^ " not registered as friend")))
          else
            #CLeaf inner_buffer $ t
        end
      else if has_self_call t then
        error (quote (Syntax.string_of_term ctxt t) ^ " contains a corecursive call but has type " ^
          quote (Syntax.string_of_typ ctxt T))
      else
        explore_nested ctxt explore_inner_general params t;

    fun explore_outer params t =
      massage_map_let_if_case explore_outer_general params t
    and explore_outer_general (params as {bound_Ts, T, ...}) t =
      if T = res_T then
        let val (f_t, arg_ts) = strip_comb t in
          (case as_member_of ctr_guards f_t of
            SOME ctr_guard' =>
            rebuild_function_after_exploration ctr_guard' explore_inner params arg_ts
            |> curry (op $) (#VLeaf outer_buffer)
          | NONE =>
            if not (has_self_call t) then
              t
              |> expand_to_ctr_term ctxt T
              |> massage_let_if_case_corec explore_outer_general params
            else
              (case as_member_of (#friends outer_buffer) f_t of
                SOME (_, friend') =>
                rebuild_function_after_exploration friend' explore_outer params arg_ts
                |> curry (op $) (#Oper outer_buffer)
              | NONE =>
                if is_self_call f_t then
                  let val arg_Ts = binder_types (fastype_of1 (bound_Ts, f_t)) in
                    map2 explore_arg (map2 (update_UT params) arg_Ts arg_Ts) arg_ts
                    |> mk_tuple1_balanced bound_Ts
                    |> curry (op $) (inner_fp_of f_t)
                  end
                else
                  error (quote (Syntax.string_of_term ctxt f_t) ^ " not registered as friend")))
        end
      else if has_self_call t then
        error (quote (Syntax.string_of_term ctxt t) ^ " contains a corecursive call but has type " ^
          quote (Syntax.string_of_typ ctxt T))
      else
        explore_nested ctxt explore_outer_general params t;
  in
    (args, rhs
      |> explore_outer (build_params [] outer_ssig_T res_T)
      |> abs_tuple_balanced args)
  end;

fun mk_corec_fun_def_rhs ctxt arg_Ts corecUU0 corecUU_arg =
  let val corecUU = enforce_type ctxt domain_type (fastype_of corecUU_arg) corecUU0 in
    abs_curried_balanced arg_Ts (corecUU $ unfold_id_bnf_etc ctxt corecUU_arg)
  end;

fun get_options ctxt opts =
  let
    val plugins = get_first (fn Plugins_Option f => SOME (f ctxt) | _ => NONE) (rev opts)
      |> the_default Plugin_Name.default_filter;
    val friend = exists (can (fn Friend_Option => ())) opts;
    val transfer = exists (can (fn Transfer_Option => ())) opts;
  in
    (plugins, friend, transfer)
  end;

fun add_function binding parsed_eq lthy =
  let
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt;

    val ({defname, pelims = [[pelim]], pinducts = [pinduct], psimps = [psimp], ...}, lthy') =
      Function.add_function [(Binding.concealed binding, NONE, NoSyn)]
        [(((Binding.concealed Binding.empty, []), parsed_eq), [], [])]
        Function_Common.default_config pat_completeness_auto lthy;
  in
    ((defname, (pelim, pinduct, psimp)), lthy')
  end;

fun build_corecUU_arg_and_goals prove_termin (Free (fun_base_name, _)) (arg_ts, explored_rhs) lthy =
  let
    val inner_fp_name0 = fun_base_name ^ inner_fp_suffix;
    val inner_fp_free = Free (inner_fp_name0, fastype_of explored_rhs);
  in
    if Term.exists_subterm (curry (op aconv) inner_fp_free) explored_rhs then
      let
        val arg = mk_tuple_balanced arg_ts;
        val inner_fp_eq =
          mk_Trueprop_eq (betapply (inner_fp_free, arg), betapply (explored_rhs, arg));

        val ((inner_fp_name, (pelim, pinduct, psimp)), lthy') =
          add_function (Binding.name inner_fp_name0) inner_fp_eq lthy;

        fun mk_triple elim induct simp = ([elim], [induct], [simp]);

        fun prepare_termin () =
          let
            val {goal, ...} = Proof.goal (Function.termination NONE lthy');
            val termin_goal = goal |> Thm.concl_of |> Logic.unprotect |> Envir.beta_eta_contract;
          in
            (lthy', (mk_triple pelim pinduct psimp, [termin_goal]))
          end;

        val (lthy'', (inner_fp_triple, termin_goals)) =
          if prove_termin then
            (case try (Function.prove_termination NONE
                (Function_Common.termination_prover_tac true lthy')) lthy' of
              NONE => prepare_termin ()
            | SOME ({elims = SOME [[elim]], inducts = SOME [induct], simps = SOME [simp], ...},
                lthy'') =>
              (lthy'', (mk_triple elim induct simp, [])))
          else
            prepare_termin ();

        val inner_fp_const = (Binding.name_of inner_fp_name, fastype_of explored_rhs)
          |>> Proof_Context.read_const {proper = true, strict = false} lthy'
          |> (fn (Const (s, _), T) => Const (s, T));
      in
        (((inner_fp_triple, termin_goals), inner_fp_const), lthy'')
      end
    else
      (((([], [], []), []), explored_rhs), lthy)
  end;

fun derive_eq_corecUU ctxt {sig_fp_sugars, ssig_fp_sugar, eval, corecUU, eval_simps,
      all_algLam_algs, corecUU_unique, ...}
    fun_t corecUU_arg fun_code =
  let
    val fun_T = fastype_of fun_t;
    val (arg_Ts, Type (fpT_name, _)) = strip_type fun_T;
    val num_args = length arg_Ts;

    val SOME {pre_bnf, fp_bnf, absT_info, fp_nesting_bnfs, live_nesting_bnfs, fp_ctr_sugar, ...} =
      fp_sugar_of ctxt fpT_name;
    val SOME {case_trivial, ...} = codatatype_extra_of ctxt fpT_name;

    val ctr_sugar = #ctr_sugar fp_ctr_sugar;
    val pre_map_def = map_def_of_bnf pre_bnf;
    val abs_inverse = #abs_inverse absT_info;
    val ctr_defs = #ctr_defs fp_ctr_sugar;
    val case_eq_ifs = #case_eq_ifs ctr_sugar @ case_eq_if_thms_of_term ctxt (Thm.prop_of fun_code);
    val all_sig_map_thms = maps (#map_thms o #fp_bnf_sugar) sig_fp_sugars;

    val fp_map_ident = map_ident_of_bnf fp_bnf;
    val fpsig_nesting_bnfs = fp_nesting_bnfs @ maps #live_nesting_bnfs sig_fp_sugars;
    val fpsig_nesting_T_names = map (fst o dest_Type o T_of_bnf) fpsig_nesting_bnfs;
    val fpsig_nesting_fp_sugars = map_filter (fp_sugar_of ctxt) fpsig_nesting_T_names;
    val fpsig_nesting_fp_bnf_sugars = map #fp_bnf_sugar fpsig_nesting_fp_sugars;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;
    val ssig_map = map_of_bnf ssig_bnf;
    val fpsig_nesting_maps = map map_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_ident0s = map map_ident0_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_comps = map map_comp_of_bnf fpsig_nesting_bnfs;
    val fpsig_nesting_map_thms = maps #map_thms fpsig_nesting_fp_bnf_sugars;
    val live_nesting_map_ident0s = map map_ident0_of_bnf live_nesting_bnfs;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val all_algLam_alg_pointfuls = map (mk_pointful ctxt) all_algLam_algs;

    val def_rhs = mk_corec_fun_def_rhs ctxt arg_Ts corecUU corecUU_arg;

    val goal = mk_Trueprop_eq (fun_t, def_rhs);
  in
    Goal.prove_sorry ctxt [] [] goal (fn {context = ctxt, prems = _} =>
      mk_eq_corecUU_tac ctxt num_args fpsig_nesting_maps ssig_map eval pre_map_def abs_inverse
        fpsig_nesting_map_ident0s fpsig_nesting_map_comps fpsig_nesting_map_thms
        live_nesting_map_ident0s fp_map_ident case_trivial ctr_defs case_eq_ifs all_sig_map_thms
        ssig_map_thms all_algLam_alg_pointfuls (all_algrho_eqs_of ctxt) eval_simps corecUU_unique
        fun_code)
    |> Thm.close_derivation \<^here>
  end;

fun derive_coinduct_cong_intros
    ({fpT = fpT0 as Type (fpT_name, _), friend_names = friend_names0,
      corecUU = Const (corecUU_name, _), dtor_coinduct_info as {dtor_coinduct, ...}, ...})
    lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val phi = Proof_Context.export_morphism lthy (Local_Theory.target_of lthy);

    val fpT = Morphism.typ phi fpT0;
    val general_fpT = body_type (Sign.the_const_type thy corecUU_name);
    val most_general = Sign.typ_instance thy (general_fpT, fpT);
  in
    (case (most_general, coinduct_extra_of lthy corecUU_name) of
      (true, SOME extra) => ((false, extra), lthy)
    | _ =>
      let
        val ctr_names = ctr_names_of_fp_name lthy fpT_name;
        val friend_names = friend_names0 |> map Long_Name.base_name |> rev;
        val cong_intro_pairs = derive_cong_intros lthy ctr_names friend_names dtor_coinduct_info;
        val (coinduct, coinduct_attrs) = derive_coinduct lthy fpT0 dtor_coinduct;
        val ((_, [coinduct]), lthy) = (* TODO check: only if most_general?*)
          Local_Theory.note ((Binding.empty, coinduct_attrs), [coinduct]) lthy;

        val extra = {coinduct = coinduct, coinduct_attrs = coinduct_attrs,
          cong_intro_pairs = cong_intro_pairs};
      in
        ((most_general, extra), lthy |> most_general ? register_coinduct_extra corecUU_name extra)
      end)
  end;

fun update_coinduct_cong_intross_dynamic fpT_name lthy =
  let val all_corec_infos = corec_infos_of lthy fpT_name in
    lthy
    |> fold_map (apfst snd oo derive_coinduct_cong_intros) all_corec_infos
    |> snd
  end;

fun derive_and_update_coinduct_cong_intross [] = pair (false, [])
  | derive_and_update_coinduct_cong_intross (corec_infos as {fpT = Type (fpT_name, _), ...} :: _) =
    fold_map derive_coinduct_cong_intros corec_infos
    #>> split_list
    #> (fn ((changeds, extras), lthy) =>
      if exists I changeds then
        ((true, extras), lthy |> update_coinduct_cong_intross_dynamic fpT_name)
      else
        ((false, extras), lthy));

fun prepare_corec_ursive_cmd int long_cmd opts (raw_fixes, raw_eq) lthy =
  let
    val _ = can the_single raw_fixes orelse
      error "Mutually corecursive functions not supported";

    val (plugins, friend, transfer) = get_options lthy opts;
    val ([((b, fun_T), mx)], [(_, eq)]) =
      fst (Specification.read_multi_specs raw_fixes [((Binding.empty_atts, raw_eq), [], [])] lthy);

    val _ = check_top_sort lthy b fun_T;

    val (arg_Ts, res_T) = strip_type fun_T;
    val fpT_name = (case res_T of Type (s, _) => s | _ => not_codatatype lthy res_T);
    val fun_free = Free (Binding.name_of b, fun_T);
    val parsed_eq = parse_corec_equation lthy [fun_free] eq;

    val fun_name = Local_Theory.full_name lthy b;
    val fun_t = Const (fun_name, fun_T);
      (* FIXME: does this work with locales that fix variables? *)

    val no_base = has_no_corec_info lthy fpT_name;
    val lthy1 = lthy |> no_base ? setup_base fpT_name;

    fun extract_rho lthy' =
      let
        val lthy'' = lthy' |> Variable.declare_typ fun_T;
        val (prepared as (_, _, version, Y, Z, preT, k_T, ssig_T, dead_pre_bnf, dead_k_bnf, _,
               ssig_fp_sugar, buffer), lthy''') =
          prepare_friend_corec fun_name fun_T lthy'';
        val friend_parse_info = friend_parse_info_of lthy''' arg_Ts res_T buffer;

        val parsed_eq' = parsed_eq ||> subst_atomic [(fun_free, fun_t)];
      in
        lthy'''
        |> extract_rho_return_transfer_goals b version dead_pre_bnf dead_k_bnf Y Z preT k_T ssig_T
          ssig_fp_sugar friend_parse_info fun_t parsed_eq'
        |>> pair prepared
      end;

    val ((prepareds, (rho_datas, transfer_goal_datas)), lthy2) =
      if friend then extract_rho lthy1 |>> (apfst single ##> (apfst single #> apsnd single))
      else (([], ([], [])), lthy1);

    val ((buffer, corec_infos), lthy3) =
      if friend then
        ((#13 (the_single prepareds), []), lthy2)
      else
        corec_info_of res_T lthy2
        ||> no_base ? update_coinduct_cong_intross_dynamic fpT_name
        |>> (fn info as {buffer, ...} => (buffer, [info]));

    val corec_parse_info = corec_parse_info_of lthy3 arg_Ts res_T buffer;

    val explored_eq =
      explore_corec_equation lthy3 true friend fun_name fun_free corec_parse_info res_T parsed_eq;

    val (((inner_fp_triple, termin_goals), corecUU_arg), lthy4) =
      build_corecUU_arg_and_goals (not long_cmd) fun_free explored_eq lthy3;

    fun def_fun (inner_fp_elims0, inner_fp_inducts0, inner_fp_simps0) const_transfers
        rho_transfers_foldeds lthy5 =
      let
        fun register_friend lthy' =
          let
            val [(old_corec_info, fp_b, version, Y, Z, _, k_T, _, _, dead_k_bnf, sig_fp_sugar,
                  ssig_fp_sugar, _)] = prepareds;
            val [(rho, rho_def)] = rho_datas;
            val [(_, rho_transfer_goal)] = transfer_goal_datas;
            val Type (fpT_name, _) = res_T;

            val rho_transfer_folded =
              (case rho_transfers_foldeds of
                [] =>
                derive_rho_transfer_folded lthy' fpT_name const_transfers rho_def rho_transfer_goal
              | [thm] => thm);
          in
            lthy'
            |> register_coinduct_dynamic_friend fpT_name fun_name
            |> register_friend_corec fun_name fp_b version Y Z k_T dead_k_bnf sig_fp_sugar
              ssig_fp_sugar fun_t rho rho_transfer_folded old_corec_info
          end;

        val (friend_infos, lthy6) = lthy5 |> (if friend then register_friend #>> single else pair []);
        val (corec_info as {corecUU = corecUU0, ...}, lthy7) =
          (case corec_infos of
            [] => corec_info_of res_T lthy6
          | [info] => (info, lthy6));

        val def_rhs = mk_corec_fun_def_rhs lthy7 arg_Ts corecUU0 corecUU_arg;
        val def = ((b, mx), ((Binding.concealed (Thm.def_binding b), []), def_rhs));

        val ((fun_lhs0, (_, fun_def0)), (lthy9, lthy8')) = lthy7
          |> (snd o Local_Theory.begin_nested)
          |> Local_Theory.define def
          |> tap (fn (def, lthy') => print_def_consts int [def] lthy')
          ||> `Local_Theory.end_nested;

        val parsed_eq = parse_corec_equation lthy9 [fun_free] eq;
        val views0 = generate_views lthy9 eq fun_free parsed_eq;

        val lthy9' = lthy9 |> fold Variable.declare_typ (res_T :: arg_Ts);
        val phi = Proof_Context.export_morphism lthy8' lthy9';

        val fun_lhs = Morphism.term phi fun_lhs0;
        val fun_def = Morphism.thm phi fun_def0;
        val inner_fp_elims = map (Morphism.thm phi) inner_fp_elims0;
        val inner_fp_inducts = map (Morphism.thm phi) inner_fp_inducts0;
        val inner_fp_simps = map (Morphism.thm phi) inner_fp_simps0;
        val (code_goal, _, _, _, _) = morph_views phi views0;

        fun derive_and_note_friend_extra_theorems lthy' =
          let
            val k_T = #7 (the_single prepareds);
            val rho_def = snd (the_single rho_datas);

            val (eq_algrho, algrho_eq) = derive_eq_algrho lthy' corec_info (the_single friend_infos)
              fun_lhs k_T code_goal const_transfers rho_def fun_def;

            val notes =
              (if Config.get lthy' bnf_internals then
                 [(eq_algrhoN, [eq_algrho])]
               else
                 [])
              |> map (fn (thmN, thms) =>
                ((Binding.qualify true (Binding.name_of b)
                    (Binding.qualify false friendN (Binding.name thmN)), []),
                 [(thms, [])]));
          in
            lthy'
            |> register_friend_extra fun_name eq_algrho algrho_eq
            |> Local_Theory.notes notes |> snd
          end;

        val lthy10 = lthy9 |> friend ? derive_and_note_friend_extra_theorems;

        val code_thm = derive_code lthy10 inner_fp_simps code_goal corec_info fun_lhs fun_def;
(* TODO:
        val ctr_thmss = map mk_thm (#2 views);
        val disc_thmss = map mk_thm (#3 views);
        val disc_iff_thmss = map mk_thm (#4 views);
        val sel_thmss = map mk_thm (#5 views);
*)

        val uniques =
          if null inner_fp_simps then
            [derive_unique lthy10 phi (#1 views0) corec_info fpT_name fun_def]
          else
            [];

(* TODO:
        val disc_iff_or_disc_thmss =
          map2 (fn [] => I | disc_iffs => K disc_iffs) disc_iff_thmss disc_thmss;
        val simp_thmss = map2 append disc_iff_or_disc_thmss sel_thmss;
*)

        val ((_, [{cong_intro_pairs, coinduct, coinduct_attrs}]), lthy11) = lthy10
          |> derive_and_update_coinduct_cong_intross [corec_info];
        val cong_intros_pairs = AList.group (op =) cong_intro_pairs;

        val anonymous_notes = [];
(* TODO:
          [(flat disc_iff_or_disc_thmss, simp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));
*)

        val notes =
          [(cong_introsN, maps snd cong_intros_pairs, []),
           (codeN, [code_thm], nitpicksimp_attrs),
           (coinductN, [coinduct], coinduct_attrs),
           (inner_inductN, inner_fp_inducts, []),
           (uniqueN, uniques, [])] @
           map (fn (thmN, thms) => (thmN, thms, [])) cong_intros_pairs @
          (if Config.get lthy11 bnf_internals then
             [(inner_elimN, inner_fp_elims, []),
              (inner_simpN, inner_fp_simps, [])]
           else
             [])
(* TODO:
           (ctrN, ctr_thms, []),
           (discN, disc_thms, []),
           (disc_iffN, disc_iff_thms, []),
           (selN, sel_thms, simp_attrs),
           (simpsN, simp_thms, []),
*)
          |> map (fn (thmN, thms, attrs) =>
              ((Binding.qualify true (Binding.name_of b)
                  (Binding.qualify false corecN (Binding.name thmN)), attrs),
               [(thms, [])]))
          |> filter_out (null o fst o hd o snd);
      in
        lthy11
(* TODO:
        |> Spec_Rules.add Spec_Rules.equational ([fun_lhs], flat sel_thmss)
        |> Spec_Rules.add Spec_Rules.equational ([fun_lhs], flat ctr_thmss)
*)
        |> Spec_Rules.add Binding.empty Spec_Rules.equational [fun_lhs] [code_thm]
        |> plugins code_plugin ? Code.declare_default_eqns [(code_thm, true)]
        |> Local_Theory.notes (anonymous_notes @ notes)
        |> snd
      end;

    fun prove_transfer_goal ctxt goal =
      Variable.add_free_names ctxt goal []
      |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
        HEADGOAL (Transfer.transfer_prover_tac ctxt)))
      |> Thm.close_derivation \<^here>;

    fun maybe_prove_transfer_goal ctxt goal =
      (case try (prove_transfer_goal ctxt) goal of
        SOME thm => apfst (cons thm)
      | NONE => apsnd (cons goal));

    val const_transfer_goals = fold (union (op aconv) o fst) transfer_goal_datas [];
    val (const_transfers, const_transfer_goals') =
      if long_cmd then ([], const_transfer_goals)
      else fold (maybe_prove_transfer_goal lthy4) const_transfer_goals ([], []);
  in
    ((def_fun, (([res_T], prepareds, rho_datas, map snd transfer_goal_datas),
        (inner_fp_triple, termin_goals), (const_transfers, const_transfer_goals'))), lthy4)
  end;

fun corec_cmd int opts (raw_fixes, raw_eq) lthy =
  let
    val ((def_fun, (_, (inner_fp_triple, termin_goals), (const_transfers, const_transfer_goals))),
         lthy') =
      prepare_corec_ursive_cmd int false opts (raw_fixes, raw_eq) lthy;
  in
    if not (null termin_goals) then
      error ("Termination prover failed (try " ^ quote (#1 \<^command_keyword>\<open>corecursive\<close>) ^
        " instead of " ^ quote (#1 \<^command_keyword>\<open>corec\<close>) ^ ")")
    else if not (null const_transfer_goals) then
      error ("Transfer prover failed (try " ^ quote (#1 \<^command_keyword>\<open>corecursive\<close>) ^
        " instead of " ^ quote (#1 \<^command_keyword>\<open>corec\<close>) ^ ")")
    else
      def_fun inner_fp_triple const_transfers [] lthy'
  end;

fun corecursive_cmd int opts (raw_fixes, raw_eq) lthy =
  let
    val ((def_fun, (([Type (fpT_name, _)], prepareds, rho_datas, rho_transfer_goals),
            (inner_fp_triple, termin_goals), (const_transfers, const_transfer_goals))), lthy') =
      prepare_corec_ursive_cmd int true opts (raw_fixes, raw_eq) lthy;

    val (rho_transfer_goals', unprime_rho_transfer_and_folds) =
      @{map 3} (fn (_, _, _, _, _, _, _, _, _, _, _, _, _) => fn (_, rho_def) =>
          prime_rho_transfer_goal lthy' fpT_name rho_def)
        prepareds rho_datas rho_transfer_goals
      |> split_list;
  in
    Proof.theorem NONE (fn [termin_thms, const_transfers', rho_transfers'] =>
      let
        val remove_domain_condition =
          full_simplify (put_simpset HOL_basic_ss lthy'
            addsimps (@{thm True_implies_equals} :: termin_thms));
      in
        def_fun (@{apply 3} (map remove_domain_condition) inner_fp_triple)
          (const_transfers @ const_transfers')
          (map2 (fn f => f) unprime_rho_transfer_and_folds rho_transfers')
      end)
      (map (map (rpair [])) [termin_goals, const_transfer_goals, rho_transfer_goals']) lthy'
  end;

fun friend_of_corec_cmd ((raw_fun_name, raw_fun_T_opt), raw_eq) lthy =
  let
    val Const (fun_name, _) =
      Proof_Context.read_const {proper = true, strict = false} lthy raw_fun_name;

    val fake_lthy = lthy
      |> (case raw_fun_T_opt of
           SOME raw_T =>
           Proof_Context.add_const_constraint (fun_name, SOME (Syntax.read_typ lthy raw_T))
         | NONE => I)
      handle TYPE (s, _, _) => error s;

    val fun_b = Binding.name (Long_Name.base_name fun_name);
    val code_goal = Syntax.read_prop fake_lthy raw_eq;

    val fun_T =
      (case code_goal of
        \<^Const_>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t $ _) => fastype_of (head_of t)
      | _ => ill_formed_equation_lhs_rhs lthy [code_goal]);
    val fun_t = Const (fun_name, fun_T);

    val (arg_Ts, res_T as Type (fpT_name, _)) = strip_type fun_T;

    val no_base = has_no_corec_info lthy fpT_name;
    val lthy1 = lthy |> no_base ? setup_base fpT_name;

    val lthy2 = lthy1 |> Variable.declare_typ fun_T;
    val ((old_corec_info, fp_b, version, Y, Z, preT, k_T, ssig_T, dead_pre_bnf, dead_k_bnf,
          sig_fp_sugar, ssig_fp_sugar, buffer), lthy3) =
      prepare_friend_corec fun_name fun_T lthy2;
    val friend_parse_info = friend_parse_info_of lthy3 arg_Ts res_T buffer;

    val parsed_eq = parse_corec_equation lthy3 [] code_goal;

    val (((rho, rho_def), (const_transfer_goals, rho_transfer_goal)), lthy4) =
      extract_rho_return_transfer_goals fun_b version dead_pre_bnf dead_k_bnf Y Z preT k_T ssig_T
        ssig_fp_sugar friend_parse_info fun_t parsed_eq lthy3;

    fun register_friend_extra_and_note_thms code_goal code_thm const_transfers k_T friend_info
        lthy5 =
      let
        val (corec_info, lthy6) = corec_info_of res_T lthy5;

        val fun_free = Free (Binding.name_of fun_b, fun_T);

        fun freeze_fun (t as Const (s, T)) = if s = fun_name andalso T = fun_T then fun_free else t
          | freeze_fun t = t;

        val eq = Term.map_aterms freeze_fun code_goal;
        val parsed_eq = parse_corec_equation lthy6 [fun_free] eq;

        val corec_parse_info = corec_parse_info_of lthy6 arg_Ts res_T buffer;
        val explored_eq = explore_corec_equation lthy6 false false fun_name fun_free corec_parse_info
          res_T parsed_eq;

        val ((_, corecUU_arg), _) = build_corecUU_arg_and_goals false fun_free explored_eq lthy6;

        val eq_corecUU = derive_eq_corecUU lthy6 corec_info fun_t corecUU_arg code_thm;
        val (eq_algrho, algrho_eq) = derive_eq_algrho lthy6 corec_info friend_info fun_t k_T
          code_goal const_transfers rho_def eq_corecUU;

        val ((_, [{cong_intro_pairs, coinduct, coinduct_attrs}]), lthy7) = lthy6
          |> register_friend_extra fun_name eq_algrho algrho_eq
          |> register_coinduct_dynamic_friend fpT_name fun_name
          |> derive_and_update_coinduct_cong_intross [corec_info];
        val cong_intros_pairs = AList.group (op =) cong_intro_pairs;

        val unique = derive_unique lthy7 Morphism.identity code_goal corec_info fpT_name eq_corecUU;

        val notes =
          [(codeN, [code_thm], []),
           (coinductN, [coinduct], coinduct_attrs),
           (cong_introsN, maps snd cong_intros_pairs, []),
           (uniqueN, [unique], [])] @
           map (fn (thmN, thms) => (thmN, thms, [])) cong_intros_pairs @
          (if Config.get lthy7 bnf_internals then
             [(eq_algrhoN, [eq_algrho], []),
              (eq_corecUUN, [eq_corecUU], [])]
           else
             [])
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true (Binding.name_of fun_b)
                (Binding.qualify false friendN (Binding.name thmN)), attrs),
             [(thms, [])]));
      in
        lthy7
        |> Local_Theory.notes notes |> snd
      end;

    val (rho_transfer_goal', unprime_rho_transfer_and_fold) =
      prime_rho_transfer_goal lthy4 fpT_name rho_def rho_transfer_goal;
  in
    lthy4
    |> Proof.theorem NONE (fn [[code_thm], const_transfers, [rho_transfer']] =>
        register_friend_corec fun_name fp_b version Y Z k_T dead_k_bnf sig_fp_sugar ssig_fp_sugar
          fun_t rho (unprime_rho_transfer_and_fold rho_transfer') old_corec_info
        #-> register_friend_extra_and_note_thms code_goal code_thm const_transfers k_T)
      (map (map (rpair [])) [[code_goal], const_transfer_goals, [rho_transfer_goal']])
    |> Proof.refine_singleton (Method.primitive_text (K I))
  end;

fun coinduction_upto_cmd (base_name, raw_fpT) lthy =
  let
    val fpT as Type (fpT_name, _) = Syntax.read_typ lthy raw_fpT;

    val no_base = has_no_corec_info lthy fpT_name;

    val (corec_info as {version, ...}, lthy1) = lthy
      |> corec_info_of fpT;
    val lthy2 = lthy1 |> no_base ? setup_base fpT_name;

    val ((changed, [{cong_intro_pairs, coinduct, coinduct_attrs}]), lthy3) = lthy2
      |> derive_and_update_coinduct_cong_intross [corec_info];
    val lthy4 = lthy3 |> (changed orelse no_base) ? update_coinduct_cong_intross_dynamic fpT_name;
    val cong_intros_pairs = AList.group (op =) cong_intro_pairs;

    val notes =
      [(cong_introsN, maps snd cong_intros_pairs, []),
       (coinduct_uptoN, [coinduct], coinduct_attrs)] @
      map (fn (thmN, thms) => (thmN, thms, [])) cong_intros_pairs
      |> map (fn (thmN, thms, attrs) =>
        (((Binding.qualify true base_name
            (Binding.qualify false ("v" ^ string_of_int version) (Binding.name thmN))), attrs),
         [(thms, [])]));
  in
    lthy4 |> Local_Theory.notes notes |> snd
  end;

fun consolidate lthy =
  let
    val corec_infoss = map (corec_infos_of lthy o fst) (all_codatatype_extras_of lthy);
    val (changeds, lthy') = lthy
      |> fold_map (apfst fst oo derive_and_update_coinduct_cong_intross) corec_infoss;
  in
    if exists I changeds then lthy' else raise Same.SAME
  end;

fun consolidate_global thy =
  SOME (Named_Target.theory_map consolidate thy)
  handle Same.SAME => NONE;

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>corec\<close>
  "define nonprimitive corecursive functions"
  ((Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 corec_option_parser)
      --| \<^keyword>\<open>)\<close>) []) -- (Parse.vars --| Parse.where_ -- Parse.prop)
   >> uncurry (corec_cmd true));

val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>corecursive\<close>
  "define nonprimitive corecursive functions"
  ((Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 corec_option_parser)
      --| \<^keyword>\<open>)\<close>) []) -- (Parse.vars --| Parse.where_ -- Parse.prop)
   >> uncurry (corecursive_cmd true));

val _ = Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>friend_of_corec\<close>
  "register a function as a legal context for nonprimitive corecursion"
  (Parse.const -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.typ) --| Parse.where_ -- Parse.prop
   >> friend_of_corec_cmd);

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>coinduction_upto\<close>
  "derive a coinduction up-to principle and a corresponding congruence closure"
  (Parse.name --| \<^keyword>\<open>:\<close> -- Parse.typ >> coinduction_upto_cmd);

val _ = Theory.setup (Theory.at_begin consolidate_global);

end;
