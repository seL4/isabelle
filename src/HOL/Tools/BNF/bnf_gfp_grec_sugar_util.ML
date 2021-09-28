(*  Title:      HOL/Tools/BNF/bnf_gfp_grec_sugar_util.ML
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Library for generalized corecursor sugar.
*)

signature BNF_GFP_GREC_SUGAR_UTIL =
sig
  type s_parse_info =
    {outer_buffer: BNF_GFP_Grec.buffer,
     ctr_guards: term Symtab.table,
     inner_buffer: BNF_GFP_Grec.buffer}

  type rho_parse_info =
    {pattern_ctrs: (term * term list) Symtab.table,
     discs: term Symtab.table,
     sels: term Symtab.table,
     it: term,
     mk_case: typ -> term}

  exception UNNATURAL of unit

  val generalize_types: int -> typ -> typ -> typ
  val mk_curry_uncurryN_balanced: Proof.context -> int -> thm
  val mk_const_transfer_goal: Proof.context -> string * typ -> term
  val mk_abs_transfer: Proof.context -> string -> thm
  val mk_rep_transfer: Proof.context -> string -> thm
  val mk_pointful_natural_from_transfer: Proof.context -> thm -> thm

  val corec_parse_info_of: Proof.context -> typ list -> typ -> BNF_GFP_Grec.buffer -> s_parse_info
  val friend_parse_info_of: Proof.context -> typ list -> typ -> BNF_GFP_Grec.buffer ->
    s_parse_info * rho_parse_info
end;

structure BNF_GFP_Grec_Sugar_Util : BNF_GFP_GREC_SUGAR_UTIL =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Tactics
open BNF_Def
open BNF_Comp
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_GFP_Grec
open BNF_GFP_Grec_Tactics

val mk_case_sumN_balanced = Balanced_Tree.make mk_case_sum;

fun generalize_types max_j T U =
  let
    val vars = Unsynchronized.ref [];

    fun var_of T U =
      (case AList.lookup (op =) (!vars) (T, U) of
        SOME V => V
      | NONE =>
        let val V = TVar ((Name.aT, length (!vars) + max_j), \<^sort>\<open>type\<close>) in
          vars := ((T, U), V) :: !vars; V
        end);

    fun gen (T as Type (s, Ts)) (U as Type (s', Us)) =
        if s = s' then Type (s, map2 gen Ts Us) else var_of T U
      | gen T U = if T = U then T else var_of T U;
  in
    gen T U
  end;

fun mk_curry_uncurryN_balanced_raw ctxt n =
  let
    val ((As, B), names_ctxt) = ctxt
      |> mk_TFrees (n + 1)
      |>> split_last;

    val tupled_As = mk_tupleT_balanced As;

    val f_T = As ---> B;
    val g_T = tupled_As --> B;

    val (((f, g), xs), _) = names_ctxt
      |> yield_singleton (mk_Frees "f") f_T
      ||>> yield_singleton (mk_Frees "g") g_T
      ||>> mk_Frees "x" As;

    val tupled_xs = mk_tuple1_balanced As xs;

    val uncurried_f = mk_tupled_fun f tupled_xs xs;
    val curried_g = abs_curried_balanced As g;

    val lhs = HOLogic.mk_eq (uncurried_f, g);
    val rhs =  HOLogic.mk_eq (f, curried_g);
    val goal = fold_rev Logic.all [f, g] (mk_Trueprop_eq (lhs, rhs));

    fun mk_tac ctxt =
      HEADGOAL (rtac ctxt iffI THEN' dtac ctxt sym THEN' hyp_subst_tac ctxt) THEN
      unfold_thms_tac ctxt @{thms prod.case} THEN
      HEADGOAL (rtac ctxt refl THEN' hyp_subst_tac ctxt THEN'
        REPEAT_DETERM o subst_tac ctxt NONE @{thms unit_abs_eta_conv case_prod_eta} THEN'
        rtac ctxt refl);
  in
    Goal.prove_sorry ctxt [] [] goal (fn {context = ctxt, ...} => mk_tac ctxt)
    |> Thm.close_derivation \<^here>
  end;

val num_curry_uncurryN_balanced_precomp = 8;
val curry_uncurryN_balanced_precomp =
  map (mk_curry_uncurryN_balanced_raw \<^context>) (0 upto num_curry_uncurryN_balanced_precomp);

fun mk_curry_uncurryN_balanced ctxt n =
  if n <= num_curry_uncurryN_balanced_precomp then nth curry_uncurryN_balanced_precomp n
  else mk_curry_uncurryN_balanced_raw ctxt n;

fun mk_const_transfer_goal ctxt (s, var_T) =
  let
    val var_As = Term.add_tvarsT var_T [];

    val ((As, Bs), names_ctxt) = ctxt
      |> Variable.declare_typ var_T
      |> mk_TFrees' (map snd var_As)
      ||>> mk_TFrees' (map snd var_As);

    val (Rs, _) = names_ctxt
      |> mk_Frees "R" (map2 mk_pred2T As Bs);

    val T = Term.typ_subst_TVars (map fst var_As ~~ As) var_T;
    val U = Term.typ_subst_TVars (map fst var_As ~~ Bs) var_T;
  in
    mk_parametricity_goal ctxt Rs (Const (s, T)) (Const (s, U))
    |> tap (fn goal => can type_of goal orelse
      error ("Cannot transfer constant " ^ quote (Syntax.string_of_term ctxt (Const (s, T))) ^
        " from type " ^ quote (Syntax.string_of_typ ctxt T) ^ " to " ^
        quote (Syntax.string_of_typ ctxt U)))
  end;

fun mk_abs_transfer ctxt fpT_name =
  let
    val SOME {pre_bnf, absT_info = {absT, repT, abs, type_definition, ...}, ...} =
      fp_sugar_of ctxt fpT_name;
  in
    if absT = repT then
      raise Fail "no abs/rep"
    else
      let
        val rel_def = rel_def_of_bnf pre_bnf;

        val absT = T_of_bnf pre_bnf
          |> singleton (freeze_types ctxt (map dest_TVar (lives_of_bnf pre_bnf)));

        val goal = mk_const_transfer_goal ctxt (dest_Const (mk_abs absT abs))
      in
        Variable.add_free_names ctxt goal []
        |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
          unfold_thms_tac ctxt [rel_def] THEN
          HEADGOAL (rtac ctxt refl ORELSE'
            rtac ctxt (@{thm Abs_transfer} OF [type_definition, type_definition]))))
      end
  end;

fun mk_rep_transfer ctxt fpT_name =
  let
    val SOME {pre_bnf, absT_info = {absT, repT, rep, ...}, ...} = fp_sugar_of ctxt fpT_name;
  in
    if absT = repT then
      raise Fail "no abs/rep"
    else
      let
        val rel_def = rel_def_of_bnf pre_bnf;

        val absT = T_of_bnf pre_bnf
          |> singleton (freeze_types ctxt (map dest_TVar (lives_of_bnf pre_bnf)));

        val goal = mk_const_transfer_goal ctxt (dest_Const (mk_rep absT rep))
      in
        Variable.add_free_names ctxt goal []
        |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
          unfold_thms_tac ctxt [rel_def] THEN
          HEADGOAL (rtac ctxt refl ORELSE' rtac ctxt @{thm vimage2p_rel_fun})))
      end
  end;

exception UNNATURAL of unit;

fun mk_pointful_natural_from_transfer ctxt transfer =
  let
    val _ $ (_ $ Const (s, T0) $ Const (_, U0)) = Thm.prop_of transfer;
    val [T, U] = freeze_types ctxt [] [T0, U0];
    val var_T = generalize_types 0 T U;

    val var_As = map TVar (rev (Term.add_tvarsT var_T []));

    val ((As, Bs), names_ctxt) = ctxt
      |> mk_TFrees' (map Type.sort_of_atyp var_As)
      ||>> mk_TFrees' (map Type.sort_of_atyp var_As);

    val TA = typ_subst_atomic (var_As ~~ As) var_T;

    val ((xs, fs), _) = names_ctxt
      |> mk_Frees "x" (binder_types TA)
      ||>> mk_Frees "f" (map2 (curry (op -->)) As Bs);

    val AB_fs = (As ~~ Bs) ~~ fs;

    fun build_applied_map TU t =
      if op = TU then
        t
      else
        (case try (build_map ctxt [] [] (the o AList.lookup (op =) AB_fs)) TU of
          SOME mapx => mapx $ t
        | NONE => raise UNNATURAL ());

    fun unextensionalize (f $ (x as Free _), rhs) = unextensionalize (f, lambda x rhs)
      | unextensionalize tu = tu;

    val TB = typ_subst_atomic (var_As ~~ Bs) var_T;

    val (binder_TAs, body_TA) = strip_type TA;
    val (binder_TBs, body_TB) = strip_type TB;

    val n = length var_As;
    val m = length binder_TAs;

    val A_nesting_bnfs = nesting_bnfs ctxt [[body_TA :: binder_TAs]] As;
    val A_nesting_map_ids = map map_id_of_bnf A_nesting_bnfs;
    val A_nesting_rel_Grps = map rel_Grp_of_bnf A_nesting_bnfs;

    val ta = Const (s, TA);
    val tb = Const (s, TB);
    val xfs = @{map 3} (curry build_applied_map) binder_TAs binder_TBs xs;

    val goal = (list_comb (tb, xfs), build_applied_map (body_TA, body_TB) (list_comb (ta, xs)))
      |> unextensionalize |> mk_Trueprop_eq;

    val _ = if can type_of goal then () else raise UNNATURAL ();

    val vars = map (fst o dest_Free) (xs @ fs);
  in
    Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_natural_from_transfer_tac ctxt m (replicate n true) transfer A_nesting_map_ids
        A_nesting_rel_Grps [])
    |> Thm.close_derivation \<^here>
  end;

type s_parse_info =
  {outer_buffer: BNF_GFP_Grec.buffer,
   ctr_guards: term Symtab.table,
   inner_buffer: BNF_GFP_Grec.buffer};

type rho_parse_info =
  {pattern_ctrs: (term * term list) Symtab.table,
   discs: term Symtab.table,
   sels: term Symtab.table,
   it: term,
   mk_case: typ -> term};

fun curry_friend (T, t) =
  let
    val prod_T = domain_type (fastype_of t);
    val Ts = dest_tupleT_balanced (num_binder_types T) prod_T;
    val xs = map_index (fn (i, T) => Free ("x" ^ string_of_int i, T)) Ts;
    val body = mk_tuple_balanced xs;
  in
    (T, fold_rev Term.lambda xs (t $ body))
  end;

fun curry_friends ({Oper, VLeaf, CLeaf, ctr_wrapper, friends} : buffer) =
  {Oper = Oper, VLeaf = VLeaf, CLeaf = CLeaf, ctr_wrapper = ctr_wrapper,
   friends = Symtab.map (K curry_friend) friends};

fun checked_gfp_sugar_of lthy (T as Type (T_name, _)) =
    (case fp_sugar_of lthy T_name of
      SOME (sugar as {fp = Greatest_FP, ...}) => sugar
    | _ => not_codatatype lthy T)
  | checked_gfp_sugar_of lthy T = not_codatatype lthy T;

fun generic_spec_of friend ctxt arg_Ts res_T (raw_buffer0 as {VLeaf = VLeaf0, ...}) =
  let
    val thy = Proof_Context.theory_of ctxt;

    val tupled_arg_T = mk_tupleT_balanced arg_Ts;

    val {T = fpT, X, fp_res_index, fp_res = {ctors = ctors0, ...},
         absT_info = {abs = abs0, rep = rep0, ...},
         fp_ctr_sugar = {ctrXs_Tss, ctr_sugar = {ctrs = ctrs0, casex = case0, discs = discs0,
           selss = selss0, sel_defs, ...}, ...}, ...} =
      checked_gfp_sugar_of ctxt res_T;

    val VLeaf0_T = fastype_of VLeaf0;
    val Y = domain_type VLeaf0_T;

    val raw_buffer = specialize_buffer_types raw_buffer0;

    val As_rho = tvar_subst thy [fpT] [res_T];

    val substAT = Term.typ_subst_TVars As_rho;
    val substA = Term.subst_TVars As_rho;
    val substYT = Tsubst Y tupled_arg_T;
    val substY = substT Y tupled_arg_T;

    val Ys_rho_inner = if friend then [] else [(Y, tupled_arg_T)];
    val substYT_inner = substAT o Term.typ_subst_atomic Ys_rho_inner;
    val substY_inner = substA o Term.subst_atomic_types Ys_rho_inner;

    val mid_T = substYT_inner (range_type VLeaf0_T);

    val substXT_mid = Tsubst X mid_T;

    val XifyT = typ_subst_nonatomic [(res_T, X)];
    val YifyT = typ_subst_nonatomic [(res_T, Y)];

    val substXYT = Tsubst X Y;

    val ctor0 = nth ctors0 fp_res_index;
    val ctor = enforce_type ctxt range_type res_T ctor0;
    val preT = YifyT (domain_type (fastype_of ctor));

    val n = length ctrs0;
    val ks = 1 upto n;

    fun mk_ctr_guards () =
      let
        val ctr_Tss = map (map (substXT_mid o substAT)) ctrXs_Tss;
        val preT = XifyT (domain_type (fastype_of ctor));
        val mid_preT = substXT_mid preT;
        val abs = enforce_type ctxt range_type mid_preT abs0;
        val absT = range_type (fastype_of abs);

        fun mk_ctr_guard k ctr_Ts (Const (s, _)) =
          let
            val xs = map_index (fn (i, T) => Free ("x" ^ string_of_int i, T)) ctr_Ts;
            val body = mk_absumprod absT abs n k xs;
          in
            (s, fold_rev Term.lambda xs body)
          end;
      in
        Symtab.make (@{map 3} mk_ctr_guard ks ctr_Tss ctrs0)
      end;

    val substYT_mid = substYT o Tsubst Y mid_T;

    val outer_T = substYT_mid preT;

    val substY_outer = substY o substT Y outer_T;

    val outer_buffer = curry_friends (map_buffer substY_outer raw_buffer);
    val ctr_guards = mk_ctr_guards ();
    val inner_buffer = curry_friends (map_buffer substY_inner raw_buffer);

    val s_parse_info =
      {outer_buffer = outer_buffer, ctr_guards = ctr_guards, inner_buffer = inner_buffer};

    fun mk_friend_spec () =
      let
        fun encapsulate_nested U T free =
          betapply (build_map ctxt [] [] (fn (T, _) =>
              if T = domain_type VLeaf0_T then Abs (Name.uu, T, VLeaf0 $ Bound 0)
              else Abs (Name.uu, T, Bound 0)) (T, U),
            free);

        val preT = YifyT (domain_type (fastype_of ctor));
        val YpreT = HOLogic.mk_prodT (Y, preT);

        val rep = rep0 |> enforce_type ctxt domain_type (substXT_mid (XifyT preT));

        fun mk_disc k =
          ctrXs_Tss
          |> map_index (fn (i, Ts) =>
            Abs (Name.uu, mk_tupleT_balanced Ts,
              if i + 1 = k then \<^Const>\<open>True\<close> else \<^Const>\<open>False\<close>))
          |> mk_case_sumN_balanced
          |> map_types substXYT
          |> (fn tm => Library.foldl1 HOLogic.mk_comp [tm, rep, snd_const YpreT])
          |> map_types substAT;

        val all_discs = map mk_disc ks;

        fun mk_pair (Const (disc_name, _)) disc = SOME (disc_name, disc)
          | mk_pair _ _ = NONE;

        val discs = @{map 2} mk_pair discs0 all_discs
          |> map_filter I |> Symtab.make;

        fun mk_sel sel_def =
          let
            val (sel_name, case_functions) =
              sel_def
              |> Object_Logic.rulify ctxt
              |> Thm.concl_of
              |> perhaps (try drop_all)
              |> perhaps (try HOLogic.dest_Trueprop)
              |> HOLogic.dest_eq
              |>> fst o strip_comb
              |>> fst o dest_Const
              ||> fst o dest_comb
              ||> snd o strip_comb
              ||> map (map_types (XifyT o substAT));

            fun encapsulate_case_function case_function =
              let
                fun encapsulate bound_Ts [] case_function =
                    let val T = fastype_of1 (bound_Ts, case_function) in
                      encapsulate_nested (substXT_mid T) (substXYT T) case_function
                    end
                  | encapsulate bound_Ts (T :: Ts) case_function =
                    Abs (Name.uu, T,
                      encapsulate (T :: bound_Ts) Ts
                        (betapply (incr_boundvars 1 case_function, Bound 0)));
              in
                encapsulate [] (binder_types (fastype_of case_function)) case_function
              end;
          in
            (sel_name, ctrXs_Tss
              |> map (map_index (fn (i, T) => Free ("x" ^ string_of_int (i + 1), T)))
              |> `(map mk_tuple_balanced)
              |> uncurry (@{map 3} mk_tupled_fun (map encapsulate_case_function case_functions))
              |> mk_case_sumN_balanced
              |> map_types substXYT
              |> (fn tm => Library.foldl1 HOLogic.mk_comp [tm, rep, snd_const YpreT])
              |> map_types substAT)
          end;

        val sels = Symtab.make (map mk_sel sel_defs);

        fun mk_disc_sels_pair disc sels =
          if forall is_some sels then SOME (disc, map the sels) else NONE;

        val pattern_ctrs = (ctrs0, selss0)
          ||> map (map (try dest_Const #> Option.mapPartial (fst #> Symtab.lookup sels)))
          ||> @{map 2} mk_disc_sels_pair all_discs
          |>> map (dest_Const #> fst)
          |> op ~~
          |> map_filter (fn (s, opt) => if is_some opt then SOME (s, the opt) else NONE)
          |> Symtab.make;

        val it = HOLogic.mk_comp (VLeaf0, fst_const YpreT);

        val mk_case =
          let
            val abs_fun_tms = case0
              |> fastype_of
              |> substAT
              |> XifyT
              |> binder_fun_types
              |> map_index (fn (i, T) => Free ("f" ^ string_of_int (i + 1), T));
            val arg_Uss = abs_fun_tms
              |> map fastype_of
              |> map binder_types;
            val arg_Tss = arg_Uss
              |> map (map substXYT);
            val case0 =
              arg_Tss
              |> map (map_index (fn (i, T) => Free ("x" ^ string_of_int (i + 1), T)))
              |> `(map mk_tuple_balanced)
              ||> @{map 3} (@{map 3} encapsulate_nested) arg_Uss arg_Tss
              |> uncurry (@{map 3} mk_tupled_fun abs_fun_tms)
              |> mk_case_sumN_balanced
              |> (fn tm => Library.foldl1 HOLogic.mk_comp [tm, rep, snd_const YpreT])
              |> fold_rev lambda abs_fun_tms
              |> map_types (substAT o substXT_mid);
          in
            fn U => case0
              |> substT (body_type (fastype_of case0)) U
              |> Syntax.check_term ctxt
          end;
      in
        {pattern_ctrs = pattern_ctrs, discs = discs, sels = sels, it = it, mk_case = mk_case}
      end;
  in
    (s_parse_info, mk_friend_spec)
  end;

fun corec_parse_info_of ctxt =
  fst ooo generic_spec_of false ctxt;

fun friend_parse_info_of ctxt =
  apsnd (fn f => f ()) ooo generic_spec_of true ctxt;

end;
