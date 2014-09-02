(*  Title:      HOL/Tools/BNF/bnf_gfp_rec_sugar.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Corecursor sugar ("primcorec" and "primcorecursive").
*)

signature BNF_GFP_REC_SUGAR =
sig
  datatype primcorec_option = Sequential_Option | Exhaustive_Option

  val add_primcorecursive_cmd: primcorec_option list ->
    (binding * string option * mixfix) list * ((Attrib.binding * string) * string option) list ->
    Proof.context -> Proof.state
  val add_primcorec_cmd: primcorec_option list ->
    (binding * string option * mixfix) list * ((Attrib.binding * string) * string option) list ->
    local_theory -> local_theory
end;

structure BNF_GFP_Rec_Sugar : BNF_GFP_REC_SUGAR =
struct

open Ctr_Sugar_General_Tactics
open Ctr_Sugar
open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar
open BNF_FP_Rec_Sugar_Util
open BNF_GFP_Rec_Sugar_Tactics

val codeN = "code"
val ctrN = "ctr"
val discN = "disc"
val disc_iffN = "disc_iff"
val excludeN = "exclude"
val selN = "sel"

val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};
val code_nitpicksimp_attrs = Code.add_default_eqn_attrib :: nitpicksimp_attrs;

exception PRIMCOREC of string * term list;

fun primcorec_error str = raise PRIMCOREC (str, []);
fun primcorec_error_eqn str eqn = raise PRIMCOREC (str, [eqn]);
fun primcorec_error_eqns str eqns = raise PRIMCOREC (str, eqns);

datatype primcorec_option = Sequential_Option | Exhaustive_Option;

datatype corec_call =
  Dummy_No_Corec of int |
  No_Corec of int |
  Mutual_Corec of int * int * int |
  Nested_Corec of int;

type basic_corec_ctr_spec =
  {ctr: term,
   disc: term,
   sels: term list};

type corec_ctr_spec =
  {ctr: term,
   disc: term,
   sels: term list,
   pred: int option,
   calls: corec_call list,
   discI: thm,
   sel_thms: thm list,
   distinct_discss: thm list list,
   collapse: thm,
   corec_thm: thm,
   corec_disc: thm,
   corec_sels: thm list};

type corec_spec =
  {corec: term,
   exhaust_discs: thm list,
   sel_defs: thm list,
   fp_nesting_maps: thm list,
   fp_nesting_map_ident0s: thm list,
   fp_nesting_map_comps: thm list,
   ctr_specs: corec_ctr_spec list};

exception NOT_A_MAP of term;

fun not_codatatype ctxt T =
  error ("Not a codatatype: " ^ Syntax.string_of_typ ctxt T);
fun ill_formed_corec_call ctxt t =
  error ("Ill-formed corecursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun invalid_map ctxt t =
  error ("Invalid map function in " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_corec_call ctxt t =
  error ("Unexpected corecursive call: " ^ quote (Syntax.string_of_term ctxt t));

fun sort_list_duplicates xs = map snd (sort (int_ord o pairself fst) xs);

val mk_conjs = try (foldr1 HOLogic.mk_conj) #> the_default @{const True};
val mk_disjs = try (foldr1 HOLogic.mk_disj) #> the_default @{const False};
val mk_dnf = mk_disjs o map mk_conjs;

val conjuncts_s = filter_out (curry (op aconv) @{const True}) o HOLogic.conjuncts;

fun s_not @{const True} = @{const False}
  | s_not @{const False} = @{const True}
  | s_not (@{const Not} $ t) = t
  | s_not (@{const conj} $ t $ u) = @{const disj} $ s_not t $ s_not u
  | s_not (@{const disj} $ t $ u) = @{const conj} $ s_not t $ s_not u
  | s_not t = @{const Not} $ t;

val s_not_conj = conjuncts_s o s_not o mk_conjs;

fun propagate_unit_pos u cs = if member (op aconv) cs u then [@{const False}] else cs;

fun propagate_unit_neg not_u cs = remove (op aconv) not_u cs;

fun propagate_units css =
  (case List.partition (can the_single) css of
     ([], _) => css
   | ([u] :: uss, css') =>
     [u] :: propagate_units (map (propagate_unit_neg (s_not u))
       (map (propagate_unit_pos u) (uss @ css'))));

fun s_conjs cs =
  if member (op aconv) cs @{const False} then @{const False}
  else mk_conjs (remove (op aconv) @{const True} cs);

fun s_disjs ds =
  if member (op aconv) ds @{const True} then @{const True}
  else mk_disjs (remove (op aconv) @{const False} ds);

fun s_dnf css0 =
  let val css = propagate_units css0 in
    if null css then
      [@{const False}]
    else if exists null css then
      []
    else
      map (fn c :: cs => (c, cs)) css
      |> AList.coalesce (op =)
      |> map (fn (c, css) => c :: s_dnf css)
      |> (fn [cs] => cs | css => [s_disjs (map s_conjs css)])
  end;

fun fold_rev_let_if_case ctxt f bound_Ts =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun fld conds t =
      (case Term.strip_comb t of
        (Const (@{const_name Let}, _), [_, _]) => fld conds (unfold_lets_splits t)
      | (Const (@{const_name If}, _), [cond, then_branch, else_branch]) =>
        fld (conds @ conjuncts_s cond) then_branch o fld (conds @ s_not_conj [cond]) else_branch
      | (Const (c, _), args as _ :: _ :: _) =>
        let val n = num_binder_types (Sign.the_const_type thy c) - 1 in
          if n >= 0 andalso n < length args then
            (case fastype_of1 (bound_Ts, nth args n) of
              Type (s, Ts) =>
              (case dest_case ctxt s Ts t of
                SOME ({split_sels = _ :: _, ...}, conds', branches) =>
                fold_rev (uncurry fld) (map (append conds o conjuncts_s) conds' ~~ branches)
              | _ => f conds t)
            | _ => f conds t)
          else
            f conds t
        end
      | _ => f conds t);
  in
    fld []
  end;

fun case_of ctxt s =
  (case ctr_sugar_of ctxt s of
    SOME {casex = Const (s', _), split_sels = _ :: _, ...} => SOME s'
  | _ => NONE);

fun massage_let_if_case ctxt has_call massage_leaf =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun check_no_call t = if has_call t then unexpected_corec_call ctxt t else ();

    fun massage_abs bound_Ts 0 t = massage_rec bound_Ts t
      | massage_abs bound_Ts m (Abs (s, T, t)) = Abs (s, T, massage_abs (T :: bound_Ts) (m - 1) t)
      | massage_abs bound_Ts m t =
        let val T = domain_type (fastype_of1 (bound_Ts, t)) in
          Abs (Name.uu, T, massage_abs (T :: bound_Ts) (m - 1) (incr_boundvars 1 t $ Bound 0))
        end
    and massage_rec bound_Ts t =
      let val typof = curry fastype_of1 bound_Ts in
        (case Term.strip_comb t of
          (Const (@{const_name Let}, _), [_, _]) => massage_rec bound_Ts (unfold_lets_splits t)
        | (Const (@{const_name If}, _), obj :: (branches as [_, _])) =>
          let val branches' = map (massage_rec bound_Ts) branches in
            Term.list_comb (If_const (typof (hd branches')) $ tap check_no_call obj, branches')
          end
        | (c as Const (@{const_name case_prod}, _), arg :: args) =>
          massage_rec bound_Ts
            (unfold_splits_lets (Term.list_comb (c $ Envir.eta_long bound_Ts arg, args)))
        | (Const (c, _), args as _ :: _ :: _) =>
          (case try strip_fun_type (Sign.the_const_type thy c) of
            SOME (gen_branch_Ts, gen_body_fun_T) =>
            let
              val gen_branch_ms = map num_binder_types gen_branch_Ts;
              val n = length gen_branch_ms;
            in
              if n < length args then
                (case gen_body_fun_T of
                  Type (_, [Type (T_name, _), _]) =>
                  if case_of ctxt T_name = SOME c then
                    let
                      val (branches, obj_leftovers) = chop n args;
                      val branches' = map2 (massage_abs bound_Ts) gen_branch_ms branches;
                      val branch_Ts' = map typof branches';
                      val body_T' = snd (strip_typeN (hd gen_branch_ms) (hd branch_Ts'));
                      val casex' = Const (c, branch_Ts' ---> map typof obj_leftovers ---> body_T');
                    in
                      Term.list_comb (casex',
                        branches' @ tap (List.app check_no_call) obj_leftovers)
                    end
                  else
                    massage_leaf bound_Ts t
                | _ => massage_leaf bound_Ts t)
              else
                massage_leaf bound_Ts t
            end
          | NONE => massage_leaf bound_Ts t)
        | _ => massage_leaf bound_Ts t)
      end;
  in
    massage_rec
  end;

fun curried_type (Type (@{type_name fun}, [Type (@{type_name prod}, Ts), T])) = Ts ---> T;

fun massage_nested_corec_call ctxt has_call raw_massage_call bound_Ts U t =
  let
    fun check_no_call t = if has_call t then unexpected_corec_call ctxt t else ();

    val build_map_Inl = build_map ctxt [] (uncurry Inl_const o dest_sumT o snd);

    fun massage_mutual_call bound_Ts U T t =
      if has_call t then
        (case try dest_sumT U of
          SOME (U1, U2) => if U1 = T then raw_massage_call bound_Ts T U2 t else invalid_map ctxt t
        | NONE => invalid_map ctxt t)
      else
        build_map_Inl (T, U) $ t;

    fun massage_map bound_Ts (Type (_, Us)) (Type (s, Ts)) t =
        (case try (dest_map ctxt s) t of
          SOME (map0, fs) =>
          let
            val Type (_, dom_Ts) = domain_type (fastype_of1 (bound_Ts, t));
            val map' = mk_map (length fs) dom_Ts Us map0;
            val fs' =
              map_flattened_map_args ctxt s (map3 (massage_map_or_map_arg bound_Ts) Us Ts) fs;
          in
            Term.list_comb (map', fs')
          end
        | NONE => raise NOT_A_MAP t)
      | massage_map _ _ _ t = raise NOT_A_MAP t
    and massage_map_or_map_arg bound_Ts U T t =
      if T = U then
        tap check_no_call t
      else
        massage_map bound_Ts U T t
        handle NOT_A_MAP _ => massage_mutual_fun bound_Ts U T t
    and massage_mutual_fun bound_Ts U T t =
      (case t of
        Const (@{const_name comp}, _) $ t1 $ t2 =>
        mk_comp bound_Ts (massage_mutual_fun bound_Ts U T t1, tap check_no_call t2)
      | _ =>
        let
          val var = Var ((Name.uu, Term.maxidx_of_term t + 1),
            domain_type (fastype_of1 (bound_Ts, t)));
        in
          Term.lambda var (massage_call bound_Ts U T (betapply (t, var)))
        end)
    and massage_call bound_Ts U T =
      massage_let_if_case ctxt has_call (fn bound_Ts => fn t =>
        if has_call t then
          (case U of
            Type (s, Us) =>
            (case try (dest_ctr ctxt s) t of
              SOME (f, args) =>
              let
                val typof = curry fastype_of1 bound_Ts;
                val f' = mk_ctr Us f
                val f'_T = typof f';
                val arg_Ts = map typof args;
              in
                Term.list_comb (f', map3 (massage_call bound_Ts) (binder_types f'_T) arg_Ts args)
              end
            | NONE =>
              (case t of
                Const (@{const_name case_prod}, _) $ t' =>
                let
                  val U' = curried_type U;
                  val T' = curried_type T;
                in
                  Const (@{const_name case_prod}, U' --> U) $ massage_call bound_Ts U' T' t'
                end
              | t1 $ t2 =>
                (if has_call t2 then
                  massage_mutual_call bound_Ts U T t
                else
                  massage_map bound_Ts U T t1 $ t2
                  handle NOT_A_MAP _ => massage_mutual_call bound_Ts U T t)
              | Abs (s, T', t') =>
                Abs (s, T', massage_call (T' :: bound_Ts) (range_type U) (range_type T) t')
              | _ => massage_mutual_call bound_Ts U T t))
          | _ => ill_formed_corec_call ctxt t)
        else
          build_map_Inl (T, U) $ t) bound_Ts;

    val T = fastype_of1 (bound_Ts, t);
  in
    if has_call t then massage_call bound_Ts U T t else build_map_Inl (T, U) $ t
  end;

fun expand_to_ctr_term ctxt s Ts t =
  (case ctr_sugar_of ctxt s of
    SOME {ctrs, casex, ...} =>
    Term.list_comb (mk_case Ts (Type (s, Ts)) casex, map (mk_ctr Ts) ctrs) $ t
  | NONE => raise Fail "expand_to_ctr_term");

fun expand_corec_code_rhs ctxt has_call bound_Ts t =
  (case fastype_of1 (bound_Ts, t) of
    Type (s, Ts) =>
    massage_let_if_case ctxt has_call (fn _ => fn t =>
      if can (dest_ctr ctxt s) t then t else expand_to_ctr_term ctxt s Ts t) bound_Ts t
  | _ => raise Fail "expand_corec_code_rhs");

fun massage_corec_code_rhs ctxt massage_ctr =
  massage_let_if_case ctxt (K false)
    (fn bound_Ts => uncurry (massage_ctr bound_Ts) o Term.strip_comb);

fun fold_rev_corec_code_rhs ctxt f =
  fold_rev_let_if_case ctxt (fn conds => uncurry (f conds) o Term.strip_comb);

fun case_thms_of_term ctxt t =
  let val ctr_sugars = map_filter (Ctr_Sugar.ctr_sugar_of_case ctxt o fst) (Term.add_consts t []) in
    (maps #distincts ctr_sugars, maps #discIs ctr_sugars, maps #exhaust_discs ctr_sugars,
     maps #split_sels ctr_sugars, maps #split_sel_asms ctr_sugars)
  end;

fun basic_corec_specs_of ctxt res_T =
  (case res_T of
    Type (T_name, _) =>
    (case Ctr_Sugar.ctr_sugar_of ctxt T_name of
      NONE => not_codatatype ctxt res_T
    | SOME {ctrs, discs, selss, ...} =>
      let
        val thy = Proof_Context.theory_of ctxt;

        val gfpT = body_type (fastype_of (hd ctrs));
        val As_rho = tvar_subst thy [gfpT] [res_T];
        val substA = Term.subst_TVars As_rho;

        fun mk_spec ctr disc sels = {ctr = substA ctr, disc = substA disc, sels = map substA sels};
      in
        map3 mk_spec ctrs discs selss
        handle ListPair.UnequalLengths => not_codatatype ctxt res_T
      end)
  | _ => not_codatatype ctxt res_T);

fun map_thms_of_typ ctxt (Type (s, _)) =
    (case fp_sugar_of ctxt s of SOME {maps, ...} => maps | NONE => [])
  | map_thms_of_typ _ _ = [];

fun corec_specs_of bs arg_Ts res_Ts callers callssss0 lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val ((missing_res_Ts, perm0_kks, fp_sugars as {fp_nesting_bnfs,
          common_co_inducts = common_coinduct_thms, ...} :: _, (_, gfp_sugar_thms)), lthy) =
      nested_to_mutual_fps Greatest_FP bs res_Ts callers callssss0 lthy0;

    val perm_fp_sugars = sort (int_ord o pairself #fp_res_index) fp_sugars;

    val indices = map #fp_res_index fp_sugars;
    val perm_indices = map #fp_res_index perm_fp_sugars;

    val perm_gfpTs = map #T perm_fp_sugars;
    val perm_ctrXs_Tsss' = map (repair_nullary_single_ctr o #ctrXs_Tss) perm_fp_sugars;

    val nn0 = length res_Ts;
    val nn = length perm_gfpTs;
    val kks = 0 upto nn - 1;
    val perm_ns' = map length perm_ctrXs_Tsss';

    val perm_Ts = map #T perm_fp_sugars;
    val perm_Xs = map #X perm_fp_sugars;
    val perm_Cs = map (domain_type o body_fun_type o fastype_of o #co_rec) perm_fp_sugars;
    val Xs_TCs = perm_Xs ~~ (perm_Ts ~~ perm_Cs);

    fun zip_corecT (Type (s, Us)) = [Type (s, map (mk_sumTN o zip_corecT) Us)]
      | zip_corecT U =
        (case AList.lookup (op =) Xs_TCs U of
          SOME (T, C) => [T, C]
        | NONE => [U]);

    val perm_p_Tss = mk_corec_p_pred_types perm_Cs perm_ns';
    val perm_f_Tssss =
      map2 (fn C => map (map (map (curry (op -->) C) o zip_corecT))) perm_Cs perm_ctrXs_Tsss';
    val perm_q_Tssss =
      map (map (map (fn [_] => [] | [_, T] => [mk_pred1T (domain_type T)]))) perm_f_Tssss;

    val (perm_p_hss, h) = indexedd perm_p_Tss 0;
    val (perm_q_hssss, h') = indexedddd perm_q_Tssss h;
    val (perm_f_hssss, _) = indexedddd perm_f_Tssss h';

    val fun_arg_hs =
      flat (map3 flat_corec_preds_predsss_gettersss perm_p_hss perm_q_hssss perm_f_hssss);

    fun unpermute0 perm0_xs = permute_like_unique (op =) perm0_kks kks perm0_xs;
    fun unpermute perm_xs = permute_like_unique (op =) perm_indices indices perm_xs;

    val coinduct_thmss = map (unpermute0 o conj_dests nn) common_coinduct_thms;

    val p_iss = map (map (find_index_eq fun_arg_hs)) (unpermute perm_p_hss);
    val q_issss = map (map (map (map (find_index_eq fun_arg_hs)))) (unpermute perm_q_hssss);
    val f_issss = map (map (map (map (find_index_eq fun_arg_hs)))) (unpermute perm_f_hssss);

    val f_Tssss = unpermute perm_f_Tssss;
    val gfpTs = unpermute perm_gfpTs;
    val Cs = unpermute perm_Cs;

    val As_rho = tvar_subst thy (take nn0 gfpTs) res_Ts;
    val Cs_rho = map (fst o dest_TVar) Cs ~~ pad_list HOLogic.unitT nn arg_Ts;

    val substA = Term.subst_TVars As_rho;
    val substAT = Term.typ_subst_TVars As_rho;
    val substCT = Term.typ_subst_TVars Cs_rho;

    val perm_Cs' = map substCT perm_Cs;

    fun call_of nullary [] [g_i] [Type (@{type_name fun}, [_, T])] =
        (if exists_subtype_in Cs T then Nested_Corec
         else if nullary then Dummy_No_Corec
         else No_Corec) g_i
      | call_of _ [q_i] [g_i, g_i'] _ = Mutual_Corec (q_i, g_i, g_i');

    fun mk_ctr_spec ctr disc sels p_io q_iss f_iss f_Tss discI sel_thms distinct_discss collapse
        corec_thm corec_disc corec_sels =
      let val nullary = not (can dest_funT (fastype_of ctr)) in
        {ctr = substA ctr, disc = substA disc, sels = map substA sels, pred = p_io,
         calls = map3 (call_of nullary) q_iss f_iss f_Tss, discI = discI, sel_thms = sel_thms,
         distinct_discss = distinct_discss, collapse = collapse, corec_thm = corec_thm,
         corec_disc = corec_disc, corec_sels = corec_sels}
      end;

    fun mk_ctr_specs ({ctrs, discs, selss, discIs, sel_thmss, distinct_discsss, collapses, ...}
        : ctr_sugar) p_is q_isss f_isss f_Tsss corec_thms corec_discs corec_selss =
      let val p_ios = map SOME p_is @ [NONE] in
        map14 mk_ctr_spec ctrs discs selss p_ios q_isss f_isss f_Tsss discIs sel_thmss
          distinct_discsss collapses corec_thms corec_discs corec_selss
      end;

    fun mk_spec ({T, ctr_sugar as {exhaust_discs, sel_defs, ...}, co_rec = corec,
        co_rec_thms = corec_thms, co_rec_discs = corec_discs,
        co_rec_selss = corec_selss, ...} : fp_sugar) p_is q_isss f_isss f_Tsss =
      {corec = mk_co_rec thy Greatest_FP (substAT T) perm_Cs' corec, exhaust_discs = exhaust_discs,
       sel_defs = sel_defs,
       fp_nesting_maps = maps (map_thms_of_typ lthy o T_of_bnf) fp_nesting_bnfs,
       fp_nesting_map_ident0s = map map_ident0_of_bnf fp_nesting_bnfs,
       fp_nesting_map_comps = map map_comp_of_bnf fp_nesting_bnfs,
       ctr_specs = mk_ctr_specs ctr_sugar p_is q_isss f_isss f_Tsss corec_thms corec_discs
         corec_selss};
  in
    ((is_some gfp_sugar_thms, map5 mk_spec fp_sugars p_iss q_issss f_issss f_Tssss, missing_res_Ts,
      co_induct_of common_coinduct_thms, strong_co_induct_of common_coinduct_thms,
      co_induct_of coinduct_thmss, strong_co_induct_of coinduct_thmss), lthy)
  end;

val undef_const = Const (@{const_name undefined}, dummyT);

val abs_tuple_balanced = HOLogic.tupled_lambda o mk_tuple_balanced;

fun abstract vs =
  let
    fun abs n (t $ u) = abs n t $ abs n u
      | abs n (Abs (v, T, b)) = Abs (v, T, abs (n + 1) b)
      | abs n t =
        let val j = find_index (curry (op =) t) vs in
          if j < 0 then t else Bound (n + j)
        end;
  in abs 0 end;

type coeqn_data_disc = {
  fun_name: string,
  fun_T: typ,
  fun_args: term list,
  ctr: term,
  ctr_no: int,
  disc: term,
  prems: term list,
  auto_gen: bool,
  ctr_rhs_opt: term option,
  code_rhs_opt: term option,
  eqn_pos: int,
  user_eqn: term
};

type coeqn_data_sel = {
  fun_name: string,
  fun_T: typ,
  fun_args: term list,
  ctr: term,
  sel: term,
  rhs_term: term,
  ctr_rhs_opt: term option,
  code_rhs_opt: term option,
  eqn_pos: int,
  user_eqn: term
};

datatype coeqn_data =
  Disc of coeqn_data_disc |
  Sel of coeqn_data_sel;

fun check_extra_variables lthy vars names eqn =
  let val b = fold_aterms (fn x as Free (v, _) =>
    if (not (member (op =) vars x) andalso
      not (member (op =) names v) andalso
      v <> Name.uu_ andalso
      not (Variable.is_fixed lthy v)) then cons x else I | _ => I) eqn []
  in
    null b orelse
    primcorec_error_eqn ("extra variable(s) in equation: " ^
      commas (map (Syntax.string_of_term lthy) b)) eqn
  end;

fun dissect_coeqn_disc lthy fun_names sequentials (basic_ctr_specss : basic_corec_ctr_spec list list)
    eqn_pos ctr_rhs_opt code_rhs_opt prems' concl matchedsss =
  let
    fun find_subterm p =
      let (* FIXME \<exists>? *)
        fun find (t as u $ v) = if p t then SOME t else merge_options (find u, find v)
          | find t = if p t then SOME t else NONE;
      in find end;

    val applied_fun = concl
      |> find_subterm (member (op = o apsnd SOME) fun_names o try (fst o dest_Free o head_of))
      |> the
      handle Option.Option => primcorec_error_eqn "malformed discriminator formula" concl;
    val ((fun_name, fun_T), fun_args) = strip_comb applied_fun |>> dest_Free;

    val _ = let val fixeds = filter (Variable.is_fixed lthy o fst o dest_Free) fun_args in
        null fixeds orelse primcorec_error_eqns "function argument(s) are fixed in context" fixeds
      end;

    val _ =
      let
        val bad = prems'
          |> filter (exists_subterm (fn Free (v, _) => member (op =) fun_names v | _ => false))
      in
        null bad orelse primcorec_error_eqns "corecursive call(s) in condition(s)" bad
      end;

    val _ = forall is_Free fun_args orelse
      primcorec_error_eqn ("non-variable function argument \"" ^
        Syntax.string_of_term lthy (find_first (not o is_Free) fun_args |> the) ^
          "\" (pattern matching is not supported by primcorec(ursive))") applied_fun

    val _ = let val d = duplicates (op =) fun_args in null d orelse
      primcorec_error_eqn ("duplicate variable \"" ^ Syntax.string_of_term lthy (hd d) ^ "\"")
        applied_fun end;

    val SOME (sequential, basic_ctr_specs) =
      AList.lookup (op =) (fun_names ~~ (sequentials ~~ basic_ctr_specss)) fun_name;

    val discs = map #disc basic_ctr_specs;
    val ctrs = map #ctr basic_ctr_specs;
    val not_disc = head_of concl = @{term Not};
    val _ = not_disc andalso length ctrs <> 2 andalso
      primcorec_error_eqn "negated discriminator for a type with \<noteq> 2 constructors" concl;
    val disc' = find_subterm (member (op =) discs o head_of) concl;
    val eq_ctr0 = concl |> perhaps (try HOLogic.dest_not) |> try (HOLogic.dest_eq #> snd)
        |> (fn SOME t => let val n = find_index (curry (op =) t) ctrs in
          if n >= 0 then SOME n else NONE end | _ => NONE);

    val _ = if is_some disc' andalso perhaps (try HOLogic.dest_not) concl <> the disc'
      then primcorec_error_eqn "malformed discriminator formula" concl else ();


    val _ = is_some disc' orelse is_some eq_ctr0 orelse
      primcorec_error_eqn "no discriminator in equation" concl;
    val ctr_no' =
      if is_none disc' then the eq_ctr0 else find_index (curry (op =) (head_of (the disc'))) discs;
    val ctr_no = if not_disc then 1 - ctr_no' else ctr_no';
    val {ctr, disc, ...} = nth basic_ctr_specs ctr_no;

    val catch_all = try (fst o dest_Free o the_single) prems' = SOME Name.uu_;
    val matchedss = AList.lookup (op =) matchedsss fun_name |> the_default [];
    val prems = map (abstract (List.rev fun_args)) prems';
    val actual_prems =
      (if catch_all orelse sequential then maps s_not_conj matchedss else []) @
      (if catch_all then [] else prems);

    val matchedsss' = AList.delete (op =) fun_name matchedsss
      |> cons (fun_name, if sequential then matchedss @ [prems] else matchedss @ [actual_prems]);

    val user_eqn =
      (actual_prems, concl)
      |>> map HOLogic.mk_Trueprop ||> HOLogic.mk_Trueprop o abstract (List.rev fun_args)
      |> curry Logic.list_all (map dest_Free fun_args) o Logic.list_implies;

    val _ = check_extra_variables lthy fun_args fun_names user_eqn;
  in
    (Disc {
      fun_name = fun_name,
      fun_T = fun_T,
      fun_args = fun_args,
      ctr = ctr,
      ctr_no = ctr_no,
      disc = disc,
      prems = actual_prems,
      auto_gen = catch_all,
      ctr_rhs_opt = ctr_rhs_opt,
      code_rhs_opt = code_rhs_opt,
      eqn_pos = eqn_pos,
      user_eqn = user_eqn
    }, matchedsss')
  end;

fun dissect_coeqn_sel lthy fun_names (basic_ctr_specss : basic_corec_ctr_spec list list) eqn_pos
    ctr_rhs_opt code_rhs_opt eqn0 of_spec_opt eqn =
  let
    val (lhs, rhs) = HOLogic.dest_eq eqn
      handle TERM _ =>
             primcorec_error_eqn "malformed function equation (expected \"lhs = rhs\")" eqn;
    val sel = head_of lhs;
    val ((fun_name, fun_T), fun_args) = dest_comb lhs |> snd |> strip_comb |> apfst dest_Free
      handle TERM _ =>
             primcorec_error_eqn "malformed selector argument in left-hand side" eqn;

    val _ = let val fixeds = filter (Variable.is_fixed lthy o fst o dest_Free) fun_args in
        null fixeds orelse primcorec_error_eqns "function argument(s) are fixed in context" fixeds
      end;

    val basic_ctr_specs = the (AList.lookup (op =) (fun_names ~~ basic_ctr_specss) fun_name)
      handle Option.Option =>
             primcorec_error_eqn "malformed selector argument in left-hand side" eqn;
    val {ctr, ...} =
      (case of_spec_opt of
        SOME of_spec => the (find_first (curry (op =) of_spec o #ctr) basic_ctr_specs)
      | NONE => filter (exists (curry (op =) sel) o #sels) basic_ctr_specs |> the_single
          handle List.Empty => primcorec_error_eqn "ambiguous selector - use \"of\"" eqn);
    val user_eqn = drop_all eqn0;

    val _ = check_extra_variables lthy fun_args fun_names user_eqn;
  in
    Sel {
      fun_name = fun_name,
      fun_T = fun_T,
      fun_args = fun_args,
      ctr = ctr,
      sel = sel,
      rhs_term = rhs,
      ctr_rhs_opt = ctr_rhs_opt,
      code_rhs_opt = code_rhs_opt,
      eqn_pos = eqn_pos,
      user_eqn = user_eqn
    }
  end;

fun dissect_coeqn_ctr lthy fun_names sequentials (basic_ctr_specss : basic_corec_ctr_spec list list)
    eqn_pos eqn0 code_rhs_opt prems concl matchedsss =
  let
    val (lhs, rhs) = HOLogic.dest_eq concl;
    val (fun_name, fun_args) = strip_comb lhs |>> fst o dest_Free;

    val _ = check_extra_variables lthy fun_args fun_names (drop_all eqn0);

    val SOME basic_ctr_specs = AList.lookup (op =) (fun_names ~~ basic_ctr_specss) fun_name;
    val (ctr, ctr_args) = strip_comb (unfold_lets_splits rhs);
    val {disc, sels, ...} = the (find_first (curry (op =) ctr o #ctr) basic_ctr_specs)
      handle Option.Option => primcorec_error_eqn "not a constructor" ctr;

    val disc_concl = betapply (disc, lhs);
    val (eqn_data_disc_opt, matchedsss') =
      if null (tl basic_ctr_specs) then
        (NONE, matchedsss)
      else
        apfst SOME (dissect_coeqn_disc lthy fun_names sequentials basic_ctr_specss eqn_pos
          (SOME (abstract (List.rev fun_args) rhs)) code_rhs_opt prems disc_concl matchedsss);

    val sel_concls = sels ~~ ctr_args
      |> map (fn (sel, ctr_arg) => HOLogic.mk_eq (betapply (sel, lhs), ctr_arg))
        handle ListPair.UnequalLengths =>
          primcorec_error_eqn "partially applied constructor in right-hand side" rhs;

    val eqns_data_sel =
      map (dissect_coeqn_sel lthy fun_names basic_ctr_specss eqn_pos
        (SOME (abstract (List.rev fun_args) rhs)) code_rhs_opt eqn0 (SOME ctr)) sel_concls;
  in
    (the_list eqn_data_disc_opt @ eqns_data_sel, matchedsss')
  end;

fun dissect_coeqn_code lthy has_call fun_names basic_ctr_specss eqn_pos eqn0 concl matchedsss =
  let
    val (lhs, (rhs', rhs)) = HOLogic.dest_eq concl ||> `(expand_corec_code_rhs lthy has_call []);
    val (fun_name, fun_args) = strip_comb lhs |>> fst o dest_Free;

    val _ = check_extra_variables lthy fun_args fun_names concl;

    val SOME basic_ctr_specs = AList.lookup (op =) (fun_names ~~ basic_ctr_specss) fun_name;

    val cond_ctrs = fold_rev_corec_code_rhs lthy (fn cs => fn ctr => fn _ =>
        if member (op = o apsnd #ctr) basic_ctr_specs ctr then cons (ctr, cs)
        else primcorec_error_eqn "not a constructor" ctr) [] rhs' []
      |> AList.group (op =);

    val ctr_premss = (case cond_ctrs of [_] => [[]] | _ => map (s_dnf o snd) cond_ctrs);
    val ctr_concls = cond_ctrs |> map (fn (ctr, _) =>
        binder_types (fastype_of ctr)
        |> map_index (fn (n, T) => massage_corec_code_rhs lthy (fn _ => fn ctr' => fn args =>
          if ctr' = ctr then nth args n else Const (@{const_name undefined}, T)) [] rhs')
        |> curry Term.list_comb ctr
        |> curry HOLogic.mk_eq lhs);

    val sequentials = replicate (length fun_names) false;
  in
    fold_map2 (dissect_coeqn_ctr lthy fun_names sequentials basic_ctr_specss eqn_pos eqn0
        (SOME (abstract (List.rev fun_args) rhs)))
      ctr_premss ctr_concls matchedsss
  end;

fun dissect_coeqn lthy has_call fun_names sequentials
    (basic_ctr_specss : basic_corec_ctr_spec list list) (eqn_pos, eqn0) of_spec_opt matchedsss =
  let
    val eqn = drop_all eqn0
      handle TERM _ => primcorec_error_eqn "malformed function equation" eqn0;
    val (prems, concl) = Logic.strip_horn eqn
      |> map_prod (map HOLogic.dest_Trueprop) HOLogic.dest_Trueprop
        handle TERM _ => primcorec_error_eqn "malformed function equation" eqn;

    val head = concl
      |> perhaps (try HOLogic.dest_not) |> perhaps (try (fst o HOLogic.dest_eq))
      |> head_of;

    val rhs_opt = concl |> perhaps (try HOLogic.dest_not) |> try (snd o HOLogic.dest_eq);

    val discs = maps (map #disc) basic_ctr_specss;
    val sels = maps (maps #sels) basic_ctr_specss;
    val ctrs = maps (map #ctr) basic_ctr_specss;
  in
    if member (op =) discs head orelse
        is_some rhs_opt andalso
          member (op =) (map SOME fun_names) (try (fst o dest_Free) head) andalso
          member (op =) (filter (null o binder_types o fastype_of) ctrs) (the rhs_opt) then
      dissect_coeqn_disc lthy fun_names sequentials basic_ctr_specss eqn_pos NONE NONE prems concl
        matchedsss
      |>> single
    else if member (op =) sels head then
      (null prems orelse
       primcorec_error_eqn "premise(s) in selector formula" eqn;
       ([dissect_coeqn_sel lthy fun_names basic_ctr_specss eqn_pos NONE NONE eqn0 of_spec_opt
           concl], matchedsss))
    else if is_some rhs_opt andalso
        is_Free head andalso member (op =) fun_names (fst (dest_Free head)) then
      if member (op =) ctrs (head_of (unfold_lets_splits (the rhs_opt))) then
        dissect_coeqn_ctr lthy fun_names sequentials basic_ctr_specss eqn_pos eqn0
          (if null prems then
             SOME (snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Logic.strip_assums_concl eqn0))))
           else
             NONE)
          prems concl matchedsss
      else if null prems then
        dissect_coeqn_code lthy has_call fun_names basic_ctr_specss eqn_pos eqn0 concl matchedsss
        |>> flat
      else
        primcorec_error_eqn "cannot mix constructor and code views (see manual for details)" eqn
    else
      primcorec_error_eqn "malformed function equation" eqn
  end;

fun build_corec_arg_disc (ctr_specs : corec_ctr_spec list)
    ({fun_args, ctr_no, prems, ...} : coeqn_data_disc) =
  if is_none (#pred (nth ctr_specs ctr_no)) then
    I
  else
    s_conjs prems
    |> curry subst_bounds (List.rev fun_args)
    |> abs_tuple_balanced fun_args
    |> K |> nth_map (the (#pred (nth ctr_specs ctr_no)));

fun build_corec_arg_no_call (sel_eqns : coeqn_data_sel list) sel =
  find_first (curry (op =) sel o #sel) sel_eqns
  |> try (fn SOME {fun_args, rhs_term, ...} => abs_tuple_balanced fun_args rhs_term)
  |> the_default undef_const
  |> K;

fun build_corec_args_mutual_call lthy has_call (sel_eqns : coeqn_data_sel list) sel =
  (case find_first (curry (op =) sel o #sel) sel_eqns of
    NONE => (I, I, I)
  | SOME {fun_args, rhs_term, ... } =>
    let
      val bound_Ts = List.rev (map fastype_of fun_args);
      fun rewrite_stop _ t = if has_call t then @{term False} else @{term True};
      fun rewrite_end _ t = if has_call t then undef_const else t;
      fun rewrite_cont bound_Ts t =
        if has_call t then mk_tuple1_balanced bound_Ts (snd (strip_comb t)) else undef_const;
      fun massage f _ = massage_let_if_case lthy has_call f bound_Ts rhs_term
        |> abs_tuple_balanced fun_args;
    in
      (massage rewrite_stop, massage rewrite_end, massage rewrite_cont)
    end);

fun build_corec_arg_nested_call lthy has_call (sel_eqns : coeqn_data_sel list) sel =
  (case find_first (curry (op =) sel o #sel) sel_eqns of
    NONE => I
  | SOME {fun_args, rhs_term, ...} =>
    let
      fun massage bound_Ts U T =
        let
          fun rewrite bound_Ts (Abs (v, V, b)) = Abs (v, V, rewrite (V :: bound_Ts) b)
            | rewrite bound_Ts (t as _ $ _) =
              let val (u, vs) = strip_comb t in
                if is_Free u andalso has_call u then
                  Inr_const U T $ mk_tuple1_balanced bound_Ts vs
                else if try (fst o dest_Const) u = SOME @{const_name case_prod} then
                  map (rewrite bound_Ts) vs |> chop 1
                  |>> HOLogic.mk_split o the_single
                  |> Term.list_comb
                else
                  Term.list_comb (rewrite bound_Ts u, map (rewrite bound_Ts) vs)
              end
            | rewrite _ t =
              if is_Free t andalso has_call t then Inr_const U T $ HOLogic.unit else t;
          in
            rewrite bound_Ts
          end;

      val bound_Ts = List.rev (map fastype_of fun_args);

      fun build t =
        rhs_term
        |> massage_nested_corec_call lthy has_call massage bound_Ts (range_type (fastype_of t))
        |> abs_tuple_balanced fun_args;
    in
      build
    end);

fun build_corec_args_sel lthy has_call (all_sel_eqns : coeqn_data_sel list)
    (ctr_spec : corec_ctr_spec) =
  (case filter (curry (op =) (#ctr ctr_spec) o #ctr) all_sel_eqns of
    [] => I
  | sel_eqns =>
    let
      val sel_call_list = #sels ctr_spec ~~ #calls ctr_spec;
      val no_calls' = map_filter (try (apsnd (fn No_Corec n => n))) sel_call_list;
      val mutual_calls' = map_filter (try (apsnd (fn Mutual_Corec n => n))) sel_call_list;
      val nested_calls' = map_filter (try (apsnd (fn Nested_Corec n => n))) sel_call_list;
    in
      I
      #> fold (fn (sel, n) => nth_map n (build_corec_arg_no_call sel_eqns sel)) no_calls'
      #> fold (fn (sel, (q, g, h)) =>
        let val (fq, fg, fh) = build_corec_args_mutual_call lthy has_call sel_eqns sel in
          nth_map q fq o nth_map g fg o nth_map h fh end) mutual_calls'
      #> fold (fn (sel, n) => nth_map n
        (build_corec_arg_nested_call lthy has_call sel_eqns sel)) nested_calls'
    end);

fun build_codefs lthy bs mxs has_call arg_Tss (corec_specs : corec_spec list)
    (disc_eqnss : coeqn_data_disc list list) (sel_eqnss : coeqn_data_sel list list) =
  let
    val corecs = map #corec corec_specs;
    val ctr_specss = map #ctr_specs corec_specs;
    val corec_args = hd corecs
      |> fst o split_last o binder_types o fastype_of
      |> map (fn T => if range_type T = HOLogic.boolT
          then Abs (Name.uu_, domain_type T, @{term False})
          else Const (@{const_name undefined}, T))
      |> fold2 (fold o build_corec_arg_disc) ctr_specss disc_eqnss
      |> fold2 (fold o build_corec_args_sel lthy has_call) sel_eqnss ctr_specss;
    fun currys [] t = t
      | currys Ts t = t $ mk_tuple1_balanced (List.rev Ts) (map Bound (length Ts - 1 downto 0))
          |> fold_rev (Term.abs o pair Name.uu) Ts;

    val excludess' =
      disc_eqnss
      |> map (map (fn x => (#fun_args x, #ctr_no x, #prems x, #auto_gen x))
        #> fst o (fn xs => fold_map (fn x => fn ys => ((x, ys), ys @ [x])) xs [])
        #> maps (uncurry (map o pair)
          #> map (fn ((fun_args, c, x, a), (_, c', y, a')) =>
              ((c, c', a orelse a'), (x, s_not (s_conjs y)))
            ||> map_prod (map HOLogic.mk_Trueprop) HOLogic.mk_Trueprop
            ||> Logic.list_implies
            ||> curry Logic.list_all (map dest_Free fun_args))));
  in
    map (Term.list_comb o rpair corec_args) corecs
    |> map2 (fn Ts => fn t => if length Ts = 0 then t $ HOLogic.unit else t) arg_Tss
    |> map2 currys arg_Tss
    |> Syntax.check_terms lthy
    |> map3 (fn b => fn mx => fn t => ((b, mx), ((Binding.conceal (Thm.def_binding b), []), t)))
      bs mxs
    |> rpair excludess'
  end;

fun mk_actual_disc_eqns fun_binding arg_Ts exhaustive ({ctr_specs, ...} : corec_spec)
    (sel_eqns : coeqn_data_sel list) (disc_eqns : coeqn_data_disc list) =
  let val num_disc_eqns = length disc_eqns in
    if (exhaustive andalso num_disc_eqns <> 0) orelse num_disc_eqns <> length ctr_specs - 1 then
      disc_eqns
    else
      let
        val n = 0 upto length ctr_specs
          |> the o find_first (fn j => not (exists (curry (op =) j o #ctr_no) disc_eqns));
        val {ctr, disc, ...} = nth ctr_specs n;
        val fun_args = (try (#fun_args o hd) disc_eqns, try (#fun_args o hd) sel_eqns)
          |> the_default (map (curry Free Name.uu) arg_Ts) o merge_options;
        val sel_eqn_opt = find_first (equal ctr o #ctr) sel_eqns;
        val extra_disc_eqn = {
          fun_name = Binding.name_of fun_binding,
          fun_T = arg_Ts ---> body_type (fastype_of (#ctr (hd ctr_specs))),
          fun_args = fun_args,
          ctr = ctr,
          ctr_no = n,
          disc = disc,
          prems = maps (s_not_conj o #prems) disc_eqns,
          auto_gen = true,
          ctr_rhs_opt = Option.map #ctr_rhs_opt sel_eqn_opt |> the_default NONE,
          code_rhs_opt = Option.map #code_rhs_opt sel_eqn_opt |> the_default NONE,
          eqn_pos = Option.map (curry (op +) 1 o #eqn_pos) sel_eqn_opt |> the_default 100000 (* FIXME *),
          user_eqn = undef_const};
      in
        chop n disc_eqns ||> cons extra_disc_eqn |> (op @)
      end
  end;

fun find_corec_calls ctxt has_call (basic_ctr_specs : basic_corec_ctr_spec list)
    ({ctr, sel, rhs_term, ...} : coeqn_data_sel) =
  let
    val sel_no = find_first (curry (op =) ctr o #ctr) basic_ctr_specs
      |> find_index (curry (op =) sel) o #sels o the;
  in
    K (if has_call rhs_term then fold_rev_let_if_case ctxt (K cons) [] rhs_term [] else [])
    |> nth_map sel_no |> AList.map_entry (op =) ctr
  end;

fun applied_fun_of fun_name fun_T fun_args =
  Term.list_comb (Free (fun_name, fun_T), map Bound (length fun_args - 1 downto 0));

fun is_trivial_implies thm =
  uncurry (member (op aconv)) (Logic.strip_horn (Thm.prop_of thm));

fun add_primcorec_ursive auto opts fixes specs of_specs_opt lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val (bs, mxs) = map_split (apfst fst) fixes;
    val (arg_Ts, res_Ts) = map (strip_type o snd o fst #>> mk_tupleT_balanced) fixes |> split_list;

    val _ = (case filter_out (fn (_, T) => Sign.of_sort thy (T, @{sort type})) (bs ~~ arg_Ts) of
        [] => ()
      | (b, _) :: _ => primcorec_error ("type of " ^ Binding.print b ^ " contains top sort"));

    val actual_nn = length bs;

    val sequentials = replicate actual_nn (member (op =) opts Sequential_Option);
    val exhaustives = replicate actual_nn (member (op =) opts Exhaustive_Option);

    val fun_names = map Binding.name_of bs;
    val basic_ctr_specss = map (basic_corec_specs_of lthy) res_Ts;
    val frees = map (fst #>> Binding.name_of #> Free) fixes;
    val has_call = exists_subterm (member (op =) frees);
    val eqns_data =
      fold_map2 (dissect_coeqn lthy has_call fun_names sequentials basic_ctr_specss)
        (tag_list 0 (map snd specs)) of_specs_opt []
      |> flat o fst;

    val _ =
      let
        val missing = fun_names
          |> filter (map (fn Disc x => #fun_name x | Sel x => #fun_name x) eqns_data
            |> not oo member (op =))
      in
        null missing
          orelse primcorec_error_eqns ("missing equations for function(s): " ^ commas missing) []
      end;

    val callssss =
      map_filter (try (fn Sel x => x)) eqns_data
      |> partition_eq (op = o pairself #fun_name)
      |> fst o finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names
      |> map (flat o snd)
      |> map2 (fold o find_corec_calls lthy has_call) basic_ctr_specss
      |> map2 (curry (op |>)) (map (map (fn {ctr, sels, ...} =>
        (ctr, map (K []) sels))) basic_ctr_specss);

    val ((n2m, corec_specs', _, coinduct_thm, coinduct_strong_thm, coinduct_thms,
          coinduct_strong_thms), lthy') =
      corec_specs_of bs arg_Ts res_Ts frees callssss lthy;
    val corec_specs = take actual_nn corec_specs';
    val ctr_specss = map #ctr_specs corec_specs;

    val disc_eqnss' = map_filter (try (fn Disc x => x)) eqns_data
      |> partition_eq (op = o pairself #fun_name)
      |> fst o finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names
      |> map (sort (op < o pairself #ctr_no |> make_ord) o flat o snd);

    val _ = disc_eqnss' |> map (fn x =>
      let val d = duplicates (op = o pairself #ctr_no) x in null d orelse
        (if forall (is_some o #ctr_rhs_opt) x then
          primcorec_error_eqns "multiple equations for constructor(s)"
            (maps (fn t => filter (curry (op =) (#ctr_no t) o #ctr_no) x) d
              |> map (the o #ctr_rhs_opt)) else
          primcorec_error_eqns "excess discriminator formula in definition"
            (maps (fn t => filter (curry (op =) (#ctr_no t) o #ctr_no) x) d |> map #user_eqn)) end);

    val sel_eqnss = map_filter (try (fn Sel x => x)) eqns_data
      |> partition_eq (op = o pairself #fun_name)
      |> fst o finds (fn (x, ({fun_name, ...} :: _)) => x = fun_name) fun_names
      |> map (flat o snd);

    val arg_Tss = map (binder_types o snd o fst) fixes;
    val disc_eqnss = map6 mk_actual_disc_eqns bs arg_Tss exhaustives corec_specs sel_eqnss
      disc_eqnss';
    val (defs, excludess') =
      build_codefs lthy' bs mxs has_call arg_Tss corec_specs disc_eqnss sel_eqnss;

    val tac_opts =
      map (fn {code_rhs_opt, ...} :: _ =>
        if auto orelse is_some code_rhs_opt then SOME (auto_tac o #context) else NONE) disc_eqnss;

    fun exclude_tac tac_opt sequential (c, c', a) =
      if a orelse c = c' orelse sequential then
        SOME (K (HEADGOAL (mk_primcorec_assumption_tac lthy [])))
      else
        tac_opt;

    val excludess'' = map3 (fn tac_opt => fn sequential => map (fn (j, goal) =>
        (j, (Option.map (Goal.prove_sorry lthy [] [] goal #> Thm.close_derivation)
           (exclude_tac tac_opt sequential j), goal))))
      tac_opts sequentials excludess';

    val taut_thmss = map (map (apsnd (the o fst)) o filter (is_some o fst o snd)) excludess'';
    val (goal_idxss, exclude_goalss) = excludess''
      |> map (map (apsnd (rpair [] o snd)) o filter (is_none o fst o snd))
      |> split_list o map split_list;

    fun list_all_fun_args extras =
      map2 (fn [] => I
          | {fun_args, ...} :: _ => map (curry Logic.list_all (extras @ map dest_Free fun_args)))
        disc_eqnss;

    val syntactic_exhaustives =
      map (fn disc_eqns => forall (null o #prems orf is_some o #code_rhs_opt) disc_eqns
          orelse exists #auto_gen disc_eqns)
        disc_eqnss;
    val de_facto_exhaustives =
      map2 (fn b => fn b' => b orelse b') exhaustives syntactic_exhaustives;

    val nchotomy_goalss =
      map2 (fn false => K [] | true => single o HOLogic.mk_Trueprop o mk_dnf o map #prems)
        de_facto_exhaustives disc_eqnss
      |> list_all_fun_args []
    val nchotomy_taut_thmss =
      map5 (fn tac_opt => fn {exhaust_discs = res_exhaust_discs, ...} =>
          fn {code_rhs_opt, ...} :: _ => fn [] => K []
            | [goal] => fn true =>
              let
                val (_, _, arg_exhaust_discs, _, _) =
                  case_thms_of_term lthy (the_default Term.dummy code_rhs_opt);
              in
                [Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                   mk_primcorec_nchotomy_tac ctxt (res_exhaust_discs @ arg_exhaust_discs))
                 |> Thm.close_derivation]
              end
            | false =>
              (case tac_opt of
                SOME tac => [Goal.prove_sorry lthy [] [] goal tac |> Thm.close_derivation]
              | NONE => []))
        tac_opts corec_specs disc_eqnss nchotomy_goalss syntactic_exhaustives;

    val syntactic_exhaustives =
      map (fn disc_eqns => forall (null o #prems orf is_some o #code_rhs_opt) disc_eqns
          orelse exists #auto_gen disc_eqns)
        disc_eqnss;

    val nchotomy_goalss =
      map2 (fn (NONE, false) => map (rpair []) | _ => K []) (tac_opts ~~ syntactic_exhaustives)
        nchotomy_goalss;

    val goalss = nchotomy_goalss @ exclude_goalss;

    fun prove thmss'' def_infos lthy =
      let
        val def_thms = map (snd o snd) def_infos;

        val (nchotomy_thmss, exclude_thmss) =
          (map2 append (take actual_nn thmss'') nchotomy_taut_thmss, drop actual_nn thmss'');

        val ps =
          Variable.variant_frees lthy (maps (maps #fun_args) disc_eqnss) [("P", HOLogic.boolT)];

        val exhaust_thmss =
          map2 (fn false => K []
              | true => fn disc_eqns as {fun_args, ...} :: _ =>
                let
                  val p = Bound (length fun_args);
                  fun mk_imp_p Qs = Logic.list_implies (Qs, HOLogic.mk_Trueprop p);
                in
                  [mk_imp_p (map (mk_imp_p o map HOLogic.mk_Trueprop o #prems) disc_eqns)]
                end)
            de_facto_exhaustives disc_eqnss
          |> list_all_fun_args ps
          |> map3 (fn disc_eqns as {fun_args, ...} :: _ => fn [] => K []
              | [nchotomy_thm] => fn [goal] =>
                [mk_primcorec_exhaust_tac lthy ("" (* for "P" *) :: map (fst o dest_Free) fun_args)
                   (length disc_eqns) nchotomy_thm
                 |> K |> Goal.prove_sorry lthy [] [] goal
                 |> Thm.close_derivation])
            disc_eqnss nchotomy_thmss;
        val nontriv_exhaust_thmss = map (filter_out is_trivial_implies) exhaust_thmss;

        val excludess' = map (op ~~) (goal_idxss ~~ exclude_thmss);
        fun mk_excludesss excludes n =
          fold (fn ((c, c', _), thm) => nth_map c (nth_map c' (K [thm])))
            excludes (map (fn k => replicate k [asm_rl] @ replicate (n - k) []) (0 upto n - 1));
        val excludessss =
          map2 (fn excludes => mk_excludesss excludes o length o #ctr_specs)
            (map2 append excludess' taut_thmss) corec_specs;

        fun prove_disc ({ctr_specs, ...} : corec_spec) excludesss
            ({fun_name, fun_T, fun_args, ctr_no, prems, eqn_pos, ...} : coeqn_data_disc) =
          if Term.aconv_untyped (#disc (nth ctr_specs ctr_no), @{term "\<lambda>x. x = x"}) then
            []
          else
            let
              val {disc, corec_disc, ...} = nth ctr_specs ctr_no;
              val k = 1 + ctr_no;
              val m = length prems;
              val goal =
                applied_fun_of fun_name fun_T fun_args
                |> curry betapply disc
                |> HOLogic.mk_Trueprop
                |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
                |> curry Logic.list_all (map dest_Free fun_args);
            in
              if prems = [@{term False}] then
                []
              else
                mk_primcorec_disc_tac lthy def_thms corec_disc k m excludesss
                |> K |> Goal.prove_sorry lthy [] [] goal
                |> Thm.close_derivation
                |> pair (#disc (nth ctr_specs ctr_no))
                |> pair eqn_pos
                |> single
            end;

        fun prove_sel ({sel_defs, fp_nesting_maps, fp_nesting_map_ident0s, fp_nesting_map_comps,
              ctr_specs, ...} : corec_spec) (disc_eqns : coeqn_data_disc list) excludesss
            ({fun_name, fun_T, fun_args, ctr, sel, rhs_term, code_rhs_opt, eqn_pos, ...}
             : coeqn_data_sel) =
          let
            val SOME ctr_spec = find_first (curry (op =) ctr o #ctr) ctr_specs;
            val ctr_no = find_index (curry (op =) ctr o #ctr) ctr_specs;
            val prems = the_default (maps (s_not_conj o #prems) disc_eqns)
              (find_first (curry (op =) ctr_no o #ctr_no) disc_eqns |> Option.map #prems);
            val corec_sel = find_index (curry (op =) sel) (#sels ctr_spec)
              |> nth (#corec_sels ctr_spec);
            val k = 1 + ctr_no;
            val m = length prems;
            val goal =
              applied_fun_of fun_name fun_T fun_args
              |> curry betapply sel
              |> rpair (abstract (List.rev fun_args) rhs_term)
              |> HOLogic.mk_Trueprop o HOLogic.mk_eq
              |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
              |> curry Logic.list_all (map dest_Free fun_args);
            val (distincts, _, _, split_sels, split_sel_asms) = case_thms_of_term lthy rhs_term;
          in
            mk_primcorec_sel_tac lthy def_thms distincts split_sels split_sel_asms fp_nesting_maps
              fp_nesting_map_ident0s fp_nesting_map_comps corec_sel k m excludesss
            |> K |> Goal.prove_sorry lthy [] [] goal
            |> Thm.close_derivation
            |> `(is_some code_rhs_opt ? fold_thms lthy sel_defs) (*mildly too aggressive*)
            |> pair sel
            |> pair eqn_pos
          end;

        fun prove_ctr disc_alist sel_alist ({sel_defs, ...} : corec_spec)
            (disc_eqns : coeqn_data_disc list) (sel_eqns : coeqn_data_sel list)
            ({ctr, disc, sels, collapse, ...} : corec_ctr_spec) =
          (* don't try to prove theorems when some sel_eqns are missing *)
          if not (exists (curry (op =) ctr o #ctr) disc_eqns)
              andalso not (exists (curry (op =) ctr o #ctr) sel_eqns)
            orelse
              filter (curry (op =) ctr o #ctr) sel_eqns
              |> fst o finds (op = o apsnd #sel) sels
              |> exists (null o snd) then
            []
          else
            let
              val (fun_name, fun_T, fun_args, prems, ctr_rhs_opt, code_rhs_opt, eqn_pos) =
                (find_first (curry (op =) ctr o #ctr) disc_eqns,
                 find_first (curry (op =) ctr o #ctr) sel_eqns)
                |>> Option.map (fn x => (#fun_name x, #fun_T x, #fun_args x, #prems x,
                  #ctr_rhs_opt x, #code_rhs_opt x, #eqn_pos x))
                ||> Option.map (fn x => (#fun_name x, #fun_T x, #fun_args x, [],
                  #ctr_rhs_opt x, #code_rhs_opt x, #eqn_pos x))
                |> the o merge_options;
              val m = length prems;
              val goal =
                (case ctr_rhs_opt of
                  SOME rhs => rhs
                | NONE =>
                  filter (curry (op =) ctr o #ctr) sel_eqns
                  |> fst o finds (op = o apsnd #sel) sels
                  |> map (snd #> (fn [x] => (List.rev (#fun_args x), #rhs_term x)) #-> abstract)
                  |> curry Term.list_comb ctr)
                |> curry mk_Trueprop_eq (applied_fun_of fun_name fun_T fun_args)
                |> curry Logic.list_implies (map HOLogic.mk_Trueprop prems)
                |> curry Logic.list_all (map dest_Free fun_args);
              val disc_thm_opt = AList.lookup (op =) disc_alist disc;
              val sel_thms = map (snd o snd) (filter (member (op =) sels o fst) sel_alist);
            in
              if prems = [@{term False}] then
                []
              else
                mk_primcorec_ctr_tac lthy m collapse disc_thm_opt sel_thms
                |> K |> Goal.prove_sorry lthy [] [] goal
                |> is_some code_rhs_opt ? fold_thms lthy sel_defs (*mildly too aggressive*)
                |> Thm.close_derivation
                |> pair ctr
                |> pair eqn_pos
                |> single
            end;

        fun prove_code exhaustive (disc_eqns : coeqn_data_disc list)
            (sel_eqns : coeqn_data_sel list) nchotomys ctr_alist ctr_specs =
          let
            val fun_data_opt =
              (find_first (member (op =) (map #ctr ctr_specs) o #ctr) disc_eqns,
               find_first (member (op =) (map #ctr ctr_specs) o #ctr) sel_eqns)
              |>> Option.map (fn x => (#fun_name x, #fun_T x, #fun_args x, #code_rhs_opt x))
              ||> Option.map (fn x => (#fun_name x, #fun_T x, #fun_args x, #code_rhs_opt x))
              |> merge_options;
          in
            (case fun_data_opt of
              NONE => []
            | SOME (fun_name, fun_T, fun_args, rhs_opt) =>
              let
                val bound_Ts = List.rev (map fastype_of fun_args);

                val lhs = applied_fun_of fun_name fun_T fun_args;
                val rhs_info_opt =
                  (case rhs_opt of
                    SOME rhs =>
                    let
                      val raw_rhs = expand_corec_code_rhs lthy has_call bound_Ts rhs;
                      val cond_ctrs =
                        fold_rev_corec_code_rhs lthy (K oo (cons oo pair)) bound_Ts raw_rhs [];
                      val ctr_thms =
                        map (the_default FalseE o AList.lookup (op =) ctr_alist o snd) cond_ctrs;
                    in SOME (false, rhs, raw_rhs, ctr_thms) end
                  | NONE =>
                    let
                      fun prove_code_ctr ({ctr, sels, ...} : corec_ctr_spec) =
                        if not (exists (curry (op =) ctr o fst) ctr_alist) then
                          NONE
                        else
                          let
                            val prems = find_first (curry (op =) ctr o #ctr) disc_eqns
                              |> Option.map #prems |> the_default [];
                            val t =
                              filter (curry (op =) ctr o #ctr) sel_eqns
                              |> fst o finds (op = o apsnd #sel) sels
                              |> map (snd #> (fn [x] => (List.rev (#fun_args x), #rhs_term x))
                                #-> abstract)
                              |> curry Term.list_comb ctr;
                          in
                            SOME (prems, t)
                          end;
                      val ctr_conds_argss_opt = map prove_code_ctr ctr_specs;
                      val exhaustive_code =
                        exhaustive
                        orelse exists (is_some andf (null o fst o the)) ctr_conds_argss_opt
                        orelse forall is_some ctr_conds_argss_opt
                          andalso exists #auto_gen disc_eqns;
                      val rhs =
                        (if exhaustive_code then
                           split_last (map_filter I ctr_conds_argss_opt) ||> snd
                         else
                           Const (@{const_name Code.abort}, @{typ String.literal} -->
                               (HOLogic.unitT --> body_type fun_T) --> body_type fun_T) $
                             HOLogic.mk_literal fun_name $
                             absdummy HOLogic.unitT (incr_boundvars 1 lhs)
                           |> pair (map_filter I ctr_conds_argss_opt))
                         |-> fold_rev (fn (prems, u) => mk_If (s_conjs prems) u)
                    in
                      SOME (exhaustive_code, rhs, rhs, map snd ctr_alist)
                    end);
              in
                (case rhs_info_opt of
                  NONE => []
                | SOME (exhaustive_code, rhs, raw_rhs, ctr_thms) =>
                  let
                    val ms = map (Logic.count_prems o prop_of) ctr_thms;
                    val (raw_goal, goal) = (raw_rhs, rhs)
                      |> pairself (curry mk_Trueprop_eq (applied_fun_of fun_name fun_T fun_args)
                        #> curry Logic.list_all (map dest_Free fun_args));
                    val (distincts, discIs, _, split_sels, split_sel_asms) =
                      case_thms_of_term lthy raw_rhs;

                    val raw_code_thm = mk_primcorec_raw_code_tac lthy distincts discIs split_sels
                        split_sel_asms ms ctr_thms
                        (if exhaustive_code then try the_single nchotomys else NONE)
                      |> K |> Goal.prove_sorry lthy [] [] raw_goal
                      |> Thm.close_derivation;
                  in
                    mk_primcorec_code_tac lthy distincts split_sels raw_code_thm
                    |> K |> Goal.prove_sorry lthy [] [] goal
                    |> Thm.close_derivation
                    |> single
                  end)
              end)
          end;

        val disc_alistss = map3 (map oo prove_disc) corec_specs excludessss disc_eqnss;
        val disc_alists = map (map snd o flat) disc_alistss;
        val sel_alists = map4 (map ooo prove_sel) corec_specs disc_eqnss excludessss sel_eqnss;
        val disc_thmss = map (map snd o sort_list_duplicates o flat) disc_alistss;
        val disc_thmsss' = map (map (map (snd o snd))) disc_alistss;
        val sel_thmss = map (map (fst o snd) o sort_list_duplicates) sel_alists;

        fun prove_disc_iff ({ctr_specs, ...} : corec_spec) exhaust_thms disc_thmss'
            (({fun_args = exhaust_fun_args, ...} : coeqn_data_disc) :: _) disc_thms
            ({fun_name, fun_T, fun_args, ctr_no, prems, eqn_pos, ...} : coeqn_data_disc) =
          if null exhaust_thms orelse null disc_thms then
            []
          else
            let
              val {disc, distinct_discss, ...} = nth ctr_specs ctr_no;
              val goal =
                mk_Trueprop_eq (applied_fun_of fun_name fun_T fun_args |> curry betapply disc,
                  mk_conjs prems)
                |> curry Logic.list_all (map dest_Free fun_args);
            in
              mk_primcorec_disc_iff_tac lthy (map (fst o dest_Free) exhaust_fun_args)
                (the_single exhaust_thms) disc_thms disc_thmss' (flat distinct_discss)
              |> K |> Goal.prove_sorry lthy [] [] goal
              |> Thm.close_derivation
              |> fold (fn rule => perhaps (try (fn thm => Meson.first_order_resolve thm rule)))
                @{thms eqTrueE eq_False[THEN iffD1] notnotD}
              |> pair eqn_pos
              |> single
            end;

        val disc_iff_thmss = map6 (flat ooo map2 oooo prove_disc_iff) corec_specs exhaust_thmss
          disc_thmsss' disc_eqnss disc_thmsss' disc_eqnss
          |> map sort_list_duplicates;

        val ctr_alists = map6 (fn disc_alist => maps oooo prove_ctr disc_alist) disc_alists
          (map (map snd) sel_alists) corec_specs disc_eqnss sel_eqnss ctr_specss;
        val ctr_thmss' = map (map snd) ctr_alists;
        val ctr_thmss = map (map snd o order_list) ctr_alists;

        val code_thmss = map6 prove_code exhaustives disc_eqnss sel_eqnss nchotomy_thmss ctr_thmss'
          ctr_specss;

        val disc_iff_or_disc_thmss =
          map2 (fn [] => I | disc_iffs => K disc_iffs) disc_iff_thmss disc_thmss;
        val simp_thmss = map2 append disc_iff_or_disc_thmss sel_thmss;

        val common_name = mk_common_name fun_names;

        val anonymous_notes =
          [(flat disc_iff_or_disc_thmss, simp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val notes =
          [(coinductN, map (if n2m then single else K []) coinduct_thms, []),
           (codeN, code_thmss, code_nitpicksimp_attrs),
           (ctrN, ctr_thmss, []),
           (discN, disc_thmss, []),
           (disc_iffN, disc_iff_thmss, []),
           (excludeN, exclude_thmss, []),
           (exhaustN, nontriv_exhaust_thmss, []),
           (selN, sel_thmss, simp_attrs),
           (simpsN, simp_thmss, []),
           (coinduct_strongN, map (if n2m then single else K []) coinduct_strong_thms, [])]
          |> maps (fn (thmN, thmss, attrs) =>
            map2 (fn fun_name => fn thms =>
                ((Binding.qualify true fun_name (Binding.name thmN), attrs), [(thms, [])]))
              fun_names (take actual_nn thmss))
          |> filter_out (null o fst o hd o snd);

        val common_notes =
          [(coinductN, if n2m then [coinduct_thm] else [], []),
           (coinduct_strongN, if n2m then [coinduct_strong_thm] else [], [])]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));
      in
        lthy
        |> Spec_Rules.add Spec_Rules.Equational (map fst def_infos, flat sel_thmss)
        |> Spec_Rules.add Spec_Rules.Equational (map fst def_infos, flat ctr_thmss)
        |> Spec_Rules.add Spec_Rules.Equational (map fst def_infos, flat code_thmss)
        |> Local_Theory.notes (anonymous_notes @ notes @ common_notes)
        |> snd
      end;

    fun after_qed thmss' = fold_map Local_Theory.define defs #-> prove thmss';
  in
    (goalss, after_qed, lthy')
  end;

fun add_primcorec_ursive_cmd auto opts (raw_fixes, raw_specs_of) lthy =
  let
    val (raw_specs, of_specs_opt) =
      split_list raw_specs_of ||> map (Option.map (Syntax.read_term lthy));
    val (fixes, specs) = fst (Specification.read_spec raw_fixes raw_specs lthy);
  in
    add_primcorec_ursive auto opts fixes specs of_specs_opt lthy
    handle ERROR str => primcorec_error str
  end
  handle PRIMCOREC (str, eqns) =>
         if null eqns then
           error ("primcorec error:\n  " ^ str)
         else
           error ("primcorec error:\n  " ^ str ^ "\nin\n  " ^
             space_implode "\n  " (map (quote o Syntax.string_of_term lthy) eqns));

val add_primcorecursive_cmd = (fn (goalss, after_qed, lthy) =>
  lthy
  |> Proof.theorem NONE after_qed goalss
  |> Proof.refine (Method.primitive_text (K I))
  |> Seq.hd) ooo add_primcorec_ursive_cmd false;

val add_primcorec_cmd = (fn (goalss, after_qed, lthy) =>
  lthy
  |> after_qed (map (fn [] => []
      | _ => error "\"auto\" failed -- use \"primcorecursive\" instead of \"primcorec\"")
    goalss)) ooo add_primcorec_ursive_cmd true;

val primcorec_option_parser = Parse.group (fn () => "option")
  (Parse.reserved "sequential" >> K Sequential_Option
  || Parse.reserved "exhaustive" >> K Exhaustive_Option)

val where_alt_specs_of_parser = Parse.where_ |-- Parse.!!! (Parse.enum1 "|"
  (Parse_Spec.spec -- Scan.option (Parse.reserved "of" |-- Parse.const)));

val _ = Outer_Syntax.local_theory_to_proof @{command_spec "primcorecursive"}
  "define primitive corecursive functions"
  ((Scan.optional (@{keyword "("} |--
      Parse.!!! (Parse.list1 primcorec_option_parser) --| @{keyword ")"}) []) --
    (Parse.fixes -- where_alt_specs_of_parser) >> uncurry add_primcorecursive_cmd);

val _ = Outer_Syntax.local_theory @{command_spec "primcorec"}
  "define primitive corecursive functions"
  ((Scan.optional (@{keyword "("} |--
      Parse.!!! (Parse.list1 primcorec_option_parser) --| @{keyword ")"}) []) --
    (Parse.fixes -- where_alt_specs_of_parser) >> uncurry add_primcorec_cmd);

end;
