(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar_util.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Library for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_UTIL =
sig
  datatype rec_call =
    No_Rec of int |
    Mutual_Rec of int (*before*) * int (*after*) |
    Nested_Rec of int

  datatype corec_call =
    Dummy_No_Corec of int |
    No_Corec of int |
    Mutual_Corec of int (*stop?*) * int (*end*) * int (*continue*) |
    Nested_Corec of int

  type rec_ctr_spec =
    {ctr: term,
     offset: int,
     calls: rec_call list,
     rec_thm: thm}

  type basic_corec_ctr_spec =
    {ctr: term,
     disc: term,
     sels: term list}

  type corec_ctr_spec =
    {ctr: term,
     disc: term,
     sels: term list,
     pred: int option,
     calls: corec_call list,
     discI: thm,
     sel_thms: thm list,
     collapse: thm,
     corec_thm: thm,
     disc_corec: thm,
     sel_corecs: thm list}

  type rec_spec =
    {recx: term,
     nested_map_idents: thm list,
     nested_map_comps: thm list,
     ctr_specs: rec_ctr_spec list}

  type corec_spec =
    {corec: term,
     nested_maps: thm list,
     nested_map_idents: thm list,
     nested_map_comps: thm list,
     ctr_specs: corec_ctr_spec list}

  val s_not: term -> term
  val s_not_conj: term list -> term list
  val s_conjs: term list -> term
  val s_disjs: term list -> term
  val s_dnf: term list list -> term list

  val massage_nested_rec_call: Proof.context -> (term -> bool) -> (typ -> typ -> term -> term) ->
    typ list -> term -> term -> term -> term
  val unfold_let: term -> term
  val massage_mutual_corec_call: Proof.context -> (term -> bool) -> (typ list -> term -> term) ->
    typ list -> term -> term
  val massage_nested_corec_call: Proof.context -> (term -> bool) ->
    (typ list -> typ -> typ -> term -> term) -> typ list -> typ -> term -> term
  val expand_corec_code_rhs: Proof.context -> (term -> bool) -> typ list -> term -> term
  val massage_corec_code_rhs: Proof.context -> (typ list -> term -> term list -> term) ->
    typ list -> term -> term
  val fold_rev_corec_code_rhs: Proof.context -> (term list -> term -> term list -> 'a -> 'a) ->
    typ list -> term -> 'a -> 'a
  val case_thms_of_term: Proof.context -> typ list -> term ->
    thm list * thm list * thm list * thm list

  val rec_specs_of: binding list -> typ list -> typ list -> (term -> int list) ->
    ((term * term list list) list) list -> local_theory ->
    (bool * rec_spec list * typ list * thm * thm list) * local_theory
  val basic_corec_specs_of: Proof.context -> typ -> basic_corec_ctr_spec list
  val corec_specs_of: binding list -> typ list -> typ list -> (term -> int list) ->
    ((term * term list list) list) list -> local_theory ->
    (bool * corec_spec list * typ list * thm * thm * thm list * thm list) * local_theory
end;

structure BNF_FP_Rec_Sugar_Util : BNF_FP_REC_SUGAR_UTIL =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar

datatype rec_call =
  No_Rec of int |
  Mutual_Rec of int * int |
  Nested_Rec of int;

datatype corec_call =
  Dummy_No_Corec of int |
  No_Corec of int |
  Mutual_Corec of int * int * int |
  Nested_Corec of int;

type rec_ctr_spec =
  {ctr: term,
   offset: int,
   calls: rec_call list,
   rec_thm: thm};

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
   collapse: thm,
   corec_thm: thm,
   disc_corec: thm,
   sel_corecs: thm list};

type rec_spec =
  {recx: term,
   nested_map_idents: thm list,
   nested_map_comps: thm list,
   ctr_specs: rec_ctr_spec list};

type corec_spec =
  {corec: term,
   nested_maps: thm list,
   nested_map_idents: thm list,
   nested_map_comps: thm list,
   ctr_specs: corec_ctr_spec list};

val id_def = @{thm id_def};

exception AINT_NO_MAP of term;

fun not_codatatype ctxt T =
  error ("Not a codatatype: " ^ Syntax.string_of_typ ctxt T);
fun ill_formed_rec_call ctxt t =
  error ("Ill-formed recursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun ill_formed_corec_call ctxt t =
  error ("Ill-formed corecursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun invalid_map ctxt t =
  error ("Invalid map function in " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_rec_call ctxt t =
  error ("Unexpected recursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_corec_call ctxt t =
  error ("Unexpected corecursive call: " ^ quote (Syntax.string_of_term ctxt t));

val mk_conjs = try (foldr1 HOLogic.mk_conj) #> the_default @{const True};
val mk_disjs = try (foldr1 HOLogic.mk_disj) #> the_default @{const False};

val conjuncts_s = filter_out (curry (op =) @{const True}) o HOLogic.conjuncts;

fun s_not @{const True} = @{const False}
  | s_not @{const False} = @{const True}
  | s_not (@{const Not} $ t) = t
  | s_not (@{const conj} $ t $ u) = @{const disj} $ s_not t $ s_not u
  | s_not (@{const disj} $ t $ u) = @{const conj} $ s_not t $ s_not u
  | s_not t = @{const Not} $ t;

val s_not_conj = conjuncts_s o s_not o mk_conjs;

fun s_conj c @{const True} = c
  | s_conj c d = HOLogic.mk_conj (c, d);

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

fun factor_out_types ctxt massage destU U T =
  (case try destU U of
    SOME (U1, U2) => if U1 = T then massage T U2 else invalid_map ctxt
  | NONE => invalid_map ctxt);

fun map_flattened_map_args ctxt s map_args fs =
  let
    val flat_fs = flatten_type_args_of_bnf (the (bnf_of ctxt s)) Term.dummy fs;
    val flat_fs' = map_args flat_fs;
  in
    permute_like (op aconv) flat_fs fs flat_fs'
  end;

fun mk_partial_comp gT fT g =
  let val T = domain_type fT --> range_type gT in
    Const (@{const_name Fun.comp}, gT --> fT --> T) $ g
  end;

fun mk_compN' 0 _ _ g = g
  | mk_compN' n gT fT g =
    let val g' = mk_compN' (n - 1) gT (range_type fT) g in
      mk_partial_comp (fastype_of g') fT g'
    end;

fun mk_compN bound_Ts n (g, f) =
  let val typof = curry fastype_of1 bound_Ts in
    mk_compN' n (typof g) (typof f) g $ f
  end;

fun massage_nested_rec_call ctxt has_call raw_massage_fun bound_Ts y y' =
  let
    val typof = curry fastype_of1 bound_Ts;
    val build_map_fst = build_map ctxt (fst_const o fst);

    val yT = typof y;
    val yU = typof y';

    fun y_of_y' () = build_map_fst (yU, yT) $ y';
    val elim_y = Term.map_aterms (fn t => if t = y then y_of_y' () else t);

    fun massage_mutual_fun U T t =
      if has_call t then factor_out_types ctxt raw_massage_fun HOLogic.dest_prodT U T t
      else HOLogic.mk_comp (t, build_map_fst (U, T));

    fun massage_map (Type (_, Us)) (Type (s, Ts)) t =
        (case try (dest_map ctxt s) t of
          SOME (map0, fs) =>
          let
            val Type (_, ran_Ts) = range_type (typof t);
            val map' = mk_map (length fs) Us ran_Ts map0;
            val fs' = map_flattened_map_args ctxt s (map3 massage_map_or_map_arg Us Ts) fs;
          in
            Term.list_comb (map', fs')
          end
        | NONE => raise AINT_NO_MAP t)
      | massage_map _ _ t = raise AINT_NO_MAP t
    and massage_map_or_map_arg U T t =
      if T = U then
        if has_call t then unexpected_rec_call ctxt t else t
      else
        massage_map U T t
        handle AINT_NO_MAP _ => massage_mutual_fun U T t;

    fun massage_call (t as t1 $ t2) =
        if t2 = y then
          massage_map yU yT (elim_y t1) $ y'
          handle AINT_NO_MAP t' => invalid_map ctxt t'
        else
          let val (g, xs) = Term.strip_comb t2 in
            if g = y then
              if exists has_call xs then unexpected_rec_call ctxt t2
              else Term.list_comb (massage_call (mk_compN bound_Ts (length xs) (t1, y)), xs)
            else
              ill_formed_rec_call ctxt t
          end
      | massage_call t = if t = y then y_of_y' () else ill_formed_rec_call ctxt t;
  in
    massage_call
  end;

fun unfold_let (Const (@{const_name Let}, _) $ arg1 $ arg2) = unfold_let (betapply (arg2, arg1))
  | unfold_let (Const (@{const_name prod_case}, _) $ t) =
    (case unfold_let t of
      t' as Abs (s1, T1, Abs (s2, T2, _)) =>
      let
        val x = (s1 ^ s2, Term.maxidx_of_term t + 1);
        val v = Var (x, HOLogic.mk_prodT (T1, T2));
      in
        lambda v (unfold_let (betapplys (t', [HOLogic.mk_fst v, HOLogic.mk_snd v])))
      end
    | _ => t)
  | unfold_let (t $ u) = betapply (unfold_let t, u)
  | unfold_let t = t;

fun fold_rev_let_if_case ctxt f bound_Ts t =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun fld conds t =
      (case Term.strip_comb t of
        (Const (@{const_name Let}, _), [_, _]) => fld conds (unfold_let t)
      | (Const (@{const_name If}, _), [cond, then_branch, else_branch]) =>
        fld (conds @ conjuncts_s cond) then_branch
        o fld (conds @ s_not_conj [cond]) else_branch
      | (Const (c, _), args as _ :: _ :: _) =>
        let val n = num_binder_types (Sign.the_const_type thy c) - 1 in
          if n >= 0 andalso n < length args then
            (case fastype_of1 (bound_Ts, nth args n) of
              Type (s, Ts) =>
              (case dest_case ctxt s Ts t of
                NONE => apsnd (f conds t)
              | SOME (conds', branches) =>
                apfst (cons s) o fold_rev (uncurry fld)
                  (map (append conds o conjuncts_s) conds' ~~ branches))
            | _ => apsnd (f conds t))
          else
            apsnd (f conds t)
        end
      | _ => apsnd (f conds t))
  in
    fld [] t o pair []
  end;

fun case_of ctxt = ctr_sugar_of ctxt #> Option.map (fst o dest_Const o #casex);

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
          (Const (@{const_name Let}, _), [_, _]) => massage_rec bound_Ts (unfold_let t)
        | (Const (@{const_name If}, _), obj :: (branches as [_, _])) =>
          let val branches' = map (massage_rec bound_Ts) branches in
            Term.list_comb (If_const (typof (hd branches')) $ tap check_no_call obj, branches')
          end
        | (Const (c, _), args as _ :: _ :: _) =>
          let
            val gen_T = Sign.the_const_type thy c;
            val (gen_branch_ms, gen_body_fun_T) = strip_fun_type gen_T |>> map num_binder_types;
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
                    Term.list_comb (casex', branches' @ tap (List.app check_no_call) obj_leftovers)
                  end
                else
                  massage_leaf bound_Ts t
              | _ => massage_leaf bound_Ts t)
            else
              massage_leaf bound_Ts t
          end
        | _ => massage_leaf bound_Ts t)
      end
  in
    massage_rec
  end;

val massage_mutual_corec_call = massage_let_if_case;

fun curried_type (Type (@{type_name fun}, [Type (@{type_name prod}, Ts), T])) = Ts ---> T;

fun massage_nested_corec_call ctxt has_call raw_massage_call bound_Ts U t =
  let
    val build_map_Inl = build_map ctxt (uncurry Inl_const o dest_sumT o snd)

    fun massage_mutual_call bound_Ts U T t =
      if has_call t then factor_out_types ctxt (raw_massage_call bound_Ts) dest_sumT U T t
      else build_map_Inl (T, U) $ t;

    fun massage_mutual_fun bound_Ts U T t =
      let
        val var = Var ((Name.uu, Term.maxidx_of_term t + 1),
          domain_type (fastype_of1 (bound_Ts, t)));
      in
        Term.lambda var (massage_mutual_call bound_Ts U T (t $ var))
      end;

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
        | NONE => raise AINT_NO_MAP t)
      | massage_map _ _ _ t = raise AINT_NO_MAP t
    and massage_map_or_map_arg bound_Ts U T t =
      if T = U then
        if has_call t then unexpected_corec_call ctxt t else t
      else
        massage_map bound_Ts U T t
        handle AINT_NO_MAP _ => massage_mutual_fun bound_Ts U T t;

    fun massage_call bound_Ts U T =
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
                Const (@{const_name prod_case}, _) $ t' =>
                let
                  val U' = curried_type U;
                  val T' = curried_type T;
                in
                  Const (@{const_name prod_case}, U' --> U) $ massage_call bound_Ts U' T' t'
                end
              | t1 $ t2 =>
                (if has_call t2 then
                  massage_mutual_call bound_Ts U T t
                else
                  massage_map bound_Ts U T t1 $ t2
                  handle AINT_NO_MAP _ => massage_mutual_call bound_Ts U T t)
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
  snd ooo fold_rev_let_if_case ctxt (fn conds => uncurry (f conds) o Term.strip_comb);

fun case_thms_of_term ctxt bound_Ts t =
  let
    val (caseT_names, _) = fold_rev_let_if_case ctxt (K (K I)) bound_Ts t ();
    val ctr_sugars = map (the o ctr_sugar_of ctxt) caseT_names;
  in
    (maps #distincts ctr_sugars, maps #discIs ctr_sugars, maps #sel_splits ctr_sugars,
     maps #sel_split_asms ctr_sugars)
  end;

fun indexed xs h = let val h' = h + length xs in (h upto h' - 1, h') end;
fun indexedd xss = fold_map indexed xss;
fun indexeddd xsss = fold_map indexedd xsss;
fun indexedddd xssss = fold_map indexeddd xssss;

fun find_index_eq hs h = find_index (curry (op =) h) hs;

(*FIXME: remove special cases for products and sum once they are registered as datatypes*)
fun map_thms_of_typ ctxt (Type (s, _)) =
    if s = @{type_name prod} then
      @{thms map_pair_simp}
    else if s = @{type_name sum} then
      @{thms sum_map.simps}
    else
      (case fp_sugar_of ctxt s of
        SOME {index, mapss, ...} => nth mapss index
      | NONE => [])
  | map_thms_of_typ _ _ = [];

fun rec_specs_of bs arg_Ts res_Ts get_indices callssss0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val ((missing_arg_Ts, perm0_kks,
          fp_sugars as {nested_bnfs, fp_res = {xtor_co_iterss = ctor_iters1 :: _, ...},
            co_inducts = [induct_thm], ...} :: _, (lfp_sugar_thms, _)), lthy') =
      nested_to_mutual_fps Least_FP bs arg_Ts get_indices callssss0 lthy;

    val perm_fp_sugars = sort (int_ord o pairself #index) fp_sugars;

    val indices = map #index fp_sugars;
    val perm_indices = map #index perm_fp_sugars;

    val perm_ctrss = map (#ctrs o of_fp_sugar #ctr_sugars) perm_fp_sugars;
    val perm_ctr_Tsss = map (map (binder_types o fastype_of)) perm_ctrss;
    val perm_lfpTs = map (body_type o fastype_of o hd) perm_ctrss;

    val nn0 = length arg_Ts;
    val nn = length perm_lfpTs;
    val kks = 0 upto nn - 1;
    val perm_ns = map length perm_ctr_Tsss;
    val perm_mss = map (map length) perm_ctr_Tsss;

    val perm_Cs = map (body_type o fastype_of o co_rec_of o of_fp_sugar (#xtor_co_iterss o #fp_res))
      perm_fp_sugars;
    val perm_fun_arg_Tssss =
      mk_iter_fun_arg_types perm_ctr_Tsss perm_ns perm_mss (co_rec_of ctor_iters1);

    fun unpermute0 perm0_xs = permute_like (op =) perm0_kks kks perm0_xs;
    fun unpermute perm_xs = permute_like (op =) perm_indices indices perm_xs;

    val induct_thms = unpermute0 (conj_dests nn induct_thm);

    val lfpTs = unpermute perm_lfpTs;
    val Cs = unpermute perm_Cs;

    val As_rho = tvar_subst thy (take nn0 lfpTs) arg_Ts;
    val Cs_rho = map (fst o dest_TVar) Cs ~~ pad_list HOLogic.unitT nn res_Ts;

    val substA = Term.subst_TVars As_rho;
    val substAT = Term.typ_subst_TVars As_rho;
    val substCT = Term.typ_subst_TVars Cs_rho;

    val perm_Cs' = map substCT perm_Cs;

    fun offset_of_ctr 0 _ = 0
      | offset_of_ctr n (({ctrs, ...} : ctr_sugar) :: ctr_sugars) =
        length ctrs + offset_of_ctr (n - 1) ctr_sugars;

    fun call_of [i] [T] = (if exists_subtype_in Cs T then Nested_Rec else No_Rec) i
      | call_of [i, i'] _ = Mutual_Rec (i, i');

    fun mk_ctr_spec ctr offset fun_arg_Tss rec_thm =
      let
        val (fun_arg_hss, _) = indexedd fun_arg_Tss 0;
        val fun_arg_hs = flat_rec_arg_args fun_arg_hss;
        val fun_arg_iss = map (map (find_index_eq fun_arg_hs)) fun_arg_hss;
      in
        {ctr = substA ctr, offset = offset, calls = map2 call_of fun_arg_iss fun_arg_Tss,
         rec_thm = rec_thm}
      end;

    fun mk_ctr_specs index (ctr_sugars : ctr_sugar list) iter_thmsss =
      let
        val ctrs = #ctrs (nth ctr_sugars index);
        val rec_thmss = co_rec_of (nth iter_thmsss index);
        val k = offset_of_ctr index ctr_sugars;
        val n = length ctrs;
      in
        map4 mk_ctr_spec ctrs (k upto k + n - 1) (nth perm_fun_arg_Tssss index) rec_thmss
      end;

    fun mk_spec ({T, index, ctr_sugars, co_iterss = iterss, co_iter_thmsss = iter_thmsss, ...}
      : fp_sugar) =
      {recx = mk_co_iter thy Least_FP (substAT T) perm_Cs' (co_rec_of (nth iterss index)),
       nested_map_idents = map (unfold_thms lthy [id_def] o map_id0_of_bnf) nested_bnfs,
       nested_map_comps = map map_comp_of_bnf nested_bnfs,
       ctr_specs = mk_ctr_specs index ctr_sugars iter_thmsss};
  in
    ((is_some lfp_sugar_thms, map mk_spec fp_sugars, missing_arg_Ts, induct_thm, induct_thms),
     lthy')
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
      end)
  | _ => not_codatatype ctxt res_T);

fun corec_specs_of bs arg_Ts res_Ts get_indices callssss0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val ((missing_res_Ts, perm0_kks,
          fp_sugars as {nested_bnfs, fp_res = {xtor_co_iterss = dtor_coiters1 :: _, ...},
            co_inducts = coinduct_thms, ...} :: _, (_, gfp_sugar_thms)), lthy') =
      nested_to_mutual_fps Greatest_FP bs res_Ts get_indices callssss0 lthy;

    val perm_fp_sugars = sort (int_ord o pairself #index) fp_sugars;

    val indices = map #index fp_sugars;
    val perm_indices = map #index perm_fp_sugars;

    val perm_ctrss = map (#ctrs o of_fp_sugar #ctr_sugars) perm_fp_sugars;
    val perm_ctr_Tsss = map (map (binder_types o fastype_of)) perm_ctrss;
    val perm_gfpTs = map (body_type o fastype_of o hd) perm_ctrss;

    val nn0 = length res_Ts;
    val nn = length perm_gfpTs;
    val kks = 0 upto nn - 1;
    val perm_ns = map length perm_ctr_Tsss;

    val perm_Cs = map (domain_type o body_fun_type o fastype_of o co_rec_of o
      of_fp_sugar (#xtor_co_iterss o #fp_res)) perm_fp_sugars;
    val (perm_p_Tss, (perm_q_Tssss, _, perm_f_Tssss, _)) =
      mk_coiter_fun_arg_types perm_ctr_Tsss perm_Cs perm_ns (co_rec_of dtor_coiters1);

    val (perm_p_hss, h) = indexedd perm_p_Tss 0;
    val (perm_q_hssss, h') = indexedddd perm_q_Tssss h;
    val (perm_f_hssss, _) = indexedddd perm_f_Tssss h';

    val fun_arg_hs =
      flat (map3 flat_corec_preds_predsss_gettersss perm_p_hss perm_q_hssss perm_f_hssss);

    fun unpermute0 perm0_xs = permute_like (op =) perm0_kks kks perm0_xs;
    fun unpermute perm_xs = permute_like (op =) perm_indices indices perm_xs;

    val coinduct_thmss = map (unpermute0 o conj_dests nn) coinduct_thms;

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

    fun mk_ctr_spec ctr disc sels p_ho q_iss f_iss f_Tss discI sel_thms collapse corec_thm
        disc_corec sel_corecs =
      let val nullary = not (can dest_funT (fastype_of ctr)) in
        {ctr = substA ctr, disc = substA disc, sels = map substA sels, pred = p_ho,
         calls = map3 (call_of nullary) q_iss f_iss f_Tss, discI = discI, sel_thms = sel_thms,
         collapse = collapse, corec_thm = corec_thm, disc_corec = disc_corec,
         sel_corecs = sel_corecs}
      end;

    fun mk_ctr_specs index (ctr_sugars : ctr_sugar list) p_is q_isss f_isss f_Tsss
        coiter_thmsss disc_coitersss sel_coiterssss =
      let
        val ctrs = #ctrs (nth ctr_sugars index);
        val discs = #discs (nth ctr_sugars index);
        val selss = #selss (nth ctr_sugars index);
        val p_ios = map SOME p_is @ [NONE];
        val discIs = #discIs (nth ctr_sugars index);
        val sel_thmss = #sel_thmss (nth ctr_sugars index);
        val collapses = #collapses (nth ctr_sugars index);
        val corec_thms = co_rec_of (nth coiter_thmsss index);
        val disc_corecs = co_rec_of (nth disc_coitersss index);
        val sel_corecss = co_rec_of (nth sel_coiterssss index);
      in
        map13 mk_ctr_spec ctrs discs selss p_ios q_isss f_isss f_Tsss discIs sel_thmss collapses
          corec_thms disc_corecs sel_corecss
      end;

    fun mk_spec ({T, index, ctr_sugars, co_iterss = coiterss, co_iter_thmsss = coiter_thmsss,
          disc_co_itersss = disc_coitersss, sel_co_iterssss = sel_coiterssss, ...} : fp_sugar)
        p_is q_isss f_isss f_Tsss =
      {corec = mk_co_iter thy Greatest_FP (substAT T) perm_Cs' (co_rec_of (nth coiterss index)),
       nested_maps = maps (map_thms_of_typ lthy o T_of_bnf) nested_bnfs,
       nested_map_idents = map (unfold_thms lthy [id_def] o map_id0_of_bnf) nested_bnfs,
       nested_map_comps = map map_comp_of_bnf nested_bnfs,
       ctr_specs = mk_ctr_specs index ctr_sugars p_is q_isss f_isss f_Tsss coiter_thmsss
         disc_coitersss sel_coiterssss};
  in
    ((is_some gfp_sugar_thms, map5 mk_spec fp_sugars p_iss q_issss f_issss f_Tssss, missing_res_Ts,
      co_induct_of coinduct_thms, strong_co_induct_of coinduct_thms, co_induct_of coinduct_thmss,
      strong_co_induct_of coinduct_thmss), lthy')
  end;

end;
