(*  Title:      HOL/BNF/Tools/bnf_fp_def_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Sugared datatype and codatatype constructions.
*)

signature BNF_FP_DEF_SUGAR =
sig
  type fp_sugar =
    {T: typ,
     fp: BNF_FP_Util.fp_kind,
     index: int,
     pre_bnfs: BNF_Def.bnf list,
     nested_bnfs: BNF_Def.bnf list,
     fp_res: BNF_FP_Util.fp_result,
     ctr_defss: thm list list,
     ctr_sugars: BNF_Ctr_Sugar.ctr_sugar list,
     co_iterss: term list list,
     co_inducts: thm list,
     co_iter_thmsss: thm list list list};

  val of_fp_sugar: (fp_sugar -> 'a list) -> fp_sugar -> 'a
  val morph_fp_sugar: morphism -> fp_sugar -> fp_sugar
  val fp_sugar_of: Proof.context -> string -> fp_sugar option

  val co_induct_of: 'a list -> 'a
  val strong_co_induct_of: 'a list -> 'a

  val tvar_subst: theory -> typ list -> typ list -> ((string * int) * typ) list
  val exists_subtype_in: typ list -> typ -> bool
  val flat_rec_arg_args: 'a list list -> 'a list
  val flat_corec_preds_predsss_gettersss: 'a list -> 'a list list list -> 'a list list list ->
    'a list
  val mk_co_iter: theory -> BNF_FP_Util.fp_kind -> typ -> typ list -> term -> term
  val nesty_bnfs: Proof.context -> typ list list list -> typ list -> BNF_Def.bnf list
  val mk_map: int -> typ list -> typ list -> term -> term
  val build_map: local_theory -> (typ * typ -> term) -> typ * typ -> term
  val dest_map: Proof.context -> string -> term -> term * term list
  val dest_ctr: Proof.context -> string -> term -> term * term list
  val mk_co_iters_prelims: BNF_FP_Util.fp_kind -> typ list -> typ list -> int list ->
    int list list -> term list list -> Proof.context ->
    (term list list
     * (typ list list * typ list list list list * term list list
        * term list list list list) list option
     * (string * term list * term list list
        * ((term list list * term list list list) * (typ list * typ list list)) list) option)
    * Proof.context

  val mk_iter_fun_arg_types: typ list -> int list -> int list list -> term ->
    typ list list list list
  val mk_coiter_fun_arg_types: typ list -> int list -> int list list -> term ->
    typ list list
    * (typ list list list list * typ list list list * typ list list list list * typ list)
  val define_iters: string list ->
    (typ list list * typ list list list list * term list list * term list list list list) list ->
    (string -> binding) -> typ list -> typ list -> term list -> Proof.context ->
    (term list * thm list) * Proof.context
  val define_coiters: string list -> string * term list * term list list
    * ((term list list * term list list list) * (typ list * typ list list)) list ->
    (string -> binding) -> typ list -> typ list -> term list -> Proof.context ->
    (term list * thm list) * Proof.context
  val derive_induct_iters_thms_for_types: BNF_Def.bnf list ->
    (typ list list * typ list list list list * term list list * term list list list list) list ->
    thm -> thm list list -> BNF_Def.bnf list -> BNF_Def.bnf list -> typ list -> typ list ->
    typ list -> typ list list list -> term list list -> thm list list -> term list list ->
    thm list list -> local_theory ->
    (thm list * thm * Args.src list) * (thm list list * Args.src list)
    * (thm list list * Args.src list)
  val derive_coinduct_coiters_thms_for_types: BNF_Def.bnf list ->
    string * term list * term list list * ((term list list * term list list list)
      * (typ list * typ list list)) list ->
    thm -> thm list -> thm list list -> BNF_Def.bnf list -> typ list -> typ list -> typ list ->
    int list list -> int list list -> int list -> thm list list -> BNF_Ctr_Sugar.ctr_sugar list ->
    term list list -> thm list list -> (thm list -> thm list) -> local_theory ->
    ((thm list * thm) list * Args.src list)
    * (thm list list * thm list list * Args.src list)
    * (thm list list * thm list list) * (thm list list * thm list list * Args.src list)
    * (thm list list * thm list list * Args.src list)
    * (thm list list * thm list list * Args.src list)

  val co_datatypes: BNF_FP_Util.fp_kind -> (mixfix list -> binding list -> binding list ->
      binding list list -> binding list -> (string * sort) list -> typ list * typ list list ->
      BNF_Def.bnf list -> local_theory -> BNF_FP_Util.fp_result * local_theory) ->
    (bool * bool) * (((((binding * (typ * sort)) list * binding) * (binding * binding)) * mixfix) *
      ((((binding * binding) * (binding * typ) list) * (binding * term) list) *
        mixfix) list) list ->
    local_theory -> local_theory
  val parse_co_datatype_cmd: BNF_FP_Util.fp_kind -> (mixfix list -> binding list -> binding list ->
      binding list list -> binding list -> (string * sort) list -> typ list * typ list list ->
      BNF_Def.bnf list -> local_theory -> BNF_FP_Util.fp_result * local_theory) ->
    (local_theory -> local_theory) parser
end;

structure BNF_FP_Def_Sugar : BNF_FP_DEF_SUGAR =
struct

open BNF_Util
open BNF_Ctr_Sugar
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar_Tactics

val EqN = "Eq_";

type fp_sugar =
  {T: typ,
   fp: fp_kind,
   index: int,
   pre_bnfs: bnf list,
   nested_bnfs: bnf list,
   fp_res: fp_result,
   ctr_defss: thm list list,
   ctr_sugars: ctr_sugar list,
   co_iterss: term list list,
   co_inducts: thm list,
   co_iter_thmsss: thm list list list};

fun of_fp_sugar f (fp_sugar as {index, ...}) = nth (f fp_sugar) index;

fun eq_fp_sugar ({T = T1, fp = fp1, index = index1, fp_res = fp_res1, ...} : fp_sugar,
    {T = T2, fp = fp2, index = index2, fp_res = fp_res2, ...} : fp_sugar) =
  T1 = T2 andalso fp1 = fp2 andalso index1 = index2 andalso eq_fp_result (fp_res1, fp_res2);

fun morph_fp_sugar phi {T, fp, index, pre_bnfs, nested_bnfs, fp_res, ctr_defss, ctr_sugars,
    co_iterss, co_inducts, co_iter_thmsss} =
  {T = Morphism.typ phi T, fp = fp, index = index, pre_bnfs = map (morph_bnf phi) pre_bnfs,
    nested_bnfs = map (morph_bnf phi) nested_bnfs, fp_res = morph_fp_result phi fp_res,
   ctr_defss = map (map (Morphism.thm phi)) ctr_defss,
   ctr_sugars = map (morph_ctr_sugar phi) ctr_sugars,
   co_iterss = map (map (Morphism.term phi)) co_iterss,
   co_inducts = map (Morphism.thm phi) co_inducts,
   co_iter_thmsss = map (map (map (Morphism.thm phi))) co_iter_thmsss};

structure Data = Generic_Data
(
  type T = fp_sugar Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge eq_fp_sugar;
);

fun fp_sugar_of ctxt =
  Symtab.lookup (Data.get (Context.Proof ctxt))
  #> Option.map (morph_fp_sugar
    (Morphism.thm_morphism (Thm.transfer (Proof_Context.theory_of ctxt))));

fun co_induct_of (i :: _) = i;
fun strong_co_induct_of [_, s] = s;

fun register_fp_sugar key fp_sugar =
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.default (key, morph_fp_sugar phi fp_sugar)));

fun register_fp_sugars fp pre_bnfs nested_bnfs (fp_res as {Ts, ...}) ctr_defss ctr_sugars co_iterss
    co_inducts co_iter_thmsss lthy =
  (0, lthy)
  |> fold (fn T as Type (s, _) => fn (kk, lthy) => (kk + 1,
    register_fp_sugar s {T = T, fp = fp, index = kk, pre_bnfs = pre_bnfs,
        nested_bnfs = nested_bnfs, fp_res = fp_res, ctr_defss = ctr_defss, ctr_sugars = ctr_sugars,
        co_iterss = co_iterss, co_inducts = co_inducts, co_iter_thmsss = co_iter_thmsss}
      lthy)) Ts
  |> snd;

(* This function could produce clashes in contrived examples (e.g., "x.A", "x.x_A", "y.A"). *)
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
  end;

val id_def = @{thm id_def};
val mp_conj = @{thm mp_conj};

val simp_attrs = @{attributes [simp]};
val code_simp_attrs = Code.add_default_eqn_attrib :: simp_attrs;

fun tvar_subst thy Ts Us =
  Vartab.fold (cons o apsnd snd) (fold (Sign.typ_match thy) (Ts ~~ Us) Vartab.empty) [];

val exists_subtype_in = Term.exists_subtype o member (op =);

val lists_bmoc = fold (fn xs => fn t => Term.list_comb (t, xs));

fun flat_rec_arg_args xss =
  (* FIXME (once the old datatype package is phased out): The first line below gives the preferred
     order. The second line is for compatibility with the old datatype package. *)
(*
  flat xss
*)
  map hd xss @ maps tl xss;

fun flat_corec_predss_getterss qss fss = maps (op @) (qss ~~ fss);

fun flat_corec_preds_predsss_gettersss [] [qss] [fss] = flat_corec_predss_getterss qss fss
  | flat_corec_preds_predsss_gettersss (p :: ps) (qss :: qsss) (fss :: fsss) =
    p :: flat_corec_predss_getterss qss fss @ flat_corec_preds_predsss_gettersss ps qsss fsss;

fun mk_tupled_fun x f xs = HOLogic.tupled_lambda x (Term.list_comb (f, xs));
fun mk_uncurried2_fun f xss =
  mk_tupled_fun (HOLogic.mk_tuple (map HOLogic.mk_tuple xss)) f (flat_rec_arg_args xss);

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

fun mk_co_iter thy fp fpT Cs t =
  let
    val (f_Cs, Type (_, [prebody, body])) = strip_fun_type (fastype_of t);
    val fpT0 = fp_case fp prebody body;
    val Cs0 = distinct (op =) (map (fp_case fp body_type domain_type) f_Cs);
    val rho = tvar_subst thy (fpT0 :: Cs0) (fpT :: Cs);
  in
    Term.subst_TVars rho t
  end;

fun mk_co_iters thy fp fpTs Cs ts0 =
  let
    val nn = length fpTs;
    val (fpTs0, Cs0) =
      map ((fp = Greatest_FP ? swap) o dest_funT o snd o strip_typeN nn o fastype_of) ts0
      |> split_list;
    val rho = tvar_subst thy (fpTs0 @ Cs0) (fpTs @ Cs);
  in
    map (Term.subst_TVars rho) ts0
  end;

val mk_fp_iter_fun_types = binder_fun_types o fastype_of;

fun unzip_recT Cs (T as Type (@{type_name prod}, Ts as [_, U])) =
    if member (op =) Cs U then Ts else [T]
  | unzip_recT _ T = [T];

fun unzip_corecT Cs (T as Type (@{type_name sum}, Ts as [_, U])) =
    if member (op =) Cs U then Ts else [T]
  | unzip_corecT _ T = [T];

fun mk_map live Ts Us t =
  let val (Type (_, Ts0), Type (_, Us0)) = strip_typeN (live + 1) (fastype_of t) |>> List.last in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_rel live Ts Us t =
  let val [Type (_, Ts0), Type (_, Us0)] = binder_types (snd (strip_typeN live (fastype_of t))) in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun build_map lthy build_simple =
  let
    fun build (TU as (T, U)) =
      if T = U then
        HOLogic.id_const T
      else
        (case TU of
          (Type (s, Ts), Type (s', Us)) =>
          if s = s' then
            let
              val bnf = the (bnf_of lthy s);
              val live = live_of_bnf bnf;
              val mapx = mk_map live Ts Us (map_of_bnf bnf);
              val TUs' = map dest_funT (fst (strip_typeN live (fastype_of mapx)));
            in Term.list_comb (mapx, map build TUs') end
          else
            build_simple TU
        | _ => build_simple TU);
  in build end;

fun fo_match ctxt t pat =
  let val thy = Proof_Context.theory_of ctxt in
    Pattern.first_order_match thy (pat, t) (Vartab.empty, Vartab.empty)
  end;

val dummy_var_name = "?f"

fun mk_map_pattern ctxt s =
  let
    val bnf = the (bnf_of ctxt s);
    val mapx = map_of_bnf bnf;
    val live = live_of_bnf bnf;
    val (f_Ts, _) = strip_typeN live (fastype_of mapx);
    val fs = map_index (fn (i, T) => Var ((dummy_var_name, i), T)) f_Ts;
  in
    (mapx, betapplys (mapx, fs))
  end;

fun dest_map ctxt s call =
  let
    val (map0, pat) = mk_map_pattern ctxt s;
    val (_, tenv) = fo_match ctxt call pat;
  in
    (map0, Vartab.fold_rev (fn (_, (_, f)) => cons f) tenv [])
  end;

fun dest_ctr ctxt s t =
  let
    val (f, args) = Term.strip_comb t;
  in
    (case fp_sugar_of ctxt s of
      SOME fp_sugar =>
      (case find_first (can (fo_match ctxt f)) (#ctrs (of_fp_sugar #ctr_sugars fp_sugar)) of
        SOME f' => (f', args)
      | NONE => raise Fail "dest_ctr")
    | NONE => raise Fail "dest_ctr")
  end;

fun liveness_of_fp_bnf n bnf =
  (case T_of_bnf bnf of
    Type (_, Ts) => map (not o member (op =) (deads_of_bnf bnf)) Ts
  | _ => replicate n false);

fun cannot_merge_types () = error "Mutually recursive types must have the same type parameters";

fun merge_type_arg T T' = if T = T' then T else cannot_merge_types ();

fun merge_type_args (As, As') =
  if length As = length As' then map2 merge_type_arg As As' else cannot_merge_types ();

fun reassoc_conjs thm =
  reassoc_conjs (thm RS @{thm conj_assoc[THEN iffD1]})
  handle THM _ => thm;

fun type_args_named_constrained_of ((((ncAs, _), _), _), _) = ncAs;
fun type_binding_of ((((_, b), _), _), _) = b;
fun map_binding_of (((_, (b, _)), _), _) = b;
fun rel_binding_of (((_, (_, b)), _), _) = b;
fun mixfix_of ((_, mx), _) = mx;
fun ctr_specs_of (_, ctr_specs) = ctr_specs;

fun disc_of ((((disc, _), _), _), _) = disc;
fun ctr_of ((((_, ctr), _), _), _) = ctr;
fun args_of (((_, args), _), _) = args;
fun defaults_of ((_, ds), _) = ds;
fun ctr_mixfix_of (_, mx) = mx;

fun add_nesty_bnf_names Us =
  let
    fun add (Type (s, Ts)) ss =
        let val (needs, ss') = fold_map add Ts ss in
          if exists I needs then (true, insert (op =) s ss') else (false, ss')
        end
      | add T ss = (member (op =) Us T, ss);
  in snd oo add end;

fun nesty_bnfs ctxt ctr_Tsss Us =
  map_filter (bnf_of ctxt) (fold (fold (fold (add_nesty_bnf_names Us))) ctr_Tsss []);

fun indexify proj xs f p = f (find_index (curry op = (proj p)) xs) p;

fun mk_iter_fun_arg_types0 n ms = map2 dest_tupleT ms o dest_sumTN_balanced n o domain_type;

fun mk_iter_fun_arg_types Cs ns mss =
  mk_fp_iter_fun_types
  #> map3 mk_iter_fun_arg_types0 ns mss
  #> map (map (map (unzip_recT Cs)));

fun mk_iters_args_types Cs ns mss ctor_iter_fun_Tss lthy =
  let
    val Css = map2 replicate ns Cs;
    val y_Tsss = map3 mk_iter_fun_arg_types0 ns mss (map un_fold_of ctor_iter_fun_Tss);
    val g_Tss = map2 (fn C => map (fn y_Ts => y_Ts ---> C)) Cs y_Tsss;

    val ((gss, ysss), lthy) =
      lthy
      |> mk_Freess "f" g_Tss
      ||>> mk_Freesss "x" y_Tsss;

    val y_Tssss = map (map (map single)) y_Tsss;
    val yssss = map (map (map single)) ysss;

    val z_Tssss =
      map3 (fn n => fn ms => map2 (map (unzip_recT Cs) oo dest_tupleT) ms o
        dest_sumTN_balanced n o domain_type o co_rec_of) ns mss ctor_iter_fun_Tss;

    val z_Tsss' = map (map flat_rec_arg_args) z_Tssss;
    val h_Tss = map2 (map2 (curry op --->)) z_Tsss' Css;

    val hss = map2 (map2 retype_free) h_Tss gss;
    val zssss_hd = map2 (map2 (map2 (retype_free o hd))) z_Tssss ysss;
    val (zssss_tl, lthy) =
      lthy
      |> mk_Freessss "y" (map (map (map tl)) z_Tssss);
    val zssss = map2 (map2 (map2 cons)) zssss_hd zssss_tl;
  in
    ([(g_Tss, y_Tssss, gss, yssss), (h_Tss, z_Tssss, hss, zssss)], lthy)
  end;

fun mk_coiter_fun_arg_types0 Cs ns mss fun_Ts =
  let
    (*avoid "'a itself" arguments in coiterators and corecursors*)
    fun repair_arity [0] = [1]
      | repair_arity ms = ms;

    val f_sum_prod_Ts = map range_type fun_Ts;
    val f_prod_Tss = map2 dest_sumTN_balanced ns f_sum_prod_Ts;
    val f_Tsss = map2 (map2 dest_tupleT o repair_arity) mss f_prod_Tss;
    val f_Tssss = map2 (fn C => map (map (map (curry op --> C) o unzip_corecT Cs))) Cs f_Tsss;
    val q_Tssss = map (map (map (fn [_] => [] | [_, T] => [mk_pred1T (domain_type T)]))) f_Tssss;
  in
    (q_Tssss, f_Tsss, f_Tssss, f_sum_prod_Ts)
  end;

fun mk_coiter_p_pred_types Cs ns = map2 (fn n => replicate (Int.max (0, n - 1)) o mk_pred1T) ns Cs;

fun mk_coiter_fun_arg_types Cs ns mss dtor_coiter =
  (mk_coiter_p_pred_types Cs ns,
   mk_fp_iter_fun_types dtor_coiter |> mk_coiter_fun_arg_types0 Cs ns mss);

fun mk_coiters_args_types Cs ns mss dtor_coiter_fun_Tss lthy =
  let
    val p_Tss = mk_coiter_p_pred_types Cs ns;

    fun mk_types get_Ts =
      let
        val fun_Ts = map get_Ts dtor_coiter_fun_Tss;
        val (q_Tssss, f_Tsss, f_Tssss, f_sum_prod_Ts) = mk_coiter_fun_arg_types0 Cs ns mss fun_Ts;
        val pf_Tss = map3 flat_corec_preds_predsss_gettersss p_Tss q_Tssss f_Tssss;
      in
        (q_Tssss, f_Tsss, f_Tssss, (f_sum_prod_Ts, pf_Tss))
      end;

    val (r_Tssss, g_Tsss, g_Tssss, unfold_types) = mk_types un_fold_of;
    val (s_Tssss, h_Tsss, h_Tssss, corec_types) = mk_types co_rec_of;

    val ((((Free (z, _), cs), pss), gssss), lthy) =
      lthy
      |> yield_singleton (mk_Frees "z") dummyT
      ||>> mk_Frees "a" Cs
      ||>> mk_Freess "p" p_Tss
      ||>> mk_Freessss "g" g_Tssss;
    val rssss = map (map (map (fn [] => []))) r_Tssss;

    val hssss_hd = map2 (map2 (map2 (fn T :: _ => fn [g] => retype_free T g))) h_Tssss gssss;
    val ((sssss, hssss_tl), lthy) =
      lthy
      |> mk_Freessss "q" s_Tssss
      ||>> mk_Freessss "h" (map (map (map tl)) h_Tssss);
    val hssss = map2 (map2 (map2 cons)) hssss_hd hssss_tl;

    val cpss = map2 (map o rapp) cs pss;

    fun build_sum_inj mk_inj = build_map lthy (uncurry mk_inj o dest_sumT o snd);

    fun build_dtor_coiter_arg _ [] [cf] = cf
      | build_dtor_coiter_arg T [cq] [cf, cf'] =
        mk_If cq (build_sum_inj Inl_const (fastype_of cf, T) $ cf)
          (build_sum_inj Inr_const (fastype_of cf', T) $ cf');

    fun mk_args qssss fssss f_Tsss =
      let
        val pfss = map3 flat_corec_preds_predsss_gettersss pss qssss fssss;
        val cqssss = map2 (map o map o map o rapp) cs qssss;
        val cfssss = map2 (map o map o map o rapp) cs fssss;
        val cqfsss = map3 (map3 (map3 build_dtor_coiter_arg)) f_Tsss cqssss cfssss;
      in (pfss, cqfsss) end;

    val unfold_args = mk_args rssss gssss g_Tsss;
    val corec_args = mk_args sssss hssss h_Tsss;
  in
    ((z, cs, cpss, [(unfold_args, unfold_types), (corec_args, corec_types)]), lthy)
  end;

fun mk_co_iters_prelims fp fpTs Cs ns mss xtor_co_iterss0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val (xtor_co_iter_fun_Tss, xtor_co_iterss) =
      map (mk_co_iters thy fp fpTs Cs #> `(mk_fp_iter_fun_types o hd)) (transpose xtor_co_iterss0)
      |> apsnd transpose o apfst transpose o split_list;

    val ((iters_args_types, coiters_args_types), lthy') =
      if fp = Least_FP then
        mk_iters_args_types Cs ns mss xtor_co_iter_fun_Tss lthy |>> (rpair NONE o SOME)
      else
        mk_coiters_args_types Cs ns mss xtor_co_iter_fun_Tss lthy |>> (pair NONE o SOME)
  in
    ((xtor_co_iterss, iters_args_types, coiters_args_types), lthy')
  end;

fun mk_iter_body ctor_iter fss xssss =
  Term.list_comb (ctor_iter, map2 (mk_sum_caseN_balanced oo map2 mk_uncurried2_fun) fss xssss);

fun mk_preds_getterss_join c cps sum_prod_T cqfss =
  let val n = length cqfss in
    Term.lambda c (mk_IfN sum_prod_T cps
      (map2 (mk_InN_balanced sum_prod_T n) (map HOLogic.mk_tuple cqfss) (1 upto n)))
  end;

fun mk_coiter_body cs cpss f_sum_prod_Ts cqfsss dtor_coiter =
  Term.list_comb (dtor_coiter, map4 mk_preds_getterss_join cs cpss f_sum_prod_Ts cqfsss);

fun define_co_iters fp fpT Cs binding_specs lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val ((csts, defs), (lthy', lthy)) = lthy0
      |> apfst split_list o fold_map (fn (b, spec) =>
        Specification.definition (SOME (b, NONE, NoSyn), ((Thm.def_binding b, []), spec))
        #>> apsnd snd) binding_specs
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy lthy';

    val csts' = map (mk_co_iter thy fp fpT Cs o Morphism.term phi) csts;
    val defs' = map (Morphism.thm phi) defs;
  in
    ((csts', defs'), lthy')
  end;

fun define_iters iterNs iter_args_typess' mk_binding fpTs Cs ctor_iters lthy =
  let
    val nn = length fpTs;

    val fpT_to_C as Type (_, [fpT, _]) = snd (strip_typeN nn (fastype_of (hd ctor_iters)));

    fun generate_iter suf (f_Tss, _, fss, xssss) ctor_iter =
      let
        val res_T = fold_rev (curry op --->) f_Tss fpT_to_C;
        val b = mk_binding suf;
        val spec =
          mk_Trueprop_eq (lists_bmoc fss (Free (Binding.name_of b, res_T)),
            mk_iter_body ctor_iter fss xssss);
      in (b, spec) end;
  in
    define_co_iters Least_FP fpT Cs (map3 generate_iter iterNs iter_args_typess' ctor_iters) lthy
  end;

fun define_coiters coiterNs (_, cs, cpss, coiter_args_typess') mk_binding fpTs Cs dtor_coiters
    lthy =
  let
    val nn = length fpTs;

    val C_to_fpT as Type (_, [_, fpT]) = snd (strip_typeN nn (fastype_of (hd dtor_coiters)));

    fun generate_coiter suf ((pfss, cqfsss), (f_sum_prod_Ts, pf_Tss)) dtor_coiter =
      let
        val res_T = fold_rev (curry op --->) pf_Tss C_to_fpT;
        val b = mk_binding suf;
        val spec =
          mk_Trueprop_eq (lists_bmoc pfss (Free (Binding.name_of b, res_T)),
            mk_coiter_body cs cpss f_sum_prod_Ts cqfsss dtor_coiter);
      in (b, spec) end;
  in
    define_co_iters Greatest_FP fpT Cs
      (map3 generate_coiter coiterNs coiter_args_typess' dtor_coiters) lthy
  end;

fun derive_induct_iters_thms_for_types pre_bnfs [fold_args_types, rec_args_types] ctor_induct
    ctor_iter_thmss nesting_bnfs nested_bnfs fpTs Cs Xs ctrXs_Tsss ctrss ctr_defss iterss iter_defss
    lthy =
  let
    val iterss' = transpose iterss;
    val iter_defss' = transpose iter_defss;

    val [folds, recs] = iterss';
    val [fold_defs, rec_defs] = iter_defss';

    val ctr_Tsss = map (map (binder_types o fastype_of)) ctrss;

    val nn = length pre_bnfs;
    val ns = map length ctr_Tsss;
    val mss = map (map length) ctr_Tsss;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val nesting_map_ids'' = map (unfold_thms lthy [id_def] o map_id_of_bnf) nesting_bnfs;
    val nested_map_ids'' = map (unfold_thms lthy [id_def] o map_id_of_bnf) nested_bnfs;
    val nested_set_map's = maps set_map'_of_bnf nested_bnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val ((((ps, ps'), xsss), us'), names_lthy) =
      lthy
      |> mk_Frees' "P" (map mk_pred1T fpTs)
      ||>> mk_Freesss "x" ctr_Tsss
      ||>> Variable.variant_fixes fp_b_names;

    val us = map2 (curry Free) us' fpTs;

    fun mk_sets_nested bnf =
      let
        val Type (T_name, Us) = T_of_bnf bnf;
        val lives = lives_of_bnf bnf;
        val sets = sets_of_bnf bnf;
        fun mk_set U =
          (case find_index (curry op = U) lives of
            ~1 => Term.dummy
          | i => nth sets i);
      in
        (T_name, map mk_set Us)
      end;

    val setss_nested = map mk_sets_nested nested_bnfs;

    val (induct_thms, induct_thm) =
      let
        fun mk_set Ts t =
          let val Type (_, Ts0) = domain_type (fastype_of t) in
            Term.subst_atomic_types (Ts0 ~~ Ts) t
          end;

        fun mk_raw_prem_prems _ (x as Free (_, Type _)) (X as TFree _) =
            [([], (find_index (curry op = X) Xs + 1, x))]
          | mk_raw_prem_prems names_lthy (x as Free (s, Type (T_name, Ts0))) (Type (_, Xs_Ts0)) =
            (case AList.lookup (op =) setss_nested T_name of
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
              HOLogic.mk_Trueprop (HOLogic.mk_mem (y, set $ x'))) xysets,
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
            HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map2 (curry op $) ps us)));

        val kksss = map (map (map (fst o snd) o #2)) raw_premss;

        val ctor_induct' = ctor_induct OF (map mk_sumEN_tupled_balanced mss);

        val thm =
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
            mk_induct_tac ctxt nn ns mss kksss (flat ctr_defss) ctor_induct' nested_set_map's
              pre_set_defss)
          |> singleton (Proof_Context.export names_lthy lthy)
          |> Thm.close_derivation;
      in
        `(conj_dests nn) thm
      end;

    val induct_cases = quasi_unambiguous_case_names (maps (map name_of_ctr) ctrss);
    val induct_case_names_attr = Attrib.internal (K (Rule_Cases.case_names induct_cases));

    val xctrss = map2 (map2 (curry Term.list_comb)) ctrss xsss;

    fun mk_iter_thmss (_, x_Tssss, fss, _) iters iter_defs ctor_iter_thms =
      let
        val fiters = map (lists_bmoc fss) iters;

        fun mk_goal fss fiter xctr f xs fxs =
          fold_rev (fold_rev Logic.all) (xs :: fss)
            (mk_Trueprop_eq (fiter $ xctr, Term.list_comb (f, fxs)));

        fun maybe_tick (T, U) u f =
          if try (fst o HOLogic.dest_prodT) U = SOME T then
            Term.lambda u (HOLogic.mk_prod (u, f $ u))
          else
            f;

        fun build_iter (x as Free (_, T)) U =
          if T = U then
            x
          else
            build_map lthy (indexify (perhaps (try (snd o HOLogic.dest_prodT)) o snd) Cs
              (fn kk => fn TU => maybe_tick TU (nth us kk) (nth fiters kk))) (T, U) $ x;

        val fxsss = map2 (map2 (flat_rec_arg_args oo map2 (map o build_iter))) xsss x_Tssss;

        val goalss = map5 (map4 o mk_goal fss) fiters xctrss fss xsss fxsss;

        val tacss =
          map2 (map o mk_iter_tac pre_map_defs (nested_map_ids'' @ nesting_map_ids'') iter_defs)
            ctor_iter_thms ctr_defss;

        fun prove goal tac =
          Goal.prove_sorry lthy [] [] goal (tac o #context)
          |> Thm.close_derivation;
      in
        map2 (map2 prove) goalss tacss
      end;

    val fold_thmss = mk_iter_thmss fold_args_types folds fold_defs (map un_fold_of ctor_iter_thmss);
    val rec_thmss = mk_iter_thmss rec_args_types recs rec_defs (map co_rec_of ctor_iter_thmss);
  in
    ((induct_thms, induct_thm, [induct_case_names_attr]),
     (fold_thmss, code_simp_attrs), (rec_thmss, code_simp_attrs))
  end;

fun derive_coinduct_coiters_thms_for_types pre_bnfs (z, cs, cpss,
      coiters_args_types as [((pgss, crgsss), _), ((phss, cshsss), _)])
    dtor_coinduct dtor_ctors dtor_coiter_thmss nesting_bnfs fpTs Cs As kss mss ns ctr_defss
    ctr_sugars coiterss coiter_defss export_args lthy =
  let
    val coiterss' = transpose coiterss;
    val coiter_defss' = transpose coiter_defss;

    val [unfold_defs, corec_defs] = coiter_defss';

    val nn = length pre_bnfs;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_rel_defs = map rel_def_of_bnf pre_bnfs;
    val nesting_map_ids'' = map (unfold_thms lthy [id_def] o map_id_of_bnf) nesting_bnfs;
    val nesting_rel_eqs = map rel_eq_of_bnf nesting_bnfs;

    val fp_b_names = map base_name_of_typ fpTs;

    val ctrss = map (map (mk_ctr As) o #ctrs) ctr_sugars;
    val discss = map (map (mk_disc_or_sel As) o #discs) ctr_sugars;
    val selsss = map (map (map (mk_disc_or_sel As)) o #selss) ctr_sugars;
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

        (* TODO: generalize (cf. "build_map") *)
        fun build_rel rs' T =
          (case find_index (curry op = T) fpTs of
            ~1 =>
            if exists_subtype_in fpTs T then
              let
                val Type (s, Ts) = T
                val bnf = the (bnf_of lthy s);
                val live = live_of_bnf bnf;
                val rel = mk_rel live Ts Ts (rel_of_bnf bnf);
                val Ts' = map domain_type (fst (strip_typeN live (fastype_of rel)));
              in Term.list_comb (rel, map (build_rel rs') Ts') end
            else
              HOLogic.eq_const T
          | kk => nth rs' kk);

        fun build_rel_app rs' usel vsel = fold rapp [usel, vsel] (build_rel rs' (fastype_of usel));

        fun mk_prem_ctr_concls rs' n k udisc usels vdisc vsels =
          (if k = n then [] else [HOLogic.mk_eq (udisc, vdisc)]) @
          (if null usels then
             []
           else
             [Library.foldr HOLogic.mk_imp (if n = 1 then [] else [udisc, vdisc],
                Library.foldr1 HOLogic.mk_conj (map2 (build_rel_app rs') usels vsels))]);

        fun mk_prem_concl rs' n udiscs uselss vdiscs vselss =
          Library.foldr1 HOLogic.mk_conj
            (flat (map5 (mk_prem_ctr_concls rs' n) (1 upto n) udiscs uselss vdiscs vselss))
          handle List.Empty => @{term True};

        fun mk_prem rs' uvr u v n udiscs uselss vdiscs vselss =
          fold_rev Logic.all [u, v] (Logic.mk_implies (HOLogic.mk_Trueprop uvr,
            HOLogic.mk_Trueprop (mk_prem_concl rs' n udiscs uselss vdiscs vselss)));

        val concl =
          HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
            (map3 (fn uvr => fn u => fn v => HOLogic.mk_imp (uvr, HOLogic.mk_eq (u, v)))
               uvrs us vs));

        fun mk_goal rs' =
          Logic.list_implies (map8 (mk_prem rs') uvrs us vs ns udiscss uselsss vdiscss vselsss,
            concl);

        val goals = map mk_goal [rs, strong_rs];

        fun prove dtor_coinduct' goal =
          Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
            mk_coinduct_tac ctxt nesting_rel_eqs nn ns dtor_coinduct' pre_rel_defs dtor_ctors
              exhausts ctr_defss disc_thmsss sel_thmsss)
          |> singleton (Proof_Context.export names_lthy lthy)
          |> Thm.close_derivation;

        fun postproc nn thm =
          Thm.permute_prems 0 nn
            (if nn = 1 then thm RS mp else funpow nn (fn thm => reassoc_conjs (thm RS mp_conj)) thm)
          |> Drule.zero_var_indexes
          |> `(conj_dests nn);

        val rel_eqs = map rel_eq_of_bnf pre_bnfs;
        val rel_monos = map rel_mono_of_bnf pre_bnfs;
        val dtor_coinducts =
          [dtor_coinduct, mk_strong_coinduct_thm dtor_coinduct rel_eqs rel_monos lthy];
      in
        map2 (postproc nn oo prove) dtor_coinducts goals
      end;

    fun mk_coinduct_concls ms discs ctrs =
      let
        fun mk_disc_concl disc = [name_of_disc disc];
        fun mk_ctr_concl 0 _ = []
          | mk_ctr_concl _ ctor = [name_of_ctr ctor];
        val disc_concls = map mk_disc_concl (fst (split_last discs)) @ [[]];
        val ctr_concls = map2 mk_ctr_concl ms ctrs;
      in
        flat (map2 append disc_concls ctr_concls)
      end;

    val coinduct_cases = quasi_unambiguous_case_names (map (prefix EqN) fp_b_names);
    val coinduct_conclss =
      map3 (quasi_unambiguous_case_names ooo mk_coinduct_concls) mss discss ctrss;

    fun mk_maybe_not pos = not pos ? HOLogic.mk_not;

    val fcoiterss' as [gunfolds, hcorecs] =
      map2 (fn (pfss, _) => map (lists_bmoc pfss)) (map fst coiters_args_types) coiterss';

    val (unfold_thmss, corec_thmss, safe_unfold_thmss, safe_corec_thmss) =
      let
        fun mk_goal pfss c cps fcoiter n k ctr m cfs' =
          fold_rev (fold_rev Logic.all) ([c] :: pfss)
            (Logic.list_implies (seq_conds (HOLogic.mk_Trueprop oo mk_maybe_not) n k cps,
               mk_Trueprop_eq (fcoiter $ c, Term.list_comb (ctr, take m cfs'))));

        fun mk_U maybe_mk_sumT =
          typ_subst_nonatomic (map2 (fn C => fn fpT => (maybe_mk_sumT fpT C, fpT)) Cs fpTs);

        fun tack z_name (c, u) f =
          let val z = Free (z_name, mk_sumT (fastype_of u, fastype_of c)) in
            Term.lambda z (mk_sum_case (Term.lambda u u, Term.lambda c (f $ c)) $ z)
          end;

        fun build_coiter fcoiters maybe_mk_sumT maybe_tack cqf =
          let val T = fastype_of cqf in
            if exists_subtype_in Cs T then
              let val U = mk_U maybe_mk_sumT T in
                build_map lthy (indexify snd fpTs (fn kk => fn _ =>
                  maybe_tack (nth cs kk, nth us kk) (nth fcoiters kk))) (T, U) $ cqf
              end
            else
              cqf
          end;

        val crgsss' = map (map (map (build_coiter (un_fold_of fcoiterss') (K I) (K I)))) crgsss;
        val cshsss' = map (map (map (build_coiter (co_rec_of fcoiterss') (curry mk_sumT) (tack z))))
          cshsss;

        val unfold_goalss = map8 (map4 oooo mk_goal pgss) cs cpss gunfolds ns kss ctrss mss crgsss';
        val corec_goalss = map8 (map4 oooo mk_goal phss) cs cpss hcorecs ns kss ctrss mss cshsss';

        val unfold_tacss =
          map3 (map oo mk_coiter_tac unfold_defs nesting_map_ids'')
            (map un_fold_of dtor_coiter_thmss) pre_map_defs ctr_defss;
        val corec_tacss =
          map3 (map oo mk_coiter_tac corec_defs nesting_map_ids'')
            (map co_rec_of dtor_coiter_thmss) pre_map_defs ctr_defss;

        fun prove goal tac =
          Goal.prove_sorry lthy [] [] goal (tac o #context)
          |> Thm.close_derivation;

        val unfold_thmss = map2 (map2 prove) unfold_goalss unfold_tacss;
        val corec_thmss =
          map2 (map2 prove) corec_goalss corec_tacss
          |> map (map (unfold_thms lthy @{thms sum_case_if}));

        val unfold_safesss = map2 (map2 (map2 (curry op =))) crgsss' crgsss;
        val corec_safesss = map2 (map2 (map2 (curry op =))) cshsss' cshsss;

        val filter_safesss =
          map2 (map_filter (fn (safes, thm) => if forall I safes then SOME thm else NONE) oo
            curry (op ~~));

        val safe_unfold_thmss = filter_safesss unfold_safesss unfold_thmss;
        val safe_corec_thmss = filter_safesss corec_safesss corec_thmss;
      in
        (unfold_thmss, corec_thmss, safe_unfold_thmss, safe_corec_thmss)
      end;

    val (disc_unfold_iff_thmss, disc_corec_iff_thmss) =
      let
        fun mk_goal c cps fcoiter n k disc =
          mk_Trueprop_eq (disc $ (fcoiter $ c),
            if n = 1 then @{const True}
            else Library.foldr1 HOLogic.mk_conj (seq_conds mk_maybe_not n k cps));

        val unfold_goalss = map6 (map2 oooo mk_goal) cs cpss gunfolds ns kss discss;
        val corec_goalss = map6 (map2 oooo mk_goal) cs cpss hcorecs ns kss discss;

        fun mk_case_split' cp = Drule.instantiate' [] [SOME (certify lthy cp)] @{thm case_split};

        val case_splitss' = map (map mk_case_split') cpss;

        val unfold_tacss =
          map3 (map oo mk_disc_coiter_iff_tac) case_splitss' unfold_thmss disc_thmsss;
        val corec_tacss =
          map3 (map oo mk_disc_coiter_iff_tac) case_splitss' corec_thmss disc_thmsss;

        fun prove goal tac =
          Goal.prove_sorry lthy [] [] goal (tac o #context)
          |> singleton export_args
          |> singleton (Proof_Context.export names_lthy lthy)
          |> Thm.close_derivation;

        fun proves [_] [_] = []
          | proves goals tacs = map2 prove goals tacs;
      in
        (map2 proves unfold_goalss unfold_tacss, map2 proves corec_goalss corec_tacss)
      end;

    val is_triv_discI = is_triv_implies orf is_concl_refl;

    fun mk_disc_coiter_thms coiters discIs =
      map (op RS) (filter_out (is_triv_discI o snd) (coiters ~~ discIs));

    val disc_unfold_thmss = map2 mk_disc_coiter_thms unfold_thmss discIss;
    val disc_corec_thmss = map2 mk_disc_coiter_thms corec_thmss discIss;

    fun mk_sel_coiter_thm coiter_thm sel sel_thm =
      let
        val (domT, ranT) = dest_funT (fastype_of sel);
        val arg_cong' =
          Drule.instantiate' (map (SOME o certifyT lthy) [domT, ranT])
            [NONE, NONE, SOME (certify lthy sel)] arg_cong
          |> Thm.varifyT_global;
        val sel_thm' = sel_thm RSN (2, trans);
      in
        coiter_thm RS arg_cong' RS sel_thm'
      end;

    fun mk_sel_coiter_thms coiter_thmss =
      map3 (map3 (map2 o mk_sel_coiter_thm)) coiter_thmss selsss sel_thmsss |> map flat;

    val sel_unfold_thmss = mk_sel_coiter_thms unfold_thmss;
    val sel_corec_thmss = mk_sel_coiter_thms corec_thmss;

    val coinduct_consumes_attr = Attrib.internal (K (Rule_Cases.consumes nn));
    val coinduct_case_names_attr = Attrib.internal (K (Rule_Cases.case_names coinduct_cases));
    val coinduct_case_concl_attrs =
      map2 (fn casex => fn concls =>
          Attrib.internal (K (Rule_Cases.case_conclusion (casex, concls))))
        coinduct_cases coinduct_conclss;
    val coinduct_case_attrs =
      coinduct_consumes_attr :: coinduct_case_names_attr :: coinduct_case_concl_attrs;
  in
    ((coinduct_thms_pairs, coinduct_case_attrs),
     (unfold_thmss, corec_thmss, []),
     (safe_unfold_thmss, safe_corec_thmss),
     (disc_unfold_thmss, disc_corec_thmss, simp_attrs),
     (disc_unfold_iff_thmss, disc_corec_iff_thmss, simp_attrs),
     (sel_unfold_thmss, sel_corec_thmss, simp_attrs))
  end;

fun define_co_datatypes prepare_constraint prepare_typ prepare_term fp construct_fp
    (wrap_opts as (no_discs_sels, rep_compat), specs) no_defs_lthy0 =
  let
    (* TODO: sanity checks on arguments *)

    val _ = if fp = Greatest_FP andalso no_discs_sels then
        error "Cannot define codatatypes without discriminators and selectors"
      else
        ();

    fun qualify mandatory fp_b_name =
      Binding.qualify mandatory fp_b_name o (rep_compat ? Binding.qualify false rep_compat_prefix);

    val nn = length specs;
    val fp_bs = map type_binding_of specs;
    val fp_b_names = map Binding.name_of fp_bs;
    val fp_common_name = mk_common_name fp_b_names;
    val map_bs = map2 (fn fp_b_name => qualify false fp_b_name o map_binding_of) fp_b_names specs;
    val rel_bs = map2 (fn fp_b_name => qualify false fp_b_name o rel_binding_of) fp_b_names specs;

    fun prepare_type_arg (_, (ty, c)) =
      let val TFree (s, _) = prepare_typ no_defs_lthy0 ty in
        TFree (s, prepare_constraint no_defs_lthy0 c)
      end;

    val Ass0 = map (map prepare_type_arg o type_args_named_constrained_of) specs;
    val unsorted_Ass0 = map (map (resort_tfree HOLogic.typeS)) Ass0;
    val unsorted_As = Library.foldr1 merge_type_args unsorted_Ass0;
    val set_bss = map (map fst o type_args_named_constrained_of) specs;

    val _ = has_duplicates (op =) unsorted_As andalso
      error ("Duplicate parameters in " ^ co_prefix fp ^ "datatype specification");

    val bad_args =
      map (Logic.type_map (singleton (Variable.polymorphic no_defs_lthy0))) unsorted_As
      |> filter_out Term.is_TVar;
    val _ = null bad_args orelse
      error ("Locally fixed type argument " ^
        quote (Syntax.string_of_typ no_defs_lthy0 (hd bad_args)) ^ " in " ^ co_prefix fp ^
        "datatype specification");

    val (((Bs0, Cs), Xs), no_defs_lthy) =
      no_defs_lthy0
      |> fold (Variable.declare_typ o resort_tfree dummyS) unsorted_As
      |> mk_TFrees (length unsorted_As)
      ||>> mk_TFrees nn
      ||>> variant_tfrees fp_b_names;

    (* TODO: Cleaner handling of fake contexts, without "background_theory". *)

    fun add_fake_type spec =
      (*The "qualify" hack below is for the case where the new type shadows an existing global type
        defined in the same theory.*)
      Sign.add_type no_defs_lthy (qualify false "" (type_binding_of spec),
        length (type_args_named_constrained_of spec), mixfix_of spec);

    val fake_thy = fold add_fake_type specs;
    val fake_lthy = Proof_Context.background_theory fake_thy no_defs_lthy;

    fun mk_fake_T b =
      Type (fst (Term.dest_Type (Proof_Context.read_type_name fake_lthy true (Binding.name_of b))),
        unsorted_As);

    val fake_Ts = map mk_fake_T fp_bs;

    val mixfixes = map mixfix_of specs;

    val _ = (case duplicates Binding.eq_name fp_bs of [] => ()
      | b :: _ => error ("Duplicate type name declaration " ^ quote (Binding.name_of b)));

    val ctr_specss = map ctr_specs_of specs;

    val disc_bindingss = map (map disc_of) ctr_specss;
    val ctr_bindingss =
      map2 (fn fp_b_name => map (qualify false fp_b_name o ctr_of)) fp_b_names ctr_specss;
    val ctr_argsss = map (map args_of) ctr_specss;
    val ctr_mixfixess = map (map ctr_mixfix_of) ctr_specss;

    val sel_bindingsss = map (map (map fst)) ctr_argsss;
    val fake_ctr_Tsss0 = map (map (map (prepare_typ fake_lthy o snd))) ctr_argsss;
    val raw_sel_defaultsss = map (map defaults_of) ctr_specss;

    val (As :: _) :: fake_ctr_Tsss =
      burrow (burrow (Syntax.check_typs fake_lthy)) (Ass0 :: fake_ctr_Tsss0);

    val _ = (case duplicates (op =) unsorted_As of [] => ()
      | A :: _ => error ("Duplicate type parameter " ^
          quote (Syntax.string_of_typ no_defs_lthy A)));

    val rhs_As' = fold (fold (fold Term.add_tfreesT)) fake_ctr_Tsss [];
    val _ = (case subtract (op =) (map dest_TFree As) rhs_As' of
        [] => ()
      | A' :: _ => error ("Extra type variable on right-hand side: " ^
          quote (Syntax.string_of_typ no_defs_lthy (TFree A'))));

    fun eq_fpT_check (T as Type (s, Us)) (Type (s', Us')) =
        s = s' andalso (Us = Us' orelse error ("Illegal occurrence of recursive type " ^
          quote (Syntax.string_of_typ fake_lthy T)))
      | eq_fpT_check _ _ = false;

    fun freeze_fp (T as Type (s, Us)) =
        (case find_index (eq_fpT_check T) fake_Ts of
          ~1 => Type (s, map freeze_fp Us)
        | kk => nth Xs kk)
      | freeze_fp T = T;

    val ctrXs_Tsss = map (map (map freeze_fp)) fake_ctr_Tsss;
    val ctrXs_sum_prod_Ts = map (mk_sumTN_balanced o map HOLogic.mk_tupleT) ctrXs_Tsss;

    val fp_eqs =
      map dest_TFree Xs ~~ map (Term.typ_subst_atomic (As ~~ unsorted_As)) ctrXs_sum_prod_Ts;

    val (pre_bnfs, (fp_res as {bnfs = fp_bnfs as any_fp_bnf :: _, ctors = ctors0, dtors = dtors0,
           xtor_co_iterss = xtor_co_iterss0, xtor_co_induct, dtor_ctors, ctor_dtors, ctor_injects,
           xtor_map_thms, xtor_set_thmss, xtor_rel_thms, xtor_co_iter_thmss, ...}, lthy)) =
      fp_bnf (construct_fp mixfixes map_bs rel_bs set_bss) fp_bs (map dest_TFree unsorted_As) fp_eqs
        no_defs_lthy0;

    val timer = time (Timer.startRealTimer ());

    val nesting_bnfs = nesty_bnfs lthy ctrXs_Tsss As;
    val nested_bnfs = nesty_bnfs lthy ctrXs_Tsss Xs;

    val pre_map_defs = map map_def_of_bnf pre_bnfs;
    val pre_set_defss = map set_defs_of_bnf pre_bnfs;
    val pre_rel_defs = map rel_def_of_bnf pre_bnfs;
    val nesting_set_map's = maps set_map'_of_bnf nesting_bnfs;
    val nested_set_map's = maps set_map'_of_bnf nested_bnfs;

    val live = live_of_bnf any_fp_bnf;
    val _ =
      if live = 0 andalso exists (not o Binding.is_empty) (map_bs @ rel_bs) then
        warning ("Map function and relator names ignored")
      else
        ();

    val Bs =
      map3 (fn alive => fn A as TFree (_, S) => fn B => if alive then resort_tfree S B else A)
        (liveness_of_fp_bnf (length As) any_fp_bnf) As Bs0;

    val B_ify = Term.typ_subst_atomic (As ~~ Bs);

    val ctors = map (mk_ctor As) ctors0;
    val dtors = map (mk_dtor As) dtors0;

    val fpTs = map (domain_type o fastype_of) dtors;

    fun massage_simple_notes base =
      filter_out (null o #2)
      #> map (fn (thmN, thms, attrs) =>
        ((qualify true base (Binding.name thmN), attrs), [(thms, [])]));

    val massage_multi_notes =
      maps (fn (thmN, thmss, attrs) =>
        if forall null thmss then
          []
        else
          map3 (fn fp_b_name => fn Type (T_name, _) => fn thms =>
              ((qualify true fp_b_name (Binding.name thmN), attrs T_name), [(thms, [])]))
            fp_b_names fpTs thmss);

    val ctr_Tsss = map (map (map (Term.typ_subst_atomic (Xs ~~ fpTs)))) ctrXs_Tsss;
    val ns = map length ctr_Tsss;
    val kss = map (fn n => 1 upto n) ns;
    val mss = map (map length) ctr_Tsss;

    val ((xtor_co_iterss, iters_args_types, coiters_args_types), lthy') =
      mk_co_iters_prelims fp fpTs Cs ns mss xtor_co_iterss0 lthy;

    fun define_ctrs_dtrs_for_type (((((((((((((((((((((((fp_bnf, fp_b), fpT), ctor), dtor),
            xtor_co_iters), ctor_dtor), dtor_ctor), ctor_inject), pre_map_def), pre_set_defs),
          pre_rel_def), fp_map_thm), fp_set_thms), fp_rel_thm), n), ks), ms), ctr_bindings),
        ctr_mixfixes), ctr_Tss), disc_bindings), sel_bindingss), raw_sel_defaultss) no_defs_lthy =
      let
        val fp_b_name = Binding.name_of fp_b;

        val dtorT = domain_type (fastype_of ctor);
        val ctr_prod_Ts = map HOLogic.mk_tupleT ctr_Tss;
        val ctr_sum_prod_T = mk_sumTN_balanced ctr_prod_Ts;

        val ((((w, xss), yss), u'), names_lthy) =
          no_defs_lthy
          |> yield_singleton (mk_Frees "w") dtorT
          ||>> mk_Freess "x" ctr_Tss
          ||>> mk_Freess "y" (map (map B_ify) ctr_Tss)
          ||>> yield_singleton Variable.variant_fixes fp_b_name;

        val u = Free (u', fpT);

        val tuple_xs = map HOLogic.mk_tuple xss;
        val tuple_ys = map HOLogic.mk_tuple yss;

        val ctr_rhss =
          map3 (fn k => fn xs => fn tuple_x => fold_rev Term.lambda xs (ctor $
            mk_InN_balanced ctr_sum_prod_T n tuple_x k)) ks xss tuple_xs;

        val ((raw_ctrs, raw_ctr_defs), (lthy', lthy)) = no_defs_lthy
          |> apfst split_list o fold_map3 (fn b => fn mx => fn rhs =>
              Local_Theory.define ((b, mx), ((Thm.def_binding b, []), rhs)) #>> apsnd snd)
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
                      mk_ctor_iff_dtor_tac ctxt (map (SOME o certifyT lthy) [dtorT, fpT])
                        (certify lthy ctor) (certify lthy dtor) ctor_dtor dtor_ctor)
                    |> Thm.close_derivation
                    |> Morphism.thm phi
                  end;

                val sumEN_thm' =
                  unfold_thms lthy @{thms unit_all_eq1}
                    (Drule.instantiate' (map (SOME o certifyT lthy) ctr_prod_Ts) []
                       (mk_sumEN_balanced n))
                  |> Morphism.thm phi;
              in
                mk_exhaust_tac ctxt n ctr_defs ctor_iff_dtor_thm sumEN_thm'
              end;

            val inject_tacss =
              map2 (fn 0 => K [] | _ => fn ctr_def => [fn {context = ctxt, ...} =>
                  mk_inject_tac ctxt ctr_def ctor_inject]) ms ctr_defs;

            val half_distinct_tacss =
              map (map (fn (def, def') => fn {context = ctxt, ...} =>
                mk_half_distinct_tac ctxt ctor_inject [def, def'])) (mk_half_pairss (`I ctr_defs));

            val tacss = [exhaust_tac] :: inject_tacss @ half_distinct_tacss;

            val sel_defaultss = map (map (apsnd (prepare_term lthy))) raw_sel_defaultss
          in
            wrap_free_constructors tacss (((wrap_opts, ctrs0), standard_binding), (disc_bindings,
              (sel_bindingss, sel_defaultss))) lthy
          end;

        fun derive_maps_sets_rels (ctr_sugar, lthy) =
          if live = 0 then
            ((([], [], [], []), ctr_sugar), lthy)
          else
            let
              val rel_flip = rel_flip_of_bnf fp_bnf;
              val nones = replicate live NONE;

              val ctor_cong =
                if fp = Least_FP then
                  Drule.dummy_thm
                else
                  let val ctor' = mk_ctor Bs ctor in
                    cterm_instantiate_pos [NONE, NONE, SOME (certify lthy ctor')] arg_cong
                  end;

              fun mk_cIn ify =
                certify lthy o (fp = Greatest_FP ? curry (op $) (map_types ify ctor)) oo
                mk_InN_balanced (ify ctr_sum_prod_T) n;

              val cxIns = map2 (mk_cIn I) tuple_xs ks;
              val cyIns = map2 (mk_cIn B_ify) tuple_ys ks;

              fun mk_map_thm ctr_def' cxIn =
                fold_thms lthy [ctr_def']
                  (unfold_thms lthy (pre_map_def ::
                       (if fp = Least_FP then [] else [ctor_dtor, dtor_ctor]) @ sum_prod_thms_map)
                     (cterm_instantiate_pos (nones @ [SOME cxIn])
                        (if fp = Least_FP then fp_map_thm else fp_map_thm RS ctor_cong)))
                |> singleton (Proof_Context.export names_lthy no_defs_lthy);

              fun mk_set_thm fp_set_thm ctr_def' cxIn =
                fold_thms lthy [ctr_def']
                  (unfold_thms lthy (pre_set_defs @ nested_set_map's @ nesting_set_map's @
                       (if fp = Least_FP then [] else [dtor_ctor]) @ sum_prod_thms_set)
                     (cterm_instantiate_pos [SOME cxIn] fp_set_thm))
                |> singleton (Proof_Context.export names_lthy no_defs_lthy);

              fun mk_set_thms fp_set_thm = map2 (mk_set_thm fp_set_thm) ctr_defs' cxIns;

              val map_thms = map2 mk_map_thm ctr_defs' cxIns;
              val set_thmss = map mk_set_thms fp_set_thms;

              val rel_infos = (ctr_defs' ~~ cxIns, ctr_defs' ~~ cyIns);

              fun mk_rel_thm postproc ctr_defs' cxIn cyIn =
                fold_thms lthy ctr_defs'
                   (unfold_thms lthy (@{thm Inl_Inr_False} :: pre_rel_def ::
                        (if fp = Least_FP then [] else [dtor_ctor]) @ sum_prod_thms_rel)
                      (cterm_instantiate_pos (nones @ [SOME cxIn, SOME cyIn]) fp_rel_thm))
                |> postproc
                |> singleton (Proof_Context.export names_lthy no_defs_lthy);

              fun mk_rel_inject_thm ((ctr_def', cxIn), (_, cyIn)) =
                mk_rel_thm (unfold_thms lthy @{thms eq_sym_Unity_conv}) [ctr_def'] cxIn cyIn;

              val rel_inject_thms = map mk_rel_inject_thm (op ~~ rel_infos);

              fun mk_half_rel_distinct_thm ((xctr_def', cxIn), (yctr_def', cyIn)) =
                mk_rel_thm (fn thm => thm RS @{thm eq_False[THEN iffD1]}) [xctr_def', yctr_def']
                  cxIn cyIn;

              fun mk_other_half_rel_distinct_thm thm =
                flip_rels lthy live thm
                RS (rel_flip RS sym RS @{thm arg_cong[of _ _ Not]} RS iffD2);

              val half_rel_distinct_thmss =
                map (map mk_half_rel_distinct_thm) (mk_half_pairss rel_infos);
              val other_half_rel_distinct_thmss =
                map (map mk_other_half_rel_distinct_thm) half_rel_distinct_thmss;
              val (rel_distinct_thms, _) =
                join_halves n half_rel_distinct_thmss other_half_rel_distinct_thmss;

              val notes =
                [(mapN, map_thms, code_simp_attrs),
                 (rel_distinctN, rel_distinct_thms, code_simp_attrs),
                 (rel_injectN, rel_inject_thms, code_simp_attrs),
                 (setsN, flat set_thmss, code_simp_attrs)]
                |> massage_simple_notes fp_b_name;
            in
              (((map_thms, rel_inject_thms, rel_distinct_thms, set_thmss), ctr_sugar),
               lthy |> Local_Theory.notes notes |> snd)
            end;

        fun mk_binding suf = qualify false fp_b_name (Binding.suffix_name ("_" ^ suf) fp_b);

        fun massage_res (((maps_sets_rels, ctr_sugar), co_iter_res), lthy) =
          (((maps_sets_rels, (ctrs, xss, ctr_defs, ctr_sugar)), co_iter_res), lthy);
      in
        (wrap_ctrs
         #> derive_maps_sets_rels
         ##>>
           (if fp = Least_FP then define_iters [foldN, recN] (the iters_args_types)
            else define_coiters [unfoldN, corecN] (the coiters_args_types))
             mk_binding fpTs Cs xtor_co_iters
         #> massage_res, lthy')
      end;

    fun wrap_types_etc (wrap_types_etcs, lthy) =
      fold_map I wrap_types_etcs lthy
      |>> apsnd split_list o apfst (apsnd split_list4 o apfst split_list4 o split_list)
        o split_list;

    val mk_simp_thmss =
      map7 (fn {injects, distincts, case_thms, ...} => fn un_folds => fn co_recs =>
        fn mapsx => fn rel_injects => fn rel_distincts => fn setss =>
          injects @ distincts @ case_thms @ co_recs @ un_folds @ mapsx @ rel_injects
          @ rel_distincts @ flat setss);

    fun derive_and_note_induct_iters_thms_for_types
        ((((mapsx, rel_injects, rel_distincts, setss), (ctrss, _, ctr_defss, ctr_sugars)),
          (iterss, iter_defss)), lthy) =
      let
        val ((induct_thms, induct_thm, induct_attrs), (fold_thmss, fold_attrs),
             (rec_thmss, rec_attrs)) =
          derive_induct_iters_thms_for_types pre_bnfs (the iters_args_types) xtor_co_induct
            xtor_co_iter_thmss nesting_bnfs nested_bnfs fpTs Cs Xs ctrXs_Tsss ctrss ctr_defss iterss
            iter_defss lthy;

        val induct_type_attr = Attrib.internal o K o Induct.induct_type;

        val simp_thmss =
          mk_simp_thmss ctr_sugars fold_thmss rec_thmss mapsx rel_injects rel_distincts setss;

        val common_notes =
          (if nn > 1 then [(inductN, [induct_thm], induct_attrs)] else [])
          |> massage_simple_notes fp_common_name;

        val notes =
          [(foldN, fold_thmss, K fold_attrs),
           (inductN, map single induct_thms, fn T_name => induct_attrs @ [induct_type_attr T_name]),
           (recN, rec_thmss, K rec_attrs),
           (simpsN, simp_thmss, K [])]
          |> massage_multi_notes;
      in
        lthy
        |> Local_Theory.notes (common_notes @ notes) |> snd
        |> register_fp_sugars Least_FP pre_bnfs nested_bnfs fp_res ctr_defss ctr_sugars iterss
          [induct_thm] (transpose [fold_thmss, rec_thmss])
      end;

    fun derive_and_note_coinduct_coiters_thms_for_types
        ((((mapsx, rel_injects, rel_distincts, setss), (_, _, ctr_defss, ctr_sugars)),
          (coiterss, coiter_defss)), lthy) =
      let
        val (([(coinduct_thms, coinduct_thm), (strong_coinduct_thms, strong_coinduct_thm)],
              coinduct_attrs),
             (unfold_thmss, corec_thmss, coiter_attrs),
             (safe_unfold_thmss, safe_corec_thmss),
             (disc_unfold_thmss, disc_corec_thmss, disc_coiter_attrs),
             (disc_unfold_iff_thmss, disc_corec_iff_thmss, disc_coiter_iff_attrs),
             (sel_unfold_thmss, sel_corec_thmss, sel_coiter_attrs)) =
          derive_coinduct_coiters_thms_for_types pre_bnfs (the coiters_args_types) xtor_co_induct
            dtor_ctors xtor_co_iter_thmss nesting_bnfs fpTs Cs As kss mss ns ctr_defss ctr_sugars
            coiterss coiter_defss (Proof_Context.export lthy' no_defs_lthy) lthy;

        val coinduct_type_attr = Attrib.internal o K o Induct.coinduct_type;

        fun flat_coiter_thms coiters disc_coiters sel_coiters =
          coiters @ disc_coiters @ sel_coiters;

        val simp_thmss =
          mk_simp_thmss ctr_sugars
            (map3 flat_coiter_thms safe_unfold_thmss disc_unfold_thmss sel_unfold_thmss)
            (map3 flat_coiter_thms safe_corec_thmss disc_corec_thmss sel_corec_thmss)
            mapsx rel_injects rel_distincts setss;

        val anonymous_notes =
          [(flat safe_unfold_thmss @ flat safe_corec_thmss, simp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val common_notes =
          (if nn > 1 then
             [(coinductN, [coinduct_thm], coinduct_attrs),
              (strong_coinductN, [strong_coinduct_thm], coinduct_attrs)]
           else
             [])
          |> massage_simple_notes fp_common_name;

        val notes =
          [(coinductN, map single coinduct_thms,
            fn T_name => coinduct_attrs @ [coinduct_type_attr T_name]),
           (corecN, corec_thmss, K coiter_attrs),
           (disc_corecN, disc_corec_thmss, K disc_coiter_attrs),
           (disc_corec_iffN, disc_corec_iff_thmss, K disc_coiter_iff_attrs),
           (disc_unfoldN, disc_unfold_thmss, K disc_coiter_attrs),
           (disc_unfold_iffN, disc_unfold_iff_thmss, K disc_coiter_iff_attrs),
           (sel_corecN, sel_corec_thmss, K sel_coiter_attrs),
           (sel_unfoldN, sel_unfold_thmss, K sel_coiter_attrs),
           (simpsN, simp_thmss, K []),
           (strong_coinductN, map single strong_coinduct_thms, K coinduct_attrs),
           (unfoldN, unfold_thmss, K coiter_attrs)]
          |> massage_multi_notes;
      in
        lthy
        |> Local_Theory.notes (anonymous_notes @ common_notes @ notes) |> snd
        |> register_fp_sugars Greatest_FP pre_bnfs nested_bnfs fp_res ctr_defss ctr_sugars coiterss
          [coinduct_thm, strong_coinduct_thm] (transpose [unfold_thmss, corec_thmss])
      end;

    val lthy'' = lthy'
      |> fold_map define_ctrs_dtrs_for_type (fp_bnfs ~~ fp_bs ~~ fpTs ~~ ctors ~~ dtors ~~
        xtor_co_iterss ~~ ctor_dtors ~~ dtor_ctors ~~ ctor_injects ~~ pre_map_defs ~~
        pre_set_defss ~~ pre_rel_defs ~~ xtor_map_thms ~~ xtor_set_thmss ~~ xtor_rel_thms ~~ ns ~~
        kss ~~ mss ~~ ctr_bindingss ~~ ctr_mixfixess ~~ ctr_Tsss ~~ disc_bindingss ~~
        sel_bindingsss ~~ raw_sel_defaultsss)
      |> wrap_types_etc
      |> fp_case fp derive_and_note_induct_iters_thms_for_types
           derive_and_note_coinduct_coiters_thms_for_types;

    val timer = time (timer ("Constructors, discriminators, selectors, etc., for the new " ^
      co_prefix fp ^ "datatype"));
  in
    timer; lthy''
  end;

val co_datatypes = define_co_datatypes (K I) (K I) (K I);

val co_datatype_cmd =
  define_co_datatypes Typedecl.read_constraint Syntax.parse_typ Syntax.parse_term;

val parse_ctr_arg =
  @{keyword "("} |-- parse_binding_colon -- Parse.typ --| @{keyword ")"} ||
  (Parse.typ >> pair Binding.empty);

val parse_defaults =
  @{keyword "("} |-- @{keyword "defaults"} |-- Scan.repeat parse_bound_term --| @{keyword ")"};

val parse_type_arg_constrained =
  Parse.type_ident -- Scan.option (@{keyword "::"} |-- Parse.!!! Parse.sort);

val parse_type_arg_named_constrained = parse_opt_binding_colon -- parse_type_arg_constrained;

val parse_type_args_named_constrained =
  parse_type_arg_constrained >> (single o pair Binding.empty) ||
  @{keyword "("} |-- Parse.!!! (Parse.list1 parse_type_arg_named_constrained --| @{keyword ")"}) ||
  Scan.succeed [];

val parse_map_rel_binding = Parse.short_ident --| @{keyword ":"} -- parse_binding;

val no_map_rel = (Binding.empty, Binding.empty);

(* "map" and "rel" are purposedly not registered as keywords, because they are short and nice names
   that we don't want them to be highlighted everywhere. *)
fun extract_map_rel ("map", b) = apfst (K b)
  | extract_map_rel ("rel", b) = apsnd (K b)
  | extract_map_rel (s, _) = error ("Expected \"map\" or \"rel\" instead of " ^ quote s);

val parse_map_rel_bindings =
  @{keyword "("} |-- Scan.repeat parse_map_rel_binding --| @{keyword ")"}
    >> (fn ps => fold extract_map_rel ps no_map_rel) ||
  Scan.succeed no_map_rel;

val parse_ctr_spec =
  parse_opt_binding_colon -- parse_binding -- Scan.repeat parse_ctr_arg --
  Scan.optional parse_defaults [] -- Parse.opt_mixfix;

val parse_spec =
  parse_type_args_named_constrained -- parse_binding -- parse_map_rel_bindings --
  Parse.opt_mixfix -- (@{keyword "="} |-- Parse.enum1 "|" parse_ctr_spec);

val parse_co_datatype = parse_wrap_free_constructors_options -- Parse.and_list1 parse_spec;

fun parse_co_datatype_cmd fp construct_fp = parse_co_datatype >> co_datatype_cmd fp construct_fp;

end;
