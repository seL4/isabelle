(*  Title:      HOL/Tools/BNF/bnf_lfp_rec_sugar.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Recursor sugar ("primrec").
*)

signature BNF_LFP_REC_SUGAR =
sig
  datatype rec_option =
    Plugins_Option of Proof.context -> Plugin_Name.filter |
    Nonexhaustive_Option |
    Transfer_Option

  datatype rec_call =
    No_Rec of int * typ |
    Mutual_Rec of (int * typ) * (int * typ) |
    Nested_Rec of int * typ

  type rec_ctr_spec =
    {ctr: term,
     offset: int,
     calls: rec_call list,
     rec_thm: thm}

  type rec_spec =
    {recx: term,
     fp_nesting_map_ident0s: thm list,
     fp_nesting_map_comps: thm list,
     fp_nesting_pred_maps: thm list,
     ctr_specs: rec_ctr_spec list}

  type basic_lfp_sugar =
    {T: typ,
     fp_res_index: int,
     C: typ,
     fun_arg_Tsss : typ list list list,
     ctr_sugar: Ctr_Sugar.ctr_sugar,
     recx: term,
     rec_thms: thm list};

  type lfp_rec_extension =
    {nested_simps: thm list,
     special_endgame_tac: Proof.context -> thm list -> thm list -> thm list -> tactic,
     is_new_datatype: Proof.context -> string -> bool,
     basic_lfp_sugars_of: binding list -> typ list -> term list ->
       (term * term list list) list list -> local_theory ->
       typ list * int list * basic_lfp_sugar list * thm list * thm list * thm list * thm
       * Token.src list * bool * local_theory,
     rewrite_nested_rec_call: (Proof.context -> (term -> bool) -> (string -> int) -> typ list ->
       term -> term -> term -> term) option};

  val register_lfp_rec_extension: lfp_rec_extension -> theory -> theory
  val default_basic_lfp_sugars_of: binding list -> typ list -> term list ->
    (term * term list list) list list -> local_theory ->
    typ list * int list * basic_lfp_sugar list * thm list * thm list * thm list * thm
    * Token.src list * bool * local_theory
  val rec_specs_of: binding list -> typ list -> typ list -> term list ->
    (term * term list list) list list -> local_theory ->
    (bool * rec_spec list * typ list * thm * thm list * Token.src list * typ list) * local_theory

  val lfp_rec_sugar_interpretation: string ->
    (BNF_FP_Rec_Sugar_Util.fp_rec_sugar -> local_theory -> local_theory) -> theory -> theory

  val primrec: bool -> rec_option list -> (binding * typ option * mixfix) list ->
    Specification.multi_specs -> local_theory ->
    (term list * thm list * thm list list) * local_theory
  val primrec_cmd: bool -> rec_option list -> (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> local_theory ->
    (term list * thm list * thm list list) * local_theory
  val primrec_global: bool -> rec_option list -> (binding * typ option * mixfix) list ->
    Specification.multi_specs -> theory -> (term list * thm list * thm list list) * theory
  val primrec_overloaded: bool -> rec_option list -> (string * (string * typ) * bool) list ->
    (binding * typ option * mixfix) list ->
    Specification.multi_specs -> theory -> (term list * thm list * thm list list) * theory
  val primrec_simple: bool -> ((binding * typ) * mixfix) list -> term list -> local_theory ->
    ((string list * (binding -> binding) list)
     * (term list * thm list * (int list list * thm list list))) * local_theory
end;

structure BNF_LFP_Rec_Sugar : BNF_LFP_REC_SUGAR =
struct

open Ctr_Sugar
open Ctr_Sugar_Util
open Ctr_Sugar_General_Tactics
open BNF_FP_Rec_Sugar_Util

val inductN = "induct";
val simpsN = "simps";

val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};
val nitpicksimp_simp_attrs = nitpicksimp_attrs @ simp_attrs;

exception OLD_PRIMREC of unit;

datatype rec_option =
  Plugins_Option of Proof.context -> Plugin_Name.filter |
  Nonexhaustive_Option |
  Transfer_Option;

datatype rec_call =
  No_Rec of int * typ |
  Mutual_Rec of (int * typ) * (int * typ) |
  Nested_Rec of int * typ;

type rec_ctr_spec =
  {ctr: term,
   offset: int,
   calls: rec_call list,
   rec_thm: thm};

type rec_spec =
  {recx: term,
   fp_nesting_map_ident0s: thm list,
   fp_nesting_map_comps: thm list,
   fp_nesting_pred_maps: thm list,
   ctr_specs: rec_ctr_spec list};

type basic_lfp_sugar =
  {T: typ,
   fp_res_index: int,
   C: typ,
   fun_arg_Tsss : typ list list list,
   ctr_sugar: ctr_sugar,
   recx: term,
   rec_thms: thm list};

type lfp_rec_extension =
  {nested_simps: thm list,
   special_endgame_tac: Proof.context -> thm list -> thm list -> thm list -> tactic,
   is_new_datatype: Proof.context -> string -> bool,
   basic_lfp_sugars_of: binding list -> typ list -> term list ->
     (term * term list list) list list -> local_theory ->
     typ list * int list * basic_lfp_sugar list * thm list * thm list * thm list * thm
     * Token.src list * bool * local_theory,
   rewrite_nested_rec_call: (Proof.context -> (term -> bool) -> (string -> int) -> typ list ->
     term -> term -> term -> term) option};

structure Data = Theory_Data
(
  type T = lfp_rec_extension option;
  val empty = NONE;
  val extend = I;
  val merge = merge_options;
);

val register_lfp_rec_extension = Data.put o SOME;

fun nested_simps ctxt =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME {nested_simps, ...} => nested_simps
  | NONE => []);

fun special_endgame_tac ctxt =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME {special_endgame_tac, ...} => special_endgame_tac ctxt
  | NONE => K (K (K no_tac)));

fun is_new_datatype ctxt =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME {is_new_datatype, ...} => is_new_datatype ctxt
  | NONE => K true);

fun default_basic_lfp_sugars_of _ [Type (arg_T_name, _)] _ _ ctxt =
    let
      val ctr_sugar as {T, ctrs, casex, case_thms, ...} =
        (case ctr_sugar_of ctxt arg_T_name of
          SOME ctr_sugar => ctr_sugar
        | NONE => error ("Unsupported type " ^ quote arg_T_name ^ " at this stage"));

      val C = body_type (fastype_of casex);
      val fun_arg_Tsss = map (map single o binder_types o fastype_of) ctrs;

      val basic_lfp_sugar =
        {T = T, fp_res_index = 0, C = C, fun_arg_Tsss = fun_arg_Tsss, ctr_sugar = ctr_sugar,
         recx = casex, rec_thms = case_thms};
    in
      ([], [0], [basic_lfp_sugar], [], [], [], TrueI (*dummy*), [], false, ctxt)
    end
  | default_basic_lfp_sugars_of _ [T] _ _ ctxt =
    error ("Cannot recurse through type " ^ quote (Syntax.string_of_typ ctxt T))
  | default_basic_lfp_sugars_of _ _ _ _ _ = error "Unsupported mutual recursion at this stage";

fun basic_lfp_sugars_of bs arg_Ts callers callssss lthy =
  (case Data.get (Proof_Context.theory_of lthy) of
    SOME {basic_lfp_sugars_of, ...} => basic_lfp_sugars_of
  | NONE => default_basic_lfp_sugars_of) bs arg_Ts callers callssss lthy;

fun rewrite_nested_rec_call ctxt =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME {rewrite_nested_rec_call = SOME f, ...} => f ctxt
  | _ => error "Unsupported nested recursion");

structure LFP_Rec_Sugar_Plugin = Plugin(type T = fp_rec_sugar);

fun lfp_rec_sugar_interpretation name f =
  LFP_Rec_Sugar_Plugin.interpretation name (fn fp_rec_sugar => fn lthy =>
    f (transfer_fp_rec_sugar (Proof_Context.theory_of lthy) fp_rec_sugar) lthy);

val interpret_lfp_rec_sugar = LFP_Rec_Sugar_Plugin.data;

fun rec_specs_of bs arg_Ts res_Ts callers callssss0 lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val (missing_arg_Ts, perm0_kks, basic_lfp_sugars, fp_nesting_map_ident0s, fp_nesting_map_comps,
         fp_nesting_pred_maps, common_induct, induct_attrs, n2m, lthy) =
      basic_lfp_sugars_of bs arg_Ts callers callssss0 lthy0;

    val perm_basic_lfp_sugars = sort (int_ord o apply2 #fp_res_index) basic_lfp_sugars;

    val indices = map #fp_res_index basic_lfp_sugars;
    val perm_indices = map #fp_res_index perm_basic_lfp_sugars;

    val perm_ctrss = map (#ctrs o #ctr_sugar) perm_basic_lfp_sugars;

    val nn0 = length arg_Ts;
    val nn = length perm_ctrss;
    val kks = 0 upto nn - 1;

    val perm_ctr_offsets = map (fn kk => Integer.sum (map length (take kk perm_ctrss))) kks;

    val perm_fpTs = map #T perm_basic_lfp_sugars;
    val perm_Cs = map #C perm_basic_lfp_sugars;
    val perm_fun_arg_Tssss = map #fun_arg_Tsss perm_basic_lfp_sugars;

    fun unpermute0 perm0_xs = permute_like_unique (op =) perm0_kks kks perm0_xs;
    fun unpermute perm_xs = permute_like_unique (op =) perm_indices indices perm_xs;

    val inducts = unpermute0 (conj_dests nn common_induct);

    val fpTs = unpermute perm_fpTs;
    val Cs = unpermute perm_Cs;
    val ctr_offsets = unpermute perm_ctr_offsets;

    val As_rho = tvar_subst thy (take nn0 fpTs) arg_Ts;
    val Cs_rho = map (fst o dest_TVar) Cs ~~ pad_list HOLogic.unitT nn res_Ts;

    val substA = Term.subst_TVars As_rho;
    val substAT = Term.typ_subst_TVars As_rho;
    val substCT = Term.typ_subst_TVars Cs_rho;
    val substACT = substAT o substCT;

    val perm_Cs' = map substCT perm_Cs;

    fun call_of [i] [T] = (if exists_subtype_in Cs T then Nested_Rec else No_Rec) (i, substACT T)
      | call_of [i, i'] [T, T'] = Mutual_Rec ((i, substACT T), (i', substACT T'));

    fun mk_ctr_spec ctr offset fun_arg_Tss rec_thm =
      let
        val (fun_arg_hss, _) = indexedd fun_arg_Tss 0;
        val fun_arg_hs = flat_rec_arg_args fun_arg_hss;
        val fun_arg_iss = map (map (find_index_eq fun_arg_hs)) fun_arg_hss;
      in
        {ctr = substA ctr, offset = offset, calls = map2 call_of fun_arg_iss fun_arg_Tss,
         rec_thm = rec_thm}
      end;

    fun mk_ctr_specs fp_res_index k ctrs rec_thms =
      @{map 4} mk_ctr_spec ctrs (k upto k + length ctrs - 1) (nth perm_fun_arg_Tssss fp_res_index)
        rec_thms;

    fun mk_spec ctr_offset
        ({T, fp_res_index, ctr_sugar = {ctrs, ...}, recx, rec_thms, ...} : basic_lfp_sugar) =
      {recx = mk_co_rec thy Least_FP perm_Cs' (substAT T) recx,
       fp_nesting_map_ident0s = fp_nesting_map_ident0s, fp_nesting_map_comps = fp_nesting_map_comps,
       fp_nesting_pred_maps = fp_nesting_pred_maps,
       ctr_specs = mk_ctr_specs fp_res_index ctr_offset ctrs rec_thms};
  in
    ((n2m, map2 mk_spec ctr_offsets basic_lfp_sugars, missing_arg_Ts, common_induct, inducts,
      induct_attrs, map #T basic_lfp_sugars), lthy)
  end;

val undef_const = Const (\<^const_name>\<open>undefined\<close>, dummyT);

type eqn_data = {
  fun_name: string,
  rec_type: typ,
  ctr: term,
  ctr_args: term list,
  left_args: term list,
  right_args: term list,
  res_type: typ,
  rhs_term: term,
  user_eqn: term
};

fun dissect_eqn ctxt fun_names eqn0 =
  let
    val eqn = drop_all eqn0 |> HOLogic.dest_Trueprop
      handle TERM _ => ill_formed_equation_lhs_rhs ctxt [eqn0];
    val (lhs, rhs) = HOLogic.dest_eq eqn
      handle TERM _ => ill_formed_equation_lhs_rhs ctxt [eqn];
    val (fun_name, args) = strip_comb lhs
      |>> (fn x => if is_Free x then fst (dest_Free x) else ill_formed_equation_head ctxt [eqn]);
    val (left_args, rest) = chop_prefix is_Free args;
    val (nonfrees, right_args) = chop_suffix is_Free rest;
    val num_nonfrees = length nonfrees;
    val _ = num_nonfrees = 1 orelse
      (if num_nonfrees = 0 then missing_pattern ctxt [eqn]
       else more_than_one_nonvar_in_lhs ctxt [eqn]);
    val _ = member (op =) fun_names fun_name orelse raise ill_formed_equation_head ctxt [eqn];

    val (ctr, ctr_args) = strip_comb (the_single nonfrees);
    val _ = try (num_binder_types o fastype_of) ctr = SOME (length ctr_args) orelse
      partially_applied_ctr_in_pattern ctxt [eqn];

    val _ = check_duplicate_variables_in_lhs ctxt [eqn] (left_args @ ctr_args @ right_args)
    val _ = forall is_Free ctr_args orelse nonprimitive_pattern_in_lhs ctxt [eqn];
    val _ =
      let
        val bads =
          fold_aterms (fn x as Free (v, _) =>
              if (not (member (op =) (left_args @ ctr_args @ right_args) x) andalso
                  not (member (op =) fun_names v) andalso not (Variable.is_fixed ctxt v)) then
                cons x
              else
                I
            | _ => I) rhs [];
      in
        null bads orelse extra_variable_in_rhs ctxt [eqn] (hd bads)
      end;
  in
    {fun_name = fun_name,
     rec_type = body_type (type_of ctr),
     ctr = ctr,
     ctr_args = ctr_args,
     left_args = left_args,
     right_args = right_args,
     res_type = map fastype_of (left_args @ right_args) ---> fastype_of rhs,
     rhs_term = rhs,
     user_eqn = eqn0}
  end;

fun subst_rec_calls ctxt get_ctr_pos has_call ctr_args mutual_calls nested_calls =
  let
    fun try_nested_rec bound_Ts y t =
      AList.lookup (op =) nested_calls y
      |> Option.map (fn y' => rewrite_nested_rec_call ctxt has_call get_ctr_pos bound_Ts y y' t);

    fun subst bound_Ts (t as g' $ y) =
        let
          fun subst_comb (h $ z) = subst bound_Ts h $ subst bound_Ts z
            | subst_comb t = t;

          val y_head = head_of y;
        in
          if not (member (op =) ctr_args y_head) then
            subst_comb t
          else
            (case try_nested_rec bound_Ts y_head t of
              SOME t' => subst_comb t'
            | NONE =>
              let val (g, g_args) = strip_comb g' in
                (case try (get_ctr_pos o fst o dest_Free) g of
                  SOME ~1 => subst_comb t
                | SOME ctr_pos =>
                  (length g_args >= ctr_pos orelse too_few_args_in_rec_call ctxt [] t;
                   (case AList.lookup (op =) mutual_calls y of
                     SOME y' => list_comb (y', map (subst bound_Ts) g_args)
                   | NONE => subst_comb t))
                | NONE => subst_comb t)
              end)
        end
      | subst bound_Ts (Abs (v, T, b)) = Abs (v, T, subst (T :: bound_Ts) b)
      | subst bound_Ts t = try_nested_rec bound_Ts (head_of t) t |> the_default t;

    fun subst' t =
      if has_call t then rec_call_not_apply_to_ctr_arg ctxt [] t
      else try_nested_rec [] (head_of t) t |> the_default t;
  in
    subst' o subst []
  end;

fun build_rec_arg ctxt (funs_data : eqn_data list list) has_call (ctr_spec : rec_ctr_spec)
    (eqn_data_opt : eqn_data option) =
  (case eqn_data_opt of
    NONE => undef_const
  | SOME {ctr_args, left_args, right_args, rhs_term = t, ...} =>
    let
      val calls = #calls ctr_spec;
      val n_args = fold (Integer.add o (fn Mutual_Rec _ => 2 | _ => 1)) calls 0;

      val no_calls' = tag_list 0 calls
        |> map_filter (try (apsnd (fn No_Rec p => p | Mutual_Rec (p, _) => p)));
      val mutual_calls' = tag_list 0 calls
        |> map_filter (try (apsnd (fn Mutual_Rec (_, p) => p)));
      val nested_calls' = tag_list 0 calls
        |> map_filter (try (apsnd (fn Nested_Rec p => p)));

      fun ensure_unique frees t =
        if member (op =) frees t then Free (the_single (Term.variant_frees t [dest_Free t])) else t;

      val args = replicate n_args ("", dummyT)
        |> Term.rename_wrt_term t
        |> map Free
        |> fold (fn (ctr_arg_idx, (arg_idx, _)) =>
            nth_map arg_idx (K (nth ctr_args ctr_arg_idx)))
          no_calls'
        |> fold (fn (ctr_arg_idx, (arg_idx, T)) => fn xs =>
            nth_map arg_idx (K (ensure_unique xs
              (retype_const_or_free T (nth ctr_args ctr_arg_idx)))) xs)
          mutual_calls'
        |> fold (fn (ctr_arg_idx, (arg_idx, T)) =>
            nth_map arg_idx (K (retype_const_or_free T (nth ctr_args ctr_arg_idx))))
          nested_calls';

      val fun_name_ctr_pos_list =
        map (fn (x :: _) => (#fun_name x, length (#left_args x))) funs_data;
      val get_ctr_pos = try (the o AList.lookup (op =) fun_name_ctr_pos_list) #> the_default ~1;
      val mutual_calls = map (map_prod (nth ctr_args) (nth args o fst)) mutual_calls';
      val nested_calls = map (map_prod (nth ctr_args) (nth args o fst)) nested_calls';
    in
      t
      |> subst_rec_calls ctxt get_ctr_pos has_call ctr_args mutual_calls nested_calls
      |> fold_rev lambda (args @ left_args @ right_args)
    end);

fun build_defs ctxt nonexhaustives bs mxs (funs_data : eqn_data list list)
    (rec_specs : rec_spec list) has_call =
  let
    val n_funs = length funs_data;

    val ctr_spec_eqn_data_list' =
      maps (fn ((xs, ys), z) =>
        let
          val zs = replicate (length xs) z;
          val (b, c) = finds (fn ((x, _), y) => #ctr x = #ctr y) (xs ~~ zs) ys;
          val _ = null c orelse excess_equations ctxt (map #rhs_term c);
        in b end) (map #ctr_specs (take n_funs rec_specs) ~~ funs_data ~~ nonexhaustives);

    val (_ : unit list) = ctr_spec_eqn_data_list' |> map (fn (({ctr, ...}, nonexhaustive), x) =>
      if length x > 1 then
        multiple_equations_for_ctr ctxt (map #user_eqn x)
      else if length x = 1 orelse nonexhaustive orelse not (Context_Position.is_visible ctxt) then
        ()
      else
        no_equation_for_ctr_warning ctxt [] ctr);

    val ctr_spec_eqn_data_list =
      map (apfst fst) ctr_spec_eqn_data_list' @
      (drop n_funs rec_specs |> maps #ctr_specs |> map (rpair []));

    val recs = take n_funs rec_specs |> map #recx;
    val rec_args = ctr_spec_eqn_data_list
      |> sort (op < o apply2 (#offset o fst) |> make_ord)
      |> map (uncurry (build_rec_arg ctxt funs_data has_call) o apsnd (try the_single));
    val ctr_poss = map (fn x =>
      if length (distinct (op = o apply2 (length o #left_args)) x) <> 1 then
        inconstant_pattern_pos_for_fun ctxt [] (#fun_name (hd x))
      else
        hd x |> #left_args |> length) funs_data;
  in
    (recs, ctr_poss)
    |-> map2 (fn recx => fn ctr_pos => list_comb (recx, rec_args) |> permute_args ctr_pos)
    |> Syntax.check_terms ctxt
    |> @{map 3} (fn b => fn mx => fn t =>
        ((b, mx), ((Binding.concealed (Thm.def_binding b), []), t)))
      bs mxs
  end;

fun find_rec_calls has_call ({ctr, ctr_args, rhs_term, ...} : eqn_data) =
  let
    fun find bound_Ts (Abs (_, T, b)) ctr_arg = find (T :: bound_Ts) b ctr_arg
      | find bound_Ts (t as _ $ _) ctr_arg =
        let
          val typof = curry fastype_of1 bound_Ts;
          val (f', args') = strip_comb t;
          val n = find_index (equal ctr_arg o head_of) args';
        in
          if n < 0 then
            find bound_Ts f' ctr_arg @ maps (fn x => find bound_Ts x ctr_arg) args'
          else
            let
              val (f, args as arg :: _) = chop n args' |>> curry list_comb f'
              val (arg_head, arg_args) = Term.strip_comb arg;
            in
              if has_call f then
                mk_partial_compN (length arg_args) (typof arg_head) f ::
                maps (fn x => find bound_Ts x ctr_arg) args
              else
                find bound_Ts f ctr_arg @ maps (fn x => find bound_Ts x ctr_arg) args
            end
        end
      | find _ _ _ = [];
  in
    map (find [] rhs_term) ctr_args
    |> (fn [] => NONE | callss => SOME (ctr, callss))
  end;

fun mk_primrec_tac ctxt num_extra_args fp_nesting_map_ident0s fp_nesting_map_comps
    fp_nesting_pred_maps fun_defs recx =
  unfold_thms_tac ctxt fun_defs THEN
  HEADGOAL (rtac ctxt (funpow num_extra_args (fn thm => thm RS fun_cong) recx RS trans)) THEN
  unfold_thms_tac ctxt (nested_simps ctxt @ fp_nesting_map_ident0s @ fp_nesting_map_comps @
    fp_nesting_pred_maps) THEN
  REPEAT_DETERM (HEADGOAL (rtac ctxt refl) ORELSE
    special_endgame_tac ctxt fp_nesting_map_ident0s fp_nesting_map_comps fp_nesting_pred_maps);

fun prepare_primrec plugins nonexhaustives transfers fixes specs lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val (bs, mxs) = map_split (apfst fst) fixes;
    val fun_names = map Binding.name_of bs;
    val qualifys = map (fold_rev (uncurry Binding.qualify o swap) o Binding.path_of) bs;
    val eqns_data = map (dissect_eqn lthy0 fun_names) specs;
    val funs_data = eqns_data
      |> partition_eq (op = o apply2 #fun_name)
      |> finds (fn (x, y) => x = #fun_name (hd y)) fun_names |> fst
      |> map (fn (x, y) => the_single y
        handle List.Empty => missing_equations_for_fun x);

    val frees = map (fst #>> Binding.name_of #> Free) fixes;
    val has_call = exists_subterm (member (op =) frees);
    val arg_Ts = map (#rec_type o hd) funs_data;
    val res_Ts = map (#res_type o hd) funs_data;
    val callssss = funs_data
      |> map (partition_eq (op = o apply2 #ctr))
      |> map (maps (map_filter (find_rec_calls has_call)));

    fun is_only_old_datatype (Type (s, _)) =
        is_some (Old_Datatype_Data.get_info thy s) andalso not (is_new_datatype lthy0 s)
      | is_only_old_datatype _ = false;

    val _ = if exists is_only_old_datatype arg_Ts then raise OLD_PRIMREC () else ();
    val _ = List.app (uncurry (check_top_sort lthy0)) (bs ~~ res_Ts);

    val ((n2m, rec_specs, _, common_induct, inducts, induct_attrs, Ts), lthy) =
      rec_specs_of bs arg_Ts res_Ts frees callssss lthy0;

    val actual_nn = length funs_data;

    val ctrs = maps (map #ctr o #ctr_specs) rec_specs;
    val _ = List.app (fn {ctr, user_eqn, ...} =>
        ignore (member (op =) ctrs ctr orelse not_constructor_in_pattern lthy0 [user_eqn] ctr))
      eqns_data;

    val defs = build_defs lthy nonexhaustives bs mxs funs_data rec_specs has_call;

    fun prove def_thms ({ctr_specs, fp_nesting_map_ident0s, fp_nesting_map_comps,
        fp_nesting_pred_maps, ...} : rec_spec) (fun_data : eqn_data list) lthy' =
      let
        val js =
          find_indices (op = o apply2 (fn {fun_name, ctr, ...} => (fun_name, ctr)))
            fun_data eqns_data;

        val simps = finds (fn (x, y) => #ctr x = #ctr y) fun_data ctr_specs
          |> fst
          |> map_filter (try (fn (x, [y]) =>
            (#user_eqn x, length (#left_args x) + length (#right_args x), #rec_thm y)))
          |> map (fn (user_eqn, num_extra_args, rec_thm) =>
              Goal.prove_sorry lthy' [] [] user_eqn
                (fn {context = ctxt, prems = _} =>
                  mk_primrec_tac ctxt num_extra_args fp_nesting_map_ident0s fp_nesting_map_comps
                    fp_nesting_pred_maps def_thms rec_thm)
              |> Thm.close_derivation \<^here>);
      in
        ((js, simps), lthy')
      end;

    val notes =
      (if n2m then
         @{map 3} (fn name => fn qualify => fn thm => (name, qualify, inductN, [thm], induct_attrs))
         fun_names qualifys (take actual_nn inducts)
       else
         [])
      |> map (fn (prefix, qualify, thmN, thms, attrs) =>
        ((qualify (Binding.qualify true prefix (Binding.name thmN)), attrs), [(thms, [])]));

    val common_name = mk_common_name fun_names;
    val common_qualify = fold_rev I qualifys;

    val common_notes =
      (if n2m then [(inductN, [common_induct], [])] else [])
      |> map (fn (thmN, thms, attrs) =>
        ((common_qualify (Binding.qualify true common_name (Binding.name thmN)), attrs),
          [(thms, [])]));
  in
    (((fun_names, qualifys, arg_Ts, defs),
      fn lthy => fn defs =>
        let
          val def_thms = map (snd o snd) defs;
          val ts = map fst defs;
          val phi = Local_Theory.target_morphism lthy;
          val fp_rec_sugar =
            {transfers = transfers, fun_names = fun_names, funs = map (Morphism.term phi) ts,
             fun_defs = Morphism.fact phi def_thms, fpTs = take actual_nn Ts};
        in
          map_prod split_list (interpret_lfp_rec_sugar plugins fp_rec_sugar)
            (@{fold_map 2} (prove (map (snd o snd) defs)) (take actual_nn rec_specs) funs_data lthy)
        end),
      lthy |> Local_Theory.notes (notes @ common_notes) |> snd)
  end;

fun primrec_simple0 int plugins nonexhaustive transfer fixes ts lthy =
  let
    val _ = check_duplicate_const_names (map (fst o fst) fixes);

    val actual_nn = length fixes;

    val nonexhaustives = replicate actual_nn nonexhaustive;
    val transfers = replicate actual_nn transfer;

    val (((names, qualifys, arg_Ts, defs), prove), lthy') =
      prepare_primrec plugins nonexhaustives transfers fixes ts lthy;
  in
    lthy'
    |> fold_map Local_Theory.define defs
    |> tap (uncurry (print_def_consts int))
    |-> (fn defs => fn lthy =>
      let
        val ((jss, simpss), lthy) = prove lthy defs;
        val res =
          {prefix = (names, qualifys),
           types = map (#1 o dest_Type) arg_Ts,
           result = (map fst defs, map (snd o snd) defs, (jss, simpss))};
      in (res, lthy) end)
  end;

fun primrec_simple int fixes ts lthy =
  primrec_simple0 int Plugin_Name.default_filter false false fixes ts lthy
    |>> (fn {prefix, result, ...} => (prefix, result))
  handle OLD_PRIMREC () =>
    Old_Primrec.primrec_simple int fixes ts lthy
    |>> (fn {prefix, result = (ts, thms), ...} =>
          (map_split (rpair I) [prefix], (ts, [], ([], [thms]))))

fun gen_primrec old_primrec prep_spec int opts raw_fixes raw_specs lthy =
  let
    val plugins = get_first (fn Plugins_Option f => SOME (f lthy) | _ => NONE) (rev opts)
      |> the_default Plugin_Name.default_filter;
    val nonexhaustive = exists (can (fn Nonexhaustive_Option => ())) opts;
    val transfer = exists (can (fn Transfer_Option => ())) opts;

    val (fixes, specs) = fst (prep_spec raw_fixes raw_specs lthy);
    val spec_name = Binding.conglomerate (map (#1 o #1) fixes);

    val mk_notes =
      flat oooo @{map 4} (fn js => fn prefix => fn qualify => fn thms =>
        let
          val (bs, attrss) = map_split (fst o nth specs) js;
          val notes =
            @{map 3} (fn b => fn attrs => fn thm =>
                ((Binding.qualify false prefix b, nitpicksimp_simp_attrs @ attrs),
                 [([thm], [])]))
              bs attrss thms;
        in
          ((qualify (Binding.qualify true prefix (Binding.name simpsN)), []), [(thms, [])]) :: notes
        end);
  in
    lthy
    |> primrec_simple0 int plugins nonexhaustive transfer fixes (map snd specs)
    |-> (fn {prefix = (names, qualifys), types, result = (ts, defs, (jss, simpss))} =>
      Spec_Rules.add spec_name (Spec_Rules.equational_primrec types) ts (flat simpss)
      #> Local_Theory.notes (mk_notes jss names qualifys simpss)
      #-> (fn notes =>
        plugins code_plugin ? Code.declare_default_eqns (map (rpair true) (maps snd notes))
        #> pair (ts, defs, map_filter (fn ("", _) => NONE | (_, thms) => SOME thms) notes)))
  end
  handle OLD_PRIMREC () =>
    old_primrec int raw_fixes raw_specs lthy
    |>> (fn {result = (ts, thms), ...} => (ts, [], [thms]));

val primrec = gen_primrec Old_Primrec.primrec Specification.check_multi_specs;
val primrec_cmd = gen_primrec Old_Primrec.primrec_cmd Specification.read_multi_specs;

fun primrec_global int opts fixes specs =
  Named_Target.theory_init
  #> primrec int opts fixes specs
  ##> Local_Theory.exit_global;

fun primrec_overloaded int opts ops fixes specs =
  Overloading.overloading ops
  #> primrec int opts fixes specs
  ##> Local_Theory.exit_global;

val rec_option_parser = Parse.group (K "option")
  (Plugin_Name.parse_filter >> Plugins_Option
   || Parse.reserved "nonexhaustive" >> K Nonexhaustive_Option
   || Parse.reserved "transfer" >> K Transfer_Option);

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>primrec\<close>
  "define primitive recursive functions"
  ((Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 rec_option_parser)
      --| \<^keyword>\<open>)\<close>) []) -- Parse_Spec.specification
    >> (fn (opts, (fixes, specs)) => snd o primrec_cmd true opts fixes specs));

end;
