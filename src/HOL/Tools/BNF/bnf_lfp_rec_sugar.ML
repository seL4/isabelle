(*  Title:      HOL/Tools/BNF/bnf_lfp_rec_sugar.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Recursor sugar ("primrec").
*)

signature BNF_LFP_REC_SUGAR =
sig
  datatype primrec_option = Nonexhaustive_Option

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
     is_new_datatype: Proof.context -> string -> bool,
     get_basic_lfp_sugars: binding list -> typ list -> term list ->
       (term * term list list) list list -> local_theory ->
       typ list * int list * basic_lfp_sugar list * thm list * thm list * thm * Token.src list
       * bool * local_theory,
     rewrite_nested_rec_call: Proof.context -> (term -> bool) -> (string -> int) -> typ list ->
       term -> term -> term -> term};

  exception PRIMREC of string * term list;

  val register_lfp_rec_extension: lfp_rec_extension -> theory -> theory
  val rec_specs_of: binding list -> typ list -> typ list -> term list ->
    (term * term list list) list list -> local_theory ->
    (bool * rec_spec list * typ list * thm * thm list * Token.src list) * local_theory

  val add_primrec: (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> local_theory -> (term list * thm list list) * local_theory
  val add_primrec_cmd: primrec_option list -> (binding * string option * mixfix) list ->
    (Attrib.binding * string) list -> local_theory -> (term list * thm list list) * local_theory
  val add_primrec_global: (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> theory -> (term list * thm list list) * theory
  val add_primrec_overloaded: (string * (string * typ) * bool) list ->
    (binding * typ option * mixfix) list ->
    (Attrib.binding * term) list -> theory -> (term list * thm list list) * theory
  val add_primrec_simple: ((binding * typ) * mixfix) list -> term list ->
    local_theory -> (string list * (term list * (int list list * thm list list))) * local_theory
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
val code_nitpicksimp_simp_attrs = Code.add_default_eqn_attrib :: nitpicksimp_attrs @ simp_attrs;

exception OLD_PRIMREC of unit;
exception PRIMREC of string * term list;

datatype primrec_option = Nonexhaustive_Option;

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
   is_new_datatype: Proof.context -> string -> bool,
   get_basic_lfp_sugars: binding list -> typ list -> term list ->
     (term * term list list) list list -> local_theory ->
     typ list * int list * basic_lfp_sugar list * thm list * thm list * thm * Token.src list * bool
     * local_theory,
   rewrite_nested_rec_call: Proof.context -> (term -> bool) -> (string -> int) -> typ list ->
     term -> term -> term -> term};

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

fun is_new_datatype ctxt =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME {is_new_datatype, ...} => is_new_datatype ctxt
  | NONE => K false);

fun get_basic_lfp_sugars bs arg_Ts callers callssss lthy =
  (case Data.get (Proof_Context.theory_of lthy) of
    SOME {get_basic_lfp_sugars, ...} => get_basic_lfp_sugars bs arg_Ts callers callssss lthy
  | NONE => error "Functionality not loaded yet");

fun rewrite_nested_rec_call ctxt =
  (case Data.get (Proof_Context.theory_of ctxt) of
    SOME {rewrite_nested_rec_call, ...} => rewrite_nested_rec_call ctxt);

fun rec_specs_of bs arg_Ts res_Ts callers callssss0 lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val (missing_arg_Ts, perm0_kks, basic_lfp_sugars, fp_nesting_map_ident0s, fp_nesting_map_comps,
         common_induct, induct_attrs, n2m, lthy) =
      get_basic_lfp_sugars bs arg_Ts callers callssss0 lthy0;

    val perm_basic_lfp_sugars = sort (int_ord o pairself #fp_res_index) basic_lfp_sugars;

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
      map4 mk_ctr_spec ctrs (k upto k + length ctrs - 1) (nth perm_fun_arg_Tssss fp_res_index)
        rec_thms;

    fun mk_spec ctr_offset
        ({T, fp_res_index, ctr_sugar = {ctrs, ...}, recx, rec_thms, ...} : basic_lfp_sugar) =
      {recx = mk_co_rec thy Least_FP perm_Cs' (substAT T) recx,
       fp_nesting_map_ident0s = fp_nesting_map_ident0s, fp_nesting_map_comps = fp_nesting_map_comps,
       ctr_specs = mk_ctr_specs fp_res_index ctr_offset ctrs rec_thms};
  in
    ((n2m, map2 mk_spec ctr_offsets basic_lfp_sugars, missing_arg_Ts, common_induct, inducts,
      induct_attrs), lthy)
  end;

val undef_const = Const (@{const_name undefined}, dummyT);

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

fun dissect_eqn ctxt fun_names eqn' =
  let
    val eqn = drop_all eqn' |> HOLogic.dest_Trueprop
      handle TERM _ =>
             raise PRIMREC ("malformed function equation (expected \"lhs = rhs\")", [eqn']);
    val (lhs, rhs) = HOLogic.dest_eq eqn
        handle TERM _ =>
               raise PRIMREC ("malformed function equation (expected \"lhs = rhs\")", [eqn']);
    val (fun_name, args) = strip_comb lhs
      |>> (fn x => if is_Free x then fst (dest_Free x)
          else raise PRIMREC ("malformed function equation (does not start with free)", [eqn]));
    val (left_args, rest) = take_prefix is_Free args;
    val (nonfrees, right_args) = take_suffix is_Free rest;
    val num_nonfrees = length nonfrees;
    val _ = num_nonfrees = 1 orelse if num_nonfrees = 0 then
      raise PRIMREC ("constructor pattern missing in left-hand side", [eqn]) else
      raise PRIMREC ("more than one non-variable argument in left-hand side", [eqn]);
    val _ = member (op =) fun_names fun_name orelse
      raise PRIMREC ("malformed function equation (does not start with function name)", [eqn]);

    val (ctr, ctr_args) = strip_comb (the_single nonfrees);
    val _ = try (num_binder_types o fastype_of) ctr = SOME (length ctr_args) orelse
      raise PRIMREC ("partially applied constructor in pattern", [eqn]);
    val _ = let val d = duplicates (op =) (left_args @ ctr_args @ right_args) in null d orelse
      raise PRIMREC ("duplicate variable \"" ^ Syntax.string_of_term ctxt (hd d) ^
        "\" in left-hand side", [eqn]) end;
    val _ = forall is_Free ctr_args orelse
      raise PRIMREC ("non-primitive pattern in left-hand side", [eqn]);
    val _ =
      let
        val b =
          fold_aterms (fn x as Free (v, _) =>
              if (not (member (op =) (left_args @ ctr_args @ right_args) x) andalso
                  not (member (op =) fun_names v) andalso not (Variable.is_fixed ctxt v)) then
                cons x
              else
                I
            | _ => I) rhs [];
      in
        null b orelse
        raise PRIMREC ("extra variable(s) in right-hand side: " ^
          commas (map (Syntax.string_of_term ctxt) b), [eqn])
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
     user_eqn = eqn'}
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
                  (length g_args >= ctr_pos orelse
                   raise PRIMREC ("too few arguments in recursive call", [t]);
                   (case AList.lookup (op =) mutual_calls y of
                     SOME y' => list_comb (y', map (subst bound_Ts) g_args)
                   | NONE => subst_comb t))
                | NONE => subst_comb t)
              end)
        end
      | subst bound_Ts (Abs (v, T, b)) = Abs (v, T, subst (T :: bound_Ts) b)
      | subst _ t = t

    fun subst' t =
      if has_call t then
        raise PRIMREC ("recursive call not directly applied to constructor argument", [t])
      else
        try_nested_rec [] (head_of t) t |> the_default t;
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

fun build_defs ctxt nonexhaustive bs mxs (funs_data : eqn_data list list)
    (rec_specs : rec_spec list) has_call =
  let
    val n_funs = length funs_data;

    val ctr_spec_eqn_data_list' =
      map #ctr_specs (take n_funs rec_specs) ~~ funs_data
      |> maps (uncurry (finds (fn (x, y) => #ctr x = #ctr y))
        ##> (fn x => null x orelse
          raise PRIMREC ("excess equations in definition", map #rhs_term x)) #> fst);
    val _ = ctr_spec_eqn_data_list' |> map (fn ({ctr, ...}, x) =>
      if length x > 1 then raise PRIMREC ("multiple equations for constructor", map #user_eqn x)
      else if length x = 1 orelse nonexhaustive then ()
      else warning ("no equation for constructor " ^ Syntax.string_of_term ctxt ctr));

    val ctr_spec_eqn_data_list =
      ctr_spec_eqn_data_list' @ (drop n_funs rec_specs |> maps #ctr_specs |> map (rpair []));

    val recs = take n_funs rec_specs |> map #recx;
    val rec_args = ctr_spec_eqn_data_list
      |> sort (op < o pairself (#offset o fst) |> make_ord)
      |> map (uncurry (build_rec_arg ctxt funs_data has_call) o apsnd (try the_single));
    val ctr_poss = map (fn x =>
      if length (distinct (op = o pairself (length o #left_args)) x) <> 1 then
        raise PRIMREC ("inconstant constructor pattern position for function " ^
          quote (#fun_name (hd x)), [])
      else
        hd x |> #left_args |> length) funs_data;
  in
    (recs, ctr_poss)
    |-> map2 (fn recx => fn ctr_pos => list_comb (recx, rec_args) |> permute_args ctr_pos)
    |> Syntax.check_terms ctxt
    |> map3 (fn b => fn mx => fn t => ((b, mx), ((Binding.conceal (Thm.def_binding b), []), t)))
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

fun mk_primrec_tac ctxt num_extra_args map_ident0s map_comps fun_defs recx =
  unfold_thms_tac ctxt fun_defs THEN
  HEADGOAL (rtac (funpow num_extra_args (fn thm => thm RS fun_cong) recx RS trans)) THEN
  unfold_thms_tac ctxt (nested_simps ctxt @ map_ident0s @ map_comps) THEN
  HEADGOAL (rtac refl);

fun prepare_primrec nonexhaustive fixes specs lthy0 =
  let
    val thy = Proof_Context.theory_of lthy0;

    val (bs, mxs) = map_split (apfst fst) fixes;
    val fun_names = map Binding.name_of bs;
    val eqns_data = map (dissect_eqn lthy0 fun_names) specs;
    val funs_data = eqns_data
      |> partition_eq (op = o pairself #fun_name)
      |> finds (fn (x, y) => x = #fun_name (hd y)) fun_names |> fst
      |> map (fn (x, y) => the_single y
          handle List.Empty => raise PRIMREC ("missing equations for function " ^ quote x, []));

    val frees = map (fst #>> Binding.name_of #> Free) fixes;
    val has_call = exists_subterm (member (op =) frees);
    val arg_Ts = map (#rec_type o hd) funs_data;
    val res_Ts = map (#res_type o hd) funs_data;
    val callssss = funs_data
      |> map (partition_eq (op = o pairself #ctr))
      |> map (maps (map_filter (find_rec_calls has_call)));

    fun is_only_old_datatype (Type (s, _)) =
        is_some (Old_Datatype_Data.get_info thy s) andalso not (is_new_datatype lthy0 s)
      | is_only_old_datatype _ = false;

    val _ = if exists is_only_old_datatype arg_Ts then raise OLD_PRIMREC () else ();
    val _ = (case filter_out (fn (_, T) => Sign.of_sort thy (T, @{sort type})) (bs ~~ res_Ts) of
        [] => ()
      | (b, _) :: _ => raise PRIMREC ("type of " ^ Binding.print b ^ " contains top sort", []));

    val ((n2m, rec_specs, _, common_induct, inducts, induct_attrs), lthy) =
      rec_specs_of bs arg_Ts res_Ts frees callssss lthy0;

    val actual_nn = length funs_data;

    val ctrs = maps (map #ctr o #ctr_specs) rec_specs;
    val _ =
      map (fn {ctr, user_eqn, ...} => member (op =) ctrs ctr orelse
        raise PRIMREC ("argument " ^ quote (Syntax.string_of_term lthy ctr) ^
          " is not a constructor in left-hand side", [user_eqn])) eqns_data;

    val defs = build_defs lthy nonexhaustive bs mxs funs_data rec_specs has_call;

    fun prove lthy' def_thms' ({ctr_specs, fp_nesting_map_ident0s, fp_nesting_map_comps, ...}
        : rec_spec) (fun_data : eqn_data list) =
      let
        val js =
          find_indices (op = o pairself (fn {fun_name, ctr, ...} => (fun_name, ctr)))
            fun_data eqns_data;

        val def_thms = map (snd o snd) def_thms';
        val simp_thms = finds (fn (x, y) => #ctr x = #ctr y) fun_data ctr_specs
          |> fst
          |> map_filter (try (fn (x, [y]) =>
            (#fun_name x, #user_eqn x, length (#left_args x) + length (#right_args x), #rec_thm y)))
          |> map2 (fn j => fn (fun_name, user_eqn, num_extra_args, rec_thm) =>
              mk_primrec_tac lthy' num_extra_args fp_nesting_map_ident0s fp_nesting_map_comps
                def_thms rec_thm
              |> K |> Goal.prove_sorry lthy' [] [] user_eqn
              |> singleton (Proof_Context.export lthy' lthy)
              (* for code extraction from proof terms: *)
              |> Thm.name_derivation (Sign.full_name thy (Binding.name fun_name) ^
                Long_Name.separator ^ simpsN ^
                (if js = [0] then "" else "_" ^ string_of_int (j + 1))))
            js;
      in
        (js, simp_thms)
      end;

    val notes =
      (if n2m then
         map2 (fn name => fn thm => (name, inductN, [thm], induct_attrs)) fun_names
           (take actual_nn inducts)
       else
         [])
      |> map (fn (prefix, thmN, thms, attrs) =>
        ((Binding.qualify true prefix (Binding.name thmN), attrs), [(thms, [])]));

    val common_name = mk_common_name fun_names;

    val common_notes =
      (if n2m then [(inductN, [common_induct], [])] else [])
      |> map (fn (thmN, thms, attrs) =>
        ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));
  in
    (((fun_names, defs),
      fn lthy => fn defs =>
        split_list (map2 (prove lthy defs) (take actual_nn rec_specs) funs_data)),
      lthy |> Local_Theory.notes (notes @ common_notes) |> snd)
  end;

fun add_primrec_simple' opts fixes ts lthy =
  let
    val nonexhaustive = member (op =) opts Nonexhaustive_Option;
    val (((names, defs), prove), lthy') = prepare_primrec nonexhaustive fixes ts lthy
      handle ERROR str => raise PRIMREC (str, []);
  in
    lthy'
    |> fold_map Local_Theory.define defs
    |-> (fn defs => `(fn lthy => (names, (map fst defs, prove lthy defs))))
  end
  handle PRIMREC (str, eqns) =>
         if null eqns then
           error ("primrec error:\n  " ^ str)
         else
           error ("primrec error:\n  " ^ str ^ "\nin\n  " ^
             space_implode "\n  " (map (quote o Syntax.string_of_term lthy) eqns));

fun add_primrec_simple fixes ts lthy =
  add_primrec_simple' [] fixes ts lthy
  handle OLD_PRIMREC () =>
    Old_Primrec.add_primrec_simple fixes ts lthy
    |>> apsnd (apsnd (pair [] o single)) o apfst single;

fun gen_primrec old_primrec prep_spec opts
    (raw_fixes : (binding * 'a option * mixfix) list) raw_specs lthy =
  let
    val d = duplicates (op =) (map (Binding.name_of o #1) raw_fixes)
    val _ = null d orelse raise PRIMREC ("duplicate function name(s): " ^ commas d, []);

    val (fixes, specs) = fst (prep_spec raw_fixes raw_specs lthy);

    val mk_notes =
      flat ooo map3 (fn js => fn prefix => fn thms =>
        let
          val (bs, attrss) = map_split (fst o nth specs) js;
          val notes =
            map3 (fn b => fn attrs => fn thm =>
                ((Binding.qualify false prefix b, code_nitpicksimp_simp_attrs @ attrs),
                 [([thm], [])]))
              bs attrss thms;
        in
          ((Binding.qualify true prefix (Binding.name simpsN), []), [(thms, [])]) :: notes
        end);
  in
    lthy
    |> add_primrec_simple' opts fixes (map snd specs)
    |-> (fn (names, (ts, (jss, simpss))) =>
      Spec_Rules.add Spec_Rules.Equational (ts, flat simpss)
      #> Local_Theory.notes (mk_notes jss names simpss)
      #>> pair ts o map snd)
  end
  handle OLD_PRIMREC () => old_primrec raw_fixes raw_specs lthy |>> apsnd single;

val add_primrec = gen_primrec Old_Primrec.add_primrec Specification.check_spec [];
val add_primrec_cmd = gen_primrec Old_Primrec.add_primrec_cmd Specification.read_spec;

fun add_primrec_global fixes specs =
  Named_Target.theory_init
  #> add_primrec fixes specs
  ##> Local_Theory.exit_global;

fun add_primrec_overloaded ops fixes specs =
  Overloading.overloading ops
  #> add_primrec fixes specs
  ##> Local_Theory.exit_global;

val primrec_option_parser = Parse.group (fn () => "option")
  (Parse.reserved "nonexhaustive" >> K Nonexhaustive_Option)

val _ = Outer_Syntax.local_theory @{command_spec "primrec"}
  "define primitive recursive functions"
  ((Scan.optional (@{keyword "("} |--
      Parse.!!! (Parse.list1 primrec_option_parser) --| @{keyword ")"}) []) --
    (Parse.fixes -- Parse_Spec.where_alt_specs)
    >> (fn (opts, (fixes, specs)) => snd o add_primrec_cmd opts fixes specs));

end;
