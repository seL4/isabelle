(*  Title:      HOL/Tools/BNF/bnf_lfp_compat.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013, 2014

Compatibility layer with the old datatype package. Partly based on

    Title:      HOL/Tools/Old_Datatype/old_datatype_data.ML
    Author:     Stefan Berghofer, TU Muenchen
*)

signature BNF_LFP_COMPAT =
sig
  datatype preference = Keep_Nesting | Include_GFPs | Kill_Type_Args

  val get_all: theory -> preference list -> Old_Datatype_Aux.info Symtab.table
  val get_info: theory -> preference list -> string -> Old_Datatype_Aux.info option
  val the_info: theory -> preference list -> string -> Old_Datatype_Aux.info
  val the_spec: theory -> string -> (string * sort) list * (string * typ list) list
  val the_descr: theory -> preference list -> string list ->
    Old_Datatype_Aux.descr * (string * sort) list * string list * string
    * (string list * string list) * (typ list * typ list)
  val get_constrs: theory -> string -> (string * typ) list option
  val interpretation: string -> preference list ->
    (Old_Datatype_Aux.config -> string list -> theory -> theory) -> theory -> theory
  val datatype_compat: string list -> local_theory -> local_theory
  val datatype_compat_global: string list -> theory -> theory
  val datatype_compat_cmd: string list -> local_theory -> local_theory
  val add_datatype: preference list -> Old_Datatype_Aux.spec list -> theory -> string list * theory
  val primrec: (binding * typ option * mixfix) list -> Specification.multi_specs ->
    local_theory -> (term list * thm list) * local_theory
  val primrec_global: (binding * typ option * mixfix) list ->
    Specification.multi_specs -> theory -> (term list * thm list) * theory
  val primrec_overloaded: (string * (string * typ) * bool) list ->
    (binding * typ option * mixfix) list -> Specification.multi_specs -> theory ->
    (term list * thm list) * theory
  val primrec_simple: ((binding * typ) * mixfix) list -> term list ->
    local_theory -> (string list * (term list * thm list)) * local_theory
end;

structure BNF_LFP_Compat : BNF_LFP_COMPAT =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Tactics
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar
open BNF_LFP

val compat_N = "compat_";
val rec_split_N = "rec_split_";

datatype preference = Keep_Nesting | Include_GFPs | Kill_Type_Args;

fun mk_split_rec_rhs ctxt fpTs Cs (recs as rec1 :: _) =
  let
    fun repair_rec_arg_args [] [] = []
      | repair_rec_arg_args ((g_T as Type (\<^type_name>\<open>fun\<close>, _)) :: g_Ts) (g :: gs) =
        let
          val (x_Ts, body_T) = strip_type g_T;
        in
          (case try HOLogic.dest_prodT body_T of
            NONE => [g]
          | SOME (fst_T, _) =>
            if member (op =) fpTs fst_T then
              let val (xs, _) = mk_Frees "x" x_Ts ctxt in
                map (fn mk_proj => fold_rev Term.lambda xs (mk_proj (Term.list_comb (g, xs))))
                  [HOLogic.mk_fst, HOLogic.mk_snd]
              end
            else
              [g])
          :: repair_rec_arg_args g_Ts gs
        end
      | repair_rec_arg_args (g_T :: g_Ts) (g :: gs) =
        if member (op =) fpTs g_T then
          let
            val j = find_index (member (op =) Cs) g_Ts;
            val h = nth gs j;
            val g_Ts' = nth_drop j g_Ts;
            val gs' = nth_drop j gs;
          in
            [g, h] :: repair_rec_arg_args g_Ts' gs'
          end
        else
          [g] :: repair_rec_arg_args g_Ts gs;

    fun repair_back_rec_arg f_T f' =
      let
        val g_Ts = Term.binder_types f_T;
        val (gs, _) = mk_Frees "g" g_Ts ctxt;
      in
        fold_rev Term.lambda gs (Term.list_comb (f',
          flat_rec_arg_args (repair_rec_arg_args g_Ts gs)))
      end;

    val f_Ts = binder_fun_types (fastype_of rec1);
    val (fs', _) = mk_Frees "f" (replicate (length f_Ts) Term.dummyT) ctxt;

    fun mk_rec' recx =
      fold_rev Term.lambda fs' (Term.list_comb (recx, map2 repair_back_rec_arg f_Ts fs'))
      |> Syntax.check_term ctxt;
  in
    map mk_rec' recs
  end;

fun define_split_recs fpTs Cs recs lthy =
  let
    val b_names = Name.variant_list [] (map base_name_of_typ fpTs);

    fun mk_binding b_name =
      Binding.qualify true (compat_N ^ b_name)
        (Binding.prefix_name rec_split_N (Binding.name b_name));

    val bs = map mk_binding b_names;
    val rhss = mk_split_rec_rhs lthy fpTs Cs recs;
  in
    @{fold_map 3} (define_co_rec_as Least_FP Cs) fpTs bs rhss lthy
  end;

fun mk_split_rec_thmss ctxt Xs ctrXs_Tsss ctrss rec0_thmss (recs as rec1 :: _) rec_defs =
  let
    val f_Ts = binder_fun_types (fastype_of rec1);
    val (fs, _) = mk_Frees "f" f_Ts ctxt;
    val frecs = map (fn recx => Term.list_comb (recx, fs)) recs;

    val Xs_frecs = Xs ~~ frecs;
    val fss = unflat ctrss fs;

    fun mk_rec_call g n (Type (\<^type_name>\<open>fun\<close>, [_, ran_T])) =
        Abs (Name.uu, Term.dummyT, mk_rec_call g (n + 1) ran_T)
      | mk_rec_call g n X =
        let
          val frec = the (AList.lookup (op =) Xs_frecs X);
          val xg = Term.list_comb (g, map Bound (n - 1 downto 0));
        in frec $ xg end;

    fun mk_rec_arg_arg ctrXs_T g =
      g :: (if member (op =) Xs (body_type ctrXs_T) then [mk_rec_call g 0 ctrXs_T] else []);

    fun mk_goal frec ctrXs_Ts ctr f =
      let
        val ctr_Ts = binder_types (fastype_of ctr);
        val (gs, _) = mk_Frees "g" ctr_Ts ctxt;
        val gctr = Term.list_comb (ctr, gs);
        val fgs = flat_rec_arg_args (map2 mk_rec_arg_arg ctrXs_Ts gs);
      in
        fold_rev (fold_rev Logic.all) [fs, gs]
          (mk_Trueprop_eq (frec $ gctr, Term.list_comb (f, fgs)))
        |> Syntax.check_term ctxt
      end;

    val goalss = @{map 4} (@{map 3} o mk_goal) frecs ctrXs_Tsss ctrss fss;

    fun tac ctxt =
      unfold_thms_tac ctxt (@{thms o_apply fst_conv snd_conv} @ rec_defs @ flat rec0_thmss) THEN
      HEADGOAL (rtac ctxt refl);

    fun prove goal =
      Goal.prove_sorry ctxt [] [] goal (tac o #context)
      |> Thm.close_derivation \<^here>;
  in
    map (map prove) goalss
  end;

fun define_split_rec_derive_induct_rec_thms Xs fpTs ctrXs_Tsss ctrss inducts induct recs0 rec_thmss
    lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    (* imperfect: will not yield the expected theorem for functions taking a large number of
       arguments *)
    val repair_induct = unfold_thms lthy @{thms all_mem_range};

    val inducts' = map repair_induct inducts;
    val induct' = repair_induct induct;

    val Cs = map ((fn TVar ((s, _), S) => TFree (s, S)) o body_type o fastype_of) recs0;
    val recs = map2 (mk_co_rec thy Least_FP Cs) fpTs recs0;
    val ((recs', rec'_defs), lthy') = define_split_recs fpTs Cs recs lthy |>> split_list;
    val rec'_thmss = mk_split_rec_thmss lthy' Xs ctrXs_Tsss ctrss rec_thmss recs' rec'_defs;
  in
    ((inducts', induct', recs', rec'_thmss), lthy')
  end;

fun body_rec_indices (Old_Datatype_Aux.DtRec kk) = [kk]
  | body_rec_indices (Old_Datatype_Aux.DtType (\<^type_name>\<open>fun\<close>, [_, D])) = body_rec_indices D
  | body_rec_indices _ = [];

fun reindex_desc desc =
  let
    val kks = map fst desc;
    val perm_kks = sort int_ord kks;

    fun perm_dtyp (Old_Datatype_Aux.DtType (s, Ds)) = Old_Datatype_Aux.DtType (s, map perm_dtyp Ds)
      | perm_dtyp (Old_Datatype_Aux.DtRec kk) =
        Old_Datatype_Aux.DtRec (find_index (curry (op =) kk) kks)
      | perm_dtyp D = D;
  in
    if perm_kks = kks then
      desc
    else
      perm_kks ~~
      map (fn (_, (s, Ds, sDss)) => (s, map perm_dtyp Ds, map (apsnd (map perm_dtyp)) sDss)) desc
  end;

fun mk_infos_of_mutually_recursive_new_datatypes prefs check_names fpT_names0 lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    fun not_datatype_name s =
      error (quote s ^ " is not a datatype");
    fun not_mutually_recursive ss =
      error ("{" ^ commas ss ^ "} is not a complete set of mutually recursive datatypes");

    fun checked_fp_sugar_of s =
      (case fp_sugar_of lthy s of
        SOME (fp_sugar as {fp, fp_co_induct_sugar = SOME _, ...}) =>
        if member (op =) prefs Include_GFPs orelse fp = Least_FP then fp_sugar
        else not_datatype_name s
      | _ => not_datatype_name s);

    val fpTs0 as Type (_, var_As) :: _ =
      map (#T o checked_fp_sugar_of o dest_Type_name)
        (#Ts (#fp_res (checked_fp_sugar_of (hd fpT_names0))));
    val fpT_names as fpT_name1 :: _ = map (dest_Type_name) fpTs0;

    val _ = check_names (op =) (fpT_names0, fpT_names) orelse not_mutually_recursive fpT_names0;

    val (As_names, _) = Variable.variant_fixes (map (fn TVar ((s, _), _) => s) var_As) lthy;
    val As = map2 (fn s => fn TVar (_, S) => TFree (s, S)) As_names var_As;
    val fpTs = map (fn s => Type (s, As)) fpT_names;

    val nn_fp = length fpTs;

    val mk_dtyp = Old_Datatype_Aux.dtyp_of_typ (map (apsnd (map Term.dest_TFree) o dest_Type) fpTs);

    fun mk_ctr_descr Ts = mk_ctr Ts #> dest_Const ##> (binder_types #> map mk_dtyp);
    fun mk_typ_descr index (Type (T_name, Ts)) ({ctrs, ...} : ctr_sugar) =
      (index, (T_name, map mk_dtyp Ts, map (mk_ctr_descr Ts) ctrs));

    val fp_sugars as {fp, ...} :: _ = map checked_fp_sugar_of fpT_names;
    val fp_ctr_sugars = map (#ctr_sugar o #fp_ctr_sugar) fp_sugars;
    val orig_descr = @{map 3} mk_typ_descr (0 upto nn_fp - 1) fpTs fp_ctr_sugars;
    val all_infos = Old_Datatype_Data.get_all thy;
    val (orig_descr' :: nested_descrs) =
      if member (op =) prefs Keep_Nesting then [orig_descr]
      else fst (Old_Datatype_Aux.unfold_datatypes lthy orig_descr all_infos orig_descr nn_fp);

    fun cliquify_descr [] = []
      | cliquify_descr [entry] = [[entry]]
      | cliquify_descr (full_descr as (_, (T_name1, _, _)) :: _) =
        let
          val nn =
            if member (op =) fpT_names T_name1 then
              nn_fp
            else
              (case Symtab.lookup all_infos T_name1 of
                SOME {descr, ...} =>
                length (filter_out (exists Old_Datatype_Aux.is_rec_type o #2 o snd) descr)
              | NONE => raise Fail "unknown old-style datatype");
        in
          chop nn full_descr ||> cliquify_descr |> op ::
        end;

    (* put nested types before the types that nest them, as needed for N2M *)
    val descrs = burrow reindex_desc (orig_descr' :: rev nested_descrs);
    val (mutual_cliques, descr) =
      split_list (flat (map_index (fn (i, descr) => map (pair i) descr)
        (maps cliquify_descr descrs)));

    val fpTs' = Old_Datatype_Aux.get_rec_types descr;
    val nn = length fpTs';

    val fp_sugars = map (checked_fp_sugar_of o dest_Type_name) fpTs';
    val ctr_Tsss = map (map (map (Old_Datatype_Aux.typ_of_dtyp descr) o snd) o #3 o snd) descr;
    val kkssss = map (map (map body_rec_indices o snd) o #3 o snd) descr;

    val callers = map (fn kk => Var ((Name.uu, kk), \<^typ>\<open>unit => unit\<close>)) (0 upto nn - 1);

    fun apply_comps n kk =
      mk_partial_compN n (replicate n HOLogic.unitT ---> HOLogic.unitT) (nth callers kk);

    val callssss = map2 (map2 (map2 (map o apply_comps o num_binder_types))) ctr_Tsss kkssss;

    val b_names = Name.variant_list [] (map base_name_of_typ fpTs');
    val compat_b_names = map (prefix compat_N) b_names;
    val compat_bs = map Binding.name compat_b_names;

    val ((fp_sugars', (lfp_sugar_thms', _)), lthy') =
      if nn > nn_fp then
        mutualize_fp_sugars (K true) Least_FP mutual_cliques compat_bs fpTs' callers callssss
          fp_sugars lthy
      else
        ((fp_sugars, (NONE, NONE)), lthy);

    fun mk_ctr_of ({fp_ctr_sugar = {ctr_sugar = {ctrs, ...}, ...}, ...} : fp_sugar) (Type (_, Ts)) =
      map (mk_ctr Ts) ctrs;
    val substAT = Term.typ_subst_atomic (var_As ~~ As);

    val Xs' = map #X fp_sugars';
    val ctrXs_Tsss' = map (map (map substAT) o #ctrXs_Tss o #fp_ctr_sugar) fp_sugars';
    val ctrss' = map2 mk_ctr_of fp_sugars' fpTs';
    val {fp_co_induct_sugar = SOME {common_co_inducts = induct :: _, ...}, ...} :: _ = fp_sugars';
    val inducts = map (hd o #co_inducts o the o #fp_co_induct_sugar) fp_sugars';
    val recs = map (#co_rec o the o #fp_co_induct_sugar) fp_sugars';
    val rec_thmss = map (#co_rec_thms o the o #fp_co_induct_sugar) fp_sugars';

    fun is_nested_rec_type (Type (\<^type_name>\<open>fun\<close>, [_, T])) = member (op =) Xs' (body_type T)
      | is_nested_rec_type _ = false;

    val ((lfp_sugar_thms'', (inducts', induct', recs', rec'_thmss)), lthy'') =
      if member (op =) prefs Keep_Nesting orelse
         not (exists (exists (exists is_nested_rec_type)) ctrXs_Tsss') then
        ((lfp_sugar_thms', (inducts, induct, recs, rec_thmss)), lthy')
      else if fp = Least_FP then
        define_split_rec_derive_induct_rec_thms Xs' fpTs' ctrXs_Tsss' ctrss' inducts induct recs
          rec_thmss lthy'
        |>> `(fn (inducts', induct', _, rec'_thmss) =>
          SOME ((inducts', induct', mk_induct_attrs ctrss'), (rec'_thmss, [])))
      else
        not_datatype_name fpT_name1;

    val rec'_names = map dest_Const_name recs';
    val rec'_thms = flat rec'_thmss;

    fun mk_info (kk, {T = Type (T_name0, _), fp_ctr_sugar = {ctr_sugar = {casex, exhaust, nchotomy,
        injects, distincts, case_thms, case_cong, case_cong_weak, split,
        split_asm, ...}, ...}, ...} : fp_sugar) =
      (T_name0,
       {index = kk, descr = descr, inject = injects, distinct = distincts, induct = induct',
        inducts = inducts', exhaust = exhaust, nchotomy = nchotomy, rec_names = rec'_names,
        rec_rewrites = rec'_thms, case_name = dest_Const_name casex, case_rewrites = case_thms,
        case_cong = case_cong, case_cong_weak = case_cong_weak, split = split,
        split_asm = split_asm});

    val infos = map_index mk_info (take nn_fp fp_sugars');
  in
    (nn, b_names, compat_b_names, lfp_sugar_thms'', infos, lthy'')
  end;

fun infos_of_new_datatype_mutual_cluster lthy prefs fpT_name =
  let
    fun get prefs =
      #5 (mk_infos_of_mutually_recursive_new_datatypes prefs subset [fpT_name] lthy)
      handle ERROR _ => [];
  in
    (case get prefs of
      [] => if member (op =) prefs Keep_Nesting then [] else get (Keep_Nesting :: prefs)
    | infos => infos)
  end;

fun get_all thy prefs =
  let
    val ctxt = Proof_Context.init_global thy;
    val old_info_tab = Old_Datatype_Data.get_all thy;
    val new_T_names = BNF_FP_Def_Sugar.fp_sugars_of_global thy
      |> map_filter (try (fn {T = Type (s, _), fp_res_index = 0, ...} => s));
    val new_infos =
      maps (infos_of_new_datatype_mutual_cluster ctxt (insert (op =) Keep_Nesting prefs))
        new_T_names;
  in
    fold (if member (op =) prefs Keep_Nesting then Symtab.update else Symtab.default) new_infos
      old_info_tab
  end;

fun get_one get_old get_new thy prefs x =
  let
    val (get_fst, get_snd) = (get_old thy, get_new thy) |> member (op =) prefs Keep_Nesting ? swap;
  in
    (case get_fst x of NONE => get_snd x | res => res)
  end;

fun get_info_of_new_datatype prefs thy T_name =
  let val ctxt = Proof_Context.init_global thy in
    AList.lookup (op =) (infos_of_new_datatype_mutual_cluster ctxt prefs T_name) T_name
  end;

fun get_info thy prefs =
  get_one Old_Datatype_Data.get_info (get_info_of_new_datatype prefs) thy prefs;

fun the_info thy prefs T_name =
  (case get_info thy prefs T_name of
    SOME info => info
  | NONE => error ("Unknown datatype " ^ quote T_name));

fun the_spec thy T_name =
  let
    val {descr, index, ...} = the_info thy [Keep_Nesting, Include_GFPs] T_name;
    val (_, Ds, ctrs0) = the (AList.lookup (op =) descr index);
    val tfrees = map Old_Datatype_Aux.dest_DtTFree Ds;
    val ctrs = map (apsnd (map (Old_Datatype_Aux.typ_of_dtyp descr))) ctrs0;
  in (tfrees, ctrs) end;

fun the_descr thy prefs (T_names0 as T_name01 :: _) =
  let
    fun not_mutually_recursive ss =
      error ("{" ^ commas ss ^ "} is not a complete set of mutually recursive datatypes");

    val info = the_info thy prefs T_name01;
    val descr = #descr info;

    val (_, Ds, _) = the (AList.lookup (op =) descr (#index info));
    val vs = map Old_Datatype_Aux.dest_DtTFree Ds;

    fun is_DtTFree (Old_Datatype_Aux.DtTFree _) = true
      | is_DtTFree _ = false;

    val k = find_index (fn (_, (_, dTs, _)) => not (forall is_DtTFree dTs)) descr;
    val protoTs as (dataTs, _) = chop k descr
      |> (apply2 o map)
        (fn (_, (T_name, Ds, _)) => (T_name, map (Old_Datatype_Aux.typ_of_dtyp descr) Ds));

    val T_names = map fst dataTs;
    val _ = eq_set (op =) (T_names, T_names0) orelse not_mutually_recursive T_names0

    val (Ts, Us) = apply2 (map Type) protoTs;

    val names = map Long_Name.base_name T_names;
    val (auxnames, _) = Name.make_context names
      |> fold_map (Name.variant o Old_Datatype_Aux.name_of_typ) Us;
    val prefix = space_implode "_" names;
  in
    (descr, vs, T_names, prefix, (names, auxnames), (Ts, Us))
  end;

fun get_constrs thy T_name =
  try (the_spec thy) T_name
  |> Option.map (fn (tfrees, ctrs) =>
    let
      fun varify_tfree (s, S) = TVar ((s, 0), S);
      fun varify_typ (TFree x) = varify_tfree x
        | varify_typ T = T;

      val dataT = Type (T_name, map varify_tfree tfrees);

      fun mk_ctr_typ Ts = map (Term.map_atyps varify_typ) Ts ---> dataT;
    in
      map (apsnd mk_ctr_typ) ctrs
    end);

fun old_interpretation_of prefs f config T_names thy =
  if not (member (op =) prefs Keep_Nesting) orelse
     exists (is_none o fp_sugar_of_global thy) T_names then
    f config T_names thy
  else
    thy;

fun new_interpretation_of prefs f (fp_sugars : fp_sugar list) thy =
  let val T_names = map (dest_Type_name o #T) fp_sugars in
    if (member (op =) prefs Include_GFPs orelse forall (curry (op =) Least_FP o #fp) fp_sugars)
       andalso (member (op =) prefs Keep_Nesting orelse
         exists (is_none o Old_Datatype_Data.get_info thy) T_names) then
      f Old_Datatype_Aux.default_config T_names thy
    else
      thy
  end;

fun interpretation name prefs f =
  Old_Datatype_Data.interpretation (old_interpretation_of prefs f)
  #> fp_sugars_interpretation name (Local_Theory.background_theory o new_interpretation_of prefs f);

val nitpicksimp_simp_attrs = @{attributes [nitpick_simp, simp]};

fun datatype_compat fpT_names lthy =
  let
    val (nn, b_names, compat_b_names, lfp_sugar_thms, infos, lthy') =
      mk_infos_of_mutually_recursive_new_datatypes [] eq_set fpT_names lthy;

    val (all_notes, rec_thmss) =
      (case lfp_sugar_thms of
        NONE => ([], [])
      | SOME ((inducts, induct, induct_attrs), (rec_thmss, _)) =>
        let
          val common_name = compat_N ^ mk_common_name b_names;

          val common_notes =
            (if nn > 1 then [(inductN, [induct], induct_attrs)] else [])
            |> filter_out (null o #2)
            |> map (fn (thmN, thms, attrs) =>
              ((Binding.qualify true common_name (Binding.name thmN), attrs), [(thms, [])]));

          val notes =
            [(inductN, map single inducts, induct_attrs),
             (recN, rec_thmss, nitpicksimp_simp_attrs)]
            |> filter_out (null o #2)
            |> maps (fn (thmN, thmss, attrs) =>
              if forall null thmss then
                []
              else
                map2 (fn b_name => fn thms =>
                    ((Binding.qualify true b_name (Binding.name thmN), attrs), [(thms, [])]))
                  compat_b_names thmss);
        in
          (common_notes @ notes, rec_thmss)
        end);

    val register_interpret =
      Old_Datatype_Data.register infos
      #> Old_Datatype_Data.interpretation_data (Old_Datatype_Aux.default_config, map fst infos);
  in
    lthy'
    |> Local_Theory.raw_theory register_interpret
    |> Local_Theory.notes all_notes
    |> snd
    |> Code.declare_default_eqns (map (rpair true) (flat rec_thmss))
  end;

val datatype_compat_global = Named_Target.theory_map o datatype_compat;

fun datatype_compat_cmd raw_fpT_names lthy =
  let
    val fpT_names =
      map (dest_Type_name o Proof_Context.read_type_name {proper = true, strict = false} lthy)
        raw_fpT_names;
  in
    datatype_compat fpT_names lthy
  end;

fun add_datatype prefs old_specs thy =
  let
    val fpT_names = map (Sign.full_name thy o #1 o fst) old_specs;

    fun new_type_args_of (s, S) =
      (if member (op =) prefs Kill_Type_Args then NONE else SOME Binding.empty,
       (TFree (s, \<^sort>\<open>type\<close>), S));
    fun new_ctr_spec_of (b, Ts, mx) = (((Binding.empty, b), map (pair Binding.empty) Ts), mx);

    fun new_spec_of ((b, old_tyargs, mx), old_ctr_specs) =
      (((((map new_type_args_of old_tyargs, b), mx), map new_ctr_spec_of old_ctr_specs),
        (Binding.empty, Binding.empty, Binding.empty)), []);

    val new_specs = map new_spec_of old_specs;
  in
    (fpT_names,
     thy
     |> Named_Target.theory_map
       (co_datatypes Least_FP construct_lfp (default_ctr_options, new_specs))
     |> not (member (op =) prefs Keep_Nesting) ? perhaps (try (datatype_compat_global fpT_names)))
  end;

fun old_of_new f (ts, _, simpss) = (ts, f simpss);

val primrec = apfst (old_of_new flat) ooo BNF_LFP_Rec_Sugar.primrec false [];
val primrec_global = apfst (old_of_new flat) ooo BNF_LFP_Rec_Sugar.primrec_global false [];
val primrec_overloaded = apfst (old_of_new flat) oooo BNF_LFP_Rec_Sugar.primrec_overloaded false [];
val primrec_simple = apfst (apfst fst o apsnd (old_of_new (flat o snd))) ooo
  BNF_LFP_Rec_Sugar.primrec_simple false;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>datatype_compat\<close>
    "register datatypes as old-style datatypes and derive old-style properties"
    (Scan.repeat1 Parse.type_const >> datatype_compat_cmd);

end;
