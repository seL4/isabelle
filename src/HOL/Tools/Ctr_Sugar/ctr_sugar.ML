(*  Title:      HOL/Tools/Ctr_Sugar/ctr_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2012, 2013

Wrapping existing freely generated type's constructors.
*)

signature CTR_SUGAR =
sig
  datatype ctr_sugar_kind = Datatype | Codatatype | Record | Unknown

  type ctr_sugar =
    {kind: ctr_sugar_kind,
     T: typ,
     ctrs: term list,
     casex: term,
     discs: term list,
     selss: term list list,
     exhaust: thm,
     nchotomy: thm,
     injects: thm list,
     distincts: thm list,
     case_thms: thm list,
     case_cong: thm,
     case_cong_weak: thm,
     case_distribs: thm list,
     split: thm,
     split_asm: thm,
     disc_defs: thm list,
     disc_thmss: thm list list,
     discIs: thm list,
     disc_eq_cases: thm list,
     sel_defs: thm list,
     sel_thmss: thm list list,
     distinct_discsss: thm list list list,
     exhaust_discs: thm list,
     exhaust_sels: thm list,
     collapses: thm list,
     expands: thm list,
     split_sels: thm list,
     split_sel_asms: thm list,
     case_eq_ifs: thm list};

  val morph_ctr_sugar: morphism -> ctr_sugar -> ctr_sugar
  val transfer_ctr_sugar: theory -> ctr_sugar -> ctr_sugar
  val ctr_sugar_of: Proof.context -> string -> ctr_sugar option
  val ctr_sugar_of_global: theory -> string -> ctr_sugar option
  val ctr_sugars_of: Proof.context -> ctr_sugar list
  val ctr_sugars_of_global: theory -> ctr_sugar list
  val ctr_sugar_of_case: Proof.context -> string -> ctr_sugar option
  val ctr_sugar_of_case_global: theory -> string -> ctr_sugar option
  val ctr_sugar_interpretation: string -> (ctr_sugar -> local_theory -> local_theory) -> theory ->
    theory
  val interpret_ctr_sugar: (string -> bool) -> ctr_sugar -> local_theory -> local_theory
  val register_ctr_sugar_raw: ctr_sugar -> local_theory -> local_theory
  val register_ctr_sugar: (string -> bool) -> ctr_sugar -> local_theory -> local_theory
  val default_register_ctr_sugar_global: (string -> bool) -> ctr_sugar -> theory -> theory

  val mk_half_pairss: 'a list * 'a list -> ('a * 'a) list list
  val join_halves: int -> 'a list list -> 'a list list -> 'a list * 'a list list list

  val mk_ctr: typ list -> term -> term
  val mk_case: typ list -> typ -> term -> term
  val mk_disc_or_sel: typ list -> term -> term
  val name_of_ctr: term -> string
  val name_of_disc: term -> string
  val dest_ctr: Proof.context -> string -> term -> term * term list
  val dest_case: Proof.context -> string -> typ list -> term ->
    (ctr_sugar * term list * term list) option

  type ('c, 'a) ctr_spec = (binding * 'c) * 'a list

  val disc_of_ctr_spec: ('c, 'a) ctr_spec -> binding
  val ctr_of_ctr_spec: ('c, 'a) ctr_spec -> 'c
  val args_of_ctr_spec: ('c, 'a) ctr_spec -> 'a list

  val code_plugin: string

  type ctr_options = (string -> bool) * bool
  type ctr_options_cmd = (Proof.context -> string -> bool) * bool

  val fake_local_theory_for_sel_defaults: (binding * typ) list -> Proof.context -> Proof.context
  val free_constructors: ctr_sugar_kind ->
    ({prems: thm list, context: Proof.context} -> tactic) list list ->
    ((ctr_options * binding) * (term, binding) ctr_spec list) * term list -> local_theory ->
    ctr_sugar * local_theory
  val free_constructors_cmd: ctr_sugar_kind ->
    ((((Proof.context -> Plugin_Name.filter) * bool) * binding)
     * ((binding * string) * binding list) list) * string list ->
    Proof.context -> Proof.state
  val default_ctr_options: ctr_options
  val default_ctr_options_cmd: ctr_options_cmd
  val parse_bound_term: (binding * string) parser
  val parse_ctr_options: ctr_options_cmd parser
  val parse_ctr_spec: 'c parser -> 'a parser -> ('c, 'a) ctr_spec parser
  val parse_sel_default_eqs: string list parser
end;

structure Ctr_Sugar : CTR_SUGAR =
struct

open Ctr_Sugar_Util
open Ctr_Sugar_Tactics
open Ctr_Sugar_Code

datatype ctr_sugar_kind = Datatype | Codatatype | Record | Unknown;

type ctr_sugar =
  {kind: ctr_sugar_kind,
   T: typ,
   ctrs: term list,
   casex: term,
   discs: term list,
   selss: term list list,
   exhaust: thm,
   nchotomy: thm,
   injects: thm list,
   distincts: thm list,
   case_thms: thm list,
   case_cong: thm,
   case_cong_weak: thm,
   case_distribs: thm list,
   split: thm,
   split_asm: thm,
   disc_defs: thm list,
   disc_thmss: thm list list,
   discIs: thm list,
   disc_eq_cases: thm list,
   sel_defs: thm list,
   sel_thmss: thm list list,
   distinct_discsss: thm list list list,
   exhaust_discs: thm list,
   exhaust_sels: thm list,
   collapses: thm list,
   expands: thm list,
   split_sels: thm list,
   split_sel_asms: thm list,
   case_eq_ifs: thm list};

fun morph_ctr_sugar phi ({kind, T, ctrs, casex, discs, selss, exhaust, nchotomy, injects, distincts,
    case_thms, case_cong, case_cong_weak, case_distribs, split, split_asm, disc_defs, disc_thmss,
    discIs, disc_eq_cases, sel_defs, sel_thmss, distinct_discsss, exhaust_discs, exhaust_sels,
    collapses, expands, split_sels, split_sel_asms, case_eq_ifs} : ctr_sugar) =
  {kind = kind,
   T = Morphism.typ phi T,
   ctrs = map (Morphism.term phi) ctrs,
   casex = Morphism.term phi casex,
   discs = map (Morphism.term phi) discs,
   selss = map (map (Morphism.term phi)) selss,
   exhaust = Morphism.thm phi exhaust,
   nchotomy = Morphism.thm phi nchotomy,
   injects = map (Morphism.thm phi) injects,
   distincts = map (Morphism.thm phi) distincts,
   case_thms = map (Morphism.thm phi) case_thms,
   case_cong = Morphism.thm phi case_cong,
   case_cong_weak = Morphism.thm phi case_cong_weak,
   case_distribs = map (Morphism.thm phi) case_distribs,
   split = Morphism.thm phi split,
   split_asm = Morphism.thm phi split_asm,
   disc_defs = map (Morphism.thm phi) disc_defs,
   disc_thmss = map (map (Morphism.thm phi)) disc_thmss,
   discIs = map (Morphism.thm phi) discIs,
   disc_eq_cases = map (Morphism.thm phi) disc_eq_cases,
   sel_defs = map (Morphism.thm phi) sel_defs,
   sel_thmss = map (map (Morphism.thm phi)) sel_thmss,
   distinct_discsss = map (map (map (Morphism.thm phi))) distinct_discsss,
   exhaust_discs = map (Morphism.thm phi) exhaust_discs,
   exhaust_sels = map (Morphism.thm phi) exhaust_sels,
   collapses = map (Morphism.thm phi) collapses,
   expands = map (Morphism.thm phi) expands,
   split_sels = map (Morphism.thm phi) split_sels,
   split_sel_asms = map (Morphism.thm phi) split_sel_asms,
   case_eq_ifs = map (Morphism.thm phi) case_eq_ifs};

val transfer_ctr_sugar = morph_ctr_sugar o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = (Position.T * ctr_sugar) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun ctr_sugar_of_generic context =
  Option.map (transfer_ctr_sugar (Context.theory_of context) o #2) o Symtab.lookup (Data.get context);

fun ctr_sugars_of_generic context =
  Symtab.fold (cons o transfer_ctr_sugar (Context.theory_of context) o #2 o #2) (Data.get context) [];

fun ctr_sugar_of_case_generic context s =
  find_first (fn {casex = Const (s', _), ...} => s' = s | _ => false)
    (ctr_sugars_of_generic context);

val ctr_sugar_of = ctr_sugar_of_generic o Context.Proof;
val ctr_sugar_of_global = ctr_sugar_of_generic o Context.Theory;

val ctr_sugars_of = ctr_sugars_of_generic o Context.Proof;
val ctr_sugars_of_global = ctr_sugars_of_generic o Context.Theory;

val ctr_sugar_of_case = ctr_sugar_of_case_generic o Context.Proof;
val ctr_sugar_of_case_global = ctr_sugar_of_case_generic o Context.Theory;

structure Ctr_Sugar_Plugin = Plugin(type T = ctr_sugar);

fun ctr_sugar_interpretation name f =
  Ctr_Sugar_Plugin.interpretation name (fn ctr_sugar => fn lthy =>
    f (transfer_ctr_sugar (Proof_Context.theory_of lthy) ctr_sugar) lthy);

val interpret_ctr_sugar = Ctr_Sugar_Plugin.data;

fun register_ctr_sugar_raw (ctr_sugar as {T = Type (name, _), ...}) =
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => fn context =>
      let val pos = Position.thread_data ()
      in Data.map (Symtab.update (name, (pos, morph_ctr_sugar phi ctr_sugar))) context end);

fun register_ctr_sugar plugins ctr_sugar =
  register_ctr_sugar_raw ctr_sugar #> interpret_ctr_sugar plugins ctr_sugar;

fun default_register_ctr_sugar_global plugins (ctr_sugar as {T = Type (name, _), ...}) thy =
  let
    val tab = Data.get (Context.Theory thy);
    val pos = Position.thread_data ();
  in
    if Symtab.defined tab name then thy
    else
      thy
      |> Context.theory_map (Data.put (Symtab.update_new (name, (pos, ctr_sugar)) tab))
      |> Named_Target.theory_map (Ctr_Sugar_Plugin.data plugins ctr_sugar)
  end;

val is_prefix = "is_";
val un_prefix = "un_";
val not_prefix = "not_";

fun mk_unN 1 1 suf = un_prefix ^ suf
  | mk_unN _ l suf = un_prefix ^ suf ^ string_of_int l;

val caseN = "case";
val case_congN = "case_cong";
val case_eq_ifN = "case_eq_if";
val collapseN = "collapse";
val discN = "disc";
val disc_eq_caseN = "disc_eq_case";
val discIN = "discI";
val distinctN = "distinct";
val distinct_discN = "distinct_disc";
val exhaustN = "exhaust";
val exhaust_discN = "exhaust_disc";
val expandN = "expand";
val injectN = "inject";
val nchotomyN = "nchotomy";
val selN = "sel";
val exhaust_selN = "exhaust_sel";
val splitN = "split";
val split_asmN = "split_asm";
val split_selN = "split_sel";
val split_sel_asmN = "split_sel_asm";
val splitsN = "splits";
val split_selsN = "split_sels";
val case_cong_weak_thmsN = "case_cong_weak";
val case_distribN = "case_distrib";

val cong_attrs = @{attributes [cong]};
val dest_attrs = @{attributes [dest]};
val safe_elim_attrs = @{attributes [elim!]};
val iff_attrs = @{attributes [iff]};
val inductsimp_attrs = @{attributes [induct_simp]};
val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};

fun unflat_lookup eq xs ys = map (fn xs' => permute_like_unique eq xs xs' ys);

fun mk_half_pairss' _ ([], []) = []
  | mk_half_pairss' indent (x :: xs, _ :: ys) =
    indent @ fold_rev (cons o single o pair x) ys (mk_half_pairss' ([] :: indent) (xs, ys));

fun mk_half_pairss p = mk_half_pairss' [[]] p;

fun join_halves n half_xss other_half_xss =
  (splice (flat half_xss) (flat other_half_xss),
   map2 (map2 append) (Library.chop_groups n half_xss)
     (transpose (Library.chop_groups n other_half_xss)));

fun mk_undefined T = Const (\<^const_name>\<open>undefined\<close>, T);

fun mk_ctr Ts t =
  let val Type (_, Ts0) = body_type (fastype_of t) in
    subst_nonatomic_types (Ts0 ~~ Ts) t
  end;

fun mk_case Ts T t =
  let val (Type (_, Ts0), body) = strip_type (fastype_of t) |>> List.last in
    subst_nonatomic_types ((body, T) :: (Ts0 ~~ Ts)) t
  end;

fun mk_disc_or_sel Ts t =
  subst_nonatomic_types (snd (Term.dest_Type (domain_type (fastype_of t))) ~~ Ts) t;

val name_of_ctr = name_of_const "constructor" body_type;

fun name_of_disc t =
  (case head_of t of
    Abs (_, _, \<^const>\<open>Not\<close> $ (t' $ Bound 0)) =>
    Long_Name.map_base_name (prefix not_prefix) (name_of_disc t')
  | Abs (_, _, Const (\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ t') =>
    Long_Name.map_base_name (prefix is_prefix) (name_of_disc t')
  | Abs (_, _, \<^const>\<open>Not\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ Bound 0 $ t')) =>
    Long_Name.map_base_name (prefix (not_prefix ^ is_prefix)) (name_of_disc t')
  | t' => name_of_const "discriminator" (perhaps (try domain_type)) t');

val base_name_of_ctr = Long_Name.base_name o name_of_ctr;

fun dest_ctr ctxt s t =
  let val (f, args) = Term.strip_comb t in
    (case ctr_sugar_of ctxt s of
      SOME {ctrs, ...} =>
      (case find_first (can (fo_match ctxt f)) ctrs of
        SOME f' => (f', args)
      | NONE => raise Fail "dest_ctr")
    | NONE => raise Fail "dest_ctr")
  end;

fun dest_case ctxt s Ts t =
  (case Term.strip_comb t of
    (Const (c, _), args as _ :: _) =>
    (case ctr_sugar_of ctxt s of
      SOME (ctr_sugar as {casex = Const (case_name, _), discs = discs0, selss = selss0, ...}) =>
      if case_name = c then
        let val n = length discs0 in
          if n < length args then
            let
              val (branches, obj :: leftovers) = chop n args;
              val discs = map (mk_disc_or_sel Ts) discs0;
              val selss = map (map (mk_disc_or_sel Ts)) selss0;
              val conds = map (rapp obj) discs;
              val branch_argss = map (fn sels => map (rapp obj) sels @ leftovers) selss;
              val branches' = map2 (curry Term.betapplys) branches branch_argss;
            in
              SOME (ctr_sugar, conds, branches')
            end
          else
            NONE
        end
      else
        NONE
    | _ => NONE)
  | _ => NONE);

fun const_or_free_name (Const (s, _)) = Long_Name.base_name s
  | const_or_free_name (Free (s, _)) = s
  | const_or_free_name t = raise TERM ("const_or_free_name", [t])

fun extract_sel_default ctxt t =
  let
    fun malformed () =
      error ("Malformed selector default value equation: " ^ Syntax.string_of_term ctxt t);

    val ((sel, (ctr, vars)), rhs) =
      fst (Term.replace_dummy_patterns (Syntax.check_term ctxt t) 0)
      |> HOLogic.dest_eq
      |>> (Term.dest_comb
        #>> const_or_free_name
        ##> (Term.strip_comb #>> (Term.dest_Const #> fst)))
      handle TERM _ => malformed ();
  in
    if forall (is_Free orf is_Var) vars andalso not (has_duplicates (op aconv) vars) then
      ((ctr, sel), fold_rev Term.lambda vars rhs)
    else
      malformed ()
  end;

(* Ideally, we would enrich the context with constants rather than free variables. *)
fun fake_local_theory_for_sel_defaults sel_bTs =
  Proof_Context.allow_dummies
  #> Proof_Context.add_fixes (map (fn (b, T) => (b, SOME T, NoSyn)) sel_bTs)
  #> snd;

type ('c, 'a) ctr_spec = (binding * 'c) * 'a list;

fun disc_of_ctr_spec ((disc, _), _) = disc;
fun ctr_of_ctr_spec ((_, ctr), _) = ctr;
fun args_of_ctr_spec (_, args) = args;

val code_plugin = Plugin_Name.declare_setup \<^binding>\<open>code\<close>;

fun prepare_free_constructors kind prep_plugins prep_term
    ((((raw_plugins, discs_sels), raw_case_binding), ctr_specs), sel_default_eqs) no_defs_lthy =
  let
    val plugins = prep_plugins no_defs_lthy raw_plugins;

    (* TODO: sanity checks on arguments *)

    val raw_ctrs = map ctr_of_ctr_spec ctr_specs;
    val raw_disc_bindings = map disc_of_ctr_spec ctr_specs;
    val raw_sel_bindingss = map args_of_ctr_spec ctr_specs;

    val n = length raw_ctrs;
    val ks = 1 upto n;

    val _ = n > 0 orelse error "No constructors specified";

    val ctrs0 = map (prep_term no_defs_lthy) raw_ctrs;

    val (fcT_name, As0) =
      (case body_type (fastype_of (hd ctrs0)) of
        Type T' => T'
      | _ => error "Expected type constructor in body type of constructor");
    val _ = forall ((fn Type (T_name, _) => T_name = fcT_name | _ => false) o body_type
      o fastype_of) (tl ctrs0) orelse error "Constructors not constructing same type";

    val fc_b_name = Long_Name.base_name fcT_name;
    val fc_b = Binding.name fc_b_name;

    fun qualify mandatory = Binding.qualify mandatory fc_b_name;

    val (unsorted_As, [B, C]) =
      no_defs_lthy
      |> variant_tfrees (map (fst o dest_TFree_or_TVar) As0)
      ||> fst o mk_TFrees 2;

    val As = map2 (resort_tfree_or_tvar o snd o dest_TFree_or_TVar) As0 unsorted_As;

    val fcT = Type (fcT_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val ms = map length ctr_Tss;

    fun can_definitely_rely_on_disc k =
      not (Binding.is_empty (nth raw_disc_bindings (k - 1))) orelse nth ms (k - 1) = 0;
    fun can_rely_on_disc k =
      can_definitely_rely_on_disc k orelse (k = 1 andalso not (can_definitely_rely_on_disc 2));
    fun should_omit_disc_binding k = n = 1 orelse (n = 2 andalso can_rely_on_disc (3 - k));

    val equal_binding = \<^binding>\<open>=\<close>;

    fun is_disc_binding_valid b =
      not (Binding.is_empty b orelse Binding.eq_name (b, equal_binding));

    val standard_disc_binding = Binding.name o prefix is_prefix o base_name_of_ctr;

    val disc_bindings =
      raw_disc_bindings
      |> @{map 4} (fn k => fn m => fn ctr => fn disc =>
        qualify false
          (if Binding.is_empty disc then
             if m = 0 then equal_binding
             else if should_omit_disc_binding k then disc
             else standard_disc_binding ctr
           else if Binding.eq_name (disc, standard_binding) then
             standard_disc_binding ctr
           else
             disc)) ks ms ctrs0;

    fun standard_sel_binding m l = Binding.name o mk_unN m l o base_name_of_ctr;

    val sel_bindingss =
      @{map 3} (fn ctr => fn m => map2 (fn l => fn sel =>
        qualify false
          (if Binding.is_empty sel orelse Binding.eq_name (sel, standard_binding) then
            standard_sel_binding m l ctr
          else
            sel)) (1 upto m) o pad_list Binding.empty m) ctrs0 ms raw_sel_bindingss;

    val add_bindings =
      Variable.add_fixes (distinct (op =) (filter Symbol_Pos.is_identifier
        (map Binding.name_of (disc_bindings @ flat sel_bindingss))))
      #> snd;

    val case_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    val (((((((((u, exh_y), xss), yss), fs), gs), w), (p, p'))), _) = no_defs_lthy
      |> add_bindings
      |> yield_singleton (mk_Frees fc_b_name) fcT
      ||>> yield_singleton (mk_Frees "y") fcT (* for compatibility with "datatype_realizer.ML" *)
      ||>> mk_Freess "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" case_Ts
      ||>> mk_Frees "g" case_Ts
      ||>> yield_singleton (mk_Frees "z") B
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "P") HOLogic.boolT;

    val q = Free (fst p', mk_pred1T B);

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;

    val xfs = map2 (curry Term.list_comb) fs xss;
    val xgs = map2 (curry Term.list_comb) gs xss;

    (* TODO: Eta-expension is for compatibility with the old datatype package (but it also provides
       nicer names). Consider removing. *)
    val eta_fs = map2 (fold_rev Term.lambda) xss xfs;
    val eta_gs = map2 (fold_rev Term.lambda) xss xgs;

    val case_binding =
      qualify false
        (if Binding.is_empty raw_case_binding orelse
            Binding.eq_name (raw_case_binding, standard_binding) then
           Binding.prefix_name (caseN ^ "_") fc_b
         else
           raw_case_binding);

    fun mk_case_disj xctr xf xs =
      list_exists_free xs (HOLogic.mk_conj (HOLogic.mk_eq (u, xctr), HOLogic.mk_eq (w, xf)));

    val case_rhs = fold_rev (fold_rev Term.lambda) [fs, [u]]
      (Const (\<^const_name>\<open>The\<close>, (B --> HOLogic.boolT) --> B) $
         Term.lambda w (Library.foldr1 HOLogic.mk_disj (@{map 3} mk_case_disj xctrs xfs xss)));

    val ((raw_case, (_, raw_case_def)), (lthy, lthy_old)) = no_defs_lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((case_binding, NoSyn),
        ((Binding.concealed (Thm.def_binding case_binding), []), case_rhs))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val case_def = Morphism.thm phi raw_case_def;

    val case0 = Morphism.term phi raw_case;
    val casex = mk_case As B case0;
    val casexC = mk_case As C case0;
    val casexBool = mk_case As HOLogic.boolT case0;

    fun mk_uu_eq () = HOLogic.mk_eq (u, u);

    val exist_xs_u_eq_ctrs =
      map2 (fn xctr => fn xs => list_exists_free xs (HOLogic.mk_eq (u, xctr))) xctrs xss;

    val unique_disc_no_def = TrueI; (*arbitrary marker*)
    val alternate_disc_no_def = FalseE; (*arbitrary marker*)

    fun alternate_disc_lhs get_udisc k =
      HOLogic.mk_not
        (let val b = nth disc_bindings (k - 1) in
           if is_disc_binding_valid b then get_udisc b (k - 1) else nth exist_xs_u_eq_ctrs (k - 1)
         end);

    val no_discs_sels =
      not discs_sels andalso
      forall (forall Binding.is_empty) (raw_disc_bindings :: raw_sel_bindingss) andalso
      null sel_default_eqs;

    val (all_sels_distinct, discs, selss, disc_defs, sel_defs, sel_defss, lthy) =
      if no_discs_sels then
        (true, [], [], [], [], [], lthy)
      else
        let
          val all_sel_bindings = flat sel_bindingss;
          val num_all_sel_bindings = length all_sel_bindings;
          val uniq_sel_bindings = distinct Binding.eq_name all_sel_bindings;
          val all_sels_distinct = (length uniq_sel_bindings = num_all_sel_bindings);

          val sel_binding_index =
            if all_sels_distinct then
              1 upto num_all_sel_bindings
            else
              map (fn b => find_index (curry Binding.eq_name b) uniq_sel_bindings) all_sel_bindings;

          val all_proto_sels = flat (@{map 3} (fn k => fn xs => map (pair k o pair xs)) ks xss xss);
          val sel_infos =
            AList.group (op =) (sel_binding_index ~~ all_proto_sels)
            |> sort (int_ord o apply2 fst)
            |> map snd |> curry (op ~~) uniq_sel_bindings;
          val sel_bindings = map fst sel_infos;

          val sel_defaults =
            if null sel_default_eqs then
              []
            else
              let
                val sel_Ts = map (curry (op -->) fcT o fastype_of o snd o snd o hd o snd) sel_infos;
                val fake_lthy =
                  fake_local_theory_for_sel_defaults (sel_bindings ~~ sel_Ts) no_defs_lthy;
              in
                map (extract_sel_default fake_lthy o prep_term fake_lthy) sel_default_eqs
              end;

          fun disc_free b = Free (Binding.name_of b, mk_pred1T fcT);

          fun disc_spec b exist_xs_u_eq_ctr = mk_Trueprop_eq (disc_free b $ u, exist_xs_u_eq_ctr);

          fun alternate_disc k =
            Term.lambda u (alternate_disc_lhs (K o rapp u o disc_free) (3 - k));

          fun mk_sel_case_args b proto_sels T =
            @{map 3} (fn Const (c, _) => fn Ts => fn k =>
              (case AList.lookup (op =) proto_sels k of
                NONE =>
                (case filter (curry (op =) (c, Binding.name_of b) o fst) sel_defaults of
                  [] => fold_rev (Term.lambda o curry Free Name.uu) Ts (mk_undefined T)
                | [(_, t)] => t
                | _ => error "Multiple default values for selector/constructor pair")
              | SOME (xs, x) => fold_rev Term.lambda xs x)) ctrs ctr_Tss ks;

          fun sel_spec b proto_sels =
            let
              val _ =
                (case duplicates (op =) (map fst proto_sels) of
                   k :: _ => error ("Duplicate selector name " ^ quote (Binding.name_of b) ^
                     " for constructor " ^ quote (Syntax.string_of_term lthy (nth ctrs (k - 1))))
                 | [] => ())
              val T =
                (case distinct (op =) (map (fastype_of o snd o snd) proto_sels) of
                  [T] => T
                | T :: T' :: _ => error ("Inconsistent range type for selector " ^
                    quote (Binding.name_of b) ^ ": " ^ quote (Syntax.string_of_typ lthy T) ^
                    " vs. " ^ quote (Syntax.string_of_typ lthy T')));
            in
              mk_Trueprop_eq (Free (Binding.name_of b, fcT --> T) $ u,
                Term.list_comb (mk_case As T case0, mk_sel_case_args b proto_sels T) $ u)
            end;

          fun unflat_selss xs = unflat_lookup Binding.eq_name sel_bindings xs sel_bindingss;

          val (((raw_discs, raw_disc_defs), (raw_sels, raw_sel_defs)), (lthy', lthy)) =
            lthy
            |> (snd o Local_Theory.begin_nested)
            |> apfst split_list o @{fold_map 3} (fn k => fn exist_xs_u_eq_ctr => fn b =>
                if Binding.is_empty b then
                  if n = 1 then pair (Term.lambda u (mk_uu_eq ()), unique_disc_no_def)
                  else pair (alternate_disc k, alternate_disc_no_def)
                else if Binding.eq_name (b, equal_binding) then
                  pair (Term.lambda u exist_xs_u_eq_ctr, refl)
                else
                  Specification.definition (SOME (b, NONE, NoSyn)) [] []
                    ((Thm.def_binding b, []), disc_spec b exist_xs_u_eq_ctr) #>> apsnd snd)
              ks exist_xs_u_eq_ctrs disc_bindings
            ||>> apfst split_list o fold_map (fn (b, proto_sels) =>
              Specification.definition (SOME (b, NONE, NoSyn)) [] []
                ((Thm.def_binding b, []), sel_spec b proto_sels) #>> apsnd snd) sel_infos
            ||> `Local_Theory.end_nested;

          val phi = Proof_Context.export_morphism lthy lthy';

          val disc_defs = map (Morphism.thm phi) raw_disc_defs;
          val sel_defs = map (Morphism.thm phi) raw_sel_defs;
          val sel_defss = unflat_selss sel_defs;

          val discs0 = map (Morphism.term phi) raw_discs;
          val selss0 = unflat_selss (map (Morphism.term phi) raw_sels);

          val discs = map (mk_disc_or_sel As) discs0;
          val selss = map (map (mk_disc_or_sel As)) selss0;
        in
          (all_sels_distinct, discs, selss, disc_defs, sel_defs, sel_defss, lthy')
        end;

    fun mk_imp_p Qs = Logic.list_implies (Qs, HOLogic.mk_Trueprop p);

    val exhaust_goal =
      let fun mk_prem xctr xs = fold_rev Logic.all xs (mk_imp_p [mk_Trueprop_eq (exh_y, xctr)]) in
        fold_rev Logic.all [p, exh_y] (mk_imp_p (map2 mk_prem xctrs xss))
      end;

    val inject_goalss =
      let
        fun mk_goal _ _ [] [] = []
          | mk_goal xctr yctr xs ys =
            [fold_rev Logic.all (xs @ ys) (mk_Trueprop_eq (HOLogic.mk_eq (xctr, yctr),
              Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys)))];
      in
        @{map 4} mk_goal xctrs yctrs xss yss
      end;

    val half_distinct_goalss =
      let
        fun mk_goal ((xs, xc), (xs', xc')) =
          fold_rev Logic.all (xs @ xs')
            (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (xc, xc'))));
      in
        map (map mk_goal) (mk_half_pairss (`I (xss ~~ xctrs)))
      end;

    val goalss = [exhaust_goal] :: inject_goalss @ half_distinct_goalss;

    fun after_qed ([exhaust_thm] :: thmss) lthy =
      let
        val ((((((((u, u'), (xss, xss')), fs), gs), h), v), p), _) = lthy
          |> add_bindings
          |> yield_singleton (apfst (op ~~) oo mk_Frees' fc_b_name) fcT
          ||>> mk_Freess' "x" ctr_Tss
          ||>> mk_Frees "f" case_Ts
          ||>> mk_Frees "g" case_Ts
          ||>> yield_singleton (mk_Frees "h") (B --> C)
          ||>> yield_singleton (mk_Frees (fc_b_name ^ "'")) fcT
          ||>> yield_singleton (mk_Frees "P") HOLogic.boolT;

        val xfs = map2 (curry Term.list_comb) fs xss;
        val xgs = map2 (curry Term.list_comb) gs xss;

        val fcase = Term.list_comb (casex, fs);

        val ufcase = fcase $ u;
        val vfcase = fcase $ v;

        val eta_fcase = Term.list_comb (casex, eta_fs);
        val eta_gcase = Term.list_comb (casex, eta_gs);

        val eta_ufcase = eta_fcase $ u;
        val eta_vgcase = eta_gcase $ v;

        fun mk_uu_eq () = HOLogic.mk_eq (u, u);

        val uv_eq = mk_Trueprop_eq (u, v);

        val ((inject_thms, inject_thmss), half_distinct_thmss) = chop n thmss |>> `flat;

        val rho_As =
          map (fn (T, U) => (dest_TVar T, Thm.ctyp_of lthy U))
            (map Logic.varifyT_global As ~~ As);

        fun inst_thm t thm =
          Thm.instantiate' [] [SOME (Thm.cterm_of lthy t)]
            (Thm.instantiate (TVars.make rho_As, Vars.empty) (Drule.zero_var_indexes thm));

        val uexhaust_thm = inst_thm u exhaust_thm;

        val exhaust_cases = map base_name_of_ctr ctrs;

        val other_half_distinct_thmss = map (map (fn thm => thm RS not_sym)) half_distinct_thmss;

        val (distinct_thms, (distinct_thmsss', distinct_thmsss)) =
          join_halves n half_distinct_thmss other_half_distinct_thmss ||> `transpose;

        val nchotomy_thm =
          let
            val goal =
              HOLogic.mk_Trueprop (HOLogic.mk_all (fst u', snd u',
                Library.foldr1 HOLogic.mk_disj exist_xs_u_eq_ctrs));
          in
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_nchotomy_tac ctxt n exhaust_thm)
            |> Thm.close_derivation \<^here>
          end;

        val case_thms =
          let
            val goals =
              @{map 3} (fn xctr => fn xf => fn xs =>
                fold_rev Logic.all (fs @ xs) (mk_Trueprop_eq (fcase $ xctr, xf))) xctrs xfs xss;
          in
            @{map 4} (fn k => fn goal => fn injects => fn distinctss =>
                Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                  mk_case_tac ctxt n k case_def injects distinctss)
                |> Thm.close_derivation \<^here>)
              ks goals inject_thmss distinct_thmsss
          end;

        val (case_cong_thm, case_cong_weak_thm) =
          let
            fun mk_prem xctr xs xf xg =
              fold_rev Logic.all xs (Logic.mk_implies (mk_Trueprop_eq (v, xctr),
                mk_Trueprop_eq (xf, xg)));

            val goal =
              Logic.list_implies (uv_eq :: @{map 4} mk_prem xctrs xss xfs xgs,
                 mk_Trueprop_eq (eta_ufcase, eta_vgcase));
            val weak_goal = Logic.mk_implies (uv_eq, mk_Trueprop_eq (ufcase, vfcase));
            val vars = Variable.add_free_names lthy goal [];
            val weak_vars = Variable.add_free_names lthy weak_goal [];
          in
            (Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
               mk_case_cong_tac ctxt uexhaust_thm case_thms),
             Goal.prove_sorry lthy weak_vars [] weak_goal (fn {context = ctxt, prems = _} =>
               etac ctxt arg_cong 1))
            |> apply2 (Thm.close_derivation \<^here>)
          end;

        val split_lhs = q $ ufcase;

        fun mk_split_conjunct xctr xs f_xs =
          list_all_free xs (HOLogic.mk_imp (HOLogic.mk_eq (u, xctr), q $ f_xs));
        fun mk_split_disjunct xctr xs f_xs =
          list_exists_free xs (HOLogic.mk_conj (HOLogic.mk_eq (u, xctr),
            HOLogic.mk_not (q $ f_xs)));

        fun mk_split_goal xctrs xss xfs =
          mk_Trueprop_eq (split_lhs, Library.foldr1 HOLogic.mk_conj
            (@{map 3} mk_split_conjunct xctrs xss xfs));
        fun mk_split_asm_goal xctrs xss xfs =
          mk_Trueprop_eq (split_lhs, HOLogic.mk_not (Library.foldr1 HOLogic.mk_disj
            (@{map 3} mk_split_disjunct xctrs xss xfs)));

        fun prove_split selss goal =
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
            mk_split_tac ctxt uexhaust_thm case_thms selss inject_thmss distinct_thmsss))
          |> Thm.close_derivation \<^here>;

        fun prove_split_asm asm_goal split_thm =
          Variable.add_free_names lthy asm_goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] asm_goal (fn {context = ctxt, ...} =>
            mk_split_asm_tac ctxt split_thm))
          |> Thm.close_derivation \<^here>;

        val (split_thm, split_asm_thm) =
          let
            val goal = mk_split_goal xctrs xss xfs;
            val asm_goal = mk_split_asm_goal xctrs xss xfs;

            val thm = prove_split (replicate n []) goal;
            val asm_thm = prove_split_asm asm_goal thm;
          in
            (thm, asm_thm)
          end;

        val (sel_defs, all_sel_thms, sel_thmss, nontriv_disc_defs, disc_thmss, nontriv_disc_thmss,
             discI_thms, nontriv_discI_thms, distinct_disc_thms, distinct_disc_thmsss,
             exhaust_disc_thms, exhaust_sel_thms, all_collapse_thms, safe_collapse_thms,
             expand_thms, split_sel_thms, split_sel_asm_thms, case_eq_if_thms, disc_eq_case_thms) =
          if no_discs_sels then
            ([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [])
          else
            let
              val udiscs = map (rapp u) discs;
              val uselss = map (map (rapp u)) selss;
              val usel_ctrs = map2 (curry Term.list_comb) ctrs uselss;
              val usel_fs = map2 (curry Term.list_comb) fs uselss;

              val vdiscs = map (rapp v) discs;
              val vselss = map (map (rapp v)) selss;

              fun make_sel_thm xs' case_thm sel_def =
                zero_var_indexes
                  (Variable.gen_all lthy
                    (Drule.rename_bvars'
                      (map (SOME o fst) xs')
                      (Thm.forall_intr_vars (case_thm RS (sel_def RS trans)))));

              val sel_thmss = @{map 3} (map oo make_sel_thm) xss' case_thms sel_defss;

              fun has_undefined_rhs thm =
                (case snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of thm))) of
                  Const (\<^const_name>\<open>undefined\<close>, _) => true
                | _ => false);

              val all_sel_thms =
                (if all_sels_distinct andalso null sel_default_eqs then
                   flat sel_thmss
                 else
                   map_product (fn s => fn (xs', c) => make_sel_thm xs' c s) sel_defs
                     (xss' ~~ case_thms))
                |> filter_out has_undefined_rhs;

              fun mk_unique_disc_def () =
                let
                  val m = the_single ms;
                  val goal = mk_Trueprop_eq (mk_uu_eq (), the_single exist_xs_u_eq_ctrs);
                  val vars = Variable.add_free_names lthy goal [];
                in
                  Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
                    mk_unique_disc_def_tac ctxt m uexhaust_thm)
                  |> Thm.close_derivation \<^here>
                end;

              fun mk_alternate_disc_def k =
                let
                  val goal =
                    mk_Trueprop_eq (alternate_disc_lhs (K (nth udiscs)) (3 - k),
                      nth exist_xs_u_eq_ctrs (k - 1));
                  val vars = Variable.add_free_names lthy goal [];
                in
                  Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, ...} =>
                    mk_alternate_disc_def_tac ctxt k (nth disc_defs (2 - k))
                      (nth distinct_thms (2 - k)) uexhaust_thm)
                  |> Thm.close_derivation \<^here>
                end;

              val has_alternate_disc_def =
                exists (fn def => Thm.eq_thm_prop (def, alternate_disc_no_def)) disc_defs;

              val nontriv_disc_defs = disc_defs
                |> filter_out (member Thm.eq_thm_prop [unique_disc_no_def, alternate_disc_no_def,
                  refl]);

              val disc_defs' =
                map2 (fn k => fn def =>
                  if Thm.eq_thm_prop (def, unique_disc_no_def) then mk_unique_disc_def ()
                  else if Thm.eq_thm_prop (def, alternate_disc_no_def) then mk_alternate_disc_def k
                  else def) ks disc_defs;

              val discD_thms = map (fn def => def RS iffD1) disc_defs';
              val discI_thms =
                map2 (fn m => fn def => funpow m (fn thm => exI RS thm) (def RS iffD2)) ms
                  disc_defs';
              val not_discI_thms =
                map2 (fn m => fn def => funpow m (fn thm => allI RS thm)
                    (unfold_thms lthy @{thms not_ex} (def RS @{thm ssubst[of _ _ Not]})))
                  ms disc_defs';

              val (disc_thmss', disc_thmss) =
                let
                  fun mk_thm discI _ [] = refl RS discI
                    | mk_thm _ not_discI [distinct] = distinct RS not_discI;
                  fun mk_thms discI not_discI distinctss = map (mk_thm discI not_discI) distinctss;
                in
                  @{map 3} mk_thms discI_thms not_discI_thms distinct_thmsss' |> `transpose
                end;

              val nontriv_disc_thmss =
                map2 (fn b => if is_disc_binding_valid b then I else K []) disc_bindings disc_thmss;

              fun is_discI_triv b =
                (n = 1 andalso Binding.is_empty b) orelse Binding.eq_name (b, equal_binding);

              val nontriv_discI_thms =
                flat (map2 (fn b => if is_discI_triv b then K [] else single) disc_bindings
                  discI_thms);

              val (distinct_disc_thms, (distinct_disc_thmsss', distinct_disc_thmsss)) =
                let
                  fun mk_goal [] = []
                    | mk_goal [((_, udisc), (_, udisc'))] =
                      [Logic.all u (Logic.mk_implies (HOLogic.mk_Trueprop udisc,
                         HOLogic.mk_Trueprop (HOLogic.mk_not udisc')))];

                  fun prove tac goal =
                    Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} => tac ctxt)
                    |> Thm.close_derivation \<^here>;

                  val half_pairss = mk_half_pairss (`I (ms ~~ discD_thms ~~ udiscs));

                  val half_goalss = map mk_goal half_pairss;
                  val half_thmss =
                    @{map 3} (fn [] => K (K []) | [goal] => fn [(((m, discD), _), _)] =>
                        fn disc_thm => [prove (fn ctxt =>
                          mk_half_distinct_disc_tac ctxt m discD disc_thm) goal])
                      half_goalss half_pairss (flat disc_thmss');

                  val other_half_goalss = map (mk_goal o map swap) half_pairss;
                  val other_half_thmss =
                    map2 (map2 (fn thm => prove (fn ctxt =>
                        mk_other_half_distinct_disc_tac ctxt thm))) half_thmss
                      other_half_goalss;
                in
                  join_halves n half_thmss other_half_thmss ||> `transpose
                  |>> has_alternate_disc_def ? K []
                end;

              val exhaust_disc_thm =
                let
                  fun mk_prem udisc = mk_imp_p [HOLogic.mk_Trueprop udisc];
                  val goal = fold_rev Logic.all [p, u] (mk_imp_p (map mk_prem udiscs));
                in
                  Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
                    mk_exhaust_disc_tac ctxt n exhaust_thm discI_thms)
                  |> Thm.close_derivation \<^here>
                end;

              val (safe_collapse_thms, all_collapse_thms) =
                let
                  fun mk_goal m udisc usel_ctr =
                    let
                      val prem = HOLogic.mk_Trueprop udisc;
                      val concl = mk_Trueprop_eq ((usel_ctr, u) |> m = 0 ? swap);
                    in
                      (prem aconv concl, Logic.all u (Logic.mk_implies (prem, concl)))
                    end;
                  val (trivs, goals) = @{map 3} mk_goal ms udiscs usel_ctrs |> split_list;
                  val thms =
                    @{map 5} (fn m => fn discD => fn sel_thms => fn triv => fn goal =>
                        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                          mk_collapse_tac ctxt m discD sel_thms ORELSE HEADGOAL (assume_tac ctxt))
                        |> Thm.close_derivation \<^here>
                        |> not triv ? perhaps (try (fn thm => refl RS thm)))
                      ms discD_thms sel_thmss trivs goals;
                in
                  (map_filter (fn (true, _) => NONE | (false, thm) => SOME thm) (trivs ~~ thms),
                   thms)
                end;

              val swapped_all_collapse_thms =
                map2 (fn m => fn thm => if m = 0 then thm else thm RS sym) ms all_collapse_thms;

              val exhaust_sel_thm =
                let
                  fun mk_prem usel_ctr = mk_imp_p [mk_Trueprop_eq (u, usel_ctr)];
                  val goal = fold_rev Logic.all [p, u] (mk_imp_p (map mk_prem usel_ctrs));
                in
                  Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
                    mk_exhaust_sel_tac ctxt n exhaust_disc_thm swapped_all_collapse_thms)
                  |> Thm.close_derivation \<^here>
                end;

              val expand_thm =
                let
                  fun mk_prems k udisc usels vdisc vsels =
                    (if k = n then [] else [mk_Trueprop_eq (udisc, vdisc)]) @
                    (if null usels then
                       []
                     else
                       [Logic.list_implies
                          (if n = 1 then [] else map HOLogic.mk_Trueprop [udisc, vdisc],
                             HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                               (map2 (curry HOLogic.mk_eq) usels vsels)))]);

                  val goal =
                    Library.foldr Logic.list_implies
                      (@{map 5} mk_prems ks udiscs uselss vdiscs vselss, uv_eq);
                  val uncollapse_thms =
                    map2 (fn thm => fn [] => thm | _ => thm RS sym) all_collapse_thms uselss;
                  val vars = Variable.add_free_names lthy goal [];
                in
                  Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
                    mk_expand_tac ctxt n ms (inst_thm u exhaust_disc_thm)
                      (inst_thm v exhaust_disc_thm) uncollapse_thms distinct_disc_thmsss
                      distinct_disc_thmsss')
                  |> Thm.close_derivation \<^here>
                end;

              val (split_sel_thm, split_sel_asm_thm) =
                let
                  val zss = map (K []) xss;
                  val goal = mk_split_goal usel_ctrs zss usel_fs;
                  val asm_goal = mk_split_asm_goal usel_ctrs zss usel_fs;

                  val thm = prove_split sel_thmss goal;
                  val asm_thm = prove_split_asm asm_goal thm;
                in
                  (thm, asm_thm)
                end;

              val case_eq_if_thm =
                let
                  val goal = mk_Trueprop_eq (ufcase, mk_IfN B udiscs usel_fs);
                  val vars = Variable.add_free_names lthy goal [];
                in
                  Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, ...} =>
                    mk_case_eq_if_tac ctxt n uexhaust_thm case_thms disc_thmss' sel_thmss)
                  |> Thm.close_derivation \<^here>
                end;

              val disc_eq_case_thms =
                let
                  fun const_of_bool b = if b then \<^const>\<open>True\<close> else \<^const>\<open>False\<close>;
                  fun mk_case_args n = map_index (fn (k, argTs) =>
                    fold_rev Term.absdummy argTs (const_of_bool (n = k))) ctr_Tss;
                  val goals = map_index (fn (n, udisc) =>
                    mk_Trueprop_eq (udisc, list_comb (casexBool, mk_case_args n) $ u)) udiscs;
                  val goal = Logic.mk_conjunction_balanced goals;
                  val vars = Variable.add_free_names lthy goal [];
                in
                  Goal.prove_sorry lthy vars [] goal
                    (fn {context = ctxt, ...} => mk_disc_eq_case_tac ctxt (Thm.cterm_of ctxt u)
                       exhaust_thm (flat nontriv_disc_thmss) distinct_thms case_thms)
                  |> Thm.close_derivation \<^here>
                  |> Conjunction.elim_balanced (length goals)
                end;
            in
              (sel_defs, all_sel_thms, sel_thmss, nontriv_disc_defs, disc_thmss, nontriv_disc_thmss,
               discI_thms, nontriv_discI_thms, distinct_disc_thms, distinct_disc_thmsss,
               [exhaust_disc_thm], [exhaust_sel_thm], all_collapse_thms, safe_collapse_thms,
               [expand_thm], [split_sel_thm], [split_sel_asm_thm], [case_eq_if_thm],
               disc_eq_case_thms)
            end;

        val case_distrib_thm =
          let
            val args = @{map 2} (fn f => fn argTs =>
              let val (args, _) = mk_Frees "x" argTs lthy in
                fold_rev Term.lambda args (h $ list_comb (f, args))
              end) fs ctr_Tss;
            val goal = mk_Trueprop_eq (h $ ufcase, list_comb (casexC, args) $ u);
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, ...} =>
              mk_case_distrib_tac ctxt (Thm.cterm_of ctxt u) exhaust_thm case_thms)
            |> Thm.close_derivation \<^here>
          end;

        val exhaust_case_names_attr = Attrib.internal (K (Rule_Cases.case_names exhaust_cases));
        val cases_type_attr = Attrib.internal (K (Induct.cases_type fcT_name));

        val nontriv_disc_eq_thmss =
          map (map (fn th => th RS @{thm eq_False[THEN iffD2]}
            handle THM _ => th RS @{thm eq_True[THEN iffD2]})) nontriv_disc_thmss;

        val anonymous_notes =
          [(map (fn th => th RS notE) distinct_thms, safe_elim_attrs),
           (flat nontriv_disc_eq_thmss, nitpicksimp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val notes =
          [(caseN, case_thms, nitpicksimp_attrs @ simp_attrs),
           (case_congN, [case_cong_thm], []),
           (case_cong_weak_thmsN, [case_cong_weak_thm], cong_attrs),
           (case_distribN, [case_distrib_thm], []),
           (case_eq_ifN, case_eq_if_thms, []),
           (collapseN, safe_collapse_thms, if ms = [0] then [] else simp_attrs),
           (discN, flat nontriv_disc_thmss, simp_attrs),
           (disc_eq_caseN, disc_eq_case_thms, []),
           (discIN, nontriv_discI_thms, []),
           (distinctN, distinct_thms, simp_attrs @ inductsimp_attrs),
           (distinct_discN, distinct_disc_thms, dest_attrs),
           (exhaustN, [exhaust_thm], [exhaust_case_names_attr, cases_type_attr]),
           (exhaust_discN, exhaust_disc_thms, [exhaust_case_names_attr]),
           (exhaust_selN, exhaust_sel_thms, [exhaust_case_names_attr]),
           (expandN, expand_thms, []),
           (injectN, inject_thms, iff_attrs @ inductsimp_attrs),
           (nchotomyN, [nchotomy_thm], []),
           (selN, all_sel_thms, nitpicksimp_attrs @ simp_attrs),
           (splitN, [split_thm], []),
           (split_asmN, [split_asm_thm], []),
           (split_selN, split_sel_thms, []),
           (split_sel_asmN, split_sel_asm_thms, []),
           (split_selsN, split_sel_thms @ split_sel_asm_thms, []),
           (splitsN, [split_thm, split_asm_thm], [])]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((qualify true (Binding.name thmN), attrs), [(thms, [])]));

        val (noted, lthy') = lthy
          |> Spec_Rules.add Binding.empty Spec_Rules.equational [casex] case_thms
          |> fold (uncurry (Spec_Rules.add Binding.empty Spec_Rules.equational))
            (AList.group (eq_list (op aconv)) (map (`(single o lhs_head_of)) all_sel_thms))
          |> fold (uncurry (Spec_Rules.add Binding.empty Spec_Rules.equational))
            (filter_out (null o snd) (map single discs ~~ nontriv_disc_eq_thmss))
          |> Local_Theory.declaration {syntax = false, pervasive = true}
            (fn phi => Case_Translation.register
               (Morphism.term phi casex) (map (Morphism.term phi) ctrs))
          |> plugins code_plugin ?
             (Code.declare_default_eqns (map (rpair true) (flat nontriv_disc_eq_thmss @ case_thms @ all_sel_thms))
             #> Local_Theory.declaration {syntax = false, pervasive = false}
               (fn phi => Context.mapping
                  (add_ctr_code fcT_name (map (Morphism.typ phi) As)
                     (map (dest_Const o Morphism.term phi) ctrs) (Morphism.fact phi inject_thms)
                     (Morphism.fact phi distinct_thms) (Morphism.fact phi case_thms))
                  I))
          |> Local_Theory.notes (anonymous_notes @ notes)
          (* for "datatype_realizer.ML": *)
          |>> name_noted_thms fcT_name exhaustN;

        val ctr_sugar =
          {kind = kind, T = fcT, ctrs = ctrs, casex = casex, discs = discs, selss = selss,
           exhaust = exhaust_thm, nchotomy = nchotomy_thm, injects = inject_thms,
           distincts = distinct_thms, case_thms = case_thms, case_cong = case_cong_thm,
           case_cong_weak = case_cong_weak_thm, case_distribs = [case_distrib_thm],
           split = split_thm, split_asm = split_asm_thm, disc_defs = nontriv_disc_defs,
           disc_thmss = disc_thmss, discIs = discI_thms, disc_eq_cases = disc_eq_case_thms,
           sel_defs = sel_defs, sel_thmss = sel_thmss, distinct_discsss = distinct_disc_thmsss,
           exhaust_discs = exhaust_disc_thms, exhaust_sels = exhaust_sel_thms,
           collapses = all_collapse_thms, expands = expand_thms, split_sels = split_sel_thms,
           split_sel_asms = split_sel_asm_thms, case_eq_ifs = case_eq_if_thms}
          |> morph_ctr_sugar (substitute_noted_thm noted);
      in
        (ctr_sugar, lthy' |> register_ctr_sugar plugins ctr_sugar)
      end;
  in
    (goalss, after_qed, lthy)
  end;

fun free_constructors kind tacss = (fn (goalss, after_qed, lthy) =>
  map2 (map2 (Thm.close_derivation \<^here> oo Goal.prove_sorry lthy [] [])) goalss tacss
  |> (fn thms => after_qed thms lthy)) oo prepare_free_constructors kind (K I) (K I);

fun free_constructors_cmd kind = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE (snd oo after_qed) (map (map (rpair [])) goalss) lthy) oo
  prepare_free_constructors kind Plugin_Name.make_filter Syntax.read_term;

val parse_bound_term = Parse.binding --| \<^keyword>\<open>:\<close> -- Parse.term;

type ctr_options = Plugin_Name.filter * bool;
type ctr_options_cmd = (Proof.context -> Plugin_Name.filter) * bool;

val default_ctr_options : ctr_options = (Plugin_Name.default_filter, false);
val default_ctr_options_cmd : ctr_options_cmd = (K Plugin_Name.default_filter, false);

val parse_ctr_options =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.list1
        (Plugin_Name.parse_filter >> (apfst o K)
         || Parse.reserved "discs_sels" >> (apsnd o K o K true)) --|
      \<^keyword>\<open>)\<close>
      >> (fn fs => fold I fs default_ctr_options_cmd))
    default_ctr_options_cmd;

fun parse_ctr_spec parse_ctr parse_arg =
  parse_opt_binding_colon -- parse_ctr -- Scan.repeat parse_arg;

val parse_ctr_specs = Parse.enum1 "|" (parse_ctr_spec Parse.term Parse.binding);
val parse_sel_default_eqs = Scan.optional (\<^keyword>\<open>where\<close> |-- Parse.enum1 "|" Parse.prop) [];

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>free_constructors\<close>
    "register an existing freely generated type's constructors"
    (parse_ctr_options -- Parse.binding --| \<^keyword>\<open>for\<close> -- parse_ctr_specs
       -- parse_sel_default_eqs
     >> free_constructors_cmd Unknown);



(** external views **)

(* document antiquotations *)

local

fun antiquote_setup binding co =
  Document_Output.antiquotation_pretty_source_embedded binding
    ((Scan.ahead (Scan.lift Parse.not_eof) >> Token.pos_of) --
      Args.type_name {proper = true, strict = true})
    (fn ctxt => fn (pos, type_name) =>
      let
        fun err () =
          error ("Bad " ^ Binding.name_of binding ^ ": " ^ quote type_name ^ Position.here pos);
      in
        (case ctr_sugar_of ctxt type_name of
          NONE => err ()
        | SOME {kind, T = T0, ctrs = ctrs0, ...} =>
            let
              val _ = if co = (kind = Codatatype) then () else err ();

              val T = Logic.unvarifyT_global T0;
              val ctrs = map Logic.unvarify_global ctrs0;

              val pretty_typ_bracket = Syntax.pretty_typ (Config.put pretty_priority 1001 ctxt);
              fun pretty_ctr ctr =
                Pretty.block (Pretty.breaks (Syntax.pretty_term ctxt ctr ::
                  map pretty_typ_bracket (binder_types (fastype_of ctr))));
            in
              Pretty.block (Pretty.keyword1 (Binding.name_of binding) :: Pretty.brk 1 ::
                Syntax.pretty_typ ctxt T :: Pretty.str " =" :: Pretty.brk 1 ::
                flat (separate [Pretty.brk 1, Pretty.str "| "] (map (single o pretty_ctr) ctrs)))
            end)
        end);

in

val _ =
  Theory.setup
   (antiquote_setup \<^binding>\<open>datatype\<close> false #>
    antiquote_setup \<^binding>\<open>codatatype\<close> true);

end;


(* theory export *)

val _ =
  (Theory.setup o Thy_Info.add_presentation) (fn context => fn thy =>
    if Export_Theory.export_enabled context then
      let
        val parents = map (Data.get o Context.Theory) (Theory.parents_of thy);
        val datatypes =
          (Data.get (Context.Theory thy), []) |-> Symtab.fold
            (fn (name, (pos, {kind, T, ctrs, ...})) =>
              if kind = Record orelse exists (fn tab => Symtab.defined tab name) parents then I
              else
                let
                  val pos_properties = Thy_Info.adjust_pos_properties context pos;
                  val typ = Logic.unvarifyT_global T;
                  val constrs = map Logic.unvarify_global ctrs;
                  val typargs = rev (fold Term.add_tfrees (Logic.mk_type typ :: constrs) []);
                  val constructors = map (fn t => (t, Term.type_of t)) constrs;
                in
                  cons (pos_properties, (name, (kind = Codatatype, (typargs, (typ, constructors)))))
                end);
      in
        if null datatypes then ()
        else
          Export_Theory.export_body thy "datatypes"
            let open XML.Encode Term_XML.Encode in
              list (pair properties (pair string (pair bool (pair (list (pair string sort))
                (pair typ (list (pair (term (Sign.consts_of thy)) typ))))))) datatypes
            end
      end
    else ());

end;
