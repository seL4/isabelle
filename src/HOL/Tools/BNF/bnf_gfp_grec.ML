(*  Title:      HOL/Tools/BNF/bnf_gfp_grec.ML
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Dmitriy Traytel, ETH Zürich
    Copyright   2015, 2016

Generalized corecursor construction.
*)

signature BNF_GFP_GREC =
sig
  val Tsubst: typ -> typ -> typ -> typ
  val substT: typ -> typ -> term -> term
  val freeze_types: Proof.context -> (indexname * sort) list -> typ list -> typ list
  val dummify_atomic_types: term -> term
  val define_const: bool -> binding -> int -> string -> term -> local_theory ->
    (term * thm) * local_theory

  type buffer =
    {Oper: term,
     VLeaf: term,
     CLeaf: term,
     ctr_wrapper: term,
     friends: (typ * term) Symtab.table}

  val map_buffer: (term -> term) -> buffer -> buffer
  val specialize_buffer_types: buffer -> buffer

  type dtor_coinduct_info =
    {dtor_coinduct: thm,
     cong_def: thm,
     cong_locale: thm,
     cong_base: thm,
     cong_refl: thm,
     cong_sym: thm,
     cong_trans: thm,
     cong_alg_intros: thm list}

  type corec_info =
    {fp_b: binding,
     version: int,
     fpT: typ,
     Y: typ,
     Z: typ,
     friend_names: string list,
     sig_fp_sugars: BNF_FP_Def_Sugar.fp_sugar list,
     ssig_fp_sugar: BNF_FP_Def_Sugar.fp_sugar,
     Lam: term,
     proto_sctr: term,
     flat: term,
     eval_core: term,
     eval: term,
     algLam: term,
     corecUU: term,
     dtor_transfer: thm,
     Lam_transfer: thm,
     Lam_pointful_natural: thm,
     proto_sctr_transfer: thm,
     flat_simps: thm list,
     eval_core_simps: thm list,
     eval_thm: thm,
     eval_simps: thm list,
     all_algLam_algs: thm list,
     algLam_thm: thm,
     dtor_algLam: thm,
     corecUU_thm: thm,
     corecUU_unique: thm,
     corecUU_transfer: thm,
     buffer: buffer,
     all_dead_k_bnfs: BNF_Def.bnf list,
     Retr: term,
     equivp_Retr: thm,
     Retr_coinduct: thm,
     dtor_coinduct_info: dtor_coinduct_info}

  type friend_info =
    {algrho: term,
     dtor_algrho: thm,
     algLam_algrho: thm}

  val not_codatatype: Proof.context -> typ -> 'a
  val mk_fp_binding: binding -> string -> binding
  val bnf_kill_all_but: int -> BNF_Def.bnf -> local_theory -> BNF_Def.bnf * local_theory

  val print_corec_infos: Proof.context -> unit
  val has_no_corec_info: Proof.context -> string -> bool
  val corec_info_of: typ -> local_theory -> corec_info * local_theory
  val maybe_corec_info_of: Proof.context -> typ -> corec_info option
  val corec_infos_of: Proof.context -> string -> corec_info list
  val corec_infos_of_generic: Context.generic -> Symtab.key -> corec_info list
  val prepare_friend_corec: string -> typ -> local_theory ->
    (corec_info * binding * int * typ * typ * typ * typ * typ * BNF_Def.bnf * BNF_Def.bnf
     * BNF_FP_Def_Sugar.fp_sugar * BNF_FP_Def_Sugar.fp_sugar * buffer) * local_theory
  val register_friend_corec: string -> binding -> int -> typ -> typ -> typ -> BNF_Def.bnf ->
    BNF_FP_Def_Sugar.fp_sugar -> BNF_FP_Def_Sugar.fp_sugar -> term -> term -> thm -> corec_info ->
    local_theory -> friend_info * local_theory
end;

structure BNF_GFP_Grec : BNF_GFP_GREC =
struct

open Ctr_Sugar
open BNF_Util
open BNF_Def
open BNF_Comp
open BNF_FP_Util
open BNF_LFP
open BNF_FP_Def_Sugar
open BNF_LFP_Rec_Sugar
open BNF_GFP_Grec_Tactics

val algLamN = "algLam";
val algLam_algLamN = "algLam_algLam";
val algLam_algrhoN = "algLam_algrho";
val algrhoN = "algrho";
val CLeafN = "CLeaf";
val congN = "congclp";
val cong_alg_introsN = "cong_alg_intros";
val cong_localeN = "cong_locale";
val corecUUN = "corecUU";
val corecUU_transferN = "corecUU_transfer";
val corecUU_uniqueN = "corecUU_unique";
val cutSsigN = "cutSsig";
val dtor_algLamN = "dtor_algLam";
val dtor_algrhoN = "dtor_algrho";
val dtor_coinductN = "dtor_coinduct";
val dtor_transferN = "dtor_transfer";
val embLN = "embL";
val embLLN = "embLL";
val embLRN = "embLR";
val embL_pointful_naturalN = "embL_pointful_natural";
val embL_transferN = "embL_transfer";
val equivp_RetrN = "equivp_Retr";
val evalN = "eval";
val eval_coreN = "eval_core";
val eval_core_pointful_naturalN = "eval_core_pointful_natural";
val eval_core_transferN = "eval_core_transfer";
val eval_flatN = "eval_flat";
val eval_simpsN = "eval_simps";
val flatN = "flat";
val flat_pointful_naturalN = "flat_pointful_natural";
val flat_transferN = "flat_transfer";
val k_as_ssig_naturalN = "k_as_ssig_natural";
val k_as_ssig_transferN = "k_as_ssig_transfer";
val LamN = "Lam";
val Lam_transferN = "Lam_transfer";
val Lam_pointful_naturalN = "Lam_pointful_natural";
val OperN = "Oper";
val proto_sctrN = "proto_sctr";
val proto_sctr_pointful_naturalN = "proto_sctr_pointful_natural";
val proto_sctr_transferN = "proto_sctr_transfer";
val rho_transferN = "rho_transfer";
val Retr_coinductN = "Retr_coinduct";
val sctrN = "sctr";
val sctr_transferN = "sctr_transfer";
val sctr_pointful_naturalN = "sctr_pointful_natural";
val sigN = "sig";
val SigN = "Sig";
val Sig_pointful_naturalN = "Sig_pointful_natural";
val corecUN = "corecU";
val corecU_ctorN = "corecU_ctor";
val corecU_uniqueN = "corecU_unique";
val unsigN = "unsig";
val VLeafN = "VLeaf";

val s_prefix = "s"; (* transforms "sig" into "ssig" *)

fun not_codatatype ctxt T =
  error ("Not a codatatype: " ^ Syntax.string_of_typ ctxt T);
fun mutual_codatatype () =
  error ("Mutually corecursive codatatypes are not supported (try " ^
    quote (#1 \<^command_keyword>\<open>primcorec\<close>) ^ " instead of " ^
    quote (#1 \<^command_keyword>\<open>corec\<close>) ^ ")");
fun noncorecursive_codatatype () =
  error ("Noncorecursive codatatypes are not supported (try " ^
    quote (#1 \<^command_keyword>\<open>definition\<close>) ^ " instead of " ^
    quote (#1 \<^command_keyword>\<open>corec\<close>) ^ ")");
fun singleton_codatatype ctxt =
  error ("Singleton corecursive codatatypes are not supported (use " ^
    quote (Syntax.string_of_typ ctxt \<^typ>\<open>unit\<close>) ^ " instead)");

fun merge_lists eq old1 old2 = (old1 |> subtract eq old2) @ old2;

fun add_type_namesT (Type (s, Ts)) = insert (op =) s #> fold add_type_namesT Ts
  | add_type_namesT _ = I;

fun Tsubst Y T = Term.typ_subst_atomic [(Y, T)];
fun substT Y T = Term.subst_atomic_types [(Y, T)];

fun freeze_types ctxt except_tvars Ts =
  let
    val As = fold Term.add_tvarsT Ts [] |> subtract (op =) except_tvars;
    val (Bs, _) = ctxt |> mk_TFrees' (map snd As);
  in
    map (Term.typ_subst_TVars (map fst As ~~ Bs)) Ts
  end;

fun typ_unify_disjointly thy (T, T') =
  if T = T' then
    T
  else
    let
      val tvars = Term.add_tvar_namesT T [];
      val tvars' = Term.add_tvar_namesT T' [];
      val maxidx' = maxidx_of_typ T';
      val T = T |> exists (member (op =) tvars') tvars ? Logic.incr_tvar (maxidx' + 1);
      val maxidx = Integer.max (maxidx_of_typ T) maxidx';
      val (tyenv, _) = Sign.typ_unify thy (T, T') (Vartab.empty, maxidx);
    in
      Envir.subst_type tyenv T
    end;

val dummify_atomic_types = Term.map_types (Term.map_atyps (K Term.dummyT));

fun mk_internal internal ctxt f =
  if internal andalso not (Config.get ctxt bnf_internals) then f else I
fun mk_fp_binding fp_b pre = Binding.map_name (K pre) fp_b
  |> Binding.qualify true (Binding.name_of fp_b);
fun mk_version_binding version = Binding.qualify false ("v" ^ string_of_int version);
fun mk_version_fp_binding internal ctxt =
  mk_internal internal ctxt Binding.concealed ooo (mk_fp_binding oo mk_version_binding);
(*FIXME: get rid of ugly names when typedef and primrec respect qualification*)
fun mk_version_binding_ugly version = Binding.suffix_name ("_v" ^ string_of_int version);
fun mk_version_fp_binding_ugly internal ctxt version fp_b pre =
  Binding.prefix_name (pre ^ "_") fp_b
  |> mk_version_binding_ugly version
  |> mk_internal internal ctxt Binding.concealed;

fun mk_mapN ctxt live_AsBs TA bnf =
  let val TB = Term.typ_subst_atomic live_AsBs TA in
    enforce_type ctxt (snd o strip_typeN (length live_AsBs)) (TA --> TB) (map_of_bnf bnf)
  end;

fun mk_relN ctxt live_AsBs TA bnf =
  let val TB = Term.typ_subst_atomic live_AsBs TA in
    enforce_type ctxt (snd o strip_typeN (length live_AsBs)) (mk_pred2T TA TB) (rel_of_bnf bnf)
  end;

fun mk_map1 ctxt Y Z = mk_mapN ctxt [(Y, Z)];
fun mk_rel1 ctxt Y Z = mk_relN ctxt [(Y, Z)];

fun define_const internal fp_b version name rhs lthy =
  let
    val b = mk_version_fp_binding internal lthy version fp_b name;

    val ((free, (_, def_free)), (lthy, lthy_old)) = lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((b, NoSyn), ((Thm.def_binding b |> Binding.concealed, []), rhs))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val const = Morphism.term phi free;
    val const' = enforce_type lthy I (fastype_of free) const;
  in
    ((const', Morphism.thm phi def_free), lthy)
  end;

fun define_single_primrec b eqs lthy =
  let
    val (([free], [def_free], [simps_free]), (lthy, lthy_old)) = lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.map_background_naming (mk_internal true lthy Name_Space.concealed) (*TODO check*)
      |> primrec false [] [(b, NONE, NoSyn)] (map (fn eq => ((Binding.empty_atts, eq), [], [])) eqs)
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val const = Morphism.term phi free;
    val const' = enforce_type lthy I (fastype_of free) const;
  in
    ((const', Morphism.thm phi def_free, map (Morphism.thm phi) simps_free), lthy)
  end;

type buffer =
  {Oper: term,
   VLeaf: term,
   CLeaf: term,
   ctr_wrapper: term,
   friends: (typ * term) Symtab.table};

fun map_buffer f {Oper, VLeaf, CLeaf, ctr_wrapper, friends} =
  {Oper = f Oper, VLeaf = f VLeaf, CLeaf = f CLeaf, ctr_wrapper = f ctr_wrapper,
   friends = Symtab.map (K (apsnd f)) friends};

fun morph_buffer phi = map_buffer (Morphism.term phi);

fun specialize_buffer_types {Oper, VLeaf, CLeaf, ctr_wrapper, friends} =
  let
    val ssig_T as Type (_, Ts) = body_type (fastype_of VLeaf);
    val Y = List.last Ts;
    val ssigifyT = substT Y ssig_T;
  in
    {Oper = Oper, VLeaf = VLeaf, CLeaf = CLeaf, ctr_wrapper = ssigifyT ctr_wrapper,
     friends = Symtab.map (K (apsnd ssigifyT)) friends}
  end;

type dtor_coinduct_info =
  {dtor_coinduct: thm,
   cong_def: thm,
   cong_locale: thm,
   cong_base: thm,
   cong_refl: thm,
   cong_sym: thm,
   cong_trans: thm,
   cong_alg_intros: thm list};

fun map_dtor_coinduct_info f {dtor_coinduct, cong_def, cong_locale, cong_base, cong_refl, cong_sym,
    cong_trans, cong_alg_intros} =
  {dtor_coinduct = f dtor_coinduct, cong_def = f cong_def, cong_locale = f cong_locale,
   cong_base = f cong_base, cong_refl = f cong_refl, cong_sym = f cong_sym,
   cong_trans = f cong_trans, cong_alg_intros = map f cong_alg_intros};

fun morph_dtor_coinduct_info phi = map_dtor_coinduct_info (Morphism.thm phi);

type corec_ad =
  {fpT: typ,
   friend_names: string list};

fun morph_corec_ad phi {fpT, friend_names} =
  {fpT = Morphism.typ phi fpT, friend_names = friend_names};

type corec_info =
  {fp_b: binding,
   version: int,
   fpT: typ,
   Y: typ,
   Z: typ,
   friend_names: string list,
   sig_fp_sugars: fp_sugar list,
   ssig_fp_sugar: fp_sugar,
   Lam: term,
   proto_sctr: term,
   flat: term,
   eval_core: term,
   eval: term,
   algLam: term,
   corecUU: term,
   dtor_transfer: thm,
   Lam_transfer: thm,
   Lam_pointful_natural: thm,
   proto_sctr_transfer: thm,
   flat_simps: thm list,
   eval_core_simps: thm list,
   eval_thm: thm,
   eval_simps: thm list,
   all_algLam_algs: thm list,
   algLam_thm: thm,
   dtor_algLam: thm,
   corecUU_thm: thm,
   corecUU_unique: thm,
   corecUU_transfer: thm,
   buffer: buffer,
   all_dead_k_bnfs: bnf list,
   Retr: term,
   equivp_Retr: thm,
   Retr_coinduct: thm,
   dtor_coinduct_info: dtor_coinduct_info};

fun morph_corec_info phi
    ({fp_b, version, fpT, Y, Z, friend_names, sig_fp_sugars, ssig_fp_sugar, Lam, proto_sctr, flat,
      eval_core, eval, algLam, corecUU, dtor_transfer, Lam_transfer, Lam_pointful_natural,
      proto_sctr_transfer, flat_simps, eval_core_simps, eval_thm, eval_simps, all_algLam_algs,
      algLam_thm, dtor_algLam, corecUU_thm, corecUU_unique, corecUU_transfer, buffer,
      all_dead_k_bnfs, Retr, equivp_Retr, Retr_coinduct, dtor_coinduct_info} : corec_info) =
  {fp_b = fp_b, version = version, fpT = Morphism.typ phi fpT, Y = Morphism.typ phi Y,
   Z = Morphism.typ phi Z, friend_names = friend_names, sig_fp_sugars = sig_fp_sugars (*no morph*),
   ssig_fp_sugar = ssig_fp_sugar (*no morph*), Lam = Morphism.term phi Lam,
   proto_sctr = Morphism.term phi proto_sctr, flat = Morphism.term phi flat,
   eval_core = Morphism.term phi eval_core, eval = Morphism.term phi eval,
   algLam = Morphism.term phi algLam, corecUU = Morphism.term phi corecUU,
   dtor_transfer = dtor_transfer, Lam_transfer = Morphism.thm phi Lam_transfer,
   Lam_pointful_natural = Morphism.thm phi Lam_pointful_natural,
   proto_sctr_transfer = Morphism.thm phi proto_sctr_transfer,
   flat_simps = map (Morphism.thm phi) flat_simps,
   eval_core_simps = map (Morphism.thm phi) eval_core_simps, eval_thm = Morphism.thm phi eval_thm,
   eval_simps = map (Morphism.thm phi) eval_simps,
   all_algLam_algs = map (Morphism.thm phi) all_algLam_algs,
   algLam_thm = Morphism.thm phi algLam_thm, dtor_algLam = Morphism.thm phi dtor_algLam,
   corecUU_thm = Morphism.thm phi corecUU_thm, corecUU_unique = Morphism.thm phi corecUU_unique,
   corecUU_transfer = Morphism.thm phi corecUU_transfer, buffer = morph_buffer phi buffer,
   all_dead_k_bnfs = map (morph_bnf phi) all_dead_k_bnfs, Retr = Morphism.term phi Retr,
   equivp_Retr = Morphism.thm phi equivp_Retr, Retr_coinduct = Morphism.thm phi Retr_coinduct,
   dtor_coinduct_info = morph_dtor_coinduct_info phi dtor_coinduct_info};

datatype ('a, 'b) expr =
  Ad of 'a * (local_theory -> 'b * local_theory) |
  Info of 'b;

fun is_Ad (Ad _) = true
  | is_Ad _ = false;

fun is_Info (Info _) = true
  | is_Info _ = false;

type corec_info_expr = (corec_ad, corec_info) expr;

fun morph_corec_info_expr phi (Ad (ad, f)) = Ad (morph_corec_ad phi ad, f)
  | morph_corec_info_expr phi (Info info) = Info (morph_corec_info phi info);

val transfer_corec_info_expr = morph_corec_info_expr o Morphism.transfer_morphism;

type corec_data = int Symtab.table * corec_info_expr list Symtab.table list;

structure Data = Generic_Data
(
  type T = corec_data;
  val empty = (Symtab.empty, [Symtab.empty]);
  val extend = I;
  fun merge ((version_tab1, info_tabs1), (version_tab2, info_tabs2)) : T =
    (Symtab.join (K Int.max) (version_tab1, version_tab2), info_tabs1 @ info_tabs2);
);

fun corec_ad_of_expr (Ad (ad, _)) = ad
  | corec_ad_of_expr (Info {fpT, friend_names, ...}) = {fpT = fpT, friend_names = friend_names};

fun corec_info_exprs_of_generic context fpT_name =
  let
    val thy = Context.theory_of context;
    val info_tabs = snd (Data.get context);
  in
    maps (fn info_tab => these (Symtab.lookup info_tab fpT_name)) info_tabs
    |> map (transfer_corec_info_expr thy)
  end;

val corec_info_exprs_of = corec_info_exprs_of_generic o Context.Proof;

val keep_corec_infos = map_filter (fn Ad _ => NONE | Info info => SOME info);

val corec_infos_of_generic = keep_corec_infos oo corec_info_exprs_of_generic;
val corec_infos_of = keep_corec_infos oo corec_info_exprs_of;

fun str_of_corec_ad ctxt {fpT, friend_names} =
  "[" ^ Syntax.string_of_typ ctxt fpT ^ "; " ^ commas friend_names ^ "]";

fun str_of_corec_info ctxt {fpT, version, friend_names, ...} =
  "{" ^ Syntax.string_of_typ ctxt fpT ^ "; " ^ commas friend_names ^ "; v" ^ string_of_int version ^
  "}";

fun str_of_corec_info_expr ctxt (Ad (ad, _)) = str_of_corec_ad ctxt ad
  | str_of_corec_info_expr ctxt (Info info) = str_of_corec_info ctxt info;

fun print_corec_infos ctxt =
  Symtab.fold (fn (fpT_name, exprs) => fn () =>
      writeln (fpT_name ^ ":\n" ^
        cat_lines (map (prefix "  " o str_of_corec_info_expr ctxt) exprs)))
    (the_single (snd (Data.get (Context.Proof ctxt)))) ();

val has_no_corec_info = null oo corec_info_exprs_of;

fun get_name_next_version_of fpT_name ctxt =
  let
    val (version_tab, info_tabs) = Data.get (Context.Theory (Proof_Context.theory_of ctxt));
    val fp_base = Long_Name.base_name fpT_name;
    val fp_b = Binding.name fp_base;
    val version_tab' = Symtab.map_default (fp_base, ~1) (Integer.add 1) version_tab;
    val SOME version = Symtab.lookup version_tab' fp_base;
    val ctxt' = ctxt
      |> Local_Theory.background_theory (Context.theory_map (Data.put (version_tab', info_tabs)));
  in
    ((fp_b, version), ctxt')
  end;

type friend_info =
  {algrho: term,
   dtor_algrho: thm,
   algLam_algrho: thm};

fun morph_friend_info phi ({algrho, dtor_algrho, algLam_algrho} : friend_info) =
  {algrho = Morphism.term phi algrho, dtor_algrho = Morphism.thm phi dtor_algrho,
   algLam_algrho = Morphism.thm phi algLam_algrho};

fun checked_fp_sugar_of ctxt fpT_name =
  let
    val fp_sugar as {X, fp_res = {Ts = fpTs, ...}, fp_ctr_sugar = {ctrXs_Tss, ...}, ...} =
      (case fp_sugar_of ctxt fpT_name of
        SOME (fp_sugar as {fp = Greatest_FP, ...}) => fp_sugar
      | _ => not_codatatype ctxt (Type (fpT_name, [] (*yuck*))));

    val _ =
      if length fpTs > 1 then
        mutual_codatatype ()
      else if not (exists (exists (Term.exists_subtype (curry (op =) X))) ctrXs_Tss) then
        noncorecursive_codatatype ()
      else if ctrXs_Tss = [[X]] then
        singleton_codatatype ctxt
      else
        ();
  in
    fp_sugar
  end;

fun bnf_kill_all_but nn bnf lthy =
  ((empty_comp_cache, empty_unfolds), lthy)
  |> kill_bnf I (live_of_bnf bnf - nn) bnf
  ||> snd;

fun bnf_with_deads_and_lives dead_Es live_As Y fpT T lthy =
   let
     val qsoty = quote o Syntax.string_of_typ lthy;

     val unfreeze_fp = Tsubst Y fpT;

    fun flatten_tyargs Ass =
      map dest_TFree live_As
      |> filter (fn T => exists (fn Ts => member (op =) Ts T) Ass);

    val ((bnf, _), (_, lthy)) =
      bnf_of_typ false Do_Inline I flatten_tyargs [Term.dest_TFree Y] (map Term.dest_TFree dead_Es)
        T ((empty_comp_cache, empty_unfolds), lthy)
      handle BAD_DEAD (Y, Y_backdrop) =>
        (case Y_backdrop of
          Type (bad_tc, _) =>
          let
            val T = qsoty (unfreeze_fp Y);
            val T_backdrop = qsoty (unfreeze_fp Y_backdrop);
            fun register_hint () =
              "\nUse the " ^ quote (#1 \<^command_keyword>\<open>bnf\<close>) ^ " command to register " ^
              quote bad_tc ^ " as a bounded natural functor to allow nested (co)recursion through \
              \it";
          in
            if is_some (bnf_of lthy bad_tc) orelse is_some (fp_sugar_of lthy bad_tc) then
              error ("Inadmissible occurrence of type " ^ T ^ " in type expression " ^
                T_backdrop)
            else
              error ("Unsupported occurrence of type " ^ T ^ " via type constructor " ^
                quote bad_tc ^ " in type expression " ^ T_backdrop ^ register_hint ())
          end);

    val phi =
      Morphism.term_morphism "BNF" (Raw_Simplifier.rewrite_term (Proof_Context.theory_of lthy)
        @{thms BNF_Composition.id_bnf_def} [])
      $> Morphism.thm_morphism "BNF" (unfold_thms lthy @{thms BNF_Composition.id_bnf_def});
  in
    (morph_bnf phi bnf, lthy)
  end;

fun define_sig_type fp_b version fp_alives Es Y rhsT lthy =
  let
    val T_b = mk_version_fp_binding_ugly true lthy version fp_b sigN;
    val ctr_b = mk_version_fp_binding false lthy version fp_b SigN;
    val sel_b = mk_version_fp_binding true lthy version fp_b unsigN;

    val lthy = (snd o Local_Theory.begin_nested) lthy;

    val T_name = Local_Theory.full_name lthy T_b;

    val tyargs = map2 (fn alive => fn T =>
        (if alive then SOME Binding.empty else NONE, (T, Type.sort_of_atyp T)))
      (fp_alives @ [true]) (Es @ [Y]);
    val ctr_specs = [(((Binding.empty, ctr_b), [(sel_b, rhsT)]), NoSyn)];
    val spec = (((((tyargs, T_b), NoSyn), ctr_specs),
      (Binding.empty, Binding.empty, Binding.empty)), []);

    val plugins = Plugin_Name.make_filter lthy (K (curry (op =) transfer_plugin));
    val discs_sels = true;

    val lthy = lthy
      |> Local_Theory.map_background_naming (mk_internal true lthy Name_Space.concealed) (*TODO check*)
      |> with_typedef_threshold ~1
        (co_datatypes Least_FP construct_lfp ((plugins, discs_sels), [spec]))
      |> Local_Theory.end_nested;

    val SOME fp_sugar = fp_sugar_of lthy T_name;
  in
    (fp_sugar, lthy)
  end;

fun define_ssig_type fp_b version fp_alives Es Y fpT lthy =
  let
    val sig_T_b = mk_version_fp_binding_ugly true lthy version fp_b sigN;
    val T_b = Binding.prefix_name s_prefix sig_T_b;
    val Oper_b = mk_version_fp_binding false lthy version fp_b OperN;
    val VLeaf_b = mk_version_fp_binding false lthy version fp_b VLeafN;
    val CLeaf_b = mk_version_fp_binding false lthy version fp_b CLeafN;

    val lthy = (snd o Local_Theory.begin_nested) lthy;

    val sig_T_name = Local_Theory.full_name lthy sig_T_b;
    val T_name = Long_Name.map_base_name (prefix s_prefix) sig_T_name;

    val As = Es @ [Y];
    val ssig_sig_T = Type (sig_T_name, Es @ [Type (T_name, As)]);

    val tyargs = map2 (fn alive => fn T =>
        (if alive then SOME Binding.empty else NONE, (T, Type.sort_of_atyp T)))
      (fp_alives @ [true]) (Es @ [Y]);
    val ctr_specs =
      [(((Binding.empty, Oper_b), [(Binding.empty, ssig_sig_T)]), NoSyn),
       (((Binding.empty, VLeaf_b), [(Binding.empty, Y)]), NoSyn),
       (((Binding.empty, CLeaf_b), [(Binding.empty, fpT)]), NoSyn)];
    val spec = (((((tyargs, T_b), NoSyn), ctr_specs),
      (Binding.empty, Binding.empty, Binding.empty)), []);

    val plugins = Plugin_Name.make_filter lthy (K (curry (op =) transfer_plugin));
    val discs_sels = false;

    val lthy = lthy
      |> Local_Theory.map_background_naming (mk_internal true lthy Name_Space.concealed) (*TODO check*)
      |> with_typedef_threshold ~1
        (co_datatypes Least_FP construct_lfp ((plugins, discs_sels), [spec]))
      |> Local_Theory.end_nested;

    val SOME fp_sugar = fp_sugar_of lthy T_name;
  in
    (fp_sugar, lthy)
  end;

fun embed_Sig ctxt Sig inl_or_r t =
  Library.foldl1 HOLogic.mk_comp [Sig, inl_or_r, dummify_atomic_types t]
  |> Syntax.check_term ctxt;

fun mk_ctr_wrapper_friends ctxt friend_name friend_T old_sig_T k_T Sig old_buffer =
  let
    val embed_Sig_inl = embed_Sig ctxt Sig (Inl_const old_sig_T k_T);

    val ctr_wrapper = embed_Sig_inl (#ctr_wrapper old_buffer);
    val friends = Symtab.map (K (apsnd embed_Sig_inl)) (#friends old_buffer)
      |> Symtab.update_new (friend_name, (friend_T,
        HOLogic.mk_comp (Sig, Inr_const old_sig_T k_T)));
  in
    (ctr_wrapper, friends)
  end;

fun pre_type_of_ctor Y ctor =
  let
    val (fp_preT, fpT) = dest_funT (fastype_of ctor);
  in
    typ_subst_nonatomic [(fpT, Y)] fp_preT
  end;

fun mk_k_as_ssig Z old_sig_T k_T ssig_T Sig dead_sig_map Oper VLeaf =
  let
    val inr' = Inr_const old_sig_T k_T;
    val dead_sig_map' = substT Z ssig_T dead_sig_map;
  in
    Library.foldl1 HOLogic.mk_comp [Oper, dead_sig_map' $ VLeaf, Sig, inr']
  end;

fun define_embL name fp_b version Y Z fpT old_sig_T old_ssig_T other_summand_T ssig_T Inl_or_r_const
    dead_old_sig_map Sig old_Oper old_VLeaf old_CLeaf Oper VLeaf CLeaf lthy =
  let
    val embL_b = mk_version_fp_binding true lthy version fp_b name;
    val old_ssig_old_sig_T = Tsubst Y old_ssig_T old_sig_T;
    val ssig_old_sig_T = Tsubst Y ssig_T old_sig_T;
    val ssig_other_summand_T = Tsubst Y ssig_T other_summand_T;

    val sigx = Var (("s", 0), old_ssig_old_sig_T);
    val x = Var (("x", 0), Y);
    val j = Var (("j", 0), fpT);
    val embL = Free (Binding.name_of embL_b, old_ssig_T --> ssig_T);
    val dead_old_sig_map' = Term.subst_atomic_types [(Y, old_ssig_T), (Z, ssig_T)] dead_old_sig_map;
    val Sig' = substT Y ssig_T Sig;
    val inl' = Inl_or_r_const ssig_old_sig_T ssig_other_summand_T;

    val Oper_eq = mk_Trueprop_eq (embL $ (old_Oper $ sigx),
        Oper $ (Sig' $ (inl' $ (dead_old_sig_map' $ embL $ sigx))))
      |> Logic.all sigx;
    val VLeaf_eq = mk_Trueprop_eq (embL $ (old_VLeaf $ x), VLeaf $ x)
      |> Logic.all x;
    val CLeaf_eq = mk_Trueprop_eq (embL $ (old_CLeaf $ j), CLeaf $ j)
      |> Logic.all j;
  in
    define_single_primrec embL_b [Oper_eq, VLeaf_eq, CLeaf_eq] lthy
  end;

fun define_Lam_base fp_b version Y Z preT ssig_T dead_pre_map Sig unsig dead_sig_map Oper VLeaf
    lthy =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);

    val snd' = snd_const YpreT;
    val dead_pre_map' = substT Z ssig_T dead_pre_map;
    val Sig' = substT Y ssig_T Sig;
    val unsig' = substT Y ssig_T unsig;
    val dead_sig_map' = Term.subst_atomic_types [(Y, YpreT), (Z, ssig_T)] dead_sig_map;

    val rhs = HOLogic.mk_comp (unsig', dead_sig_map'
      $ Library.foldl1 HOLogic.mk_comp [Oper, Sig', dead_pre_map' $ VLeaf, snd']);
  in
    define_const true fp_b version LamN rhs lthy
  end;

fun define_Lam_step_or_merge fp_b version Y preT unsig left_case right_case lthy =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);

    val unsig' = substT Y YpreT unsig;

    val rhs = HOLogic.mk_comp (mk_case_sum (left_case, right_case), unsig');
  in
    define_const true fp_b version LamN rhs lthy
  end;

fun define_Lam_step fp_b version Y Z preT old_ssig_T ssig_T dead_pre_map unsig rho embL old_Lam
    lthy =
  let
    val dead_pre_map' = Term.subst_atomic_types [(Y, old_ssig_T), (Z, ssig_T)] dead_pre_map;
    val left_case = HOLogic.mk_comp (dead_pre_map' $ embL, old_Lam);
  in
    define_Lam_step_or_merge fp_b version Y preT unsig left_case rho lthy
  end;

fun define_Lam_merge fp_b version Y Z preT old1_ssig_T old2_ssig_T ssig_T dead_pre_map unsig embLL
    embLR old1_Lam old2_Lam lthy =
  let
    val dead_pre_map' = Term.subst_atomic_types [(Y, old1_ssig_T), (Z, ssig_T)] dead_pre_map;
    val dead_pre_map'' = Term.subst_atomic_types [(Y, old2_ssig_T), (Z, ssig_T)] dead_pre_map;
    val left_case = HOLogic.mk_comp (dead_pre_map' $ embLL, old1_Lam);
    val right_case = HOLogic.mk_comp (dead_pre_map'' $ embLR, old2_Lam);
  in
    define_Lam_step_or_merge fp_b version Y preT unsig left_case right_case lthy
  end;

fun define_proto_sctr_step_or_merge fp_b version old_sig_T right_T Sig old_proto_sctr =
  let
    val rhs = Library.foldl1 HOLogic.mk_comp [Sig, Inl_const old_sig_T right_T, old_proto_sctr];
  in
    define_const true fp_b version proto_sctrN rhs
  end;

fun define_flat fp_b version Y Z fpT sig_T ssig_T Oper VLeaf CLeaf dead_sig_map lthy =
  let
    val flat_b = mk_version_fp_binding true lthy version fp_b flatN;
    val ssig_sig_T = Tsubst Y ssig_T sig_T;
    val ssig_ssig_sig_T = Tsubst Y ssig_T ssig_sig_T;
    val ssig_ssig_T = Tsubst Y ssig_T ssig_T;

    val sigx = Var (("s", 0), ssig_ssig_sig_T);
    val x = Var (("x", 0), ssig_T);
    val j = Var (("j", 0), fpT);
    val flat = Free (Binding.name_of flat_b, ssig_ssig_T --> ssig_T);
    val Oper' = substT Y ssig_T Oper;
    val VLeaf' = substT Y ssig_T VLeaf;
    val CLeaf' = substT Y ssig_T CLeaf;
    val dead_sig_map' = Term.subst_atomic_types [(Y, ssig_ssig_T), (Z, ssig_T)] dead_sig_map;

    val Oper_eq = mk_Trueprop_eq (flat $ (Oper' $ sigx), Oper $ (dead_sig_map' $ flat $ sigx))
      |> Logic.all sigx;
    val VLeaf_eq = mk_Trueprop_eq (flat $ (VLeaf' $ x), x)
      |> Logic.all x;
    val CLeaf_eq = mk_Trueprop_eq (flat $ (CLeaf' $ j), CLeaf $ j)
      |> Logic.all j;
  in
    define_single_primrec flat_b [Oper_eq, VLeaf_eq, CLeaf_eq] lthy
  end;

fun define_eval_core fp_b version Y Z preT fpT sig_T ssig_T dtor Oper VLeaf CLeaf dead_pre_map
    dead_sig_map dead_ssig_map flat Lam lthy =
  let
    val eval_core_b = mk_version_fp_binding true lthy version fp_b eval_coreN;
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val Ypre_ssig_T = Tsubst Y YpreT ssig_T;
    val Ypre_ssig_sig_T = Tsubst Y Ypre_ssig_T sig_T;
    val ssig_preT = Tsubst Y ssig_T preT;
    val ssig_YpreT = Tsubst Y ssig_T YpreT;
    val ssig_ssig_T = Tsubst Y ssig_T ssig_T;

    val sigx = Var (("s", 0), Ypre_ssig_sig_T);
    val x = Var (("x", 0), YpreT);
    val j = Var (("j", 0), fpT);
    val eval_core = Free (Binding.name_of eval_core_b, Ypre_ssig_T --> ssig_preT);
    val Oper' = substT Y YpreT Oper;
    val VLeaf' = substT Y YpreT VLeaf;
    val CLeaf' = substT Y YpreT CLeaf;
    val dead_pre_map' = Term.subst_atomic_types [(Y, ssig_ssig_T), (Z, ssig_T)] dead_pre_map;
    val dead_pre_map'' = substT Z ssig_T dead_pre_map;
    val dead_pre_map''' = Term.subst_atomic_types [(Y, fpT), (Z, ssig_T)] dead_pre_map;
    val dead_sig_map' = Term.subst_atomic_types [(Y, Ypre_ssig_T), (Z, ssig_YpreT)] dead_sig_map;
    val dead_ssig_map' = Term.subst_atomic_types [(Y, YpreT), (Z, Y)] dead_ssig_map;
    val Lam' = substT Y ssig_T Lam;
    val fst' = fst_const YpreT;
    val snd' = snd_const YpreT;

    val Oper_eq = mk_Trueprop_eq (eval_core $ (Oper' $ sigx),
        dead_pre_map' $ flat $ (Lam' $ (dead_sig_map' $ (Abs (Name.uu, Ypre_ssig_T,
          HOLogic.mk_prod (dead_ssig_map' $ fst' $ Bound 0, eval_core $ Bound 0))) $ sigx)))
      |> Logic.all sigx;
    val VLeaf_eq = mk_Trueprop_eq (eval_core $ (VLeaf' $ x), dead_pre_map'' $ VLeaf $ (snd' $ x))
      |> Logic.all x;
    val CLeaf_eq = mk_Trueprop_eq (eval_core $ (CLeaf' $ j), dead_pre_map''' $ CLeaf $ (dtor $ j))
      |> Logic.all j;
  in
    define_single_primrec eval_core_b [Oper_eq, VLeaf_eq, CLeaf_eq] lthy
  end;

fun define_eval fp_b version Y Z preT fpT ssig_T dtor dtor_unfold dead_ssig_map eval_core lthy =
  let
    val fp_preT = Tsubst Y fpT preT;
    val fppreT = HOLogic.mk_prodT (fpT, fp_preT);
    val fp_ssig_T = Tsubst Y fpT ssig_T;

    val dtor_unfold' = substT Z fp_ssig_T dtor_unfold;
    val dead_ssig_map' = Term.subst_atomic_types [(Y, fpT), (Z, fppreT)] dead_ssig_map;
    val eval_core' = substT Y fpT eval_core;
    val id' = HOLogic.id_const fpT;

    val rhs = dtor_unfold' $ HOLogic.mk_comp (eval_core', dead_ssig_map' $ mk_convol (id', dtor));
  in
    define_const true fp_b version evalN rhs lthy
  end;

fun define_cutSsig fp_b version Y Z preT ssig_T dead_pre_map VLeaf dead_ssig_map flat eval_core
    lthy =
  let
    val ssig_preT = Tsubst Y ssig_T preT;
    val ssig_ssig_T = Tsubst Y ssig_T ssig_T;
    val ssig_ssig_preT = HOLogic.mk_prodT (ssig_T, ssig_preT);

    val h = Var (("h", 0), Y --> ssig_preT);
    val dead_pre_map' = Term.subst_atomic_types [(Y, ssig_ssig_T), (Z, ssig_T)] dead_pre_map;
    val dead_ssig_map' = substT Z ssig_ssig_preT dead_ssig_map;
    val eval_core' = substT Y ssig_T eval_core;

    val rhs = Library.foldl1 HOLogic.mk_comp [dead_pre_map' $ flat, eval_core',
        dead_ssig_map' $ mk_convol (VLeaf, h)]
      |> Term.lambda h;
  in
    define_const true fp_b version cutSsigN rhs lthy
  end;

fun define_algLam fp_b version Y Z fpT ssig_T Oper VLeaf dead_sig_map eval lthy =
  let
    val fp_ssig_T = Tsubst Y fpT ssig_T;

    val Oper' = substT Y fpT Oper;
    val VLeaf' = substT Y fpT VLeaf;
    val dead_sig_map' = Term.subst_atomic_types [(Y, fpT), (Z, fp_ssig_T)] dead_sig_map;

    val rhs = Library.foldl1 HOLogic.mk_comp [eval, Oper', dead_sig_map' $ VLeaf'];
  in
    define_const true fp_b version algLamN rhs lthy
  end;

fun define_corecU fp_b version Y Z preT ssig_T dtor_unfold VLeaf cutSsig lthy =
  let
    val ssig_preT = Tsubst Y ssig_T preT;

    val h = Var (("h", 0), Y --> ssig_preT);
    val dtor_unfold' = substT Z ssig_T dtor_unfold;

    val rhs = HOLogic.mk_comp (dtor_unfold' $ (cutSsig $ h), VLeaf)
      |> Term.lambda h;
  in
    define_const true fp_b version corecUN rhs lthy
  end;

fun define_corecUU fp_b version Y Z preT ssig_T dead_pre_map dead_ssig_map flat eval_core sctr
    corecU lthy =
  let
    val ssig_preT = Tsubst Y ssig_T preT;
    val ssig_ssig_T = Tsubst Y ssig_T ssig_T
    val ssig_ssig_preT = HOLogic.mk_prodT (ssig_T, ssig_preT);

    val ssig_pre_ssig_T = Tsubst Y ssig_preT ssig_T;

    val h = Var (("h", 0), Y --> ssig_pre_ssig_T);
    val dead_pre_map' = Term.subst_atomic_types [(Y, ssig_ssig_T), (Z, ssig_T)] dead_pre_map;
    val eval_core' = substT Y ssig_T eval_core;
    val dead_ssig_map' =
      Term.subst_atomic_types [(Y, ssig_preT), (Z, ssig_ssig_preT)] dead_ssig_map;
    val id' = HOLogic.id_const ssig_preT;

    val rhs = corecU $ Library.foldl1 HOLogic.mk_comp
        [dead_pre_map' $ flat, eval_core', dead_ssig_map' $ mk_convol (sctr, id'), h]
      |> Term.lambda h;
  in
    define_const true fp_b version corecUUN rhs lthy
  end;

fun derive_sig_transfer maybe_swap ctxt live_AsBs pre_rel sig_rel Rs R const pre_rel_def
    preT_rel_eqs transfer_thm =
  let
    val RRpre_rel = list_comb (pre_rel, Rs) $ R;
    val RRsig_rel = list_comb (sig_rel, Rs) $ R;
    val constB = Term.subst_atomic_types live_AsBs const;

    val goal = uncurry mk_rel_fun (maybe_swap (RRpre_rel, RRsig_rel)) $ const $ constB
      |> HOLogic.mk_Trueprop;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_sig_transfer_tac ctxt pre_rel_def preT_rel_eqs transfer_thm))
    |> Thm.close_derivation \<^here>
  end;

fun derive_transfer_by_transfer_prover ctxt live_AsBs Rs R const const_defs rel_eqs transfers =
  let
    val constB = Term.subst_atomic_types live_AsBs const;
    val goal = mk_parametricity_goal ctxt (Rs @ [R]) const constB;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_transfer_by_transfer_prover_tac ctxt (const_defs @ map (fn thm => thm RS sym) rel_eqs)
        rel_eqs transfers))
    |> Thm.close_derivation \<^here>
  end;

fun derive_dtor_transfer ctxt live_EsFs Y Z pre_rel fp_rel Rs dtor dtor_rel_thm =
  let
    val Type (\<^type_name>\<open>fun\<close>, [fpT, Type (\<^type_name>\<open>fun\<close>, [fpTB, \<^typ>\<open>bool\<close>])]) =
      snd (strip_typeN (length live_EsFs) (fastype_of fp_rel));

    val pre_rel' = Term.subst_atomic_types [(Y, fpT), (Z, fpTB)] pre_rel;
    val Rpre_rel = list_comb (pre_rel', Rs);
    val Rfp_rel = list_comb (fp_rel, Rs);
    val dtorB = Term.subst_atomic_types live_EsFs dtor;

    val goal = HOLogic.mk_Trueprop (mk_rel_fun Rfp_rel (Rpre_rel $ Rfp_rel) $ dtor $ dtorB);
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_dtor_transfer_tac ctxt dtor_rel_thm))
    |> Thm.close_derivation \<^here>
  end;

fun derive_Lam_or_eval_core_transfer ctxt live_AsBs Y Z preT ssig_T Rs R pre_rel sig_or_ssig_rel
    ssig_rel const const_def rel_eqs transfers =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val ZpreTB = typ_subst_atomic live_AsBs YpreT;
    val ssig_TB = typ_subst_atomic live_AsBs ssig_T;

    val pre_rel' = Term.subst_atomic_types [(Y, ssig_T), (Z, ssig_TB)] pre_rel;
    val sig_or_ssig_rel' = Term.subst_atomic_types [(Y, YpreT), (Z, ZpreTB)] sig_or_ssig_rel;
    val Rsig_or_ssig_rel' = list_comb (sig_or_ssig_rel', Rs);
    val RRpre_rel = list_comb (pre_rel, Rs) $ R;
    val RRssig_rel = list_comb (ssig_rel, Rs) $ R;
    val Rpre_rel' = list_comb (pre_rel', Rs);
    val constB = subst_atomic_types live_AsBs const;

    val goal = mk_rel_fun (Rsig_or_ssig_rel' $ mk_rel_prod R RRpre_rel) (Rpre_rel' $ RRssig_rel)
        $ const $ constB
      |> HOLogic.mk_Trueprop;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_transfer_by_transfer_prover_tac ctxt [const_def] rel_eqs transfers))
    |> Thm.close_derivation \<^here>
  end;

fun derive_proto_sctr_transfer_step_or_merge ctxt Y Z R dead_pre_rel dead_sig_rel proto_sctr
    proto_sctr_def fp_k_T_rel_eqs transfers =
  let
    val proto_sctrZ = substT Y Z proto_sctr;
    val goal = mk_rel_fun (dead_pre_rel $ R) (dead_sig_rel $ R) $ proto_sctr $ proto_sctrZ
      |> HOLogic.mk_Trueprop;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_transfer_by_transfer_prover_tac ctxt [proto_sctr_def] fp_k_T_rel_eqs transfers))
    |> Thm.close_derivation \<^here>
  end;

fun derive_sctr_transfer ctxt live_AsBs Y Z ssig_T Rs R pre_rel ssig_rel sctr sctr_def
    fp_k_T_rel_eqs transfers =
  let
    val ssig_TB = typ_subst_atomic live_AsBs ssig_T;

    val pre_rel' = Term.subst_atomic_types [(Y, ssig_T), (Z, ssig_TB)] pre_rel;
    val Rpre_rel' = list_comb (pre_rel', Rs);
    val RRssig_rel = list_comb (ssig_rel, Rs) $ R;
    val sctrB = subst_atomic_types live_AsBs sctr;

    val goal = HOLogic.mk_Trueprop (mk_rel_fun (Rpre_rel' $ RRssig_rel) RRssig_rel $ sctr $ sctrB);
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_transfer_by_transfer_prover_tac ctxt [sctr_def] fp_k_T_rel_eqs transfers))
    |> Thm.close_derivation \<^here>
  end;

fun derive_corecUU_transfer ctxt live_AsBs Y Z Rs R preT ssig_T pre_rel fp_rel ssig_rel corecUU
    cutSsig_def corecU_def corecUU_def fp_k_T_rel_eqs transfers =
  let
    val ssig_preT = Tsubst Y ssig_T preT;
    val ssig_TB = typ_subst_atomic live_AsBs ssig_T;
    val ssig_preTB = typ_subst_atomic live_AsBs ssig_preT;

    val pre_rel' = Term.subst_atomic_types [(Y, ssig_T), (Z, ssig_TB)] pre_rel;
    val ssig_rel' = Term.subst_atomic_types [(Y, ssig_preT), (Z, ssig_preTB)] ssig_rel;
    val Rpre_rel' = list_comb (pre_rel', Rs);
    val Rfp_rel = list_comb (fp_rel, Rs);
    val RRssig_rel = list_comb (ssig_rel, Rs) $ R;
    val Rssig_rel' = list_comb (ssig_rel', Rs);
    val corecUUB = subst_atomic_types live_AsBs corecUU;

    val goal = mk_rel_fun (mk_rel_fun R (Rssig_rel' $ (Rpre_rel' $ RRssig_rel)))
        (mk_rel_fun R Rfp_rel) $ corecUU $ corecUUB
      |> HOLogic.mk_Trueprop;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove (*no sorry*) ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_transfer_by_transfer_prover_tac ctxt [cutSsig_def, corecU_def, corecUU_def] fp_k_T_rel_eqs
        transfers))
    |> Thm.close_derivation \<^here>
  end;

fun mk_natural_goal ctxt simple_T_mapfs fs t u =
  let
    fun build_simple (T, _) =
      (case AList.lookup (op =) simple_T_mapfs T of
        SOME mapf => mapf
      | NONE => the (find_first (fn f => domain_type (fastype_of f) = T) fs));

    val simple_Ts = map fst simple_T_mapfs;

    val t_map = build_map ctxt simple_Ts [] build_simple (apply2 (range_type o fastype_of) (t, u));
    val u_map = build_map ctxt simple_Ts [] build_simple (apply2 (domain_type o fastype_of) (t, u));
  in
    mk_Trueprop_eq (HOLogic.mk_comp (u, u_map), HOLogic.mk_comp (t_map, t))
  end;

fun derive_natural_by_unfolding ctxt live_AsBs preT pre_map fs f const map_thms =
  let
    val ffpre_map = list_comb (pre_map, fs) $ f;
    val constB = subst_atomic_types live_AsBs const;

    val goal = mk_natural_goal ctxt [(preT, ffpre_map)] (fs @ [f]) const constB;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_natural_by_unfolding_tac ctxt map_thms))
    |> Thm.close_derivation \<^here>
  end;

fun derive_natural_from_transfer ctxt live_AsBs simple_T_mapfs fs f const transfer bnfs subst_bnfs =
  let
    val m = length live_AsBs;

    val constB = Term.subst_atomic_types live_AsBs const;
    val goal = mk_natural_goal ctxt simple_T_mapfs (fs @ [f]) const constB;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_natural_from_transfer_tac ctxt m (replicate m true) transfer [] (map rel_Grp_of_bnf bnfs)
        (map rel_Grp_of_bnf subst_bnfs)))
    |> Thm.close_derivation \<^here>
  end;

fun derive_natural_from_transfer_with_pre_type ctxt live_AsBs Y Z preT ssig_T pre_map ssig_map fs
    f =
  let
    val ssig_TB = typ_subst_atomic live_AsBs ssig_T;
    val preT' = Term.typ_subst_atomic [(Y, ssig_T), (Z, ssig_TB)] preT;

    val ffpre_map = list_comb (pre_map, fs) $ f;
    val pre_map' = Term.subst_atomic_types [(Y, ssig_T), (Z, ssig_TB)] pre_map;
    val fpre_map' = list_comb (pre_map', fs);
    val ffssig_map = list_comb (ssig_map, fs) $ f;

    val preT_mapfs = [(preT, ffpre_map), (preT', fpre_map' $ ffssig_map)];
  in
    derive_natural_from_transfer ctxt live_AsBs preT_mapfs fs f
  end;

fun derive_Lam_Inl_Inr ctxt Y Z preT old_sig_T old_ssig_T k_T ssig_T dead_pre_map Sig embL old_Lam
    Lam rho unsig_thm Lam_def =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val Ypre_old_sig_T = Tsubst Y YpreT old_sig_T;
    val Ypre_k_T = Tsubst Y YpreT k_T;

    val inl' = Inl_const Ypre_old_sig_T Ypre_k_T;
    val inr' = Inr_const Ypre_old_sig_T Ypre_k_T;
    val dead_pre_map' = Term.subst_atomic_types [(Y, old_ssig_T), (Z, ssig_T)] dead_pre_map;
    val Sig' = substT Y YpreT Sig;
    val Lam_o_Sig = HOLogic.mk_comp (Lam, Sig');

    val inl_goal = mk_Trueprop_eq (HOLogic.mk_comp (Lam_o_Sig, inl'),
      HOLogic.mk_comp (dead_pre_map' $ embL, old_Lam));
    val inr_goal = mk_Trueprop_eq (HOLogic.mk_comp (Lam_o_Sig, inr'), rho);
    val goals = [inl_goal, inr_goal];
    val goal = Logic.mk_conjunction_balanced goals;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal
      (fn {context = ctxt, prems = _} => mk_Lam_Inl_Inr_tac ctxt unsig_thm Lam_def))
    |> Conjunction.elim_balanced (length goals)
    |> map (Thm.close_derivation \<^here>)
  end;

fun derive_flat_VLeaf ctxt Y Z ssig_T x VLeaf dead_ssig_map flat ssig_induct fp_map_id sig_map_cong
    sig_map_ident sig_map_comp ssig_map_thms flat_simps =
  let
    val x' = substT Y ssig_T x;
    val dead_ssig_map' = substT Z ssig_T dead_ssig_map;

    val goal = mk_Trueprop_eq (flat $ (dead_ssig_map' $ VLeaf $ x'), x');

    val ssig_induct' = infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt x')] ssig_induct;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_flat_VLeaf_or_flat_tac ctxt ssig_induct' sig_map_cong
        (fp_map_id :: sig_map_ident :: sig_map_comp :: ssig_map_thms @ flat_simps @
         @{thms o_apply id_apply id_def[symmetric]})))
    |> Thm.close_derivation \<^here>
  end;

fun derive_flat_flat ctxt Y Z ssig_T x dead_ssig_map flat ssig_induct fp_map_id sig_map_cong
    sig_map_comp ssig_map_thms flat_simps =
  let
    val ssig_ssig_T = Tsubst Y ssig_T ssig_T;
    val ssig_ssig_ssig_T = Tsubst Y ssig_T ssig_ssig_T;

    val x' = substT Y ssig_ssig_ssig_T x;
    val dead_ssig_map' = Term.subst_atomic_types [(Y, ssig_ssig_T), (Z, ssig_T)] dead_ssig_map;
    val flat' = substT Y ssig_T flat;

    val goal = mk_Trueprop_eq (flat $ (dead_ssig_map' $ flat $ x'), flat $ (flat' $ x'));

    val ssig_induct' = infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt x')] ssig_induct;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_flat_VLeaf_or_flat_tac ctxt ssig_induct' sig_map_cong
        (o_apply :: fp_map_id :: sig_map_comp :: ssig_map_thms @ flat_simps)))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_core_flat ctxt Y Z preT ssig_T dead_pre_map dead_ssig_map flat eval_core x
    ssig_induct dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp fp_map_id sig_map_comp
    sig_map_cong ssig_map_thms ssig_map_comp flat_simps flat_pointful_natural flat_flat
    Lam_pointful_natural eval_core_simps =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val ssig_ssig_T = Tsubst Y ssig_T ssig_T;
    val Ypre_ssig_T = Tsubst Y YpreT ssig_T;
    val Ypre_ssig_ssig_T = Tsubst Y YpreT ssig_ssig_T;
    val ssig_YpreT = Tsubst Y ssig_T YpreT;

    val dead_pre_map' = Term.subst_atomic_types [(Y, ssig_ssig_T), (Z, ssig_T)] dead_pre_map;
    val dead_ssig_map' = Term.subst_atomic_types [(Y, Ypre_ssig_T), (Z, ssig_YpreT)] dead_ssig_map;
    val dead_ssig_map'' = Term.subst_atomic_types [(Y, YpreT), (Z, Y)] dead_ssig_map;
    val flat' = substT Y YpreT flat;
    val eval_core' = substT Y ssig_T eval_core;
    val x' = substT Y Ypre_ssig_ssig_T x;
    val fst' = fst_const YpreT;

    val goal = mk_Trueprop_eq (eval_core $ (flat' $ x'), dead_pre_map' $ flat
      $ (eval_core' $ (dead_ssig_map' $ mk_convol (dead_ssig_map'' $ fst', eval_core) $ x')));

    val ssig_induct' = infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt x')] ssig_induct;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_core_flat_tac ctxt ssig_induct' dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp
        fp_map_id sig_map_comp sig_map_cong ssig_map_thms ssig_map_comp flat_simps
        flat_pointful_natural flat_flat Lam_pointful_natural eval_core_simps))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_thm ctxt dtor_inject dtor_unfold_thm eval_def =
  (trans OF [iffD2 OF [dtor_inject, HOLogic.mk_obj_eq eval_def RS fun_cong], dtor_unfold_thm])
  |> unfold_thms ctxt [o_apply, eval_def RS symmetric_thm];

fun derive_eval_flat ctxt Y Z fpT ssig_T dead_ssig_map flat eval x dead_pre_map_comp0
    dtor_unfold_unique ssig_map_id ssig_map_comp flat_pointful_natural eval_core_pointful_natural
    eval_core_flat eval_thm =
  let
    val fp_ssig_T = Tsubst Y fpT ssig_T;
    val fp_ssig_ssig_T = Tsubst Y fp_ssig_T ssig_T;

    val dead_ssig_map' = Term.subst_atomic_types [(Y, fp_ssig_T), (Z, fpT)] dead_ssig_map;
    val flat' = substT Y fpT flat;
    val x' = substT Y fp_ssig_ssig_T x;

    val goal = mk_Trueprop_eq (eval $ (flat' $ x'), eval $ (dead_ssig_map' $ eval $ x'));

    val cond_eval_o_flat =
      infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt (HOLogic.mk_comp (eval, flat')))]
        (trans OF [dtor_unfold_unique, dtor_unfold_unique RS sym] RS fun_cong)
      OF [ext, ext];
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_flat_tac ctxt dead_pre_map_comp0 ssig_map_id ssig_map_comp flat_pointful_natural
        eval_core_pointful_natural eval_core_flat eval_thm cond_eval_o_flat))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_Oper ctxt live Y Z fpT sig_T ssig_T dead_sig_map Oper eval algLam x sig_map_ident
    sig_map_comp0 sig_map_comp Oper_natural_pointful VLeaf_natural flat_simps eval_flat algLam_def =
  let
    val fp_ssig_T = Tsubst Y fpT ssig_T;
    val fp_ssig_sig_T = Tsubst Y fp_ssig_T sig_T;

    val dead_sig_map' = Term.subst_atomic_types [(Y, fp_ssig_T), (Z, fpT)] dead_sig_map;
    val Oper' = substT Y fpT Oper;
    val x' = substT Y fp_ssig_sig_T x;

    val goal = mk_Trueprop_eq (eval $ (Oper' $ x'), algLam $ (dead_sig_map' $ eval $ x'));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_Oper_tac ctxt live sig_map_ident sig_map_comp0 sig_map_comp Oper_natural_pointful
        VLeaf_natural flat_simps eval_flat algLam_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_V_or_CLeaf ctxt Y fpT V_or_CLeaf eval x dead_pre_map_id dead_pre_map_comp fp_map_id
    dtor_unfold_unique V_or_CLeaf_map_thm eval_core_simps eval_thm =
  let
    val V_or_CLeaf' = substT Y fpT V_or_CLeaf;
    val x' = substT Y fpT x;

    val goal = mk_Trueprop_eq (eval $ (V_or_CLeaf' $ x'), x');
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_V_or_CLeaf_tac ctxt dead_pre_map_id dead_pre_map_comp fp_map_id dtor_unfold_unique
        V_or_CLeaf_map_thm eval_core_simps eval_thm))
    |> Thm.close_derivation \<^here>
  end;

fun derive_extdd_mor ctxt Y Z preT fpT ssig_T dead_pre_map dtor extdd cutSsig f g dead_pre_map_comp0
    dead_pre_map_comp VLeaf_map_thm ssig_map_comp flat_pointful_natural eval_core_pointful_natural
    eval_thm eval_flat eval_VLeaf cutSsig_def =
  let
    val ssig_preT = Tsubst Y ssig_T preT;

    val dead_pre_map' = Term.subst_atomic_types [(Y, ssig_T), (Z, fpT)] dead_pre_map;
    val f' = substT Z fpT f;
    val g' = substT Z ssig_preT g;
    val extdd_f = extdd $ f';

    val prem = mk_Trueprop_eq (HOLogic.mk_comp (dead_pre_map' $ extdd_f, g'),
      HOLogic.mk_comp (dtor, f'));
    val goal = mk_Trueprop_eq (HOLogic.mk_comp (dead_pre_map' $ extdd_f, cutSsig $ g'),
      HOLogic.mk_comp (dtor, extdd_f));
  in
    fold (Variable.add_free_names ctxt) [prem, goal] []
    |> (fn vars => Goal.prove_sorry ctxt vars [prem] goal (fn {context = ctxt, prems = [prem]} =>
      mk_extdd_mor_tac ctxt dead_pre_map_comp0 dead_pre_map_comp VLeaf_map_thm ssig_map_comp
        flat_pointful_natural eval_core_pointful_natural eval_thm eval_flat eval_VLeaf cutSsig_def
        prem))
    |> Thm.close_derivation \<^here>
  end;

fun derive_mor_cutSsig_flat ctxt Y Z preT fpT ssig_T dead_pre_map dead_ssig_map dtor flat eval_core
    eval cutSsig f g dead_pre_map_comp0 dead_pre_map_comp dead_pre_map_cong dtor_unfold_unique
    dead_ssig_map_comp0 ssig_map_comp flat_simps flat_pointful_natural eval_core_pointful_natural
    flat_flat flat_VLeaf eval_core_flat cutSsig_def cutSsig_def_pointful_natural eval_thm =
  let
    val ssig_preT = Tsubst Y ssig_T preT;

    val substYZ = Term.subst_atomic_types [(Y, ssig_T), (Z, fpT)];

    val dead_pre_map' = substYZ dead_pre_map;
    val dead_ssig_map' = substYZ dead_ssig_map;
    val f' = substYZ f;
    val g' = substT Z ssig_preT g;
    val cutSsig_g = cutSsig $ g';

    val id' = HOLogic.id_const ssig_T;
    val convol' = mk_convol (id', cutSsig_g);
    val dead_ssig_map'' =
      Term.subst_atomic_types [(Y, ssig_T), (Z, range_type (fastype_of convol'))] dead_ssig_map;
    val eval_core' = substT Y ssig_T eval_core;
    val eval_core_o_map = HOLogic.mk_comp (eval_core', dead_ssig_map'' $ convol');

    val prem = mk_Trueprop_eq (HOLogic.mk_comp (dead_pre_map' $ f', cutSsig_g),
      HOLogic.mk_comp (dtor, f'));
    val goal = mk_Trueprop_eq (HOLogic.mk_comp (eval, dead_ssig_map' $ f'),
      HOLogic.mk_comp (f', flat));
  in
    fold (Variable.add_free_names ctxt) [prem, goal] []
    |> (fn vars => Goal.prove_sorry ctxt vars [prem] goal (fn {context = ctxt, prems = [prem]} =>
      mk_mor_cutSsig_flat_tac ctxt eval_core_o_map dead_pre_map_comp0 dead_pre_map_comp
        dead_pre_map_cong dtor_unfold_unique dead_ssig_map_comp0 ssig_map_comp flat_simps
        flat_pointful_natural eval_core_pointful_natural flat_flat flat_VLeaf eval_core_flat
        cutSsig_def cutSsig_def_pointful_natural eval_thm prem))
    |> Thm.close_derivation \<^here>
  end;

fun derive_extdd_o_VLeaf ctxt Y Z preT fpT ssig_T dead_pre_map dtor VLeaf extdd f g
    dead_pre_map_comp0 dead_pre_map_comp dtor_inject ssig_map_thms eval_core_simps eval_thm
    eval_VLeaf =
  let
    val ssig_preT = Tsubst Y ssig_T preT;

    val substYZ = Term.subst_atomic_types [(Y, ssig_T), (Z, fpT)];

    val dead_pre_map' = substYZ dead_pre_map;
    val f' = substT Z fpT f;
    val g' = substT Z ssig_preT g;
    val extdd_f = extdd $ f';

    val prem = mk_Trueprop_eq (HOLogic.mk_comp (dead_pre_map' $ extdd_f, g'),
      HOLogic.mk_comp (dtor, f'));
    val goal = mk_Trueprop_eq (HOLogic.mk_comp (extdd_f, VLeaf), f');
  in
    fold (Variable.add_free_names ctxt) [prem, goal] []
    |> (fn vars => Goal.prove_sorry ctxt vars [prem] goal (fn {context = ctxt, prems = [prem]} =>
      mk_extdd_o_VLeaf_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_inject ssig_map_thms
        eval_core_simps eval_thm eval_VLeaf prem))
    |> Thm.close_derivation \<^here>
  end;

fun derive_corecU_pointfree ctxt Y Z preT fpT ssig_T dead_pre_map dtor extdd corecU g
    dead_pre_map_comp dtor_unfold_thm ssig_map_thms dead_ssig_map_comp0 flat_simps flat_VLeaf
    eval_core_simps cutSsig_def mor_cutSsig_flat corecU_def =
  let
    val ssig_preT = Tsubst Y ssig_T preT;

    val substYZ = Term.subst_atomic_types [(Y, ssig_T), (Z, fpT)];

    val dead_pre_map' = substYZ dead_pre_map;
    val g' = substT Z ssig_preT g;
    val corecU_g = corecU $ g';

    val goal = mk_Trueprop_eq (HOLogic.mk_comp (dead_pre_map' $ (extdd $ corecU_g), g'),
      HOLogic.mk_comp (dtor, corecU_g));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_corecU_pointfree_tac ctxt dead_pre_map_comp dtor_unfold_thm ssig_map_thms
      dead_ssig_map_comp0 flat_simps flat_VLeaf eval_core_simps cutSsig_def mor_cutSsig_flat
      corecU_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_corecU_ctor_unique ctxt Y Z preT fpT ssig_T dead_pre_map ctor dtor VLeaf extdd corecU f g
    dead_pre_map_comp ctor_dtor dtor_unfold_thm dtor_unfold_unique ssig_map_thms dead_ssig_map_comp0
    flat_simps flat_VLeaf eval_core_simps extdd_mor extdd_o_VLeaf cutSsig_def mor_cutSsig_flat
    corecU_def =
  let
    val corecU_pointfree = derive_corecU_pointfree ctxt Y Z preT fpT ssig_T dead_pre_map dtor extdd
      corecU g dead_pre_map_comp dtor_unfold_thm ssig_map_thms dead_ssig_map_comp0 flat_simps
      flat_VLeaf eval_core_simps cutSsig_def mor_cutSsig_flat corecU_def;

    val corecU_thm = corecU_pointfree RS @{thm comp_eq_dest};

    val corecU_ctor =
      let
        val arg_cong' =
          infer_instantiate' ctxt [NONE, NONE, SOME (Thm.cterm_of ctxt ctor)] arg_cong;
      in
        unfold_thms ctxt [ctor_dtor] (corecU_thm RS arg_cong')
      end;

    val corecU_unique =
      let
        val substYZ = Term.subst_atomic_types [(Y, ssig_T), (Z, fpT)];

        val f' = substYZ f;
        val abs_f_o_VLeaf = Term.lambda f' (HOLogic.mk_comp (f', VLeaf));

        val inject_refine' = infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt abs_f_o_VLeaf),
          SOME (Thm.cterm_of ctxt extdd)] @{thm inject_refine};
      in
        unfold_thms ctxt @{thms atomize_imp}
          (((inject_refine' OF [extdd_o_VLeaf, extdd_o_VLeaf] RS iffD1)
            OF [asm_rl, corecU_pointfree])
           OF [asm_rl, trans OF [dtor_unfold_unique, dtor_unfold_unique RS sym]
             OF [extdd_mor, corecU_pointfree RS extdd_mor]])
        RS @{thm obj_distinct_prems}
      end;
  in
    (corecU_ctor, corecU_unique)
  end;

fun derive_dtor_algLam ctxt Y Z preT fpT sig_T ssig_T dead_pre_map dtor dead_sig_map Lam eval algLam
    x pre_map_comp dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp sig_map_comp
    Oper_pointful_natural ssig_map_thms dead_ssig_map_comp0 Lam_pointful_natural eval_core_simps
    eval_thm eval_flat eval_VLeaf algLam_def =
  let
    val fp_preT = Tsubst Y fpT preT;
    val fppreT = HOLogic.mk_prodT (fpT, fp_preT);
    val fp_sig_T = Tsubst Y fpT sig_T;
    val fp_ssig_T = Tsubst Y fpT ssig_T;

    val id' = HOLogic.id_const fpT;
    val convol' = mk_convol (id', dtor);
    val dead_pre_map' = Term.subst_atomic_types [(Y, fp_ssig_T), (Z, fpT)] dead_pre_map;
    val dead_sig_map' = Term.subst_atomic_types [(Y, fpT), (Z, fppreT)] dead_sig_map;
    val Lam' = substT Y fpT Lam;
    val x' = substT Y fp_sig_T x;

    val goal = mk_Trueprop_eq (dtor $ (algLam $ x'),
      dead_pre_map' $ eval $ (Lam' $ (dead_sig_map' $ convol' $ x')));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_dtor_algLam_tac ctxt pre_map_comp dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp
        sig_map_comp Oper_pointful_natural ssig_map_thms dead_ssig_map_comp0 Lam_pointful_natural
        eval_core_simps eval_thm eval_flat eval_VLeaf algLam_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_algLam_base ctxt Y Z preT fpT dead_pre_map ctor dtor algLam proto_sctr dead_pre_map_id
    dead_pre_map_comp ctor_dtor dtor_ctor dtor_unfold_unique unsig_thm Sig_pointful_natural
    ssig_map_thms Lam_def flat_simps eval_core_simps eval_thm algLam_def =
  let
    val fp_preT = Tsubst Y fpT preT;

    val proto_sctr' = substT Y fpT proto_sctr;

    val dead_pre_map' = Term.subst_atomic_types [(Y, fpT), (Z, fp_preT)] dead_pre_map;
    val dead_pre_map_dtor = dead_pre_map' $ dtor;

    val goal = mk_Trueprop_eq (HOLogic.mk_comp (algLam, proto_sctr'), ctor);
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_algLam_base_tac ctxt dead_pre_map_dtor dead_pre_map_id dead_pre_map_comp ctor_dtor
        dtor_ctor dtor_unfold_unique unsig_thm Sig_pointful_natural ssig_map_thms Lam_def flat_simps
        eval_core_simps eval_thm algLam_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_flat_embL ctxt Y Z old_ssig_T ssig_T dead_old_ssig_map embL old_flat flat x
    old_ssig_induct fp_map_id Sig_pointful_natural old_sig_map_comp old_sig_map_cong
    old_ssig_map_thms old_flat_simps flat_simps embL_simps =
  let
    val old_ssig_old_ssig_T = Tsubst Y old_ssig_T old_ssig_T;

    val dead_old_ssig_map' =
      Term.subst_atomic_types [(Y, old_ssig_T), (Z, ssig_T)] dead_old_ssig_map;
    val embL' = substT Y ssig_T embL;
    val x' = substT Y old_ssig_old_ssig_T x;

    val goal = mk_Trueprop_eq (flat $ (embL' $ (dead_old_ssig_map' $ embL $ x')),
      embL $ (old_flat $ x'));

    val old_ssig_induct' =
      infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt x')] old_ssig_induct;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_flat_embL_tac ctxt old_ssig_induct' fp_map_id Sig_pointful_natural old_sig_map_comp
        old_sig_map_cong old_ssig_map_thms old_flat_simps flat_simps embL_simps))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_core_embL ctxt Y Z preT old_ssig_T ssig_T dead_pre_map embL old_eval_core eval_core
    x old_ssig_induct dead_pre_map_comp0 dead_pre_map_comp Sig_pointful_natural unsig_thm
    old_sig_map_comp old_sig_map_cong old_Lam_pointful_natural Lam_def flat_embL embL_simps
    embL_pointful_natural old_eval_core_simps eval_core_simps =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val Ypre_old_ssig_T = Tsubst Y YpreT old_ssig_T;

    val dead_pre_map' = Term.subst_atomic_types [(Y, old_ssig_T), (Z, ssig_T)] dead_pre_map;
    val embL' = substT Y YpreT embL;
    val x' = substT Y Ypre_old_ssig_T x;

    val goal =
      mk_Trueprop_eq (eval_core $ (embL' $ x'), dead_pre_map' $ embL $ (old_eval_core $ x'));

    val old_ssig_induct' =
      infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt x')] old_ssig_induct;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_core_embL_tac ctxt old_ssig_induct' dead_pre_map_comp0 dead_pre_map_comp
        Sig_pointful_natural unsig_thm old_sig_map_comp old_sig_map_cong old_Lam_pointful_natural
        Lam_def flat_embL old_eval_core_simps eval_core_simps embL_simps embL_pointful_natural))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_embL ctxt Y fpT embL old_eval eval dead_pre_map_comp0 dtor_unfold_unique
    embL_pointful_natural eval_core_embL old_eval_thm eval_thm =
  let
    val embL' = substT Y fpT embL;
    val goal = mk_Trueprop_eq (HOLogic.mk_comp (eval, embL'), old_eval);
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_embL_tac ctxt dead_pre_map_comp0 dtor_unfold_unique embL_pointful_natural
        eval_core_embL old_eval_thm eval_thm))
    |> Thm.close_derivation \<^here>
  end;

fun derive_algLam_algLam ctxt Inx_const Y fpT Sig old_algLam algLam dead_pre_map_comp dtor_inject
    unsig_thm sig_map_thm Lam_def eval_embL old_dtor_algLam dtor_algLam =
  let
    val Sig' = substT Y fpT Sig;
    val (left_T, right_T) = dest_sumT (domain_type (fastype_of Sig'));
    val inx' = Inx_const left_T right_T;

    val goal = mk_Trueprop_eq (Library.foldl1 HOLogic.mk_comp [algLam, Sig', inx'], old_algLam);
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_algLam_algLam_tac ctxt dead_pre_map_comp dtor_inject unsig_thm sig_map_thm Lam_def
        eval_embL old_dtor_algLam dtor_algLam))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_core_k_as_ssig ctxt Y preT k_T rho eval_core k_as_ssig x pre_map_comp
    dead_pre_map_id sig_map_comp ssig_map_thms Lam_natural_pointful Lam_Inr flat_VLeaf
    eval_core_simps =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val Ypre_k_T = Tsubst Y YpreT k_T;

    val k_as_ssig' = substT Y YpreT k_as_ssig;
    val x' = substT Y Ypre_k_T x;

    val goal = mk_Trueprop_eq (eval_core $ (k_as_ssig' $ x'), rho $ x');
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_core_k_as_ssig_tac ctxt pre_map_comp dead_pre_map_id sig_map_comp ssig_map_thms
        Lam_natural_pointful Lam_Inr flat_VLeaf eval_core_simps))
    |> Thm.close_derivation \<^here>
  end;

fun derive_algLam_algrho ctxt Y fpT Sig algLam algrho algLam_def algrho_def =
  let
    val Sig' = substT Y fpT Sig;
    val (left_T, right_T) = dest_sumT (domain_type (fastype_of Sig'));
    val inr' = Inr_const left_T right_T;

    val goal = mk_Trueprop_eq (Library.foldl1 HOLogic.mk_comp [algLam, Sig', inr'], algrho);
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_algLam_algrho_tac ctxt algLam_def algrho_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_dtor_algrho ctxt Y Z preT fpT k_T ssig_T dead_pre_map dead_k_map dtor rho eval algrho x
    eval_thm k_as_ssig_natural_pointful eval_core_k_as_ssig algrho_def =
  let
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val fppreT = Tsubst Y fpT YpreT;
    val fp_k_T = Tsubst Y fpT k_T;
    val fp_ssig_T = Tsubst Y fpT ssig_T;

    val id' = HOLogic.id_const fpT;
    val convol' = mk_convol (id', dtor);
    val dead_pre_map' = Term.subst_atomic_types [(Y, fp_ssig_T), (Z, fpT)] dead_pre_map;
    val dead_k_map' = Term.subst_atomic_types [(Y, fpT), (Z, fppreT)] dead_k_map;
    val rho' = substT Y fpT rho;
    val x' = substT Y fp_k_T x;

    val goal = mk_Trueprop_eq (dtor $ (algrho $ x'),
      dead_pre_map' $ eval $ (rho' $ (dead_k_map' $ convol' $ x')));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_dtor_algrho_tac ctxt eval_thm k_as_ssig_natural_pointful eval_core_k_as_ssig algrho_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_algLam_step_or_merge ctxt Y fpT ctor proto_sctr algLam proto_sctr_def old_algLam_pointful
    algLam_algLam =
  let
    val proto_sctr' = substT Y fpT proto_sctr;
    val goal = mk_Trueprop_eq (HOLogic.mk_comp (algLam, proto_sctr'), ctor);

    val algLam_algLam_pointful = mk_pointful ctxt algLam_algLam;
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_algLam_step_tac ctxt proto_sctr_def old_algLam_pointful algLam_algLam_pointful))
    |> Thm.close_derivation \<^here>
  end;

fun derive_eval_sctr ctxt Y Z fpT ssig_T dead_pre_map ctor eval sctr proto_sctr_pointful_natural
    eval_Oper algLam_thm sctr_def =
  let
    val fp_ssig_T = Tsubst Y fpT ssig_T;

    val dead_pre_map' = Term.subst_atomic_types [(Y, fp_ssig_T), (Z, fpT)] dead_pre_map;
    val sctr' = substT Y fpT sctr;

    val goal = mk_Trueprop_eq (HOLogic.mk_comp (eval, sctr'),
      HOLogic.mk_comp (ctor, dead_pre_map' $ eval));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_eval_sctr_tac ctxt proto_sctr_pointful_natural eval_Oper algLam_thm sctr_def))
    |> Thm.close_derivation \<^here>
  end;

fun derive_corecUU_pointfree_unique ctxt Y Z preT fpT ssig_T dead_pre_map ctor dead_ssig_map eval
    corecUU f g dead_pre_map_comp0 dead_pre_map_comp dtor_ctor dtor_inject ssig_map_comp
    flat_pointful_natural eval_core_pointful_natural eval_thm eval_flat corecU_ctor corecU_unique
    sctr_pointful_natural eval_sctr_pointful corecUU_def =
  let
    val ssig_preT = Tsubst Y ssig_T preT;
    val ssig_pre_ssig_T = Tsubst Y ssig_preT ssig_T;
    val fp_ssig_T = Tsubst Y fpT ssig_T;

    val dead_pre_map' = Term.subst_atomic_types [(Y, fp_ssig_T), (Z, fpT)] dead_pre_map;
    val dead_pre_map'' = Term.subst_atomic_types [(Y, ssig_T), (Z, fp_ssig_T)] dead_pre_map;
    val dead_ssig_map' = Term.subst_atomic_types [(Y, ssig_preT), (Z, fpT)] dead_ssig_map;
    val dead_ssig_map'' = substT Z fpT dead_ssig_map;
    val f' = substT Z ssig_pre_ssig_T f;
    val g' = substT Z fpT g;
    val corecUU_f = corecUU $ f';

    fun mk_eq fpf =
      mk_Trueprop_eq (fpf, Library.foldl1 HOLogic.mk_comp [eval, dead_ssig_map' $
          Library.foldl1 HOLogic.mk_comp [ctor, dead_pre_map' $ eval, dead_pre_map''
            $ (dead_ssig_map'' $ fpf)],
        f']);

    val corecUU_pointfree =
      let
        val goal = mk_eq corecUU_f;
      in
        Variable.add_free_names ctxt goal []
        |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
          mk_corecUU_pointfree_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor dtor_inject
            ssig_map_comp flat_pointful_natural eval_core_pointful_natural eval_thm eval_flat
            corecU_ctor sctr_pointful_natural eval_sctr_pointful corecUU_def))
        |> Thm.close_derivation \<^here>
      end;

    val corecUU_unique =
      let
        val prem = mk_eq g';
        val goal = mk_Trueprop_eq (g', corecUU_f);
      in
        fold (Variable.add_free_names ctxt) [prem, goal] []
        |> (fn vars => Goal.prove_sorry ctxt vars [prem] goal
              (fn {context = ctxt, prems = [prem]} =>
                mk_corecUU_unique_tac ctxt dead_pre_map_comp0 dead_pre_map_comp dtor_ctor
                  ssig_map_comp flat_pointful_natural eval_core_pointful_natural eval_thm eval_flat
                  corecU_unique sctr_pointful_natural eval_sctr_pointful corecUU_def prem))
        |> Thm.close_derivation \<^here>
      end;
  in
    (corecUU_pointfree, corecUU_unique)
  end;

fun define_flat_etc fp_b version live_AsBs Y Z preT fpT sig_T ssig_T Oper VLeaf CLeaf pre_rel
    dead_pre_map dtor dtor_unfold dead_sig_map ssig_rel dead_ssig_map Lam Rs R pre_map_transfer
    fp_k_T_rel_eqs sig_map_transfer ssig_map_transfer Lam_transfer dtor_transfer lthy =
  let
    val (flat_data as (flat, flat_def, _), lthy) = lthy
      |> define_flat fp_b version Y Z fpT sig_T ssig_T Oper VLeaf CLeaf dead_sig_map;

    val (eval_core_data as (eval_core, eval_core_def, _), lthy) = lthy
      |> define_eval_core fp_b version Y Z preT fpT sig_T ssig_T dtor Oper VLeaf CLeaf dead_pre_map
        dead_sig_map dead_ssig_map flat Lam;

    val ((eval_data as (eval, _), cutSsig_data as (cutSsig, _)), lthy) = lthy
      |> define_eval fp_b version Y Z preT fpT ssig_T dtor dtor_unfold dead_ssig_map eval_core
      ||>> define_cutSsig fp_b version Y Z preT ssig_T dead_pre_map VLeaf dead_ssig_map flat
        eval_core;

    val ((algLam_data, unfold_data), lthy) = lthy
      |> define_algLam fp_b version Y Z fpT ssig_T Oper VLeaf dead_sig_map eval
      ||>> define_corecU fp_b version Y Z preT ssig_T dtor_unfold VLeaf cutSsig;

    val flat_transfer = derive_transfer_by_transfer_prover lthy live_AsBs Rs R flat [flat_def] []
      [sig_map_transfer];
    val eval_core_transfer = derive_Lam_or_eval_core_transfer lthy live_AsBs Y Z preT ssig_T Rs R
      pre_rel ssig_rel ssig_rel eval_core eval_core_def fp_k_T_rel_eqs
      [pre_map_transfer, sig_map_transfer, ssig_map_transfer, flat_transfer, Lam_transfer,
       dtor_transfer];
  in
    (((((((flat_data, flat_transfer), (eval_core_data, eval_core_transfer)), eval_data),
      cutSsig_data), algLam_data), unfold_data), lthy)
  end;

fun derive_Sig_natural_etc ctxt live live_AsBs Y Z preT fpT k_or_fpT sig_T ssig_T pre_map
    dead_pre_map ctor dtor Sig dead_sig_map Oper VLeaf CLeaf ssig_map dead_ssig_map Lam flat
    eval_core eval cutSsig algLam corecU x fs f g ctor_dtor dtor_inject dtor_unfold_thm
    dtor_unfold_unique sig_map_thm ssig_induct ssig_map_thms Oper_map_thm VLeaf_map_thm
    CLeaf_map_thm Lam_transfer flat_simps flat_transfer eval_core_simps eval_core_transfer eval_def
    cutSsig_def algLam_def corecU_def live_pre_bnf pre_bnf dead_pre_bnf fp_bnf sig_bnf ssig_bnf
    dead_ssig_bnf =
  let
    val SOME prod_bnf = bnf_of ctxt \<^type_name>\<open>prod\<close>;

    val f' = substT Z fpT f;
    val dead_ssig_map' = substT Z fpT dead_ssig_map;
    val extdd = Term.lambda f' (HOLogic.mk_comp (eval, dead_ssig_map' $ f'));

    val live_pre_map_def = map_def_of_bnf live_pre_bnf;
    val pre_map_comp = map_comp_of_bnf pre_bnf;
    val dead_pre_map_id = map_id_of_bnf dead_pre_bnf;
    val dead_pre_map_comp0 = map_comp0_of_bnf dead_pre_bnf;
    val dead_pre_map_comp = map_comp_of_bnf dead_pre_bnf;
    val dead_pre_map_cong = map_cong_of_bnf dead_pre_bnf;
    val fp_map_id = map_id_of_bnf fp_bnf;
    val sig_map_ident = map_ident_of_bnf sig_bnf;
    val sig_map_comp0 = map_comp0_of_bnf sig_bnf;
    val sig_map_comp = map_comp_of_bnf sig_bnf;
    val sig_map_cong = map_cong_of_bnf sig_bnf;
    val ssig_map_id = map_id_of_bnf ssig_bnf;
    val ssig_map_comp = map_comp_of_bnf ssig_bnf;
    val dead_ssig_map_comp0 = map_comp0_of_bnf dead_ssig_bnf;

    val k_preT_map_id0s =
      map map_id0_of_bnf (map_filter (bnf_of ctxt) (fold add_type_namesT [preT, k_or_fpT] []));

    val Sig_natural = derive_natural_by_unfolding ctxt live_AsBs preT pre_map fs f Sig
      ([sig_map_thm, live_pre_map_def, @{thm BNF_Composition.id_bnf_def}] @ k_preT_map_id0s);
    val Oper_natural =
      derive_natural_by_unfolding ctxt live_AsBs preT pre_map fs f Oper [Oper_map_thm];
    val VLeaf_natural =
      derive_natural_by_unfolding ctxt live_AsBs preT pre_map fs f VLeaf [VLeaf_map_thm];
    val Lam_natural = derive_natural_from_transfer_with_pre_type ctxt live_AsBs Y Z preT ssig_T
      pre_map ssig_map fs f Lam Lam_transfer [prod_bnf, pre_bnf, sig_bnf, ssig_bnf] [];
    val flat_natural = derive_natural_from_transfer ctxt live_AsBs [] fs f flat flat_transfer
      [ssig_bnf] [];
    val eval_core_natural = derive_natural_from_transfer_with_pre_type ctxt live_AsBs Y Z preT
      ssig_T pre_map ssig_map fs f eval_core eval_core_transfer [prod_bnf, pre_bnf, ssig_bnf] [];

    val Sig_pointful_natural = mk_pointful ctxt Sig_natural RS sym;
    val Oper_natural_pointful = mk_pointful ctxt Oper_natural;
    val Oper_pointful_natural = Oper_natural_pointful RS sym;
    val flat_pointful_natural = mk_pointful ctxt flat_natural RS sym;
    val Lam_natural_pointful = mk_pointful ctxt Lam_natural;
    val Lam_pointful_natural = Lam_natural_pointful RS sym;
    val eval_core_pointful_natural = mk_pointful ctxt eval_core_natural RS sym;
    val cutSsig_def_pointful_natural = mk_pointful ctxt (HOLogic.mk_obj_eq cutSsig_def) RS sym;

    val flat_VLeaf = derive_flat_VLeaf ctxt Y Z ssig_T x VLeaf dead_ssig_map flat ssig_induct
      fp_map_id sig_map_cong sig_map_ident sig_map_comp ssig_map_thms flat_simps;
    val flat_flat = derive_flat_flat ctxt Y Z ssig_T x dead_ssig_map flat ssig_induct fp_map_id
      sig_map_cong sig_map_comp ssig_map_thms flat_simps;

    val eval_core_flat = derive_eval_core_flat ctxt Y Z preT ssig_T dead_pre_map dead_ssig_map flat
      eval_core x ssig_induct dead_pre_map_id dead_pre_map_comp0 dead_pre_map_comp fp_map_id
      sig_map_comp sig_map_cong ssig_map_thms ssig_map_comp flat_simps flat_pointful_natural
      flat_flat Lam_pointful_natural eval_core_simps;

    val eval_thm = derive_eval_thm ctxt dtor_inject dtor_unfold_thm eval_def;
    val eval_flat = derive_eval_flat ctxt Y Z fpT ssig_T dead_ssig_map flat eval x
      dead_pre_map_comp0 dtor_unfold_unique ssig_map_id ssig_map_comp flat_pointful_natural
      eval_core_pointful_natural eval_core_flat eval_thm;
    val eval_Oper = derive_eval_Oper ctxt live Y Z fpT sig_T ssig_T dead_sig_map Oper eval algLam x
      sig_map_ident sig_map_comp0 sig_map_comp Oper_natural_pointful VLeaf_natural flat_simps
      eval_flat algLam_def;
    val eval_VLeaf = derive_eval_V_or_CLeaf ctxt Y fpT VLeaf eval x dead_pre_map_id
      dead_pre_map_comp fp_map_id dtor_unfold_unique VLeaf_map_thm eval_core_simps eval_thm;
    val eval_CLeaf = derive_eval_V_or_CLeaf ctxt Y fpT CLeaf eval x dead_pre_map_id
      dead_pre_map_comp fp_map_id dtor_unfold_unique CLeaf_map_thm eval_core_simps eval_thm;

    val extdd_mor = derive_extdd_mor ctxt Y Z preT fpT ssig_T dead_pre_map dtor extdd cutSsig f g
      dead_pre_map_comp0 dead_pre_map_comp VLeaf_map_thm ssig_map_comp flat_pointful_natural
      eval_core_pointful_natural eval_thm eval_flat eval_VLeaf cutSsig_def;
    val mor_cutSsig_flat = derive_mor_cutSsig_flat ctxt Y Z preT fpT ssig_T dead_pre_map
      dead_ssig_map dtor flat eval_core eval cutSsig f g dead_pre_map_comp0 dead_pre_map_comp
      dead_pre_map_cong dtor_unfold_unique dead_ssig_map_comp0 ssig_map_comp flat_simps
      flat_pointful_natural eval_core_pointful_natural flat_flat flat_VLeaf eval_core_flat
      cutSsig_def cutSsig_def_pointful_natural eval_thm;
    val extdd_o_VLeaf = derive_extdd_o_VLeaf ctxt Y Z preT fpT ssig_T dead_pre_map dtor VLeaf extdd
      f g dead_pre_map_comp0 dead_pre_map_comp dtor_inject ssig_map_thms eval_core_simps eval_thm
      eval_VLeaf;

    val (corecU_ctor, corecU_unique) = derive_corecU_ctor_unique ctxt Y Z preT fpT ssig_T
      dead_pre_map ctor dtor VLeaf extdd corecU f g dead_pre_map_comp ctor_dtor dtor_unfold_thm
      dtor_unfold_unique ssig_map_thms dead_ssig_map_comp0 flat_simps flat_VLeaf eval_core_simps
      extdd_mor extdd_o_VLeaf cutSsig_def mor_cutSsig_flat corecU_def;

    val dtor_algLam = derive_dtor_algLam ctxt Y Z preT fpT sig_T ssig_T dead_pre_map dtor
      dead_sig_map Lam eval algLam x pre_map_comp dead_pre_map_id dead_pre_map_comp0
      dead_pre_map_comp sig_map_comp Oper_pointful_natural ssig_map_thms dead_ssig_map_comp0
      Lam_pointful_natural eval_core_simps eval_thm eval_flat eval_VLeaf algLam_def;
  in
    (Sig_pointful_natural, flat_pointful_natural, Lam_natural_pointful, Lam_pointful_natural,
     flat_VLeaf, eval_core_pointful_natural, eval_thm, eval_flat,
     [eval_Oper, eval_VLeaf, eval_CLeaf], corecU_ctor, corecU_unique, dtor_algLam)
  end;

fun derive_embL_natural_etc ctxt Inx_const old_ssig_bnf ssig_bnf Y Z preT fpT old_ssig_T ssig_T
    dead_pre_map Sig dead_old_ssig_map embL old_algLam algLam old_flat flat old_eval_core eval_core
    old_eval eval x f old_ssig_induct dead_pre_map_comp0 dead_pre_map_comp fp_map_id dtor_inject
    dtor_unfold_unique Sig_pointful_natural unsig_thm sig_map_thm old_sig_map_comp old_sig_map_cong
    old_ssig_map_thms old_Lam_pointful_natural Lam_def old_flat_simps flat_simps embL_simps
    embL_transfer old_eval_core_simps eval_core_simps old_eval_thm eval_thm old_dtor_algLam
    dtor_algLam old_algLam_thm =
  let
    val embL_natural = derive_natural_from_transfer ctxt [(Y, Z)] [] [] f embL embL_transfer
      [old_ssig_bnf, ssig_bnf] [];

    val embL_pointful_natural = mk_pointful ctxt embL_natural RS sym;
    val old_algLam_pointful = mk_pointful ctxt old_algLam_thm;

    val flat_embL = derive_flat_embL ctxt Y Z old_ssig_T ssig_T dead_old_ssig_map embL old_flat flat
      x old_ssig_induct fp_map_id Sig_pointful_natural old_sig_map_comp old_sig_map_cong
      old_ssig_map_thms old_flat_simps flat_simps embL_simps;
    val eval_core_embL = derive_eval_core_embL ctxt Y Z preT old_ssig_T ssig_T dead_pre_map embL
      old_eval_core eval_core x old_ssig_induct dead_pre_map_comp0 dead_pre_map_comp
      Sig_pointful_natural unsig_thm old_sig_map_comp old_sig_map_cong old_Lam_pointful_natural
      Lam_def flat_embL embL_simps embL_pointful_natural old_eval_core_simps eval_core_simps;
    val eval_embL = derive_eval_embL ctxt Y fpT embL old_eval eval dead_pre_map_comp0
      dtor_unfold_unique embL_pointful_natural eval_core_embL old_eval_thm eval_thm;

    val algLam_algLam = derive_algLam_algLam ctxt Inx_const Y fpT Sig old_algLam algLam
      dead_pre_map_comp dtor_inject unsig_thm sig_map_thm Lam_def eval_embL old_dtor_algLam
      dtor_algLam;
  in
    (embL_pointful_natural, old_algLam_pointful, eval_embL, algLam_algLam)
  end;

fun define_corecUU_etc fp_b version live_AsBs Y Z preT fpT ssig_T pre_map dead_pre_map pre_rel
    fp_rel ctor Oper ssig_map dead_ssig_map ssig_rel proto_sctr flat eval_core eval corecU fs f g Rs
    R pre_map_transfer fp_k_T_rel_eqs dtor_unfold_transfer dtor_transfer ssig_map_transfer
    proto_sctr_transfer proto_sctr_pointful_natural flat_transfer flat_pointful_natural
    eval_core_transfer eval_core_pointful_natural eval_thm eval_flat eval_Oper algLam_thm
    cutSsig_def corecU_def corecU_ctor corecU_unique pre_bnf dead_pre_bnf fp_res ssig_fp_sugar
    lthy =
  let
    val ssig_bnf = #fp_bnf ssig_fp_sugar;

    val dead_pre_map_comp0 = map_comp0_of_bnf dead_pre_bnf;
    val dead_pre_map_comp = map_comp_of_bnf dead_pre_bnf;
    val [dtor_ctor] = #dtor_ctors fp_res;
    val [dtor_inject] = #dtor_injects fp_res;
    val ssig_map_comp = map_comp_of_bnf ssig_bnf;

    val sctr_rhs = HOLogic.mk_comp (Oper, substT Y ssig_T proto_sctr);
    val ((sctr, sctr_def), lthy) = lthy
      |> define_const true fp_b version sctrN sctr_rhs;

    val (corecUU_data as (corecUU, corecUU_def), lthy) = lthy
      |> define_corecUU fp_b version Y Z preT ssig_T dead_pre_map dead_ssig_map flat eval_core sctr
        corecU;

    val eval_sctr = derive_eval_sctr lthy Y Z fpT ssig_T dead_pre_map ctor eval sctr
      proto_sctr_pointful_natural eval_Oper algLam_thm sctr_def;

    val sctr_transfer = derive_sctr_transfer lthy live_AsBs Y Z ssig_T Rs R pre_rel ssig_rel sctr
      sctr_def fp_k_T_rel_eqs [proto_sctr_transfer];

    val sctr_natural = derive_natural_from_transfer_with_pre_type lthy live_AsBs Y Z preT ssig_T
      pre_map ssig_map fs f sctr sctr_transfer [pre_bnf, ssig_bnf] [];

    val sctr_pointful_natural = mk_pointful lthy sctr_natural RS sym;
    val eval_sctr_pointful = mk_pointful lthy eval_sctr RS sym;

    val (corecUU_pointfree, corecUU_unique) = derive_corecUU_pointfree_unique lthy Y Z preT fpT
      ssig_T dead_pre_map ctor dead_ssig_map eval corecUU f g dead_pre_map_comp0 dead_pre_map_comp
      dtor_ctor dtor_inject ssig_map_comp flat_pointful_natural eval_core_pointful_natural eval_thm
      eval_flat corecU_ctor corecU_unique sctr_pointful_natural eval_sctr_pointful corecUU_def;

    val corecUU_thm = mk_pointful lthy corecUU_pointfree;

    val corecUU_transfer = derive_corecUU_transfer lthy live_AsBs Y Z Rs R preT ssig_T pre_rel
      fp_rel ssig_rel corecUU cutSsig_def corecU_def corecUU_def fp_k_T_rel_eqs
      [pre_map_transfer, dtor_unfold_transfer, dtor_transfer, ssig_map_transfer, flat_transfer,
       eval_core_transfer, sctr_transfer, @{thm convol_transfer} (*FIXME: needed?*)];
  in
    ((corecUU_data, corecUU_thm, corecUU_unique, corecUU_transfer, eval_sctr, sctr_transfer,
      sctr_pointful_natural), lthy)
  end;

fun mk_equivp T = Const (\<^const_name>\<open>equivp\<close>, mk_predT [mk_pred2T T T]);

fun derive_equivp_Retr ctxt fpT Retr R dead_pre_rel_refl_thm dead_pre_rel_flip_thm
    dead_pre_rel_mono_thm dead_pre_rel_compp_thm =
  let
    val prem = HOLogic.mk_Trueprop (mk_equivp fpT $ R);
    val goal = Logic.mk_implies (prem, HOLogic.mk_Trueprop (mk_equivp fpT $ (betapply (Retr, R))));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} =>
      mk_equivp_Retr_tac ctxt dead_pre_rel_refl_thm dead_pre_rel_flip_thm dead_pre_rel_mono_thm
        dead_pre_rel_compp_thm))
    |> Thm.close_derivation \<^here>
  end;

fun derive_Retr_coinduct ctxt fpT Retr R dtor_rel_coinduct_thm rel_eq_thm =
  let
    val goal = HOLogic.mk_Trueprop (list_all_free [R]
      (HOLogic.mk_imp (mk_leq R (Retr $ R), mk_leq R (HOLogic.eq_const fpT))));
  in
    Goal.prove_sorry ctxt [] [] goal (fn {context = ctxt, prems = _} =>
      mk_Retr_coinduct_tac ctxt dtor_rel_coinduct_thm rel_eq_thm)
    |> Thm.close_derivation \<^here>
  end;

fun derive_Retr fp_sugar fpT dead_pre_bnf ctor dtor names_lthy lthy =
  let
    val (R, _) = names_lthy
      |> yield_singleton (mk_Frees "R") (mk_pred2T fpT fpT);
    val pre_fpT = pre_type_of_ctor fpT ctor;
    val fp_pre_rel = mk_rel1 lthy fpT fpT pre_fpT dead_pre_bnf;
    val Retr = Abs ("R", fastype_of R, Abs ("a", fpT,
      Abs ("b", fpT, list_comb (fp_pre_rel, [Bound 2, dtor $ Bound 1, dtor $ Bound 0]))));
    val equivp_Retr = derive_equivp_Retr lthy fpT Retr R (rel_refl_of_bnf dead_pre_bnf)
      (rel_flip_of_bnf dead_pre_bnf) (rel_mono_of_bnf dead_pre_bnf) (rel_OO_of_bnf dead_pre_bnf);

    val Retr_coinduct = derive_Retr_coinduct lthy fpT Retr R
      (fp_sugar |> #fp_res |> #xtor_rel_co_induct) (fp_sugar |> #fp_bnf |> rel_eq_of_bnf);
  in
    (Retr, equivp_Retr, Retr_coinduct)
  end;

fun mk_gen_cong fpT eval_domT =
  let val fp_relT = mk_pred2T fpT fpT in
    Const (\<^const_name>\<open>cong.gen_cong\<close>,
      [mk_predT [fp_relT, eval_domT, eval_domT], eval_domT --> fpT, fp_relT] ---> fp_relT)
  end;

fun mk_cong_locale rel eval Retr =
  Const (\<^const_name>\<open>cong\<close>, mk_predT (map fastype_of [rel, eval, Retr]));

fun derive_cong_locale ctxt rel eval Retr0 tac =
  let
    val Retr = enforce_type ctxt domain_type (domain_type (fastype_of rel)) Retr0;
    val goal = HOLogic.mk_Trueprop (list_comb (mk_cong_locale rel eval Retr, [rel, eval, Retr]));
  in
    Variable.add_free_names ctxt goal []
    |> (fn vars => Goal.prove_sorry ctxt vars [] goal (fn {context = ctxt, prems = _} => tac ctxt))
    |> Thm.close_derivation \<^here>
  end;

fun derive_cong_general fp_b version fpT dead_ssig_bnf dead_pre_bnf eval Retr equivp_Retr
    Retr_coinduct eval_thm eval_core_transfer lthy =
  let
    val eval_domT = domain_type (fastype_of eval);

    fun cong_locale_tac ctxt =
      mk_cong_locale_tac ctxt (rel_mono_of_bnf dead_pre_bnf) (rel_map_of_bnf dead_pre_bnf)
        equivp_Retr (rel_mono_of_bnf dead_ssig_bnf) (rel_map_of_bnf dead_ssig_bnf) eval_thm
        eval_core_transfer;

    val rel = mk_rel1 lthy fpT fpT eval_domT dead_ssig_bnf;
    val cong_rhs = list_comb (mk_gen_cong fpT eval_domT, [rel, eval]);
    val ((_, cong_def), lthy) = lthy
      |> define_const false fp_b version congN cong_rhs;

    val cong_locale = derive_cong_locale lthy rel eval Retr cong_locale_tac;

    val fold_cong_def = Local_Defs.fold lthy [cong_def];

    fun instance_of_gen thm = fold_cong_def (thm OF [cong_locale]);

    val cong_base = instance_of_gen @{thm cong.imp_gen_cong};
    val cong_refl = instance_of_gen @{thm cong.gen_cong_reflp};
    val cong_sym = instance_of_gen @{thm cong.gen_cong_symp};
    val cong_trans = instance_of_gen @{thm cong.gen_cong_transp};

    fun mk_cong_rho thm = thm RS instance_of_gen @{thm cong.gen_cong_rho};

    val dtor_coinduct = @{thm predicate2I_obj} RS
      (Retr_coinduct RS instance_of_gen @{thm cong.coinduction} RS @{thm predicate2D_obj});
  in
    (cong_def, cong_locale, cong_base, cong_refl, cong_sym, cong_trans, dtor_coinduct, mk_cong_rho,
     lthy)
  end;

fun derive_cong_base fp_b version fpT dead_ssig_bnf ssig_fp_bnf_sugar dead_pre_bnf eval eval_thm
    eval_core_transfer eval_VLeaf eval_sctr sctr_transfer Retr equivp_Retr Retr_coinduct lthy =
  let
    val (cong_def, cong_locale, cong_base, cong_refl, cong_sym, cong_trans, dtor_coinduct,
         mk_cong_rho, lthy) =
      derive_cong_general fp_b version fpT dead_ssig_bnf dead_pre_bnf eval Retr equivp_Retr
        Retr_coinduct eval_thm eval_core_transfer lthy;

    val dead_pre_map_id0 = map_id0_of_bnf dead_pre_bnf;
    val dead_pre_map_comp0 = map_comp0_of_bnf dead_pre_bnf;
    val dead_pre_map_cong0 = map_cong0_of_bnf dead_pre_bnf;
    val dead_pre_map_cong0' =
      @{thm box_equals[OF _ o_apply[symmetric] id_apply[symmetric]]} RS dead_pre_map_cong0 RS ext;
    val dead_pre_rel_map = rel_map_of_bnf dead_pre_bnf;

    val ctor_alt_thm = eval_VLeaf RS (@{thm eq_comp_compI} OF [eval_sctr,
      trans OF [dead_pre_map_comp0 RS sym, trans OF [dead_pre_map_cong0', dead_pre_map_id0]]]);

    val cong_ctor_intro = mk_cong_rho ctor_alt_thm
      |> unfold_thms lthy [o_apply]
      |> (fn thm => sctr_transfer RS rel_funD RS thm)
      |> unfold_thms lthy (id_apply :: dead_pre_rel_map @ #rel_injects ssig_fp_bnf_sugar);
  in
    ({cong_def = cong_def, cong_locale = cong_locale, cong_base = cong_base, cong_refl = cong_refl,
      cong_sym = cong_sym, cong_trans = cong_trans, dtor_coinduct = dtor_coinduct,
      cong_alg_intros = [cong_ctor_intro]}, lthy)
  end;

fun update_cong_alg_intros ctxt cong_def cong_locale old_cong_def old_cong_locale emb =
  let
    fun instance_of_gen thm = Local_Defs.fold ctxt [cong_def] (thm OF [cong_locale]);
    fun instance_of_old_gen thm = Local_Defs.fold ctxt [old_cong_def] (thm OF [old_cong_locale]);

    val emb_idem = @{thm ord_le_eq_trans} OF [emb, instance_of_gen @{thm cong.gen_cong_idem}];
    fun mk_rel_mono bnf = instance_of_old_gen @{thm cong.leq_gen_cong} RS rel_mono_of_bnf bnf RS
      @{thm predicate2D};
    fun mk_intro bnf thm = mk_rel_mono bnf RS (@{thm predicate2D} OF [emb_idem, thm]);
  in
    map2 mk_intro
  end

fun derive_cong_step fp_b version fpT dead_ssig_bnf dead_pre_bnf eval eval_thm eval_core_transfer
    old_dtor_coinduct_info algrho_def k_as_ssig_transfer Retr equivp_Retr Retr_coinduct
    eval_embL embL_transfer old_all_dead_k_bnfs lthy =
  let
    val old_cong_def = #cong_def old_dtor_coinduct_info;
    val old_cong_locale = #cong_locale old_dtor_coinduct_info;
    val old_cong_alg_intros = #cong_alg_intros old_dtor_coinduct_info;

    val (cong_def, cong_locale, cong_base, cong_refl, cong_sym, cong_trans, dtor_coinduct,
         mk_cong_rho, lthy) =
      derive_cong_general fp_b version fpT dead_ssig_bnf dead_pre_bnf eval Retr equivp_Retr
        Retr_coinduct eval_thm eval_core_transfer lthy;

    val cong_alg_intro =
      k_as_ssig_transfer RS rel_funD RS mk_cong_rho (HOLogic.mk_obj_eq algrho_def);

    val gen_cong_emb =
      (@{thm gen_cong_emb} OF [old_cong_locale, cong_locale, eval_embL, embL_transfer])
      |> Local_Defs.fold lthy [old_cong_def, cong_def];

    val cong_alg_intros = update_cong_alg_intros lthy cong_def cong_locale old_cong_def
      old_cong_locale gen_cong_emb old_all_dead_k_bnfs old_cong_alg_intros;
  in
    ({cong_def = cong_def, cong_locale = cong_locale, cong_base = cong_base, cong_refl = cong_refl,
      cong_sym = cong_sym, cong_trans = cong_trans, dtor_coinduct = dtor_coinduct,
      cong_alg_intros = cong_alg_intro :: cong_alg_intros}, lthy)
  end;

fun derive_cong_merge fp_b version fpT old1_friend_names old2_friend_names dead_ssig_bnf
    dead_pre_bnf eval eval_thm eval_core_transfer old1_dtor_coinduct_info old2_dtor_coinduct_info
    Retr equivp_Retr Retr_coinduct eval_embLL embLL_transfer eval_embLR embLR_transfer
    old1_all_dead_k_bnfs old2_all_dead_k_bnfs lthy =
  let
    val old1_cong_def = #cong_def old1_dtor_coinduct_info;
    val old1_cong_locale = #cong_locale old1_dtor_coinduct_info;
    val old1_cong_alg_intros = #cong_alg_intros old1_dtor_coinduct_info;
    val old2_cong_def = #cong_def old2_dtor_coinduct_info;
    val old2_cong_locale = #cong_locale old2_dtor_coinduct_info;
    val old2_cong_alg_intros = #cong_alg_intros old2_dtor_coinduct_info;

    val (cong_def, cong_locale, cong_base, cong_refl, cong_sym, cong_trans, dtor_coinduct, _,
         lthy) =
      derive_cong_general fp_b version fpT dead_ssig_bnf dead_pre_bnf eval Retr equivp_Retr
        Retr_coinduct eval_thm eval_core_transfer lthy;

    val emb1 = (@{thm gen_cong_emb} OF [old1_cong_locale, cong_locale, eval_embLL, embLL_transfer])
      |> Local_Defs.fold lthy [old1_cong_def, cong_def];
    val emb2 = (@{thm gen_cong_emb} OF [old2_cong_locale, cong_locale, eval_embLR, embLR_transfer])
      |> Local_Defs.fold lthy [old2_cong_def, cong_def];

    val cong_alg_intros1 = update_cong_alg_intros lthy cong_def cong_locale old1_cong_def
      old1_cong_locale emb1 old1_all_dead_k_bnfs old1_cong_alg_intros;
    val cong_alg_intros2 = update_cong_alg_intros lthy cong_def cong_locale old2_cong_def
      old2_cong_locale emb2 old2_all_dead_k_bnfs old2_cong_alg_intros;

    val (cong_algrho_intros1, cong_ctor_intro1) = split_last cong_alg_intros1;
    val (cong_algrho_intros2, _) = split_last cong_alg_intros2;
    val (old1_all_rho_k_bnfs, old1_Sig_bnf) = split_last old1_all_dead_k_bnfs;
    val (old2_all_rho_k_bnfs, _) = split_last old2_all_dead_k_bnfs;

    val (friend_names, (cong_algrho_intros, all_rho_k_bnfs)) =
      merge_lists (op = o apply2 fst)
        (old1_friend_names ~~ (cong_algrho_intros1 ~~ old1_all_rho_k_bnfs))
        (old2_friend_names ~~ (cong_algrho_intros2 ~~ old2_all_rho_k_bnfs))
      |> split_list ||> split_list;
  in
    (({cong_def = cong_def, cong_locale = cong_locale, cong_base = cong_base, cong_refl = cong_refl,
       cong_sym = cong_sym, cong_trans = cong_trans, dtor_coinduct = dtor_coinduct,
       cong_alg_intros = cong_algrho_intros @ [cong_ctor_intro1]}, all_rho_k_bnfs @ [old1_Sig_bnf],
       friend_names), lthy)
  end;

fun derive_corecUU_base fpT_name lthy =
  let
    val fp_sugar as {T = Type (_, fpT_args0), pre_bnf, fp_bnf, fp_res, ...} =
      checked_fp_sugar_of lthy fpT_name;
    val fpT_Ss = map Type.sort_of_atyp fpT_args0;
    val fp_alives = liveness_of_fp_bnf (length fpT_args0) fp_bnf;

    val (((Es, Fs0), [Y, Z]), names_lthy) = lthy
      |> mk_TFrees' fpT_Ss
      ||>> mk_TFrees' fpT_Ss
      ||>> mk_TFrees 2;
    val Fs = @{map 3} (fn alive => fn E => fn F => if alive then F else E) fp_alives Es Fs0;

    val As = Es @ [Y];
    val Bs = Es @ [Z];

    val live_EsFs = filter (op <>) (Es ~~ Fs);
    val live_AsBs = live_EsFs @ [(Y, Z)];
    val fTs = map (op -->) live_EsFs;
    val RTs = map (uncurry mk_pred2T) live_EsFs;
    val live = length live_EsFs;

    val ((((((x, fs), f), g), Rs), R), names_lthy) = names_lthy
      |> yield_singleton (mk_Frees "x") Y
      ||>> mk_Frees "f" fTs
      ||>> yield_singleton (mk_Frees "f") (Y --> Z)
      ||>> yield_singleton (mk_Frees "g") (Y --> Z)
      ||>> mk_Frees "R" RTs
      ||>> yield_singleton (mk_Frees "R") (mk_pred2T Y Z);

    val ctor = mk_ctor Es (the_single (#ctors fp_res));
    val dtor = mk_dtor Es (the_single (#dtors fp_res));

    val fpT = Type (fpT_name, Es);
    val preT = pre_type_of_ctor Y ctor;

    val ((fp_b, version), lthy) = lthy |> get_name_next_version_of fpT_name;

    val ((sig_fp_sugar, ssig_fp_sugar), lthy) = lthy
      |> define_sig_type fp_b version fp_alives Es Y preT
      ||>> define_ssig_type fp_b version fp_alives Es Y fpT;

    val sig_bnf = #fp_bnf sig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;

    val (((dead_pre_bnf, dead_sig_bnf), dead_ssig_bnf), lthy) = lthy
      |> bnf_kill_all_but 1 pre_bnf
      ||>> bnf_kill_all_but 1 sig_bnf
      ||>> bnf_kill_all_but 1 ssig_bnf;

    val sig_fp_ctr_sugar = #fp_ctr_sugar sig_fp_sugar;
    val ssig_fp_ctr_sugar = #fp_ctr_sugar ssig_fp_sugar;

    val sig_fp_bnf_sugar = #fp_bnf_sugar sig_fp_sugar;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val ssig_fp_induct_sugar = the (#fp_co_induct_sugar ssig_fp_sugar);

    val sig_ctr_sugar = #ctr_sugar sig_fp_ctr_sugar;
    val ssig_ctr_sugar = #ctr_sugar ssig_fp_ctr_sugar;

    val sig_T_name = fst (dest_Type (#T sig_fp_sugar));
    val ssig_T_name = fst (dest_Type (#T ssig_fp_sugar));

    val sig_T = Type (sig_T_name, As);
    val ssig_T = Type (ssig_T_name, As);

    val pre_map = mk_mapN lthy live_AsBs preT pre_bnf;
    val pre_rel = mk_relN lthy live_AsBs preT pre_bnf;
    val dead_pre_map = mk_map1 lthy Y Z preT dead_pre_bnf;
    val fp_rel = mk_relN lthy live_EsFs fpT fp_bnf;
    val dtor_unfold = mk_co_rec (Proof_Context.theory_of lthy) Greatest_FP [Z] fpT
      (the_single (#xtor_un_folds fp_res));
    val Sig = mk_ctr As (the_single (#ctrs sig_ctr_sugar));
    val unsig = mk_disc_or_sel As (the_single (the_single (#selss sig_ctr_sugar)));
    val sig_rel = mk_relN lthy live_AsBs sig_T sig_bnf;
    val dead_sig_map = mk_map 1 As Bs (map_of_bnf dead_sig_bnf);
    val [Oper, VLeaf, CLeaf] = map (mk_ctr As) (#ctrs ssig_ctr_sugar);
    val ssig_map = mk_mapN lthy live_AsBs ssig_T ssig_bnf;
    val ssig_rel = mk_relN lthy live_AsBs ssig_T ssig_bnf;
    val dead_ssig_map = mk_map 1 As Bs (map_of_bnf dead_ssig_bnf);

    val ((Lam, Lam_def), lthy) = lthy
      |> define_Lam_base fp_b version Y Z preT ssig_T dead_pre_map Sig unsig dead_sig_map Oper
        VLeaf;

    val proto_sctr = Sig;

    val pre_map_transfer = map_transfer_of_bnf pre_bnf;
    val pre_rel_def = rel_def_of_bnf pre_bnf;
    val dead_pre_map_id = map_id_of_bnf dead_pre_bnf;
    val dead_pre_map_comp = map_comp_of_bnf dead_pre_bnf;
    val fp_rel_eq = rel_eq_of_bnf fp_bnf;
    val [ctor_dtor] = #ctor_dtors fp_res;
    val [dtor_ctor] = #dtor_ctors fp_res;
    val [dtor_inject] = #dtor_injects fp_res;
    val [dtor_unfold_thm] = #xtor_un_fold_thms fp_res;
    val dtor_unfold_unique = #xtor_un_fold_unique fp_res;
    val [dtor_unfold_transfer] = #xtor_un_fold_transfers fp_res;
    val [dtor_rel_thm] = #xtor_rels fp_res;
    val unsig_thm = the_single (the_single (#sel_thmss sig_ctr_sugar));
    val [sig_map_thm] = #map_thms sig_fp_bnf_sugar;
    val [Oper_map_thm, VLeaf_map_thm, CLeaf_map_thm] = #map_thms ssig_fp_bnf_sugar;
    val sig_map_transfer = map_transfer_of_bnf sig_bnf;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val ssig_map_transfer = map_transfer_of_bnf ssig_bnf;
    val ssig_induct = the_single (#co_inducts ssig_fp_induct_sugar);

    val dtor_transfer = derive_dtor_transfer lthy live_EsFs Y Z pre_rel fp_rel Rs dtor dtor_rel_thm;
    val preT_rel_eqs = map rel_eq_of_bnf (map_filter (bnf_of lthy) (add_type_namesT preT []));

    val Sig_transfer = derive_sig_transfer I lthy live_AsBs pre_rel sig_rel Rs R Sig pre_rel_def
      preT_rel_eqs (the_single (#ctr_transfers sig_fp_ctr_sugar));
    val proto_sctr_transfer = Sig_transfer;
    val unsig_transfer = derive_sig_transfer swap lthy live_AsBs pre_rel sig_rel Rs R unsig
      pre_rel_def preT_rel_eqs (the_single (#sel_transfers sig_fp_ctr_sugar));
    val Lam_transfer = derive_Lam_or_eval_core_transfer lthy live_AsBs Y Z preT ssig_T Rs R pre_rel
      sig_rel ssig_rel Lam Lam_def []
      [pre_map_transfer, sig_map_transfer, Sig_transfer, unsig_transfer];

    val ((((((((flat, _, flat_simps), flat_transfer),
            ((eval_core, _, eval_core_simps), eval_core_transfer)), (eval, eval_def)),
          (cutSsig, cutSsig_def)), (algLam, algLam_def)), (corecU, corecU_def)), lthy) = lthy
      |> define_flat_etc fp_b version live_AsBs Y Z preT fpT sig_T ssig_T Oper VLeaf CLeaf pre_rel
        dead_pre_map dtor dtor_unfold dead_sig_map ssig_rel dead_ssig_map Lam Rs R pre_map_transfer
        [fp_rel_eq] sig_map_transfer ssig_map_transfer Lam_transfer dtor_transfer;

    val (Sig_pointful_natural, flat_pointful_natural, _, Lam_pointful_natural, _,
         eval_core_pointful_natural, eval_thm, eval_flat, eval_simps as [eval_Oper, eval_VLeaf, _],
         corecU_ctor, corecU_unique, dtor_algLam) =
      derive_Sig_natural_etc lthy live live_AsBs Y Z preT fpT fpT sig_T ssig_T pre_map dead_pre_map
        ctor dtor Sig dead_sig_map Oper VLeaf CLeaf ssig_map dead_ssig_map Lam flat eval_core eval
        cutSsig algLam corecU x fs f g ctor_dtor dtor_inject dtor_unfold_thm dtor_unfold_unique
        sig_map_thm ssig_induct ssig_map_thms Oper_map_thm VLeaf_map_thm CLeaf_map_thm Lam_transfer
        flat_simps flat_transfer eval_core_simps eval_core_transfer eval_def cutSsig_def algLam_def
        corecU_def pre_bnf pre_bnf dead_pre_bnf fp_bnf sig_bnf ssig_bnf dead_ssig_bnf;

    val proto_sctr_pointful_natural = Sig_pointful_natural;

    val algLam_thm = derive_algLam_base lthy Y Z preT fpT dead_pre_map ctor dtor algLam proto_sctr
      dead_pre_map_id dead_pre_map_comp ctor_dtor dtor_ctor dtor_unfold_unique unsig_thm
      Sig_pointful_natural ssig_map_thms Lam_def flat_simps eval_core_simps eval_thm algLam_def;

    val (((corecUU, _), corecUU_thm, corecUU_unique, corecUU_transfer, eval_sctr, sctr_transfer,
          sctr_pointful_natural), lthy) = lthy
      |> define_corecUU_etc fp_b version live_AsBs Y Z preT fpT ssig_T pre_map dead_pre_map pre_rel
        fp_rel ctor Oper ssig_map dead_ssig_map ssig_rel proto_sctr flat eval_core eval corecU fs f
        g Rs R pre_map_transfer [] dtor_unfold_transfer dtor_transfer ssig_map_transfer
        proto_sctr_transfer proto_sctr_pointful_natural flat_transfer flat_pointful_natural
        eval_core_transfer eval_core_pointful_natural eval_thm eval_flat eval_Oper algLam_thm
        cutSsig_def corecU_def corecU_ctor corecU_unique pre_bnf dead_pre_bnf fp_res ssig_fp_sugar;

    val (Retr, equivp_Retr, Retr_coinduct) = lthy
      |> derive_Retr fp_sugar fpT dead_pre_bnf ctor dtor names_lthy;

    val (dtor_coinduct_info, lthy) = lthy
      |> derive_cong_base fp_b version fpT dead_ssig_bnf ssig_fp_bnf_sugar dead_pre_bnf eval
      eval_thm eval_core_transfer eval_VLeaf eval_sctr sctr_transfer Retr equivp_Retr Retr_coinduct;

    val buffer =
      {Oper = Oper, VLeaf = VLeaf, CLeaf = CLeaf, ctr_wrapper = Sig, friends = Symtab.empty};

    val notes =
      [(corecUU_transferN, [corecUU_transfer])] @
      (if Config.get lthy bnf_internals then
         [(algLamN, [algLam_thm]),
          (cong_alg_introsN, #cong_alg_intros dtor_coinduct_info),
          (cong_localeN, [#cong_locale dtor_coinduct_info]),
          (corecU_ctorN, [corecU_ctor]),
          (corecU_uniqueN, [corecU_unique]),
          (corecUUN, [corecUU_thm]),
          (corecUU_uniqueN, [corecUU_unique]),
          (dtor_algLamN, [dtor_algLam]),
          (dtor_coinductN, [#dtor_coinduct dtor_coinduct_info]),
          (dtor_transferN, [dtor_transfer]),
          (equivp_RetrN, [equivp_Retr]),
          (evalN, [eval_thm]),
          (eval_core_pointful_naturalN, [eval_core_pointful_natural]),
          (eval_core_transferN, [eval_core_transfer]),
          (eval_flatN, [eval_flat]),
          (eval_simpsN, eval_simps),
          (flat_pointful_naturalN, [flat_pointful_natural]),
          (flat_transferN, [flat_transfer]),
          (Lam_pointful_naturalN, [Lam_pointful_natural]),
          (Lam_transferN, [Lam_transfer]),
          (proto_sctr_pointful_naturalN, [proto_sctr_pointful_natural]),
          (proto_sctr_transferN, [proto_sctr_transfer]),
          (Retr_coinductN, [Retr_coinduct]),
          (sctr_pointful_naturalN, [sctr_pointful_natural]),
          (sctr_transferN, [sctr_transfer]),
          (Sig_pointful_naturalN, [Sig_pointful_natural])]
        else
          [])
      |> map (fn (thmN, thms) =>
        ((mk_version_fp_binding true lthy version fp_b thmN, []), [(thms, [])]));
  in
    ({fp_b = fp_b, version = version, fpT = fpT, Y = Y, Z = Z, friend_names = [],
      sig_fp_sugars = [sig_fp_sugar], ssig_fp_sugar = ssig_fp_sugar, Lam = Lam,
      proto_sctr = proto_sctr, flat = flat, eval_core = eval_core, eval = eval, algLam = algLam,
      corecUU = corecUU, dtor_transfer = dtor_transfer, Lam_transfer = Lam_transfer,
      Lam_pointful_natural = Lam_pointful_natural, proto_sctr_transfer = proto_sctr_transfer,
      flat_simps = flat_simps, eval_core_simps = eval_core_simps, eval_thm = eval_thm,
      eval_simps = eval_simps, all_algLam_algs = [algLam_thm], algLam_thm = algLam_thm,
      dtor_algLam = dtor_algLam, corecUU_thm = corecUU_thm, corecUU_unique = corecUU_unique,
      corecUU_transfer = corecUU_transfer, buffer = buffer, all_dead_k_bnfs = [dead_pre_bnf],
      Retr = Retr, equivp_Retr = equivp_Retr, Retr_coinduct = Retr_coinduct,
      dtor_coinduct_info = dtor_coinduct_info}
     |> morph_corec_info (Local_Theory.target_morphism lthy),
     lthy |> Local_Theory.notes notes |> snd)
  end;

fun derive_corecUU_step (fpT as Type (fpT_name, res_Ds))
    ({friend_names = old_friend_names, sig_fp_sugars = old_sig_fp_sugars as old_sig_fp_sugar :: _,
      ssig_fp_sugar = old_ssig_fp_sugar, Lam = old_Lam0, proto_sctr = old_proto_sctr0,
      flat = old_flat0, eval_core = old_eval_core0, eval = old_eval0, algLam = old_algLam0,
      dtor_transfer, Lam_transfer = old_Lam_transfer,
      Lam_pointful_natural = old_Lam_pointful_natural,
      proto_sctr_transfer = old_proto_sctr_transfer, flat_simps = old_flat_simps,
      eval_core_simps = old_eval_core_simps, eval_thm = old_eval_thm,
      all_algLam_algs = old_all_algLam_algs, algLam_thm = old_algLam_thm,
      dtor_algLam = old_dtor_algLam, buffer = old_buffer, all_dead_k_bnfs = old_all_dead_k_bnfs,
      Retr = old_Retr0, equivp_Retr, Retr_coinduct, dtor_coinduct_info = old_dtor_coinduct_info,
      ...} : corec_info)
    friend_name friend_T fp_b version Y Z k_T dead_k_bnf sig_fp_sugar ssig_fp_sugar rho rho_transfer
    lthy =
  let
    val {pre_bnf = live_pre_bnf, fp_bnf = live_fp_bnf, fp_res, ...} =
      checked_fp_sugar_of lthy fpT_name;

    val names_lthy = lthy
      |> fold Variable.declare_typ [Y, Z];

    (* FIXME *)
    val live_EsFs = [];
    val live_AsBs = live_EsFs @ [(Y, Z)];
    val live = length live_EsFs;

    val ((((x, f), g), R), _) = names_lthy
      |> yield_singleton (mk_Frees "x") Y
      ||>> yield_singleton (mk_Frees "f") (Y --> Z)
      ||>> yield_singleton (mk_Frees "g") (Y --> Z)
      ||>> yield_singleton (mk_Frees "R") (mk_pred2T Y Z);

    (* FIXME *)
    val fs = [];
    val Rs = [];

    val ctor = mk_ctor res_Ds (the_single (#ctors fp_res));
    val dtor = mk_dtor res_Ds (the_single (#dtors fp_res));

    val friend_names = friend_name :: old_friend_names;

    val old_sig_bnf = #fp_bnf old_sig_fp_sugar;
    val old_ssig_bnf = #fp_bnf old_ssig_fp_sugar;
    val sig_bnf = #fp_bnf sig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;

    val ((((((dead_pre_bnf, dead_fp_bnf), dead_old_sig_bnf), dead_old_ssig_bnf), dead_sig_bnf),
          dead_ssig_bnf), lthy) = lthy
      |> bnf_kill_all_but 1 live_pre_bnf
      ||>> bnf_kill_all_but 0 live_fp_bnf
      ||>> bnf_kill_all_but 1 old_sig_bnf
      ||>> bnf_kill_all_but 1 old_ssig_bnf
      ||>> bnf_kill_all_but 1 sig_bnf
      ||>> bnf_kill_all_but 1 ssig_bnf;

    (* FIXME *)
    val pre_bnf = dead_pre_bnf;
    val fp_bnf = dead_fp_bnf;

    val old_ssig_fp_ctr_sugar = #fp_ctr_sugar old_ssig_fp_sugar;
    val sig_fp_ctr_sugar = #fp_ctr_sugar sig_fp_sugar;
    val ssig_fp_ctr_sugar = #fp_ctr_sugar ssig_fp_sugar;

    val sig_fp_bnf_sugar = #fp_bnf_sugar sig_fp_sugar;
    val old_ssig_fp_bnf_sugar = #fp_bnf_sugar old_ssig_fp_sugar;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val old_ssig_fp_induct_sugar = the (#fp_co_induct_sugar old_ssig_fp_sugar);
    val ssig_fp_induct_sugar = the (#fp_co_induct_sugar ssig_fp_sugar);

    val old_ssig_ctr_sugar = #ctr_sugar old_ssig_fp_ctr_sugar;
    val sig_ctr_sugar = #ctr_sugar sig_fp_ctr_sugar;
    val ssig_ctr_sugar = #ctr_sugar ssig_fp_ctr_sugar;

    val old_sig_T_name = fst (dest_Type (#T old_sig_fp_sugar));
    val old_ssig_T_name = fst (dest_Type (#T old_ssig_fp_sugar));
    val sig_T_name = fst (dest_Type (#T sig_fp_sugar));
    val ssig_T_name = fst (dest_Type (#T ssig_fp_sugar));

    val res_As = res_Ds @ [Y];
    val res_Bs = res_Ds @ [Z];
    val preT = pre_type_of_ctor Y ctor;
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val old_sig_T = Type (old_sig_T_name, res_As);
    val old_ssig_T = Type (old_ssig_T_name, res_As);
    val sig_T = Type (sig_T_name, res_As);
    val ssig_T = Type (ssig_T_name, res_As);
    val old_Lam_domT = Tsubst Y YpreT old_sig_T;
    val old_eval_core_domT = Tsubst Y YpreT old_ssig_T;

    val pre_map = mk_mapN lthy live_AsBs preT pre_bnf;
    val pre_rel = mk_relN lthy live_AsBs preT pre_bnf;
    val dead_pre_map = mk_map1 lthy Y Z preT dead_pre_bnf;
    val dead_pre_rel = mk_rel1 lthy Y Z preT dead_pre_bnf;
    val fp_rel = mk_relN lthy live_EsFs fpT fp_bnf;
    val dtor_unfold = mk_co_rec (Proof_Context.theory_of lthy) Greatest_FP [Z] fpT
      (the_single (#xtor_un_folds fp_res));
    val dead_k_map = mk_map1 lthy Y Z k_T dead_k_bnf;
    val Sig = mk_ctr res_As (the_single (#ctrs sig_ctr_sugar));
    val unsig = mk_disc_or_sel res_As (the_single (the_single (#selss sig_ctr_sugar)));
    val sig_rel = mk_relN lthy live_AsBs sig_T sig_bnf;
    val dead_old_sig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_old_sig_bnf);
    val dead_sig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_sig_bnf);
    val dead_sig_rel = mk_rel 1 res_As res_Bs (rel_of_bnf dead_sig_bnf);
    val [old_Oper, old_VLeaf, old_CLeaf] = map (mk_ctr res_As) (#ctrs old_ssig_ctr_sugar);
    val [Oper, VLeaf, CLeaf] = map (mk_ctr res_As) (#ctrs ssig_ctr_sugar);
    val dead_old_ssig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_old_ssig_bnf);
    val ssig_map = mk_mapN lthy live_AsBs ssig_T ssig_bnf;
    val ssig_rel = mk_relN lthy live_AsBs ssig_T ssig_bnf;
    val dead_ssig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_ssig_bnf);
    val old_Lam = enforce_type lthy domain_type old_Lam_domT old_Lam0;
    val old_proto_sctr = enforce_type lthy domain_type preT old_proto_sctr0;
    val old_flat = enforce_type lthy range_type old_ssig_T old_flat0;
    val old_eval_core = enforce_type lthy domain_type old_eval_core_domT old_eval_core0;
    val old_eval = enforce_type lthy range_type fpT old_eval0;
    val old_algLam = enforce_type lthy range_type fpT old_algLam0;

    val ((embL, embL_def, embL_simps), lthy) = lthy
      |> define_embL embLN fp_b version Y Z fpT old_sig_T old_ssig_T k_T ssig_T Inl_const
        dead_old_sig_map Sig old_Oper old_VLeaf old_CLeaf Oper VLeaf CLeaf;

    val ((Lam, Lam_def), lthy) = lthy
      |> define_Lam_step fp_b version Y Z preT old_ssig_T ssig_T dead_pre_map unsig rho embL
        old_Lam;

    val ((proto_sctr, proto_sctr_def), lthy) = lthy
      |> define_proto_sctr_step_or_merge fp_b version old_sig_T k_T Sig old_proto_sctr;

    val pre_map_comp = map_comp_of_bnf pre_bnf;
    val pre_map_transfer = map_transfer_of_bnf pre_bnf;
    val dead_pre_map_id = map_id_of_bnf dead_pre_bnf;
    val dead_pre_map_comp0 = map_comp0_of_bnf dead_pre_bnf;
    val dead_pre_map_comp = map_comp_of_bnf dead_pre_bnf;
    val fp_map_id = map_id_of_bnf fp_bnf;
    val [ctor_dtor] = #ctor_dtors fp_res;
    val [dtor_inject] = #dtor_injects fp_res;
    val [dtor_unfold_thm] = #xtor_un_fold_thms fp_res;
    val dtor_unfold_unique = #xtor_un_fold_unique fp_res;
    val [dtor_unfold_transfer] = #xtor_un_fold_transfers fp_res;
    val fp_k_T_rel_eqs =
      map rel_eq_of_bnf (map_filter (bnf_of lthy) (fold add_type_namesT [fpT, k_T] []));
    val unsig_thm = the_single (the_single (#sel_thmss sig_ctr_sugar));
    val [sig_map_thm] = #map_thms sig_fp_bnf_sugar;
    val old_sig_map_comp = map_comp_of_bnf old_sig_bnf;
    val old_sig_map_cong = map_cong_of_bnf old_sig_bnf;
    val old_ssig_map_thms = #map_thms old_ssig_fp_bnf_sugar;
    val [Oper_map_thm, VLeaf_map_thm, CLeaf_map_thm] = #map_thms ssig_fp_bnf_sugar;
    val old_sig_map_transfer = map_transfer_of_bnf old_sig_bnf;
    val sig_map_comp = map_comp_of_bnf sig_bnf;
    val sig_map_transfer = map_transfer_of_bnf sig_bnf;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val ssig_map_transfer = map_transfer_of_bnf ssig_bnf;
    val old_ssig_induct = the_single (#co_inducts old_ssig_fp_induct_sugar);
    val ssig_induct = the_single (#co_inducts ssig_fp_induct_sugar);

    val proto_sctr_transfer = derive_proto_sctr_transfer_step_or_merge lthy Y Z R dead_pre_rel
      dead_sig_rel proto_sctr proto_sctr_def fp_k_T_rel_eqs [old_proto_sctr_transfer];
    val embL_transfer = derive_transfer_by_transfer_prover lthy live_AsBs Rs R embL [embL_def]
      fp_k_T_rel_eqs [old_sig_map_transfer];
    val Lam_transfer = derive_Lam_or_eval_core_transfer lthy live_AsBs Y Z preT ssig_T Rs R pre_rel
      sig_rel ssig_rel Lam Lam_def fp_k_T_rel_eqs
      [pre_map_transfer, old_Lam_transfer, embL_transfer, rho_transfer];

    val ((((((((flat, _, flat_simps), flat_transfer),
            ((eval_core, _, eval_core_simps), eval_core_transfer)), (eval, eval_def)),
          (cutSsig, cutSsig_def)), (algLam, algLam_def)), (corecU, corecU_def)), lthy) = lthy
      |> define_flat_etc fp_b version live_AsBs Y Z preT fpT sig_T ssig_T Oper VLeaf CLeaf pre_rel
        dead_pre_map dtor dtor_unfold dead_sig_map ssig_rel dead_ssig_map Lam Rs R pre_map_transfer
        fp_k_T_rel_eqs sig_map_transfer ssig_map_transfer Lam_transfer dtor_transfer;

    val (Sig_pointful_natural, flat_pointful_natural, Lam_natural_pointful, Lam_pointful_natural,
         flat_VLeaf, eval_core_pointful_natural, eval_thm, eval_flat,
         eval_simps as [eval_Oper, _, _], corecU_ctor, corecU_unique, dtor_algLam) =
      derive_Sig_natural_etc lthy live live_AsBs Y Z preT fpT k_T sig_T ssig_T pre_map dead_pre_map
        ctor dtor Sig dead_sig_map Oper VLeaf CLeaf ssig_map dead_ssig_map Lam flat eval_core eval
        cutSsig algLam corecU x fs f g ctor_dtor dtor_inject dtor_unfold_thm dtor_unfold_unique
        sig_map_thm ssig_induct ssig_map_thms Oper_map_thm VLeaf_map_thm CLeaf_map_thm Lam_transfer
        flat_simps flat_transfer eval_core_simps eval_core_transfer eval_def cutSsig_def algLam_def
        corecU_def live_pre_bnf pre_bnf dead_pre_bnf fp_bnf sig_bnf ssig_bnf dead_ssig_bnf;

    val proto_sctr_natural = derive_natural_from_transfer_with_pre_type lthy live_AsBs Y Z preT
      ssig_T pre_map ssig_map fs f proto_sctr proto_sctr_transfer [pre_bnf, sig_bnf] [];
    val proto_sctr_pointful_natural = mk_pointful lthy proto_sctr_natural RS sym;

    val (embL_pointful_natural, old_algLam_pointful, eval_embL, algLam_algLam) =
      derive_embL_natural_etc lthy Inl_const old_ssig_bnf ssig_bnf Y Z preT fpT old_ssig_T ssig_T
        dead_pre_map Sig dead_old_ssig_map embL old_algLam algLam old_flat flat old_eval_core
        eval_core old_eval eval x f old_ssig_induct dead_pre_map_comp0 dead_pre_map_comp fp_map_id
        dtor_inject dtor_unfold_unique Sig_pointful_natural unsig_thm sig_map_thm old_sig_map_comp
        old_sig_map_cong old_ssig_map_thms old_Lam_pointful_natural Lam_def old_flat_simps
        flat_simps embL_simps embL_transfer old_eval_core_simps eval_core_simps old_eval_thm
        eval_thm old_dtor_algLam dtor_algLam old_algLam_thm;

    val algLam_thm = derive_algLam_step_or_merge lthy Y fpT ctor proto_sctr algLam proto_sctr_def
      old_algLam_pointful algLam_algLam;

    val k_as_ssig = mk_k_as_ssig Z old_sig_T k_T ssig_T Sig dead_sig_map Oper VLeaf;
    val k_as_ssig' = substT Y fpT k_as_ssig;

    val algrho_rhs = HOLogic.mk_comp (eval, k_as_ssig');
    val ((algrho, algrho_def), lthy) = lthy
      |> define_const true fp_b version algrhoN algrho_rhs;

    val k_as_ssig_transfer = derive_transfer_by_transfer_prover lthy live_AsBs Rs R k_as_ssig []
      fp_k_T_rel_eqs [sig_map_transfer];

    val k_as_ssig_natural = derive_natural_from_transfer lthy [(Y, Z)] [] [] f k_as_ssig
      k_as_ssig_transfer [ssig_bnf] [dead_k_bnf];

    val k_as_ssig_natural_pointful = mk_pointful lthy k_as_ssig_natural;

    val [_, Lam_Inr] = derive_Lam_Inl_Inr lthy Y Z preT old_sig_T old_ssig_T k_T ssig_T
      dead_pre_map Sig embL old_Lam Lam rho unsig_thm Lam_def;

    val eval_core_k_as_ssig = derive_eval_core_k_as_ssig lthy Y preT k_T rho eval_core k_as_ssig x
      pre_map_comp dead_pre_map_id sig_map_comp ssig_map_thms Lam_natural_pointful Lam_Inr
      flat_VLeaf eval_core_simps;

    val algLam_algrho = derive_algLam_algrho lthy Y fpT Sig algLam algrho algLam_def algrho_def;
    val dtor_algrho = derive_dtor_algrho lthy Y Z preT fpT k_T ssig_T dead_pre_map dead_k_map dtor
      rho eval algrho x eval_thm k_as_ssig_natural_pointful eval_core_k_as_ssig algrho_def;
    val all_algLam_algs = algLam_algLam :: algLam_algrho :: old_all_algLam_algs;

    val (((corecUU, _), corecUU_thm, corecUU_unique, corecUU_transfer, _, sctr_transfer,
          sctr_pointful_natural), lthy) = lthy
      |> define_corecUU_etc fp_b version live_AsBs Y Z preT fpT ssig_T pre_map dead_pre_map pre_rel
        fp_rel ctor Oper ssig_map dead_ssig_map ssig_rel proto_sctr flat eval_core eval corecU fs f
        g Rs R pre_map_transfer fp_k_T_rel_eqs dtor_unfold_transfer dtor_transfer ssig_map_transfer
        proto_sctr_transfer proto_sctr_pointful_natural flat_transfer flat_pointful_natural
        eval_core_transfer eval_core_pointful_natural eval_thm eval_flat eval_Oper algLam_thm
        cutSsig_def corecU_def corecU_ctor corecU_unique pre_bnf dead_pre_bnf fp_res ssig_fp_sugar;

    val (ctr_wrapper, friends) =
      mk_ctr_wrapper_friends lthy friend_name friend_T old_sig_T k_T Sig old_buffer;

    val Retr = enforce_type lthy (domain_type o domain_type) fpT old_Retr0;

    val (dtor_coinduct_info, lthy) = lthy
      |> derive_cong_step fp_b version fpT dead_ssig_bnf dead_pre_bnf eval eval_thm
        eval_core_transfer old_dtor_coinduct_info algrho_def k_as_ssig_transfer Retr equivp_Retr
        Retr_coinduct eval_embL embL_transfer old_all_dead_k_bnfs;

    val buffer =
      {Oper = Oper, VLeaf = VLeaf, CLeaf = CLeaf, ctr_wrapper = ctr_wrapper, friends = friends};

    val notes =
      [(corecUU_transferN, [corecUU_transfer])] @
      (if Config.get lthy bnf_internals then
         [(algLamN, [algLam_thm]),
          (algLam_algLamN, [algLam_algLam]),
          (algLam_algrhoN, [algLam_algrho]),
          (cong_alg_introsN, #cong_alg_intros dtor_coinduct_info),
          (cong_localeN, [#cong_locale dtor_coinduct_info]),
          (corecU_ctorN, [corecU_ctor]),
          (corecU_uniqueN, [corecU_unique]),
          (corecUUN, [corecUU_thm]),
          (corecUU_uniqueN, [corecUU_unique]),
          (dtor_algLamN, [dtor_algLam]),
          (dtor_algrhoN, [dtor_algrho]),
          (dtor_coinductN, [#dtor_coinduct dtor_coinduct_info]),
          (embL_pointful_naturalN, [embL_pointful_natural]),
          (embL_transferN, [embL_transfer]),
          (evalN, [eval_thm]),
          (eval_core_pointful_naturalN, [eval_core_pointful_natural]),
          (eval_core_transferN, [eval_core_transfer]),
          (eval_flatN, [eval_flat]),
          (eval_simpsN, eval_simps),
          (flat_pointful_naturalN, [flat_pointful_natural]),
          (flat_transferN, [flat_transfer]),
          (k_as_ssig_naturalN, [k_as_ssig_natural]),
          (k_as_ssig_transferN, [k_as_ssig_transfer]),
          (Lam_pointful_naturalN, [Lam_pointful_natural]),
          (Lam_transferN, [Lam_transfer]),
          (proto_sctr_pointful_naturalN, [proto_sctr_pointful_natural]),
          (proto_sctr_transferN, [proto_sctr_transfer]),
          (rho_transferN, [rho_transfer]),
          (sctr_pointful_naturalN, [sctr_pointful_natural]),
          (sctr_transferN, [sctr_transfer]),
          (Sig_pointful_naturalN, [Sig_pointful_natural])]
       else
         [])
      |> map (fn (thmN, thms) =>
        ((mk_version_fp_binding true lthy version fp_b thmN, []), [(thms, [])]));

    val phi = Local_Theory.target_morphism lthy;
  in
    (({fp_b = fp_b, version = version, fpT = fpT, Y = Y, Z = Z, friend_names = friend_names,
       sig_fp_sugars = sig_fp_sugar :: old_sig_fp_sugars, ssig_fp_sugar = ssig_fp_sugar, Lam = Lam,
       proto_sctr = proto_sctr, flat = flat, eval_core = eval_core, eval = eval, algLam = algLam,
       corecUU = corecUU, dtor_transfer = dtor_transfer, Lam_transfer = Lam_transfer,
       Lam_pointful_natural = Lam_pointful_natural, proto_sctr_transfer = proto_sctr_transfer,
       flat_simps = flat_simps, eval_core_simps = eval_core_simps, eval_thm = eval_thm,
       eval_simps = eval_simps, all_algLam_algs = all_algLam_algs, algLam_thm = algLam_thm,
       dtor_algLam = dtor_algLam, corecUU_thm = corecUU_thm, corecUU_unique = corecUU_unique,
       corecUU_transfer = corecUU_transfer, buffer = buffer,
       all_dead_k_bnfs = dead_k_bnf :: old_all_dead_k_bnfs, Retr = Retr, equivp_Retr = equivp_Retr,
       Retr_coinduct = Retr_coinduct, dtor_coinduct_info = dtor_coinduct_info}
      |> morph_corec_info phi,
      ({algrho = algrho, dtor_algrho = dtor_algrho, algLam_algrho = algLam_algrho}
       |> morph_friend_info phi)),
     lthy |> Local_Theory.notes notes |> snd)
  end;

fun derive_corecUU_merge (fpT as Type (fpT_name, res_Ds))
    ({friend_names = old1_friend_names,
      sig_fp_sugars = old1_sig_fp_sugars as old1_sig_fp_sugar :: _,
      ssig_fp_sugar = old1_ssig_fp_sugar, Lam = old1_Lam0, proto_sctr = old1_proto_sctr0,
      flat = old1_flat0, eval_core = old1_eval_core0, eval = old1_eval0, algLam = old1_algLam0,
      dtor_transfer, Lam_transfer = old1_Lam_transfer,
      Lam_pointful_natural = old1_Lam_pointful_natural,
      proto_sctr_transfer = old1_proto_sctr_transfer, flat_simps = old1_flat_simps,
      eval_core_simps = old1_eval_core_simps, eval_thm = old1_eval_thm,
      all_algLam_algs = old1_all_algLam_algs, algLam_thm = old1_algLam_thm,
      dtor_algLam = old1_dtor_algLam, buffer = old1_buffer, all_dead_k_bnfs = old1_all_dead_k_bnfs,
      Retr = old1_Retr0, equivp_Retr, Retr_coinduct, dtor_coinduct_info = old1_dtor_coinduct_info,
      ...} : corec_info)
    ({friend_names = old2_friend_names,
      sig_fp_sugars = old2_sig_fp_sugars as old2_sig_fp_sugar :: _,
      ssig_fp_sugar = old2_ssig_fp_sugar, Lam = old2_Lam0, flat = old2_flat0,
      eval_core = old2_eval_core0, eval = old2_eval0, algLam = old2_algLam0,
      Lam_transfer = old2_Lam_transfer, Lam_pointful_natural = old2_Lam_pointful_natural,
      flat_simps = old2_flat_simps, eval_core_simps = old2_eval_core_simps,
      eval_thm = old2_eval_thm, all_algLam_algs = old2_all_algLam_algs,
      algLam_thm = old2_algLam_thm, dtor_algLam = old2_dtor_algLam, buffer = old2_buffer,
      all_dead_k_bnfs = old2_all_dead_k_bnfs, dtor_coinduct_info = old2_dtor_coinduct_info, ...}
     : corec_info)
    lthy =
  let
    val {T = Type (_, fpT_args0), pre_bnf = live_pre_bnf, fp_bnf = live_fp_bnf, fp_res, ...} =
      checked_fp_sugar_of lthy fpT_name;
    val fpT_Ss = map Type.sort_of_atyp fpT_args0;
    val live_fp_alives = liveness_of_fp_bnf (length fpT_args0) live_fp_bnf;

    val ((Ds, [Y, Z]), names_lthy) = lthy
      |> mk_TFrees' fpT_Ss
      ||>> mk_TFrees 2;

    (* FIXME *)
    val live_EsFs = [];
    val live_AsBs = live_EsFs @ [(Y, Z)];
    val live = length live_EsFs;

    val ((((x, f), g), R), _) = names_lthy
      |> yield_singleton (mk_Frees "x") Y
      ||>> yield_singleton (mk_Frees "f") (Y --> Z)
      ||>> yield_singleton (mk_Frees "g") (Y --> Z)
      ||>> yield_singleton (mk_Frees "R") (mk_pred2T Y Z);

    (* FIXME *)
    val fs = [];
    val Rs = [];

    val ctor = mk_ctor res_Ds (the_single (#ctors fp_res));
    val dtor = mk_dtor res_Ds (the_single (#dtors fp_res));

    val old1_sig_T_name = fst (dest_Type (#T old1_sig_fp_sugar));
    val old2_sig_T_name = fst (dest_Type (#T old2_sig_fp_sugar));
    val old1_ssig_T_name = fst (dest_Type (#T old1_ssig_fp_sugar));
    val old2_ssig_T_name = fst (dest_Type (#T old2_ssig_fp_sugar));

    val fp_alives = map (K false) live_fp_alives;

    val As = Ds @ [Y];
    val res_As = res_Ds @ [Y];
    val res_Bs = res_Ds @ [Z];
    val preT = pre_type_of_ctor Y ctor;
    val YpreT = HOLogic.mk_prodT (Y, preT);
    val fpT0 = Type (fpT_name, Ds);
    val old1_sig_T0 = Type (old1_sig_T_name, As);
    val old2_sig_T0 = Type (old2_sig_T_name, As);
    val old1_sig_T = Type (old1_sig_T_name, res_As);
    val old2_sig_T = Type (old2_sig_T_name, res_As);
    val old1_ssig_T = Type (old1_ssig_T_name, res_As);
    val old2_ssig_T = Type (old2_ssig_T_name, res_As);
    val old1_Lam_domT = Tsubst Y YpreT old1_sig_T;
    val old2_Lam_domT = Tsubst Y YpreT old2_sig_T;
    val old1_eval_core_domT = Tsubst Y YpreT old1_ssig_T;
    val old2_eval_core_domT = Tsubst Y YpreT old2_ssig_T;

    val ((fp_b, version), lthy) = lthy |> get_name_next_version_of fpT_name;

    val ((sig_fp_sugar, ssig_fp_sugar), lthy) = lthy
      |> define_sig_type fp_b version fp_alives Ds Y (mk_sumT (old1_sig_T0, old2_sig_T0))
      ||>> define_ssig_type fp_b version fp_alives Ds Y fpT0;

    val sig_T_name = fst (dest_Type (#T sig_fp_sugar));
    val ssig_T_name = fst (dest_Type (#T ssig_fp_sugar));

    val old1_sig_bnf = #fp_bnf old1_sig_fp_sugar;
    val old2_sig_bnf = #fp_bnf old2_sig_fp_sugar;
    val old1_ssig_bnf = #fp_bnf old1_ssig_fp_sugar;
    val old2_ssig_bnf = #fp_bnf old2_ssig_fp_sugar;
    val sig_bnf = #fp_bnf sig_fp_sugar;
    val ssig_bnf = #fp_bnf ssig_fp_sugar;

    val ((((((((dead_pre_bnf, dead_fp_bnf), dead_old1_sig_bnf), dead_old2_sig_bnf),
        dead_old1_ssig_bnf), dead_old2_ssig_bnf), dead_sig_bnf), dead_ssig_bnf), lthy) = lthy
      |> bnf_kill_all_but 1 live_pre_bnf
      ||>> bnf_kill_all_but 0 live_fp_bnf
      ||>> bnf_kill_all_but 1 old1_sig_bnf
      ||>> bnf_kill_all_but 1 old2_sig_bnf
      ||>> bnf_kill_all_but 1 old1_ssig_bnf
      ||>> bnf_kill_all_but 1 old2_ssig_bnf
      ||>> bnf_kill_all_but 1 sig_bnf
      ||>> bnf_kill_all_but 1 ssig_bnf;

    (* FIXME *)
    val pre_bnf = dead_pre_bnf;
    val fp_bnf = dead_fp_bnf;

    val old1_ssig_fp_ctr_sugar = #fp_ctr_sugar old1_ssig_fp_sugar;
    val old2_ssig_fp_ctr_sugar = #fp_ctr_sugar old2_ssig_fp_sugar;
    val sig_fp_ctr_sugar = #fp_ctr_sugar sig_fp_sugar;
    val ssig_fp_ctr_sugar = #fp_ctr_sugar ssig_fp_sugar;

    val sig_fp_bnf_sugar = #fp_bnf_sugar sig_fp_sugar;
    val old1_ssig_fp_bnf_sugar = #fp_bnf_sugar old1_ssig_fp_sugar;
    val old2_ssig_fp_bnf_sugar = #fp_bnf_sugar old2_ssig_fp_sugar;
    val ssig_fp_bnf_sugar = #fp_bnf_sugar ssig_fp_sugar;
    val old1_ssig_fp_induct_sugar = the (#fp_co_induct_sugar old1_ssig_fp_sugar);
    val old2_ssig_fp_induct_sugar = the (#fp_co_induct_sugar old2_ssig_fp_sugar);
    val ssig_fp_induct_sugar = the (#fp_co_induct_sugar ssig_fp_sugar);

    val old1_ssig_ctr_sugar = #ctr_sugar old1_ssig_fp_ctr_sugar;
    val old2_ssig_ctr_sugar = #ctr_sugar old2_ssig_fp_ctr_sugar;
    val sig_ctr_sugar = #ctr_sugar sig_fp_ctr_sugar;
    val ssig_ctr_sugar = #ctr_sugar ssig_fp_ctr_sugar;

    val sig_T = Type (sig_T_name, res_As);
    val ssig_T = Type (ssig_T_name, res_As);

    val pre_map = mk_mapN lthy live_AsBs preT pre_bnf;
    val pre_rel = mk_relN lthy live_AsBs preT pre_bnf;
    val dead_pre_map = mk_map1 lthy Y Z preT dead_pre_bnf;
    val dead_pre_rel = mk_rel1 lthy Y Z preT dead_pre_bnf;
    val fp_rel = mk_relN lthy live_EsFs fpT fp_bnf;
    val dtor_unfold = mk_co_rec (Proof_Context.theory_of lthy) Greatest_FP [Z] fpT
      (the_single (#xtor_un_folds fp_res));
    val Sig = mk_ctr res_As (the_single (#ctrs sig_ctr_sugar));
    val unsig = mk_disc_or_sel res_As (the_single (the_single (#selss sig_ctr_sugar)));
    val sig_rel = mk_relN lthy live_AsBs sig_T sig_bnf;
    val dead_old1_sig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_old1_sig_bnf);
    val dead_old2_sig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_old2_sig_bnf);
    val dead_sig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_sig_bnf);
    val dead_sig_rel = mk_rel 1 res_As res_Bs (rel_of_bnf dead_sig_bnf);
    val [old1_Oper, old1_VLeaf, old1_CLeaf] = map (mk_ctr res_As) (#ctrs old1_ssig_ctr_sugar);
    val [old2_Oper, old2_VLeaf, old2_CLeaf] = map (mk_ctr res_As) (#ctrs old2_ssig_ctr_sugar);
    val [Oper, VLeaf, CLeaf] = map (mk_ctr res_As) (#ctrs ssig_ctr_sugar);
    val old1_ssig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_old1_ssig_bnf);
    val old2_ssig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_old2_ssig_bnf);
    val ssig_map = mk_mapN lthy live_AsBs ssig_T ssig_bnf;
    val ssig_rel = mk_relN lthy live_AsBs ssig_T ssig_bnf;
    val dead_ssig_map = mk_map 1 res_As res_Bs (map_of_bnf dead_ssig_bnf);
    val old1_Lam = enforce_type lthy domain_type old1_Lam_domT old1_Lam0;
    val old2_Lam = enforce_type lthy domain_type old2_Lam_domT old2_Lam0;
    val old1_proto_sctr = enforce_type lthy domain_type preT old1_proto_sctr0;
    val old1_flat = enforce_type lthy range_type old1_ssig_T old1_flat0;
    val old2_flat = enforce_type lthy range_type old2_ssig_T old2_flat0;
    val old1_eval_core = enforce_type lthy domain_type old1_eval_core_domT old1_eval_core0;
    val old2_eval_core = enforce_type lthy domain_type old2_eval_core_domT old2_eval_core0;
    val old1_eval = enforce_type lthy range_type fpT old1_eval0;
    val old2_eval = enforce_type lthy range_type fpT old2_eval0;
    val old1_algLam = enforce_type lthy range_type fpT old1_algLam0;
    val old2_algLam = enforce_type lthy range_type fpT old2_algLam0;

    val ((embLL, embLL_def, embLL_simps), lthy) = lthy
      |> define_embL embLLN fp_b version Y Z fpT old1_sig_T old1_ssig_T old2_sig_T ssig_T Inl_const
        dead_old1_sig_map Sig old1_Oper old1_VLeaf old1_CLeaf Oper VLeaf CLeaf;

    val ((embLR, embLR_def, embLR_simps), lthy) = lthy
      |> define_embL embLRN fp_b version Y Z fpT old2_sig_T old2_ssig_T old1_sig_T ssig_T
        (fn T => fn U => Inr_const U T) dead_old2_sig_map Sig old2_Oper old2_VLeaf old2_CLeaf Oper
        VLeaf CLeaf;

    val ((Lam, Lam_def), lthy) = lthy
      |> define_Lam_merge fp_b version Y Z preT old1_ssig_T old2_ssig_T ssig_T dead_pre_map unsig
        embLL embLR old1_Lam old2_Lam;

    val ((proto_sctr, proto_sctr_def), lthy) = lthy
      |> define_proto_sctr_step_or_merge fp_b version old1_sig_T old2_sig_T Sig old1_proto_sctr;

    val pre_map_transfer = map_transfer_of_bnf pre_bnf;
    val dead_pre_map_comp0 = map_comp0_of_bnf dead_pre_bnf;
    val dead_pre_map_comp = map_comp_of_bnf dead_pre_bnf;
    val fp_map_id = map_id_of_bnf fp_bnf;
    val fp_rel_eq = rel_eq_of_bnf fp_bnf;
    val [ctor_dtor] = #ctor_dtors fp_res;
    val [dtor_inject] = #dtor_injects fp_res;
    val [dtor_unfold_thm] = #xtor_un_fold_thms fp_res;
    val dtor_unfold_unique = #xtor_un_fold_unique fp_res;
    val [dtor_unfold_transfer] = #xtor_un_fold_transfers fp_res;
    val unsig_thm = the_single (the_single (#sel_thmss sig_ctr_sugar));
    val [sig_map_thm] = #map_thms sig_fp_bnf_sugar;
    val old1_sig_map_comp = map_comp_of_bnf old1_sig_bnf;
    val old2_sig_map_comp = map_comp_of_bnf old2_sig_bnf;
    val old1_sig_map_cong = map_cong_of_bnf old1_sig_bnf;
    val old2_sig_map_cong = map_cong_of_bnf old2_sig_bnf;
    val old1_ssig_map_thms = #map_thms old1_ssig_fp_bnf_sugar;
    val old2_ssig_map_thms = #map_thms old2_ssig_fp_bnf_sugar;
    val [Oper_map_thm, VLeaf_map_thm, CLeaf_map_thm] = #map_thms ssig_fp_bnf_sugar;
    val old1_sig_map_transfer = map_transfer_of_bnf old1_sig_bnf;
    val old2_sig_map_transfer = map_transfer_of_bnf old2_sig_bnf;
    val sig_map_transfer = map_transfer_of_bnf sig_bnf;
    val ssig_map_thms = #map_thms ssig_fp_bnf_sugar;
    val ssig_map_transfer = map_transfer_of_bnf ssig_bnf;
    val old1_ssig_induct = the_single (#co_inducts old1_ssig_fp_induct_sugar);
    val old2_ssig_induct = the_single (#co_inducts old2_ssig_fp_induct_sugar);
    val ssig_induct = the_single (#co_inducts ssig_fp_induct_sugar);

    val proto_sctr_transfer = derive_proto_sctr_transfer_step_or_merge lthy Y Z R dead_pre_rel
      dead_sig_rel proto_sctr proto_sctr_def [] [old1_proto_sctr_transfer];
    val embLL_transfer = derive_transfer_by_transfer_prover lthy live_AsBs Rs R embLL [embLL_def] []
      [old1_sig_map_transfer];
    val embLR_transfer = derive_transfer_by_transfer_prover lthy live_AsBs Rs R embLR [embLR_def] []
      [old2_sig_map_transfer];
    val Lam_transfer = derive_Lam_or_eval_core_transfer lthy live_AsBs Y Z preT ssig_T Rs R
      pre_rel sig_rel ssig_rel Lam Lam_def []
      [pre_map_transfer, old1_Lam_transfer, old2_Lam_transfer, embLL_transfer, embLR_transfer];

    val ((((((((flat, _, flat_simps), flat_transfer),
            ((eval_core, _, eval_core_simps), eval_core_transfer)), (eval, eval_def)),
          (cutSsig, cutSsig_def)), (algLam, algLam_def)), (corecU, corecU_def)), lthy) = lthy
      |> define_flat_etc fp_b version live_AsBs Y Z preT fpT sig_T ssig_T Oper VLeaf CLeaf pre_rel
        dead_pre_map dtor dtor_unfold dead_sig_map ssig_rel dead_ssig_map Lam Rs R pre_map_transfer
        [fp_rel_eq] sig_map_transfer ssig_map_transfer Lam_transfer dtor_transfer;

    val (Sig_pointful_natural, flat_pointful_natural, _, Lam_pointful_natural, _,
         eval_core_pointful_natural, eval_thm, eval_flat, eval_simps as [eval_Oper, _, _],
         corecU_ctor, corecU_unique, dtor_algLam) =
      derive_Sig_natural_etc lthy live live_AsBs Y Z preT fpT fpT sig_T ssig_T pre_map dead_pre_map
        ctor dtor Sig dead_sig_map Oper VLeaf CLeaf ssig_map dead_ssig_map Lam flat eval_core eval
        cutSsig algLam corecU x fs f g ctor_dtor dtor_inject dtor_unfold_thm dtor_unfold_unique
        sig_map_thm ssig_induct ssig_map_thms Oper_map_thm VLeaf_map_thm CLeaf_map_thm Lam_transfer
        flat_simps flat_transfer eval_core_simps eval_core_transfer eval_def cutSsig_def algLam_def
        corecU_def live_pre_bnf pre_bnf dead_pre_bnf fp_bnf sig_bnf ssig_bnf dead_ssig_bnf;

    val proto_sctr_natural = derive_natural_from_transfer_with_pre_type lthy live_AsBs Y Z preT
      ssig_T pre_map ssig_map fs f proto_sctr proto_sctr_transfer [pre_bnf, sig_bnf] [];
    val proto_sctr_pointful_natural = mk_pointful lthy proto_sctr_natural RS sym;

    val (embLL_pointful_natural, old1_algLam_pointful, eval_embLL, algLam_algLamL) =
      derive_embL_natural_etc lthy Inl_const old1_ssig_bnf ssig_bnf Y Z preT fpT old1_ssig_T ssig_T
        dead_pre_map Sig old1_ssig_map embLL old1_algLam algLam old1_flat flat old1_eval_core
        eval_core old1_eval eval x f old1_ssig_induct dead_pre_map_comp0 dead_pre_map_comp fp_map_id
        dtor_inject dtor_unfold_unique Sig_pointful_natural unsig_thm sig_map_thm old1_sig_map_comp
        old1_sig_map_cong old1_ssig_map_thms old1_Lam_pointful_natural Lam_def old1_flat_simps
        flat_simps embLL_simps embLL_transfer old1_eval_core_simps eval_core_simps old1_eval_thm
        eval_thm old1_dtor_algLam dtor_algLam old1_algLam_thm;

    val (embLR_pointful_natural, _, eval_embLR, algLam_algLamR) =
      derive_embL_natural_etc lthy Inr_const old2_ssig_bnf ssig_bnf Y Z preT fpT old2_ssig_T ssig_T
        dead_pre_map Sig old2_ssig_map embLR old2_algLam algLam old2_flat flat old2_eval_core
        eval_core old2_eval eval x f old2_ssig_induct dead_pre_map_comp0 dead_pre_map_comp fp_map_id
        dtor_inject dtor_unfold_unique Sig_pointful_natural unsig_thm sig_map_thm old2_sig_map_comp
        old2_sig_map_cong old2_ssig_map_thms old2_Lam_pointful_natural Lam_def old2_flat_simps
        flat_simps embLR_simps embLR_transfer old2_eval_core_simps eval_core_simps old2_eval_thm
        eval_thm old2_dtor_algLam dtor_algLam old2_algLam_thm;

    val algLam_thm = derive_algLam_step_or_merge lthy Y fpT ctor proto_sctr algLam proto_sctr_def
      old1_algLam_pointful algLam_algLamL;

    val all_algLam_algs = algLam_algLamL :: algLam_algLamR ::
      merge_lists (Thm.eq_thm_prop o apply2 zero_var_indexes) old1_all_algLam_algs
        old2_all_algLam_algs;

    val (((corecUU, _), corecUU_thm, corecUU_unique, corecUU_transfer, _, sctr_transfer,
          sctr_pointful_natural), lthy) = lthy
      |> define_corecUU_etc fp_b version live_AsBs Y Z preT fpT ssig_T pre_map dead_pre_map pre_rel
        fp_rel ctor Oper ssig_map dead_ssig_map ssig_rel proto_sctr flat eval_core eval corecU fs f
        g Rs R pre_map_transfer [] dtor_unfold_transfer dtor_transfer ssig_map_transfer
        proto_sctr_transfer proto_sctr_pointful_natural flat_transfer flat_pointful_natural
        eval_core_transfer eval_core_pointful_natural eval_thm eval_flat eval_Oper algLam_thm
        cutSsig_def corecU_def corecU_ctor corecU_unique pre_bnf dead_pre_bnf fp_res ssig_fp_sugar;

    val Retr = enforce_type lthy (domain_type o domain_type) fpT old1_Retr0;

    val embed_Sig_inl = embed_Sig lthy Sig (Inl_const old1_sig_T old2_sig_T);
    val embed_Sig_inr = embed_Sig lthy Sig (Inr_const old1_sig_T old2_sig_T);

    val ctr_wrapper = embed_Sig_inl (#ctr_wrapper old1_buffer);
    val friends = Symtab.merge (K true)
      (Symtab.map (K (apsnd embed_Sig_inl)) (#friends old1_buffer),
       Symtab.map (K (apsnd embed_Sig_inr)) (#friends old2_buffer));

    val old_fp_sugars =
      merge_lists (op = o apply2 (fst o dest_Type o #T)) old1_sig_fp_sugars old2_sig_fp_sugars;

    val ((dtor_coinduct_info, all_dead_k_bnfs, friend_names), lthy) = lthy
      |> derive_cong_merge fp_b version fpT old1_friend_names old2_friend_names dead_ssig_bnf
        dead_pre_bnf eval eval_thm eval_core_transfer old1_dtor_coinduct_info
        old2_dtor_coinduct_info Retr equivp_Retr Retr_coinduct eval_embLL embLL_transfer eval_embLR
        embLR_transfer old1_all_dead_k_bnfs old2_all_dead_k_bnfs;

    val buffer =
      {Oper = Oper, VLeaf = VLeaf, CLeaf = CLeaf, ctr_wrapper = ctr_wrapper, friends = friends};

    val notes =
      [(corecUU_transferN, [corecUU_transfer])] @
      (if Config.get lthy bnf_internals then
         [(algLamN, [algLam_thm]),
          (algLam_algLamN, [algLam_algLamL, algLam_algLamR]),
          (cong_alg_introsN, #cong_alg_intros dtor_coinduct_info),
          (cong_localeN, [#cong_locale dtor_coinduct_info]),
          (corecU_ctorN, [corecU_ctor]),
          (corecU_uniqueN, [corecU_unique]),
          (corecUUN, [corecUU_thm]),
          (corecUU_uniqueN, [corecUU_unique]),
          (dtor_algLamN, [dtor_algLam]),
          (dtor_coinductN, [#dtor_coinduct dtor_coinduct_info]),
          (eval_core_pointful_naturalN, [eval_core_pointful_natural]),
          (eval_core_transferN, [eval_core_transfer]),
          (embL_pointful_naturalN, [embLL_pointful_natural, embLR_pointful_natural]),
          (embL_transferN, [embLL_transfer, embLR_transfer]),
          (evalN, [eval_thm]),
          (eval_flatN, [eval_flat]),
          (eval_simpsN, eval_simps),
          (flat_pointful_naturalN, [flat_pointful_natural]),
          (flat_transferN, [flat_transfer]),
          (Lam_pointful_naturalN, [Lam_pointful_natural]),
          (Lam_transferN, [Lam_transfer]),
          (proto_sctr_pointful_naturalN, [proto_sctr_pointful_natural]),
          (proto_sctr_transferN, [proto_sctr_transfer]),
          (sctr_pointful_naturalN, [sctr_pointful_natural]),
          (sctr_transferN, [sctr_transfer]),
          (Sig_pointful_naturalN, [Sig_pointful_natural])]
       else
         [])
      |> map (fn (thmN, thms) =>
        ((mk_version_fp_binding true lthy version fp_b thmN, []), [(thms, [])]));
  in
    ({fp_b = fp_b, version = version, fpT = fpT, Y = Y, Z = Z, friend_names = friend_names,
      sig_fp_sugars = sig_fp_sugar :: old_fp_sugars, ssig_fp_sugar = ssig_fp_sugar, Lam = Lam,
      proto_sctr = proto_sctr, flat = flat, eval_core = eval_core, eval = eval, algLam = algLam,
      corecUU = corecUU, dtor_transfer = dtor_transfer, Lam_transfer = Lam_transfer,
      Lam_pointful_natural = Lam_pointful_natural, proto_sctr_transfer = proto_sctr_transfer,
      flat_simps = flat_simps, eval_core_simps = eval_core_simps, eval_thm = eval_thm,
      eval_simps = eval_simps, all_algLam_algs = all_algLam_algs, algLam_thm = algLam_thm,
      dtor_algLam = dtor_algLam, corecUU_thm = corecUU_thm, corecUU_unique = corecUU_unique,
      corecUU_transfer = corecUU_transfer, buffer = buffer, all_dead_k_bnfs = all_dead_k_bnfs,
      Retr = Retr, equivp_Retr = equivp_Retr, Retr_coinduct = Retr_coinduct,
      dtor_coinduct_info = dtor_coinduct_info}
     |> morph_corec_info (Local_Theory.target_morphism lthy),
     lthy |> Local_Theory.notes notes |> snd)
  end;

fun set_corec_info_exprs fpT_name f =
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    let val exprs = f phi in
      Data.map (apsnd (fn [info_tab] => [Symtab.map_default (fpT_name, exprs) (K exprs) info_tab]))
    end);

fun subsume_corec_info_ad ctxt {fpT = fpT1, friend_names = friend_names1}
    {fpT = fpT2, friend_names = friend_names2} =
  Sign.typ_instance (Proof_Context.theory_of ctxt) (fpT1, fpT2) andalso
  subset (op =) (friend_names1, friend_names2);

fun subsume_corec_info_expr ctxt expr1 expr2 =
  subsume_corec_info_ad ctxt (corec_ad_of_expr expr1) (corec_ad_of_expr expr2);

fun instantiate_corec_info thy res_T (info as {fpT, ...}) =
  let
    val As_rho = tvar_subst thy [fpT] [res_T];
    val substAT = Term.typ_subst_TVars As_rho;
    val substA = Term.subst_TVars As_rho;
    val phi = Morphism.typ_morphism "BNF" substAT $> Morphism.term_morphism "BNF" substA;
  in
    morph_corec_info phi info
  end;

fun instantiate_corec_info_expr thy res_T (Ad ({friend_names, ...}, f)) =
    Ad ({fpT = res_T, friend_names = friend_names}, f #>> instantiate_corec_info thy res_T)
  | instantiate_corec_info_expr thy res_T (Info info) =
    Info (instantiate_corec_info thy res_T info);

fun ensure_Info expr = corec_info_of_expr expr #>> Info
and ensure_Info_if_Info old_expr (expr, lthy) =
  if is_Info old_expr then ensure_Info expr lthy else (expr, lthy)
and merge_corec_info_exprs old_exprs expr1 expr2 lthy =
  if subsume_corec_info_expr lthy expr2 expr1 then
    if subsume_corec_info_expr lthy expr1 expr2 andalso is_Ad expr1 then
      (expr2, lthy)
    else
      ensure_Info_if_Info expr2 (expr1, lthy)
  else if subsume_corec_info_expr lthy expr1 expr2 then
    ensure_Info_if_Info expr1 (expr2, lthy)
  else
    let
      val thy = Proof_Context.theory_of lthy;

      val {fpT = fpT1, friend_names = friend_names1} = corec_ad_of_expr expr1;
      val {fpT = fpT2, friend_names = friend_names2} = corec_ad_of_expr expr2;
      val fpT0 = typ_unify_disjointly thy (fpT1, fpT2);

      val fpT = singleton (freeze_types lthy []) fpT0;
      val friend_names = merge_lists (op =) friend_names1 friend_names2;

      val expr =
        Ad ({fpT = fpT, friend_names = friend_names},
          corec_info_of_expr expr1
          ##>> corec_info_of_expr expr2
          #-> uncurry (derive_corecUU_merge fpT));

      val old_same_type_exprs =
        if old_exprs then
          []
          |> Sign.typ_instance thy (fpT1, fpT0) ? cons expr1
          |> Sign.typ_instance thy (fpT2, fpT0) ? cons expr2
        else
          [];
    in
      (expr, lthy) |> fold ensure_Info_if_Info old_same_type_exprs
    end
and insert_corec_info_expr expr exprs lthy =
  let
    val thy = Proof_Context.theory_of lthy;

    val {fpT = new_fpT, ...} = corec_ad_of_expr expr;

    val is_Tinst = curry (Sign.typ_instance thy);
    fun is_Tequiv T U = is_Tinst T U andalso is_Tinst U T;

    val (((equiv_exprs, sub_exprs), sup_exprs), incomp_exprs) = exprs
      |> List.partition ((fn {fpT, ...} => is_Tequiv fpT new_fpT) o corec_ad_of_expr)
      ||>> List.partition ((fn {fpT, ...} => is_Tinst fpT new_fpT) o corec_ad_of_expr)
      ||>> List.partition ((fn {fpT, ...} => is_Tinst new_fpT fpT) o corec_ad_of_expr);

    fun add_instantiated_incomp_expr expr exprs =
      let val {fpT, ...} = corec_ad_of_expr expr in
        (case try (typ_unify_disjointly thy) (fpT, new_fpT) of
          SOME new_T =>
          let val subsumes = (fn {fpT, ...} => is_Tinst new_T fpT) o corec_ad_of_expr in
            if exists (exists subsumes) [exprs, sub_exprs] then exprs
            else instantiate_corec_info_expr thy new_T expr :: exprs
          end
        | NONE => exprs)
      end;

    val unincomp_exprs = fold add_instantiated_incomp_expr incomp_exprs [];
    val ((merged_sub_exprs, merged_unincomp_exprs), lthy) = lthy
      |> fold_map (merge_corec_info_exprs true expr) sub_exprs
      ||>> fold_map (merge_corec_info_exprs false expr) unincomp_exprs;
    val (merged_equiv_expr, lthy) = (expr, lthy)
      |> fold (uncurry o merge_corec_info_exprs true) equiv_exprs;
  in
    (merged_unincomp_exprs @ merged_sub_exprs @ merged_equiv_expr :: sup_exprs @ incomp_exprs
     |> sort (rev_order o int_ord o apply2 (length o #friend_names o corec_ad_of_expr)),
     lthy)
  end
and register_corec_info (info as {fpT = Type (fpT_name, _), ...}) lthy =
  let
    val (exprs, lthy) = insert_corec_info_expr (Info info) (corec_info_exprs_of lthy fpT_name) lthy;
  in
    lthy |> set_corec_info_exprs fpT_name (fn phi => map (morph_corec_info_expr phi) exprs)
  end
and corec_info_of_expr (Ad (_, f)) lthy = f lthy
  | corec_info_of_expr (Info info) lthy = (info, lthy);

fun nonempty_corec_info_exprs_of fpT_name lthy =
  (case corec_info_exprs_of lthy fpT_name of
    [] =>
    derive_corecUU_base fpT_name lthy
    |> (fn (info, lthy) =>
      ([Info info], lthy
         |> set_corec_info_exprs fpT_name (fn phi => [Info (morph_corec_info phi info)])))
  | exprs => (exprs, lthy));

fun corec_info_of res_T lthy =
  (case res_T of
    Type (fpT_name, _) =>
    let
      val (exprs, lthy) = nonempty_corec_info_exprs_of fpT_name lthy;
      val thy = Proof_Context.theory_of lthy;
      val expr =
        (case find_first ((fn {fpT, ...} => Sign.typ_instance thy (res_T, fpT)) o corec_ad_of_expr)
            exprs of
          SOME expr => expr
        | NONE => error ("Invalid type: " ^ Syntax.string_of_typ lthy res_T));
      val (info, lthy) = corec_info_of_expr expr lthy;
    in
      (instantiate_corec_info thy res_T info, lthy |> is_Ad expr ? register_corec_info info)
    end
  | _ => not_codatatype lthy res_T);

fun maybe_corec_info_of ctxt res_T =
  (case res_T of
    Type (fpT_name, _) =>
    let
      val thy = Proof_Context.theory_of ctxt;
      val infos = corec_infos_of ctxt fpT_name;
    in
      find_first (fn {fpT, ...} => Sign.typ_instance thy (res_T, fpT)) infos
      |> Option.map (instantiate_corec_info thy res_T)
    end
  | _ => not_codatatype ctxt res_T);

fun prepare_friend_corec friend_name friend_T lthy =
  let
    val (arg_Ts, res_T) = strip_type friend_T;
    val Type (fpT_name, res_Ds) =
      (case res_T of
        T as Type _ => T
      | T => error (not_codatatype lthy T));

    val _ = not (null arg_Ts) orelse
      error "Function with no argument cannot be registered as friend";

    val {T = Type (fpT_name, fpT_args0), pre_bnf, fp_bnf = live_fp_bnf, fp_res, ...} =
      checked_fp_sugar_of lthy fpT_name;
    val num_fp_tyargs = length fpT_args0;
    val fpT_Ss = map Type.sort_of_atyp fpT_args0;
    val live_fp_alives = liveness_of_fp_bnf num_fp_tyargs live_fp_bnf;

    val (old_info as {friend_names = old_friend_names, sig_fp_sugars = old_sig_fp_sugar :: _,
           buffer = old_buffer, ...}, lthy) =
      corec_info_of res_T lthy;
    val old_sig_T_name = fst (dest_Type (#T old_sig_fp_sugar));
    val old_sig_alives = liveness_of_fp_bnf (num_fp_tyargs + 1) (#fp_bnf old_sig_fp_sugar);

    (* FIXME: later *)
    val fp_alives = fst (split_last old_sig_alives);
    val fp_alives = map (K false) live_fp_alives;

    val _ = not (member (op =) old_friend_names friend_name) orelse
      error ("Function " ^ quote (Syntax.string_of_term lthy (Const (friend_name, friend_T))) ^
        " already registered as friend");

    val lthy = lthy |> Variable.declare_typ friend_T;
    val ((Ds, [Y, Z]), _) = lthy
      |> mk_TFrees' fpT_Ss
      ||>> mk_TFrees 2;

    (* FIXME *)
    val dead_Ds = Ds;
    val live_As = [Y];

    val ctor = mk_ctor res_Ds (the_single (#ctors fp_res));

    val fpT0 = Type (fpT_name, Ds);
    val k_Ts0 = map (typ_subst_nonatomic (res_Ds ~~ Ds) o typ_subst_nonatomic [(res_T, Y)]) arg_Ts;
    val k_T0 = mk_tupleT_balanced k_Ts0;

    val As = Ds @ [Y];
    val res_As = res_Ds @ [Y];

    val k_As = fold Term.add_tfreesT k_Ts0 [];
    val _ = (case filter_out (member (op =) As o TFree) k_As of [] => ()
      | k_A :: _ => error ("Cannot have type variable " ^
          quote (Syntax.string_of_typ lthy (TFree k_A)) ^
          " in the argument types when it does not occur as an immediate argument of the result \
          \type constructor"));

    val substDT = Term.typ_subst_atomic (Ds ~~ res_Ds);

    val old_sig_T0 = Type (old_sig_T_name, As);

    val ((fp_b, version), lthy) = lthy |> get_name_next_version_of fpT_name;

    val (((dead_k_bnf, sig_fp_sugar), ssig_fp_sugar), lthy) = lthy
      |> bnf_with_deads_and_lives dead_Ds live_As Y fpT0 k_T0
      ||>> define_sig_type fp_b version fp_alives Ds Y (mk_sumT (old_sig_T0, k_T0))
      ||>> define_ssig_type fp_b version fp_alives Ds Y fpT0;

    val _ = live_of_bnf dead_k_bnf = 1 orelse
      error "Impossible type for friend (the result codatatype must occur live in the arguments)";

    val (dead_pre_bnf, lthy) = lthy
      |> bnf_kill_all_but 1 pre_bnf;

    val sig_fp_ctr_sugar = #fp_ctr_sugar sig_fp_sugar;
    val ssig_fp_ctr_sugar = #fp_ctr_sugar ssig_fp_sugar;

    val sig_ctr_sugar = #ctr_sugar sig_fp_ctr_sugar;
    val ssig_ctr_sugar = #ctr_sugar ssig_fp_ctr_sugar;

    val ssig_T_name = fst (dest_Type (#T ssig_fp_sugar));

    val preT = pre_type_of_ctor Y ctor;
    val old_sig_T = substDT old_sig_T0;
    val k_T = substDT k_T0;
    val ssig_T = Type (ssig_T_name, res_As);

    val Sig = mk_ctr res_As (the_single (#ctrs sig_ctr_sugar));

    val [Oper, VLeaf, CLeaf] = map (mk_ctr res_As) (#ctrs ssig_ctr_sugar);
    val (ctr_wrapper, friends) =
      mk_ctr_wrapper_friends lthy friend_name friend_T old_sig_T k_T Sig old_buffer;

    val buffer =
      {Oper = Oper, VLeaf = VLeaf, CLeaf = CLeaf, ctr_wrapper = ctr_wrapper, friends = friends};
  in
    ((old_info, fp_b, version, Y, Z, preT, k_T, ssig_T, dead_pre_bnf, dead_k_bnf, sig_fp_sugar,
      ssig_fp_sugar, buffer), lthy)
  end;

fun register_friend_corec key fp_b version Y Z k_T dead_k_bnf sig_fp_sugar ssig_fp_sugar
    friend_const rho rho_transfer old_info lthy =
  let
    val friend_T = fastype_of friend_const;
    val res_T = body_type friend_T;
  in
    derive_corecUU_step res_T old_info key friend_T fp_b version Y Z k_T dead_k_bnf sig_fp_sugar
      ssig_fp_sugar rho rho_transfer lthy
    |> (fn ((info, friend_info), lthy) => (friend_info, register_corec_info info lthy))
  end;

fun merge_corec_info_exprss exprs1 exprs2 lthy =
  let
    fun all_friend_names_of exprs =
      fold (union (op =)) (map (#friend_names o corec_ad_of_expr) exprs) [];

    val friend_names1 = all_friend_names_of exprs1;
    val friend_names2 = all_friend_names_of exprs2;
  in
    if subset (op =) (friend_names2, friend_names1) then
      if subset (op =) (friend_names1, friend_names2) andalso
         length (filter is_Info exprs2) > length (filter is_Info exprs1) then
        (exprs2, lthy)
      else
        (exprs1, lthy)
    else if subset (op =) (friend_names1, friend_names2) then
      (exprs2, lthy)
    else
      fold_rev (uncurry o insert_corec_info_expr) exprs2 (exprs1, lthy)
  end;

fun merge_corec_info_tabs info_tab1 info_tab2 lthy =
  let
    val fpT_names = union (op =) (Symtab.keys info_tab1) (Symtab.keys info_tab2);

    fun add_infos_of fpT_name (info_tab, lthy) =
      (case Symtab.lookup info_tab1 fpT_name of
        NONE =>
        (Symtab.update_new (fpT_name, the (Symtab.lookup info_tab2 fpT_name)) info_tab, lthy)
      | SOME exprs1 =>
        (case Symtab.lookup info_tab2 fpT_name of
          NONE => (Symtab.update_new (fpT_name, exprs1) info_tab, lthy)
        | SOME exprs2 =>
          let val (exprs, lthy) = merge_corec_info_exprss exprs1 exprs2 lthy in
            (Symtab.update_new (fpT_name, exprs) info_tab, lthy)
          end));
  in
    fold add_infos_of fpT_names (Symtab.empty, lthy)
  end;

fun consolidate lthy =
  (case snd (Data.get (Context.Proof lthy)) of
    [_] => raise Same.SAME
  | info_tab :: info_tabs =>
    let
      val (info_tab', lthy) = fold_rev (uncurry o merge_corec_info_tabs) info_tabs (info_tab, lthy);
    in
      Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
          Data.map (apsnd (fn _ => [Symtab.map (K (map (morph_corec_info_expr phi))) info_tab'])))
        lthy
    end);

fun consolidate_global thy =
  SOME (Named_Target.theory_map consolidate thy)
  handle Same.SAME => NONE;

val _ = Theory.setup (Theory.at_begin consolidate_global);

end;
