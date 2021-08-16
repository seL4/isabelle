(*  Title:      HOL/Tools/Lifting/lifting_info.ML
    Author:     Ondrej Kuncar

Context data for the lifting package.
*)

signature LIFTING_INFO =
sig
  type quot_map = {rel_quot_thm: thm}
  val lookup_quot_maps: Proof.context -> string -> quot_map option
  val print_quot_maps: Proof.context -> unit

  type pcr = {pcrel_def: thm, pcr_cr_eq: thm}
  type quotient = {quot_thm: thm, pcr_info: pcr option}
  val pcr_eq: pcr * pcr -> bool
  val quotient_eq: quotient * quotient -> bool
  val transform_quotient: morphism -> quotient -> quotient
  val lookup_quotients: Proof.context -> string -> quotient option
  val lookup_quot_thm_quotients: Proof.context -> thm -> quotient option
  val update_quotients: string -> quotient -> Context.generic -> Context.generic
  val delete_quotients: thm -> Context.generic -> Context.generic
  val print_quotients: Proof.context -> unit

  type restore_data = {quotient : quotient, transfer_rules: thm Item_Net.T}
  val lookup_restore_data: Proof.context -> string -> restore_data option
  val init_restore_data: string -> quotient -> Context.generic -> Context.generic
  val add_transfer_rules_in_restore_data: string -> thm Item_Net.T -> Context.generic -> Context.generic

  val get_relator_eq_onp_rules: Proof.context -> thm list

  val get_reflexivity_rules: Proof.context -> thm list
  val add_reflexivity_rule_attribute: attribute

  type relator_distr_data = {pos_mono_rule: thm, neg_mono_rule: thm,
    pos_distr_rules: thm list, neg_distr_rules: thm list}
  val lookup_relator_distr_data: Proof.context -> string -> relator_distr_data option

  val add_no_code_type: string -> Context.generic -> Context.generic
  val is_no_code_type: Proof.context -> string -> bool

  val get_quot_maps           : Proof.context -> quot_map Symtab.table
  val get_quotients           : Proof.context -> quotient Symtab.table
  val get_relator_distr_data  : Proof.context -> relator_distr_data Symtab.table
  val get_restore_data        : Proof.context -> restore_data Symtab.table
  val get_no_code_types       : Proof.context -> unit Symtab.table
end

structure Lifting_Info: LIFTING_INFO =
struct

open Lifting_Util


(* context data *)

type quot_map = {rel_quot_thm: thm}
type pcr = {pcrel_def: thm, pcr_cr_eq: thm}
type quotient = {quot_thm: thm, pcr_info: pcr option}
type relator_distr_data = {pos_mono_rule: thm, neg_mono_rule: thm,
  pos_distr_rules: thm list, neg_distr_rules: thm list}
type restore_data = {quotient : quotient, transfer_rules: thm Item_Net.T}

fun pcr_eq ({pcrel_def = pcrel_def1, pcr_cr_eq = pcr_cr_eq1},
           {pcrel_def = pcrel_def2, pcr_cr_eq = pcr_cr_eq2}) =
           Thm.eq_thm (pcrel_def1, pcrel_def2) andalso Thm.eq_thm (pcr_cr_eq1, pcr_cr_eq2)

fun quotient_eq ({quot_thm = quot_thm1, pcr_info = pcr_info1},
                {quot_thm = quot_thm2, pcr_info = pcr_info2}) =
                Thm.eq_thm (quot_thm1, quot_thm2) andalso eq_option pcr_eq (pcr_info1, pcr_info2)

fun join_restore_data key (rd1:restore_data, rd2) =
  if pointer_eq (rd1, rd2) then raise Symtab.SAME else
  if not (quotient_eq (#quotient rd1, #quotient rd2)) then raise Symtab.DUP key else
    { quotient = #quotient rd1,
      transfer_rules = Item_Net.merge (#transfer_rules rd1, #transfer_rules rd2)}

structure Data = Generic_Data
(
  type T =
    { quot_maps : quot_map Symtab.table,
      quotients : quotient Symtab.table,
      reflexivity_rules : thm Item_Net.T,
      relator_distr_data : relator_distr_data Symtab.table,
      restore_data : restore_data Symtab.table,
      no_code_types : unit Symtab.table
    }
  val empty =
    { quot_maps = Symtab.empty,
      quotients = Symtab.empty,
      reflexivity_rules = Thm.item_net,
      relator_distr_data = Symtab.empty,
      restore_data = Symtab.empty,
      no_code_types = Symtab.empty
    }
  val extend = I
  fun merge
    ( { quot_maps = qm1, quotients = q1, reflexivity_rules = rr1, relator_distr_data = rdd1,
        restore_data = rd1, no_code_types = nct1 },
      { quot_maps = qm2, quotients = q2, reflexivity_rules = rr2, relator_distr_data = rdd2,
        restore_data = rd2, no_code_types = nct2 } ) =
    { quot_maps = Symtab.merge (K true) (qm1, qm2),
      quotients = Symtab.merge (K true) (q1, q2),
      reflexivity_rules = Item_Net.merge (rr1, rr2),
      relator_distr_data = Symtab.merge (K true) (rdd1, rdd2),
      restore_data = Symtab.join join_restore_data (rd1, rd2),
      no_code_types = Symtab.merge (K true) (nct1, nct2)
    }
)

fun map_data f1 f2 f3 f4 f5 f6
  { quot_maps, quotients, reflexivity_rules, relator_distr_data, restore_data, no_code_types } =
  { quot_maps = f1 quot_maps,
    quotients = f2 quotients,
    reflexivity_rules = f3 reflexivity_rules,
    relator_distr_data = f4 relator_distr_data,
    restore_data = f5 restore_data,
    no_code_types = f6 no_code_types
  }

fun map_quot_maps           f = map_data f I I I I I
fun map_quotients           f = map_data I f I I I I
fun map_reflexivity_rules   f = map_data I I f I I I
fun map_relator_distr_data  f = map_data I I I f I I
fun map_restore_data        f = map_data I I I I f I
fun map_no_code_types       f = map_data I I I I I f

val get_quot_maps' = #quot_maps o Data.get
val get_quotients' = #quotients o Data.get
val get_reflexivity_rules' = #reflexivity_rules o Data.get
val get_relator_distr_data' = #relator_distr_data o Data.get
val get_restore_data' = #restore_data o Data.get
val get_no_code_types' = #no_code_types o Data.get

val get_quot_maps = get_quot_maps' o Context.Proof
val get_quotients = get_quotients' o Context.Proof
val get_relator_distr_data = get_relator_distr_data' o Context.Proof
val get_restore_data = get_restore_data' o Context.Proof
val get_no_code_types = get_no_code_types' o Context.Proof


(* info about Quotient map theorems *)

val lookup_quot_maps = Symtab.lookup o get_quot_maps

fun quot_map_thm_sanity_check rel_quot_thm ctxt =
  let
    fun quot_term_absT ctxt quot_term =
      let
        val (_, abs, _, _) = (dest_Quotient o HOLogic.dest_Trueprop) quot_term
          handle TERM (_, [t]) => error (Pretty.string_of (Pretty.block
            [Pretty.str "The Quotient map theorem is not in the right form.",
             Pretty.brk 1,
             Pretty.str "The following term is not the Quotient predicate:",
             Pretty.brk 1,
             Syntax.pretty_term ctxt t]))
      in
        fastype_of abs
      end

    val ((_, [rel_quot_thm_fixed]), ctxt') = Variable.importT [rel_quot_thm] ctxt
    val rel_quot_thm_prop = Thm.prop_of rel_quot_thm_fixed
    val rel_quot_thm_concl = Logic.strip_imp_concl rel_quot_thm_prop
    val rel_quot_thm_prems = Logic.strip_imp_prems rel_quot_thm_prop;
    val concl_absT = quot_term_absT ctxt' rel_quot_thm_concl
    val concl_tfrees = Term.add_tfree_namesT (concl_absT) []
    val prems_tfrees = fold (fn typ => fn list => Term.add_tfree_namesT (quot_term_absT ctxt' typ) list)
                          rel_quot_thm_prems []
    val extra_prem_tfrees =
      case subtract (op =) concl_tfrees prems_tfrees of
        [] => []
      | extras => [Pretty.block ([Pretty.str "Extra type variables in the premises:",
                                 Pretty.brk 1] @
                                 ((Pretty.commas o map (Pretty.str o quote)) extras) @
                                 [Pretty.str "."])]
    val errs = extra_prem_tfrees
  in
    if null errs then () else error (cat_lines (["Sanity check of the quotient map theorem failed:",""]
                                                 @ (map Pretty.string_of errs)))
  end


fun add_quot_map rel_quot_thm context =
  let
    val _ = Context.cases (K ()) (quot_map_thm_sanity_check rel_quot_thm) context
    val rel_quot_thm_concl = (Logic.strip_imp_concl o Thm.prop_of) rel_quot_thm
    val (_, abs, _, _) = (dest_Quotient o HOLogic.dest_Trueprop) rel_quot_thm_concl
    val relatorT_name = (fst o dest_Type o fst o dest_funT o fastype_of) abs
    val minfo = {rel_quot_thm = Thm.trim_context rel_quot_thm}
  in
    Data.map (map_quot_maps (Symtab.update (relatorT_name, minfo))) context
  end

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>quot_map\<close> (Scan.succeed (Thm.declaration_attribute add_quot_map))
      "declaration of the Quotient map theorem")

fun print_quot_maps ctxt =
  let
    fun prt_map (ty_name, {rel_quot_thm}) =
      Pretty.block (separate (Pretty.brk 2)
         [Pretty.str "type:",
          Pretty.str ty_name,
          Pretty.str "quot. theorem:",
          Syntax.pretty_term ctxt (Thm.prop_of rel_quot_thm)])
  in
    map prt_map (Symtab.dest (get_quot_maps ctxt))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end


(* info about quotient types *)

fun transform_pcr_info phi {pcrel_def, pcr_cr_eq} =
  {pcrel_def = Morphism.thm phi pcrel_def, pcr_cr_eq = Morphism.thm phi pcr_cr_eq}

fun transform_quotient phi {quot_thm, pcr_info} =
  {quot_thm = Morphism.thm phi quot_thm, pcr_info = Option.map (transform_pcr_info phi) pcr_info}

fun lookup_quotients ctxt type_name =
  Symtab.lookup (get_quotients ctxt) type_name
  |> Option.map (transform_quotient (Morphism.transfer_morphism' ctxt))

fun lookup_quot_thm_quotients ctxt quot_thm =
  let
    val (_, qtyp) = quot_thm_rty_qty quot_thm
    val qty_full_name = (fst o dest_Type) qtyp
    fun compare_data (data:quotient) = Thm.eq_thm_prop (#quot_thm data, quot_thm)
  in
    case lookup_quotients ctxt qty_full_name of
      SOME quotient => if compare_data quotient then SOME quotient else NONE
    | NONE => NONE
  end

fun update_quotients type_name qinfo context =
  let val qinfo' = transform_quotient Morphism.trim_context_morphism qinfo
  in Data.map (map_quotients (Symtab.update (type_name, qinfo'))) context end

fun delete_quotients quot_thm context =
  let
    val (_, qtyp) = quot_thm_rty_qty quot_thm
    val qty_full_name = (fst o dest_Type) qtyp
  in
    if is_some (lookup_quot_thm_quotients (Context.proof_of context) quot_thm)
    then Data.map (map_quotients (Symtab.delete qty_full_name)) context
    else context
  end

fun print_quotients ctxt =
  let
    fun prt_quot (qty_name, {quot_thm, pcr_info}: quotient) =
      Pretty.block (separate (Pretty.brk 2)
        ([Pretty.str "type:", Pretty.str qty_name,
          Pretty.str "quot thm:", Thm.pretty_thm ctxt quot_thm] @
         (case pcr_info of
           NONE => []
         | SOME {pcrel_def, pcr_cr_eq, ...} =>
            [Pretty.str "pcrel_def thm:", Thm.pretty_thm ctxt pcrel_def,
             Pretty.str "pcr_cr_eq thm:", Thm.pretty_thm ctxt pcr_cr_eq])))
  in
    map prt_quot (Symtab.dest (get_quotients ctxt))
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>quot_del\<close> (Scan.succeed (Thm.declaration_attribute delete_quotients))
      "deletes the Quotient theorem")

(* data for restoring Transfer/Lifting context *)

fun lookup_restore_data ctxt bundle_name = Symtab.lookup (get_restore_data ctxt) bundle_name

fun update_restore_data bundle_name restore_data context =
  Data.map (map_restore_data (Symtab.update (bundle_name, restore_data))) context

fun init_restore_data bundle_name qinfo context =
  update_restore_data bundle_name { quotient = qinfo, transfer_rules = Thm.item_net } context

fun add_transfer_rules_in_restore_data bundle_name transfer_rules context =
  (case Symtab.lookup (get_restore_data' context) bundle_name of
    SOME restore_data =>
      update_restore_data bundle_name { quotient = #quotient restore_data,
        transfer_rules = Item_Net.merge ((#transfer_rules restore_data), transfer_rules) } context
  | NONE => error ("The restore data " ^ quote bundle_name ^ " is not defined."))


(* theorems that a relator of an eq_onp is an eq_onp of the corresponding predicate *)

fun get_relator_eq_onp_rules ctxt =
  map safe_mk_meta_eq (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>relator_eq_onp\<close>))


(* info about reflexivity rules *)

fun get_reflexivity_rules ctxt =
  Item_Net.content (get_reflexivity_rules' (Context.Proof ctxt))
  |> map (Thm.transfer' ctxt)

fun add_reflexivity_rule thm =
  Data.map (map_reflexivity_rules (Item_Net.update (Thm.trim_context thm)))

val add_reflexivity_rule_attribute = Thm.declaration_attribute add_reflexivity_rule


(* info about relator distributivity theorems *)

fun map_relator_distr_data' f1 f2 f3 f4
  {pos_mono_rule, neg_mono_rule, pos_distr_rules, neg_distr_rules} =
  {pos_mono_rule   = f1 pos_mono_rule,
   neg_mono_rule   = f2 neg_mono_rule,
   pos_distr_rules = f3 pos_distr_rules,
   neg_distr_rules = f4 neg_distr_rules}

fun map_pos_mono_rule f = map_relator_distr_data' f I I I
fun map_neg_mono_rule f = map_relator_distr_data' I f I I
fun map_pos_distr_rules f = map_relator_distr_data' I I f I
fun map_neg_distr_rules f = map_relator_distr_data' I I I f

fun introduce_polarities rule =
  let
    val dest_less_eq = HOLogic.dest_bin \<^const_name>\<open>less_eq\<close> dummyT
    val prems_pairs = map (dest_less_eq o HOLogic.dest_Trueprop) (Thm.prems_of rule)
    val equal_prems = filter op= prems_pairs
    val _ =
      if null equal_prems then ()
      else error "The rule contains reflexive assumptions."
    val concl_pairs = rule
      |> Thm.concl_of
      |> HOLogic.dest_Trueprop
      |> dest_less_eq
      |> apply2 (snd o strip_comb)
      |> op ~~
      |> filter_out op =

    val _ = if has_duplicates op= concl_pairs
      then error "The rule contains duplicated variables in the conlusion." else ()

    fun rewrite_prem prem_pair =
      if member op= concl_pairs prem_pair
      then HOLogic.Trueprop_conv (Conv.rewr_conv (Thm.symmetric @{thm POS_def}))
      else if member op= concl_pairs (swap prem_pair)
      then HOLogic.Trueprop_conv (Conv.rewr_conv (Thm.symmetric @{thm NEG_def}))
      else error "The rule contains a non-relevant assumption."

    fun rewrite_prems [] = Conv.all_conv
      | rewrite_prems (x::xs) = Conv.implies_conv (rewrite_prem x) (rewrite_prems xs)

    val rewrite_prems_conv = rewrite_prems prems_pairs
    val rewrite_concl_conv =
      Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.rewr_conv (Thm.symmetric @{thm POS_def})))
  in
    (Conv.fconv_rule (rewrite_prems_conv then_conv rewrite_concl_conv)) rule
  end
  handle
    TERM _ => error "The rule has a wrong format."
    | CTERM _ => error "The rule has a wrong format."

fun negate_mono_rule mono_rule =
  let
    val rewr_conv = HOLogic.Trueprop_conv (Conv.rewrs_conv [@{thm POS_NEG}, @{thm NEG_POS}])
  in
    Conv.fconv_rule (Conv.prems_conv ~1 rewr_conv then_conv Conv.concl_conv ~1 rewr_conv) mono_rule
  end;

fun add_reflexivity_rules mono_rule context =
  let
    val ctxt = Context.proof_of context
    val thy = Context.theory_of context

    fun find_eq_rule thm =
      let
        val concl_rhs = (hd o get_args 1 o HOLogic.dest_Trueprop o Thm.concl_of) thm
        val rules = Transfer.retrieve_relator_eq ctxt concl_rhs
      in
        find_first (fn th => Pattern.matches thy (concl_rhs,
          (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o Thm.concl_of) th)) rules
      end

    val eq_rule = find_eq_rule mono_rule;
    val eq_rule = if is_some eq_rule then the eq_rule else error
      "No corresponding rule that the relator preserves equality was found."
  in
    context
    |> add_reflexivity_rule (Drule.zero_var_indexes (@{thm ord_le_eq_trans} OF [mono_rule, eq_rule]))
    |> add_reflexivity_rule
      (Drule.zero_var_indexes (@{thm ord_eq_le_trans} OF [sym OF [eq_rule], mono_rule]))
  end

fun add_mono_rule mono_rule context =
  let
    val pol_mono_rule = introduce_polarities mono_rule
    val mono_ruleT_name = (fst o dest_Type o fst o relation_types o fst o relation_types o snd o
      dest_Const o head_of o HOLogic.dest_Trueprop o Thm.concl_of) pol_mono_rule
  in
    if Symtab.defined (get_relator_distr_data' context) mono_ruleT_name
    then
      (if Context_Position.is_visible_generic context then
        warning ("Monotonicity rule for type " ^ quote mono_ruleT_name ^ " is already_defined.")
       else (); context)
    else
      let
        val neg_mono_rule = negate_mono_rule pol_mono_rule
        val relator_distr_data = {pos_mono_rule = pol_mono_rule, neg_mono_rule = neg_mono_rule,
          pos_distr_rules = [], neg_distr_rules = []}
      in
        context
        |> Data.map (map_relator_distr_data (Symtab.update (mono_ruleT_name, relator_distr_data)))
        |> add_reflexivity_rules mono_rule
      end
  end;

local
  fun add_distr_rule update_entry distr_rule context =
    let
      val distr_ruleT_name = (fst o dest_Type o fst o relation_types o fst o relation_types o snd o
        dest_Const o head_of o HOLogic.dest_Trueprop o Thm.concl_of) distr_rule
    in
      if Symtab.defined (get_relator_distr_data' context) distr_ruleT_name then
        Data.map (map_relator_distr_data (Symtab.map_entry distr_ruleT_name (update_entry distr_rule)))
          context
      else error "The monotonicity rule is not defined."
    end

  fun rewrite_concl_conv thm ctm =
    Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.rewr_conv (Thm.symmetric thm))) ctm
    handle CTERM _ => error "The rule has a wrong format."

in
  fun add_pos_distr_rule distr_rule context =
    let
      val distr_rule = Conv.fconv_rule (rewrite_concl_conv @{thm POS_def}) distr_rule
      fun update_entry distr_rule data =
        map_pos_distr_rules (cons (@{thm POS_trans} OF [distr_rule, #pos_mono_rule data])) data
    in
      add_distr_rule update_entry distr_rule context
    end
    handle THM _ => error "Combining of the distr. rule and the monotonicity rule together has failed."

  fun add_neg_distr_rule distr_rule context =
    let
      val distr_rule = Conv.fconv_rule (rewrite_concl_conv @{thm NEG_def}) distr_rule
      fun update_entry distr_rule data =
        map_neg_distr_rules (cons (@{thm NEG_trans} OF [distr_rule, #neg_mono_rule data])) data
    in
      add_distr_rule update_entry distr_rule context
    end
    handle THM _ => error "Combining of the distr. rule and the monotonicity rule together has failed."
end

local
  val eq_refl2 = sym RS @{thm eq_refl}
in
  fun add_eq_distr_rule distr_rule context =
    let
      val pos_distr_rule = @{thm eq_refl} OF [distr_rule]
      val neg_distr_rule = eq_refl2 OF [distr_rule]
    in
      context
      |> add_pos_distr_rule pos_distr_rule
      |> add_neg_distr_rule neg_distr_rule
    end
end;

local
  fun sanity_check rule =
    let
      val assms = map (perhaps (try HOLogic.dest_Trueprop)) (Thm.prems_of rule)
      val concl = (perhaps (try HOLogic.dest_Trueprop)) (Thm.concl_of rule);
      val (lhs, rhs) =
        (case concl of
          Const (\<^const_name>\<open>less_eq\<close>, _) $ (lhs as Const (\<^const_name>\<open>relcompp\<close>,_) $ _ $ _) $ rhs =>
            (lhs, rhs)
        | Const (\<^const_name>\<open>less_eq\<close>, _) $ rhs $ (lhs as Const (\<^const_name>\<open>relcompp\<close>,_) $ _ $ _) =>
            (lhs, rhs)
        | Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (lhs as Const (\<^const_name>\<open>relcompp\<close>,_) $ _ $ _) $ rhs =>
            (lhs, rhs)
        | _ => error "The rule has a wrong format.")

      val lhs_vars = Term.add_vars lhs []
      val rhs_vars = Term.add_vars rhs []
      val assms_vars = fold Term.add_vars assms [];
      val _ =
        if has_duplicates op= lhs_vars
        then error "Left-hand side has variable duplicates" else ()
      val _ =
        if subset op= (rhs_vars, lhs_vars) then ()
        else error "Extra variables in the right-hand side of the rule"
      val _ =
        if subset op= (assms_vars, lhs_vars) then ()
        else error "Extra variables in the assumptions of the rule"
      val rhs_args = (snd o strip_comb) rhs;
      fun check_comp t =
        (case t of
          Const (\<^const_name>\<open>relcompp\<close>, _) $ Var _ $ Var _ => ()
        | _ => error "There is an argument on the rhs that is not a composition.")
      val _ = map check_comp rhs_args
    in () end
in

  fun add_distr_rule distr_rule context =
    let
      val _ = sanity_check distr_rule
      val concl = (perhaps (try HOLogic.dest_Trueprop)) (Thm.concl_of distr_rule)
    in
      (case concl of
        Const (\<^const_name>\<open>less_eq\<close>, _) $ (Const (\<^const_name>\<open>relcompp\<close>,_) $ _ $ _) $ _ =>
          add_pos_distr_rule distr_rule context
      | Const (\<^const_name>\<open>less_eq\<close>, _) $ _ $ (Const (\<^const_name>\<open>relcompp\<close>,_) $ _ $ _) =>
          add_neg_distr_rule distr_rule context
      | Const (\<^const_name>\<open>HOL.eq\<close>, _) $ (Const (\<^const_name>\<open>relcompp\<close>,_) $ _ $ _) $ _ =>
          add_eq_distr_rule distr_rule context)
    end
end

fun get_distr_rules_raw context =
  Symtab.fold (fn (_, {pos_distr_rules, neg_distr_rules, ...}) => fn rules =>
      pos_distr_rules @ neg_distr_rules @ rules)
    (get_relator_distr_data' context) []
  |> map (Thm.transfer'' context)

fun get_mono_rules_raw context =
  Symtab.fold (fn (_, {pos_mono_rule, neg_mono_rule, ...}) => fn rules =>
      [pos_mono_rule, neg_mono_rule] @ rules)
    (get_relator_distr_data' context) []
  |> map (Thm.transfer'' context)

val lookup_relator_distr_data = Symtab.lookup o get_relator_distr_data

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>relator_mono\<close> (Scan.succeed (Thm.declaration_attribute add_mono_rule))
      "declaration of relator's monotonicity"
    #> Attrib.setup \<^binding>\<open>relator_distr\<close> (Scan.succeed (Thm.declaration_attribute add_distr_rule))
      "declaration of relator's distributivity over OO"
    #> Global_Theory.add_thms_dynamic
       (\<^binding>\<open>relator_distr_raw\<close>, get_distr_rules_raw)
    #> Global_Theory.add_thms_dynamic
       (\<^binding>\<open>relator_mono_raw\<close>, get_mono_rules_raw))


(* no_code types *)

fun add_no_code_type type_name context =
  Data.map (map_no_code_types (Symtab.update (type_name, ()))) context;

fun is_no_code_type context type_name = (Symtab.defined o get_no_code_types) context type_name


(* setup fixed eq_onp rules *)

val _ = Context.>>
  (fold (Named_Theorems.add_thm \<^named_theorems>\<open>relator_eq_onp\<close> o
    Transfer.prep_transfer_domain_thm \<^context>)
  @{thms composed_equiv_rel_eq_onp composed_equiv_rel_eq_eq_onp})


(* setup fixed reflexivity rules *)

val _ = Context.>> (fold add_reflexivity_rule
  @{thms order_refl[of "(=)"] eq_onp_le_eq Quotient_composition_le_eq Quotient_composition_ge_eq
    bi_unique_OO bi_total_OO right_unique_OO right_total_OO left_unique_OO left_total_OO})


(* outer syntax commands *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_quot_maps\<close> "print quotient map functions"
    (Scan.succeed (Toplevel.keep (print_quot_maps o Toplevel.context_of)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_quotients\<close> "print quotients"
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

end
