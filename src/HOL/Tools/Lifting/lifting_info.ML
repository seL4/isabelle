(*  Title:      HOL/Tools/Lifting/lifting_info.ML
    Author:     Ondrej Kuncar

Context data for the lifting package.
*)

signature LIFTING_INFO =
sig
  type quotmaps = {rel_quot_thm: thm}
  val lookup_quotmaps: Proof.context -> string -> quotmaps option
  val lookup_quotmaps_global: theory -> string -> quotmaps option
  val print_quotmaps: Proof.context -> unit

  type pcrel_info = {pcrel_def: thm, pcr_cr_eq: thm}
  type quotients = {quot_thm: thm, pcrel_info: pcrel_info option}
  val transform_quotients: morphism -> quotients -> quotients
  val lookup_quotients: Proof.context -> string -> quotients option
  val lookup_quotients_global: theory -> string -> quotients option
  val update_quotients: string -> quotients -> Context.generic -> Context.generic
  val dest_quotients: Proof.context -> quotients list
  val print_quotients: Proof.context -> unit

  val get_invariant_commute_rules: Proof.context -> thm list
  
  val get_reflexivity_rules: Proof.context -> thm list
  val add_reflexivity_rule_attribute: attribute
  val add_reflexivity_rule_attrib: Attrib.src

  type relator_distr_data = {pos_mono_rule: thm, neg_mono_rule: thm, 
    pos_distr_rules: thm list, neg_distr_rules: thm list}
  val lookup_relator_distr_data: Proof.context -> string -> relator_distr_data option
  val lookup_relator_distr_data_global: theory -> string -> relator_distr_data option

  val setup: theory -> theory
end;

structure Lifting_Info: LIFTING_INFO =
struct

open Lifting_Util

(** data containers **)

(* info about Quotient map theorems *)
type quotmaps = {rel_quot_thm: thm}

structure Quotmaps = Generic_Data
(
  type T = quotmaps Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

val lookup_quotmaps = Symtab.lookup o Quotmaps.get o Context.Proof
val lookup_quotmaps_global = Symtab.lookup o Quotmaps.get o Context.Theory

(* FIXME export proper internal update operation!? *)

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
    val rel_quot_thm_prop = prop_of rel_quot_thm_fixed
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


fun add_quot_map rel_quot_thm ctxt = 
  let
    val _ = Context.cases (K ()) (quot_map_thm_sanity_check rel_quot_thm) ctxt
    val rel_quot_thm_concl = (Logic.strip_imp_concl o prop_of) rel_quot_thm
    val (_, abs, _, _) = (dest_Quotient o HOLogic.dest_Trueprop) rel_quot_thm_concl
    val relatorT_name = (fst o dest_Type o fst o dest_funT o fastype_of) abs
    val minfo = {rel_quot_thm = rel_quot_thm}
  in
    Quotmaps.map (Symtab.update (relatorT_name, minfo)) ctxt
  end    

val quot_map_attribute_setup =
  Attrib.setup @{binding quot_map} (Scan.succeed (Thm.declaration_attribute add_quot_map))
    "declaration of the Quotient map theorem"

fun print_quotmaps ctxt =
  let
    fun prt_map (ty_name, {rel_quot_thm}) =
      Pretty.block (separate (Pretty.brk 2)
         [Pretty.str "type:", 
          Pretty.str ty_name,
          Pretty.str "quot. theorem:", 
          Syntax.pretty_term ctxt (prop_of rel_quot_thm)])
  in
    map prt_map (Symtab.dest (Quotmaps.get (Context.Proof ctxt)))
    |> Pretty.big_list "maps for type constructors:"
    |> Pretty.writeln
  end

(* info about quotient types *)
type pcrel_info = {pcrel_def: thm, pcr_cr_eq: thm}
type quotients = {quot_thm: thm, pcrel_info: pcrel_info option}

structure Quotients = Generic_Data
(
  type T = quotients Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

fun transform_pcrel_info phi {pcrel_def, pcr_cr_eq} =
  {pcrel_def = Morphism.thm phi pcrel_def, pcr_cr_eq = Morphism.thm phi pcr_cr_eq}

fun transform_quotients phi {quot_thm, pcrel_info} =
  {quot_thm = Morphism.thm phi quot_thm, pcrel_info = Option.map (transform_pcrel_info phi) pcrel_info}

val lookup_quotients = Symtab.lookup o Quotients.get o Context.Proof
val lookup_quotients_global = Symtab.lookup o Quotients.get o Context.Theory

fun update_quotients str qinfo = Quotients.map (Symtab.update (str, qinfo))

fun delete_quotients quot_thm ctxt =
  let
    val (_, qtyp) = quot_thm_rty_qty quot_thm
    val qty_full_name = (fst o dest_Type) qtyp
    val symtab = Quotients.get ctxt
    val opt_stored_quot_thm = Symtab.lookup symtab qty_full_name
  in
    case opt_stored_quot_thm of
      SOME data => 
        if Thm.eq_thm_prop (#quot_thm data, quot_thm) then
          Quotients.map (Symtab.delete qty_full_name) ctxt
        else
          ctxt
      | NONE => ctxt
  end

fun dest_quotients ctxt =  (* FIXME slightly expensive way to retrieve data *)
  map snd (Symtab.dest (Quotients.get (Context.Proof ctxt)))

fun print_quotients ctxt =
  let
    fun prt_quot (qty_name, {quot_thm, pcrel_info}: quotients) =
      Pretty.block (separate (Pretty.brk 2)
       [Pretty.str "type:", 
        Pretty.str qty_name,
        Pretty.str "quot. thm:",
        Syntax.pretty_term ctxt (prop_of quot_thm),
        Pretty.str "pcrel_def thm:",
        option_fold (Pretty.str "-") ((Syntax.pretty_term ctxt) o prop_of o #pcrel_def) pcrel_info,
        Pretty.str "pcr_cr_eq thm:",
        option_fold (Pretty.str "-") ((Syntax.pretty_term ctxt) o prop_of o #pcr_cr_eq) pcrel_info])
  in
    map prt_quot (Symtab.dest (Quotients.get (Context.Proof ctxt)))
    |> Pretty.big_list "quotients:"
    |> Pretty.writeln
  end

val quot_del_attribute_setup =
  Attrib.setup @{binding quot_del} (Scan.succeed (Thm.declaration_attribute delete_quotients))
    "deletes the Quotient theorem"

structure Invariant_Commute = Named_Thms
(
  val name = @{binding invariant_commute}
  val description = "theorems that a relator of an invariant is an invariant of the corresponding predicate"
)

fun get_invariant_commute_rules ctxt = map safe_mk_meta_eq (Invariant_Commute.get ctxt)

structure Reflp_Preserve = Named_Thms
(
  val name = @{binding reflexivity_rule}
  val description = "theorems that a relator preserves a reflexivity property"
)

val get_reflexivity_rules = Reflp_Preserve.get
val add_reflexivity_rule_attribute = Reflp_Preserve.add
val add_reflexivity_rule_attrib = Attrib.internal (K add_reflexivity_rule_attribute)

(* info about relator distributivity theorems *)
type relator_distr_data = {pos_mono_rule: thm, neg_mono_rule: thm, 
  pos_distr_rules: thm list, neg_distr_rules: thm list}

fun map_relator_distr_data f1 f2 f3 f4
  {pos_mono_rule, neg_mono_rule, pos_distr_rules, neg_distr_rules} =
  {pos_mono_rule   = f1 pos_mono_rule, 
   neg_mono_rule   = f2 neg_mono_rule,
   pos_distr_rules = f3 pos_distr_rules, 
   neg_distr_rules = f4 neg_distr_rules}

fun map_pos_mono_rule f = map_relator_distr_data f I I I
fun map_neg_mono_rule f = map_relator_distr_data I f I I
fun map_pos_distr_rules f = map_relator_distr_data I I f I 
fun map_neg_distr_rules f = map_relator_distr_data I I I f

structure Relator_Distr = Generic_Data
(
  type T = relator_distr_data Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
);

fun introduce_polarities rule =
  let
    val dest_less_eq = HOLogic.dest_bin @{const_name "less_eq"} dummyT
    val prems_pairs = map (dest_less_eq o HOLogic.dest_Trueprop) (prems_of rule)
    val equal_prems = filter op= prems_pairs
    val _ = if null equal_prems then () 
      else error "The rule contains reflexive assumptions."
    val concl_pairs = rule 
      |> concl_of
      |> HOLogic.dest_Trueprop
      |> dest_less_eq
      |> pairself (snd o strip_comb)
      |> op~~
      |> filter_out op=
    
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

fun add_mono_rule mono_rule ctxt = 
  let
    val mono_rule = introduce_polarities mono_rule
    val mono_ruleT_name = (fst o dest_Type o fst o relation_types o fst o relation_types o snd o 
      dest_Const o head_of o HOLogic.dest_Trueprop o concl_of) mono_rule
    val _ = if Symtab.defined (Relator_Distr.get ctxt) mono_ruleT_name 
      then error ("Monotocity rule for type " ^ quote mono_ruleT_name ^ " is already_defined.")
      else ()
    val neg_mono_rule = negate_mono_rule mono_rule
    val relator_distr_data = {pos_mono_rule = mono_rule, neg_mono_rule = neg_mono_rule, 
      pos_distr_rules = [], neg_distr_rules = []}
  in
    Relator_Distr.map (Symtab.update (mono_ruleT_name, relator_distr_data)) ctxt
  end;

local 
  fun add_distr_rule update_entry distr_rule ctxt =
    let
      val distr_ruleT_name = (fst o dest_Type o fst o relation_types o fst o relation_types o snd o 
        dest_Const o head_of o HOLogic.dest_Trueprop o concl_of) distr_rule
    in
      if Symtab.defined (Relator_Distr.get ctxt) distr_ruleT_name then 
        Relator_Distr.map (Symtab.map_entry distr_ruleT_name (update_entry distr_rule)) ctxt
      else error "The monoticity rule is not defined."
    end

    fun rewrite_concl_conv thm ctm = 
      Conv.concl_conv ~1 (HOLogic.Trueprop_conv (Conv.rewr_conv (Thm.symmetric thm))) ctm
      handle CTERM _ => error "The rule has a wrong format."

in
  fun add_pos_distr_rule distr_rule ctxt = 
    let
      val distr_rule = Conv.fconv_rule (rewrite_concl_conv @{thm POS_def}) distr_rule
      fun update_entry distr_rule data = 
        map_pos_distr_rules (cons (@{thm POS_trans} OF [distr_rule, #pos_mono_rule data])) data
    in
      add_distr_rule update_entry distr_rule ctxt
    end
    handle THM _ => error "Combining of the distr. rule and the monotonicity rule together has failed."

  
  fun add_neg_distr_rule distr_rule ctxt = 
    let
      val distr_rule = Conv.fconv_rule (rewrite_concl_conv @{thm NEG_def}) distr_rule
      fun update_entry distr_rule data = 
        map_neg_distr_rules (cons (@{thm NEG_trans} OF [distr_rule, #neg_mono_rule data])) data
    in
      add_distr_rule update_entry distr_rule ctxt
    end
    handle THM _ => error "Combining of the distr. rule and the monotonicity rule together has failed."
end

local 
  val eq_refl2 = sym RS @{thm eq_refl}
in
  fun add_eq_distr_rule distr_rule ctxt =
    let 
      val pos_distr_rule = @{thm eq_refl} OF [distr_rule]
      val neg_distr_rule = eq_refl2 OF [distr_rule]
    in
      ctxt 
      |> add_pos_distr_rule pos_distr_rule
      |> add_neg_distr_rule neg_distr_rule
    end
end;

local
  fun sanity_check rule =
    let
      val assms = map (perhaps (try HOLogic.dest_Trueprop)) (prems_of rule)
      val concl = (perhaps (try HOLogic.dest_Trueprop)) (concl_of rule);
      val (lhs, rhs) = case concl of
        Const ("Orderings.ord_class.less_eq", _) $ (lhs as Const ("Relation.relcompp",_) $ _ $ _) $ rhs => 
          (lhs, rhs)
        | Const ("Orderings.ord_class.less_eq", _) $ rhs $ (lhs as Const ("Relation.relcompp",_) $ _ $ _) => 
          (lhs, rhs)
        | Const ("HOL.eq", _) $ (lhs as Const ("Relation.relcompp",_) $ _ $ _) $ rhs => (lhs, rhs)
        | _ => error "The rule has a wrong format."
      
      val lhs_vars = Term.add_vars lhs []
      val rhs_vars = Term.add_vars rhs []
      val assms_vars = fold Term.add_vars assms [];
      val _ = if has_duplicates op= lhs_vars then error "Left-hand side has variable duplicates" else ()
      val _ = if subset op= (rhs_vars, lhs_vars) then () 
        else error "Extra variables in the right-hand side of the rule"
      val _ = if subset op= (assms_vars, lhs_vars) then () 
        else error "Extra variables in the assumptions of the rule"
      val rhs_args = (snd o strip_comb) rhs;
      fun check_comp t = case t of 
        Const ("Relation.relcompp", _) $ Var (_, _) $ Var (_,_) => ()
        | _ => error "There is an argument on the rhs that is not a composition."
      val _ = map check_comp rhs_args
    in
      ()
    end
in

  fun add_distr_rule distr_rule ctxt = 
    let
      val _ = sanity_check distr_rule
      val concl = (perhaps (try HOLogic.dest_Trueprop)) (concl_of distr_rule)
    in
      case concl of
        Const ("Orderings.ord_class.less_eq", _) $ (Const ("Relation.relcompp",_) $ _ $ _) $ _ => 
          add_pos_distr_rule distr_rule ctxt
        | Const ("Orderings.ord_class.less_eq", _) $ _ $ (Const ("Relation.relcompp",_) $ _ $ _) => 
          add_neg_distr_rule distr_rule ctxt
        | Const ("HOL.eq", _) $ (Const ("Relation.relcompp",_) $ _ $ _) $ _ =>
          add_eq_distr_rule distr_rule ctxt
    end
end

fun get_distr_rules_raw ctxt = Symtab.fold 
  (fn (_, {pos_distr_rules, neg_distr_rules, ...}) => fn rules => pos_distr_rules @ neg_distr_rules @ rules) 
    (Relator_Distr.get ctxt) []

fun get_mono_rules_raw ctxt = Symtab.fold 
  (fn (_, {pos_mono_rule, neg_mono_rule, ...}) => fn rules => [pos_mono_rule, neg_mono_rule] @ rules) 
    (Relator_Distr.get ctxt) []

val lookup_relator_distr_data = Symtab.lookup o Relator_Distr.get o Context.Proof
val lookup_relator_distr_data_global = Symtab.lookup o Relator_Distr.get o Context.Theory

val relator_distr_attribute_setup =
  Attrib.setup @{binding relator_mono} (Scan.succeed (Thm.declaration_attribute add_mono_rule))
    "declaration of relator's monoticity"
  #> Attrib.setup @{binding relator_distr} (Scan.succeed (Thm.declaration_attribute add_distr_rule))
    "declaration of relator's distributivity over OO"
  #> Global_Theory.add_thms_dynamic
     (@{binding relator_distr_raw}, get_distr_rules_raw)
  #> Global_Theory.add_thms_dynamic
     (@{binding relator_mono_raw}, get_mono_rules_raw)

(* theory setup *)

val setup =
  quot_map_attribute_setup
  #> quot_del_attribute_setup
  #> Invariant_Commute.setup
  #> Reflp_Preserve.setup
  #> relator_distr_attribute_setup

(* outer syntax commands *)

val _ =
  Outer_Syntax.improper_command @{command_spec "print_quotmaps"} "print quotient map functions"
    (Scan.succeed (Toplevel.keep (print_quotmaps o Toplevel.context_of)))

val _ =
  Outer_Syntax.improper_command @{command_spec "print_quotients"} "print quotients"
    (Scan.succeed (Toplevel.keep (print_quotients o Toplevel.context_of)))

end;
