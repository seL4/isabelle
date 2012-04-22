(*  Title:      HOL/Tools/Nitpick/nitpick_hol.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Auxiliary HOL-related functions used by Nitpick.
*)

signature NITPICK_HOL =
sig
  type styp = Nitpick_Util.styp
  type const_table = term list Symtab.table
  type special_fun = (styp * int list * term list) * styp
  type unrolled = styp * styp
  type wf_cache = (styp * (bool * bool)) list

  type hol_context =
    {thy: theory,
     ctxt: Proof.context,
     max_bisim_depth: int,
     boxes: (typ option * bool option) list,
     stds: (typ option * bool) list,
     wfs: (styp option * bool option) list,
     user_axioms: bool option,
     debug: bool,
     whacks: term list,
     binary_ints: bool option,
     destroy_constrs: bool,
     specialize: bool,
     star_linear_preds: bool,
     total_consts: bool option,
     needs: term list option,
     tac_timeout: Time.time option,
     evals: term list,
     case_names: (string * int) list,
     def_tables: const_table * const_table,
     nondef_table: const_table,
     nondefs: term list,
     simp_table: const_table Unsynchronized.ref,
     psimp_table: const_table,
     choice_spec_table: const_table,
     intro_table: const_table,
     ground_thm_table: term list Inttab.table,
     ersatz_table: (string * string) list,
     skolems: (string * string list) list Unsynchronized.ref,
     special_funs: special_fun list Unsynchronized.ref,
     unrolled_preds: unrolled list Unsynchronized.ref,
     wf_cache: wf_cache Unsynchronized.ref,
     constr_cache: (typ * styp list) list Unsynchronized.ref}

  datatype fixpoint_kind = Lfp | Gfp | NoFp
  datatype boxability =
    InConstr | InSel | InExpr | InPair | InFunLHS | InFunRHS1 | InFunRHS2

  val name_sep : string
  val numeral_prefix : string
  val base_prefix : string
  val step_prefix : string
  val unrolled_prefix : string
  val ubfp_prefix : string
  val lbfp_prefix : string
  val quot_normal_prefix : string
  val skolem_prefix : string
  val special_prefix : string
  val uncurry_prefix : string
  val eval_prefix : string
  val iter_var_prefix : string
  val strip_first_name_sep : string -> string * string
  val original_name : string -> string
  val abs_var : indexname * typ -> term -> term
  val s_conj : term * term -> term
  val s_disj : term * term -> term
  val strip_any_connective : term -> term list * term
  val conjuncts_of : term -> term list
  val disjuncts_of : term -> term list
  val unarize_unbox_etc_type : typ -> typ
  val uniterize_unarize_unbox_etc_type : typ -> typ
  val string_for_type : Proof.context -> typ -> string
  val pretty_for_type : Proof.context -> typ -> Pretty.T
  val prefix_name : string -> string -> string
  val shortest_name : string -> string
  val short_name : string -> string
  val shorten_names_in_term : term -> term
  val strict_type_match : theory -> typ * typ -> bool
  val type_match : theory -> typ * typ -> bool
  val const_match : theory -> styp * styp -> bool
  val term_match : theory -> term * term -> bool
  val frac_from_term_pair : typ -> term -> term -> term
  val is_TFree : typ -> bool
  val is_fun_type : typ -> bool
  val is_set_type : typ -> bool
  val is_fun_or_set_type : typ -> bool
  val is_set_like_type : typ -> bool
  val is_pair_type : typ -> bool
  val is_lfp_iterator_type : typ -> bool
  val is_gfp_iterator_type : typ -> bool
  val is_fp_iterator_type : typ -> bool
  val is_iterator_type : typ -> bool
  val is_boolean_type : typ -> bool
  val is_integer_type : typ -> bool
  val is_bit_type : typ -> bool
  val is_word_type : typ -> bool
  val is_integer_like_type : typ -> bool
  val is_record_type : typ -> bool
  val is_number_type : Proof.context -> typ -> bool
  val is_higher_order_type : typ -> bool
  val elem_type : typ -> typ
  val pseudo_domain_type : typ -> typ
  val pseudo_range_type : typ -> typ
  val const_for_iterator_type : typ -> styp
  val strip_n_binders : int -> typ -> typ list * typ
  val nth_range_type : int -> typ -> typ
  val num_factors_in_type : typ -> int
  val num_binder_types : typ -> int
  val curried_binder_types : typ -> typ list
  val mk_flat_tuple : typ -> term list -> term
  val dest_n_tuple : int -> term -> term list
  val is_real_datatype : theory -> string -> bool
  val is_standard_datatype : theory -> (typ option * bool) list -> typ -> bool
  val is_codatatype : Proof.context -> typ -> bool
  val is_quot_type : Proof.context -> typ -> bool
  val is_pure_typedef : Proof.context -> typ -> bool
  val is_univ_typedef : Proof.context -> typ -> bool
  val is_datatype : Proof.context -> (typ option * bool) list -> typ -> bool
  val is_record_constr : styp -> bool
  val is_record_get : theory -> styp -> bool
  val is_record_update : theory -> styp -> bool
  val is_abs_fun : Proof.context -> styp -> bool
  val is_rep_fun : Proof.context -> styp -> bool
  val is_quot_abs_fun : Proof.context -> styp -> bool
  val is_quot_rep_fun : Proof.context -> styp -> bool
  val mate_of_rep_fun : Proof.context -> styp -> styp
  val is_constr_like : Proof.context -> styp -> bool
  val is_constr : Proof.context -> (typ option * bool) list -> styp -> bool
  val is_sel : string -> bool
  val is_sel_like_and_no_discr : string -> bool
  val box_type : hol_context -> boxability -> typ -> typ
  val binarize_nat_and_int_in_type : typ -> typ
  val binarize_nat_and_int_in_term : term -> term
  val discr_for_constr : styp -> styp
  val num_sels_for_constr_type : typ -> int
  val nth_sel_name_for_constr_name : string -> int -> string
  val nth_sel_for_constr : styp -> int -> styp
  val binarized_and_boxed_nth_sel_for_constr :
    hol_context -> bool -> styp -> int -> styp
  val sel_no_from_name : string -> int
  val close_form : term -> term
  val distinctness_formula : typ -> term list -> term
  val register_frac_type :
    string -> (string * string) list -> morphism -> Context.generic
    -> Context.generic
  val register_frac_type_global :
    string -> (string * string) list -> theory -> theory
  val unregister_frac_type :
    string -> morphism -> Context.generic -> Context.generic
  val unregister_frac_type_global : string -> theory -> theory
  val register_ersatz :
    (string * string) list -> morphism -> Context.generic -> Context.generic
  val register_ersatz_global : (string * string) list -> theory -> theory
  val register_codatatype :
    typ -> string -> styp list -> morphism -> Context.generic -> Context.generic
  val register_codatatype_global :
    typ -> string -> styp list -> theory -> theory
  val unregister_codatatype :
    typ -> morphism -> Context.generic -> Context.generic
  val unregister_codatatype_global : typ -> theory -> theory
  val datatype_constrs : hol_context -> typ -> styp list
  val binarized_and_boxed_datatype_constrs :
    hol_context -> bool -> typ -> styp list
  val num_datatype_constrs : hol_context -> typ -> int
  val constr_name_for_sel_like : string -> string
  val binarized_and_boxed_constr_for_sel : hol_context -> bool -> styp -> styp
  val card_of_type : (typ * int) list -> typ -> int
  val bounded_card_of_type : int -> int -> (typ * int) list -> typ -> int
  val bounded_exact_card_of_type :
    hol_context -> typ list -> int -> int -> (typ * int) list -> typ -> int
  val typical_card_of_type : typ -> int
  val is_finite_type : hol_context -> typ -> bool
  val is_special_eligible_arg : bool -> typ list -> term -> bool
  val s_let :
    typ list -> string -> int -> typ -> typ -> (term -> term) -> term -> term
  val s_betapply : typ list -> term * term -> term
  val s_betapplys : typ list -> term * term list -> term
  val discriminate_value : hol_context -> styp -> term -> term
  val select_nth_constr_arg :
    Proof.context -> (typ option * bool) list -> styp -> term -> int -> typ
    -> term
  val construct_value :
    Proof.context -> (typ option * bool) list -> styp -> term list -> term
  val coerce_term : hol_context -> typ list -> typ -> typ -> term -> term
  val special_bounds : term list -> (indexname * typ) list
  val is_funky_typedef : Proof.context -> typ -> bool
  val all_defs_of : theory -> (term * term) list -> term list
  val all_nondefs_of : Proof.context -> (term * term) list -> term list
  val arity_of_built_in_const :
    theory -> (typ option * bool) list -> styp -> int option
  val is_built_in_const :
    theory -> (typ option * bool) list -> styp -> bool
  val term_under_def : term -> term
  val case_const_names :
    Proof.context -> (typ option * bool) list -> (string * int) list
  val unfold_defs_in_term : hol_context -> term -> term
  val const_def_tables :
    Proof.context -> (term * term) list -> term list
    -> const_table * const_table
  val const_nondef_table : term list -> const_table
  val const_simp_table : Proof.context -> (term * term) list -> const_table
  val const_psimp_table : Proof.context -> (term * term) list -> const_table
  val const_choice_spec_table :
    Proof.context -> (term * term) list -> const_table
  val inductive_intro_table :
    Proof.context -> (term * term) list -> const_table * const_table
    -> const_table
  val ground_theorem_table : theory -> term list Inttab.table
  val ersatz_table : Proof.context -> (string * string) list
  val add_simps : const_table Unsynchronized.ref -> string -> term list -> unit
  val inverse_axioms_for_rep_fun : Proof.context -> styp -> term list
  val optimized_typedef_axioms : Proof.context -> string * typ list -> term list
  val optimized_quot_type_axioms :
    Proof.context -> (typ option * bool) list -> string * typ list -> term list
  val def_of_const : theory -> const_table * const_table -> styp -> term option
  val fixpoint_kind_of_rhs : term -> fixpoint_kind
  val fixpoint_kind_of_const :
    theory -> const_table * const_table -> string * typ -> fixpoint_kind
  val is_real_inductive_pred : hol_context -> styp -> bool
  val is_constr_pattern : Proof.context -> term -> bool
  val is_constr_pattern_lhs : Proof.context -> term -> bool
  val is_constr_pattern_formula : Proof.context -> term -> bool
  val nondef_props_for_const :
    theory -> bool -> const_table -> styp -> term list
  val is_choice_spec_fun : hol_context -> styp -> bool
  val is_choice_spec_axiom : theory -> const_table -> term -> bool
  val is_real_equational_fun : hol_context -> styp -> bool
  val is_equational_fun_but_no_plain_def : hol_context -> styp -> bool
  val codatatype_bisim_axioms : hol_context -> typ -> term list
  val is_well_founded_inductive_pred : hol_context -> styp -> bool
  val unrolled_inductive_pred_const : hol_context -> bool -> styp -> term
  val equational_fun_axioms : hol_context -> styp -> term list
  val is_equational_fun_surely_complete : hol_context -> styp -> bool
  val merged_type_var_table_for_terms :
    theory -> term list -> (sort * string) list
  val merge_type_vars_in_term :
    theory -> bool -> (sort * string) list -> term -> term
  val ground_types_in_type : hol_context -> bool -> typ -> typ list
  val ground_types_in_terms : hol_context -> bool -> term list -> typ list
end;

structure Nitpick_HOL : NITPICK_HOL =
struct

open Nitpick_Util

type const_table = term list Symtab.table
type special_fun = (styp * int list * term list) * styp
type unrolled = styp * styp
type wf_cache = (styp * (bool * bool)) list

type hol_context =
  {thy: theory,
   ctxt: Proof.context,
   max_bisim_depth: int,
   boxes: (typ option * bool option) list,
   stds: (typ option * bool) list,
   wfs: (styp option * bool option) list,
   user_axioms: bool option,
   debug: bool,
   whacks: term list,
   binary_ints: bool option,
   destroy_constrs: bool,
   specialize: bool,
   star_linear_preds: bool,
   total_consts: bool option,
   needs: term list option,
   tac_timeout: Time.time option,
   evals: term list,
   case_names: (string * int) list,
   def_tables: const_table * const_table,
   nondef_table: const_table,
   nondefs: term list,
   simp_table: const_table Unsynchronized.ref,
   psimp_table: const_table,
   choice_spec_table: const_table,
   intro_table: const_table,
   ground_thm_table: term list Inttab.table,
   ersatz_table: (string * string) list,
   skolems: (string * string list) list Unsynchronized.ref,
   special_funs: special_fun list Unsynchronized.ref,
   unrolled_preds: unrolled list Unsynchronized.ref,
   wf_cache: wf_cache Unsynchronized.ref,
   constr_cache: (typ * styp list) list Unsynchronized.ref}

datatype fixpoint_kind = Lfp | Gfp | NoFp
datatype boxability =
  InConstr | InSel | InExpr | InPair | InFunLHS | InFunRHS1 | InFunRHS2

structure Data = Generic_Data
(
  type T = {frac_types: (string * (string * string) list) list,
            ersatz_table: (string * string) list,
            codatatypes: (string * (string * styp list)) list}
  val empty = {frac_types = [], ersatz_table = [], codatatypes = []}
  val extend = I
  fun merge ({frac_types = fs1, ersatz_table = et1, codatatypes = cs1},
             {frac_types = fs2, ersatz_table = et2, codatatypes = cs2}) : T =
    {frac_types = AList.merge (op =) (K true) (fs1, fs2),
     ersatz_table = AList.merge (op =) (K true) (et1, et2),
     codatatypes = AList.merge (op =) (K true) (cs1, cs2)}
)

val name_sep = "$"
val numeral_prefix = nitpick_prefix ^ "num" ^ name_sep
val sel_prefix = nitpick_prefix ^ "sel"
val discr_prefix = nitpick_prefix ^ "is" ^ name_sep
val set_prefix = nitpick_prefix ^ "set" ^ name_sep
val lfp_iterator_prefix = nitpick_prefix ^ "lfpit" ^ name_sep
val gfp_iterator_prefix = nitpick_prefix ^ "gfpit" ^ name_sep
val unrolled_prefix = nitpick_prefix ^ "unroll" ^ name_sep
val base_prefix = nitpick_prefix ^ "base" ^ name_sep
val step_prefix = nitpick_prefix ^ "step" ^ name_sep
val ubfp_prefix = nitpick_prefix ^ "ubfp" ^ name_sep
val lbfp_prefix = nitpick_prefix ^ "lbfp" ^ name_sep
val quot_normal_prefix = nitpick_prefix ^ "qn" ^ name_sep
val skolem_prefix = nitpick_prefix ^ "sk"
val special_prefix = nitpick_prefix ^ "sp"
val uncurry_prefix = nitpick_prefix ^ "unc"
val eval_prefix = nitpick_prefix ^ "eval"
val iter_var_prefix = "i"

(** Constant/type information and term/type manipulation **)

fun sel_prefix_for j = sel_prefix ^ string_of_int j ^ name_sep
fun quot_normal_name_for_type ctxt T =
  quot_normal_prefix ^ unyxml (Syntax.string_of_typ ctxt T)

val strip_first_name_sep =
  Substring.full #> Substring.position name_sep ##> Substring.triml 1
  #> pairself Substring.string
fun original_name s =
  if String.isPrefix nitpick_prefix s then
    case strip_first_name_sep s of (s1, "") => s1 | (_, s2) => original_name s2
  else
    s

fun s_conj (t1, @{const True}) = t1
  | s_conj (@{const True}, t2) = t2
  | s_conj (t1, t2) =
    if t1 = @{const False} orelse t2 = @{const False} then @{const False}
    else HOLogic.mk_conj (t1, t2)
fun s_disj (t1, @{const False}) = t1
  | s_disj (@{const False}, t2) = t2
  | s_disj (t1, t2) =
    if t1 = @{const True} orelse t2 = @{const True} then @{const True}
    else HOLogic.mk_disj (t1, t2)

fun strip_connective conn_t (t as (t0 $ t1 $ t2)) =
    if t0 = conn_t then strip_connective t0 t2 @ strip_connective t0 t1 else [t]
  | strip_connective _ t = [t]
fun strip_any_connective (t as (t0 $ _ $ _)) =
    if t0 = @{const HOL.conj} orelse t0 = @{const HOL.disj} then
      (strip_connective t0 t, t0)
    else
      ([t], @{const Not})
  | strip_any_connective t = ([t], @{const Not})
val conjuncts_of = strip_connective @{const HOL.conj}
val disjuncts_of = strip_connective @{const HOL.disj}

(* When you add constants to these lists, make sure to handle them in
   "Nitpick_Nut.nut_from_term", and perhaps in "Nitpick_Mono.consider_term" as
   well. *)
val built_in_consts =
  [(@{const_name all}, 1),
   (@{const_name "=="}, 2),
   (@{const_name "==>"}, 2),
   (@{const_name Pure.conjunction}, 2),
   (@{const_name Trueprop}, 1),
   (@{const_name Not}, 1),
   (@{const_name False}, 0),
   (@{const_name True}, 0),
   (@{const_name All}, 1),
   (@{const_name Ex}, 1),
   (@{const_name HOL.eq}, 1),
   (@{const_name HOL.conj}, 2),
   (@{const_name HOL.disj}, 2),
   (@{const_name HOL.implies}, 2),
   (@{const_name If}, 3),
   (@{const_name Let}, 2),
   (@{const_name Pair}, 2),
   (@{const_name fst}, 1),
   (@{const_name snd}, 1),
   (@{const_name Set.member}, 2),
   (@{const_name Collect}, 1),
   (@{const_name Id}, 0),
   (@{const_name converse}, 1),
   (@{const_name trancl}, 1),
   (@{const_name relcomp}, 2),
   (@{const_name finite}, 1),
   (@{const_name unknown}, 0),
   (@{const_name is_unknown}, 1),
   (@{const_name safe_The}, 1),
   (@{const_name Frac}, 0),
   (@{const_name norm_frac}, 0)]
val built_in_nat_consts =
  [(@{const_name Suc}, 0),
   (@{const_name nat}, 0),
   (@{const_name nat_gcd}, 0),
   (@{const_name nat_lcm}, 0)]
val built_in_typed_consts =
  [((@{const_name zero_class.zero}, int_T), 0),
   ((@{const_name one_class.one}, int_T), 0),
   ((@{const_name plus_class.plus}, int_T --> int_T --> int_T), 0),
   ((@{const_name minus_class.minus}, int_T --> int_T --> int_T), 0),
   ((@{const_name times_class.times}, int_T --> int_T --> int_T), 0),
   ((@{const_name div_class.div}, int_T --> int_T --> int_T), 0),
   ((@{const_name uminus_class.uminus}, int_T --> int_T), 0),
   ((@{const_name ord_class.less}, int_T --> int_T --> bool_T), 2),
   ((@{const_name ord_class.less_eq}, int_T --> int_T --> bool_T), 2)]
val built_in_typed_nat_consts =
  [((@{const_name zero_class.zero}, nat_T), 0),
   ((@{const_name one_class.one}, nat_T), 0),
   ((@{const_name plus_class.plus}, nat_T --> nat_T --> nat_T), 0),
   ((@{const_name minus_class.minus}, nat_T --> nat_T --> nat_T), 0),
   ((@{const_name times_class.times}, nat_T --> nat_T --> nat_T), 0),
   ((@{const_name div_class.div}, nat_T --> nat_T --> nat_T), 0),
   ((@{const_name ord_class.less}, nat_T --> nat_T --> bool_T), 2),
   ((@{const_name ord_class.less_eq}, nat_T --> nat_T --> bool_T), 2),
   ((@{const_name of_nat}, nat_T --> int_T), 0)]
val built_in_set_like_consts =
  [(@{const_name ord_class.less_eq}, 2)]

fun unarize_type @{typ "unsigned_bit word"} = nat_T
  | unarize_type @{typ "signed_bit word"} = int_T
  | unarize_type (Type (s, Ts as _ :: _)) = Type (s, map unarize_type Ts)
  | unarize_type T = T
fun unarize_unbox_etc_type (Type (@{type_name fun_box}, Ts)) =
    unarize_unbox_etc_type (Type (@{type_name fun}, Ts))
  | unarize_unbox_etc_type (Type (@{type_name pair_box}, Ts)) =
    Type (@{type_name prod}, map unarize_unbox_etc_type Ts)
  | unarize_unbox_etc_type @{typ "unsigned_bit word"} = nat_T
  | unarize_unbox_etc_type @{typ "signed_bit word"} = int_T
  | unarize_unbox_etc_type (Type (s, Ts as _ :: _)) =
    Type (s, map unarize_unbox_etc_type Ts)
  | unarize_unbox_etc_type T = T
fun uniterize_type (Type (s, Ts as _ :: _)) = Type (s, map uniterize_type Ts)
  | uniterize_type @{typ bisim_iterator} = nat_T
  | uniterize_type T = T
val uniterize_unarize_unbox_etc_type = uniterize_type o unarize_unbox_etc_type

fun string_for_type ctxt = Syntax.string_of_typ ctxt o unarize_unbox_etc_type
fun pretty_for_type ctxt = Syntax.pretty_typ ctxt o unarize_unbox_etc_type

val prefix_name = Long_Name.qualify o Long_Name.base_name
fun shortest_name s = List.last (space_explode "." s) handle List.Empty => ""
val prefix_abs_vars = Term.map_abs_vars o prefix_name
fun short_name s =
  case space_explode name_sep s of
    [_] => s |> String.isPrefix nitpick_prefix s ? unprefix nitpick_prefix
  | ss => map shortest_name ss |> space_implode "_"
fun shorten_names_in_type (Type (s, Ts)) =
    Type (short_name s, map shorten_names_in_type Ts)
  | shorten_names_in_type T = T
val shorten_names_in_term =
  map_aterms (fn Const (s, T) => Const (short_name s, T) | t => t)
  #> map_types shorten_names_in_type

fun strict_type_match thy (T1, T2) =
  (Sign.typ_match thy (T2, T1) Vartab.empty; true)
  handle Type.TYPE_MATCH => false
fun type_match thy = strict_type_match thy o pairself unarize_unbox_etc_type
fun const_match thy ((s1, T1), (s2, T2)) =
  s1 = s2 andalso type_match thy (T1, T2)
fun term_match thy (Const x1, Const x2) = const_match thy (x1, x2)
  | term_match thy (Free (s1, T1), Free (s2, T2)) =
    const_match thy ((shortest_name s1, T1), (shortest_name s2, T2))
  | term_match _ (t1, t2) = t1 aconv t2

fun frac_from_term_pair T t1 t2 =
  case snd (HOLogic.dest_number t1) of
    0 => HOLogic.mk_number T 0
  | n1 => case snd (HOLogic.dest_number t2) of
            1 => HOLogic.mk_number T n1
          | n2 => Const (@{const_name divide}, T --> T --> T)
                  $ HOLogic.mk_number T n1 $ HOLogic.mk_number T n2

fun is_TFree (TFree _) = true
  | is_TFree _ = false
fun is_fun_type (Type (@{type_name fun}, _)) = true
  | is_fun_type _ = false
fun is_set_type (Type (@{type_name set}, _)) = true
  | is_set_type _ = false
val is_fun_or_set_type = is_fun_type orf is_set_type
fun is_set_like_type (Type (@{type_name fun}, [_, T'])) =
    (body_type T' = bool_T)
  | is_set_like_type (Type (@{type_name set}, _)) = true
  | is_set_like_type _ = false
fun is_pair_type (Type (@{type_name prod}, _)) = true
  | is_pair_type _ = false
fun is_lfp_iterator_type (Type (s, _)) = String.isPrefix lfp_iterator_prefix s
  | is_lfp_iterator_type _ = false
fun is_gfp_iterator_type (Type (s, _)) = String.isPrefix gfp_iterator_prefix s
  | is_gfp_iterator_type _ = false
val is_fp_iterator_type = is_lfp_iterator_type orf is_gfp_iterator_type
fun is_iterator_type T =
  (T = @{typ bisim_iterator} orelse is_fp_iterator_type T)
fun is_boolean_type T = (T = prop_T orelse T = bool_T)
fun is_integer_type T = (T = nat_T orelse T = int_T)
fun is_bit_type T = (T = @{typ unsigned_bit} orelse T = @{typ signed_bit})
fun is_word_type (Type (@{type_name word}, _)) = true
  | is_word_type _ = false
val is_integer_like_type = is_iterator_type orf is_integer_type orf is_word_type
val is_record_type = not o null o Record.dest_recTs
fun is_frac_type ctxt (Type (s, [])) =
    s |> AList.defined (op =) (#frac_types (Data.get (Context.Proof ctxt)))
  | is_frac_type _ _ = false
fun is_number_type ctxt = is_integer_like_type orf is_frac_type ctxt
fun is_higher_order_type (Type (@{type_name fun}, _)) = true
  | is_higher_order_type (Type (@{type_name set}, _)) = true
  | is_higher_order_type (Type (_, Ts)) = exists is_higher_order_type Ts
  | is_higher_order_type _ = false

fun elem_type (Type (@{type_name set}, [T'])) = T'
  | elem_type T = raise TYPE ("Nitpick_HOL.elem_type", [T], [])
fun pseudo_domain_type (Type (@{type_name fun}, [T1, _])) = T1
  | pseudo_domain_type T = elem_type T
fun pseudo_range_type (Type (@{type_name fun}, [_, T2])) = T2
  | pseudo_range_type (Type (@{type_name set}, _)) = bool_T
  | pseudo_range_type T = raise TYPE ("Nitpick_HOL.pseudo_range_type", [T], [])

fun iterator_type_for_const gfp (s, T) =
  Type ((if gfp then gfp_iterator_prefix else lfp_iterator_prefix) ^ s,
        binder_types T)
fun const_for_iterator_type (Type (s, Ts)) =
    (strip_first_name_sep s |> snd, Ts ---> bool_T)
  | const_for_iterator_type T =
    raise TYPE ("Nitpick_HOL.const_for_iterator_type", [T], [])

fun strip_n_binders 0 T = ([], T)
  | strip_n_binders n (Type (@{type_name fun}, [T1, T2])) =
    strip_n_binders (n - 1) T2 |>> cons T1
  | strip_n_binders n (Type (@{type_name fun_box}, Ts)) =
    strip_n_binders n (Type (@{type_name fun}, Ts))
  | strip_n_binders _ T = raise TYPE ("Nitpick_HOL.strip_n_binders", [T], [])
val nth_range_type = snd oo strip_n_binders

fun num_factors_in_type (Type (@{type_name prod}, [T1, T2])) =
    fold (Integer.add o num_factors_in_type) [T1, T2] 0
  | num_factors_in_type _ = 1
fun num_binder_types (Type (@{type_name fun}, [_, T2])) =
    1 + num_binder_types T2
  | num_binder_types _ = 0
val curried_binder_types = maps HOLogic.flatten_tupleT o binder_types
fun maybe_curried_binder_types T =
  (if is_pair_type (body_type T) then binder_types else curried_binder_types) T

fun mk_flat_tuple _ [t] = t
  | mk_flat_tuple (Type (@{type_name prod}, [T1, T2])) (t :: ts) =
    HOLogic.pair_const T1 T2 $ t $ (mk_flat_tuple T2 ts)
  | mk_flat_tuple T ts = raise TYPE ("Nitpick_HOL.mk_flat_tuple", [T], ts)
fun dest_n_tuple 1 t = [t]
  | dest_n_tuple n t = HOLogic.dest_prod t ||> dest_n_tuple (n - 1) |> op ::

type typedef_info =
  {rep_type: typ, abs_type: typ, Rep_name: string, Abs_name: string,
   set_def: thm option, prop_of_Rep: thm, set_name: string,
   Abs_inverse: thm option, Rep_inverse: thm option}

fun typedef_info ctxt s =
  if is_frac_type ctxt (Type (s, [])) then
    SOME {abs_type = Type (s, []), rep_type = @{typ "int * int"},
          Abs_name = @{const_name Abs_Frac}, Rep_name = @{const_name Rep_Frac},
          set_def = NONE, prop_of_Rep = @{prop "Rep_Frac x \<in> Collect Frac"}
                          |> Logic.varify_global,
          set_name = @{const_name Frac}, Abs_inverse = NONE, Rep_inverse = NONE}
  else case Typedef.get_info ctxt s of
    (* When several entries are returned, it shouldn't matter much which one
       we take (according to Florian Haftmann). *)
    (* The "Logic.varifyT_global" calls are a temporary hack because these
       types's type variables sometimes clash with locally fixed type variables.
       Remove these calls once "Typedef" is fully localized. *)
    ({abs_type, rep_type, Abs_name, Rep_name, ...},
     {set_def, Rep, Abs_inverse, Rep_inverse, ...}) :: _ =>
    SOME {abs_type = Logic.varifyT_global abs_type,
          rep_type = Logic.varifyT_global rep_type, Abs_name = Abs_name,
          Rep_name = Rep_name, set_def = set_def, prop_of_Rep = prop_of Rep,
          set_name = set_prefix ^ s, Abs_inverse = SOME Abs_inverse,
          Rep_inverse = SOME Rep_inverse}
  | _ => NONE

val is_typedef = is_some oo typedef_info
val is_real_datatype = is_some oo Datatype.get_info
fun is_standard_datatype thy = the oo triple_lookup (type_match thy)

(* FIXME: Use antiquotation for "code_numeral" below or detect "rep_datatype",
   e.g., by adding a field to "Datatype_Aux.info". *)
fun is_basic_datatype thy stds s =
  member (op =) [@{type_name prod}, @{type_name set}, @{type_name bool},
                 @{type_name int}, "Code_Numeral.code_numeral"] s orelse
  (s = @{type_name nat} andalso is_standard_datatype thy stds nat_T)

fun repair_constr_type ctxt body_T' T =
  varify_and_instantiate_type ctxt (body_type T) body_T' T

fun register_frac_type_generic frac_s ersaetze generic =
  let
    val {frac_types, ersatz_table, codatatypes} = Data.get generic
    val frac_types = AList.update (op =) (frac_s, ersaetze) frac_types
  in Data.put {frac_types = frac_types, ersatz_table = ersatz_table,
               codatatypes = codatatypes} generic end
(* TODO: Consider morphism. *)
fun register_frac_type frac_s ersaetze (_ : morphism) =
  register_frac_type_generic frac_s ersaetze
val register_frac_type_global = Context.theory_map oo register_frac_type_generic

fun unregister_frac_type_generic frac_s = register_frac_type_generic frac_s []
(* TODO: Consider morphism. *)
fun unregister_frac_type frac_s (_ : morphism) =
  unregister_frac_type_generic frac_s
val unregister_frac_type_global =
  Context.theory_map o unregister_frac_type_generic

fun register_ersatz_generic ersatz generic =
  let
    val {frac_types, ersatz_table, codatatypes} = Data.get generic
    val ersatz_table = AList.merge (op =) (K true) (ersatz_table, ersatz)
  in Data.put {frac_types = frac_types, ersatz_table = ersatz_table,
               codatatypes = codatatypes} generic end
(* TODO: Consider morphism. *)
fun register_ersatz ersatz (_ : morphism) =
  register_ersatz_generic ersatz
val register_ersatz_global = Context.theory_map o register_ersatz_generic

fun register_codatatype_generic co_T case_name constr_xs generic =
  let
    val ctxt = Context.proof_of generic
    val thy = Context.theory_of generic
    val {frac_types, ersatz_table, codatatypes} = Data.get generic
    val constr_xs = map (apsnd (repair_constr_type ctxt co_T)) constr_xs
    val (co_s, co_Ts) = dest_Type co_T
    val _ =
      if forall is_TFree co_Ts andalso not (has_duplicates (op =) co_Ts) andalso
         co_s <> @{type_name fun} andalso
         not (is_basic_datatype thy [(NONE, true)] co_s) then
        ()
      else
        raise TYPE ("Nitpick_HOL.register_codatatype_generic", [co_T], [])
    val codatatypes = AList.update (op =) (co_s, (case_name, constr_xs))
                                   codatatypes
  in Data.put {frac_types = frac_types, ersatz_table = ersatz_table,
               codatatypes = codatatypes} generic end
(* TODO: Consider morphism. *)
fun register_codatatype co_T case_name constr_xs (_ : morphism) =
  register_codatatype_generic co_T case_name constr_xs
val register_codatatype_global =
  Context.theory_map ooo register_codatatype_generic

fun unregister_codatatype_generic co_T = register_codatatype_generic co_T "" []
(* TODO: Consider morphism. *)
fun unregister_codatatype co_T (_ : morphism) =
  unregister_codatatype_generic co_T
val unregister_codatatype_global =
  Context.theory_map o unregister_codatatype_generic

fun is_codatatype ctxt (Type (s, _)) =
    s |> AList.lookup (op =) (#codatatypes (Data.get (Context.Proof ctxt)))
      |> Option.map snd |> these |> null |> not
  | is_codatatype _ _ = false
fun is_real_quot_type ctxt (Type (s, _)) =
    is_some (Quotient_Info.lookup_quotients ctxt s)
  | is_real_quot_type _ _ = false
fun is_quot_type ctxt T =
    is_real_quot_type ctxt T andalso not (is_codatatype ctxt T)
fun is_pure_typedef ctxt (T as Type (s, _)) =
    let val thy = Proof_Context.theory_of ctxt in
      is_typedef ctxt s andalso
      not (is_real_datatype thy s orelse is_real_quot_type ctxt T orelse
           is_codatatype ctxt T orelse is_record_type T orelse
           is_integer_like_type T)
    end
  | is_pure_typedef _ _ = false
fun is_univ_typedef ctxt (Type (s, _)) =
    (case typedef_info ctxt s of
       SOME {set_def, prop_of_Rep, ...} =>
       let
         val t_opt =
           case set_def of
             SOME thm => try (snd o Logic.dest_equals o prop_of) thm
           | NONE => try (snd o HOLogic.dest_mem o HOLogic.dest_Trueprop)
                         prop_of_Rep
       in
         case t_opt of
           SOME (Const (@{const_name top}, _)) => true
           (* "Multiset.multiset" *)
         | SOME (Const (@{const_name Collect}, _)
                 $ Abs (_, _, Const (@{const_name finite}, _) $ _)) => true
           (* "FinFun.finfun" *)
         | SOME (Const (@{const_name Collect}, _) $ Abs (_, _,
                     Const (@{const_name Ex}, _) $ Abs (_, _,
                         Const (@{const_name finite}, _) $ _))) => true
         | _ => false
       end
     | NONE => false)
  | is_univ_typedef _ _ = false
fun is_datatype ctxt stds (T as Type (s, _)) =
    let val thy = Proof_Context.theory_of ctxt in
      (is_typedef ctxt s orelse is_codatatype ctxt T orelse
       T = @{typ ind} orelse is_real_quot_type ctxt T) andalso
      not (is_basic_datatype thy stds s)
    end
  | is_datatype _ _ _ = false

fun all_record_fields thy T =
  let val (recs, more) = Record.get_extT_fields thy T in
    recs @ more :: all_record_fields thy (snd more)
  end
  handle TYPE _ => []
fun is_record_constr (s, T) =
  String.isSuffix Record.extN s andalso
  let val dataT = body_type T in
    is_record_type dataT andalso
    s = unsuffix Record.ext_typeN (fst (dest_Type dataT)) ^ Record.extN
  end
val num_record_fields = Integer.add 1 o length o fst oo Record.get_extT_fields
fun no_of_record_field thy s T1 =
  find_index (curry (op =) s o fst)
             (Record.get_extT_fields thy T1 ||> single |> op @)
fun is_record_get thy (s, Type (@{type_name fun}, [T1, _])) =
    exists (curry (op =) s o fst) (all_record_fields thy T1)
  | is_record_get _ _ = false
fun is_record_update thy (s, T) =
  String.isSuffix Record.updateN s andalso
  exists (curry (op =) (unsuffix Record.updateN s) o fst)
         (all_record_fields thy (body_type T))
  handle TYPE _ => false
fun is_abs_fun ctxt (s, Type (@{type_name fun}, [_, Type (s', _)])) =
    (case typedef_info ctxt s' of
       SOME {Abs_name, ...} => s = Abs_name
     | NONE => false)
  | is_abs_fun _ _ = false
fun is_rep_fun ctxt (s, Type (@{type_name fun}, [Type (s', _), _])) =
    (case typedef_info ctxt s' of
       SOME {Rep_name, ...} => s = Rep_name
     | NONE => false)
  | is_rep_fun _ _ = false
fun is_quot_abs_fun ctxt (x as (_, Type (@{type_name fun},
                                         [_, abs_T as Type (s', _)]))) =
    try (Quotient_Term.absrep_const_chk ctxt Quotient_Term.AbsF) s'
    = SOME (Const x) andalso not (is_codatatype ctxt abs_T)
  | is_quot_abs_fun _ _ = false
fun is_quot_rep_fun ctxt (s, Type (@{type_name fun},
                                   [abs_T as Type (abs_s, _), _])) =
    (case try (Quotient_Term.absrep_const_chk ctxt Quotient_Term.RepF) abs_s of
       SOME (Const (s', _)) => s = s' andalso not (is_codatatype ctxt abs_T)
     | NONE => false)
  | is_quot_rep_fun _ _ = false

fun mate_of_rep_fun ctxt (x as (_, Type (@{type_name fun},
                                         [T1 as Type (s', _), T2]))) =
    (case typedef_info ctxt s' of
       SOME {Abs_name, ...} => (Abs_name, Type (@{type_name fun}, [T2, T1]))
     | NONE => raise TERM ("Nitpick_HOL.mate_of_rep_fun", [Const x]))
  | mate_of_rep_fun _ x = raise TERM ("Nitpick_HOL.mate_of_rep_fun", [Const x])
fun rep_type_for_quot_type ctxt (T as Type (s, _)) =
    let
      val thy = Proof_Context.theory_of ctxt
      val {qtyp, rtyp, ...} = the (Quotient_Info.lookup_quotients ctxt s)
    in
      instantiate_type thy qtyp T rtyp
    end
  | rep_type_for_quot_type _ T =
    raise TYPE ("Nitpick_HOL.rep_type_for_quot_type", [T], [])
fun equiv_relation_for_quot_type thy (Type (s, Ts)) =
    let
      val {qtyp, equiv_rel, equiv_thm, ...} =
        the (Quotient_Info.lookup_quotients thy s)
      val partial =
        case prop_of equiv_thm of
          @{const Trueprop} $ (Const (@{const_name equivp}, _) $ _) => false
        | @{const Trueprop} $ (Const (@{const_name part_equivp}, _) $ _) => true
        | _ => raise NOT_SUPPORTED "Ill-formed quotient type equivalence \
                                   \relation theorem"
      val Ts' = qtyp |> dest_Type |> snd
    in (subst_atomic_types (Ts' ~~ Ts) equiv_rel, partial) end
  | equiv_relation_for_quot_type _ T =
    raise TYPE ("Nitpick_HOL.equiv_relation_for_quot_type", [T], [])

fun is_coconstr ctxt (s, T) =
  case body_type T of
    co_T as Type (co_s, _) =>
    let val {codatatypes, ...} = Data.get (Context.Proof ctxt) in
      exists (fn (s', T') => s = s' andalso repair_constr_type ctxt co_T T' = T)
             (AList.lookup (op =) codatatypes co_s |> Option.map snd |> these)
    end
  | _ => false
fun is_constr_like ctxt (s, T) =
  member (op =) [@{const_name FunBox}, @{const_name PairBox},
                 @{const_name Quot}, @{const_name Zero_Rep},
                 @{const_name Suc_Rep}] s orelse
  let
    val thy = Proof_Context.theory_of ctxt
    val (x as (_, T)) = (s, unarize_unbox_etc_type T)
  in
    is_real_constr thy x orelse is_record_constr x orelse
    (is_abs_fun ctxt x andalso is_pure_typedef ctxt (range_type T)) orelse
    is_coconstr ctxt x
  end
fun is_stale_constr ctxt (x as (_, T)) =
  is_codatatype ctxt (body_type T) andalso is_constr_like ctxt x andalso
  not (is_coconstr ctxt x)
fun is_constr ctxt stds (x as (_, T)) =
  let val thy = Proof_Context.theory_of ctxt in
    is_constr_like ctxt x andalso
    not (is_basic_datatype thy stds
                         (fst (dest_Type (unarize_type (body_type T))))) andalso
    not (is_stale_constr ctxt x)
  end
val is_sel = String.isPrefix discr_prefix orf String.isPrefix sel_prefix
val is_sel_like_and_no_discr =
  String.isPrefix sel_prefix orf
  (member (op =) [@{const_name fst}, @{const_name snd}])

fun in_fun_lhs_for InConstr = InSel
  | in_fun_lhs_for _ = InFunLHS
fun in_fun_rhs_for InConstr = InConstr
  | in_fun_rhs_for InSel = InSel
  | in_fun_rhs_for InFunRHS1 = InFunRHS2
  | in_fun_rhs_for _ = InFunRHS1

fun is_boxing_worth_it (hol_ctxt : hol_context) boxy T =
  case T of
    Type (@{type_name fun}, _) =>
    (boxy = InPair orelse boxy = InFunLHS) andalso
    not (is_boolean_type (body_type T))
  | Type (@{type_name prod}, Ts) =>
    boxy = InPair orelse boxy = InFunRHS1 orelse boxy = InFunRHS2 orelse
    ((boxy = InExpr orelse boxy = InFunLHS) andalso
     exists (is_boxing_worth_it hol_ctxt InPair)
            (map (box_type hol_ctxt InPair) Ts))
  | _ => false
and should_box_type (hol_ctxt as {thy, boxes, ...}) boxy z =
  case triple_lookup (type_match thy) boxes (Type z) of
    SOME (SOME box_me) => box_me
  | _ => is_boxing_worth_it hol_ctxt boxy (Type z)
and box_type hol_ctxt boxy T =
  case T of
    Type (z as (@{type_name fun}, [T1, T2])) =>
    if boxy <> InConstr andalso boxy <> InSel andalso
       should_box_type hol_ctxt boxy z then
      Type (@{type_name fun_box},
            [box_type hol_ctxt InFunLHS T1, box_type hol_ctxt InFunRHS1 T2])
    else
      box_type hol_ctxt (in_fun_lhs_for boxy) T1
      --> box_type hol_ctxt (in_fun_rhs_for boxy) T2
  | Type (z as (@{type_name prod}, Ts)) =>
    if boxy <> InConstr andalso boxy <> InSel
       andalso should_box_type hol_ctxt boxy z then
      Type (@{type_name pair_box}, map (box_type hol_ctxt InSel) Ts)
    else
      Type (@{type_name prod},
            map (box_type hol_ctxt
                          (if boxy = InConstr orelse boxy = InSel then boxy
                           else InPair)) Ts)
  | _ => T

fun binarize_nat_and_int_in_type @{typ nat} = @{typ "unsigned_bit word"}
  | binarize_nat_and_int_in_type @{typ int} = @{typ "signed_bit word"}
  | binarize_nat_and_int_in_type (Type (s, Ts)) =
    Type (s, map binarize_nat_and_int_in_type Ts)
  | binarize_nat_and_int_in_type T = T
val binarize_nat_and_int_in_term = map_types binarize_nat_and_int_in_type

fun discr_for_constr (s, T) = (discr_prefix ^ s, body_type T --> bool_T)

fun num_sels_for_constr_type T = length (maybe_curried_binder_types T)
fun nth_sel_name_for_constr_name s n =
  if s = @{const_name Pair} then
    if n = 0 then @{const_name fst} else @{const_name snd}
  else
    sel_prefix_for n ^ s
fun nth_sel_for_constr x ~1 = discr_for_constr x
  | nth_sel_for_constr (s, T) n =
    (nth_sel_name_for_constr_name s n,
     body_type T --> nth (maybe_curried_binder_types T) n)
fun binarized_and_boxed_nth_sel_for_constr hol_ctxt binarize =
  apsnd ((binarize ? binarize_nat_and_int_in_type) o box_type hol_ctxt InSel)
  oo nth_sel_for_constr

fun sel_no_from_name s =
  if String.isPrefix discr_prefix s then
    ~1
  else if String.isPrefix sel_prefix s then
    s |> unprefix sel_prefix |> Int.fromString |> the
  else if s = @{const_name snd} then
    1
  else
    0

val close_form =
  let
    fun close_up zs zs' =
      fold (fn (z as ((s, _), T)) => fn t' =>
               Logic.all_const T $ Abs (s, T, abstract_over (Var z, t')))
           (take (length zs' - length zs) zs')
    fun aux zs (@{const "==>"} $ t1 $ t2) =
        let val zs' = Term.add_vars t1 zs in
          close_up zs zs' (Logic.mk_implies (t1, aux zs' t2))
        end
      | aux zs t = close_up zs (Term.add_vars t zs) t
  in aux [] end

fun distinctness_formula T =
  all_distinct_unordered_pairs_of
  #> map (fn (t1, t2) => @{const Not} $ (HOLogic.eq_const T $ t1 $ t2))
  #> List.foldr (s_conj o swap) @{const True}

fun zero_const T = Const (@{const_name zero_class.zero}, T)
fun suc_const T = Const (@{const_name Suc}, T --> T)

fun uncached_datatype_constrs ({thy, ctxt, stds, ...} : hol_context)
                              (T as Type (s, Ts)) =
    (case AList.lookup (op =) (#codatatypes (Data.get (Context.Proof ctxt)))
                       s of
       SOME (_, xs' as (_ :: _)) => map (apsnd (repair_constr_type ctxt T)) xs'
     | _ =>
       if is_datatype ctxt stds T then
         case Datatype.get_info thy s of
           SOME {index, descr, ...} =>
           let
             val (_, dtyps, constrs) = AList.lookup (op =) descr index |> the
           in
             map (apsnd (fn Us =>
                            map (typ_of_dtyp descr (dtyps ~~ Ts)) Us ---> T))
                 constrs
           end
         | NONE =>
           if is_record_type T then
             let
               val s' = unsuffix Record.ext_typeN s ^ Record.extN
               val T' = (Record.get_extT_fields thy T
                        |> apsnd single |> uncurry append |> map snd) ---> T
             in [(s', T')] end
           else if is_real_quot_type ctxt T then
             [(@{const_name Quot}, rep_type_for_quot_type ctxt T --> T)]
           else case typedef_info ctxt s of
             SOME {abs_type, rep_type, Abs_name, ...} =>
             [(Abs_name,
               varify_and_instantiate_type ctxt abs_type T rep_type --> T)]
           | NONE =>
             if T = @{typ ind} then
               [dest_Const @{const Zero_Rep}, dest_Const @{const Suc_Rep}]
             else
               []
       else
         [])
  | uncached_datatype_constrs _ _ = []
fun datatype_constrs (hol_ctxt as {constr_cache, ...}) T =
  case AList.lookup (op =) (!constr_cache) T of
    SOME xs => xs
  | NONE =>
    let val xs = uncached_datatype_constrs hol_ctxt T in
      (Unsynchronized.change constr_cache (cons (T, xs)); xs)
    end
fun binarized_and_boxed_datatype_constrs hol_ctxt binarize =
  map (apsnd ((binarize ? binarize_nat_and_int_in_type)
              o box_type hol_ctxt InConstr)) o datatype_constrs hol_ctxt
val num_datatype_constrs = length oo datatype_constrs

fun constr_name_for_sel_like @{const_name fst} = @{const_name Pair}
  | constr_name_for_sel_like @{const_name snd} = @{const_name Pair}
  | constr_name_for_sel_like s' = original_name s'
fun binarized_and_boxed_constr_for_sel hol_ctxt binarize (s', T') =
  let val s = constr_name_for_sel_like s' in
    AList.lookup (op =)
        (binarized_and_boxed_datatype_constrs hol_ctxt binarize (domain_type T'))
        s
    |> the |> pair s
  end

fun card_of_type assigns (Type (@{type_name fun}, [T1, T2])) =
    reasonable_power (card_of_type assigns T2) (card_of_type assigns T1)
  | card_of_type assigns (Type (@{type_name prod}, [T1, T2])) =
    card_of_type assigns T1 * card_of_type assigns T2
  | card_of_type assigns (Type (@{type_name set}, [T'])) =
    reasonable_power 2 (card_of_type assigns T')
  | card_of_type _ (Type (@{type_name itself}, _)) = 1
  | card_of_type _ @{typ prop} = 2
  | card_of_type _ @{typ bool} = 2
  | card_of_type assigns T =
    case AList.lookup (op =) assigns T of
      SOME k => k
    | NONE => if T = @{typ bisim_iterator} then 0
              else raise TYPE ("Nitpick_HOL.card_of_type", [T], [])

fun bounded_card_of_type max default_card assigns
                         (Type (@{type_name fun}, [T1, T2])) =
    let
      val k1 = bounded_card_of_type max default_card assigns T1
      val k2 = bounded_card_of_type max default_card assigns T2
    in
      if k1 = max orelse k2 = max then max
      else Int.min (max, reasonable_power k2 k1)
      handle TOO_LARGE _ => max
    end
  | bounded_card_of_type max default_card assigns
                         (Type (@{type_name prod}, [T1, T2])) =
    let
      val k1 = bounded_card_of_type max default_card assigns T1
      val k2 = bounded_card_of_type max default_card assigns T2
    in if k1 = max orelse k2 = max then max else Int.min (max, k1 * k2) end
  | bounded_card_of_type max default_card assigns
                         (Type (@{type_name set}, [T'])) =
    bounded_card_of_type max default_card assigns (T' --> bool_T)
  | bounded_card_of_type max default_card assigns T =
    Int.min (max, if default_card = ~1 then
                    card_of_type assigns T
                  else
                    card_of_type assigns T
                    handle TYPE ("Nitpick_HOL.card_of_type", _, _) =>
                           default_card)

(* Similar to "ATP_Util.tiny_card_of_type". *)
fun bounded_exact_card_of_type hol_ctxt finitizable_dataTs max default_card
                               assigns T =
  let
    fun aux avoid T =
      (if member (op =) avoid T then
         0
       else if member (op =) finitizable_dataTs T then
         raise SAME ()
       else case T of
         Type (@{type_name fun}, [T1, T2]) =>
         (case (aux avoid T1, aux avoid T2) of
            (_, 1) => 1
          | (0, _) => 0
          | (_, 0) => 0
          | (k1, k2) =>
            if k1 >= max orelse k2 >= max then max
            else Int.min (max, reasonable_power k2 k1))
       | Type (@{type_name prod}, [T1, T2]) =>
         (case (aux avoid T1, aux avoid T2) of
            (0, _) => 0
          | (_, 0) => 0
          | (k1, k2) =>
            if k1 >= max orelse k2 >= max then max
            else Int.min (max, k1 * k2))
       | Type (@{type_name set}, [T']) => aux avoid (T' --> bool_T)
       | Type (@{type_name itself}, _) => 1
       | @{typ prop} => 2
       | @{typ bool} => 2
       | Type _ =>
         (case datatype_constrs hol_ctxt T of
            [] => if is_integer_type T orelse is_bit_type T then 0
                  else raise SAME ()
          | constrs =>
            let
              val constr_cards =
                map (Integer.prod o map (aux (T :: avoid)) o binder_types o snd)
                    constrs
            in
              if exists (curry (op =) 0) constr_cards then 0
              else Int.min (max, Integer.sum constr_cards)
            end)
       | _ => raise SAME ())
      handle SAME () =>
             AList.lookup (op =) assigns T |> the_default default_card
  in Int.min (max, aux [] T) end

val typical_atomic_card = 4
val typical_card_of_type = bounded_card_of_type 16777217 typical_atomic_card []

fun is_finite_type hol_ctxt T =
  bounded_exact_card_of_type hol_ctxt [] 1 2 [] T > 0

fun is_special_eligible_arg strict Ts t =
  case map snd (Term.add_vars t []) @ map (nth Ts) (loose_bnos t) of
    [] => true
  | bad_Ts =>
    let
      val bad_Ts_cost =
        if strict then fold (curry (op *) o typical_card_of_type) bad_Ts 1
        else fold (Integer.max o typical_card_of_type) bad_Ts 0
      val T_cost = typical_card_of_type (fastype_of1 (Ts, t))
    in (bad_Ts_cost, T_cost) |> (if strict then op < else op <=) end

fun abs_var ((s, j), T) body = Abs (s, T, abstract_over (Var ((s, j), T), body))

fun let_var s = (nitpick_prefix ^ s, 999)
val let_inline_threshold = 20

fun s_let Ts s n abs_T body_T f t =
  if (n - 1) * (size_of_term t - 1) <= let_inline_threshold orelse
     is_special_eligible_arg false Ts t then
    f t
  else
    let val z = (let_var s, abs_T) in
      Const (@{const_name Let}, abs_T --> (abs_T --> body_T) --> body_T)
      $ t $ abs_var z (incr_boundvars 1 (f (Var z)))
    end

fun loose_bvar1_count (Bound i, k) = if i = k then 1 else 0
  | loose_bvar1_count (t1 $ t2, k) =
    loose_bvar1_count (t1, k) + loose_bvar1_count (t2, k)
  | loose_bvar1_count (Abs (_, _, t), k) = loose_bvar1_count (t, k + 1)
  | loose_bvar1_count _ = 0

fun s_betapply _ (t1 as Const (@{const_name "=="}, _) $ t1', t2) =
    if t1' aconv t2 then @{prop True} else t1 $ t2
  | s_betapply _ (t1 as Const (@{const_name HOL.eq}, _) $ t1', t2) =
    if t1' aconv t2 then @{term True} else t1 $ t2
  | s_betapply _ (Const (@{const_name If}, _) $ @{const True} $ t1', _) = t1'
  | s_betapply _ (Const (@{const_name If}, _) $ @{const False} $ _, t2) = t2
  | s_betapply Ts (Const (@{const_name Let},
                          Type (_, [bound_T, Type (_, [_, body_T])]))
                   $ t12 $ Abs (s, T, t13'), t2) =
    let val body_T' = range_type body_T in
      Const (@{const_name Let}, bound_T --> (bound_T --> body_T') --> body_T')
      $ t12 $ Abs (s, T, s_betapply (T :: Ts) (t13', incr_boundvars 1 t2))
    end
  | s_betapply Ts (t1 as Abs (s1, T1, t1'), t2) =
    (s_let Ts s1 (loose_bvar1_count (t1', 0)) T1 (fastype_of1 (T1 :: Ts, t1'))
           (curry betapply t1) t2
     (* FIXME: fix all "s_betapply []" calls *)
     handle TERM _ => betapply (t1, t2)
          | General.Subscript => betapply (t1, t2))
  | s_betapply _ (t1, t2) = t1 $ t2
fun s_betapplys Ts = Library.foldl (s_betapply Ts)

fun s_beta_norm Ts t =
  let
    fun aux _ (Var _) = raise Same.SAME
      | aux Ts (Abs (s, T, t')) = Abs (s, T, aux (T :: Ts) t')
      | aux Ts ((t1 as Abs _) $ t2) =
        Same.commit (aux Ts) (s_betapply Ts (t1, t2))
      | aux Ts (t1 $ t2) =
        ((case aux Ts t1 of
           t1 as Abs _ => Same.commit (aux Ts) (s_betapply Ts (t1, t2))
         | t1 => t1 $ Same.commit (aux Ts) t2)
        handle Same.SAME => t1 $ aux Ts t2)
      | aux _ _ = raise Same.SAME
  in aux Ts t handle Same.SAME => t end

fun discr_term_for_constr hol_ctxt (x as (s, T)) =
  let val dataT = body_type T in
    if s = @{const_name Suc} then
      Abs (Name.uu, dataT,
           @{const Not} $ HOLogic.mk_eq (zero_const dataT, Bound 0))
    else if num_datatype_constrs hol_ctxt dataT >= 2 then
      Const (discr_for_constr x)
    else
      Abs (Name.uu, dataT, @{const True})
  end
fun discriminate_value (hol_ctxt as {ctxt, ...}) x t =
  case head_of t of
    Const x' =>
    if x = x' then @{const True}
    else if is_constr_like ctxt x' then @{const False}
    else s_betapply [] (discr_term_for_constr hol_ctxt x, t)
  | _ => s_betapply [] (discr_term_for_constr hol_ctxt x, t)

fun nth_arg_sel_term_for_constr thy stds (x as (s, T)) n =
  let val (arg_Ts, dataT) = strip_type T in
    if dataT = nat_T andalso is_standard_datatype thy stds nat_T then
      @{term "%n::nat. n - 1"}
    else if is_pair_type dataT then
      Const (nth_sel_for_constr x n)
    else
      let
        fun aux m (Type (@{type_name prod}, [T1, T2])) =
            let
              val (m, t1) = aux m T1
              val (m, t2) = aux m T2
            in (m, HOLogic.mk_prod (t1, t2)) end
          | aux m T =
            (m + 1, Const (nth_sel_name_for_constr_name s m, dataT --> T)
                    $ Bound 0)
        val m = fold (Integer.add o num_factors_in_type)
                     (List.take (arg_Ts, n)) 0
      in Abs ("x", dataT, aux m (nth arg_Ts n) |> snd) end
  end
fun select_nth_constr_arg ctxt stds x t n res_T =
  let val thy = Proof_Context.theory_of ctxt in
    (case strip_comb t of
       (Const x', args) =>
       if x = x' then nth args n
       else if is_constr_like ctxt x' then Const (@{const_name unknown}, res_T)
       else raise SAME ()
     | _ => raise SAME())
    handle SAME () =>
           s_betapply [] (nth_arg_sel_term_for_constr thy stds x n, t)
  end

fun construct_value _ _ x [] = Const x
  | construct_value ctxt stds (x as (s, _)) args =
    let val args = map Envir.eta_contract args in
      case hd args of
        Const (s', _) $ t =>
        if is_sel_like_and_no_discr s' andalso
           constr_name_for_sel_like s' = s andalso
           forall (fn (n, t') =>
                      select_nth_constr_arg ctxt stds x t n dummyT = t')
                  (index_seq 0 (length args) ~~ args) then
          t
        else
          list_comb (Const x, args)
      | _ => list_comb (Const x, args)
    end

fun constr_expand (hol_ctxt as {ctxt, stds, ...}) T t =
  (case head_of t of
     Const x => if is_constr_like ctxt x then t else raise SAME ()
   | _ => raise SAME ())
  handle SAME () =>
         let
           val x' as (_, T') =
             if is_pair_type T then
               let val (T1, T2) = HOLogic.dest_prodT T in
                 (@{const_name Pair}, T1 --> T2 --> T)
               end
             else
               datatype_constrs hol_ctxt T |> hd
           val arg_Ts = binder_types T'
         in
           list_comb (Const x', map2 (select_nth_constr_arg ctxt stds x' t)
                                     (index_seq 0 (length arg_Ts)) arg_Ts)
         end

fun coerce_bound_no f j t =
  case t of
    t1 $ t2 => coerce_bound_no f j t1 $ coerce_bound_no f j t2
  | Abs (s, T, t') => Abs (s, T, coerce_bound_no f (j + 1) t')
  | Bound j' => if j' = j then f t else t
  | _ => t
fun coerce_bound_0_in_term hol_ctxt new_T old_T =
  old_T <> new_T ? coerce_bound_no (coerce_term hol_ctxt [new_T] old_T new_T) 0
and coerce_term (hol_ctxt as {ctxt, stds, ...}) Ts new_T old_T t =
  if old_T = new_T then
    t
  else
    case (new_T, old_T) of
      (Type (new_s, new_Ts as [new_T1, new_T2]),
       Type (@{type_name fun}, [old_T1, old_T2])) =>
      (case eta_expand Ts t 1 of
         Abs (s, _, t') =>
         Abs (s, new_T1,
              t' |> coerce_bound_0_in_term hol_ctxt new_T1 old_T1
                 |> coerce_term hol_ctxt (new_T1 :: Ts) new_T2 old_T2)
         |> Envir.eta_contract
         |> new_s <> @{type_name fun}
            ? construct_value ctxt stds
                  (@{const_name FunBox},
                   Type (@{type_name fun}, new_Ts) --> new_T)
              o single
       | t' => raise TERM ("Nitpick_HOL.coerce_term", [t']))
    | (Type (new_s, new_Ts as [new_T1, new_T2]),
       Type (old_s, old_Ts as [old_T1, old_T2])) =>
      if old_s = @{type_name fun_box} orelse
         old_s = @{type_name pair_box} orelse old_s = @{type_name prod} then
        case constr_expand hol_ctxt old_T t of
          Const (old_s, _) $ t1 =>
          if new_s = @{type_name fun} then
            coerce_term hol_ctxt Ts new_T (Type (@{type_name fun}, old_Ts)) t1
          else
            construct_value ctxt stds
                (old_s, Type (@{type_name fun}, new_Ts) --> new_T)
                [coerce_term hol_ctxt Ts (Type (@{type_name fun}, new_Ts))
                             (Type (@{type_name fun}, old_Ts)) t1]
        | Const _ $ t1 $ t2 =>
          construct_value ctxt stds
              (if new_s = @{type_name prod} then @{const_name Pair}
               else @{const_name PairBox}, new_Ts ---> new_T)
              (map3 (coerce_term hol_ctxt Ts) [new_T1, new_T2] [old_T1, old_T2]
                    [t1, t2])
        | t' => raise TERM ("Nitpick_HOL.coerce_term", [t'])
      else
        raise TYPE ("Nitpick_HOL.coerce_term", [new_T, old_T], [t])
    | _ => raise TYPE ("Nitpick_HOL.coerce_term", [new_T, old_T], [t])

fun is_ground_term (t1 $ t2) = is_ground_term t1 andalso is_ground_term t2
  | is_ground_term (Const _) = true
  | is_ground_term _ = false

fun special_bounds ts =
  fold Term.add_vars ts [] |> sort (Term_Ord.fast_indexname_ord o pairself fst)

(* FIXME: detect "rep_datatype"? *)
fun is_funky_typedef_name ctxt s =
  member (op =) [@{type_name unit}, @{type_name prod}, @{type_name set},
                 @{type_name Sum_Type.sum}, @{type_name int}] s orelse
  is_frac_type ctxt (Type (s, []))
fun is_funky_typedef ctxt (Type (s, _)) = is_funky_typedef_name ctxt s
  | is_funky_typedef _ _ = false
fun is_typedef_axiom ctxt boring (@{const "==>"} $ _ $ t2) =
    is_typedef_axiom ctxt boring t2
  | is_typedef_axiom ctxt boring
        (@{const Trueprop} $ (Const (@{const_name Typedef.type_definition}, _)
         $ Const (_, Type (@{type_name fun}, [Type (s, _), _]))
         $ Const _ $ _)) =
    boring <> is_funky_typedef_name ctxt s andalso is_typedef ctxt s
  | is_typedef_axiom _ _ _ = false

fun all_defs_of thy subst =
  let
    val def_names =
      thy |> Theory.defs_of
          |> Defs.all_specifications_of
          |> maps snd |> map_filter #def
          |> Ord_List.make fast_string_ord
  in
    Theory.nodes_of thy
    |> maps Thm.axioms_of
    |> map (apsnd (subst_atomic subst o prop_of))
    |> sort (fast_string_ord o pairself fst)
    |> Ord_List.inter (fast_string_ord o apsnd fst) def_names
    |> map snd
  end

(* Ideally we would check against "Complex_Main", not "Refute", but any theory
   will do as long as it contains all the "axioms" and "axiomatization"
   commands. *)
fun is_built_in_theory thy = Theory.subthy (thy, @{theory Refute})

fun all_nondefs_of ctxt subst =
  ctxt |> Spec_Rules.get
       |> filter (curry (op =) Spec_Rules.Unknown o fst)
       |> maps (snd o snd)
       |> filter_out (is_built_in_theory o theory_of_thm)
       |> map (subst_atomic subst o prop_of)

fun arity_of_built_in_const thy stds (s, T) =
  if s = @{const_name If} then
    if nth_range_type 3 T = @{typ bool} then NONE else SOME 3
  else
    let val std_nats = is_standard_datatype thy stds nat_T in
      case AList.lookup (op =)
                    (built_in_consts
                     |> std_nats ? append built_in_nat_consts) s of
        SOME n => SOME n
      | NONE =>
        case AList.lookup (op =)
                 (built_in_typed_consts
                  |> std_nats ? append built_in_typed_nat_consts)
                 (s, unarize_type T) of
          SOME n => SOME n
        | NONE =>
          case s of
            @{const_name zero_class.zero} =>
            if is_iterator_type T then SOME 0 else NONE
          | @{const_name Suc} =>
            if is_iterator_type (domain_type T) then SOME 0 else NONE
          | _ => if is_fun_type T andalso is_set_like_type (domain_type T) then
                   AList.lookup (op =) built_in_set_like_consts s
                 else
                   NONE
    end
val is_built_in_const = is_some ooo arity_of_built_in_const

(* This function is designed to work for both real definition axioms and
   simplification rules (equational specifications). *)
fun term_under_def t =
  case t of
    @{const "==>"} $ _ $ t2 => term_under_def t2
  | Const (@{const_name "=="}, _) $ t1 $ _ => term_under_def t1
  | @{const Trueprop} $ t1 => term_under_def t1
  | Const (@{const_name HOL.eq}, _) $ t1 $ _ => term_under_def t1
  | Abs (_, _, t') => term_under_def t'
  | t1 $ _ => term_under_def t1
  | _ => t

(* Here we crucially rely on "specialize_type" performing a preorder traversal
   of the term, without which the wrong occurrence of a constant could be
   matched in the face of overloading. *)
fun def_props_for_const thy stds table (x as (s, _)) =
  if is_built_in_const thy stds x then
    []
  else
    these (Symtab.lookup table s)
    |> map_filter (try (specialize_type thy x))
    |> filter (curry (op =) (Const x) o term_under_def)

fun normalized_rhs_of t =
  let
    fun aux (v as Var _) (SOME t) = SOME (lambda v t)
      | aux (c as Const (@{const_name TYPE}, _)) (SOME t) = SOME (lambda c t)
      | aux _ _ = NONE
    val (lhs, rhs) =
      case t of
        Const (@{const_name "=="}, _) $ t1 $ t2 => (t1, t2)
      | @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ t1 $ t2) =>
        (t1, t2)
      | _ => raise TERM ("Nitpick_HOL.normalized_rhs_of", [t])
    val args = strip_comb lhs |> snd
  in fold_rev aux args (SOME rhs) end

fun get_def_of_const thy table (x as (s, _)) =
  x |> def_props_for_const thy [(NONE, false)] table |> List.last
    |> normalized_rhs_of |> Option.map (prefix_abs_vars s)
  handle List.Empty => NONE

fun def_of_const_ext thy (unfold_table, fallback_table) (x as (s, _)) =
  if is_built_in_const thy [(NONE, false)] x orelse original_name s <> s then
    NONE
  else case get_def_of_const thy unfold_table x of
    SOME def => SOME (true, def)
  | NONE => get_def_of_const thy fallback_table x |> Option.map (pair false)

val def_of_const = Option.map snd ooo def_of_const_ext

fun fixpoint_kind_of_rhs (Abs (_, _, t)) = fixpoint_kind_of_rhs t
  | fixpoint_kind_of_rhs (Const (@{const_name lfp}, _) $ Abs _) = Lfp
  | fixpoint_kind_of_rhs (Const (@{const_name gfp}, _) $ Abs _) = Gfp
  | fixpoint_kind_of_rhs _ = NoFp

fun is_mutually_inductive_pred_def thy table t =
  let
    fun is_good_arg (Bound _) = true
      | is_good_arg (Const (s, _)) =
        s = @{const_name True} orelse s = @{const_name False} orelse
        s = @{const_name undefined}
      | is_good_arg _ = false
  in
    case t |> strip_abs_body |> strip_comb of
      (Const x, ts as (_ :: _)) =>
      (case def_of_const thy table x of
         SOME t' => fixpoint_kind_of_rhs t' <> NoFp andalso
                    forall is_good_arg ts
       | NONE => false)
    | _ => false
  end
fun unfold_mutually_inductive_preds thy table =
  map_aterms (fn t as Const x =>
                 (case def_of_const thy table x of
                    SOME t' =>
                    let val t' = Envir.eta_contract t' in
                      if is_mutually_inductive_pred_def thy table t' then t'
                      else t
                    end
                 | NONE => t)
               | t => t)

fun case_const_names ctxt stds =
  let val thy = Proof_Context.theory_of ctxt in
    Symtab.fold (fn (dtype_s, {index, descr, case_name, ...}) =>
                    if is_basic_datatype thy stds dtype_s then
                      I
                    else
                      cons (case_name, AList.lookup (op =) descr index
                                       |> the |> #3 |> length))
                (Datatype.get_all thy) [] @
    map (apsnd length o snd) (#codatatypes (Data.get (Context.Proof ctxt)))
  end

fun fixpoint_kind_of_const thy table x =
  if is_built_in_const thy [(NONE, false)] x then NoFp
  else fixpoint_kind_of_rhs (the (def_of_const thy table x))
  handle Option.Option => NoFp

fun is_real_inductive_pred ({thy, stds, def_tables, intro_table, ...}
                            : hol_context) x =
  fixpoint_kind_of_const thy def_tables x <> NoFp andalso
  not (null (def_props_for_const thy stds intro_table x))
fun is_inductive_pred hol_ctxt (x as (s, _)) =
  is_real_inductive_pred hol_ctxt x orelse String.isPrefix ubfp_prefix s orelse
  String.isPrefix lbfp_prefix s

fun lhs_of_equation t =
  case t of
    Const (@{const_name all}, _) $ Abs (_, _, t1) => lhs_of_equation t1
  | Const (@{const_name "=="}, _) $ t1 $ _ => SOME t1
  | @{const "==>"} $ _ $ t2 => lhs_of_equation t2
  | @{const Trueprop} $ t1 => lhs_of_equation t1
  | Const (@{const_name All}, _) $ Abs (_, _, t1) => lhs_of_equation t1
  | Const (@{const_name HOL.eq}, _) $ t1 $ _ => SOME t1
  | @{const HOL.implies} $ _ $ t2 => lhs_of_equation t2
  | _ => NONE
fun is_constr_pattern _ (Bound _) = true
  | is_constr_pattern _ (Var _) = true
  | is_constr_pattern ctxt t =
    case strip_comb t of
      (Const x, args) =>
      is_constr_like ctxt x andalso forall (is_constr_pattern ctxt) args
    | _ => false
fun is_constr_pattern_lhs ctxt t =
  forall (is_constr_pattern ctxt) (snd (strip_comb t))
fun is_constr_pattern_formula ctxt t =
  case lhs_of_equation t of
    SOME t' => is_constr_pattern_lhs ctxt t'
  | NONE => false

(* Similar to "specialize_type" but returns all matches rather than only the
   first (preorder) match. *)
fun multi_specialize_type thy slack (s, T) t =
  let
    fun aux (Const (s', T')) ys =
        if s = s' then
          ys |> (if AList.defined (op =) ys T' then
                   I
                 else
                   cons (T', monomorphic_term (Sign.typ_match thy (T', T)
                                                              Vartab.empty) t)
                   handle Type.TYPE_MATCH => I
                        | TERM _ =>
                          if slack then
                            I
                          else
                            raise NOT_SUPPORTED
                                      ("too much polymorphism in axiom \"" ^
                                       Syntax.string_of_term_global thy t ^
                                       "\" involving " ^ quote s))
        else
          ys
      | aux _ ys = ys
  in map snd (fold_aterms aux t []) end
fun nondef_props_for_const thy slack table (x as (s, _)) =
  these (Symtab.lookup table s) |> maps (multi_specialize_type thy slack x)

fun unvarify_term (t1 $ t2) = unvarify_term t1 $ unvarify_term t2
  | unvarify_term (Var ((s, 0), T)) = Free (s, T)
  | unvarify_term (Abs (s, T, t')) = Abs (s, T, unvarify_term t')
  | unvarify_term t = t
fun axiom_for_choice_spec thy =
  unvarify_term
  #> Object_Logic.atomize_term thy
  #> Choice_Specification.close_form
  #> HOLogic.mk_Trueprop
fun is_choice_spec_fun ({thy, def_tables, nondef_table, choice_spec_table, ...}
                        : hol_context) x =
  case nondef_props_for_const thy true choice_spec_table x of
    [] => false
  | ts => case def_of_const thy def_tables x of
            SOME (Const (@{const_name Eps}, _) $ _) => true
          | SOME _ => false
          | NONE =>
            let val ts' = nondef_props_for_const thy true nondef_table x in
              length ts' = length ts andalso
              forall (fn t =>
                         exists (curry (op aconv) (axiom_for_choice_spec thy t))
                                ts') ts
            end

fun is_choice_spec_axiom thy choice_spec_table t =
  Symtab.exists (fn (_, ts) =>
                    exists (curry (op aconv) t o axiom_for_choice_spec thy) ts)
                choice_spec_table

fun is_real_equational_fun ({thy, stds, simp_table, psimp_table, ...}
                            : hol_context) x =
  exists (fn table => not (null (def_props_for_const thy stds table x)))
         [!simp_table, psimp_table]
fun is_equational_fun_but_no_plain_def hol_ctxt =
  is_real_equational_fun hol_ctxt orf is_inductive_pred hol_ctxt

(** Constant unfolding **)

fun constr_case_body ctxt stds Ts (func_t, (x as (_, T))) =
  let val arg_Ts = binder_types T in
    s_betapplys Ts (func_t, map2 (select_nth_constr_arg ctxt stds x (Bound 0))
                                 (index_seq 0 (length arg_Ts)) arg_Ts)
  end
fun add_constr_case res_T (body_t, guard_t) res_t =
  if res_T = bool_T then
    s_conj (HOLogic.mk_imp (guard_t, body_t), res_t)
  else
    Const (@{const_name If}, bool_T --> res_T --> res_T --> res_T)
    $ guard_t $ body_t $ res_t
fun optimized_case_def (hol_ctxt as {ctxt, stds, ...}) Ts dataT res_T func_ts =
  let
    val xs = datatype_constrs hol_ctxt dataT
    val cases =
      func_ts ~~ xs
      |> map (fn (func_t, x) =>
                 (constr_case_body ctxt stds (dataT :: Ts)
                                   (incr_boundvars 1 func_t, x),
                  discriminate_value hol_ctxt x (Bound 0)))
      |> AList.group (op aconv)
      |> map (apsnd (List.foldl s_disj @{const False}))
      |> sort (int_ord o pairself (size_of_term o snd))
      |> rev
  in
    if res_T = bool_T then
      if forall (member (op =) [@{const False}, @{const True}] o fst) cases then
        case cases of
          [(body_t, _)] => body_t
        | [_, (@{const True}, head_t2)] => head_t2
        | [_, (@{const False}, head_t2)] => @{const Not} $ head_t2
        | _ => raise BAD ("Nitpick_HOL.optimized_case_def", "impossible cases")
      else
        @{const True} |> fold_rev (add_constr_case res_T) cases
    else
      fst (hd cases) |> fold_rev (add_constr_case res_T) (tl cases)
  end
  |> absdummy dataT

fun optimized_record_get (hol_ctxt as {thy, ctxt, stds, ...}) s rec_T res_T t =
  let val constr_x = hd (datatype_constrs hol_ctxt rec_T) in
    case no_of_record_field thy s rec_T of
      ~1 => (case rec_T of
               Type (_, Ts as _ :: _) =>
               let
                 val rec_T' = List.last Ts
                 val j = num_record_fields thy rec_T - 1
               in
                 select_nth_constr_arg ctxt stds constr_x t j res_T
                 |> optimized_record_get hol_ctxt s rec_T' res_T
               end
             | _ => raise TYPE ("Nitpick_HOL.optimized_record_get", [rec_T],
                                []))
    | j => select_nth_constr_arg ctxt stds constr_x t j res_T
  end
fun optimized_record_update (hol_ctxt as {thy, ctxt, stds, ...}) s rec_T fun_t
                            rec_t =
  let
    val constr_x as (_, constr_T) = hd (datatype_constrs hol_ctxt rec_T)
    val Ts = binder_types constr_T
    val n = length Ts
    val special_j = no_of_record_field thy s rec_T
    val ts =
      map2 (fn j => fn T =>
               let val t = select_nth_constr_arg ctxt stds constr_x rec_t j T in
                 if j = special_j then
                   s_betapply [] (fun_t, t)
                 else if j = n - 1 andalso special_j = ~1 then
                   optimized_record_update hol_ctxt s
                       (rec_T |> dest_Type |> snd |> List.last) fun_t t
                 else
                   t
               end) (index_seq 0 n) Ts
  in list_comb (Const constr_x, ts) end

(* Prevents divergence in case of cyclic or infinite definition dependencies. *)
val unfold_max_depth = 255

(* Inline definitions or define as an equational constant? Booleans tend to
   benefit more from inlining, due to the polarity analysis. (However, if
   "total_consts" is set, the polarity analysis is likely not to be so
   crucial.) *)
val def_inline_threshold_for_booleans = 60
val def_inline_threshold_for_non_booleans = 20

fun unfold_defs_in_term
        (hol_ctxt as {thy, ctxt, stds, whacks, total_consts, case_names,
                      def_tables, ground_thm_table, ersatz_table, ...}) =
  let
    fun do_numeral depth Ts mult T t0 t1 =
      (if is_number_type ctxt T then
         let
           val j = mult * (HOLogic.dest_num t1)
                   |> T = nat_T ? Integer.max 0
           val s = numeral_prefix ^ signed_string_of_int j
         in
           if is_integer_like_type T then
             if is_standard_datatype thy stds T then Const (s, T)
             else funpow j (curry (op $) (suc_const T)) (zero_const T)
           else
             do_term depth Ts (Const (@{const_name of_int}, int_T --> T)
                               $ Const (s, int_T))
         end
         handle TERM _ => raise SAME ()
       else
         raise SAME ())
      handle SAME () => s_betapply [] (do_term depth Ts t0, do_term depth Ts t1)
    and do_term depth Ts t =
      case t of
        (t0 as Const (@{const_name Num.neg_numeral_class.neg_numeral},
                      Type (@{type_name fun}, [_, ran_T]))) $ t1 =>
        do_numeral depth Ts ~1 ran_T t0 t1
      | (t0 as Const (@{const_name Num.numeral_class.numeral},
                      Type (@{type_name fun}, [_, ran_T]))) $ t1 =>
        do_numeral depth Ts 1 ran_T t0 t1
      | Const (@{const_name refl_on}, T) $ Const (@{const_name top}, _) $ t2 =>
        do_const depth Ts t (@{const_name refl'}, range_type T) [t2]
      | (t0 as Const (@{const_name Sigma}, Type (_, [T1, Type (_, [T2, T3])])))
        $ t1 $ (t2 as Abs (_, _, t2')) =>
        if loose_bvar1 (t2', 0) then
          s_betapplys Ts (do_term depth Ts t0, map (do_term depth Ts) [t1, t2])
        else
          do_term depth Ts
                  (Const (@{const_name prod}, T1 --> range_type T2 --> T3)
                   $ t1 $ incr_boundvars ~1 t2')
      | Const (x as (@{const_name distinct},
               Type (@{type_name fun}, [Type (@{type_name list}, [T']), _])))
        $ (t1 as _ $ _) =>
        (t1 |> HOLogic.dest_list |> distinctness_formula T'
         handle TERM _ => do_const depth Ts t x [t1])
      | Const (x as (@{const_name If}, _)) $ t1 $ t2 $ t3 =>
        if is_ground_term t1 andalso
           exists (Pattern.matches thy o rpair t1)
                  (Inttab.lookup_list ground_thm_table (hash_term t1)) then
          do_term depth Ts t2
        else
          do_const depth Ts t x [t1, t2, t3]
      | Const (@{const_name Let}, _) $ t1 $ t2 =>
        s_betapply Ts (pairself (do_term depth Ts) (t2, t1))
      | Const x => do_const depth Ts t x []
      | t1 $ t2 =>
        (case strip_comb t of
           (Const x, ts) => do_const depth Ts t x ts
         | _ => s_betapply [] (do_term depth Ts t1, do_term depth Ts t2))
      | Bound _ => t
      | Abs (s, T, body) => Abs (s, T, do_term depth (T :: Ts) body)
      | _ => if member (term_match thy) whacks t then
               Const (@{const_name unknown}, fastype_of1 (Ts, t))
             else
               t
    and select_nth_constr_arg_with_args _ _ (x as (_, T)) [] n res_T =
        (Abs (Name.uu, body_type T,
              select_nth_constr_arg ctxt stds x (Bound 0) n res_T), [])
      | select_nth_constr_arg_with_args depth Ts x (t :: ts) n res_T =
        (select_nth_constr_arg ctxt stds x (do_term depth Ts t) n res_T, ts)
    and quot_rep_of depth Ts abs_T rep_T ts =
      select_nth_constr_arg_with_args depth Ts
          (@{const_name Quot}, rep_T --> abs_T) ts 0 rep_T
    and do_const depth Ts t (x as (s, T)) ts =
      if member (term_match thy) whacks (Const x) then
        Const (@{const_name unknown}, fastype_of1 (Ts, t))
      else case AList.lookup (op =) ersatz_table s of
        SOME s' =>
        do_const (depth + 1) Ts (list_comb (Const (s', T), ts)) (s', T) ts
      | NONE =>
        let
          fun def_inline_threshold () =
            if is_boolean_type (nth_range_type (length ts) T) andalso
               total_consts <> SOME true then
              def_inline_threshold_for_booleans
            else
              def_inline_threshold_for_non_booleans
          val (const, ts) =
            if is_built_in_const thy stds x then
              (Const x, ts)
            else case AList.lookup (op =) case_names s of
              SOME n =>
              if length ts < n then
                (do_term depth Ts (eta_expand Ts t (n - length ts)), [])
              else
                let
                  val (dataT, res_T) = nth_range_type n T
                                       |> pairf domain_type range_type
                in
                  (optimized_case_def hol_ctxt Ts dataT res_T
                                      (map (do_term depth Ts) (take n ts)),
                   drop n ts)
                end
            | _ =>
              if is_constr ctxt stds x then
                (Const x, ts)
              else if is_stale_constr ctxt x then
                raise NOT_SUPPORTED ("(non-co)constructors of codatatypes \
                                     \(\"" ^ s ^ "\")")
              else if is_quot_abs_fun ctxt x then
                let
                  val rep_T = domain_type T
                  val abs_T = range_type T
                in
                  (Abs (Name.uu, rep_T,
                        Const (@{const_name Quot}, rep_T --> abs_T)
                               $ (Const (quot_normal_name_for_type ctxt abs_T,
                                         rep_T --> rep_T) $ Bound 0)), ts)
                end
              else if is_quot_rep_fun ctxt x then
                quot_rep_of depth Ts (domain_type T) (range_type T) ts
              else if is_record_get thy x then
                case length ts of
                  0 => (do_term depth Ts (eta_expand Ts t 1), [])
                | _ => (optimized_record_get hol_ctxt s (domain_type T)
                            (range_type T) (do_term depth Ts (hd ts)), tl ts)
              else if is_record_update thy x then
                case length ts of
                  2 => (optimized_record_update hol_ctxt
                            (unsuffix Record.updateN s) (nth_range_type 2 T)
                            (do_term depth Ts (hd ts))
                            (do_term depth Ts (nth ts 1)), [])
                | n => (do_term depth Ts (eta_expand Ts t (2 - n)), [])
              else if is_abs_fun ctxt x andalso
                      is_quot_type ctxt (range_type T) then
                let
                  val abs_T = range_type T
                  val rep_T = elem_type (domain_type T)
                  val eps_fun = Const (@{const_name Eps},
                                       (rep_T --> bool_T) --> rep_T)
                  val normal_fun =
                    Const (quot_normal_name_for_type ctxt abs_T,
                           rep_T --> rep_T)
                  val abs_fun = Const (@{const_name Quot}, rep_T --> abs_T)
                  val pred =
                    Abs (Name.uu, rep_T,
                         Const (@{const_name Set.member},
                                rep_T --> domain_type T --> bool_T)
                         $ Bound 0 $ Bound 1)
                in
                  (Abs (Name.uu, HOLogic.mk_setT rep_T,
                        abs_fun $ (normal_fun $ (eps_fun $ pred)))
                   |> do_term (depth + 1) Ts, ts)
                end
              else if is_rep_fun ctxt x then
                let val x' = mate_of_rep_fun ctxt x in
                  if is_constr ctxt stds x' then
                    select_nth_constr_arg_with_args depth Ts x' ts 0
                                                    (range_type T)
                  else if is_quot_type ctxt (domain_type T) then
                    let
                      val abs_T = domain_type T
                      val rep_T = elem_type (range_type T)
                      val (rep_fun, _) = quot_rep_of depth Ts abs_T rep_T []
                      val (equiv_rel, _) =
                        equiv_relation_for_quot_type ctxt abs_T
                    in
                      (Abs (Name.uu, abs_T,
                            HOLogic.Collect_const rep_T
                            $ (equiv_rel $ (rep_fun $ Bound 0))),
                       ts)
                    end
                  else
                    (Const x, ts)
                end
              else if is_equational_fun_but_no_plain_def hol_ctxt x orelse
                      is_choice_spec_fun hol_ctxt x then
                (Const x, ts)
              else case def_of_const_ext thy def_tables x of
                SOME (unfold, def) =>
                if depth > unfold_max_depth then
                  raise TOO_LARGE ("Nitpick_HOL.unfold_defs_in_term",
                                   "too many nested definitions (" ^
                                   string_of_int depth ^ ") while expanding " ^
                                   quote s)
                else if s = "Wfrec.wfrec'" (* FIXME unchecked! *) then
                  (do_term (depth + 1) Ts (s_betapplys Ts (def, ts)), [])
                else if not unfold andalso
                     size_of_term def > def_inline_threshold () then
                  (Const x, ts)
                else
                  (do_term (depth + 1) Ts def, ts)
              | NONE => (Const x, ts)
        in
          s_betapplys Ts (const, map (do_term depth Ts) ts)
          |> s_beta_norm Ts
        end
  in do_term 0 [] end

(** Axiom extraction/generation **)

fun extensional_equal j T t1 t2 =
  if is_fun_type T then
    let
      val dom_T = pseudo_domain_type T
      val ran_T = pseudo_range_type T
      val var_t = Var (("x", j), dom_T)
    in
      extensional_equal (j + 1) ran_T (betapply (t1, var_t))
                        (betapply (t2, var_t))
    end
  else
    Const (@{const_name HOL.eq}, T --> T --> bool_T) $ t1 $ t2

(* FIXME: needed? *)
fun equationalize_term ctxt tag t =
  let
    val j = maxidx_of_term t + 1
    val (prems, concl) = Logic.strip_horn t
  in
    Logic.list_implies (prems,
        case concl of
          @{const Trueprop} $ (Const (@{const_name HOL.eq}, Type (_, [T, _]))
                               $ t1 $ t2) =>
          @{const Trueprop} $ extensional_equal j T t1 t2
        | @{const Trueprop} $ t' =>
          @{const Trueprop} $ HOLogic.mk_eq (t', @{const True})
        | Const (@{const_name "=="}, Type (_, [T, _])) $ t1 $ t2 =>
          @{const Trueprop} $ extensional_equal j T t1 t2
        | _ => (warning ("Ignoring " ^ quote tag ^ " for non-equation " ^
                         quote (Syntax.string_of_term ctxt t) ^ ".");
                raise SAME ()))
    |> SOME
  end
  handle SAME () => NONE

fun pair_for_prop t =
  case term_under_def t of
    Const (s, _) => (s, t)
  | t' => raise TERM ("Nitpick_HOL.pair_for_prop", [t, t'])

fun def_table_for get ctxt subst =
  ctxt |> get |> map (pair_for_prop o subst_atomic subst)
       |> AList.group (op =) |> Symtab.make

fun const_def_tables ctxt subst ts =
  (def_table_for (map prop_of o Nitpick_Unfolds.get) ctxt subst,
   fold (fn (s, t) => Symtab.map_default (s, []) (cons t))
        (map pair_for_prop ts) Symtab.empty)

fun paired_with_consts t = map (rpair t) (Term.add_const_names t [])
fun const_nondef_table ts =
  fold (append o paired_with_consts) ts [] |> AList.group (op =) |> Symtab.make

fun const_simp_table ctxt =
  def_table_for (map_filter (equationalize_term ctxt "nitpick_simp" o prop_of)
                 o Nitpick_Simps.get) ctxt
fun const_psimp_table ctxt =
  def_table_for (map_filter (equationalize_term ctxt "nitpick_psimp" o prop_of)
                 o Nitpick_Psimps.get) ctxt

fun const_choice_spec_table ctxt subst =
  map (subst_atomic subst o prop_of) (Nitpick_Choice_Specs.get ctxt)
  |> const_nondef_table

fun inductive_intro_table ctxt subst def_tables =
  let val thy = Proof_Context.theory_of ctxt in
    def_table_for
        (maps (map (unfold_mutually_inductive_preds thy def_tables o prop_of)
               o snd o snd)
         o filter (fn (cat, _) => cat = Spec_Rules.Inductive orelse
                                  cat = Spec_Rules.Co_Inductive)
         o Spec_Rules.get) ctxt subst
  end

fun ground_theorem_table thy =
  fold ((fn @{const Trueprop} $ t1 =>
            is_ground_term t1 ? Inttab.map_default (hash_term t1, []) (cons t1)
          | _ => I) o prop_of o snd) (Global_Theory.all_thms_of thy) Inttab.empty

fun ersatz_table ctxt =
 #ersatz_table (Data.get (Context.Proof ctxt))
 |> fold (append o snd) (#frac_types (Data.get (Context.Proof ctxt)))

fun add_simps simp_table s eqs =
  Unsynchronized.change simp_table
      (Symtab.update (s, eqs @ these (Symtab.lookup (!simp_table) s)))

fun inverse_axioms_for_rep_fun ctxt (x as (_, T)) =
  let
    val thy = Proof_Context.theory_of ctxt
    val abs_T = domain_type T
  in
    typedef_info ctxt (fst (dest_Type abs_T)) |> the
    |> pairf #Abs_inverse #Rep_inverse
    |> pairself (specialize_type thy x o prop_of o the)
    ||> single |> op ::
  end
fun optimized_typedef_axioms ctxt (abs_z as (abs_s, _)) =
  let
    val thy = Proof_Context.theory_of ctxt
    val abs_T = Type abs_z
  in
    if is_univ_typedef ctxt abs_T then
      []
    else case typedef_info ctxt abs_s of
      SOME {abs_type, rep_type, Rep_name, prop_of_Rep, set_name, ...} =>
      let
        val rep_T = varify_and_instantiate_type ctxt abs_type abs_T rep_type
        val rep_t = Const (Rep_name, abs_T --> rep_T)
        val set_t = Const (set_name, HOLogic.mk_setT rep_T)
        val set_t' =
          prop_of_Rep |> HOLogic.dest_Trueprop
                      |> specialize_type thy (dest_Const rep_t)
                      |> HOLogic.dest_mem |> snd
      in
        [HOLogic.all_const abs_T
         $ Abs (Name.uu, abs_T, HOLogic.mk_mem (rep_t $ Bound 0, set_t))]
        |> set_t <> set_t' ? cons (HOLogic.mk_eq (set_t, set_t'))
        |> map HOLogic.mk_Trueprop
      end
    | NONE => []
  end
fun optimized_quot_type_axioms ctxt stds abs_z =
  let
    val abs_T = Type abs_z
    val rep_T = rep_type_for_quot_type ctxt abs_T
    val (equiv_rel, partial) = equiv_relation_for_quot_type ctxt abs_T
    val a_var = Var (("a", 0), abs_T)
    val x_var = Var (("x", 0), rep_T)
    val y_var = Var (("y", 0), rep_T)
    val x = (@{const_name Quot}, rep_T --> abs_T)
    val sel_a_t = select_nth_constr_arg ctxt stds x a_var 0 rep_T
    val normal_fun =
      Const (quot_normal_name_for_type ctxt abs_T, rep_T --> rep_T)
    val normal_x = normal_fun $ x_var
    val normal_y = normal_fun $ y_var
    val is_unknown_t = Const (@{const_name is_unknown}, rep_T --> bool_T)
  in
    [Logic.mk_equals (normal_fun $ sel_a_t, sel_a_t),
     Logic.list_implies
         ([@{const Not} $ (is_unknown_t $ normal_x),
           @{const Not} $ (is_unknown_t $ normal_y),
           equiv_rel $ x_var $ y_var] |> map HOLogic.mk_Trueprop,
           Logic.mk_equals (normal_x, normal_y)),
     Logic.list_implies
         ([HOLogic.mk_Trueprop (@{const Not} $ (is_unknown_t $ normal_x)),
           HOLogic.mk_Trueprop (@{const Not} $ HOLogic.mk_eq (normal_x, x_var))],
          HOLogic.mk_Trueprop (equiv_rel $ x_var $ normal_x))]
    |> partial ? cons (HOLogic.mk_Trueprop (equiv_rel $ sel_a_t $ sel_a_t))
  end

fun codatatype_bisim_axioms (hol_ctxt as {ctxt, stds, ...}) T =
  let
    val xs = datatype_constrs hol_ctxt T
    val pred_T = T --> bool_T
    val iter_T = @{typ bisim_iterator}
    val bisim_max = @{const bisim_iterator_max}
    val n_var = Var (("n", 0), iter_T)
    val n_var_minus_1 =
      Const (@{const_name safe_The}, (iter_T --> bool_T) --> iter_T)
      $ Abs ("m", iter_T, HOLogic.eq_const iter_T
                          $ (suc_const iter_T $ Bound 0) $ n_var)
    val x_var = Var (("x", 0), T)
    val y_var = Var (("y", 0), T)
    fun bisim_const T = Const (@{const_name bisim}, [iter_T, T, T] ---> bool_T)
    fun nth_sub_bisim x n nth_T =
      (if is_codatatype ctxt nth_T then bisim_const nth_T $ n_var_minus_1
       else HOLogic.eq_const nth_T)
      $ select_nth_constr_arg ctxt stds x x_var n nth_T
      $ select_nth_constr_arg ctxt stds x y_var n nth_T
    fun case_func (x as (_, T)) =
      let
        val arg_Ts = binder_types T
        val core_t =
          discriminate_value hol_ctxt x y_var ::
          map2 (nth_sub_bisim x) (index_seq 0 (length arg_Ts)) arg_Ts
          |> foldr1 s_conj
      in fold_rev absdummy arg_Ts core_t end
  in
    [HOLogic.mk_imp
       (HOLogic.mk_disj (HOLogic.eq_const iter_T $ n_var $ zero_const iter_T,
            s_betapply [] (optimized_case_def hol_ctxt [] T bool_T
                                              (map case_func xs), x_var)),
        bisim_const T $ n_var $ x_var $ y_var),
     HOLogic.eq_const pred_T $ (bisim_const T $ bisim_max $ x_var)
     $ Abs (Name.uu, T, HOLogic.mk_eq (x_var, Bound 0))]
    |> map HOLogic.mk_Trueprop
  end

exception NO_TRIPLE of unit

fun triple_for_intro_rule thy x t =
  let
    val prems = Logic.strip_imp_prems t |> map (Object_Logic.atomize_term thy)
    val concl = Logic.strip_imp_concl t |> Object_Logic.atomize_term thy
    val (main, side) = List.partition (exists_Const (curry (op =) x)) prems
    val is_good_head = curry (op =) (Const x) o head_of
  in
    if forall is_good_head main then (side, main, concl) else raise NO_TRIPLE ()
  end

val tuple_for_args = HOLogic.mk_tuple o snd o strip_comb
fun wf_constraint_for rel side concl main =
  let
    val core = HOLogic.mk_mem (HOLogic.mk_prod
                               (pairself tuple_for_args (main, concl)), Var rel)
    val t = List.foldl HOLogic.mk_imp core side
    val vars = filter_out (curry (op =) rel) (Term.add_vars t [])
  in
    Library.foldl (fn (t', ((x, j), T)) =>
                      HOLogic.all_const T
                      $ Abs (x, T, abstract_over (Var ((x, j), T), t')))
                  (t, vars)
  end
fun wf_constraint_for_triple rel (side, main, concl) =
  map (wf_constraint_for rel side concl) main |> foldr1 s_conj

fun terminates_by ctxt timeout goal tac =
  can (SINGLE (Classical.safe_tac ctxt) #> the
       #> SINGLE (DETERM_TIMEOUT timeout (tac ctxt (auto_tac ctxt)))
       #> the #> Goal.finish ctxt) goal

val max_cached_wfs = 50
val cached_timeout =
  Synchronized.var "Nitpick_HOL.cached_timeout" (SOME Time.zeroTime)
val cached_wf_props =
  Synchronized.var "Nitpick_HOL.cached_wf_props" ([] : (term * bool) list)

val termination_tacs = [Lexicographic_Order.lex_order_tac true,
                        ScnpReconstruct.sizechange_tac]

fun uncached_is_well_founded_inductive_pred
        ({thy, ctxt, stds, debug, tac_timeout, intro_table, ...} : hol_context)
        (x as (_, T)) =
  case def_props_for_const thy stds intro_table x of
    [] => raise TERM ("Nitpick_HOL.uncached_is_well_founded_inductive",
                      [Const x])
  | intro_ts =>
    (case map (triple_for_intro_rule thy x) intro_ts
          |> filter_out (null o #2) of
       [] => true
     | triples =>
       let
         val binders_T = HOLogic.mk_tupleT (binder_types T)
         val rel_T = HOLogic.mk_setT (HOLogic.mk_prodT (binders_T, binders_T))
         val j = fold Integer.max (map maxidx_of_term intro_ts) 0 + 1
         val rel = (("R", j), rel_T)
         val prop = Const (@{const_name wf}, rel_T --> bool_T) $ Var rel ::
                    map (wf_constraint_for_triple rel) triples
                    |> foldr1 s_conj |> HOLogic.mk_Trueprop
         val _ = if debug then
                   Output.urgent_message ("Wellfoundedness goal: " ^
                             Syntax.string_of_term ctxt prop ^ ".")
                 else
                   ()
       in
         if tac_timeout = Synchronized.value cached_timeout andalso
            length (Synchronized.value cached_wf_props) < max_cached_wfs then
           ()
         else
           (Synchronized.change cached_wf_props (K []);
            Synchronized.change cached_timeout (K tac_timeout));
         case AList.lookup (op =) (Synchronized.value cached_wf_props) prop of
           SOME wf => wf
         | NONE =>
           let
             val goal = prop |> cterm_of thy |> Goal.init
             val wf = exists (terminates_by ctxt tac_timeout goal)
                             termination_tacs
           in Synchronized.change cached_wf_props (cons (prop, wf)); wf end
       end)
    handle List.Empty => false | NO_TRIPLE () => false

(* The type constraint below is a workaround for a Poly/ML crash. *)

fun is_well_founded_inductive_pred
        (hol_ctxt as {thy, wfs, def_tables, wf_cache, ...} : hol_context)
        (x as (s, _)) =
  case triple_lookup (const_match thy) wfs x of
    SOME (SOME b) => b
  | _ => s = @{const_name Nats} orelse s = @{const_name fold_graph'} orelse
         case AList.lookup (op =) (!wf_cache) x of
           SOME (_, wf) => wf
         | NONE =>
           let
             val gfp = (fixpoint_kind_of_const thy def_tables x = Gfp)
             val wf = uncached_is_well_founded_inductive_pred hol_ctxt x
           in
             Unsynchronized.change wf_cache (cons (x, (gfp, wf))); wf
           end

fun ap_curry [_] _ t = t
  | ap_curry arg_Ts tuple_T t =
    let val n = length arg_Ts in
      fold_rev (Term.abs o pair "c") arg_Ts
                (incr_boundvars n t $ mk_flat_tuple tuple_T (map Bound (n - 1 downto 0)))
    end

fun num_occs_of_bound_in_term j (t1 $ t2) =
    op + (pairself (num_occs_of_bound_in_term j) (t1, t2))
  | num_occs_of_bound_in_term j (Abs (_, _, t')) =
    num_occs_of_bound_in_term (j + 1) t'
  | num_occs_of_bound_in_term j (Bound j') = if j' = j then 1 else 0
  | num_occs_of_bound_in_term _ _ = 0

val is_linear_inductive_pred_def =
  let
    fun do_disjunct j (Const (@{const_name Ex}, _) $ Abs (_, _, t2)) =
        do_disjunct (j + 1) t2
      | do_disjunct j t =
        case num_occs_of_bound_in_term j t of
          0 => true
        | 1 => exists (curry (op =) (Bound j) o head_of) (conjuncts_of t)
        | _ => false
    fun do_lfp_def (Const (@{const_name lfp}, _) $ t2) =
        let val (xs, body) = strip_abs t2 in
          case length xs of
            1 => false
          | n => forall (do_disjunct (n - 1)) (disjuncts_of body)
        end
      | do_lfp_def _ = false
  in do_lfp_def o strip_abs_body end

fun n_ptuple_paths 0 = []
  | n_ptuple_paths 1 = []
  | n_ptuple_paths n = [] :: map (cons 2) (n_ptuple_paths (n - 1))
val ap_n_split = HOLogic.mk_psplits o n_ptuple_paths

val linear_pred_base_and_step_rhss =
  let
    fun aux (Const (@{const_name lfp}, _) $ t2) =
        let
          val (xs, body) = strip_abs t2
          val arg_Ts = map snd (tl xs)
          val tuple_T = HOLogic.mk_tupleT arg_Ts
          val j = length arg_Ts
          fun repair_rec j (Const (@{const_name Ex}, T1) $ Abs (s2, T2, t2')) =
              Const (@{const_name Ex}, T1)
              $ Abs (s2, T2, repair_rec (j + 1) t2')
            | repair_rec j (@{const HOL.conj} $ t1 $ t2) =
              @{const HOL.conj} $ repair_rec j t1 $ repair_rec j t2
            | repair_rec j t =
              let val (head, args) = strip_comb t in
                if head = Bound j then
                  HOLogic.eq_const tuple_T $ Bound j
                  $ mk_flat_tuple tuple_T args
                else
                  t
              end
          val (nonrecs, recs) =
            List.partition (curry (op =) 0 o num_occs_of_bound_in_term j)
                           (disjuncts_of body)
          val base_body = nonrecs |> List.foldl s_disj @{const False}
          val step_body = recs |> map (repair_rec j)
                               |> List.foldl s_disj @{const False}
        in
          (fold_rev Term.abs (tl xs) (incr_bv (~1, j, base_body))
           |> ap_n_split (length arg_Ts) tuple_T bool_T,
           Abs ("y", tuple_T, fold_rev Term.abs (tl xs) step_body
                              |> ap_n_split (length arg_Ts) tuple_T bool_T))
        end
      | aux t =
        raise TERM ("Nitpick_HOL.linear_pred_base_and_step_rhss.aux", [t])
  in aux end

fun predicatify T t =
  let val set_T = HOLogic.mk_setT T in
    Abs (Name.uu, T,
         Const (@{const_name Set.member}, T --> set_T --> bool_T)
         $ Bound 0 $ incr_boundvars 1 t)
  end

fun starred_linear_pred_const (hol_ctxt as {simp_table, ...}) (s, T) def =
  let
    val j = maxidx_of_term def + 1
    val (outer, fp_app) = strip_abs def
    val outer_bounds = map Bound (length outer - 1 downto 0)
    val outer_vars = map (fn (s, T) => Var ((s, j), T)) outer
    val fp_app = subst_bounds (rev outer_vars, fp_app)
    val (outer_Ts, rest_T) = strip_n_binders (length outer) T
    val tuple_arg_Ts = strip_type rest_T |> fst
    val tuple_T = HOLogic.mk_tupleT tuple_arg_Ts
    val prod_T = HOLogic.mk_prodT (tuple_T, tuple_T)
    val set_T = HOLogic.mk_setT tuple_T
    val rel_T = HOLogic.mk_setT prod_T
    val pred_T = tuple_T --> bool_T
    val curried_T = tuple_T --> pred_T
    val uncurried_T = prod_T --> bool_T
    val (base_rhs, step_rhs) = linear_pred_base_and_step_rhss fp_app
    val base_x as (base_s, _) = (base_prefix ^ s, outer_Ts ---> pred_T)
    val base_eq = HOLogic.mk_eq (list_comb (Const base_x, outer_vars), base_rhs)
                  |> HOLogic.mk_Trueprop
    val _ = add_simps simp_table base_s [base_eq]
    val step_x as (step_s, _) = (step_prefix ^ s, outer_Ts ---> curried_T)
    val step_eq = HOLogic.mk_eq (list_comb (Const step_x, outer_vars), step_rhs)
                  |> HOLogic.mk_Trueprop
    val _ = add_simps simp_table step_s [step_eq]
    val image_const = Const (@{const_name Image}, rel_T --> set_T --> set_T)
    val rtrancl_const = Const (@{const_name rtrancl}, rel_T --> rel_T)
    val base_set =
      HOLogic.Collect_const tuple_T $ list_comb (Const base_x, outer_bounds)
    val step_set =
      HOLogic.Collect_const prod_T
      $ (Const (@{const_name prod_case}, curried_T --> uncurried_T)
                $ list_comb (Const step_x, outer_bounds))
    val image_set =
      image_const $ (rtrancl_const $ step_set) $ base_set
      |> predicatify tuple_T
  in
    fold_rev Term.abs outer (image_set |> ap_curry tuple_arg_Ts tuple_T)
    |> unfold_defs_in_term hol_ctxt
  end

fun is_good_starred_linear_pred_type (Type (@{type_name fun}, Ts)) =
    forall (not o (is_fun_or_set_type orf is_pair_type)) Ts
  | is_good_starred_linear_pred_type _ = false

fun unrolled_inductive_pred_const (hol_ctxt as {thy, star_linear_preds,
                                                def_tables, simp_table, ...})
                                  gfp (x as (s, T)) =
  let
    val iter_T = iterator_type_for_const gfp x
    val x' as (s', _) = (unrolled_prefix ^ s, iter_T --> T)
    val unrolled_const = Const x' $ zero_const iter_T
    val def = the (def_of_const thy def_tables x)
  in
    if is_equational_fun_but_no_plain_def hol_ctxt x' then
      unrolled_const (* already done *)
    else if not gfp andalso star_linear_preds andalso
         is_linear_inductive_pred_def def andalso
         is_good_starred_linear_pred_type T then
      starred_linear_pred_const hol_ctxt x def
    else
      let
        val j = maxidx_of_term def + 1
        val (outer, fp_app) = strip_abs def
        val outer_bounds = map Bound (length outer - 1 downto 0)
        val cur = Var ((iter_var_prefix, j + 1), iter_T)
        val next = suc_const iter_T $ cur
        val rhs =
          case fp_app of
            Const _ $ t =>
            s_betapply [] (t, list_comb (Const x', next :: outer_bounds))
          | _ => raise TERM ("Nitpick_HOL.unrolled_inductive_pred_const",
                             [fp_app])
        val (inner, naked_rhs) = strip_abs rhs
        val all = outer @ inner
        val bounds = map Bound (length all - 1 downto 0)
        val vars = map (fn (s, T) => Var ((s, j), T)) all
        val eq = HOLogic.mk_eq (list_comb (Const x', cur :: bounds), naked_rhs)
                 |> HOLogic.mk_Trueprop |> curry subst_bounds (rev vars)
        val _ = add_simps simp_table s' [eq]
      in unrolled_const end
  end

fun raw_inductive_pred_axiom ({thy, def_tables, ...} : hol_context) x =
  let
    val def = the (def_of_const thy def_tables x)
    val (outer, fp_app) = strip_abs def
    val outer_bounds = map Bound (length outer - 1 downto 0)
    val rhs =
      case fp_app of
        Const _ $ t => s_betapply [] (t, list_comb (Const x, outer_bounds))
      | _ => raise TERM ("Nitpick_HOL.raw_inductive_pred_axiom", [fp_app])
    val (inner, naked_rhs) = strip_abs rhs
    val all = outer @ inner
    val bounds = map Bound (length all - 1 downto 0)
    val j = maxidx_of_term def + 1
    val vars = map (fn (s, T) => Var ((s, j), T)) all
  in
    HOLogic.mk_eq (list_comb (Const x, bounds), naked_rhs)
    |> HOLogic.mk_Trueprop |> curry subst_bounds (rev vars)
  end
fun inductive_pred_axiom hol_ctxt (x as (s, T)) =
  if String.isPrefix ubfp_prefix s orelse String.isPrefix lbfp_prefix s then
    let val x' = (strip_first_name_sep s |> snd, T) in
      raw_inductive_pred_axiom hol_ctxt x' |> subst_atomic [(Const x', Const x)]
    end
  else
    raw_inductive_pred_axiom hol_ctxt x

fun equational_fun_axioms (hol_ctxt as {thy, ctxt, stds, def_tables, simp_table,
                                        psimp_table, ...}) x =
  case def_props_for_const thy stds (!simp_table) x of
    [] => (case def_props_for_const thy stds psimp_table x of
             [] => (if is_inductive_pred hol_ctxt x then
                      [inductive_pred_axiom hol_ctxt x]
                    else case def_of_const thy def_tables x of
                      SOME def =>
                      @{const Trueprop} $ HOLogic.mk_eq (Const x, def)
                      |> equationalize_term ctxt "" |> the |> single
                    | NONE => [])
           | psimps => psimps)
  | simps => simps
fun is_equational_fun_surely_complete hol_ctxt x =
  case equational_fun_axioms hol_ctxt x of
    [@{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ t1 $ _)] =>
    strip_comb t1 |> snd |> forall is_Var
  | _ => false

(** Type preprocessing **)

fun merged_type_var_table_for_terms thy ts =
  let
    fun add (s, S) table =
      table
      |> (case AList.lookup (Sign.subsort thy o swap) table S of
            SOME _ => I
          | NONE =>
            filter_out (fn (S', _) => Sign.subsort thy (S, S'))
            #> cons (S, s))
    val tfrees = [] |> fold Term.add_tfrees ts
                    |> sort (string_ord o pairself fst)
  in [] |> fold add tfrees |> rev end

fun merge_type_vars_in_term thy merge_type_vars table =
  merge_type_vars
  ? map_types (map_atyps
        (fn TFree (_, S) =>
            TFree (table |> find_first (fn (S', _) => Sign.subsort thy (S', S))
                         |> the |> swap)
          | T => T))

fun add_ground_types hol_ctxt binarize =
  let
    fun aux T accum =
      case T of
        Type (@{type_name fun}, Ts) => fold aux Ts accum
      | Type (@{type_name prod}, Ts) => fold aux Ts accum
      | Type (@{type_name set}, Ts) => fold aux Ts accum
      | Type (@{type_name itself}, [T1]) => aux T1 accum
      | Type (_, Ts) =>
        if member (op =) (@{typ prop} :: @{typ bool} :: accum) T then
          accum
        else
          T :: accum
          |> fold aux (case binarized_and_boxed_datatype_constrs hol_ctxt
                                                                 binarize T of
                         [] => Ts
                       | xs => map snd xs)
      | _ => insert (op =) T accum
  in aux end
fun ground_types_in_type hol_ctxt binarize T =
  add_ground_types hol_ctxt binarize T []
fun ground_types_in_terms hol_ctxt binarize ts =
  fold (fold_types (add_ground_types hol_ctxt binarize)) ts []

end;
