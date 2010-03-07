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

  type hol_context = {
    thy: theory,
    ctxt: Proof.context,
    max_bisim_depth: int,
    boxes: (typ option * bool option) list,
    stds: (typ option * bool) list,
    wfs: (styp option * bool option) list,
    user_axioms: bool option,
    debug: bool,
    binary_ints: bool option,
    destroy_constrs: bool,
    specialize: bool,
    skolemize: bool,
    star_linear_preds: bool,
    uncurry: bool,
    fast_descrs: bool,
    tac_timeout: Time.time option,
    evals: term list,
    case_names: (string * int) list,
    def_table: const_table,
    nondef_table: const_table,
    user_nondefs: term list,
    simp_table: const_table Unsynchronized.ref,
    psimp_table: const_table,
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
  val ubfp_prefix : string
  val lbfp_prefix : string
  val quot_normal_prefix : string
  val skolem_prefix : string
  val special_prefix : string
  val uncurry_prefix : string
  val eval_prefix : string
  val original_name : string -> string
  val s_conj : term * term -> term
  val s_disj : term * term -> term
  val strip_any_connective : term -> term list * term
  val conjuncts_of : term -> term list
  val disjuncts_of : term -> term list
  val unarize_and_unbox_type : typ -> typ
  val unarize_unbox_and_uniterize_type : typ -> typ
  val string_for_type : Proof.context -> typ -> string
  val prefix_name : string -> string -> string
  val shortest_name : string -> string
  val short_name : string -> string
  val shorten_names_in_term : term -> term
  val type_match : theory -> typ * typ -> bool
  val const_match : theory -> styp * styp -> bool
  val term_match : theory -> term * term -> bool
  val is_TFree : typ -> bool
  val is_higher_order_type : typ -> bool
  val is_fun_type : typ -> bool
  val is_set_type : typ -> bool
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
  val is_number_type : theory -> typ -> bool
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
  val is_quot_type : theory -> typ -> bool
  val is_codatatype : theory -> typ -> bool
  val is_pure_typedef : theory -> typ -> bool
  val is_univ_typedef : theory -> typ -> bool
  val is_datatype : theory -> (typ option * bool) list -> typ -> bool
  val is_record_constr : styp -> bool
  val is_record_get : theory -> styp -> bool
  val is_record_update : theory -> styp -> bool
  val is_abs_fun : theory -> styp -> bool
  val is_rep_fun : theory -> styp -> bool
  val is_quot_abs_fun : Proof.context -> styp -> bool
  val is_quot_rep_fun : Proof.context -> styp -> bool
  val mate_of_rep_fun : theory -> styp -> styp
  val is_constr_like : theory -> styp -> bool
  val is_stale_constr : theory -> styp -> bool
  val is_constr : theory -> (typ option * bool) list -> styp -> bool
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
  val eta_expand : typ list -> term -> int -> term
  val extensionalize : term -> term
  val distinctness_formula : typ -> term list -> term
  val register_frac_type : string -> (string * string) list -> theory -> theory
  val unregister_frac_type : string -> theory -> theory
  val register_codatatype : typ -> string -> styp list -> theory -> theory
  val unregister_codatatype : typ -> theory -> theory
  val datatype_constrs : hol_context -> typ -> styp list
  val binarized_and_boxed_datatype_constrs :
    hol_context -> bool -> typ -> styp list
  val num_datatype_constrs : hol_context -> typ -> int
  val constr_name_for_sel_like : string -> string
  val binarized_and_boxed_constr_for_sel : hol_context -> bool -> styp -> styp
  val discriminate_value : hol_context -> styp -> term -> term
  val select_nth_constr_arg :
    theory -> (typ option * bool) list -> styp -> term -> int -> typ -> term
  val construct_value :
    theory -> (typ option * bool) list -> styp -> term list -> term
  val card_of_type : (typ * int) list -> typ -> int
  val bounded_card_of_type : int -> int -> (typ * int) list -> typ -> int
  val bounded_exact_card_of_type :
    hol_context -> typ list -> int -> int -> (typ * int) list -> typ -> int
  val is_finite_type : hol_context -> typ -> bool
  val special_bounds : term list -> (indexname * typ) list
  val abs_var : indexname * typ -> term -> term
  val is_funky_typedef : theory -> typ -> bool
  val all_axioms_of :
    theory -> (term * term) list -> term list * term list * term list
  val arity_of_built_in_const :
    theory -> (typ option * bool) list -> bool -> styp -> int option
  val is_built_in_const :
    theory -> (typ option * bool) list -> bool -> styp -> bool
  val term_under_def : term -> term
  val case_const_names :
    theory -> (typ option * bool) list -> (string * int) list
  val const_def_table :
    Proof.context -> (term * term) list -> term list -> const_table
  val const_nondef_table : term list -> const_table
  val const_simp_table : Proof.context -> (term * term) list -> const_table
  val const_psimp_table : Proof.context -> (term * term) list -> const_table
  val inductive_intro_table :
    Proof.context -> (term * term) list -> const_table -> const_table
  val ground_theorem_table : theory -> term list Inttab.table
  val ersatz_table : theory -> (string * string) list
  val add_simps : const_table Unsynchronized.ref -> string -> term list -> unit
  val inverse_axioms_for_rep_fun : theory -> styp -> term list
  val optimized_typedef_axioms : theory -> string * typ list -> term list
  val optimized_quot_type_axioms :
    Proof.context -> (typ option * bool) list -> string * typ list -> term list
  val def_of_const : theory -> const_table -> styp -> term option
  val fixpoint_kind_of_const :
    theory -> const_table -> string * typ -> fixpoint_kind
  val is_inductive_pred : hol_context -> styp -> bool
  val is_equational_fun : hol_context -> styp -> bool
  val is_constr_pattern_lhs : theory -> term -> bool
  val is_constr_pattern_formula : theory -> term -> bool
  val unfold_defs_in_term : hol_context -> term -> term
  val codatatype_bisim_axioms : hol_context -> typ -> term list
  val is_well_founded_inductive_pred : hol_context -> styp -> bool
  val unrolled_inductive_pred_const : hol_context -> bool -> styp -> term
  val equational_fun_axioms : hol_context -> styp -> term list
  val is_equational_fun_surely_complete : hol_context -> styp -> bool
  val merge_type_vars_in_terms : term list -> term list
  val ground_types_in_type : hol_context -> bool -> typ -> typ list
  val ground_types_in_terms : hol_context -> bool -> term list -> typ list
  val format_type : int list -> int list -> typ -> typ
  val format_term_type :
    theory -> const_table -> (term option * int list) list -> term -> typ
  val user_friendly_const :
   hol_context -> string * string -> (term option * int list) list
   -> styp -> term * typ
  val assign_operator_for_const : styp -> string
end;

structure Nitpick_HOL : NITPICK_HOL =
struct

open Nitpick_Util

type const_table = term list Symtab.table
type special_fun = (styp * int list * term list) * styp
type unrolled = styp * styp
type wf_cache = (styp * (bool * bool)) list

type hol_context = {
  thy: theory,
  ctxt: Proof.context,
  max_bisim_depth: int,
  boxes: (typ option * bool option) list,
  stds: (typ option * bool) list,
  wfs: (styp option * bool option) list,
  user_axioms: bool option,
  debug: bool,
  binary_ints: bool option,
  destroy_constrs: bool,
  specialize: bool,
  skolemize: bool,
  star_linear_preds: bool,
  uncurry: bool,
  fast_descrs: bool,
  tac_timeout: Time.time option,
  evals: term list,
  case_names: (string * int) list,
  def_table: const_table,
  nondef_table: const_table,
  user_nondefs: term list,
  simp_table: const_table Unsynchronized.ref,
  psimp_table: const_table,
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

structure Data = Theory_Data(
  type T = {frac_types: (string * (string * string) list) list,
            codatatypes: (string * (string * styp list)) list}
  val empty = {frac_types = [], codatatypes = []}
  val extend = I
  fun merge ({frac_types = fs1, codatatypes = cs1},
               {frac_types = fs2, codatatypes = cs2}) : T =
    {frac_types = AList.merge (op =) (K true) (fs1, fs2),
     codatatypes = AList.merge (op =) (K true) (cs1, cs2)})

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
val arg_var_prefix = "x"

(* int -> string *)
fun sel_prefix_for j = sel_prefix ^ string_of_int j ^ name_sep
(* Proof.context -> typ -> string *)
fun quot_normal_name_for_type ctxt T =
  quot_normal_prefix ^ unyxml (Syntax.string_of_typ ctxt T)

(* string -> string * string *)
val strip_first_name_sep =
  Substring.full #> Substring.position name_sep ##> Substring.triml 1
  #> pairself Substring.string
(* string -> string *)
fun original_name s =
  if String.isPrefix nitpick_prefix s then
    case strip_first_name_sep s of (s1, "") => s1 | (_, s2) => original_name s2
  else
    s
val after_name_sep = snd o strip_first_name_sep

(* term * term -> term *)
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

(* term -> term -> term list *)
fun strip_connective conn_t (t as (t0 $ t1 $ t2)) =
    if t0 = conn_t then strip_connective t0 t2 @ strip_connective t0 t1 else [t]
  | strip_connective _ t = [t]
(* term -> term list * term *)
fun strip_any_connective (t as (t0 $ _ $ _)) =
    if t0 = @{const "op &"} orelse t0 = @{const "op |"} then
      (strip_connective t0 t, t0)
    else
      ([t], @{const Not})
  | strip_any_connective t = ([t], @{const Not})
(* term -> term list *)
val conjuncts_of = strip_connective @{const "op &"}
val disjuncts_of = strip_connective @{const "op |"}

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
   (@{const_name "op ="}, 2),
   (@{const_name "op &"}, 2),
   (@{const_name "op |"}, 2),
   (@{const_name "op -->"}, 2),
   (@{const_name If}, 3),
   (@{const_name Let}, 2),
   (@{const_name Unity}, 0),
   (@{const_name Pair}, 2),
   (@{const_name fst}, 1),
   (@{const_name snd}, 1),
   (@{const_name Id}, 0),
   (@{const_name insert}, 2),
   (@{const_name converse}, 1),
   (@{const_name trancl}, 1),
   (@{const_name rel_comp}, 2),
   (@{const_name image}, 2),
   (@{const_name finite}, 1),
   (@{const_name unknown}, 0),
   (@{const_name is_unknown}, 1),
   (@{const_name Tha}, 1),
   (@{const_name Frac}, 0),
   (@{const_name norm_frac}, 0)]
val built_in_nat_consts =
  [(@{const_name Suc}, 0),
   (@{const_name nat}, 0),
   (@{const_name nat_gcd}, 0),
   (@{const_name nat_lcm}, 0)]
val built_in_descr_consts =
  [(@{const_name The}, 1),
   (@{const_name Eps}, 1)]
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
val built_in_set_consts =
  [(@{const_name semilattice_inf_class.inf}, 2),
   (@{const_name semilattice_sup_class.sup}, 2),
   (@{const_name minus_class.minus}, 2),
   (@{const_name ord_class.less_eq}, 2)]

(* typ -> typ *)
fun unarize_type @{typ "unsigned_bit word"} = nat_T
  | unarize_type @{typ "signed_bit word"} = int_T
  | unarize_type (Type (s, Ts as _ :: _)) = Type (s, map unarize_type Ts)
  | unarize_type T = T
fun unarize_and_unbox_type (Type (@{type_name fun_box}, Ts)) =
    unarize_and_unbox_type (Type ("fun", Ts))
  | unarize_and_unbox_type (Type (@{type_name pair_box}, Ts)) =
    Type ("*", map unarize_and_unbox_type Ts)
  | unarize_and_unbox_type @{typ "unsigned_bit word"} = nat_T
  | unarize_and_unbox_type @{typ "signed_bit word"} = int_T
  | unarize_and_unbox_type (Type (s, Ts as _ :: _)) =
    Type (s, map unarize_and_unbox_type Ts)
  | unarize_and_unbox_type T = T
fun uniterize_type (Type (s, Ts as _ :: _)) = Type (s, map uniterize_type Ts)
  | uniterize_type @{typ bisim_iterator} = nat_T
  | uniterize_type T = T
val unarize_unbox_and_uniterize_type = uniterize_type o unarize_and_unbox_type

(* Proof.context -> typ -> string *)
fun string_for_type ctxt = Syntax.string_of_typ ctxt o unarize_and_unbox_type

(* string -> string -> string *)
val prefix_name = Long_Name.qualify o Long_Name.base_name
(* string -> string *)
fun shortest_name s = List.last (space_explode "." s) handle List.Empty => ""
(* string -> term -> term *)
val prefix_abs_vars = Term.map_abs_vars o prefix_name
(* string -> string *)
fun short_name s =
  case space_explode name_sep s of
    [_] => s |> String.isPrefix nitpick_prefix s ? unprefix nitpick_prefix
  | ss => map shortest_name ss |> space_implode "_"
(* typ -> typ *)
fun shorten_names_in_type (Type (s, Ts)) =
    Type (short_name s, map shorten_names_in_type Ts)
  | shorten_names_in_type T = T
(* term -> term *)
val shorten_names_in_term =
  map_aterms (fn Const (s, T) => Const (short_name s, T) | t => t)
  #> map_types shorten_names_in_type

(* theory -> typ * typ -> bool *)
fun type_match thy (T1, T2) =
  (Sign.typ_match thy (T2, T1) Vartab.empty; true)
  handle Type.TYPE_MATCH => false
(* theory -> styp * styp -> bool *)
fun const_match thy ((s1, T1), (s2, T2)) =
  s1 = s2 andalso type_match thy (T1, T2)
(* theory -> term * term -> bool *)
fun term_match thy (Const x1, Const x2) = const_match thy (x1, x2)
  | term_match thy (Free (s1, T1), Free (s2, T2)) =
    const_match thy ((shortest_name s1, T1), (shortest_name s2, T2))
  | term_match _ (t1, t2) = t1 aconv t2

(* typ -> bool *)
fun is_TFree (TFree _) = true
  | is_TFree _ = false
fun is_higher_order_type (Type ("fun", _)) = true
  | is_higher_order_type (Type (_, Ts)) = exists is_higher_order_type Ts
  | is_higher_order_type _ = false
fun is_fun_type (Type ("fun", _)) = true
  | is_fun_type _ = false
fun is_set_type (Type ("fun", [_, @{typ bool}])) = true
  | is_set_type _ = false
fun is_pair_type (Type ("*", _)) = true
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
(* theory -> typ -> bool *)
fun is_frac_type thy (Type (s, [])) =
    not (null (these (AList.lookup (op =) (#frac_types (Data.get thy)) s)))
  | is_frac_type _ _ = false
fun is_number_type thy = is_integer_like_type orf is_frac_type thy

(* bool -> styp -> typ *)
fun iterator_type_for_const gfp (s, T) =
  Type ((if gfp then gfp_iterator_prefix else lfp_iterator_prefix) ^ s,
        binder_types T)
(* typ -> styp *)
fun const_for_iterator_type (Type (s, Ts)) = (after_name_sep s, Ts ---> bool_T)
  | const_for_iterator_type T =
    raise TYPE ("Nitpick_HOL.const_for_iterator_type", [T], [])

(* int -> typ -> typ list * typ *)
fun strip_n_binders 0 T = ([], T)
  | strip_n_binders n (Type ("fun", [T1, T2])) =
    strip_n_binders (n - 1) T2 |>> cons T1
  | strip_n_binders n (Type (@{type_name fun_box}, Ts)) =
    strip_n_binders n (Type ("fun", Ts))
  | strip_n_binders _ T = raise TYPE ("Nitpick_HOL.strip_n_binders", [T], [])
(* typ -> typ *)
val nth_range_type = snd oo strip_n_binders

(* typ -> int *)
fun num_factors_in_type (Type ("*", [T1, T2])) =
    fold (Integer.add o num_factors_in_type) [T1, T2] 0
  | num_factors_in_type _ = 1
fun num_binder_types (Type ("fun", [_, T2])) = 1 + num_binder_types T2
  | num_binder_types _ = 0
(* typ -> typ list *)
val curried_binder_types = maps HOLogic.flatten_tupleT o binder_types
fun maybe_curried_binder_types T =
  (if is_pair_type (body_type T) then binder_types else curried_binder_types) T

(* typ -> term list -> term *)
fun mk_flat_tuple _ [t] = t
  | mk_flat_tuple (Type ("*", [T1, T2])) (t :: ts) =
    HOLogic.pair_const T1 T2 $ t $ (mk_flat_tuple T2 ts)
  | mk_flat_tuple T ts = raise TYPE ("Nitpick_HOL.mk_flat_tuple", [T], ts)
(* int -> term -> term list *)
fun dest_n_tuple 1 t = [t]
  | dest_n_tuple n t = HOLogic.dest_prod t ||> dest_n_tuple (n - 1) |> op ::

(* int -> typ -> typ list *)
fun dest_n_tuple_type 1 T = [T]
  | dest_n_tuple_type n (Type (_, [T1, T2])) =
    T1 :: dest_n_tuple_type (n - 1) T2
  | dest_n_tuple_type _ T =
    raise TYPE ("Nitpick_HOL.dest_n_tuple_type", [T], [])

type typedef_info =
  {rep_type: typ, abs_type: typ, Rep_name: string, Abs_name: string,
   set_def: thm option, prop_of_Rep: thm, set_name: string,
   Abs_inverse: thm option, Rep_inverse: thm option}

(* theory -> string -> typedef_info *)
fun typedef_info thy s =
  if is_frac_type thy (Type (s, [])) then
    SOME {abs_type = Type (s, []), rep_type = @{typ "int * int"},
          Abs_name = @{const_name Abs_Frac}, Rep_name = @{const_name Rep_Frac},
          set_def = NONE, prop_of_Rep = @{prop "Rep_Frac x \<in> Frac"}
                          |> Logic.varify,
          set_name = @{const_name Frac}, Abs_inverse = NONE, Rep_inverse = NONE}
  else case Typedef.get_info thy s of
    SOME {abs_type, rep_type, Abs_name, Rep_name, set_def, Rep, Abs_inverse,
          Rep_inverse, ...} =>
    SOME {abs_type = abs_type, rep_type = rep_type, Abs_name = Abs_name,
          Rep_name = Rep_name, set_def = set_def, prop_of_Rep = prop_of Rep,
          set_name = set_prefix ^ s, Abs_inverse = SOME Abs_inverse,
          Rep_inverse = SOME Rep_inverse}
  | NONE => NONE

(* theory -> string -> bool *)
val is_typedef = is_some oo typedef_info
val is_real_datatype = is_some oo Datatype.get_info
(* theory -> (typ option * bool) list -> typ -> bool *)
fun is_standard_datatype thy = the oo triple_lookup (type_match thy)

(* FIXME: Use antiquotation for "code_numeral" below or detect "rep_datatype",
   e.g., by adding a field to "Datatype_Aux.info". *)
(* theory -> (typ option * bool) list -> string -> bool *)
fun is_basic_datatype thy stds s =
  member (op =) [@{type_name "*"}, @{type_name bool}, @{type_name unit},
                 @{type_name int}, "Code_Numeral.code_numeral"] s orelse
  (s = @{type_name nat} andalso is_standard_datatype thy stds nat_T)

(* theory -> typ -> typ -> typ -> typ *)
fun instantiate_type thy T1 T1' T2 =
  Same.commit (Envir.subst_type_same
                   (Sign.typ_match thy (T1, T1') Vartab.empty)) T2
  handle Type.TYPE_MATCH =>
         raise TYPE ("Nitpick_HOL.instantiate_type", [T1, T1'], [])
fun varify_and_instantiate_type thy T1 T1' T2 =
  instantiate_type thy (Logic.varifyT T1) T1' (Logic.varifyT T2)

(* theory -> typ -> typ -> styp *)
fun repair_constr_type thy body_T' T =
  varify_and_instantiate_type thy (body_type T) body_T' T

(* string -> (string * string) list -> theory -> theory *)
fun register_frac_type frac_s ersaetze thy =
  let
    val {frac_types, codatatypes} = Data.get thy
    val frac_types = AList.update (op =) (frac_s, ersaetze) frac_types
  in Data.put {frac_types = frac_types, codatatypes = codatatypes} thy end
(* string -> theory -> theory *)
fun unregister_frac_type frac_s = register_frac_type frac_s []

(* typ -> string -> styp list -> theory -> theory *)
fun register_codatatype co_T case_name constr_xs thy =
  let
    val {frac_types, codatatypes} = Data.get thy
    val constr_xs = map (apsnd (repair_constr_type thy co_T)) constr_xs
    val (co_s, co_Ts) = dest_Type co_T
    val _ =
      if forall is_TFree co_Ts andalso not (has_duplicates (op =) co_Ts) andalso
         co_s <> "fun" andalso
         not (is_basic_datatype thy [(NONE, true)] co_s) then
        ()
      else
        raise TYPE ("Nitpick_HOL.register_codatatype", [co_T], [])
    val codatatypes = AList.update (op =) (co_s, (case_name, constr_xs))
                                   codatatypes
  in Data.put {frac_types = frac_types, codatatypes = codatatypes} thy end
(* typ -> theory -> theory *)
fun unregister_codatatype co_T = register_codatatype co_T "" []

(* theory -> typ -> bool *)
fun is_quot_type thy (Type (s, _)) =
    is_some (Quotient_Info.quotdata_lookup_raw thy s)
  | is_quot_type _ _ = false
fun is_codatatype thy (Type (s, _)) =
    not (null (AList.lookup (op =) (#codatatypes (Data.get thy)) s
               |> Option.map snd |> these))
  | is_codatatype _ _ = false
fun is_pure_typedef thy (T as Type (s, _)) =
    is_typedef thy s andalso
    not (is_real_datatype thy s orelse is_quot_type thy T orelse
         is_codatatype thy T orelse is_record_type T orelse
         is_integer_like_type T)
  | is_pure_typedef _ _ = false
fun is_univ_typedef thy (Type (s, _)) =
    (case typedef_info thy s of
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
(* theory -> (typ option * bool) list -> typ -> bool *)
fun is_datatype thy stds (T as Type (s, _)) =
    (is_typedef thy s orelse is_codatatype thy T orelse T = @{typ ind} orelse
     is_quot_type thy T) andalso not (is_basic_datatype thy stds s)
  | is_datatype _ _ _ = false

(* theory -> typ -> (string * typ) list * (string * typ) *)
fun all_record_fields thy T =
  let val (recs, more) = Record.get_extT_fields thy T in
    recs @ more :: all_record_fields thy (snd more)
  end
  handle TYPE _ => []
(* styp -> bool *)
fun is_record_constr (s, T) =
  String.isSuffix Record.extN s andalso
  let val dataT = body_type T in
    is_record_type dataT andalso
    s = unsuffix Record.ext_typeN (fst (dest_Type dataT)) ^ Record.extN
  end
(* theory -> typ -> int *)
val num_record_fields = Integer.add 1 o length o fst oo Record.get_extT_fields
(* theory -> string -> typ -> int *)
fun no_of_record_field thy s T1 =
  find_index (curry (op =) s o fst)
             (Record.get_extT_fields thy T1 ||> single |> op @)
(* theory -> styp -> bool *)
fun is_record_get thy (s, Type ("fun", [T1, _])) =
    exists (curry (op =) s o fst) (all_record_fields thy T1)
  | is_record_get _ _ = false
fun is_record_update thy (s, T) =
  String.isSuffix Record.updateN s andalso
  exists (curry (op =) (unsuffix Record.updateN s) o fst)
         (all_record_fields thy (body_type T))
  handle TYPE _ => false
fun is_abs_fun thy (s, Type ("fun", [_, Type (s', _)])) =
    (case typedef_info thy s' of
       SOME {Abs_name, ...} => s = Abs_name
     | NONE => false)
  | is_abs_fun _ _ = false
fun is_rep_fun thy (s, Type ("fun", [Type (s', _), _])) =
    (case typedef_info thy s' of
       SOME {Rep_name, ...} => s = Rep_name
     | NONE => false)
  | is_rep_fun _ _ = false
(* Proof.context -> styp -> bool *)
fun is_quot_abs_fun ctxt (x as (_, Type ("fun", [_, Type (s', _)]))) =
    (try (Quotient_Term.absrep_const_chk Quotient_Term.AbsF ctxt) s'
     = SOME (Const x))
  | is_quot_abs_fun _ _ = false
fun is_quot_rep_fun ctxt (x as (_, Type ("fun", [Type (s', _), _]))) =
    (try (Quotient_Term.absrep_const_chk Quotient_Term.RepF ctxt) s'
     = SOME (Const x))
  | is_quot_rep_fun _ _ = false

(* theory -> styp -> styp *)
fun mate_of_rep_fun thy (x as (_, Type ("fun", [T1 as Type (s', _), T2]))) =
    (case typedef_info thy s' of
       SOME {Abs_name, ...} => (Abs_name, Type ("fun", [T2, T1]))
     | NONE => raise TERM ("Nitpick_HOL.mate_of_rep_fun", [Const x]))
  | mate_of_rep_fun _ x = raise TERM ("Nitpick_HOL.mate_of_rep_fun", [Const x])
(* theory -> typ -> typ *)
fun rep_type_for_quot_type thy (T as Type (s, _)) =
  let val {qtyp, rtyp, ...} = Quotient_Info.quotdata_lookup thy s in
    instantiate_type thy qtyp T rtyp
  end
(* theory -> typ -> term *)
fun equiv_relation_for_quot_type thy (Type (s, Ts)) =
    let
      val {qtyp, equiv_rel, ...} = Quotient_Info.quotdata_lookup thy s
      val Ts' = qtyp |> dest_Type |> snd
    in subst_atomic_types (Ts' ~~ Ts) equiv_rel end
  | equiv_relation_for_quot_type _ T =
    raise TYPE ("Nitpick_HOL.equiv_relation_for_quot_type", [T], [])

(* theory -> styp -> bool *)
fun is_coconstr thy (s, T) =
  let
    val {codatatypes, ...} = Data.get thy
    val co_T = body_type T
    val co_s = dest_Type co_T |> fst
  in
    exists (fn (s', T') => s = s' andalso repair_constr_type thy co_T T' = T)
           (AList.lookup (op =) codatatypes co_s |> Option.map snd |> these)
  end
  handle TYPE ("dest_Type", _, _) => false
fun is_constr_like thy (s, T) =
  member (op =) [@{const_name FunBox}, @{const_name PairBox},
                 @{const_name Quot}, @{const_name Zero_Rep},
                 @{const_name Suc_Rep}] s orelse
  let val (x as (_, T)) = (s, unarize_and_unbox_type T) in
    Refute.is_IDT_constructor thy x orelse is_record_constr x orelse
    (is_abs_fun thy x andalso is_pure_typedef thy (range_type T)) orelse
    is_coconstr thy x
  end
fun is_stale_constr thy (x as (_, T)) =
  is_codatatype thy (body_type T) andalso is_constr_like thy x andalso
  not (is_coconstr thy x)
(* theory -> (typ option * bool) list -> styp -> bool *)
fun is_constr thy stds (x as (_, T)) =
  is_constr_like thy x andalso
  not (is_basic_datatype thy stds
                         (fst (dest_Type (unarize_type (body_type T))))) andalso
  not (is_stale_constr thy x)
(* string -> bool *)
val is_sel = String.isPrefix discr_prefix orf String.isPrefix sel_prefix
val is_sel_like_and_no_discr =
  String.isPrefix sel_prefix
  orf (member (op =) [@{const_name fst}, @{const_name snd}])

(* boxability -> boxability *)
fun in_fun_lhs_for InConstr = InSel
  | in_fun_lhs_for _ = InFunLHS
fun in_fun_rhs_for InConstr = InConstr
  | in_fun_rhs_for InSel = InSel
  | in_fun_rhs_for InFunRHS1 = InFunRHS2
  | in_fun_rhs_for _ = InFunRHS1

(* hol_context -> boxability -> typ -> bool *)
fun is_boxing_worth_it (hol_ctxt : hol_context) boxy T =
  case T of
    Type ("fun", _) =>
    (boxy = InPair orelse boxy = InFunLHS) andalso
    not (is_boolean_type (body_type T))
  | Type ("*", Ts) =>
    boxy = InPair orelse boxy = InFunRHS1 orelse boxy = InFunRHS2 orelse
    ((boxy = InExpr orelse boxy = InFunLHS) andalso
     exists (is_boxing_worth_it hol_ctxt InPair)
            (map (box_type hol_ctxt InPair) Ts))
  | _ => false
(* hol_context -> boxability -> string * typ list -> string *)
and should_box_type (hol_ctxt as {thy, boxes, ...}) boxy z =
  case triple_lookup (type_match thy) boxes (Type z) of
    SOME (SOME box_me) => box_me
  | _ => is_boxing_worth_it hol_ctxt boxy (Type z)
(* hol_context -> boxability -> typ -> typ *)
and box_type hol_ctxt boxy T =
  case T of
    Type (z as ("fun", [T1, T2])) =>
    if boxy <> InConstr andalso boxy <> InSel andalso
       should_box_type hol_ctxt boxy z then
      Type (@{type_name fun_box},
            [box_type hol_ctxt InFunLHS T1, box_type hol_ctxt InFunRHS1 T2])
    else
      box_type hol_ctxt (in_fun_lhs_for boxy) T1
      --> box_type hol_ctxt (in_fun_rhs_for boxy) T2
  | Type (z as ("*", Ts)) =>
    if boxy <> InConstr andalso boxy <> InSel
       andalso should_box_type hol_ctxt boxy z then
      Type (@{type_name pair_box}, map (box_type hol_ctxt InSel) Ts)
    else
      Type ("*", map (box_type hol_ctxt
                          (if boxy = InConstr orelse boxy = InSel then boxy
                           else InPair)) Ts)
  | _ => T

(* typ -> typ *)
fun binarize_nat_and_int_in_type @{typ nat} = @{typ "unsigned_bit word"}
  | binarize_nat_and_int_in_type @{typ int} = @{typ "signed_bit word"}
  | binarize_nat_and_int_in_type (Type (s, Ts)) =
    Type (s, map binarize_nat_and_int_in_type Ts)
  | binarize_nat_and_int_in_type T = T
(* term -> term *)
val binarize_nat_and_int_in_term = map_types binarize_nat_and_int_in_type

(* styp -> styp *)
fun discr_for_constr (s, T) = (discr_prefix ^ s, body_type T --> bool_T)

(* typ -> int *)
fun num_sels_for_constr_type T = length (maybe_curried_binder_types T)
(* string -> int -> string *)
fun nth_sel_name_for_constr_name s n =
  if s = @{const_name Pair} then
    if n = 0 then @{const_name fst} else @{const_name snd}
  else
    sel_prefix_for n ^ s
(* styp -> int -> styp *)
fun nth_sel_for_constr x ~1 = discr_for_constr x
  | nth_sel_for_constr (s, T) n =
    (nth_sel_name_for_constr_name s n,
     body_type T --> nth (maybe_curried_binder_types T) n)
(* hol_context -> bool -> styp -> int -> styp *)
fun binarized_and_boxed_nth_sel_for_constr hol_ctxt binarize =
  apsnd ((binarize ? binarize_nat_and_int_in_type) o box_type hol_ctxt InSel)
  oo nth_sel_for_constr

(* string -> int *)
fun sel_no_from_name s =
  if String.isPrefix discr_prefix s then
    ~1
  else if String.isPrefix sel_prefix s then
    s |> unprefix sel_prefix |> Int.fromString |> the
  else if s = @{const_name snd} then
    1
  else
    0

(* term -> term *)
val close_form =
  let
    (* (indexname * typ) list -> (indexname * typ) list -> term -> term *)
    fun close_up zs zs' =
      fold (fn (z as ((s, _), T)) => fn t' =>
               Term.all T $ Abs (s, T, abstract_over (Var z, t')))
           (take (length zs' - length zs) zs')
    (* (indexname * typ) list -> term -> term *)
    fun aux zs (@{const "==>"} $ t1 $ t2) =
        let val zs' = Term.add_vars t1 zs in
          close_up zs zs' (Logic.mk_implies (t1, aux zs' t2))
        end
      | aux zs t = close_up zs (Term.add_vars t zs) t
  in aux [] end

(* typ list -> term -> int -> term *)
fun eta_expand _ t 0 = t
  | eta_expand Ts (Abs (s, T, t')) n =
    Abs (s, T, eta_expand (T :: Ts) t' (n - 1))
  | eta_expand Ts t n =
    fold_rev (curry3 Abs ("x\<^isub>\<eta>" ^ nat_subscript n))
             (List.take (binder_types (fastype_of1 (Ts, t)), n))
             (list_comb (incr_boundvars n t, map Bound (n - 1 downto 0)))

(* term -> term *)
fun extensionalize t =
  case t of
    (t0 as @{const Trueprop}) $ t1 => t0 $ extensionalize t1
  | Const (@{const_name "op ="}, _) $ t1 $ Abs (s, T, t2) =>
    let val v = Var ((s, maxidx_of_term t + 1), T) in
      extensionalize (HOLogic.mk_eq (t1 $ v, subst_bound (v, t2)))
    end
  | _ => t

(* typ -> term list -> term *)
fun distinctness_formula T =
  all_distinct_unordered_pairs_of
  #> map (fn (t1, t2) => @{const Not} $ (HOLogic.eq_const T $ t1 $ t2))
  #> List.foldr (s_conj o swap) @{const True}

(* typ -> term *)
fun zero_const T = Const (@{const_name zero_class.zero}, T)
fun suc_const T = Const (@{const_name Suc}, T --> T)

(* hol_context -> typ -> styp list *)
fun uncached_datatype_constrs ({thy, stds, ...} : hol_context)
                              (T as Type (s, Ts)) =
    (case AList.lookup (op =) (#codatatypes (Data.get thy)) s of
       SOME (_, xs' as (_ :: _)) => map (apsnd (repair_constr_type thy T)) xs'
     | _ =>
       if is_datatype thy stds T then
         case Datatype.get_info thy s of
           SOME {index, descr, ...} =>
           let
             val (_, dtyps, constrs) = AList.lookup (op =) descr index |> the
           in
             map (fn (s', Us) =>
                     (s', map (Refute.typ_of_dtyp descr (dtyps ~~ Ts)) Us
                          ---> T)) constrs
           end
         | NONE =>
           if is_record_type T then
             let
               val s' = unsuffix Record.ext_typeN s ^ Record.extN
               val T' = (Record.get_extT_fields thy T
                        |> apsnd single |> uncurry append |> map snd) ---> T
             in [(s', T')] end
           else if is_quot_type thy T then
             [(@{const_name Quot}, rep_type_for_quot_type thy T --> T)]
           else case typedef_info thy s of
             SOME {abs_type, rep_type, Abs_name, ...} =>
             [(Abs_name,
               varify_and_instantiate_type thy abs_type T rep_type --> T)]
           | NONE =>
             if T = @{typ ind} then
               [dest_Const @{const Zero_Rep}, dest_Const @{const Suc_Rep}]
             else
               []
       else
         [])
  | uncached_datatype_constrs _ _ = []
(* hol_context -> typ -> styp list *)
fun datatype_constrs (hol_ctxt as {constr_cache, ...}) T =
  case AList.lookup (op =) (!constr_cache) T of
    SOME xs => xs
  | NONE =>
    let val xs = uncached_datatype_constrs hol_ctxt T in
      (Unsynchronized.change constr_cache (cons (T, xs)); xs)
    end
(* hol_context -> bool -> typ -> styp list *)
fun binarized_and_boxed_datatype_constrs hol_ctxt binarize =
  map (apsnd ((binarize ? binarize_nat_and_int_in_type)
              o box_type hol_ctxt InConstr)) o datatype_constrs hol_ctxt
(* hol_context -> typ -> int *)
val num_datatype_constrs = length oo datatype_constrs

(* string -> string *)
fun constr_name_for_sel_like @{const_name fst} = @{const_name Pair}
  | constr_name_for_sel_like @{const_name snd} = @{const_name Pair}
  | constr_name_for_sel_like s' = original_name s'
(* hol_context -> bool -> styp -> styp *)
fun binarized_and_boxed_constr_for_sel hol_ctxt binarize (s', T') =
  let val s = constr_name_for_sel_like s' in
    AList.lookup (op =)
        (binarized_and_boxed_datatype_constrs hol_ctxt binarize (domain_type T'))
        s
    |> the |> pair s
  end

(* hol_context -> styp -> term *)
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
(* hol_context -> styp -> term -> term *)
fun discriminate_value (hol_ctxt as {thy, ...}) x t =
  case head_of t of
    Const x' =>
    if x = x' then @{const True}
    else if is_constr_like thy x' then @{const False}
    else betapply (discr_term_for_constr hol_ctxt x, t)
  | _ => betapply (discr_term_for_constr hol_ctxt x, t)

(* theory -> (typ option * bool) list -> styp -> term -> term *)
fun nth_arg_sel_term_for_constr thy stds (x as (s, T)) n =
  let val (arg_Ts, dataT) = strip_type T in
    if dataT = nat_T andalso is_standard_datatype thy stds nat_T then
      @{term "%n::nat. n - 1"}
    else if is_pair_type dataT then
      Const (nth_sel_for_constr x n)
    else
      let
        (* int -> typ -> int * term *)
        fun aux m (Type ("*", [T1, T2])) =
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
(* theory -> (typ option * bool) list -> styp -> term -> int -> typ -> term *)
fun select_nth_constr_arg thy stds x t n res_T =
  (case strip_comb t of
     (Const x', args) =>
     if x = x' then nth args n
     else if is_constr_like thy x' then Const (@{const_name unknown}, res_T)
     else raise SAME ()
   | _ => raise SAME())
  handle SAME () => betapply (nth_arg_sel_term_for_constr thy stds x n, t)

(* theory -> (typ option * bool) list -> styp -> term list -> term *)
fun construct_value _ _ x [] = Const x
  | construct_value thy stds (x as (s, _)) args =
    let val args = map Envir.eta_contract args in
      case hd args of
        Const (s', _) $ t =>
        if is_sel_like_and_no_discr s' andalso
           constr_name_for_sel_like s' = s andalso
           forall (fn (n, t') =>
                      select_nth_constr_arg thy stds x t n dummyT = t')
                  (index_seq 0 (length args) ~~ args) then
          t
        else
          list_comb (Const x, args)
      | _ => list_comb (Const x, args)
    end

(* (typ * int) list -> typ -> int *)
fun card_of_type assigns (Type ("fun", [T1, T2])) =
    reasonable_power (card_of_type assigns T2) (card_of_type assigns T1)
  | card_of_type assigns (Type ("*", [T1, T2])) =
    card_of_type assigns T1 * card_of_type assigns T2
  | card_of_type _ (Type (@{type_name itself}, _)) = 1
  | card_of_type _ @{typ prop} = 2
  | card_of_type _ @{typ bool} = 2
  | card_of_type _ @{typ unit} = 1
  | card_of_type assigns T =
    case AList.lookup (op =) assigns T of
      SOME k => k
    | NONE => if T = @{typ bisim_iterator} then 0
              else raise TYPE ("Nitpick_HOL.card_of_type", [T], [])
(* int -> (typ * int) list -> typ -> int *)
fun bounded_card_of_type max default_card assigns (Type ("fun", [T1, T2])) =
    let
      val k1 = bounded_card_of_type max default_card assigns T1
      val k2 = bounded_card_of_type max default_card assigns T2
    in
      if k1 = max orelse k2 = max then max
      else Int.min (max, reasonable_power k2 k1)
    end
  | bounded_card_of_type max default_card assigns (Type ("*", [T1, T2])) =
    let
      val k1 = bounded_card_of_type max default_card assigns T1
      val k2 = bounded_card_of_type max default_card assigns T2
    in if k1 = max orelse k2 = max then max else Int.min (max, k1 * k2) end
  | bounded_card_of_type max default_card assigns T =
    Int.min (max, if default_card = ~1 then
                    card_of_type assigns T
                  else
                    card_of_type assigns T
                    handle TYPE ("Nitpick_HOL.card_of_type", _, _) =>
                           default_card)
(* hol_context -> typ list -> int -> (typ * int) list -> typ -> int *)
fun bounded_exact_card_of_type hol_ctxt finitizable_dataTs max default_card
                               assigns T =
  let
    (* typ list -> typ -> int *)
    fun aux avoid T =
      (if member (op =) avoid T then
         0
       else if member (op =) finitizable_dataTs T then
         raise SAME ()
       else case T of
         Type ("fun", [T1, T2]) =>
         let
           val k1 = aux avoid T1
           val k2 = aux avoid T2
         in
           if k1 = 0 orelse k2 = 0 then 0
           else if k1 >= max orelse k2 >= max then max
           else Int.min (max, reasonable_power k2 k1)
         end
       | Type ("*", [T1, T2]) =>
         let
           val k1 = aux avoid T1
           val k2 = aux avoid T2
         in
           if k1 = 0 orelse k2 = 0 then 0
           else if k1 >= max orelse k2 >= max then max
           else Int.min (max, k1 * k2)
         end
       | Type (@{type_name itself}, _) => 1
       | @{typ prop} => 2
       | @{typ bool} => 2
       | @{typ unit} => 1
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
              else Integer.sum constr_cards
            end)
       | _ => raise SAME ())
      handle SAME () =>
             AList.lookup (op =) assigns T |> the_default default_card
  in Int.min (max, aux [] T) end

(* hol_context -> typ -> bool *)
fun is_finite_type hol_ctxt T =
  bounded_exact_card_of_type hol_ctxt [] 1 2 [] T <> 0

(* term -> bool *)
fun is_ground_term (t1 $ t2) = is_ground_term t1 andalso is_ground_term t2
  | is_ground_term (Const _) = true
  | is_ground_term _ = false

(* term -> word -> word *)
fun hashw_term (t1 $ t2) = Polyhash.hashw (hashw_term t1, hashw_term t2)
  | hashw_term (Const (s, _)) = Polyhash.hashw_string (s, 0w0)
  | hashw_term _ = 0w0
(* term -> int *)
val hash_term = Word.toInt o hashw_term

(* term list -> (indexname * typ) list *)
fun special_bounds ts =
  fold Term.add_vars ts [] |> sort (Term_Ord.fast_indexname_ord o pairself fst)

(* indexname * typ -> term -> term *)
fun abs_var ((s, j), T) body = Abs (s, T, abstract_over (Var ((s, j), T), body))

(* theory -> string -> bool *)
fun is_funky_typedef_name thy s =
  member (op =) [@{type_name unit}, @{type_name "*"}, @{type_name "+"},
                 @{type_name int}] s orelse
  is_frac_type thy (Type (s, []))
(* theory -> typ -> bool *)
fun is_funky_typedef thy (Type (s, _)) = is_funky_typedef_name thy s
  | is_funky_typedef _ _ = false
(* term -> bool *)
fun is_arity_type_axiom (Const (@{const_name HOL.type_class}, _)
                         $ Const (@{const_name TYPE}, _)) = true
  | is_arity_type_axiom _ = false
(* theory -> bool -> term -> bool *)
fun is_typedef_axiom thy boring (@{const "==>"} $ _ $ t2) =
    is_typedef_axiom thy boring t2
  | is_typedef_axiom thy boring
        (@{const Trueprop} $ (Const (@{const_name Typedef.type_definition}, _)
         $ Const (_, Type ("fun", [Type (s, _), _])) $ Const _ $ _)) =
    boring <> is_funky_typedef_name thy s andalso is_typedef thy s
  | is_typedef_axiom _ _ _ = false

(* Distinguishes between (1) constant definition axioms, (2) type arity and
   typedef axioms, and (3) other axioms, and returns the pair ((1), (3)).
   Typedef axioms are uninteresting to Nitpick, because it can retrieve them
   using "typedef_info". *)
(* theory -> (string * term) list -> string list -> term list * term list *)
fun partition_axioms_by_definitionality thy axioms def_names =
  let
    val axioms = sort (fast_string_ord o pairself fst) axioms
    val defs = OrdList.inter (fast_string_ord o apsnd fst) def_names axioms
    val nondefs =
      OrdList.subtract (fast_string_ord o apsnd fst) def_names axioms
      |> filter_out ((is_arity_type_axiom orf is_typedef_axiom thy true) o snd)
  in pairself (map snd) (defs, nondefs) end

(* Ideally we would check against "Complex_Main", not "Refute", but any theory
   will do as long as it contains all the "axioms" and "axiomatization"
   commands. *)
(* theory -> bool *)
fun is_built_in_theory thy = Theory.subthy (thy, @{theory Refute})

(* term -> bool *)
val is_trivial_definition =
  the_default false o try (op aconv o Logic.dest_equals)
val is_plain_definition =
  let
    (* term -> bool *)
    fun do_lhs t1 =
      case strip_comb t1 of
        (Const _, args) =>
        forall is_Var args andalso not (has_duplicates (op =) args)
      | _ => false
    fun do_eq (Const (@{const_name "=="}, _) $ t1 $ _) = do_lhs t1
      | do_eq (@{const Trueprop} $ (Const (@{const_name "op ="}, _) $ t1 $ _)) =
        do_lhs t1
      | do_eq _ = false
  in do_eq end

(* theory -> (term * term) list -> term list * term list * term list *)
fun all_axioms_of thy subst =
  let
    (* theory list -> term list *)
    val axioms_of_thys =
      maps Thm.axioms_of #> map (apsnd (subst_atomic subst o prop_of))
    val specs = Defs.all_specifications_of (Theory.defs_of thy)
    val def_names = specs |> maps snd |> map_filter #def
                    |> OrdList.make fast_string_ord
    val thys = thy :: Theory.ancestors_of thy
    val (built_in_thys, user_thys) = List.partition is_built_in_theory thys
    val built_in_axioms = axioms_of_thys built_in_thys
    val user_axioms = axioms_of_thys user_thys
    val (built_in_defs, built_in_nondefs) =
      partition_axioms_by_definitionality thy built_in_axioms def_names
      ||> filter (is_typedef_axiom thy false)
    val (user_defs, user_nondefs) =
      partition_axioms_by_definitionality thy user_axioms def_names
    val (built_in_nondefs, user_nondefs) =
      List.partition (is_typedef_axiom thy false) user_nondefs
      |>> append built_in_nondefs
    val defs =
      (thy |> PureThy.all_thms_of
           |> filter (curry (op =) Thm.definitionK o Thm.get_kind o snd)
           |> map (prop_of o snd)
           |> filter_out is_trivial_definition
           |> filter is_plain_definition) @
      user_defs @ built_in_defs
  in (defs, built_in_nondefs, user_nondefs) end

(* theory -> (typ option * bool) list -> bool -> styp -> int option *)
fun arity_of_built_in_const thy stds fast_descrs (s, T) =
  if s = @{const_name If} then
    if nth_range_type 3 T = @{typ bool} then NONE else SOME 3
  else
    let val std_nats = is_standard_datatype thy stds nat_T in
      case AList.lookup (op =)
                    (built_in_consts
                     |> std_nats ? append built_in_nat_consts
                     |> fast_descrs ? append built_in_descr_consts) s of
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
          | _ => if is_fun_type T andalso is_set_type (domain_type T) then
                   AList.lookup (op =) built_in_set_consts s
                 else
                   NONE
    end
(* theory -> (typ option * bool) list -> bool -> styp -> bool *)
val is_built_in_const = is_some oooo arity_of_built_in_const

(* This function is designed to work for both real definition axioms and
   simplification rules (equational specifications). *)
(* term -> term *)
fun term_under_def t =
  case t of
    @{const "==>"} $ _ $ t2 => term_under_def t2
  | Const (@{const_name "=="}, _) $ t1 $ _ => term_under_def t1
  | @{const Trueprop} $ t1 => term_under_def t1
  | Const (@{const_name "op ="}, _) $ t1 $ _ => term_under_def t1
  | Abs (_, _, t') => term_under_def t'
  | t1 $ _ => term_under_def t1
  | _ => t

(* Here we crucially rely on "Refute.specialize_type" performing a preorder
   traversal of the term, without which the wrong occurrence of a constant could
   be matched in the face of overloading. *)
(* theory -> (typ option * bool) list -> bool -> const_table -> styp
   -> term list *)
fun def_props_for_const thy stds fast_descrs table (x as (s, _)) =
  if is_built_in_const thy stds fast_descrs x then
    []
  else
    these (Symtab.lookup table s)
    |> map_filter (try (Refute.specialize_type thy x))
    |> filter (curry (op =) (Const x) o term_under_def)

(* term -> term option *)
fun normalized_rhs_of t =
  let
    (* term option -> term option *)
    fun aux (v as Var _) (SOME t) = SOME (lambda v t)
      | aux (c as Const (@{const_name TYPE}, _)) (SOME t) = SOME (lambda c t)
      | aux _ _ = NONE
    val (lhs, rhs) =
      case t of
        Const (@{const_name "=="}, _) $ t1 $ t2 => (t1, t2)
      | @{const Trueprop} $ (Const (@{const_name "op ="}, _) $ t1 $ t2) =>
        (t1, t2)
      | _ => raise TERM ("Nitpick_HOL.normalized_rhs_of", [t])
    val args = strip_comb lhs |> snd
  in fold_rev aux args (SOME rhs) end

(* theory -> const_table -> styp -> term option *)
fun def_of_const thy table (x as (s, _)) =
  if is_built_in_const thy [(NONE, false)] false x orelse
     original_name s <> s then
    NONE
  else
    x |> def_props_for_const thy [(NONE, false)] false table |> List.last
      |> normalized_rhs_of |> Option.map (prefix_abs_vars s)
    handle List.Empty => NONE

(* term -> fixpoint_kind *)
fun fixpoint_kind_of_rhs (Abs (_, _, t)) = fixpoint_kind_of_rhs t
  | fixpoint_kind_of_rhs (Const (@{const_name lfp}, _) $ Abs _) = Lfp
  | fixpoint_kind_of_rhs (Const (@{const_name gfp}, _) $ Abs _) = Gfp
  | fixpoint_kind_of_rhs _ = NoFp

(* theory -> const_table -> term -> bool *)
fun is_mutually_inductive_pred_def thy table t =
  let
    (* term -> bool *)
    fun is_good_arg (Bound _) = true
      | is_good_arg (Const (s, _)) =
        s = @{const_name True} orelse s = @{const_name False} orelse
        s = @{const_name undefined}
      | is_good_arg _ = false
  in
    case t |> strip_abs_body |> strip_comb of
      (Const x, ts as (_ :: _)) =>
      (case def_of_const thy table x of
         SOME t' => fixpoint_kind_of_rhs t' <> NoFp andalso forall is_good_arg ts
       | NONE => false)
    | _ => false
  end
(* theory -> const_table -> term -> term *)
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

(* term -> string * term *)
fun pair_for_prop t =
  case term_under_def t of
    Const (s, _) => (s, t)
  | t' => raise TERM ("Nitpick_HOL.pair_for_prop", [t, t'])

(* (Proof.context -> term list) -> Proof.context -> (term * term) list
   -> const_table *)
fun table_for get ctxt subst =
  ctxt |> get |> map (pair_for_prop o subst_atomic subst)
       |> AList.group (op =) |> Symtab.make

(* theory -> (typ option * bool) list -> (string * int) list *)
fun case_const_names thy stds =
  Symtab.fold (fn (dtype_s, {index, descr, case_name, ...}) =>
                  if is_basic_datatype thy stds dtype_s then
                    I
                  else
                    cons (case_name, AList.lookup (op =) descr index
                                     |> the |> #3 |> length))
              (Datatype.get_all thy) [] @
  map (apsnd length o snd) (#codatatypes (Data.get thy))

(* Proof.context -> (term * term) list -> term list -> const_table *)
fun const_def_table ctxt subst ts =
  table_for (map prop_of o Nitpick_Defs.get) ctxt subst
  |> fold (fn (s, t) => Symtab.map_default (s, []) (cons t))
          (map pair_for_prop ts)
(* term list -> const_table *)
fun const_nondef_table ts =
  fold (fn t => append (map (fn s => (s, t)) (Term.add_const_names t []))) ts []
  |> AList.group (op =) |> Symtab.make
(* Proof.context -> (term * term) list -> const_table *)
val const_simp_table = table_for (map prop_of o Nitpick_Simps.get)
val const_psimp_table = table_for (map prop_of o Nitpick_Psimps.get)
(* Proof.context -> (term * term) list -> const_table -> const_table *)
fun inductive_intro_table ctxt subst def_table =
  table_for (map (unfold_mutually_inductive_preds (ProofContext.theory_of ctxt)
                                                  def_table o prop_of)
             o Nitpick_Intros.get) ctxt subst
(* theory -> term list Inttab.table *)
fun ground_theorem_table thy =
  fold ((fn @{const Trueprop} $ t1 =>
            is_ground_term t1 ? Inttab.map_default (hash_term t1, []) (cons t1)
          | _ => I) o prop_of o snd) (PureThy.all_thms_of thy) Inttab.empty

val basic_ersatz_table =
  [(@{const_name prod_case}, @{const_name split}),
   (@{const_name card}, @{const_name card'}),
   (@{const_name setsum}, @{const_name setsum'}),
   (@{const_name fold_graph}, @{const_name fold_graph'}),
   (@{const_name wf}, @{const_name wf'}),
   (@{const_name wf_wfrec}, @{const_name wf_wfrec'}),
   (@{const_name wfrec}, @{const_name wfrec'})]

(* theory -> (string * string) list *)
fun ersatz_table thy =
  fold (append o snd) (#frac_types (Data.get thy)) basic_ersatz_table

(* const_table Unsynchronized.ref -> string -> term list -> unit *)
fun add_simps simp_table s eqs =
  Unsynchronized.change simp_table
      (Symtab.update (s, eqs @ these (Symtab.lookup (!simp_table) s)))

(* theory -> styp -> term list *)
fun inverse_axioms_for_rep_fun thy (x as (_, T)) =
  let val abs_T = domain_type T in
    typedef_info thy (fst (dest_Type abs_T)) |> the
    |> pairf #Abs_inverse #Rep_inverse
    |> pairself (Refute.specialize_type thy x o prop_of o the)
    ||> single |> op ::
  end
(* theory -> string * typ list -> term list *)
fun optimized_typedef_axioms thy (abs_z as (abs_s, _)) =
  let val abs_T = Type abs_z in
    if is_univ_typedef thy abs_T then
      []
    else case typedef_info thy abs_s of
      SOME {abs_type, rep_type, Rep_name, prop_of_Rep, set_name, ...} =>
      let
        val rep_T = varify_and_instantiate_type thy abs_type abs_T rep_type
        val rep_t = Const (Rep_name, abs_T --> rep_T)
        val set_t = Const (set_name, rep_T --> bool_T)
        val set_t' =
          prop_of_Rep |> HOLogic.dest_Trueprop
                      |> Refute.specialize_type thy (dest_Const rep_t)
                      |> HOLogic.dest_mem |> snd
      in
        [HOLogic.all_const abs_T
         $ Abs (Name.uu, abs_T, set_t $ (rep_t $ Bound 0))]
        |> set_t <> set_t' ? cons (HOLogic.mk_eq (set_t, set_t'))
        |> map HOLogic.mk_Trueprop
      end
    | NONE => []
  end
(* Proof.context -> string * typ list -> term list *)
fun optimized_quot_type_axioms ctxt stds abs_z =
  let
    val thy = ProofContext.theory_of ctxt
    val abs_T = Type abs_z
    val rep_T = rep_type_for_quot_type thy abs_T
    val equiv_rel = equiv_relation_for_quot_type thy abs_T
    val a_var = Var (("a", 0), abs_T)
    val x_var = Var (("x", 0), rep_T)
    val y_var = Var (("y", 0), rep_T)
    val x = (@{const_name Quot}, rep_T --> abs_T)
    val sel_a_t = select_nth_constr_arg thy stds x a_var 0 rep_T
    val normal_t = Const (quot_normal_name_for_type ctxt abs_T, rep_T --> rep_T)
    val normal_x = normal_t $ x_var
    val normal_y = normal_t $ y_var
    val is_unknown_t = Const (@{const_name is_unknown}, rep_T --> bool_T)
  in
    [Logic.mk_equals (normal_t $ sel_a_t, sel_a_t),
     Logic.list_implies
         ([@{const Not} $ (is_unknown_t $ normal_x),
           @{const Not} $ (is_unknown_t $ normal_y),
           equiv_rel $ x_var $ y_var] |> map HOLogic.mk_Trueprop,
           Logic.mk_equals (normal_x, normal_y)),
     Logic.list_implies
         ([HOLogic.mk_Trueprop (@{const Not} $ (is_unknown_t $ normal_x)),
           HOLogic.mk_Trueprop (@{const Not} $ HOLogic.mk_eq (normal_x, x_var))],
          HOLogic.mk_Trueprop (equiv_rel $ x_var $ normal_x))]
  end

(* theory -> (typ option * bool) list -> int * styp -> term *)
fun constr_case_body thy stds (j, (x as (_, T))) =
  let val arg_Ts = binder_types T in
    list_comb (Bound j, map2 (select_nth_constr_arg thy stds x (Bound 0))
                             (index_seq 0 (length arg_Ts)) arg_Ts)
  end
(* hol_context -> typ -> int * styp -> term -> term *)
fun add_constr_case (hol_ctxt as {thy, stds, ...}) res_T (j, x) res_t =
  Const (@{const_name If}, bool_T --> res_T --> res_T --> res_T)
  $ discriminate_value hol_ctxt x (Bound 0) $ constr_case_body thy stds (j, x)
  $ res_t
(* hol_context -> typ -> typ -> term *)
fun optimized_case_def (hol_ctxt as {thy, stds, ...}) dataT res_T =
  let
    val xs = datatype_constrs hol_ctxt dataT
    val func_Ts = map ((fn T => binder_types T ---> res_T) o snd) xs
    val (xs', x) = split_last xs
  in
    constr_case_body thy stds (1, x)
    |> fold_rev (add_constr_case hol_ctxt res_T) (length xs downto 2 ~~ xs')
    |> fold_rev (curry absdummy) (func_Ts @ [dataT])
  end

(* hol_context -> string -> typ -> typ -> term -> term *)
fun optimized_record_get (hol_ctxt as {thy, stds, ...}) s rec_T res_T t =
  let val constr_x = hd (datatype_constrs hol_ctxt rec_T) in
    case no_of_record_field thy s rec_T of
      ~1 => (case rec_T of
               Type (_, Ts as _ :: _) =>
               let
                 val rec_T' = List.last Ts
                 val j = num_record_fields thy rec_T - 1
               in
                 select_nth_constr_arg thy stds constr_x t j res_T
                 |> optimized_record_get hol_ctxt s rec_T' res_T
               end
             | _ => raise TYPE ("Nitpick_HOL.optimized_record_get", [rec_T],
                                []))
    | j => select_nth_constr_arg thy stds constr_x t j res_T
  end
(* hol_context -> string -> typ -> term -> term -> term *)
fun optimized_record_update (hol_ctxt as {thy, stds, ...}) s rec_T fun_t rec_t =
  let
    val constr_x as (_, constr_T) = hd (datatype_constrs hol_ctxt rec_T)
    val Ts = binder_types constr_T
    val n = length Ts
    val special_j = no_of_record_field thy s rec_T
    val ts =
      map2 (fn j => fn T =>
               let val t = select_nth_constr_arg thy stds constr_x rec_t j T in
                 if j = special_j then
                   betapply (fun_t, t)
                 else if j = n - 1 andalso special_j = ~1 then
                   optimized_record_update hol_ctxt s
                       (rec_T |> dest_Type |> snd |> List.last) fun_t t
                 else
                   t
               end) (index_seq 0 n) Ts
  in list_comb (Const constr_x, ts) end

(* theory -> const_table -> string * typ -> fixpoint_kind *)
fun fixpoint_kind_of_const thy table x =
  if is_built_in_const thy [(NONE, false)] false x then
    NoFp
  else
    fixpoint_kind_of_rhs (the (def_of_const thy table x))
    handle Option.Option => NoFp

(* hol_context -> styp -> bool *)
fun is_real_inductive_pred ({thy, stds, fast_descrs, def_table, intro_table,
                             ...} : hol_context) x =
  fixpoint_kind_of_const thy def_table x <> NoFp andalso
  not (null (def_props_for_const thy stds fast_descrs intro_table x))
fun is_real_equational_fun ({thy, stds, fast_descrs, simp_table, psimp_table,
                             ...} : hol_context) x =
  exists (fn table => not (null (def_props_for_const thy stds fast_descrs table
                                                     x)))
         [!simp_table, psimp_table]
fun is_inductive_pred hol_ctxt =
  is_real_inductive_pred hol_ctxt andf (not o is_real_equational_fun hol_ctxt)
fun is_equational_fun hol_ctxt =
  (is_real_equational_fun hol_ctxt orf is_real_inductive_pred hol_ctxt
   orf (String.isPrefix ubfp_prefix orf String.isPrefix lbfp_prefix) o fst)

(* term * term -> term *)
fun s_betapply (Const (@{const_name If}, _) $ @{const True} $ t, _) = t
  | s_betapply (Const (@{const_name If}, _) $ @{const False} $ _, t) = t
  | s_betapply p = betapply p
(* term * term list -> term *)
val s_betapplys = Library.foldl s_betapply

(* term -> term *)
fun lhs_of_equation t =
  case t of
    Const (@{const_name all}, _) $ Abs (_, _, t1) => lhs_of_equation t1
  | Const (@{const_name "=="}, _) $ t1 $ _ => SOME t1
  | @{const "==>"} $ _ $ t2 => lhs_of_equation t2
  | @{const Trueprop} $ t1 => lhs_of_equation t1
  | Const (@{const_name All}, _) $ Abs (_, _, t1) => lhs_of_equation t1
  | Const (@{const_name "op ="}, _) $ t1 $ _ => SOME t1
  | @{const "op -->"} $ _ $ t2 => lhs_of_equation t2
  | _ => NONE
(* theory -> term -> bool *)
fun is_constr_pattern _ (Bound _) = true
  | is_constr_pattern _ (Var _) = true
  | is_constr_pattern thy t =
    case strip_comb t of
      (Const x, args) =>
      is_constr_like thy x andalso forall (is_constr_pattern thy) args
    | _ => false
fun is_constr_pattern_lhs thy t =
  forall (is_constr_pattern thy) (snd (strip_comb t))
fun is_constr_pattern_formula thy t =
  case lhs_of_equation t of
    SOME t' => is_constr_pattern_lhs thy t'
  | NONE => false

(* Prevents divergence in case of cyclic or infinite definition dependencies. *)
val unfold_max_depth = 255

(* hol_context -> term -> term *)
fun unfold_defs_in_term (hol_ctxt as {thy, ctxt, stds, fast_descrs, case_names,
                                      def_table, ground_thm_table, ersatz_table,
                                      ...}) =
  let
    (* int -> typ list -> term -> term *)
    fun do_term depth Ts t =
      case t of
        (t0 as Const (@{const_name Int.number_class.number_of},
                      Type ("fun", [_, ran_T]))) $ t1 =>
        ((if is_number_type thy ran_T then
            let
              val j = t1 |> HOLogic.dest_numeral
                         |> ran_T = nat_T ? Integer.max 0
              val s = numeral_prefix ^ signed_string_of_int j
            in
              if is_integer_like_type ran_T then
                if is_standard_datatype thy stds ran_T then
                  Const (s, ran_T)
                else
                  funpow j (curry (op $) (suc_const ran_T)) (zero_const ran_T)
              else
                do_term depth Ts (Const (@{const_name of_int}, int_T --> ran_T)
                                  $ Const (s, int_T))
            end
            handle TERM _ => raise SAME ()
          else
            raise SAME ())
         handle SAME () => betapply (do_term depth Ts t0, do_term depth Ts t1))
      | Const (@{const_name refl_on}, T) $ Const (@{const_name top}, _) $ t2 =>
        do_const depth Ts t (@{const_name refl'}, range_type T) [t2]
      | (t0 as Const (@{const_name Sigma}, _)) $ t1 $ (t2 as Abs (_, _, t2')) =>
        betapplys (t0 |> loose_bvar1 (t2', 0) ? do_term depth Ts,
                   map (do_term depth Ts) [t1, t2])
      | Const (x as (@{const_name distinct},
               Type ("fun", [Type (@{type_name list}, [T']), _])))
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
      | Const x $ t1 $ t2 $ t3 => do_const depth Ts t x [t1, t2, t3]
      | Const x $ t1 $ t2 => do_const depth Ts t x [t1, t2]
      | Const x $ t1 => do_const depth Ts t x [t1]
      | Const x => do_const depth Ts t x []
      | t1 $ t2 => betapply (do_term depth Ts t1, do_term depth Ts t2)
      | Free _ => t
      | Var _ => t
      | Bound _ => t
      | Abs (s, T, body) => Abs (s, T, do_term depth (T :: Ts) body)
    (* int -> typ list -> styp -> term list -> int -> typ -> term * term list *)
    and select_nth_constr_arg_with_args _ _ (x as (_, T)) [] n res_T =
        (Abs (Name.uu, body_type T,
              select_nth_constr_arg thy stds x (Bound 0) n res_T), [])
      | select_nth_constr_arg_with_args depth Ts x (t :: ts) n res_T =
        (select_nth_constr_arg thy stds x (do_term depth Ts t) n res_T, ts)
    (* int -> typ list -> term -> styp -> term list -> term *)
    and do_const depth Ts t (x as (s, T)) ts =
      case AList.lookup (op =) ersatz_table s of
        SOME s' =>
        do_const (depth + 1) Ts (list_comb (Const (s', T), ts)) (s', T) ts
      | NONE =>
        let
          val (const, ts) =
            if is_built_in_const thy stds fast_descrs x then
              (Const x, ts)
            else case AList.lookup (op =) case_names s of
              SOME n =>
              let
                val (dataT, res_T) = nth_range_type n T
                                     |> pairf domain_type range_type
              in
                (optimized_case_def hol_ctxt dataT res_T
                 |> do_term (depth + 1) Ts, ts)
              end
            | _ =>
              if is_constr thy stds x then
                (Const x, ts)
              else if is_stale_constr thy x then
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
                let
                  val abs_T = domain_type T
                  val rep_T = range_type T
                  val x' = (@{const_name Quot}, rep_T --> abs_T)
                in select_nth_constr_arg_with_args depth Ts x' ts 0 rep_T end
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
              else if is_rep_fun thy x then
                let val x' = mate_of_rep_fun thy x in
                  if is_constr thy stds x' then
                    select_nth_constr_arg_with_args depth Ts x' ts 0
                                                    (range_type T)
                  else
                    (Const x, ts)
                end
              else if is_equational_fun hol_ctxt x then
                (Const x, ts)
              else case def_of_const thy def_table x of
                SOME def =>
                if depth > unfold_max_depth then
                  raise TOO_LARGE ("Nitpick_HOL.unfold_defs_in_term",
                                   "too many nested definitions (" ^
                                   string_of_int depth ^ ") while expanding " ^
                                   quote s)
                else if s = @{const_name wfrec'} then
                  (do_term (depth + 1) Ts (betapplys (def, ts)), [])
                else
                  (do_term (depth + 1) Ts def, ts)
              | NONE => (Const x, ts)
        in s_betapplys (const, map (do_term depth Ts) ts) |> Envir.beta_norm end
  in do_term 0 [] end

(* hol_context -> typ -> term list *)
fun codatatype_bisim_axioms (hol_ctxt as {thy, stds, ...}) T =
  let
    val xs = datatype_constrs hol_ctxt T
    val set_T = T --> bool_T
    val iter_T = @{typ bisim_iterator}
    val bisim_const = Const (@{const_name bisim}, iter_T --> T --> T --> bool_T)
    val bisim_max = @{const bisim_iterator_max}
    val n_var = Var (("n", 0), iter_T)
    val n_var_minus_1 =
      Const (@{const_name Tha}, (iter_T --> bool_T) --> iter_T)
      $ Abs ("m", iter_T, HOLogic.eq_const iter_T
                          $ (suc_const iter_T $ Bound 0) $ n_var)
    val x_var = Var (("x", 0), T)
    val y_var = Var (("y", 0), T)
    (* styp -> int -> typ -> term *)
    fun nth_sub_bisim x n nth_T =
      (if is_codatatype thy nth_T then bisim_const $ n_var_minus_1
       else HOLogic.eq_const nth_T)
      $ select_nth_constr_arg thy stds x x_var n nth_T
      $ select_nth_constr_arg thy stds x y_var n nth_T
    (* styp -> term *)
    fun case_func (x as (_, T)) =
      let
        val arg_Ts = binder_types T
        val core_t =
          discriminate_value hol_ctxt x y_var ::
          map2 (nth_sub_bisim x) (index_seq 0 (length arg_Ts)) arg_Ts
          |> foldr1 s_conj
      in List.foldr absdummy core_t arg_Ts end
  in
    [HOLogic.eq_const bool_T $ (bisim_const $ n_var $ x_var $ y_var)
     $ (@{term "op |"} $ (HOLogic.eq_const iter_T $ n_var $ zero_const iter_T)
        $ (betapplys (optimized_case_def hol_ctxt T bool_T,
                      map case_func xs @ [x_var]))),
     HOLogic.eq_const set_T $ (bisim_const $ bisim_max $ x_var)
     $ (Const (@{const_name insert}, T --> set_T --> set_T)
        $ x_var $ Const (@{const_name bot_class.bot}, set_T))]
    |> map HOLogic.mk_Trueprop
  end

exception NO_TRIPLE of unit

(* theory -> styp -> term -> term list * term list * term *)
fun triple_for_intro_rule thy x t =
  let
    val prems = Logic.strip_imp_prems t |> map (Object_Logic.atomize_term thy)
    val concl = Logic.strip_imp_concl t |> Object_Logic.atomize_term thy
    val (main, side) = List.partition (exists_Const (curry (op =) x)) prems
    (* term -> bool *)
     val is_good_head = curry (op =) (Const x) o head_of
  in
    if forall is_good_head main then (side, main, concl) else raise NO_TRIPLE ()
  end

(* term -> term *)
val tuple_for_args = HOLogic.mk_tuple o snd o strip_comb

(* indexname * typ -> term list -> term -> term -> term *)
fun wf_constraint_for rel side concl main =
  let
    val core = HOLogic.mk_mem (HOLogic.mk_prod (tuple_for_args main,
                                                tuple_for_args concl), Var rel)
    val t = List.foldl HOLogic.mk_imp core side
    val vars = filter (not_equal rel) (Term.add_vars t [])
  in
    Library.foldl (fn (t', ((x, j), T)) =>
                      HOLogic.all_const T
                      $ Abs (x, T, abstract_over (Var ((x, j), T), t')))
                  (t, vars)
  end

(* indexname * typ -> term list * term list * term -> term *)
fun wf_constraint_for_triple rel (side, main, concl) =
  map (wf_constraint_for rel side concl) main |> foldr1 s_conj

(* Proof.context -> Time.time option -> thm
   -> (Proof.context -> tactic -> tactic) -> bool *)
fun terminates_by ctxt timeout goal tac =
  can (SINGLE (Classical.safe_tac (claset_of ctxt)) #> the
       #> SINGLE (DETERM_TIMEOUT timeout
                                 (tac ctxt (auto_tac (clasimpset_of ctxt))))
       #> the #> Goal.finish ctxt) goal

val max_cached_wfs = 50
val cached_timeout =
  Synchronized.var "Nitpick_HOL.cached_timeout" (SOME Time.zeroTime)
val cached_wf_props =
  Synchronized.var "Nitpick_HOL.cached_wf_props" ([] : (term * bool) list)

val termination_tacs = [Lexicographic_Order.lex_order_tac true,
                        ScnpReconstruct.sizechange_tac]

(* hol_context -> const_table -> styp -> bool *)
fun uncached_is_well_founded_inductive_pred
        ({thy, ctxt, stds, debug, fast_descrs, tac_timeout, intro_table, ...}
         : hol_context) (x as (_, T)) =
  case def_props_for_const thy stds fast_descrs intro_table x of
    [] => raise TERM ("Nitpick_HOL.uncached_is_well_founded_inductive",
                      [Const x])
  | intro_ts =>
    (case map (triple_for_intro_rule thy x) intro_ts
          |> filter_out (null o #2) of
       [] => true
     | triples =>
       let
         val binders_T = HOLogic.mk_tupleT (binder_types T)
         val rel_T = HOLogic.mk_prodT (binders_T, binders_T) --> bool_T
         val j = fold Integer.max (map maxidx_of_term intro_ts) 0 + 1
         val rel = (("R", j), rel_T)
         val prop = Const (@{const_name wf}, rel_T --> bool_T) $ Var rel ::
                    map (wf_constraint_for_triple rel) triples
                    |> foldr1 s_conj |> HOLogic.mk_Trueprop
         val _ = if debug then
                   priority ("Wellfoundedness goal: " ^
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

(* hol_context -> styp -> bool *)
fun is_well_founded_inductive_pred
        (hol_ctxt as {thy, wfs, def_table, wf_cache, ...} : hol_context)
        (x as (s, _)) =
  case triple_lookup (const_match thy) wfs x of
    SOME (SOME b) => b
  | _ => s = @{const_name Nats} orelse s = @{const_name fold_graph'} orelse
         case AList.lookup (op =) (!wf_cache) x of
           SOME (_, wf) => wf
         | NONE =>
           let
             val gfp = (fixpoint_kind_of_const thy def_table x = Gfp)
             val wf = uncached_is_well_founded_inductive_pred hol_ctxt x
           in
             Unsynchronized.change wf_cache (cons (x, (gfp, wf))); wf
           end

(* typ list -> typ -> term -> term *)
fun ap_curry [_] _ t = t
  | ap_curry arg_Ts tuple_T t =
    let val n = length arg_Ts in
      list_abs (map (pair "c") arg_Ts,
                incr_boundvars n t
                $ mk_flat_tuple tuple_T (map Bound (n - 1 downto 0)))
    end

(* int -> term -> int *)
fun num_occs_of_bound_in_term j (t1 $ t2) =
    op + (pairself (num_occs_of_bound_in_term j) (t1, t2))
  | num_occs_of_bound_in_term j (Abs (_, _, t')) =
    num_occs_of_bound_in_term (j + 1) t'
  | num_occs_of_bound_in_term j (Bound j') = if j' = j then 1 else 0
  | num_occs_of_bound_in_term _ _ = 0

(* term -> bool *)
val is_linear_inductive_pred_def =
  let
    (* int -> term -> bool *)
    fun do_disjunct j (Const (@{const_name Ex}, _) $ Abs (_, _, t2)) =
        do_disjunct (j + 1) t2
      | do_disjunct j t =
        case num_occs_of_bound_in_term j t of
          0 => true
        | 1 => exists (curry (op =) (Bound j) o head_of) (conjuncts_of t)
        | _ => false
    (* term -> bool *)
    fun do_lfp_def (Const (@{const_name lfp}, _) $ t2) =
        let val (xs, body) = strip_abs t2 in
          case length xs of
            1 => false
          | n => forall (do_disjunct (n - 1)) (disjuncts_of body)
        end
      | do_lfp_def _ = false
  in do_lfp_def o strip_abs_body end

(* int -> int list list *)
fun n_ptuple_paths 0 = []
  | n_ptuple_paths 1 = []
  | n_ptuple_paths n = [] :: map (cons 2) (n_ptuple_paths (n - 1))
(* int -> typ -> typ -> term -> term *)
val ap_n_split = HOLogic.mk_psplits o n_ptuple_paths

(* term -> term * term *)
val linear_pred_base_and_step_rhss =
  let
    (* term -> term *)
    fun aux (Const (@{const_name lfp}, _) $ t2) =
        let
          val (xs, body) = strip_abs t2
          val arg_Ts = map snd (tl xs)
          val tuple_T = HOLogic.mk_tupleT arg_Ts
          val j = length arg_Ts
          (* int -> term -> term *)
          fun repair_rec j (Const (@{const_name Ex}, T1) $ Abs (s2, T2, t2')) =
              Const (@{const_name Ex}, T1)
              $ Abs (s2, T2, repair_rec (j + 1) t2')
            | repair_rec j (@{const "op &"} $ t1 $ t2) =
              @{const "op &"} $ repair_rec j t1 $ repair_rec j t2
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
          (list_abs (tl xs, incr_bv (~1, j, base_body))
           |> ap_n_split (length arg_Ts) tuple_T bool_T,
           Abs ("y", tuple_T, list_abs (tl xs, step_body)
                              |> ap_n_split (length arg_Ts) tuple_T bool_T))
        end
      | aux t =
        raise TERM ("Nitpick_HOL.linear_pred_base_and_step_rhss.aux", [t])
  in aux end

(* hol_context -> styp -> term -> term *)
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
    val set_T = tuple_T --> bool_T
    val curried_T = tuple_T --> set_T
    val uncurried_T = Type ("*", [tuple_T, tuple_T]) --> bool_T
    val (base_rhs, step_rhs) = linear_pred_base_and_step_rhss fp_app
    val base_x as (base_s, _) = (base_prefix ^ s, outer_Ts ---> set_T)
    val base_eq = HOLogic.mk_eq (list_comb (Const base_x, outer_vars), base_rhs)
                  |> HOLogic.mk_Trueprop
    val _ = add_simps simp_table base_s [base_eq]
    val step_x as (step_s, _) = (step_prefix ^ s, outer_Ts ---> curried_T)
    val step_eq = HOLogic.mk_eq (list_comb (Const step_x, outer_vars), step_rhs)
                  |> HOLogic.mk_Trueprop
    val _ = add_simps simp_table step_s [step_eq]
  in
    list_abs (outer,
              Const (@{const_name Image}, uncurried_T --> set_T --> set_T)
              $ (Const (@{const_name rtrancl}, uncurried_T --> uncurried_T)
                 $ (Const (@{const_name split}, curried_T --> uncurried_T)
                    $ list_comb (Const step_x, outer_bounds)))
              $ list_comb (Const base_x, outer_bounds)
              |> ap_curry tuple_arg_Ts tuple_T)
    |> unfold_defs_in_term hol_ctxt
  end

(* hol_context -> bool -> styp -> term *)
fun unrolled_inductive_pred_const (hol_ctxt as {thy, star_linear_preds,
                                                def_table, simp_table, ...})
                                  gfp (x as (s, T)) =
  let
    val iter_T = iterator_type_for_const gfp x
    val x' as (s', _) = (unrolled_prefix ^ s, iter_T --> T)
    val unrolled_const = Const x' $ zero_const iter_T
    val def = the (def_of_const thy def_table x)
  in
    if is_equational_fun hol_ctxt x' then
      unrolled_const (* already done *)
    else if not gfp andalso is_linear_inductive_pred_def def andalso
         star_linear_preds then
      starred_linear_pred_const hol_ctxt x def
    else
      let
        val j = maxidx_of_term def + 1
        val (outer, fp_app) = strip_abs def
        val outer_bounds = map Bound (length outer - 1 downto 0)
        val cur = Var ((iter_var_prefix, j + 1), iter_T)
        val next = suc_const iter_T $ cur
        val rhs = case fp_app of
                    Const _ $ t =>
                    betapply (t, list_comb (Const x', next :: outer_bounds))
                  | _ => raise TERM ("Nitpick_HOL.unrolled_inductive_pred_\
                                     \const", [fp_app])
        val (inner, naked_rhs) = strip_abs rhs
        val all = outer @ inner
        val bounds = map Bound (length all - 1 downto 0)
        val vars = map (fn (s, T) => Var ((s, j), T)) all
        val eq = HOLogic.mk_eq (list_comb (Const x', cur :: bounds), naked_rhs)
                 |> HOLogic.mk_Trueprop |> curry subst_bounds (rev vars)
        val _ = add_simps simp_table s' [eq]
      in unrolled_const end
  end

(* hol_context -> styp -> term *)
fun raw_inductive_pred_axiom ({thy, def_table, ...} : hol_context) x =
  let
    val def = the (def_of_const thy def_table x)
    val (outer, fp_app) = strip_abs def
    val outer_bounds = map Bound (length outer - 1 downto 0)
    val rhs = case fp_app of
                Const _ $ t => betapply (t, list_comb (Const x, outer_bounds))
              | _ => raise TERM ("Nitpick_HOL.raw_inductive_pred_axiom",
                                 [fp_app])
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
    let val x' = (after_name_sep s, T) in
      raw_inductive_pred_axiom hol_ctxt x' |> subst_atomic [(Const x', Const x)]
    end
  else
    raw_inductive_pred_axiom hol_ctxt x

(* hol_context -> styp -> term list *)
fun raw_equational_fun_axioms (hol_ctxt as {thy, stds, fast_descrs, simp_table,
                                            psimp_table, ...}) x =
  case def_props_for_const thy stds fast_descrs (!simp_table) x of
    [] => (case def_props_for_const thy stds fast_descrs psimp_table x of
             [] => [inductive_pred_axiom hol_ctxt x]
           | psimps => psimps)
  | simps => simps
val equational_fun_axioms = map extensionalize oo raw_equational_fun_axioms
(* hol_context -> styp -> bool *)
fun is_equational_fun_surely_complete hol_ctxt x =
  case raw_equational_fun_axioms hol_ctxt x of
    [@{const Trueprop} $ (Const (@{const_name "op ="}, _) $ t1 $ _)] =>
    strip_comb t1 |> snd |> forall is_Var
  | _ => false

(* term list -> term list *)
fun merge_type_vars_in_terms ts =
  let
    (* typ -> (sort * string) list -> (sort * string) list *)
    fun add_type (TFree (s, S)) table =
        (case AList.lookup (op =) table S of
           SOME s' =>
           if string_ord (s', s) = LESS then AList.update (op =) (S, s') table
           else table
         | NONE => (S, s) :: table)
      | add_type _ table = table
    val table = fold (fold_types (fold_atyps add_type)) ts []
    (* typ -> typ *)
    fun coalesce (TFree (_, S)) = TFree (AList.lookup (op =) table S |> the, S)
      | coalesce T = T
  in map (map_types (map_atyps coalesce)) ts end

(* hol_context -> bool -> typ -> typ list -> typ list *)
fun add_ground_types hol_ctxt binarize =
  let
    fun aux T accum =
      case T of
        Type ("fun", Ts) => fold aux Ts accum
      | Type ("*", Ts) => fold aux Ts accum
      | Type (@{type_name itself}, [T1]) => aux T1 accum
      | Type (_, Ts) =>
        if member (op =) (@{typ prop} :: @{typ bool} :: @{typ unit} :: accum)
                  T then
          accum
        else
          T :: accum
          |> fold aux (case binarized_and_boxed_datatype_constrs hol_ctxt
                                                                 binarize T of
                         [] => Ts
                       | xs => map snd xs)
      | _ => insert (op =) T accum
  in aux end

(* hol_context -> bool -> typ -> typ list *)
fun ground_types_in_type hol_ctxt binarize T =
  add_ground_types hol_ctxt binarize T []
(* hol_context -> term list -> typ list *)
fun ground_types_in_terms hol_ctxt binarize ts =
  fold (fold_types (add_ground_types hol_ctxt binarize)) ts []

(* theory -> const_table -> styp -> int list *)
fun const_format thy def_table (x as (s, T)) =
  if String.isPrefix unrolled_prefix s then
    const_format thy def_table (original_name s, range_type T)
  else if String.isPrefix skolem_prefix s then
    let
      val k = unprefix skolem_prefix s
              |> strip_first_name_sep |> fst |> space_explode "@"
              |> hd |> Int.fromString |> the
    in [k, num_binder_types T - k] end
  else if original_name s <> s then
    [num_binder_types T]
  else case def_of_const thy def_table x of
    SOME t' => if fixpoint_kind_of_rhs t' <> NoFp then
                 let val k = length (strip_abs_vars t') in
                   [k, num_binder_types T - k]
                 end
               else
                 [num_binder_types T]
  | NONE => [num_binder_types T]
(* int list -> int list -> int list *)
fun intersect_formats _ [] = []
  | intersect_formats [] _ = []
  | intersect_formats ks1 ks2 =
    let val ((ks1', k1), (ks2', k2)) = pairself split_last (ks1, ks2) in
      intersect_formats (ks1' @ (if k1 > k2 then [k1 - k2] else []))
                        (ks2' @ (if k2 > k1 then [k2 - k1] else [])) @
      [Int.min (k1, k2)]
    end

(* theory -> const_table -> (term option * int list) list -> term -> int list *)
fun lookup_format thy def_table formats t =
  case AList.lookup (fn (SOME x, SOME y) =>
                        (term_match thy) (x, y) | _ => false)
                    formats (SOME t) of
    SOME format => format
  | NONE => let val format = the (AList.lookup (op =) formats NONE) in
              case t of
                Const x => intersect_formats format
                                             (const_format thy def_table x)
              | _ => format
            end

(* int list -> int list -> typ -> typ *)
fun format_type default_format format T =
  let
    val T = unarize_unbox_and_uniterize_type T
    val format = format |> filter (curry (op <) 0)
  in
    if forall (curry (op =) 1) format then
      T
    else
      let
        val (binder_Ts, body_T) = strip_type T
        val batched =
          binder_Ts
          |> map (format_type default_format default_format)
          |> rev |> chunk_list_unevenly (rev format)
          |> map (HOLogic.mk_tupleT o rev)
      in List.foldl (op -->) body_T batched end
  end
(* theory -> const_table -> (term option * int list) list -> term -> typ *)
fun format_term_type thy def_table formats t =
  format_type (the (AList.lookup (op =) formats NONE))
              (lookup_format thy def_table formats t) (fastype_of t)

(* int list -> int -> int list -> int list *)
fun repair_special_format js m format =
  m - 1 downto 0 |> chunk_list_unevenly (rev format)
                 |> map (rev o filter_out (member (op =) js))
                 |> filter_out null |> map length |> rev

(* hol_context -> string * string -> (term option * int list) list
   -> styp -> term * typ *)
fun user_friendly_const ({thy, evals, def_table, skolems, special_funs, ...}
                         : hol_context) (base_name, step_name) formats =
  let
    val default_format = the (AList.lookup (op =) formats NONE)
    (* styp -> term * typ *)
    fun do_const (x as (s, T)) =
      (if String.isPrefix special_prefix s then
         let
           (* term -> term *)
           val do_term = map_aterms (fn Const x => fst (do_const x) | t' => t')
           val (x' as (_, T'), js, ts) =
             AList.find (op =) (!special_funs) (s, unarize_and_unbox_type T)
             |> the_single
           val max_j = List.last js
           val Ts = List.take (binder_types T', max_j + 1)
           val missing_js = filter_out (member (op =) js) (0 upto max_j)
           val missing_Ts = filter_indices missing_js Ts
           (* int -> indexname *)
           fun nth_missing_var n =
             ((arg_var_prefix ^ nat_subscript (n + 1), 0), nth missing_Ts n)
           val missing_vars = map nth_missing_var (0 upto length missing_js - 1)
           val vars = special_bounds ts @ missing_vars
           val ts' =
             map (fn j =>
                     case AList.lookup (op =) (js ~~ ts) j of
                       SOME t => do_term t
                     | NONE =>
                       Var (nth missing_vars
                                (find_index (curry (op =) j) missing_js)))
                 (0 upto max_j)
           val t = do_const x' |> fst
           val format =
             case AList.lookup (fn (SOME t1, SOME t2) => term_match thy (t1, t2)
                                 | _ => false) formats (SOME t) of
               SOME format =>
               repair_special_format js (num_binder_types T') format
             | NONE =>
               const_format thy def_table x'
               |> repair_special_format js (num_binder_types T')
               |> intersect_formats default_format
         in
           (list_comb (t, ts') |> fold_rev abs_var vars,
            format_type default_format format T)
         end
       else if String.isPrefix uncurry_prefix s then
         let
           val (ss, s') = unprefix uncurry_prefix s
                          |> strip_first_name_sep |>> space_explode "@"
         in
           if String.isPrefix step_prefix s' then
             do_const (s', T)
           else
             let
               val k = the (Int.fromString (hd ss))
               val j = the (Int.fromString (List.last ss))
               val (before_Ts, (tuple_T, rest_T)) =
                 strip_n_binders j T ||> (strip_n_binders 1 #>> hd)
               val T' = before_Ts ---> dest_n_tuple_type k tuple_T ---> rest_T
             in do_const (s', T') end
         end
       else if String.isPrefix unrolled_prefix s then
         let val t = Const (original_name s, range_type T) in
           (lambda (Free (iter_var_prefix, nat_T)) t,
            format_type default_format
                        (lookup_format thy def_table formats t) T)
         end
       else if String.isPrefix base_prefix s then
         (Const (base_name, T --> T) $ Const (unprefix base_prefix s, T),
          format_type default_format default_format T)
       else if String.isPrefix step_prefix s then
         (Const (step_name, T --> T) $ Const (unprefix step_prefix s, T),
          format_type default_format default_format T)
       else if String.isPrefix quot_normal_prefix s then
         let val t = Const (nitpick_prefix ^ "normalize quotient type", T) in
           (t, format_term_type thy def_table formats t)
         end
       else if String.isPrefix skolem_prefix s then
         let
           val ss = the (AList.lookup (op =) (!skolems) s)
           val (Ts, Ts') = chop (length ss) (binder_types T)
           val frees = map Free (ss ~~ Ts)
           val s' = original_name s
         in
           (fold lambda frees (Const (s', Ts' ---> T)),
            format_type default_format
                        (lookup_format thy def_table formats (Const x)) T)
         end
       else if String.isPrefix eval_prefix s then
         let
           val t = nth evals (the (Int.fromString (unprefix eval_prefix s)))
         in (t, format_term_type thy def_table formats t) end
       else if s = @{const_name undefined_fast_The} then
         (Const (nitpick_prefix ^ "The fallback", T),
          format_type default_format
                      (lookup_format thy def_table formats
                           (Const (@{const_name The}, (T --> bool_T) --> T))) T)
       else if s = @{const_name undefined_fast_Eps} then
         (Const (nitpick_prefix ^ "Eps fallback", T),
          format_type default_format
                      (lookup_format thy def_table formats
                           (Const (@{const_name Eps}, (T --> bool_T) --> T))) T)
       else
         let val t = Const (original_name s, T) in
           (t, format_term_type thy def_table formats t)
         end)
      |>> map_types unarize_unbox_and_uniterize_type
      |>> shorten_names_in_term |>> Term.map_abs_vars shortest_name
  in do_const end

(* styp -> string *)
fun assign_operator_for_const (s, T) =
  if String.isPrefix ubfp_prefix s then
    if is_fun_type T then "\<subseteq>" else "\<le>"
  else if String.isPrefix lbfp_prefix s then
    if is_fun_type T then "\<supseteq>" else "\<ge>"
  else if original_name s <> s then
    assign_operator_for_const (after_name_sep s, T)
  else
    "="

end;
