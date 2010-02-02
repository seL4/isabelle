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

  type extended_context = {
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

  val name_sep : string
  val numeral_prefix : string
  val skolem_prefix : string
  val eval_prefix : string
  val original_name : string -> string
  val unbit_and_unbox_type : typ -> typ
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
  val is_boolean_type : typ -> bool
  val is_integer_type : typ -> bool
  val is_bit_type : typ -> bool
  val is_word_type : typ -> bool
  val is_record_type : typ -> bool
  val is_number_type : theory -> typ -> bool
  val const_for_iterator_type : typ -> styp
  val nth_range_type : int -> typ -> typ
  val num_factors_in_type : typ -> int
  val num_binder_types : typ -> int
  val curried_binder_types : typ -> typ list
  val mk_flat_tuple : typ -> term list -> term
  val dest_n_tuple : int -> term -> term list
  val instantiate_type : theory -> typ -> typ -> typ -> typ
  val is_real_datatype : theory -> string -> bool
  val is_quot_type : theory -> typ -> bool
  val is_codatatype : theory -> typ -> bool
  val is_pure_typedef : theory -> typ -> bool
  val is_univ_typedef : theory -> typ -> bool
  val is_datatype : theory -> typ -> bool
  val is_record_constr : styp -> bool
  val is_record_get : theory -> styp -> bool
  val is_record_update : theory -> styp -> bool
  val is_abs_fun : theory -> styp -> bool
  val is_rep_fun : theory -> styp -> bool
  val is_quot_abs_fun : Proof.context -> styp -> bool
  val is_quot_rep_fun : Proof.context -> styp -> bool
  val is_constr : theory -> styp -> bool
  val is_stale_constr : theory -> styp -> bool
  val is_sel : string -> bool
  val is_sel_like_and_no_discr : string -> bool
  val discr_for_constr : styp -> styp
  val num_sels_for_constr_type : typ -> int
  val nth_sel_name_for_constr_name : string -> int -> string
  val nth_sel_for_constr : styp -> int -> styp
  val boxed_nth_sel_for_constr : extended_context -> styp -> int -> styp
  val sel_no_from_name : string -> int
  val eta_expand : typ list -> term -> int -> term
  val extensionalize : term -> term
  val distinctness_formula : typ -> term list -> term
  val register_frac_type : string -> (string * string) list -> theory -> theory
  val unregister_frac_type : string -> theory -> theory
  val register_codatatype : typ -> string -> styp list -> theory -> theory
  val unregister_codatatype : typ -> theory -> theory
  val datatype_constrs : extended_context -> typ -> styp list
  val boxed_datatype_constrs : extended_context -> typ -> styp list
  val num_datatype_constrs : extended_context -> typ -> int
  val constr_name_for_sel_like : string -> string
  val boxed_constr_for_sel : extended_context -> styp -> styp
  val card_of_type : (typ * int) list -> typ -> int
  val bounded_card_of_type : int -> int -> (typ * int) list -> typ -> int
  val bounded_exact_card_of_type :
    extended_context -> int -> int -> (typ * int) list -> typ -> int
  val is_finite_type : extended_context -> typ -> bool
  val all_axioms_of : theory -> term list * term list * term list
  val arity_of_built_in_const : bool -> styp -> int option
  val is_built_in_const : bool -> styp -> bool
  val case_const_names : theory -> (string * int) list
  val const_def_table : Proof.context -> term list -> const_table
  val const_nondef_table : term list -> const_table
  val const_simp_table : Proof.context -> const_table
  val const_psimp_table : Proof.context -> const_table
  val inductive_intro_table : Proof.context -> const_table -> const_table
  val ground_theorem_table : theory -> term list Inttab.table
  val ersatz_table : theory -> (string * string) list
  val def_of_const : theory -> const_table -> styp -> term option
  val is_inductive_pred : extended_context -> styp -> bool
  val is_constr_pattern_lhs : theory -> term -> bool
  val is_constr_pattern_formula : theory -> term -> bool
  val merge_type_vars_in_terms : term list -> term list
  val ground_types_in_type : extended_context -> typ -> typ list
  val ground_types_in_terms : extended_context -> term list -> typ list
  val format_type : int list -> int list -> typ -> typ
  val format_term_type :
    theory -> const_table -> (term option * int list) list -> term -> typ
  val user_friendly_const :
   extended_context -> string * string -> (term option * int list) list
   -> styp -> term * typ
  val assign_operator_for_const : styp -> string
  val preprocess_term :
    extended_context -> term -> ((term list * term list) * (bool * bool)) * term
end;

structure Nitpick_HOL : NITPICK_HOL =
struct

open Nitpick_Util

type const_table = term list Symtab.table
type special_fun = (styp * int list * term list) * styp
type unrolled = styp * styp
type wf_cache = (styp * (bool * bool)) list

type extended_context = {
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

structure Data = Theory_Data(
  type T = {frac_types: (string * (string * string) list) list,
            codatatypes: (string * (string * styp list)) list}
  val empty = {frac_types = [], codatatypes = []}
  val extend = I
  fun merge ({frac_types = fs1, codatatypes = cs1},
               {frac_types = fs2, codatatypes = cs2}) : T =
    {frac_types = AList.merge (op =) (K true) (fs1, fs2),
     codatatypes = AList.merge (op =) (K true) (cs1, cs2)})

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
(* term -> term -> term *)
fun mk_exists v t =
  HOLogic.exists_const (fastype_of v) $ lambda v (incr_boundvars 1 t)

(* term -> term -> term list *)
fun strip_connective conn_t (t as (t0 $ t1 $ t2)) =
    if t0 = conn_t then strip_connective t0 t2 @ strip_connective t0 t1 else [t]
  | strip_connective _ t = [t]
(* term -> term list * term *)
fun strip_any_connective (t as (t0 $ t1 $ t2)) =
    if t0 = @{const "op &"} orelse t0 = @{const "op |"} then
      (strip_connective t0 t, t0)
    else
      ([t], @{const Not})
  | strip_any_connective t = ([t], @{const Not})
(* term -> term list *)
val conjuncts = strip_connective @{const "op &"}
val disjuncts = strip_connective @{const "op |"}

val name_sep = "$"
val numeral_prefix = nitpick_prefix ^ "num" ^ name_sep
val sel_prefix = nitpick_prefix ^ "sel"
val discr_prefix = nitpick_prefix ^ "is" ^ name_sep
val set_prefix = nitpick_prefix ^ "set" ^ name_sep
val lfp_iterator_prefix = nitpick_prefix ^ "lfpit" ^ name_sep
val gfp_iterator_prefix = nitpick_prefix ^ "gfpit" ^ name_sep
val nwf_prefix = nitpick_prefix ^ "nwf" ^ name_sep
val unrolled_prefix = nitpick_prefix ^ "unroll" ^ name_sep
val base_prefix = nitpick_prefix ^ "base" ^ name_sep
val step_prefix = nitpick_prefix ^ "step" ^ name_sep
val ubfp_prefix = nitpick_prefix ^ "ubfp" ^ name_sep
val lbfp_prefix = nitpick_prefix ^ "lbfp" ^ name_sep
val skolem_prefix = nitpick_prefix ^ "sk"
val special_prefix = nitpick_prefix ^ "sp"
val uncurry_prefix = nitpick_prefix ^ "unc"
val eval_prefix = nitpick_prefix ^ "eval"
val bound_var_prefix = "b"
val cong_var_prefix = "c"
val iter_var_prefix = "i"
val val_var_prefix = nitpick_prefix ^ "v"
val arg_var_prefix = "x"

(* int -> string *)
fun sel_prefix_for j = sel_prefix ^ string_of_int j ^ name_sep
fun special_prefix_for j = special_prefix ^ string_of_int j ^ name_sep
(* int -> int -> string *)
fun skolem_prefix_for k j =
  skolem_prefix ^ string_of_int k ^ "@" ^ string_of_int j ^ name_sep
fun uncurry_prefix_for k j =
  uncurry_prefix ^ string_of_int k ^ "@" ^ string_of_int j ^ name_sep

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
   (@{const_name Suc}, 0),
   (@{const_name finite}, 1),
   (@{const_name nat}, 0),
   (@{const_name zero_nat_inst.zero_nat}, 0),
   (@{const_name one_nat_inst.one_nat}, 0),
   (@{const_name plus_nat_inst.plus_nat}, 0),
   (@{const_name minus_nat_inst.minus_nat}, 0),
   (@{const_name times_nat_inst.times_nat}, 0),
   (@{const_name div_nat_inst.div_nat}, 0),
   (@{const_name ord_nat_inst.less_nat}, 2),
   (@{const_name ord_nat_inst.less_eq_nat}, 2),
   (@{const_name nat_gcd}, 0),
   (@{const_name nat_lcm}, 0),
   (@{const_name zero_int_inst.zero_int}, 0),
   (@{const_name one_int_inst.one_int}, 0),
   (@{const_name plus_int_inst.plus_int}, 0),
   (@{const_name minus_int_inst.minus_int}, 0),
   (@{const_name times_int_inst.times_int}, 0),
   (@{const_name div_int_inst.div_int}, 0),
   (@{const_name uminus_int_inst.uminus_int}, 0),
   (@{const_name ord_int_inst.less_int}, 2),
   (@{const_name ord_int_inst.less_eq_int}, 2),
   (@{const_name unknown}, 0),
   (@{const_name is_unknown}, 1),
   (@{const_name Tha}, 1),
   (@{const_name Frac}, 0),
   (@{const_name norm_frac}, 0)]
val built_in_descr_consts =
  [(@{const_name The}, 1),
   (@{const_name Eps}, 1)]
val built_in_typed_consts =
  [((@{const_name of_nat}, nat_T --> int_T), 0),
   ((@{const_name of_nat}, @{typ "unsigned_bit word => signed_bit word"}), 0)]
val built_in_set_consts =
  [(@{const_name lower_semilattice_fun_inst.inf_fun}, 2),
   (@{const_name upper_semilattice_fun_inst.sup_fun}, 2),
   (@{const_name minus_fun_inst.minus_fun}, 2),
   (@{const_name ord_fun_inst.less_eq_fun}, 2)]

(* typ -> typ *)
fun unbit_type @{typ "unsigned_bit word"} = nat_T
  | unbit_type @{typ "signed_bit word"} = int_T
  | unbit_type @{typ bisim_iterator} = nat_T
  | unbit_type (Type (s, Ts as _ :: _)) = Type (s, map unbit_type Ts)
  | unbit_type T = T
fun unbit_and_unbox_type (Type (@{type_name fun_box}, Ts)) =
    unbit_and_unbox_type (Type ("fun", Ts))
  | unbit_and_unbox_type (Type (@{type_name pair_box}, Ts)) =
    Type ("*", map unbit_and_unbox_type Ts)
  | unbit_and_unbox_type @{typ "unsigned_bit word"} = nat_T
  | unbit_and_unbox_type @{typ "signed_bit word"} = int_T
  | unbit_and_unbox_type @{typ bisim_iterator} = nat_T
  | unbit_and_unbox_type (Type (s, Ts as _ :: _)) =
    Type (s, map unbit_and_unbox_type Ts)
  | unbit_and_unbox_type T = T
(* Proof.context -> typ -> string *)
fun string_for_type ctxt = Syntax.string_of_typ ctxt o unbit_and_unbox_type

(* string -> string -> string *)
val prefix_name = Long_Name.qualify o Long_Name.base_name
(* string -> string *)
fun shortest_name s = List.last (space_explode "." s) handle List.Empty => ""
(* string -> term -> term *)
val prefix_abs_vars = Term.map_abs_vars o prefix_name
(* term -> term *)
val shorten_abs_vars = Term.map_abs_vars shortest_name
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
  | term_match thy (t1, t2) = t1 aconv t2

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
fun is_boolean_type T = (T = prop_T orelse T = bool_T)
val is_integer_type =
  member (op =) [nat_T, int_T, @{typ bisim_iterator}] orf is_fp_iterator_type
fun is_bit_type T = (T = @{typ unsigned_bit} orelse T = @{typ signed_bit})
fun is_word_type (Type (@{type_name word}, _)) = true
  | is_word_type _ = false
val is_record_type = not o null o Record.dest_recTs
(* theory -> typ -> bool *)
fun is_frac_type thy (Type (s, [])) =
    not (null (these (AList.lookup (op =) (#frac_types (Data.get thy)) s)))
  | is_frac_type _ _ = false
fun is_number_type thy = is_integer_type orf is_frac_type thy

(* bool -> styp -> typ *)
fun iterator_type_for_const gfp (s, T) =
  Type ((if gfp then gfp_iterator_prefix else lfp_iterator_prefix) ^ s,
        binder_types T)
(* typ -> styp *)
fun const_for_iterator_type (Type (s, Ts)) = (after_name_sep s, Ts ---> bool_T)
  | const_for_iterator_type T =
    raise TYPE ("Nitpick_HOL.const_for_iterator_type", [T], [])

(* int -> typ -> typ * typ *)
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

(* FIXME: Use antiquotation for "code_numeral" below or detect "rep_datatype",
   e.g., by adding a field to "Datatype_Aux.info". *)
(* string -> bool *)
val is_basic_datatype =
    member (op =) [@{type_name "*"}, @{type_name bool}, @{type_name unit},
                   @{type_name nat}, @{type_name int},
                   "Code_Numeral.code_numeral"]

(* theory -> typ -> typ -> typ -> typ *)
fun instantiate_type thy T1 T1' T2 =
  Same.commit (Envir.subst_type_same
                   (Sign.typ_match thy (Logic.varifyT T1, T1') Vartab.empty))
              (Logic.varifyT T2)
  handle Type.TYPE_MATCH =>
         raise TYPE ("Nitpick_HOL.instantiate_type", [T1, T1'], [])

(* theory -> typ -> typ -> styp *)
fun repair_constr_type thy body_T' T =
  instantiate_type thy (body_type T) body_T' T

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
         co_s <> "fun" andalso not (is_basic_datatype co_s) then
        ()
      else
        raise TYPE ("Nitpick_HOL.register_codatatype", [co_T], [])
    val codatatypes = AList.update (op =) (co_s, (case_name, constr_xs))
                                   codatatypes
  in Data.put {frac_types = frac_types, codatatypes = codatatypes} thy end
(* typ -> theory -> theory *)
fun unregister_codatatype co_T = register_codatatype co_T "" []

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
(* theory -> typ -> bool *)
fun is_quot_type _ (Type ("IntEx.my_int", _)) = true (* FIXME *)
  | is_quot_type _ _ = false
fun is_codatatype thy (T as Type (s, _)) =
    not (null (AList.lookup (op =) (#codatatypes (Data.get thy)) s
               |> Option.map snd |> these))
  | is_codatatype _ _ = false
fun is_pure_typedef thy (T as Type (s, _)) =
    is_typedef thy s andalso
    not (is_real_datatype thy s orelse is_quot_type thy T orelse
         is_codatatype thy T orelse is_record_type T orelse is_integer_type T)
  | is_pure_typedef _ _ = false
fun is_univ_typedef thy (Type (s, _)) =
    (case typedef_info thy s of
       SOME {set_def, prop_of_Rep, ...} =>
       (case set_def of
          SOME thm =>
          try (fst o dest_Const o snd o Logic.dest_equals o prop_of) thm
        | NONE =>
          try (fst o dest_Const o snd o HOLogic.dest_mem
               o HOLogic.dest_Trueprop) prop_of_Rep) = SOME @{const_name top}
     | NONE => false)
  | is_univ_typedef _ _ = false
fun is_datatype thy (T as Type (s, _)) =
    (is_typedef thy s orelse is_codatatype thy T orelse T = @{typ ind} orelse
     is_quot_type thy T) andalso
    not (is_basic_datatype s)
  | is_datatype _ _ = false

(* theory -> typ -> (string * typ) list * (string * typ) *)
fun all_record_fields thy T =
  let val (recs, more) = Record.get_extT_fields thy T in
    recs @ more :: all_record_fields thy (snd more)
  end
  handle TYPE _ => []
(* styp -> bool *)
fun is_record_constr (x as (s, T)) =
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
fun is_quot_abs_fun _ ("IntEx.abs_my_int", _) = true (* FIXME *)
  | is_quot_abs_fun _ _ = false
fun is_quot_rep_fun _ ("IntEx.rep_my_int", _) = true (* FIXME *)
  | is_quot_rep_fun _ _ = false

(* theory -> styp -> styp *)
fun mate_of_rep_fun thy (x as (_, Type ("fun", [T1 as Type (s', _), T2]))) =
    (case typedef_info thy s' of
       SOME {Abs_name, ...} => (Abs_name, Type ("fun", [T2, T1]))
     | NONE => raise TERM ("Nitpick_HOL.mate_of_rep_fun", [Const x]))
  | mate_of_rep_fun _ x = raise TERM ("Nitpick_HOL.mate_of_rep_fun", [Const x])
(* theory -> typ -> typ *)
fun rep_type_for_quot_type _ (Type ("IntEx.my_int", [])) = @{typ "nat * nat"}
  | rep_type_for_quot_type _ T =
    raise TYPE ("Nitpick_HOL.rep_type_for_quot_type", [T], [])
(* theory -> typ -> term *)
fun equiv_relation_for_quot_type _ (Type ("IntEx.my_int", [])) =
    Const ("IntEx.intrel", @{typ "(nat * nat) => (nat * nat) => bool"})
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
  let val (x as (s, T)) = (s, unbit_and_unbox_type T) in
    Refute.is_IDT_constructor thy x orelse is_record_constr x orelse
    (is_abs_fun thy x andalso is_pure_typedef thy (range_type T)) orelse
    x = (@{const_name zero_nat_inst.zero_nat}, nat_T) orelse
    is_coconstr thy x
  end
fun is_stale_constr thy (x as (_, T)) =
  is_codatatype thy (body_type T) andalso is_constr_like thy x andalso
  not (is_coconstr thy x)
fun is_constr thy (x as (_, T)) =
  is_constr_like thy x andalso
  not (is_basic_datatype (fst (dest_Type (unbit_type (body_type T))))) andalso
  not (is_stale_constr thy x)
(* string -> bool *)
val is_sel = String.isPrefix discr_prefix orf String.isPrefix sel_prefix
val is_sel_like_and_no_discr =
  String.isPrefix sel_prefix
  orf (member (op =) [@{const_name fst}, @{const_name snd}])

datatype boxability =
  InConstr | InSel | InExpr | InPair | InFunLHS | InFunRHS1 | InFunRHS2

(* boxability -> boxability *)
fun in_fun_lhs_for InConstr = InSel
  | in_fun_lhs_for _ = InFunLHS
fun in_fun_rhs_for InConstr = InConstr
  | in_fun_rhs_for InSel = InSel
  | in_fun_rhs_for InFunRHS1 = InFunRHS2
  | in_fun_rhs_for _ = InFunRHS1

(* extended_context -> boxability -> typ -> bool *)
fun is_boxing_worth_it (ext_ctxt : extended_context) boxy T =
  case T of
    Type ("fun", _) =>
    (boxy = InPair orelse boxy = InFunLHS) andalso
    not (is_boolean_type (body_type T))
  | Type ("*", Ts) =>
    boxy = InPair orelse boxy = InFunRHS1 orelse boxy = InFunRHS2 orelse
    ((boxy = InExpr orelse boxy = InFunLHS) andalso
     exists (is_boxing_worth_it ext_ctxt InPair)
            (map (box_type ext_ctxt InPair) Ts))
  | _ => false
(* extended_context -> boxability -> string * typ list -> string *)
and should_box_type (ext_ctxt as {thy, boxes, ...}) boxy (z as (s, Ts)) =
  case triple_lookup (type_match thy) boxes (Type z) of
    SOME (SOME box_me) => box_me
  | _ => is_boxing_worth_it ext_ctxt boxy (Type z)
(* extended_context -> boxability -> typ -> typ *)
and box_type ext_ctxt boxy T =
  case T of
    Type (z as ("fun", [T1, T2])) =>
    if boxy <> InConstr andalso boxy <> InSel andalso
       should_box_type ext_ctxt boxy z then
      Type (@{type_name fun_box},
            [box_type ext_ctxt InFunLHS T1, box_type ext_ctxt InFunRHS1 T2])
    else
      box_type ext_ctxt (in_fun_lhs_for boxy) T1
      --> box_type ext_ctxt (in_fun_rhs_for boxy) T2
  | Type (z as ("*", Ts)) =>
    if boxy <> InConstr andalso boxy <> InSel
       andalso should_box_type ext_ctxt boxy z then
      Type (@{type_name pair_box}, map (box_type ext_ctxt InSel) Ts)
    else
      Type ("*", map (box_type ext_ctxt
                          (if boxy = InConstr orelse boxy = InSel then boxy
                           else InPair)) Ts)
  | _ => T

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
(* extended_context -> styp -> int -> styp *)
fun boxed_nth_sel_for_constr ext_ctxt =
  apsnd (box_type ext_ctxt InSel) oo nth_sel_for_constr

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
fun zero_const T = Const (@{const_name zero_nat_inst.zero_nat}, T)
fun suc_const T = Const (@{const_name Suc}, T --> T)

(* extended_context -> typ -> styp list *)
fun uncached_datatype_constrs ({thy, stds, ...} : extended_context)
                              (T as Type (s, Ts)) =
    (case AList.lookup (op =) (#codatatypes (Data.get thy)) s of
       SOME (_, xs' as (_ :: _)) => map (apsnd (repair_constr_type thy T)) xs'
     | _ =>
       if is_datatype thy T then
         case Datatype.get_info thy s of
           SOME {index, descr, ...} =>
           let
             val (_, dtyps, constrs) = AList.lookup (op =) descr index |> the
           in
             map (fn (s', Us) =>
                     (s', map (Refute.typ_of_dtyp descr (dtyps ~~ Ts)) Us
                          ---> T)) constrs
             |> (triple_lookup (type_match thy) stds T |> the |> not) ?
                cons (@{const_name NonStd}, @{typ \<xi>} --> T)
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
             [(Abs_name, instantiate_type thy abs_type T rep_type --> T)]
           | NONE =>
             if T = @{typ ind} then
               [dest_Const @{const Zero_Rep}, dest_Const @{const Suc_Rep}]
             else
               []
       else
         [])
  | uncached_datatype_constrs _ _ = []
(* extended_context -> typ -> styp list *)
fun datatype_constrs (ext_ctxt as {constr_cache, ...}) T =
  case AList.lookup (op =) (!constr_cache) T of
    SOME xs => xs
  | NONE =>
    let val xs = uncached_datatype_constrs ext_ctxt T in
      (Unsynchronized.change constr_cache (cons (T, xs)); xs)
    end
fun boxed_datatype_constrs ext_ctxt =
  map (apsnd (box_type ext_ctxt InConstr)) o datatype_constrs ext_ctxt
(* extended_context -> typ -> int *)
val num_datatype_constrs = length oo datatype_constrs

(* string -> string *)
fun constr_name_for_sel_like @{const_name fst} = @{const_name Pair}
  | constr_name_for_sel_like @{const_name snd} = @{const_name Pair}
  | constr_name_for_sel_like s' = original_name s'
(* extended_context -> styp -> styp *)
fun boxed_constr_for_sel ext_ctxt (s', T') =
  let val s = constr_name_for_sel_like s' in
    AList.lookup (op =) (boxed_datatype_constrs ext_ctxt (domain_type T')) s
    |> the |> pair s
  end

(* extended_context -> styp -> term *)
fun discr_term_for_constr ext_ctxt (x as (s, T)) =
  let val dataT = body_type T in
    if s = @{const_name Suc} then
      Abs (Name.uu, dataT,
           @{const Not} $ HOLogic.mk_eq (zero_const dataT, Bound 0))
    else if num_datatype_constrs ext_ctxt dataT >= 2 then
      Const (discr_for_constr x)
    else
      Abs (Name.uu, dataT, @{const True})
  end
(* extended_context -> styp -> term -> term *)
fun discriminate_value (ext_ctxt as {thy, ...}) (x as (_, T)) t =
  case strip_comb t of
    (Const x', args) =>
    if x = x' then @{const True}
    else if is_constr_like thy x' then @{const False}
    else betapply (discr_term_for_constr ext_ctxt x, t)
  | _ => betapply (discr_term_for_constr ext_ctxt x, t)

(* styp -> term -> term *)
fun nth_arg_sel_term_for_constr (x as (s, T)) n =
  let val (arg_Ts, dataT) = strip_type T in
    if dataT = nat_T then
      @{term "%n::nat. minus_nat_inst.minus_nat n one_nat_inst.one_nat"}
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
(* theory -> styp -> term -> int -> typ -> term *)
fun select_nth_constr_arg thy x t n res_T =
  case strip_comb t of
    (Const x', args) =>
    if x = x' then nth args n
    else if is_constr_like thy x' then Const (@{const_name unknown}, res_T)
    else betapply (nth_arg_sel_term_for_constr x n, t)
  | _ => betapply (nth_arg_sel_term_for_constr x n, t)

(* theory -> styp -> term list -> term *)
fun construct_value _ x [] = Const x
  | construct_value thy (x as (s, _)) args =
    let val args = map Envir.eta_contract args in
      case hd args of
        Const (x' as (s', _)) $ t =>
        if is_sel_like_and_no_discr s' andalso
           constr_name_for_sel_like s' = s andalso
           forall (fn (n, t') => select_nth_constr_arg thy x t n dummyT = t')
                  (index_seq 0 (length args) ~~ args) then
          t
        else
          list_comb (Const x, args)
      | _ => list_comb (Const x, args)
    end

(* extended_context -> typ -> term -> term *)
fun constr_expand (ext_ctxt as {thy, ...}) T t =
  (case head_of t of
     Const x => if is_constr_like thy x then t else raise SAME ()
   | _ => raise SAME ())
  handle SAME () =>
         let
           val x' as (_, T') =
             if is_pair_type T then
               let val (T1, T2) = HOLogic.dest_prodT T in
                 (@{const_name Pair}, T1 --> T2 --> T)
               end
             else
               datatype_constrs ext_ctxt T |> hd
           val arg_Ts = binder_types T'
         in
           list_comb (Const x', map2 (select_nth_constr_arg thy x' t)
                                     (index_seq 0 (length arg_Ts)) arg_Ts)
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
(* extended_context -> int -> (typ * int) list -> typ -> int *)
fun bounded_exact_card_of_type ext_ctxt max default_card assigns T =
  let
    (* typ list -> typ -> int *)
    fun aux avoid T =
      (if member (op =) avoid T then
         0
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
         (case datatype_constrs ext_ctxt T of
            [] => if is_integer_type T orelse is_bit_type T then 0
                  else raise SAME ()
          | constrs =>
            let
              val constr_cards =
                datatype_constrs ext_ctxt T
                |> map (Integer.prod o map (aux (T :: avoid)) o binder_types
                        o snd)
            in
              if exists (curry (op =) 0) constr_cards then 0
              else Integer.sum constr_cards
            end)
       | _ => raise SAME ())
      handle SAME () =>
             AList.lookup (op =) assigns T |> the_default default_card
  in Int.min (max, aux [] T) end

(* extended_context -> typ -> bool *)
fun is_finite_type ext_ctxt =
  not_equal 0 o bounded_exact_card_of_type ext_ctxt 1 2 []

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
  fold Term.add_vars ts [] |> sort (TermOrd.fast_indexname_ord o pairself fst)

(* indexname * typ -> term -> term *)
fun abs_var ((s, j), T) body = Abs (s, T, abstract_over (Var ((s, j), T), body))

(* theory -> string -> bool *)
fun is_funky_typedef_name thy s =
  member (op =) [@{type_name unit}, @{type_name "*"}, @{type_name "+"},
                 @{type_name int}] s orelse
  is_frac_type thy (Type (s, []))
(* theory -> term -> bool *)
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

(* theory -> term list * term list * term list *)
fun all_axioms_of thy =
  let
    (* theory list -> term list *)
    val axioms_of_thys = maps Thm.axioms_of #> map (apsnd prop_of)
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
           |> map (prop_of o snd) |> filter is_plain_definition) @
      user_defs @ built_in_defs
  in (defs, built_in_nondefs, user_nondefs) end

(* bool -> styp -> int option *)
fun arity_of_built_in_const fast_descrs (s, T) =
  if s = @{const_name If} then
    if nth_range_type 3 T = @{typ bool} then NONE else SOME 3
  else case AList.lookup (op =)
                (built_in_consts
                 |> fast_descrs ? append built_in_descr_consts) s of
    SOME n => SOME n
  | NONE =>
    case AList.lookup (op =) built_in_typed_consts (s, T) of
      SOME n => SOME n
    | NONE =>
      if is_fun_type T andalso is_set_type (domain_type T) then
        AList.lookup (op =) built_in_set_consts s
      else
        NONE
(* bool -> styp -> bool *)
val is_built_in_const = is_some oo arity_of_built_in_const

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
(* theory -> bool -> const_table -> styp -> term list *)
fun def_props_for_const thy fast_descrs table (x as (s, _)) =
  if is_built_in_const fast_descrs x then
    []
  else
    these (Symtab.lookup table s)
    |> map_filter (try (Refute.specialize_type thy x))
    |> filter (curry (op =) (Const x) o term_under_def)

(* theory -> term -> term option *)
fun normalized_rhs_of thy t =
  let
    (* term option -> term option *)
    fun aux (v as Var _) (SOME t) = SOME (lambda v t)
      | aux (c as Const (@{const_name TYPE}, T)) (SOME t) = SOME (lambda c t)
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
  if is_built_in_const false x orelse original_name s <> s then
    NONE
  else
    x |> def_props_for_const thy false table |> List.last
      |> normalized_rhs_of thy |> Option.map (prefix_abs_vars s)
    handle List.Empty => NONE

datatype fixpoint_kind = Lfp | Gfp | NoFp

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
  | Free _ => raise NOT_SUPPORTED "local definitions"
  | t' => raise TERM ("Nitpick_HOL.pair_for_prop", [t, t'])

(* (Proof.context -> term list) -> Proof.context -> const_table *)
fun table_for get ctxt =
  get ctxt |> map pair_for_prop |> AList.group (op =) |> Symtab.make

(* theory -> (string * int) list *)
fun case_const_names thy =
  Symtab.fold (fn (dtype_s, {index, descr, case_name, ...}) =>
                  if is_basic_datatype dtype_s then
                    I
                  else
                    cons (case_name, AList.lookup (op =) descr index
                                     |> the |> #3 |> length))
              (Datatype.get_all thy) [] @
  map (apsnd length o snd) (#codatatypes (Data.get thy))

(* Proof.context -> term list -> const_table *)
fun const_def_table ctxt ts =
  table_for (map prop_of o Nitpick_Defs.get) ctxt
  |> fold (fn (s, t) => Symtab.map_default (s, []) (cons t))
          (map pair_for_prop ts)
(* term list -> const_table *)
fun const_nondef_table ts =
  fold (fn t => append (map (fn s => (s, t)) (Term.add_const_names t []))) ts []
  |> AList.group (op =) |> Symtab.make
(* Proof.context -> const_table *)
val const_simp_table = table_for (map prop_of o Nitpick_Simps.get)
val const_psimp_table = table_for (map prop_of o Nitpick_Psimps.get)
(* Proof.context -> const_table -> const_table *)
fun inductive_intro_table ctxt def_table =
  table_for (map (unfold_mutually_inductive_preds (ProofContext.theory_of ctxt)
                                                  def_table o prop_of)
             o Nitpick_Intros.get) ctxt
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

(* Similar to "Refute.specialize_type" but returns all matches rather than only
   the first (preorder) match. *)
(* theory -> styp -> term -> term list *)
fun multi_specialize_type thy slack (x as (s, T)) t =
  let
    (* term -> (typ * term) list -> (typ * term) list *)
    fun aux (Const (s', T')) ys =
        if s = s' then
          ys |> (if AList.defined (op =) ys T' then
                   I
                 else
                  cons (T', Refute.monomorphic_term
                                (Sign.typ_match thy (T', T) Vartab.empty) t)
                  handle Type.TYPE_MATCH => I
                       | Refute.REFUTE _ =>
                         if slack then
                           I
                         else
                           raise NOT_SUPPORTED ("too much polymorphism in \
                                                \axiom involving " ^ quote s))
        else
          ys
      | aux _ ys = ys
  in map snd (fold_aterms aux t []) end

(* theory -> bool -> const_table -> styp -> term list *)
fun nondef_props_for_const thy slack table (x as (s, _)) =
  these (Symtab.lookup table s) |> maps (multi_specialize_type thy slack x)

(* theory -> styp -> term list *)
fun inverse_axioms_for_rep_fun thy (x as (_, T)) =
  let val abs_T = domain_type T in
    typedef_info thy (fst (dest_Type abs_T)) |> the
    |> pairf #Abs_inverse #Rep_inverse
    |> pairself (Refute.specialize_type thy x o prop_of o the)
    ||> single |> op ::
  end
(* theory -> styp list -> term list *)
fun optimized_typedef_axioms thy (abs_z as (abs_s, abs_Ts)) =
  let val abs_T = Type abs_z in
    if is_univ_typedef thy abs_T then
      []
    else case typedef_info thy abs_s of
      SOME {abs_type, rep_type, Abs_name, Rep_name, prop_of_Rep, set_name,
            ...} =>
      let
        val rep_T = instantiate_type thy abs_type abs_T rep_type
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
fun optimized_quot_type_axioms thy abs_z =
  let
    val abs_T = Type abs_z
    val rep_T = rep_type_for_quot_type thy abs_T
    val equiv_rel = equiv_relation_for_quot_type thy abs_T
    val a_var = Var (("a", 0), abs_T)
    val x_var = Var (("x", 0), rep_T)
    val y_var = Var (("y", 0), rep_T)
    val x = (@{const_name Quot}, rep_T --> abs_T)
    val sel_a_t = select_nth_constr_arg thy x a_var 0 rep_T
    val normal_t = Const (@{const_name quot_normal}, rep_T --> rep_T)
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
     @{const "==>"}
         $ (HOLogic.mk_Trueprop (@{const Not} $ (is_unknown_t $ normal_x)))
         $ (HOLogic.mk_Trueprop (equiv_rel $ x_var $ normal_x))]
  end

(* theory -> int * styp -> term *)
fun constr_case_body thy (j, (x as (_, T))) =
  let val arg_Ts = binder_types T in
    list_comb (Bound j, map2 (select_nth_constr_arg thy x (Bound 0))
                             (index_seq 0 (length arg_Ts)) arg_Ts)
  end
(* extended_context -> typ -> int * styp -> term -> term *)
fun add_constr_case (ext_ctxt as {thy, ...}) res_T (j, x) res_t =
  Const (@{const_name If}, bool_T --> res_T --> res_T --> res_T)
  $ discriminate_value ext_ctxt x (Bound 0) $ constr_case_body thy (j, x)
  $ res_t
(* extended_context -> typ -> typ -> term *)
fun optimized_case_def (ext_ctxt as {thy, ...}) dataT res_T =
  let
    val xs = datatype_constrs ext_ctxt dataT
    val xs' = filter_out (fn (s, _) => s = @{const_name NonStd}) xs
    val func_Ts = map ((fn T => binder_types T ---> res_T) o snd) xs'
  in
    (if length xs = length xs' then
       let
         val (xs'', x) = split_last xs'
       in
         constr_case_body thy (1, x)
         |> fold_rev (add_constr_case ext_ctxt res_T)
                     (length xs' downto 2 ~~ xs'')
       end
     else
       Const (@{const_name undefined}, dataT --> res_T) $ Bound 0
       |> fold_rev (add_constr_case ext_ctxt res_T)
                   (length xs' downto 1 ~~ xs'))
    |> fold_rev (curry absdummy) (func_Ts @ [dataT])
  end

(* extended_context -> string -> typ -> typ -> term -> term *)
fun optimized_record_get (ext_ctxt as {thy, ...}) s rec_T res_T t =
  let val constr_x = hd (datatype_constrs ext_ctxt rec_T) in
    case no_of_record_field thy s rec_T of
      ~1 => (case rec_T of
               Type (_, Ts as _ :: _) =>
               let
                 val rec_T' = List.last Ts
                 val j = num_record_fields thy rec_T - 1
               in
                 select_nth_constr_arg thy constr_x t j res_T
                 |> optimized_record_get ext_ctxt s rec_T' res_T
               end
             | _ => raise TYPE ("Nitpick_HOL.optimized_record_get", [rec_T],
                                []))
    | j => select_nth_constr_arg thy constr_x t j res_T
  end
(* extended_context -> string -> typ -> term -> term -> term *)
fun optimized_record_update (ext_ctxt as {thy, ...}) s rec_T fun_t rec_t =
  let
    val constr_x as (_, constr_T) = hd (datatype_constrs ext_ctxt rec_T)
    val Ts = binder_types constr_T
    val n = length Ts
    val special_j = no_of_record_field thy s rec_T
    val ts = map2 (fn j => fn T =>
                      let
                        val t = select_nth_constr_arg thy constr_x rec_t j T
                      in
                        if j = special_j then
                          betapply (fun_t, t)
                        else if j = n - 1 andalso special_j = ~1 then
                          optimized_record_update ext_ctxt s
                              (rec_T |> dest_Type |> snd |> List.last) fun_t t
                        else
                          t
                      end) (index_seq 0 n) Ts
  in list_comb (Const constr_x, ts) end

(* Constants "c" whose definition is of the form "c == c'", where "c'" is also a
   constant, are said to be trivial. For those, we ignore the simplification
   rules and use the definition instead, to ensure that built-in symbols like
   "ord_nat_inst.less_eq_nat" are picked up correctly. *)
(* theory -> const_table -> styp -> bool *)
fun has_trivial_definition thy table x =
  case def_of_const thy table x of SOME (Const _) => true | _ => false

(* theory -> const_table -> string * typ -> fixpoint_kind *)
fun fixpoint_kind_of_const thy table x =
  if is_built_in_const false x then
    NoFp
  else
    fixpoint_kind_of_rhs (the (def_of_const thy table x))
    handle Option.Option => NoFp

(* extended_context -> styp -> bool *)
fun is_real_inductive_pred ({thy, fast_descrs, def_table, intro_table, ...}
                            : extended_context) x =
  not (null (def_props_for_const thy fast_descrs intro_table x)) andalso
  fixpoint_kind_of_const thy def_table x <> NoFp
fun is_real_equational_fun ({thy, fast_descrs, simp_table, psimp_table, ...}
                            : extended_context) x =
  exists (fn table => not (null (def_props_for_const thy fast_descrs table x)))
         [!simp_table, psimp_table]
fun is_inductive_pred ext_ctxt =
  is_real_inductive_pred ext_ctxt andf (not o is_real_equational_fun ext_ctxt)
fun is_equational_fun (ext_ctxt as {thy, def_table, ...}) =
  (is_real_equational_fun ext_ctxt orf is_real_inductive_pred ext_ctxt
   orf (String.isPrefix ubfp_prefix orf String.isPrefix lbfp_prefix) o fst)
  andf (not o has_trivial_definition thy def_table)

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
      (Const (x as (s, _)), args) =>
      is_constr_like thy x andalso forall (is_constr_pattern thy) args
    | _ => false
fun is_constr_pattern_lhs thy t =
  forall (is_constr_pattern thy) (snd (strip_comb t))
fun is_constr_pattern_formula thy t =
  case lhs_of_equation t of
    SOME t' => is_constr_pattern_lhs thy t'
  | NONE => false

val unfold_max_depth = 255
val axioms_max_depth = 255

(* extended_context -> term -> term *)
fun unfold_defs_in_term (ext_ctxt as {thy, destroy_constrs, fast_descrs,
                                      case_names, def_table, ground_thm_table,
                                      ersatz_table, ...}) =
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
              if is_integer_type ran_T then
                Const (s, ran_T)
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
      | (t0 as Const (x as (@{const_name Sigma}, T))) $ t1
        $ (t2 as Abs (_, _, t2')) =>
        betapplys (t0 |> loose_bvar1 (t2', 0) ? do_term depth Ts,
                   map (do_term depth Ts) [t1, t2])
      | Const (x as (@{const_name distinct},
               Type ("fun", [Type (@{type_name list}, [T']), _])))
        $ (t1 as _ $ _) =>
        (t1 |> HOLogic.dest_list |> distinctness_formula T'
         handle TERM _ => do_const depth Ts t x [t1])
      | (t0 as Const (x as (@{const_name If}, _))) $ t1 $ t2 $ t3 =>
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
              select_nth_constr_arg thy x (Bound 0) n res_T), [])
      | select_nth_constr_arg_with_args depth Ts x (t :: ts) n res_T =
        (select_nth_constr_arg thy x (do_term depth Ts t) n res_T, ts)
    (* int -> typ list -> term -> styp -> term list -> term *)
    and do_const depth Ts t (x as (s, T)) ts =
      case AList.lookup (op =) ersatz_table s of
        SOME s' =>
        do_const (depth + 1) Ts (list_comb (Const (s', T), ts)) (s', T) ts
      | NONE =>
        let
          val (const, ts) =
            if is_built_in_const fast_descrs x then
              (Const x, ts)
            else case AList.lookup (op =) case_names s of
              SOME n =>
              let
                val (dataT, res_T) = nth_range_type n T
                                     |> pairf domain_type range_type
              in
                (optimized_case_def ext_ctxt dataT res_T
                 |> do_term (depth + 1) Ts, ts)
              end
            | _ =>
              if is_constr thy x then
                (Const x, ts)
              else if is_stale_constr thy x then
                raise NOT_SUPPORTED ("(non-co)constructors of codatatypes \
                                     \(\"" ^ s ^ "\")")
              else if is_quot_abs_fun thy x then
                let
                  val rep_T = domain_type T
                  val abs_T = range_type T
                in
                  (Abs (Name.uu, rep_T,
                        Const (@{const_name Quot}, rep_T --> abs_T)
                               $ (Const (@{const_name quot_normal},
                                         rep_T --> rep_T) $ Bound 0)), ts)
                end
              else if is_quot_rep_fun thy x then
                let
                  val abs_T = domain_type T
                  val rep_T = range_type T
                  val x' = (@{const_name Quot}, rep_T --> abs_T)
                in select_nth_constr_arg_with_args depth Ts x' ts 0 rep_T end
              else if is_record_get thy x then
                case length ts of
                  0 => (do_term depth Ts (eta_expand Ts t 1), [])
                | _ => (optimized_record_get ext_ctxt s (domain_type T)
                            (range_type T) (do_term depth Ts (hd ts)), tl ts)
              else if is_record_update thy x then
                case length ts of
                  2 => (optimized_record_update ext_ctxt
                            (unsuffix Record.updateN s) (nth_range_type 2 T)
                            (do_term depth Ts (hd ts))
                            (do_term depth Ts (nth ts 1)), [])
                | n => (do_term depth Ts (eta_expand Ts t (2 - n)), [])
              else if is_rep_fun thy x then
                let val x' = mate_of_rep_fun thy x in
                  if is_constr thy x' then
                    select_nth_constr_arg_with_args depth Ts x' ts 0
                                                    (range_type T)
                  else
                    (Const x, ts)
                end
              else if is_equational_fun ext_ctxt x then
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

(* extended_context -> typ -> term list *)
fun codatatype_bisim_axioms (ext_ctxt as {thy, ...}) T =
  let
    val xs = datatype_constrs ext_ctxt T
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
      $ select_nth_constr_arg thy x x_var n nth_T
      $ select_nth_constr_arg thy x y_var n nth_T
    (* styp -> term *)
    fun case_func (x as (_, T)) =
      let
        val arg_Ts = binder_types T
        val core_t =
          discriminate_value ext_ctxt x y_var ::
          map2 (nth_sub_bisim x) (index_seq 0 (length arg_Ts)) arg_Ts
          |> foldr1 s_conj
      in List.foldr absdummy core_t arg_Ts end
  in
    [HOLogic.eq_const bool_T $ (bisim_const $ n_var $ x_var $ y_var)
     $ (@{term "op |"} $ (HOLogic.eq_const iter_T $ n_var $ zero_const iter_T)
        $ (betapplys (optimized_case_def ext_ctxt T bool_T,
                      map case_func xs @ [x_var]))),
     HOLogic.eq_const set_T $ (bisim_const $ bisim_max $ x_var)
     $ (Const (@{const_name insert}, T --> set_T --> set_T)
        $ x_var $ Const (@{const_name bot_fun_inst.bot_fun}, set_T))]
    |> map HOLogic.mk_Trueprop
  end

exception NO_TRIPLE of unit

(* theory -> styp -> term -> term list * term list * term *)
fun triple_for_intro_rule thy x t =
  let
    val prems = Logic.strip_imp_prems t |> map (ObjectLogic.atomize_term thy)
    val concl = Logic.strip_imp_concl t |> ObjectLogic.atomize_term thy
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

val max_cached_wfs = 100
val cached_timeout = Unsynchronized.ref (SOME Time.zeroTime)
val cached_wf_props : (term * bool) list Unsynchronized.ref =
  Unsynchronized.ref []

val termination_tacs = [Lexicographic_Order.lex_order_tac true,
                        ScnpReconstruct.sizechange_tac]

(* extended_context -> const_table -> styp -> bool *)
fun uncached_is_well_founded_inductive_pred
        ({thy, ctxt, debug, fast_descrs, tac_timeout, intro_table, ...}
         : extended_context) (x as (_, T)) =
  case def_props_for_const thy fast_descrs intro_table x of
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
         if tac_timeout = (!cached_timeout) andalso
            length (!cached_wf_props) < max_cached_wfs then
           ()
         else
           (cached_wf_props := []; cached_timeout := tac_timeout);
         case AList.lookup (op =) (!cached_wf_props) prop of
           SOME wf => wf
         | NONE =>
           let
             val goal = prop |> cterm_of thy |> Goal.init
             val wf = exists (terminates_by ctxt tac_timeout goal)
                             termination_tacs
           in Unsynchronized.change cached_wf_props (cons (prop, wf)); wf end
       end)
    handle List.Empty => false
         | NO_TRIPLE () => false

(* The type constraint below is a workaround for a Poly/ML bug. *)

(* extended_context -> styp -> bool *)
fun is_well_founded_inductive_pred
        (ext_ctxt as {thy, wfs, def_table, wf_cache, ...} : extended_context)
        (x as (s, _)) =
  case triple_lookup (const_match thy) wfs x of
    SOME (SOME b) => b
  | _ => s = @{const_name Nats} orelse s = @{const_name fold_graph'} orelse
         case AList.lookup (op =) (!wf_cache) x of
                  SOME (_, wf) => wf
                | NONE =>
                  let
                    val gfp = (fixpoint_kind_of_const thy def_table x = Gfp)
                    val wf = uncached_is_well_founded_inductive_pred ext_ctxt x
                  in
                    Unsynchronized.change wf_cache (cons (x, (gfp, wf))); wf
                  end

(* typ list -> typ -> typ -> term -> term *)
fun ap_curry [_] _ _ t = t
  | ap_curry arg_Ts tuple_T body_T t =
    let val n = length arg_Ts in
      list_abs (map (pair "c") arg_Ts,
                incr_boundvars n t
                $ mk_flat_tuple tuple_T (map Bound (n - 1 downto 0)))
    end

(* int -> term -> int *)
fun num_occs_of_bound_in_term j (t1 $ t2) =
    op + (pairself (num_occs_of_bound_in_term j) (t1, t2))
  | num_occs_of_bound_in_term j (Abs (s, T, t')) =
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
        | 1 => exists (curry (op =) (Bound j) o head_of) (conjuncts t)
        | _ => false
    (* term -> bool *)
    fun do_lfp_def (Const (@{const_name lfp}, _) $ t2) =
        let val (xs, body) = strip_abs t2 in
          case length xs of
            1 => false
          | n => forall (do_disjunct (n - 1)) (disjuncts body)
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
                           (disjuncts body)
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

(* extended_context -> styp -> term -> term *)
fun starred_linear_pred_const (ext_ctxt as {simp_table, ...}) (x as (s, T))
                              def =
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
              |> ap_curry tuple_arg_Ts tuple_T bool_T)
    |> unfold_defs_in_term ext_ctxt
  end

(* extended_context -> bool -> styp -> term *)
fun unrolled_inductive_pred_const (ext_ctxt as {thy, star_linear_preds,
                                                def_table, simp_table, ...})
                                  gfp (x as (s, T)) =
  let
    val iter_T = iterator_type_for_const gfp x
    val x' as (s', _) = (unrolled_prefix ^ s, iter_T --> T)
    val unrolled_const = Const x' $ zero_const iter_T
    val def = the (def_of_const thy def_table x)
  in
    if is_equational_fun ext_ctxt x' then
      unrolled_const (* already done *)
    else if not gfp andalso is_linear_inductive_pred_def def andalso
         star_linear_preds then
      starred_linear_pred_const ext_ctxt x def
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

(* extended_context -> styp -> term *)
fun raw_inductive_pred_axiom ({thy, def_table, ...} : extended_context) x =
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
fun inductive_pred_axiom ext_ctxt (x as (s, T)) =
  if String.isPrefix ubfp_prefix s orelse String.isPrefix lbfp_prefix s then
    let val x' = (after_name_sep s, T) in
      raw_inductive_pred_axiom ext_ctxt x' |> subst_atomic [(Const x', Const x)]
    end
  else
    raw_inductive_pred_axiom ext_ctxt x

(* extended_context -> styp -> term list *)
fun raw_equational_fun_axioms (ext_ctxt as {thy, fast_descrs, simp_table,
                                            psimp_table, ...}) (x as (s, _)) =
  case def_props_for_const thy fast_descrs (!simp_table) x of
    [] => (case def_props_for_const thy fast_descrs psimp_table x of
             [] => [inductive_pred_axiom ext_ctxt x]
           | psimps => psimps)
  | simps => simps

val equational_fun_axioms = map extensionalize oo raw_equational_fun_axioms

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
    fun coalesce (TFree (s, S)) = TFree (AList.lookup (op =) table S |> the, S)
      | coalesce T = T
  in map (map_types (map_atyps coalesce)) ts end

(* extended_context -> typ -> typ list -> typ list *)
fun add_ground_types ext_ctxt T accum =
  case T of
    Type ("fun", Ts) => fold (add_ground_types ext_ctxt) Ts accum
  | Type ("*", Ts) => fold (add_ground_types ext_ctxt) Ts accum
  | Type (@{type_name itself}, [T1]) => add_ground_types ext_ctxt T1 accum
  | Type (_, Ts) =>
    if member (op =) (@{typ prop} :: @{typ bool} :: @{typ unit} :: accum) T then
      accum
    else
      T :: accum
      |> fold (add_ground_types ext_ctxt)
              (case boxed_datatype_constrs ext_ctxt T of
                 [] => Ts
               | xs => map snd xs)
  | _ => insert (op =) T accum
(* extended_context -> typ -> typ list *)
fun ground_types_in_type ext_ctxt T = add_ground_types ext_ctxt T []
(* extended_context -> term list -> typ list *)
fun ground_types_in_terms ext_ctxt ts =
  fold (fold_types (add_ground_types ext_ctxt)) ts []

(* typ list -> int -> term -> bool *)
fun has_heavy_bounds_or_vars Ts level t =
  let
    (* typ list -> bool *)
    fun aux [] = false
      | aux [T] = is_fun_type T orelse is_pair_type T
      | aux _ = true
  in aux (map snd (Term.add_vars t []) @ map (nth Ts) (loose_bnos t)) end

(* typ list -> int -> int -> int -> term -> term *)
fun fresh_value_var Ts k n j t =
  Var ((val_var_prefix ^ nat_subscript (n - j), k), fastype_of1 (Ts, t))

(* theory -> typ list -> bool -> int -> int -> term -> term list -> term list
   -> term * term list *)
fun pull_out_constr_comb thy Ts relax k level t args seen =
  let val t_comb = list_comb (t, args) in
    case t of
      Const x =>
      if not relax andalso is_constr thy x andalso
         not (is_fun_type (fastype_of1 (Ts, t_comb))) andalso
         has_heavy_bounds_or_vars Ts level t_comb andalso
         not (loose_bvar (t_comb, level)) then
        let
          val (j, seen) = case find_index (curry (op =) t_comb) seen of
                            ~1 => (0, t_comb :: seen)
                          | j => (j, seen)
        in (fresh_value_var Ts k (length seen) j t_comb, seen) end
      else
        (t_comb, seen)
    | _ => (t_comb, seen)
  end

(* (term -> term) -> typ list -> int -> term list -> term list *)
fun equations_for_pulled_out_constrs mk_eq Ts k seen =
  let val n = length seen in
    map2 (fn j => fn t => mk_eq (fresh_value_var Ts k n j t, t))
         (index_seq 0 n) seen
  end

(* theory -> bool -> term -> term *)
fun pull_out_universal_constrs thy def t =
  let
    val k = maxidx_of_term t + 1
    (* typ list -> bool -> term -> term list -> term list -> term * term list *)
    fun do_term Ts def t args seen =
      case t of
        (t0 as Const (@{const_name "=="}, _)) $ t1 $ t2 =>
        do_eq_or_imp Ts true def t0 t1 t2 seen
      | (t0 as @{const "==>"}) $ t1 $ t2 =>
        if def then (t, []) else do_eq_or_imp Ts false def t0 t1 t2 seen
      | (t0 as Const (@{const_name "op ="}, _)) $ t1 $ t2 =>
        do_eq_or_imp Ts true def t0 t1 t2 seen
      | (t0 as @{const "op -->"}) $ t1 $ t2 =>
        do_eq_or_imp Ts false def t0 t1 t2 seen
      | Abs (s, T, t') =>
        let val (t', seen) = do_term (T :: Ts) def t' [] seen in
          (list_comb (Abs (s, T, t'), args), seen)
        end
      | t1 $ t2 =>
        let val (t2, seen) = do_term Ts def t2 [] seen in
          do_term Ts def t1 (t2 :: args) seen
        end
      | _ => pull_out_constr_comb thy Ts def k 0 t args seen
    (* typ list -> bool -> bool -> term -> term -> term -> term list
       -> term * term list *)
    and do_eq_or_imp Ts eq def t0 t1 t2 seen =
      let
        val (t2, seen) = if eq andalso def then (t2, seen)
                         else do_term Ts false t2 [] seen
        val (t1, seen) = do_term Ts false t1 [] seen
      in (t0 $ t1 $ t2, seen) end
    val (concl, seen) = do_term [] def t [] []
  in
    Logic.list_implies (equations_for_pulled_out_constrs Logic.mk_equals [] k
                                                         seen, concl)
  end

(* extended_context -> bool -> term -> term *)
fun destroy_pulled_out_constrs (ext_ctxt as {thy, ...}) axiom t =
  let
    (* styp -> int *)
    val num_occs_of_var =
      fold_aterms (fn Var z => (fn f => fn z' => f z' |> z = z' ? Integer.add 1)
                    | _ => I) t (K 0)
    (* bool -> term -> term *)
    fun aux careful ((t0 as Const (@{const_name "=="}, _)) $ t1 $ t2) =
        aux_eq careful true t0 t1 t2
      | aux careful ((t0 as @{const "==>"}) $ t1 $ t2) =
        t0 $ aux false t1 $ aux careful t2
      | aux careful ((t0 as Const (@{const_name "op ="}, _)) $ t1 $ t2) =
        aux_eq careful true t0 t1 t2
      | aux careful ((t0 as @{const "op -->"}) $ t1 $ t2) =
        t0 $ aux false t1 $ aux careful t2
      | aux careful (Abs (s, T, t')) = Abs (s, T, aux careful t')
      | aux careful (t1 $ t2) = aux careful t1 $ aux careful t2
      | aux _ t = t
    (* bool -> bool -> term -> term -> term -> term *)
    and aux_eq careful pass1 t0 t1 t2 =
      ((if careful then
          raise SAME ()
        else if axiom andalso is_Var t2 andalso
                num_occs_of_var (dest_Var t2) = 1 then
          @{const True}
        else case strip_comb t2 of
          (* The first case is not as general as it could be. *)
          (Const (@{const_name PairBox}, _),
                  [Const (@{const_name fst}, _) $ Var z1,
                   Const (@{const_name snd}, _) $ Var z2]) =>
          if z1 = z2 andalso num_occs_of_var z1 = 2 then @{const True}
          else raise SAME ()
        | (Const (x as (s, T)), args) =>
          let val arg_Ts = binder_types T in
            if length arg_Ts = length args andalso
               (is_constr thy x orelse s = @{const_name Pair} orelse
                x = (@{const_name Suc}, nat_T --> nat_T)) andalso
               (not careful orelse not (is_Var t1) orelse
                String.isPrefix val_var_prefix (fst (fst (dest_Var t1)))) then
              discriminate_value ext_ctxt x t1 ::
              map3 (sel_eq x t1) (index_seq 0 (length args)) arg_Ts args
              |> foldr1 s_conj
            else
              raise SAME ()
          end
        | _ => raise SAME ())
       |> body_type (type_of t0) = prop_T ? HOLogic.mk_Trueprop)
      handle SAME () => if pass1 then aux_eq careful false t0 t2 t1
                        else t0 $ aux false t2 $ aux false t1
    (* styp -> term -> int -> typ -> term -> term *)
    and sel_eq x t n nth_T nth_t =
      HOLogic.eq_const nth_T $ nth_t $ select_nth_constr_arg thy x t n nth_T
      |> aux false
  in aux axiom t end

(* theory -> term -> term *)
fun simplify_constrs_and_sels thy t =
  let
    (* term -> int -> term *)
    fun is_nth_sel_on t' n (Const (s, _) $ t) =
        (t = t' andalso is_sel_like_and_no_discr s andalso
         sel_no_from_name s = n)
      | is_nth_sel_on _ _ _ = false
    (* term -> term list -> term *)
    fun do_term (Const (@{const_name Rep_Frac}, _)
                 $ (Const (@{const_name Abs_Frac}, _) $ t1)) [] = do_term t1 []
      | do_term (Const (@{const_name Abs_Frac}, _)
                 $ (Const (@{const_name Rep_Frac}, _) $ t1)) [] = do_term t1 []
      | do_term (t1 $ t2) args = do_term t1 (do_term t2 [] :: args)
      | do_term (t as Const (x as (s, T))) (args as _ :: _) =
        ((if is_constr_like thy x then
            if length args = num_binder_types T then
              case hd args of
                Const (x' as (_, T')) $ t' =>
                if domain_type T' = body_type T andalso
                   forall (uncurry (is_nth_sel_on t'))
                          (index_seq 0 (length args) ~~ args) then
                  t'
                else
                  raise SAME ()
              | _ => raise SAME ()
            else
              raise SAME ()
          else if is_sel_like_and_no_discr s then
            case strip_comb (hd args) of
              (Const (x' as (s', T')), ts') =>
              if is_constr_like thy x' andalso
                 constr_name_for_sel_like s = s' andalso
                 not (exists is_pair_type (binder_types T')) then
                list_comb (nth ts' (sel_no_from_name s), tl args)
              else
                raise SAME ()
            | _ => raise SAME ()
          else
            raise SAME ())
         handle SAME () => betapplys (t, args))
      | do_term (Abs (s, T, t')) args =
        betapplys (Abs (s, T, do_term t' []), args)
      | do_term t args = betapplys (t, args)
  in do_term t [] end

(* term -> term *)
fun curry_assms (@{const "==>"} $ (@{const Trueprop}
                                   $ (@{const "op &"} $ t1 $ t2)) $ t3) =
    curry_assms (Logic.list_implies ([t1, t2] |> map HOLogic.mk_Trueprop, t3))
  | curry_assms (@{const "==>"} $ t1 $ t2) =
    @{const "==>"} $ curry_assms t1 $ curry_assms t2
  | curry_assms t = t

(* term -> term *)
val destroy_universal_equalities =
  let
    (* term list -> (indexname * typ) list -> term -> term *)
    fun aux prems zs t =
      case t of
        @{const "==>"} $ t1 $ t2 => aux_implies prems zs t1 t2
      | _ => Logic.list_implies (rev prems, t)
    (* term list -> (indexname * typ) list -> term -> term -> term *)
    and aux_implies prems zs t1 t2 =
      case t1 of
        Const (@{const_name "=="}, _) $ Var z $ t' => aux_eq prems zs z t' t1 t2
      | @{const Trueprop} $ (Const (@{const_name "op ="}, _) $ Var z $ t') =>
        aux_eq prems zs z t' t1 t2
      | @{const Trueprop} $ (Const (@{const_name "op ="}, _) $ t' $ Var z) =>
        aux_eq prems zs z t' t1 t2
      | _ => aux (t1 :: prems) (Term.add_vars t1 zs) t2
    (* term list -> (indexname * typ) list -> indexname * typ -> term -> term
       -> term -> term *)
    and aux_eq prems zs z t' t1 t2 =
      if not (member (op =) zs z) andalso
         not (exists_subterm (curry (op =) (Var z)) t') then
        aux prems zs (subst_free [(Var z, t')] t2)
      else
        aux (t1 :: prems) (Term.add_vars t1 zs) t2
  in aux [] [] end

(* theory -> term -> term *)
fun pull_out_existential_constrs thy t =
  let
    val k = maxidx_of_term t + 1
    (* typ list -> int -> term -> term list -> term list -> term * term list *)
    fun aux Ts num_exists t args seen =
      case t of
        (t0 as Const (@{const_name Ex}, _)) $ Abs (s1, T1, t1) =>
        let
          val (t1, seen') = aux (T1 :: Ts) (num_exists + 1) t1 [] []
          val n = length seen'
          (* unit -> term list *)
          fun vars () = map2 (fresh_value_var Ts k n) (index_seq 0 n) seen'
        in
          (equations_for_pulled_out_constrs HOLogic.mk_eq Ts k seen'
           |> List.foldl s_conj t1 |> fold mk_exists (vars ())
           |> curry3 Abs s1 T1 |> curry (op $) t0, seen)
        end
      | t1 $ t2 =>
        let val (t2, seen) = aux Ts num_exists t2 [] seen in
          aux Ts num_exists t1 (t2 :: args) seen
        end
      | Abs (s, T, t') =>
        let
          val (t', seen) = aux (T :: Ts) 0 t' [] (map (incr_boundvars 1) seen)
        in (list_comb (Abs (s, T, t'), args), map (incr_boundvars ~1) seen) end
      | _ =>
        if num_exists > 0 then
          pull_out_constr_comb thy Ts false k num_exists t args seen
        else
          (list_comb (t, args), seen)
  in aux [] 0 t [] [] |> fst end

(* theory -> int -> term list -> term list -> (term * term list) option *)
fun find_bound_assign _ _ _ [] = NONE
  | find_bound_assign thy j seen (t :: ts) =
    let
      (* bool -> term -> term -> (term * term list) option *)
      fun aux pass1 t1 t2 =
        (if loose_bvar1 (t2, j) then
           if pass1 then aux false t2 t1 else raise SAME ()
         else case t1 of
           Bound j' => if j' = j then SOME (t2, ts @ seen) else raise SAME ()
         | Const (s, Type ("fun", [T1, T2])) $ Bound j' =>
           if j' = j andalso s = sel_prefix_for 0 ^ @{const_name FunBox} then
             SOME (construct_value thy (@{const_name FunBox}, T2 --> T1) [t2],
                   ts @ seen)
           else
             raise SAME ()
         | _ => raise SAME ())
        handle SAME () => find_bound_assign thy j (t :: seen) ts
    in
      case t of
        Const (@{const_name "op ="}, _) $ t1 $ t2 => aux true t1 t2
      | _ => find_bound_assign thy j (t :: seen) ts
    end

(* int -> term -> term -> term *)
fun subst_one_bound j arg t =
  let
    fun aux (Bound i, lev) =
        if i < lev then raise SAME ()
        else if i = lev then incr_boundvars (lev - j) arg
        else Bound (i - 1)
      | aux (Abs (a, T, body), lev) = Abs (a, T, aux (body, lev + 1))
      | aux (f $ t, lev) =
        (aux (f, lev) $ (aux (t, lev) handle SAME () => t)
         handle SAME () => f $ aux (t, lev))
      | aux _ = raise SAME ()
  in aux (t, j) handle SAME () => t end

(* theory -> term -> term *)
fun destroy_existential_equalities thy =
  let
    (* string list -> typ list -> term list -> term *)
    fun kill [] [] ts = foldr1 s_conj ts
      | kill (s :: ss) (T :: Ts) ts =
        (case find_bound_assign thy (length ss) [] ts of
           SOME (_, []) => @{const True}
         | SOME (arg_t, ts) =>
           kill ss Ts (map (subst_one_bound (length ss)
                                (incr_bv (~1, length ss + 1, arg_t))) ts)
         | NONE =>
           Const (@{const_name Ex}, (T --> bool_T) --> bool_T)
           $ Abs (s, T, kill ss Ts ts))
      | kill _ _ _ = raise UnequalLengths
    (* string list -> typ list -> term -> term *)
    fun gather ss Ts ((t0 as Const (@{const_name Ex}, _)) $ Abs (s1, T1, t1)) =
        gather (ss @ [s1]) (Ts @ [T1]) t1
      | gather [] [] (Abs (s, T, t1)) = Abs (s, T, gather [] [] t1)
      | gather [] [] (t1 $ t2) = gather [] [] t1 $ gather [] [] t2
      | gather [] [] t = t
      | gather ss Ts t = kill ss Ts (conjuncts (gather [] [] t))
  in gather [] [] end

(* term -> term *)
fun distribute_quantifiers t =
  case t of
    (t0 as Const (@{const_name All}, T0)) $ Abs (s, T1, t1) =>
    (case t1 of
       (t10 as @{const "op &"}) $ t11 $ t12 =>
       t10 $ distribute_quantifiers (t0 $ Abs (s, T1, t11))
           $ distribute_quantifiers (t0 $ Abs (s, T1, t12))
     | (t10 as @{const Not}) $ t11 =>
       t10 $ distribute_quantifiers (Const (@{const_name Ex}, T0)
                                     $ Abs (s, T1, t11))
     | t1 =>
       if not (loose_bvar1 (t1, 0)) then
         distribute_quantifiers (incr_boundvars ~1 t1)
       else
         t0 $ Abs (s, T1, distribute_quantifiers t1))
  | (t0 as Const (@{const_name Ex}, T0)) $ Abs (s, T1, t1) =>
    (case distribute_quantifiers t1 of
       (t10 as @{const "op |"}) $ t11 $ t12 =>
       t10 $ distribute_quantifiers (t0 $ Abs (s, T1, t11))
           $ distribute_quantifiers (t0 $ Abs (s, T1, t12))
     | (t10 as @{const "op -->"}) $ t11 $ t12 =>
       t10 $ distribute_quantifiers (Const (@{const_name All}, T0)
                                     $ Abs (s, T1, t11))
           $ distribute_quantifiers (t0 $ Abs (s, T1, t12))
     | (t10 as @{const Not}) $ t11 =>
       t10 $ distribute_quantifiers (Const (@{const_name All}, T0)
                                     $ Abs (s, T1, t11))
     | t1 =>
       if not (loose_bvar1 (t1, 0)) then
         distribute_quantifiers (incr_boundvars ~1 t1)
       else
         t0 $ Abs (s, T1, distribute_quantifiers t1))
  | t1 $ t2 => distribute_quantifiers t1 $ distribute_quantifiers t2
  | Abs (s, T, t') => Abs (s, T, distribute_quantifiers t')
  | _ => t

(* int -> int -> (int -> int) -> term -> term *)
fun renumber_bounds j n f t =
  case t of
    t1 $ t2 => renumber_bounds j n f t1 $ renumber_bounds j n f t2
  | Abs (s, T, t') => Abs (s, T, renumber_bounds (j + 1) n f t')
  | Bound j' =>
    Bound (if j' >= j andalso j' < j + n then f (j' - j) + j else j')
  | _ => t

val quantifier_cluster_max_size = 8

(* theory -> term -> term *)
fun push_quantifiers_inward thy =
  let
    (* string -> string list -> typ list -> term -> term *)
    fun aux quant_s ss Ts t =
      (case t of
         (t0 as Const (s0, _)) $ Abs (s1, T1, t1 as _ $ _) =>
         if s0 = quant_s andalso length Ts < quantifier_cluster_max_size then
           aux s0 (s1 :: ss) (T1 :: Ts) t1
         else if quant_s = "" andalso
                 (s0 = @{const_name All} orelse s0 = @{const_name Ex}) then
           aux s0 [s1] [T1] t1
         else
           raise SAME ()
       | _ => raise SAME ())
      handle SAME () =>
             case t of
               t1 $ t2 =>
               if quant_s = "" then
                 aux "" [] [] t1 $ aux "" [] [] t2
               else
                 let
                   val typical_card = 4
                   (* ('a -> ''b list) -> 'a list -> ''b list *)
                   fun big_union proj ps =
                     fold (fold (insert (op =)) o proj) ps []
                   val (ts, connective) = strip_any_connective t
                   val T_costs =
                     map (bounded_card_of_type 65536 typical_card []) Ts
                   val t_costs = map size_of_term ts
                   val num_Ts = length Ts
                   (* int -> int *)
                   val flip = curry (op -) (num_Ts - 1)
                   val t_boundss = map (map flip o loose_bnos) ts
                   (* (int list * int) list -> int list -> int *)
                   fun cost boundss_cum_costs [] =
                       map snd boundss_cum_costs |> Integer.sum
                     | cost boundss_cum_costs (j :: js) =
                       let
                         val (yeas, nays) =
                           List.partition (fn (bounds, _) =>
                                              member (op =) bounds j)
                                          boundss_cum_costs
                         val yeas_bounds = big_union fst yeas
                         val yeas_cost = Integer.sum (map snd yeas)
                                         * nth T_costs j
                       in cost ((yeas_bounds, yeas_cost) :: nays) js end
                   val js = all_permutations (index_seq 0 num_Ts)
                            |> map (`(cost (t_boundss ~~ t_costs)))
                            |> sort (int_ord o pairself fst) |> hd |> snd
                   val back_js = map (fn j => find_index (curry (op =) j) js)
                                     (index_seq 0 num_Ts)
                   val ts = map (renumber_bounds 0 num_Ts (nth back_js o flip))
                                ts
                   (* (term * int list) list -> term *)
                   fun mk_connection [] =
                       raise ARG ("Nitpick_HOL.push_quantifiers_inward.aux.\
                                  \mk_connection", "")
                     | mk_connection ts_cum_bounds =
                       ts_cum_bounds |> map fst
                       |> foldr1 (fn (t1, t2) => connective $ t1 $ t2)
                   (* (term * int list) list -> int list -> term *)
                   fun build ts_cum_bounds [] = ts_cum_bounds |> mk_connection
                     | build ts_cum_bounds (j :: js) =
                       let
                         val (yeas, nays) =
                           List.partition (fn (_, bounds) =>
                                              member (op =) bounds j)
                                          ts_cum_bounds
                           ||> map (apfst (incr_boundvars ~1))
                       in
                         if null yeas then
                           build nays js
                         else
                           let val T = nth Ts (flip j) in
                             build ((Const (quant_s, (T --> bool_T) --> bool_T)
                                     $ Abs (nth ss (flip j), T,
                                            mk_connection yeas),
                                      big_union snd yeas) :: nays) js
                           end
                       end
                 in build (ts ~~ t_boundss) js end
             | Abs (s, T, t') => Abs (s, T, aux "" [] [] t')
             | _ => t
  in aux "" [] [] end

(* polarity -> string -> bool *)
fun is_positive_existential polar quant_s =
  (polar = Pos andalso quant_s = @{const_name Ex}) orelse
  (polar = Neg andalso quant_s <> @{const_name Ex})

(* extended_context -> int -> term -> term *)
fun skolemize_term_and_more (ext_ctxt as {thy, def_table, skolems, ...})
                            skolem_depth =
  let
    (* int list -> int list *)
    val incrs = map (Integer.add 1)
    (* string list -> typ list -> int list -> int -> polarity -> term -> term *)
    fun aux ss Ts js depth polar t =
      let
        (* string -> typ -> string -> typ -> term -> term *)
        fun do_quantifier quant_s quant_T abs_s abs_T t =
          if not (loose_bvar1 (t, 0)) then
            aux ss Ts js depth polar (incr_boundvars ~1 t)
          else if depth <= skolem_depth andalso
                  is_positive_existential polar quant_s then
            let
              val j = length (!skolems) + 1
              val sko_s = skolem_prefix_for (length js) j ^ abs_s
              val _ = Unsynchronized.change skolems (cons (sko_s, ss))
              val sko_t = list_comb (Const (sko_s, rev Ts ---> abs_T),
                                     map Bound (rev js))
              val abs_t = Abs (abs_s, abs_T, aux ss Ts (incrs js) depth polar t)
            in
              if null js then betapply (abs_t, sko_t)
              else Const (@{const_name Let}, abs_T --> quant_T) $ sko_t $ abs_t
            end
          else
            Const (quant_s, quant_T)
            $ Abs (abs_s, abs_T,
                   if is_higher_order_type abs_T then
                     t
                   else
                     aux (abs_s :: ss) (abs_T :: Ts) (0 :: incrs js)
                         (depth + 1) polar t)
      in
        case t of
          Const (s0 as @{const_name all}, T0) $ Abs (s1, T1, t1) =>
          do_quantifier s0 T0 s1 T1 t1
        | @{const "==>"} $ t1 $ t2 =>
          @{const "==>"} $ aux ss Ts js depth (flip_polarity polar) t1
          $ aux ss Ts js depth polar t2
        | @{const Pure.conjunction} $ t1 $ t2 =>
          @{const Pure.conjunction} $ aux ss Ts js depth polar t1
          $ aux ss Ts js depth polar t2
        | @{const Trueprop} $ t1 =>
          @{const Trueprop} $ aux ss Ts js depth polar t1
        | @{const Not} $ t1 =>
          @{const Not} $ aux ss Ts js depth (flip_polarity polar) t1
        | Const (s0 as @{const_name All}, T0) $ Abs (s1, T1, t1) =>
          do_quantifier s0 T0 s1 T1 t1
        | Const (s0 as @{const_name Ex}, T0) $ Abs (s1, T1, t1) =>
          do_quantifier s0 T0 s1 T1 t1
        | @{const "op &"} $ t1 $ t2 =>
          @{const "op &"} $ aux ss Ts js depth polar t1
          $ aux ss Ts js depth polar t2
        | @{const "op |"} $ t1 $ t2 =>
          @{const "op |"} $ aux ss Ts js depth polar t1
          $ aux ss Ts js depth polar t2
        | @{const "op -->"} $ t1 $ t2 =>
          @{const "op -->"} $ aux ss Ts js depth (flip_polarity polar) t1
          $ aux ss Ts js depth polar t2
        | (t0 as Const (@{const_name Let}, T0)) $ t1 $ t2 =>
          t0 $ t1 $ aux ss Ts js depth polar t2
        | Const (x as (s, T)) =>
          if is_inductive_pred ext_ctxt x andalso
             not (is_well_founded_inductive_pred ext_ctxt x) then
            let
              val gfp = (fixpoint_kind_of_const thy def_table x = Gfp)
              val (pref, connective, set_oper) =
                if gfp then
                  (lbfp_prefix,
                   @{const "op |"},
                   @{const_name upper_semilattice_fun_inst.sup_fun})
                else
                  (ubfp_prefix,
                   @{const "op &"},
                   @{const_name lower_semilattice_fun_inst.inf_fun})
              (* unit -> term *)
              fun pos () = unrolled_inductive_pred_const ext_ctxt gfp x
                           |> aux ss Ts js depth polar
              fun neg () = Const (pref ^ s, T)
            in
              (case polar |> gfp ? flip_polarity of
                 Pos => pos ()
               | Neg => neg ()
               | Neut =>
                 if is_fun_type T then
                   let
                     val ((trunk_arg_Ts, rump_arg_T), body_T) =
                       T |> strip_type |>> split_last
                     val set_T = rump_arg_T --> body_T
                     (* (unit -> term) -> term *)
                     fun app f =
                       list_comb (f (),
                                  map Bound (length trunk_arg_Ts - 1 downto 0))
                   in
                     List.foldr absdummy
                                (Const (set_oper, set_T --> set_T --> set_T)
                                        $ app pos $ app neg) trunk_arg_Ts
                   end
                 else
                   connective $ pos () $ neg ())
            end
          else
            Const x
        | t1 $ t2 =>
          betapply (aux ss Ts [] (skolem_depth + 1) polar t1,
                    aux ss Ts [] depth Neut t2)
        | Abs (s, T, t1) => Abs (s, T, aux ss Ts (incrs js) depth polar t1)
        | _ => t
      end
  in aux [] [] [] 0 Pos end

(* extended_context -> styp -> (int * term option) list *)
fun static_args_in_term ({ersatz_table, ...} : extended_context) x t =
  let
    (* term -> term list -> term list -> term list list *)
    fun fun_calls (Abs (_, _, t)) _ = fun_calls t []
      | fun_calls (t1 $ t2) args = fun_calls t2 [] #> fun_calls t1 (t2 :: args)
      | fun_calls t args =
        (case t of
           Const (x' as (s', T')) =>
           x = x' orelse (case AList.lookup (op =) ersatz_table s' of
                            SOME s'' => x = (s'', T')
                          | NONE => false)
         | _ => false) ? cons args
    (* term list list -> term list list -> term list -> term list list *)
    fun call_sets [] [] vs = [vs]
      | call_sets [] uss vs = vs :: call_sets uss [] []
      | call_sets ([] :: _) _ _ = []
      | call_sets ((t :: ts) :: tss) uss vs =
        OrdList.insert TermOrd.term_ord t vs |> call_sets tss (ts :: uss)
    val sets = call_sets (fun_calls t [] []) [] []
    val indexed_sets = sets ~~ (index_seq 0 (length sets))
  in
    fold_rev (fn (set, j) =>
                 case set of
                   [Var _] => AList.lookup (op =) indexed_sets set = SOME j
                              ? cons (j, NONE)
                 | [t as Const _] => cons (j, SOME t)
                 | [t as Free _] => cons (j, SOME t)
                 | _ => I) indexed_sets []
  end
(* extended_context -> styp -> term list -> (int * term option) list *)
fun static_args_in_terms ext_ctxt x =
  map (static_args_in_term ext_ctxt x)
  #> fold1 (OrdList.inter (prod_ord int_ord (option_ord TermOrd.term_ord)))

(* term -> term list *)
fun params_in_equation (@{const "==>"} $ _ $ t2) = params_in_equation t2
  | params_in_equation (@{const Trueprop} $ t1) = params_in_equation t1
  | params_in_equation (Const (@{const_name "op ="}, _) $ t1 $ _) =
    snd (strip_comb t1)
  | params_in_equation _ = []

(* styp -> styp -> int list -> term list -> term list -> term -> term *)
fun specialize_fun_axiom x x' fixed_js fixed_args extra_args t =
  let
    val k = fold Integer.max (map maxidx_of_term (fixed_args @ extra_args)) 0
            + 1
    val t = map_aterms (fn Var ((s, i), T) => Var ((s, k + i), T) | t' => t') t
    val fixed_params = filter_indices fixed_js (params_in_equation t)
    (* term list -> term -> term *)
    fun aux args (Abs (s, T, t)) = list_comb (Abs (s, T, aux [] t), args)
      | aux args (t1 $ t2) = aux (aux [] t2 :: args) t1
      | aux args t =
        if t = Const x then
          list_comb (Const x', extra_args @ filter_out_indices fixed_js args)
        else
          let val j = find_index (curry (op =) t) fixed_params in
            list_comb (if j >= 0 then nth fixed_args j else t, args)
          end
  in aux [] t end

(* typ list -> term -> bool *)
fun is_eligible_arg Ts t =
  let val bad_Ts = map snd (Term.add_vars t []) @ map (nth Ts) (loose_bnos t) in
    null bad_Ts orelse
    (is_higher_order_type (fastype_of1 (Ts, t)) andalso
     forall (not o is_higher_order_type) bad_Ts)
  end

(* (int * term option) list -> (int * term) list -> int list *)
fun overlapping_indices [] _ = []
  | overlapping_indices _ [] = []
  | overlapping_indices (ps1 as (j1, t1) :: ps1') (ps2 as (j2, t2) :: ps2') =
    if j1 < j2 then overlapping_indices ps1' ps2
    else if j1 > j2 then overlapping_indices ps1 ps2'
    else overlapping_indices ps1' ps2' |> the_default t2 t1 = t2 ? cons j1

val special_depth = 20

(* extended_context -> int -> term -> term *)
fun specialize_consts_in_term (ext_ctxt as {thy, specialize, simp_table,
                                            special_funs, ...}) depth t =
  if not specialize orelse depth > special_depth then
    t
  else
    let
      val blacklist = if depth = 0 then []
                      else case term_under_def t of Const x => [x] | _ => []
      (* term list -> typ list -> term -> term *)
      fun aux args Ts (Const (x as (s, T))) =
          ((if not (member (op =) blacklist x) andalso not (null args) andalso
               not (String.isPrefix special_prefix s) andalso
               is_equational_fun ext_ctxt x then
              let
                val eligible_args = filter (is_eligible_arg Ts o snd)
                                           (index_seq 0 (length args) ~~ args)
                val _ = not (null eligible_args) orelse raise SAME ()
                val old_axs = equational_fun_axioms ext_ctxt x
                              |> map (destroy_existential_equalities thy)
                val static_params = static_args_in_terms ext_ctxt x old_axs
                val fixed_js = overlapping_indices static_params eligible_args
                val _ = not (null fixed_js) orelse raise SAME ()
                val fixed_args = filter_indices fixed_js args
                val vars = fold Term.add_vars fixed_args []
                           |> sort (TermOrd.fast_indexname_ord o pairself fst)
                val bound_js = fold (fn t => fn js => add_loose_bnos (t, 0, js))
                                    fixed_args []
                               |> sort int_ord
                val live_args = filter_out_indices fixed_js args
                val extra_args = map Var vars @ map Bound bound_js @ live_args
                val extra_Ts = map snd vars @ filter_indices bound_js Ts
                val k = maxidx_of_term t + 1
                (* int -> term *)
                fun var_for_bound_no j =
                  Var ((bound_var_prefix ^
                        nat_subscript (find_index (curry (op =) j) bound_js
                                       + 1), k),
                       nth Ts j)
                val fixed_args_in_axiom =
                  map (curry subst_bounds
                             (map var_for_bound_no (index_seq 0 (length Ts))))
                      fixed_args
              in
                case AList.lookup (op =) (!special_funs)
                                  (x, fixed_js, fixed_args_in_axiom) of
                  SOME x' => list_comb (Const x', extra_args)
                | NONE =>
                  let
                    val extra_args_in_axiom =
                      map Var vars @ map var_for_bound_no bound_js
                    val x' as (s', _) =
                      (special_prefix_for (length (!special_funs) + 1) ^ s,
                       extra_Ts @ filter_out_indices fixed_js (binder_types T)
                       ---> body_type T)
                    val new_axs =
                      map (specialize_fun_axiom x x' fixed_js
                               fixed_args_in_axiom extra_args_in_axiom) old_axs
                    val _ =
                      Unsynchronized.change special_funs
                          (cons ((x, fixed_js, fixed_args_in_axiom), x'))
                    val _ = add_simps simp_table s' new_axs
                  in list_comb (Const x', extra_args) end
              end
            else
              raise SAME ())
           handle SAME () => list_comb (Const x, args))
        | aux args Ts (Abs (s, T, t)) =
          list_comb (Abs (s, T, aux [] (T :: Ts) t), args)
        | aux args Ts (t1 $ t2) = aux (aux [] Ts t2 :: args) Ts t1
        | aux args _ t = list_comb (t, args)
    in aux [] [] t end

(* theory -> term -> int Termtab.tab -> int Termtab.tab *)
fun add_to_uncurry_table thy t =
  let
    (* term -> term list -> int Termtab.tab -> int Termtab.tab *)
    fun aux (t1 $ t2) args table =
        let val table = aux t2 [] table in aux t1 (t2 :: args) table end
      | aux (Abs (_, _, t')) _ table = aux t' [] table
      | aux (t as Const (x as (s, _))) args table =
        if is_built_in_const true x orelse is_constr_like thy x orelse
           is_sel s orelse s = @{const_name Sigma} then
          table
        else
          Termtab.map_default (t, 65536) (curry Int.min (length args)) table
      | aux _ _ table = table
  in aux t [] end

(* int Termtab.tab term -> term *)
fun uncurry_term table t =
  let
    (* term -> term list -> term *)
    fun aux (t1 $ t2) args = aux t1 (aux t2 [] :: args)
      | aux (Abs (s, T, t')) args = betapplys (Abs (s, T, aux t' []), args)
      | aux (t as Const (s, T)) args =
        (case Termtab.lookup table t of
           SOME n =>
           if n >= 2 then
             let
               val (arg_Ts, rest_T) = strip_n_binders n T
               val j =
                 if hd arg_Ts = @{typ bisim_iterator} orelse
                    is_fp_iterator_type (hd arg_Ts) then
                   1
                 else case find_index (not_equal bool_T) arg_Ts of
                   ~1 => n
                 | j => j
               val ((before_args, tuple_args), after_args) =
                 args |> chop n |>> chop j
               val ((before_arg_Ts, tuple_arg_Ts), rest_T) =
                 T |> strip_n_binders n |>> chop j
               val tuple_T = HOLogic.mk_tupleT tuple_arg_Ts
             in
               if n - j < 2 then
                 betapplys (t, args)
               else
                 betapplys (Const (uncurry_prefix_for (n - j) j ^ s,
                                   before_arg_Ts ---> tuple_T --> rest_T),
                            before_args @ [mk_flat_tuple tuple_T tuple_args] @
                            after_args)
             end
           else
             betapplys (t, args)
         | NONE => betapplys (t, args))
      | aux t args = betapplys (t, args)
  in aux t [] end

(* (term -> term) -> int -> term -> term *)
fun coerce_bound_no f j t =
  case t of
    t1 $ t2 => coerce_bound_no f j t1 $ coerce_bound_no f j t2
  | Abs (s, T, t') => Abs (s, T, coerce_bound_no f (j + 1) t')
  | Bound j' => if j' = j then f t else t
  | _ => t

(* extended_context -> bool -> term -> term *)
fun box_fun_and_pair_in_term (ext_ctxt as {thy, fast_descrs, ...}) def orig_t =
  let
    (* typ -> typ *)
    fun box_relational_operator_type (Type ("fun", Ts)) =
        Type ("fun", map box_relational_operator_type Ts)
      | box_relational_operator_type (Type ("*", Ts)) =
        Type ("*", map (box_type ext_ctxt InPair) Ts)
      | box_relational_operator_type T = T
    (* typ -> typ -> term -> term *)
    fun coerce_bound_0_in_term new_T old_T =
      old_T <> new_T ? coerce_bound_no (coerce_term [new_T] old_T new_T) 0
    (* typ list -> typ -> term -> term *)
    and coerce_term Ts new_T old_T t =
      if old_T = new_T then
        t
      else
        case (new_T, old_T) of
          (Type (new_s, new_Ts as [new_T1, new_T2]),
           Type ("fun", [old_T1, old_T2])) =>
          (case eta_expand Ts t 1 of
             Abs (s, _, t') =>
             Abs (s, new_T1,
                  t' |> coerce_bound_0_in_term new_T1 old_T1
                     |> coerce_term (new_T1 :: Ts) new_T2 old_T2)
             |> Envir.eta_contract
             |> new_s <> "fun"
                ? construct_value thy (@{const_name FunBox},
                                       Type ("fun", new_Ts) --> new_T) o single
           | t' => raise TERM ("Nitpick_HOL.box_fun_and_pair_in_term.\
                               \coerce_term", [t']))
        | (Type (new_s, new_Ts as [new_T1, new_T2]),
           Type (old_s, old_Ts as [old_T1, old_T2])) =>
          if old_s = @{type_name fun_box} orelse
             old_s = @{type_name pair_box} orelse old_s = "*" then
            case constr_expand ext_ctxt old_T t of
              Const (@{const_name FunBox}, _) $ t1 =>
              if new_s = "fun" then
                coerce_term Ts new_T (Type ("fun", old_Ts)) t1
              else
                construct_value thy
                    (@{const_name FunBox}, Type ("fun", new_Ts) --> new_T)
                     [coerce_term Ts (Type ("fun", new_Ts))
                                  (Type ("fun", old_Ts)) t1]
            | Const _ $ t1 $ t2 =>
              construct_value thy
                  (if new_s = "*" then @{const_name Pair}
                   else @{const_name PairBox}, new_Ts ---> new_T)
                  [coerce_term Ts new_T1 old_T1 t1,
                   coerce_term Ts new_T2 old_T2 t2]
            | t' => raise TERM ("Nitpick_HOL.box_fun_and_pair_in_term.\
                                \coerce_term", [t'])
          else
            raise TYPE ("coerce_term", [new_T, old_T], [t])
        | _ => raise TYPE ("coerce_term", [new_T, old_T], [t])
    (* indexname * typ -> typ * term -> typ option list -> typ option list *)
    fun add_boxed_types_for_var (z as (_, T)) (T', t') =
      case t' of
        Var z' => z' = z ? insert (op =) T'
      | Const (@{const_name Pair}, _) $ t1 $ t2 =>
        (case T' of
           Type (_, [T1, T2]) =>
           fold (add_boxed_types_for_var z) [(T1, t1), (T2, t2)]
         | _ => raise TYPE ("Nitpick_HOL.box_fun_and_pair_in_term.\
                            \add_boxed_types_for_var", [T'], []))
      | _ => exists_subterm (curry (op =) (Var z)) t' ? insert (op =) T
    (* typ list -> typ list -> term -> indexname * typ -> typ *)
    fun box_var_in_def new_Ts old_Ts t (z as (_, T)) =
      case t of
        @{const Trueprop} $ t1 => box_var_in_def new_Ts old_Ts t1 z
      | Const (s0, _) $ t1 $ _ =>
        if s0 = @{const_name "=="} orelse s0 = @{const_name "op ="} then
          let
            val (t', args) = strip_comb t1
            val T' = fastype_of1 (new_Ts, do_term new_Ts old_Ts Neut t')
          in
            case fold (add_boxed_types_for_var z)
                      (fst (strip_n_binders (length args) T') ~~ args) [] of
              [T''] => T''
            | _ => T
          end
        else
          T
      | _ => T
    (* typ list -> typ list -> polarity -> string -> typ -> string -> typ
       -> term -> term *)
    and do_quantifier new_Ts old_Ts polar quant_s quant_T abs_s abs_T t =
      let
        val abs_T' =
          if polar = Neut orelse is_positive_existential polar quant_s then
            box_type ext_ctxt InFunLHS abs_T
          else
            abs_T
        val body_T = body_type quant_T
      in
        Const (quant_s, (abs_T' --> body_T) --> body_T)
        $ Abs (abs_s, abs_T',
               t |> do_term (abs_T' :: new_Ts) (abs_T :: old_Ts) polar)
      end
    (* typ list -> typ list -> string -> typ -> term -> term -> term *)
    and do_equals new_Ts old_Ts s0 T0 t1 t2 =
      let
        val (t1, t2) = pairself (do_term new_Ts old_Ts Neut) (t1, t2)
        val (T1, T2) = pairself (curry fastype_of1 new_Ts) (t1, t2)
        val T = [T1, T2] |> sort TermOrd.typ_ord |> List.last
      in
        list_comb (Const (s0, T --> T --> body_type T0),
                   map2 (coerce_term new_Ts T) [T1, T2] [t1, t2])
      end
    (* string -> typ -> term *)
    and do_description_operator s T =
      let val T1 = box_type ext_ctxt InFunLHS (range_type T) in
        Const (s, (T1 --> bool_T) --> T1)
      end
    (* typ list -> typ list -> polarity -> term -> term *)
    and do_term new_Ts old_Ts polar t =
      case t of
        Const (s0 as @{const_name all}, T0) $ Abs (s1, T1, t1) =>
        do_quantifier new_Ts old_Ts polar s0 T0 s1 T1 t1
      | Const (s0 as @{const_name "=="}, T0) $ t1 $ t2 =>
        do_equals new_Ts old_Ts s0 T0 t1 t2
      | @{const "==>"} $ t1 $ t2 =>
        @{const "==>"} $ do_term new_Ts old_Ts (flip_polarity polar) t1
        $ do_term new_Ts old_Ts polar t2
      | @{const Pure.conjunction} $ t1 $ t2 =>
        @{const Pure.conjunction} $ do_term new_Ts old_Ts polar t1
        $ do_term new_Ts old_Ts polar t2
      | @{const Trueprop} $ t1 =>
        @{const Trueprop} $ do_term new_Ts old_Ts polar t1
      | @{const Not} $ t1 =>
        @{const Not} $ do_term new_Ts old_Ts (flip_polarity polar) t1
      | Const (s0 as @{const_name All}, T0) $ Abs (s1, T1, t1) =>
        do_quantifier new_Ts old_Ts polar s0 T0 s1 T1 t1
      | Const (s0 as @{const_name Ex}, T0) $ Abs (s1, T1, t1) =>
        do_quantifier new_Ts old_Ts polar s0 T0 s1 T1 t1
      | Const (s0 as @{const_name "op ="}, T0) $ t1 $ t2 =>
        do_equals new_Ts old_Ts s0 T0 t1 t2
      | @{const "op &"} $ t1 $ t2 =>
        @{const "op &"} $ do_term new_Ts old_Ts polar t1
        $ do_term new_Ts old_Ts polar t2
      | @{const "op |"} $ t1 $ t2 =>
        @{const "op |"} $ do_term new_Ts old_Ts polar t1
        $ do_term new_Ts old_Ts polar t2
      | @{const "op -->"} $ t1 $ t2 =>
        @{const "op -->"} $ do_term new_Ts old_Ts (flip_polarity polar) t1
        $ do_term new_Ts old_Ts polar t2
      | Const (s as @{const_name The}, T) => do_description_operator s T
      | Const (s as @{const_name Eps}, T) => do_description_operator s T
      | Const (@{const_name quot_normal}, Type ("fun", [_, T2])) =>
        let val T' = box_type ext_ctxt InSel T2 in
          Const (@{const_name quot_normal}, T' --> T')
        end
      | Const (s as @{const_name Tha}, T) => do_description_operator s T
      | Const (x as (s, T)) =>
        Const (s, if s = @{const_name converse} orelse
                     s = @{const_name trancl} then
                    box_relational_operator_type T
                  else if is_built_in_const fast_descrs x orelse
                          s = @{const_name Sigma} then
                    T
                  else if is_constr_like thy x then
                    box_type ext_ctxt InConstr T
                  else if is_sel s
                       orelse is_rep_fun thy x then
                    box_type ext_ctxt InSel T
                  else
                    box_type ext_ctxt InExpr T)
      | t1 $ Abs (s, T, t2') =>
        let
          val t1 = do_term new_Ts old_Ts Neut t1
          val T1 = fastype_of1 (new_Ts, t1)
          val (s1, Ts1) = dest_Type T1
          val T' = hd (snd (dest_Type (hd Ts1)))
          val t2 = Abs (s, T', do_term (T' :: new_Ts) (T :: old_Ts) Neut t2')
          val T2 = fastype_of1 (new_Ts, t2)
          val t2 = coerce_term new_Ts (hd Ts1) T2 t2
        in
          betapply (if s1 = "fun" then
                      t1
                    else
                      select_nth_constr_arg thy
                          (@{const_name FunBox}, Type ("fun", Ts1) --> T1) t1 0
                          (Type ("fun", Ts1)), t2)
        end
      | t1 $ t2 =>
        let
          val t1 = do_term new_Ts old_Ts Neut t1
          val T1 = fastype_of1 (new_Ts, t1)
          val (s1, Ts1) = dest_Type T1
          val t2 = do_term new_Ts old_Ts Neut t2
          val T2 = fastype_of1 (new_Ts, t2)
          val t2 = coerce_term new_Ts (hd Ts1) T2 t2
        in
          betapply (if s1 = "fun" then
                      t1
                    else
                      select_nth_constr_arg thy
                          (@{const_name FunBox}, Type ("fun", Ts1) --> T1) t1 0
                          (Type ("fun", Ts1)), t2)
        end
      | Free (s, T) => Free (s, box_type ext_ctxt InExpr T)
      | Var (z as (x, T)) =>
        Var (x, if def then box_var_in_def new_Ts old_Ts orig_t z
                else box_type ext_ctxt InExpr T)
      | Bound _ => t
      | Abs (s, T, t') =>
        Abs (s, T, do_term (T :: new_Ts) (T :: old_Ts) Neut t')
  in do_term [] [] Pos orig_t end

(* int -> term -> term *)
fun eval_axiom_for_term j t =
  Logic.mk_equals (Const (eval_prefix ^ string_of_int j, fastype_of t), t)

(* extended_context -> styp -> bool *)
fun is_equational_fun_surely_complete ext_ctxt x =
  case raw_equational_fun_axioms ext_ctxt x of
    [@{const Trueprop} $ (Const (@{const_name "op ="}, _) $ t1 $ _)] =>
    strip_comb t1 |> snd |> forall is_Var
  | _ => false

type special = int list * term list * styp

(* styp -> special -> special -> term *)
fun special_congruence_axiom (s, T) (js1, ts1, x1) (js2, ts2, x2) =
  let
    val (bounds1, bounds2) = pairself (map Var o special_bounds) (ts1, ts2)
    val Ts = binder_types T
    val max_j = fold (fold Integer.max) [js1, js2] ~1
    val (eqs, (args1, args2)) =
      fold (fn j => case pairself (fn ps => AList.lookup (op =) ps j)
                                  (js1 ~~ ts1, js2 ~~ ts2) of
                      (SOME t1, SOME t2) => apfst (cons (t1, t2))
                    | (SOME t1, NONE) => apsnd (apsnd (cons t1))
                    | (NONE, SOME t2) => apsnd (apfst (cons t2))
                    | (NONE, NONE) =>
                      let val v = Var ((cong_var_prefix ^ nat_subscript j, 0),
                                       nth Ts j) in
                        apsnd (pairself (cons v))
                      end) (max_j downto 0) ([], ([], []))
  in
    Logic.list_implies (eqs |> filter_out (op =) |> distinct (op =)
                            |> map Logic.mk_equals,
                        Logic.mk_equals (list_comb (Const x1, bounds1 @ args1),
                                         list_comb (Const x2, bounds2 @ args2)))
    |> Refute.close_form (* TODO: needed? *)
  end

(* extended_context -> styp list -> term list *)
fun special_congruence_axioms (ext_ctxt as {special_funs, ...}) xs =
  let
    val groups =
      !special_funs
      |> map (fn ((x, js, ts), x') => (x, (js, ts, x')))
      |> AList.group (op =)
      |> filter_out (is_equational_fun_surely_complete ext_ctxt o fst)
      |> map (fn (x, zs) => (x, zs |> member (op =) xs x ? cons ([], [], x)))
    (* special -> int *)
    fun generality (js, _, _) = ~(length js)
    (* special -> special -> bool *)
    fun is_more_specific (j1, t1, x1) (j2, t2, x2) =
      x1 <> x2 andalso OrdList.subset (prod_ord int_ord TermOrd.term_ord)
                                      (j2 ~~ t2, j1 ~~ t1)
    (* styp -> special list -> special list -> special list -> term list
       -> term list *)
    fun do_pass_1 _ [] [_] [_] = I
      | do_pass_1 x skipped _ [] = do_pass_2 x skipped
      | do_pass_1 x skipped all (z :: zs) =
        case filter (is_more_specific z) all
             |> sort (int_ord o pairself generality) of
          [] => do_pass_1 x (z :: skipped) all zs
        | (z' :: _) => cons (special_congruence_axiom x z z')
                       #> do_pass_1 x skipped all zs
    (* styp -> special list -> term list -> term list *)
    and do_pass_2 _ [] = I
      | do_pass_2 x (z :: zs) =
        fold (cons o special_congruence_axiom x z) zs #> do_pass_2 x zs
  in fold (fn (x, zs) => do_pass_1 x [] zs zs) groups [] end

(* term -> bool *)
val is_trivial_equation = the_default false o try (op aconv o Logic.dest_equals)

(* 'a Symtab.table -> 'a list *)
fun all_table_entries table = Symtab.fold (append o snd) table []
(* const_table -> string -> const_table *)
fun extra_table table s = Symtab.make [(s, all_table_entries table)]

(* extended_context -> term -> (term list * term list) * (bool * bool) *)
fun axioms_for_term
        (ext_ctxt as {thy, max_bisim_depth, user_axioms, fast_descrs, evals,
                      def_table, nondef_table, user_nondefs, ...}) t =
  let
    type accumulator = styp list * (term list * term list)
    (* (term list * term list -> term list)
       -> ((term list -> term list) -> term list * term list
           -> term list * term list)
       -> int -> term -> accumulator -> accumulator *)
    fun add_axiom get app depth t (accum as (xs, axs)) =
      let
        val t = t |> unfold_defs_in_term ext_ctxt
                  |> skolemize_term_and_more ext_ctxt ~1
      in
        if is_trivial_equation t then
          accum
        else
          let val t' = t |> specialize_consts_in_term ext_ctxt depth in
            if exists (member (op aconv) (get axs)) [t, t'] then accum
            else add_axioms_for_term (depth + 1) t' (xs, app (cons t') axs)
          end
      end
    (* int -> term -> accumulator -> accumulator *)
    and add_def_axiom depth = add_axiom fst apfst depth
    and add_nondef_axiom depth = add_axiom snd apsnd depth
    and add_maybe_def_axiom depth t =
      (if head_of t <> @{const "==>"} then add_def_axiom
       else add_nondef_axiom) depth t
    and add_eq_axiom depth t =
      (if is_constr_pattern_formula thy t then add_def_axiom
       else add_nondef_axiom) depth t
    (* int -> term -> accumulator -> accumulator *)
    and add_axioms_for_term depth t (accum as (xs, axs)) =
      case t of
        t1 $ t2 => accum |> fold (add_axioms_for_term depth) [t1, t2]
      | Const (x as (s, T)) =>
        (if member (op =) xs x orelse is_built_in_const fast_descrs x then
           accum
         else
           let val accum as (xs, _) = (x :: xs, axs) in
             if depth > axioms_max_depth then
               raise TOO_LARGE ("Nitpick_HOL.axioms_for_term.\
                                \add_axioms_for_term",
                                "too many nested axioms (" ^
                                string_of_int depth ^ ")")
             else if Refute.is_const_of_class thy x then
               let
                 val class = Logic.class_of_const s
                 val of_class = Logic.mk_of_class (TVar (("'a", 0), [class]),
                                                   class)
                 val ax1 = try (Refute.specialize_type thy x) of_class
                 val ax2 = Option.map (Refute.specialize_type thy x o snd)
                                      (Refute.get_classdef thy class)
               in
                 fold (add_maybe_def_axiom depth) (map_filter I [ax1, ax2])
                      accum
               end
             else if is_constr thy x then
               accum
             else if is_equational_fun ext_ctxt x then
               fold (add_eq_axiom depth) (equational_fun_axioms ext_ctxt x)
                    accum
             else if is_abs_fun thy x then
               if is_quot_type thy (range_type T) then
                 raise NOT_SUPPORTED "\"Abs_\" function of quotient type"
               else
                 accum |> fold (add_nondef_axiom depth)
                               (nondef_props_for_const thy false nondef_table x)
                       |> is_funky_typedef thy (range_type T)
                          ? fold (add_maybe_def_axiom depth)
                                 (nondef_props_for_const thy true
                                                    (extra_table def_table s) x)
             else if is_rep_fun thy x then
               if is_quot_type thy (domain_type T) then
                 raise NOT_SUPPORTED "\"Rep_\" function of quotient type"
               else
                 accum |> fold (add_nondef_axiom depth)
                               (nondef_props_for_const thy false nondef_table x)
                       |> is_funky_typedef thy (range_type T)
                          ? fold (add_maybe_def_axiom depth)
                                 (nondef_props_for_const thy true
                                                    (extra_table def_table s) x)
                       |> add_axioms_for_term depth
                                              (Const (mate_of_rep_fun thy x))
                       |> fold (add_def_axiom depth)
                               (inverse_axioms_for_rep_fun thy x)
             else
               accum |> user_axioms <> SOME false
                        ? fold (add_nondef_axiom depth)
                               (nondef_props_for_const thy false nondef_table x)
           end)
        |> add_axioms_for_type depth T
      | Free (_, T) => add_axioms_for_type depth T accum
      | Var (_, T) => add_axioms_for_type depth T accum
      | Bound _ => accum
      | Abs (_, T, t) => accum |> add_axioms_for_term depth t
                               |> add_axioms_for_type depth T
    (* int -> typ -> accumulator -> accumulator *)
    and add_axioms_for_type depth T =
      case T of
        Type ("fun", Ts) => fold (add_axioms_for_type depth) Ts
      | Type ("*", Ts) => fold (add_axioms_for_type depth) Ts
      | @{typ prop} => I
      | @{typ bool} => I
      | @{typ unit} => I
      | TFree (_, S) => add_axioms_for_sort depth T S
      | TVar (_, S) => add_axioms_for_sort depth T S
      | Type (z as (s, Ts)) =>
        fold (add_axioms_for_type depth) Ts
        #> (if is_pure_typedef thy T then
              fold (add_maybe_def_axiom depth) (optimized_typedef_axioms thy z)
            else if is_quot_type thy T then
              fold (add_def_axiom depth) (optimized_quot_type_axioms thy z)
            else if max_bisim_depth >= 0 andalso is_codatatype thy T then
              fold (add_maybe_def_axiom depth)
                   (codatatype_bisim_axioms ext_ctxt T)
            else
              I)
    (* int -> typ -> sort -> accumulator -> accumulator *)
    and add_axioms_for_sort depth T S =
      let
        val supers = Sign.complete_sort thy S
        val class_axioms =
          maps (fn class => map prop_of (AxClass.get_info thy class |> #axioms
                                         handle ERROR _ => [])) supers
        val monomorphic_class_axioms =
          map (fn t => case Term.add_tvars t [] of
                         [] => t
                       | [(x, S)] =>
                         Refute.monomorphic_term (Vartab.make [(x, (S, T))]) t
                       | _ => raise TERM ("Nitpick_HOL.axioms_for_term.\
                                          \add_axioms_for_sort", [t]))
              class_axioms
      in fold (add_nondef_axiom depth) monomorphic_class_axioms end
    val (mono_user_nondefs, poly_user_nondefs) =
      List.partition (null o Term.hidden_polymorphism) user_nondefs
    val eval_axioms = map2 eval_axiom_for_term (index_seq 0 (length evals))
                           evals
    val (xs, (defs, nondefs)) =
      ([], ([], [])) |> add_axioms_for_term 1 t 
                     |> fold_rev (add_def_axiom 1) eval_axioms
                     |> user_axioms = SOME true
                        ? fold (add_nondef_axiom 1) mono_user_nondefs
    val defs = defs @ special_congruence_axioms ext_ctxt xs
  in
    ((defs, nondefs), (user_axioms = SOME true orelse null mono_user_nondefs,
                       null poly_user_nondefs))
  end

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
    val T = unbit_and_unbox_type T
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

(* extended_context -> string * string -> (term option * int list) list
   -> styp -> term * typ *)
fun user_friendly_const ({thy, evals, def_table, skolems, special_funs, ...}
                         : extended_context) (base_name, step_name) formats =
  let
    val default_format = the (AList.lookup (op =) formats NONE)
    (* styp -> term * typ *)
    fun do_const (x as (s, T)) =
      (if String.isPrefix special_prefix s then
         let
           (* term -> term *)
           val do_term = map_aterms (fn Const x => fst (do_const x) | t' => t')
           val (x' as (_, T'), js, ts) =
             AList.find (op =) (!special_funs) (s, unbit_and_unbox_type T)
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
           val ts' = map2 (fn T => fn j =>
                              case AList.lookup (op =) (js ~~ ts) j of
                                SOME t => do_term t
                              | NONE =>
                                Var (nth missing_vars
                                         (find_index (curry (op =) j)
                                                     missing_js)))
                          Ts (0 upto max_j)
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
      |>> map_types unbit_and_unbox_type
      |>> shorten_names_in_term |>> shorten_abs_vars
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

val binary_int_threshold = 4

(* term -> bool *)
fun may_use_binary_ints (t1 $ t2) =
    may_use_binary_ints t1 andalso may_use_binary_ints t2
  | may_use_binary_ints (t as Const (s, _)) =
    t <> @{const Suc} andalso
    not (member (op =) [@{const_name Abs_Frac}, @{const_name Rep_Frac},
                        @{const_name nat_gcd}, @{const_name nat_lcm},
                        @{const_name Frac}, @{const_name norm_frac}] s)
  | may_use_binary_ints (Abs (_, _, t')) = may_use_binary_ints t'
  | may_use_binary_ints _ = true
fun should_use_binary_ints (t1 $ t2) =
    should_use_binary_ints t1 orelse should_use_binary_ints t2
  | should_use_binary_ints (Const (s, _)) =
    member (op =) [@{const_name times_nat_inst.times_nat},
                   @{const_name div_nat_inst.div_nat},
                   @{const_name times_int_inst.times_int},
                   @{const_name div_int_inst.div_int}] s orelse
    (String.isPrefix numeral_prefix s andalso
     let val n = the (Int.fromString (unprefix numeral_prefix s)) in
       n <= ~ binary_int_threshold orelse n >= binary_int_threshold
     end)
  | should_use_binary_ints (Abs (_, _, t')) = should_use_binary_ints t'
  | should_use_binary_ints _ = false

(* typ -> typ *)
fun binarize_nat_and_int_in_type @{typ nat} = @{typ "unsigned_bit word"}
  | binarize_nat_and_int_in_type @{typ int} = @{typ "signed_bit word"}
  | binarize_nat_and_int_in_type (Type (s, Ts)) =
    Type (s, map binarize_nat_and_int_in_type Ts)
  | binarize_nat_and_int_in_type T = T
(* term -> term *)
val binarize_nat_and_int_in_term = map_types binarize_nat_and_int_in_type

(* extended_context -> term
   -> ((term list * term list) * (bool * bool)) * term *)
fun preprocess_term (ext_ctxt as {thy, binary_ints, destroy_constrs, boxes,
                                  skolemize, uncurry, ...}) t =
  let
    val skolem_depth = if skolemize then 4 else ~1
    val (((def_ts, nondef_ts), (got_all_mono_user_axioms, no_poly_user_axioms)),
         core_t) = t |> unfold_defs_in_term ext_ctxt
                     |> Refute.close_form
                     |> skolemize_term_and_more ext_ctxt skolem_depth
                     |> specialize_consts_in_term ext_ctxt 0
                     |> `(axioms_for_term ext_ctxt)
    val binarize =
      case binary_ints of
        SOME false => false
      | _ =>
        forall may_use_binary_ints (core_t :: def_ts @ nondef_ts) andalso
        (binary_ints = SOME true orelse
         exists should_use_binary_ints (core_t :: def_ts @ nondef_ts))
    val box = exists (not_equal (SOME false) o snd) boxes
    val table =
      Termtab.empty |> uncurry
        ? fold (add_to_uncurry_table thy) (core_t :: def_ts @ nondef_ts)
    (* bool -> bool -> term -> term *)
    fun do_rest def core =
      binarize ? binarize_nat_and_int_in_term
      #> uncurry ? uncurry_term table
      #> box ? box_fun_and_pair_in_term ext_ctxt def
      #> destroy_constrs ? (pull_out_universal_constrs thy def
                            #> pull_out_existential_constrs thy
                            #> destroy_pulled_out_constrs ext_ctxt def)
      #> curry_assms
      #> destroy_universal_equalities
      #> destroy_existential_equalities thy
      #> simplify_constrs_and_sels thy
      #> distribute_quantifiers
      #> push_quantifiers_inward thy
      #> Envir.eta_contract 
      #> not core ? Refute.close_form
      #> shorten_abs_vars
  in
    (((map (do_rest true false) def_ts, map (do_rest false false) nondef_ts),
      (got_all_mono_user_axioms, no_poly_user_axioms)),
     do_rest false true core_t)
  end

end;
