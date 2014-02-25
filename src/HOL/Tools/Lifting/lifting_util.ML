(*  Title:      HOL/Tools/Lifting/lifting_util.ML
    Author:     Ondrej Kuncar

General-purpose functions used by the Lifting package.
*)

signature LIFTING_UTIL =
sig
  val MRSL: thm list * thm -> thm
  val option_fold: 'b -> ('a -> 'b) -> 'a option -> 'b
  val map_snd: ('b -> 'c) -> ('a * 'b) list -> ('a * 'c) list
  val dest_Quotient: term -> term * term * term * term

  val quot_thm_rel: thm -> term
  val quot_thm_abs: thm -> term
  val quot_thm_rep: thm -> term
  val quot_thm_crel: thm -> term
  val quot_thm_rty_qty: thm -> typ * typ

  val undisch: thm -> thm
  val undisch_all: thm -> thm
  val is_fun_type: typ -> bool
  val get_args: int -> term -> term list
  val strip_args: int -> term -> term
  val all_args_conv: conv -> conv
  val is_Type: typ -> bool
  val same_type_constrs: typ * typ -> bool
  val Targs: typ -> typ list
  val Tname: typ -> string
  val is_fun_rel: term -> bool
  val relation_types: typ -> typ * typ
  val mk_HOL_eq: thm -> thm
  val safe_HOL_meta_eq: thm -> thm
  val map_interrupt: ('a -> 'b option) -> 'a list -> 'b list option
end


structure Lifting_Util: LIFTING_UTIL =
struct

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

fun option_fold a _ NONE = a
  | option_fold _ f (SOME x) = f x

fun map_snd f xs = map (fn (a, b) => (a, f b)) xs

fun dest_Quotient (Const (@{const_name Quotient}, _) $ rel $ abs $ rep $ cr)
      = (rel, abs, rep, cr)
  | dest_Quotient t = raise TERM ("dest_Quotient", [t])

(*
  quot_thm_rel, quot_thm_abs, quot_thm_rep and quot_thm_rty_qty - simple functions
    for destructing quotient theorems (Quotient R Abs Rep T).
*)

fun quot_thm_rel quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (rel, _, _, _) => rel

fun quot_thm_abs quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, abs, _, _) => abs

fun quot_thm_rep quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, _, rep, _) => rep

fun quot_thm_crel quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o prop_of) quot_thm of
    (_, _, _, crel) => crel

fun quot_thm_rty_qty quot_thm =
  let
    val abs = quot_thm_abs quot_thm
    val abs_type = fastype_of abs  
  in
    (domain_type abs_type, range_type abs_type)
  end

fun undisch thm =
  let
    val assm = Thm.cprem_of thm 1
  in
    Thm.implies_elim thm (Thm.assume assm)
  end

fun undisch_all thm = funpow (nprems_of thm) undisch thm

fun is_fun_type (Type (@{type_name fun}, _)) = true
  | is_fun_type _ = false

fun get_args n = rev o fst o funpow_yield n (swap o dest_comb)

fun strip_args n = funpow n (fst o dest_comb)

fun all_args_conv conv ctm = Conv.try_conv (Conv.combination_conv (all_args_conv conv) conv) ctm

fun is_Type (Type _) = true
  | is_Type _ = false

fun same_type_constrs (Type (r, _), Type (q, _)) = (r = q)
  | same_type_constrs _ = false

fun Targs (Type (_, args)) = args
  | Targs _ = []

fun Tname (Type (name, _)) = name
  | Tname _ = ""

fun is_fun_rel (Const (@{const_name "fun_rel"}, _) $ _ $ _) = true
  | is_fun_rel _ = false

fun relation_types typ = 
  case strip_type typ of
    ([typ1, typ2], @{typ bool}) => (typ1, typ2)
    | _ => error "relation_types: not a relation"

fun mk_HOL_eq r = r RS @{thm meta_eq_to_obj_eq}

fun safe_HOL_meta_eq r = mk_HOL_eq r handle Thm.THM _ => r

fun map_interrupt f l =
  let
    fun map_interrupt' _ [] l = SOME (rev l)
     | map_interrupt' f (x::xs) l = (case f x of
      NONE => NONE
      | SOME v => map_interrupt' f xs (v::l))
  in
    map_interrupt' f l []
  end

end
