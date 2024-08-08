(*  Title:      HOL/Tools/Lifting/lifting_util.ML
    Author:     Ondrej Kuncar

General-purpose functions used by the Lifting package.
*)

signature LIFTING_UTIL =
sig
  val MRSL: thm list * thm -> thm
  val mk_Quotient: term * term * term * term -> term
  val dest_Quotient: term -> term * term * term * term

  val quot_thm_rel: thm -> term
  val quot_thm_abs: thm -> term
  val quot_thm_rep: thm -> term
  val quot_thm_crel: thm -> term
  val quot_thm_rty_qty: thm -> typ * typ
  val Quotient_conv: conv -> conv -> conv -> conv -> conv
  val Quotient_R_conv: conv -> conv

  val undisch: thm -> thm
  val undisch_all: thm -> thm
  val is_fun_type: typ -> bool
  val get_args: int -> term -> term list
  val strip_args: int -> term -> term
  val all_args_conv: conv -> conv
  val Targs: typ -> typ list
  val Tname: typ -> string
  val is_rel_fun: term -> bool
  val relation_types: typ -> typ * typ
  val map_interrupt: ('a -> 'b option) -> 'a list -> 'b list option
  val conceal_naming_result: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory
end


structure Lifting_Util: LIFTING_UTIL =
struct

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

fun mk_Quotient (rel, abs, rep, cr) =
  let val \<^Type>\<open>fun A B\<close> = fastype_of abs
  in \<^Const>\<open>Quotient A B for rel abs rep cr\<close> end

fun dest_Quotient \<^Const_>\<open>Quotient _ _ for rel abs rep cr\<close> = (rel, abs, rep, cr)
  | dest_Quotient t = raise TERM ("dest_Quotient", [t])

(*
  quot_thm_rel, quot_thm_abs, quot_thm_rep and quot_thm_rty_qty - simple functions
    for destructing quotient theorems (Quotient R Abs Rep T).
*)

fun quot_thm_rel quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o Thm.prop_of) quot_thm of
    (rel, _, _, _) => rel

fun quot_thm_abs quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o Thm.prop_of) quot_thm of
    (_, abs, _, _) => abs

fun quot_thm_rep quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o Thm.prop_of) quot_thm of
    (_, _, rep, _) => rep

fun quot_thm_crel quot_thm =
  case (dest_Quotient o HOLogic.dest_Trueprop o Thm.prop_of) quot_thm of
    (_, _, _, crel) => crel

fun quot_thm_rty_qty quot_thm =
  let
    val abs = quot_thm_abs quot_thm
    val abs_type = fastype_of abs  
  in
    (domain_type abs_type, range_type abs_type)
  end

fun Quotient_conv R_conv Abs_conv Rep_conv T_conv = Conv.combination_conv (Conv.combination_conv 
  (Conv.combination_conv (Conv.arg_conv R_conv) Abs_conv) Rep_conv) T_conv;
  
fun Quotient_R_conv R_conv = Quotient_conv R_conv Conv.all_conv Conv.all_conv Conv.all_conv;

fun undisch thm =
  let
    val assm = Thm.cprem_of thm 1
  in
    Thm.implies_elim thm (Thm.assume assm)
  end

fun undisch_all thm = funpow (Thm.nprems_of thm) undisch thm

fun is_fun_type (Type (\<^type_name>\<open>fun\<close>, _)) = true
  | is_fun_type _ = false

fun get_args n = rev o fst o funpow_yield n (swap o dest_comb)

fun strip_args n = funpow n (fst o dest_comb)

fun all_args_conv conv ctm = Conv.try_conv (Conv.combination_conv (all_args_conv conv) conv) ctm

fun Targs (Type (_, args)) = args
  | Targs _ = []

fun Tname (Type (name, _)) = name
  | Tname _ = ""

fun is_rel_fun (Const (\<^const_name>\<open>rel_fun\<close>, _) $ _ $ _) = true
  | is_rel_fun _ = false

fun relation_types typ = 
  case strip_type typ of
    ([typ1, typ2], \<^typ>\<open>bool\<close>) => (typ1, typ2)
    | _ => error "relation_types: not a relation"

fun map_interrupt f l =
  let
    fun map_interrupt' _ [] l = SOME (rev l)
     | map_interrupt' f (x::xs) l = (case f x of
      NONE => NONE
      | SOME v => map_interrupt' f xs (v::l))
  in
    map_interrupt' f l []
  end

fun conceal_naming_result f lthy = 
  lthy |> Proof_Context.concealed |> f ||> Proof_Context.restore_naming lthy;

end
