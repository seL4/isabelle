(*  Title:      HOL/Tools/SMT/smt_utils.ML
    Author:     Sascha Boehme, TU Muenchen

General utility functions.
*)

signature SMT_UTILS =
sig
  (*basic combinators*)
  val repeat: ('a -> 'a option) -> 'a -> 'a
  val repeat_yield: ('a -> 'b -> ('a * 'b) option) -> 'a -> 'b -> 'a * 'b

  (*types*)
  val dest_funT: int -> typ -> typ list * typ

  (*terms*)
  val dest_conj: term -> term * term
  val dest_disj: term -> term * term

  (*patterns and instantiations*)
  val mk_const_pat: theory -> string -> (ctyp -> 'a) -> 'a * cterm
  val destT1: ctyp -> ctyp
  val destT2: ctyp -> ctyp
  val instTs: ctyp list -> ctyp list * cterm -> cterm
  val instT: ctyp -> ctyp * cterm -> cterm
  val instT': cterm -> ctyp * cterm -> cterm

  (*certified terms*)
  val certify: Proof.context -> term -> cterm
  val typ_of: cterm -> typ
  val dest_cabs: cterm -> Proof.context -> cterm * Proof.context
  val dest_all_cabs: cterm -> Proof.context -> cterm * Proof.context
  val dest_cbinder: cterm -> Proof.context -> cterm * Proof.context
  val dest_all_cbinders: cterm -> Proof.context -> cterm * Proof.context
  val mk_cprop: cterm -> cterm
  val dest_cprop: cterm -> cterm
  val mk_cequals: cterm -> cterm -> cterm

  (*conversions*)
  val if_conv: (term -> bool) -> conv -> conv -> conv
  val if_true_conv: (term -> bool) -> conv -> conv
  val binders_conv: (Proof.context -> conv) -> Proof.context -> conv
  val prop_conv: conv -> conv
end

structure SMT_Utils: SMT_UTILS =
struct

(* basic combinators *)

fun repeat f =
  let fun rep x = (case f x of SOME y => rep y | NONE => x)
  in rep end

fun repeat_yield f =
  let fun rep x y = (case f x y of SOME (x', y') => rep x' y' | NONE => (x, y))
  in rep end


(* types *)

val dest_funT =
  let
    fun dest Ts 0 T = (rev Ts, T)
      | dest Ts i (Type ("fun", [T, U])) = dest (T::Ts) (i-1) U
      | dest _ _ T = raise TYPE ("not a function type", [T], [])
  in dest [] end


(* terms *)

fun dest_conj (@{const HOL.conj} $ t $ u) = (t, u)
  | dest_conj t = raise TERM ("not a conjunction", [t])

fun dest_disj (@{const HOL.disj} $ t $ u) = (t, u)
  | dest_disj t = raise TERM ("not a disjunction", [t])


(* patterns and instantiations *)

fun mk_const_pat thy name destT =
  let val cpat = Thm.cterm_of thy (Const (name, Sign.the_const_type thy name))
  in (destT (Thm.ctyp_of_term cpat), cpat) end

val destT1 = hd o Thm.dest_ctyp
val destT2 = hd o tl o Thm.dest_ctyp

fun instTs cUs (cTs, ct) = Thm.instantiate_cterm (cTs ~~ cUs, []) ct
fun instT cU (cT, ct) = instTs [cU] ([cT], ct)
fun instT' ct = instT (Thm.ctyp_of_term ct)


(* certified terms *)

fun certify ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)

fun typ_of ct = #T (Thm.rep_cterm ct) 

fun dest_cabs ct ctxt =
  (case Thm.term_of ct of
    Abs _ =>
      let val (n, ctxt') = yield_singleton Variable.variant_fixes Name.uu ctxt
      in (snd (Thm.dest_abs (SOME n) ct), ctxt') end
  | _ => raise CTERM ("no abstraction", [ct]))

val dest_all_cabs = repeat_yield (try o dest_cabs) 

fun dest_cbinder ct ctxt =
  (case Thm.term_of ct of
    Const _ $ Abs _ => dest_cabs (Thm.dest_arg ct) ctxt
  | _ => raise CTERM ("not a binder", [ct]))

val dest_all_cbinders = repeat_yield (try o dest_cbinder)

val mk_cprop = Thm.capply (Thm.cterm_of @{theory} @{const Trueprop})

fun dest_cprop ct =
  (case Thm.term_of ct of
    @{const Trueprop} $ _ => Thm.dest_arg ct
  | _ => raise CTERM ("not a property", [ct]))

val equals = mk_const_pat @{theory} @{const_name "=="} destT1
fun mk_cequals ct cu = Thm.mk_binop (instT' ct equals) ct cu


(* conversions *)

fun if_conv pred cv1 cv2 ct = if pred (Thm.term_of ct) then cv1 ct else cv2 ct

fun if_true_conv pred cv = if_conv pred cv Conv.all_conv

fun binders_conv cv ctxt =
  Conv.binder_conv (binders_conv cv o snd) ctxt else_conv cv ctxt

fun prop_conv cv ct =
  (case Thm.term_of ct of
    @{const Trueprop} $ _ => Conv.arg_conv cv ct
  | _ => raise CTERM ("not a property", [ct]))

end
