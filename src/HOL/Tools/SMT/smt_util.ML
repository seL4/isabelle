(*  Title:      HOL/Tools/SMT/smt_util.ML
    Author:     Sascha Boehme, TU Muenchen

General utility functions.
*)

signature SMT_UTIL =
sig
  (*basic combinators*)
  val repeat: ('a -> 'a option) -> 'a -> 'a
  val repeat_yield: ('a -> 'b -> ('a * 'b) option) -> 'a -> 'b -> 'a * 'b

  datatype order = First_Order | Higher_Order

  (*class dictionaries*)
  type class = string list
  val basicC: class
  val string_of_class: class -> string
  type 'a dict = (class * 'a) Ord_List.T
  val dict_map_default: class * 'a -> ('a -> 'a) -> 'a dict -> 'a dict
  val dict_update: class * 'a -> 'a dict -> 'a dict
  val dict_merge: ('a * 'a -> 'a) -> 'a dict * 'a dict -> 'a dict
  val dict_lookup: 'a dict -> class -> 'a list
  val dict_get: 'a dict -> class -> 'a option

  (*types*)
  val dest_funT: int -> typ -> typ list * typ

  (*terms*)
  val dest_conj: term -> term * term
  val dest_disj: term -> term * term
  val under_quant: (term -> 'a) -> term -> 'a
  val is_number: term -> bool

  (*symbolic lists*)
  val symb_nil_const: typ -> term
  val symb_cons_const: typ -> term
  val mk_symb_list: typ -> term list -> term
  val dest_symb_list: term -> term list

  (*patterns and instantiations*)
  val mk_const_pat: theory -> string -> (ctyp -> 'a) -> 'a * cterm
  val instTs: ctyp list -> ctyp list * cterm -> cterm
  val instT: ctyp -> ctyp * cterm -> cterm
  val instT': cterm -> ctyp * cterm -> cterm

  (*certified terms*)
  val dest_cabs: cterm -> Proof.context -> cterm * Proof.context
  val dest_all_cabs: cterm -> Proof.context -> cterm * Proof.context
  val dest_cbinder: cterm -> Proof.context -> cterm * Proof.context
  val dest_all_cbinders: cterm -> Proof.context -> cterm * Proof.context
  val mk_cprop: cterm -> cterm
  val dest_cprop: cterm -> cterm
  val mk_cequals: cterm -> cterm -> cterm
  val term_of: cterm -> term
  val prop_of: thm -> term

  (*conversions*)
  val if_conv: (term -> bool) -> conv -> conv -> conv
  val if_true_conv: (term -> bool) -> conv -> conv
  val if_exists_conv: (term -> bool) -> conv -> conv
  val binders_conv: (Proof.context -> conv) -> Proof.context -> conv
  val under_quant_conv: (Proof.context * cterm list -> conv) ->
    Proof.context -> conv
  val prop_conv: conv -> conv
end;

structure SMT_Util: SMT_UTIL =
struct

(* basic combinators *)

fun repeat f =
  let fun rep x = (case f x of SOME y => rep y | NONE => x)
  in rep end

fun repeat_yield f =
  let fun rep x y = (case f x y of SOME (x', y') => rep x' y' | NONE => (x, y))
  in rep end


(* order *)

datatype order = First_Order | Higher_Order


(* class dictionaries *)

type class = string list

val basicC = []

fun string_of_class [] = "basic"
  | string_of_class cs = "basic." ^ space_implode "." cs

type 'a dict = (class * 'a) Ord_List.T

fun class_ord ((cs1, _), (cs2, _)) =
  rev_order (list_ord fast_string_ord (cs1, cs2))

fun dict_insert (cs, x) d =
  if AList.defined (op =) d cs then d
  else Ord_List.insert class_ord (cs, x) d

fun dict_map_default (cs, x) f =
  dict_insert (cs, x) #> AList.map_entry (op =) cs f

fun dict_update (e as (_, x)) = dict_map_default e (K x)

fun dict_merge val_merge = sort class_ord o AList.join (op =) (K val_merge)

fun dict_lookup d cs =
  let fun match (cs', x) = if is_prefix (op =) cs' cs then SOME x else NONE
  in map_filter match d end

fun dict_get d cs =
  (case AList.lookup (op =) d cs of
    NONE => (case cs of [] => NONE | _ => dict_get d (take (length cs - 1) cs))
  | SOME x => SOME x)


(* types *)

val dest_funT =
  let
    fun dest Ts 0 T = (rev Ts, T)
      | dest Ts i (Type ("fun", [T, U])) = dest (T::Ts) (i-1) U
      | dest _ _ T = raise TYPE ("not a function type", [T], [])
  in dest [] end


(* terms *)

fun dest_conj \<^Const_>\<open>conj for t u\<close> = (t, u)
  | dest_conj t = raise TERM ("not a conjunction", [t])

fun dest_disj \<^Const_>\<open>disj for t u\<close> = (t, u)
  | dest_disj t = raise TERM ("not a disjunction", [t])

fun under_quant f t =
  (case t of
    \<^Const_>\<open>All _ for \<open>Abs (_, _, u)\<close>\<close> => under_quant f u
  | \<^Const_>\<open>Ex _ for \<open>Abs (_, _, u)\<close>\<close> => under_quant f u
  | _ => f t)

val is_number =
  let
    fun is_num env (Const (\<^const_name>\<open>Let\<close>, _) $ t $ Abs (_, _, u)) = is_num (t :: env) u
      | is_num env (Bound i) = i < length env andalso is_num env (nth env i)
      | is_num _ t = can HOLogic.dest_number t
  in is_num [] end


(* symbolic lists *)

fun symb_listT T = Type (\<^type_name>\<open>symb_list\<close>, [T])

fun symb_nil_const T = Const (\<^const_name>\<open>Symb_Nil\<close>, symb_listT T)

fun symb_cons_const T =
  let val listT = symb_listT T in Const (\<^const_name>\<open>Symb_Cons\<close>, T --> listT --> listT) end

fun mk_symb_list T ts =
  fold_rev (fn t => fn u => symb_cons_const T $ t $ u) ts (symb_nil_const T)

fun dest_symb_list (Const (\<^const_name>\<open>Symb_Nil\<close>, _)) = []
  | dest_symb_list (Const (\<^const_name>\<open>Symb_Cons\<close>, _) $ t $ u) = t :: dest_symb_list u


(* patterns and instantiations *)

fun mk_const_pat thy name destT =
  let val cpat = Thm.global_cterm_of thy (Const (name, Sign.the_const_type thy name))
  in (destT (Thm.ctyp_of_cterm cpat), cpat) end

fun instTs cUs (cTs, ct) =
  Thm.instantiate_cterm (TVars.make (map (dest_TVar o Thm.typ_of) cTs ~~ cUs), Vars.empty) ct
fun instT cU (cT, ct) = instTs [cU] ([cT], ct)
fun instT' ct = instT (Thm.ctyp_of_cterm ct)


(* certified terms *)

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

val mk_cprop = Thm.apply \<^cterm>\<open>Trueprop\<close>

fun dest_cprop ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>Trueprop for _\<close> => Thm.dest_arg ct
  | _ => raise CTERM ("not a property", [ct]))

val equals = mk_const_pat \<^theory> \<^const_name>\<open>Pure.eq\<close> Thm.dest_ctyp0
fun mk_cequals ct cu = Thm.mk_binop (instT' ct equals) ct cu

val dest_prop = fn \<^Const_>\<open>Trueprop for t\<close> => t | t => t
fun term_of ct = dest_prop (Thm.term_of ct)
fun prop_of thm = dest_prop (Thm.prop_of thm)


(* conversions *)

fun if_conv pred cv1 cv2 ct = if pred (Thm.term_of ct) then cv1 ct else cv2 ct

fun if_true_conv pred cv = if_conv pred cv Conv.all_conv

fun if_exists_conv pred = if_true_conv (Term.exists_subterm pred)

fun binders_conv cv ctxt =
  Conv.binder_conv (binders_conv cv o snd) ctxt else_conv cv ctxt

fun under_quant_conv cv ctxt =
  let
    fun quant_conv inside ctxt cvs ct =
      (case Thm.term_of ct of
        Const (\<^const_name>\<open>All\<close>, _) $ Abs _ =>
          Conv.binder_conv (under_conv cvs) ctxt
      | Const (\<^const_name>\<open>Ex\<close>, _) $ Abs _ =>
          Conv.binder_conv (under_conv cvs) ctxt
      | _ => if inside then cv (ctxt, cvs) else Conv.all_conv) ct
    and under_conv cvs (cv, ctxt) = quant_conv true ctxt (cv :: cvs)
  in quant_conv false ctxt [] end

fun prop_conv cv ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>Trueprop for _\<close> => Conv.arg_conv cv ct
  | _ => raise CTERM ("not a property", [ct]))

end;
