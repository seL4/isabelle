(*  Title:      HOL/hologic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

Abstract syntax operations for HOL.
*)

signature HOLOGIC =
sig
  val termC: class
  val termS: sort
  val termT: typ
  val boolN: string
  val boolT: typ
  val false_const: term
  val true_const: term
  val not_const: term
  val mk_setT: typ -> typ
  val dest_setT: typ -> typ
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val conj: term
  val disj: term
  val imp: term
  val Not: term
  val mk_conj: term * term -> term
  val mk_disj: term * term -> term
  val mk_imp: term * term -> term
  val dest_imp: term -> term * term
  val dest_conj: term -> term list
  val dest_concls: term -> term list
  val eq_const: typ -> term
  val all_const: typ -> term
  val exists_const: typ -> term
  val Collect_const: typ -> term
  val mk_eq: term * term -> term
  val dest_eq: term -> term * term
  val mk_all: string * typ * term -> term
  val mk_exists: string * typ * term -> term
  val mk_Collect: string * typ * term -> term
  val mk_mem: term * term -> term
  val dest_mem: term -> term * term
  val mk_binop: string -> term * term -> term
  val mk_binrel: string -> term * term -> term
  val dest_bin: string -> typ -> term -> term * term
  val unitT: typ
  val is_unitT: typ -> bool
  val unit: term
  val is_unit: term -> bool
  val mk_prodT: typ * typ -> typ
  val dest_prodT: typ -> typ * typ
  val mk_prod: term * term -> term
  val dest_prod: term -> term * term
  val mk_fst: term -> term
  val mk_snd: term -> term
  val prodT_factors: typ -> typ list
  val split_const: typ * typ * typ -> term
  val mk_tuple: typ -> term list -> term
  val natT: typ
  val zero: term
  val is_zero: term -> bool
  val mk_Suc: term -> term
  val dest_Suc: term -> term
  val mk_nat: int -> term
  val dest_nat: term -> int
  val intT: typ
  val realT: typ
  val binT: typ
  val pls_const: term
  val min_const: term
  val bit_const: term
  val number_of_const: typ -> term
  val int_of: int list -> int
  val dest_binum: term -> int
  val mk_bin   : int -> term
end;


structure HOLogic: HOLOGIC =
struct

(* basics *)

val termC: class = "term";
val termS: sort = [termC];
val termT = TypeInfer.anyT termS;


(* bool and set *)

val boolN = "bool";
val boolT = Type (boolN, []);

val true_const =  Const ("True", boolT);
val false_const = Const ("False", boolT);
val not_const = Const ("Not", boolT --> boolT);

fun mk_setT T = Type ("set", [T]);

fun dest_setT (Type ("set", [T])) = T
  | dest_setT T = raise TYPE ("dest_setT: set type expected", [T], []);


(* logic *)

val Trueprop = Const ("Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);


val conj = Const ("op &", [boolT, boolT] ---> boolT)
and disj = Const ("op |", [boolT, boolT] ---> boolT)
and imp = Const ("op -->", [boolT, boolT] ---> boolT)
and Not = Const ("Not", boolT --> boolT);

fun mk_conj (t1, t2) = conj $ t1 $ t2
and mk_disj (t1, t2) = disj $ t1 $ t2
and mk_imp (t1, t2) = imp $ t1 $ t2;

fun dest_imp (Const("op -->",_) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun dest_conj (Const ("op &", _) $ t $ t') = t :: dest_conj t'
  | dest_conj t = [t];

fun imp_concl_of t = imp_concl_of (#2 (dest_imp t)) handle TERM _ => t;
val dest_concls = map imp_concl_of o dest_conj o dest_Trueprop;

fun eq_const T = Const ("op =", [T, T] ---> boolT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_eq (Const ("op =", _) $ lhs $ rhs) = (lhs, rhs)
  | dest_eq t = raise TERM ("dest_eq", [t])

fun all_const T = Const ("All", [T --> boolT] ---> boolT);
fun mk_all (x, T, P) = all_const T $ absfree (x, T, P);

fun exists_const T = Const ("Ex", [T --> boolT] ---> boolT);
fun mk_exists (x, T, P) = exists_const T $ absfree (x, T, P);

fun Collect_const T = Const ("Collect", [T --> boolT] ---> mk_setT T);
fun mk_Collect (a, T, t) = Collect_const T $ absfree (a, T, t);

fun mk_mem (x, A) =
  let val setT = fastype_of A in
    Const ("op :", [dest_setT setT, setT] ---> boolT) $ x $ A
  end;

fun dest_mem (Const ("op :", _) $ x $ A) = (x, A)
  | dest_mem t = raise TERM ("dest_mem", [t]);


(* binary oprations and relations *)

fun mk_binop c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> T) $ t $ u
  end;

fun mk_binrel c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> boolT) $ t $ u
  end;

fun dest_bin c T (tm as Const (c', Type ("fun", [T', _])) $ t $ u) =
      if c = c' andalso T = T' then (t, u)
      else raise TERM ("dest_bin " ^ c, [tm])
  | dest_bin c _ tm = raise TERM ("dest_bin " ^ c, [tm]);


(* unit *)

val unitT = Type ("Product_Type.unit", []);

fun is_unitT (Type ("Product_Type.unit", [])) = true
  | is_unitT _ = false;

val unit = Const ("Product_Type.Unity", unitT);

fun is_unit (Const ("Product_Type.Unity", _)) = true
  | is_unit _ = false;


(* prod *)

fun mk_prodT (T1, T2) = Type ("*", [T1, T2]);

fun dest_prodT (Type ("*", [T1, T2])) = (T1, T2)
  | dest_prodT T = raise TYPE ("dest_prodT", [T], []);

fun mk_prod (t1, t2) =
  let val T1 = fastype_of t1 and T2 = fastype_of t2 in
    Const ("Pair", [T1, T2] ---> mk_prodT (T1, T2)) $ t1 $ t2
  end;

fun dest_prod (Const ("Pair", _) $ t1 $ t2) = (t1, t2)
  | dest_prod t = raise TERM ("dest_prod", [t]);

fun mk_fst p =
  let val pT = fastype_of p in
    Const ("fst", pT --> fst (dest_prodT pT)) $ p
  end;

fun mk_snd p =
  let val pT = fastype_of p in
    Const ("snd", pT --> snd (dest_prodT pT)) $ p
  end;

(*Maps the type T1 * ... * Tn to [T1, ..., Tn], however nested*)
fun prodT_factors (Type ("*", [T1, T2])) = prodT_factors T1 @ prodT_factors T2
  | prodT_factors T = [T];

fun split_const (Ta, Tb, Tc) = 
    Const ("split", [[Ta, Tb] ---> Tc, mk_prodT (Ta, Tb)] ---> Tc);

(*Makes a nested tuple from a list, following the product type structure*)
fun mk_tuple (Type ("*", [T1, T2])) tms = 
        mk_prod (mk_tuple T1 tms, 
                 mk_tuple T2 (drop (length (prodT_factors T1), tms)))
  | mk_tuple T (t::_) = t;



(* proper tuples *)

local  (*currently unused*)

fun mk_tupleT Ts = foldr mk_prodT (Ts, unitT);

fun dest_tupleT (Type ("Product_Type.unit", [])) = []
  | dest_tupleT (Type ("*", [T, U])) = T :: dest_tupleT U
  | dest_tupleT T = raise TYPE ("dest_tupleT", [T], []);

fun mk_tuple ts = foldr mk_prod (ts, unit);

fun dest_tuple (Const ("Product_Type.Unity", _)) = []
  | dest_tuple (Const ("Pair", _) $ t $ u) = t :: dest_tuple u
  | dest_tuple t = raise TERM ("dest_tuple", [t]);

in val _ = unit end;


(* nat *)

val natT = Type ("nat", []);

val zero = Const ("0", natT);

fun is_zero (Const ("0", _)) = true
  | is_zero _ = false;

fun mk_Suc t = Const ("Suc", natT --> natT) $ t;

fun dest_Suc (Const ("Suc", _) $ t) = t
  | dest_Suc t = raise TERM ("dest_Suc", [t]);

fun mk_nat 0 = zero
  | mk_nat n = mk_Suc (mk_nat (n - 1));

fun dest_nat (Const ("0", _)) = 0
  | dest_nat (Const ("Suc", _) $ t) = dest_nat t + 1
  | dest_nat t = raise TERM ("dest_nat", [t]);


val intT = Type ("IntDef.int", []);

val realT = Type("RealDef.real",[]);


(* binary numerals *)

val binT = Type ("Numeral.bin", []);

val pls_const =  Const ("Numeral.bin.Pls", binT)
and min_const = Const ("Numeral.bin.Min", binT)
and bit_const = Const ("Numeral.bin.Bit", [binT, boolT] ---> binT);

fun number_of_const T = Const ("Numeral.number_of", binT --> T);


fun int_of [] = 0
  | int_of (b :: bs) = b + 2 * int_of bs;

fun dest_bit (Const ("False", _)) = 0
  | dest_bit (Const ("True", _)) = 1
  | dest_bit t = raise TERM("dest_bit", [t]);

fun bin_of (Const ("Numeral.bin.Pls", _)) = []
  | bin_of (Const ("Numeral.bin.Min", _)) = [~1]
  | bin_of (Const ("Numeral.bin.Bit", _) $ bs $ b) = dest_bit b :: bin_of bs
  | bin_of t = raise TERM("bin_of", [t]);

val dest_binum = int_of o bin_of;

fun mk_bit 0 = false_const
  | mk_bit 1 = true_const
  | mk_bit _ = sys_error "mk_bit";

fun mk_bin n =
  let
    fun bin_of 0  = []
      | bin_of ~1 = [~1]
      | bin_of n  = (n mod 2) :: bin_of (n div 2);

    fun term_of []   = pls_const
      | term_of [~1] = min_const
      | term_of (b :: bs) = bit_const $ term_of bs $ mk_bit b;
    in term_of (bin_of n) end;

end;
