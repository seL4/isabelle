(*  Title:      HOL/hologic.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

Abstract syntax operations for HOL.
*)

signature HOLOGIC =
sig
  val typeS: sort
  val typeT: typ
  val boolN: string
  val boolT: typ
  val true_const: term
  val false_const: term
  val mk_setT: typ -> typ
  val dest_setT: typ -> typ
  val Trueprop: term
  val mk_Trueprop: term -> term
  val dest_Trueprop: term -> term
  val Trueprop_conv: (cterm -> thm) -> cterm -> thm
  val conj: term
  val disj: term
  val imp: term
  val Not: term
  val mk_conj: term * term -> term
  val mk_disj: term * term -> term
  val mk_imp: term * term -> term
  val mk_not: term -> term
  val dest_conj: term -> term list
  val dest_disj: term -> term list
  val dest_imp: term -> term * term
  val dest_not: term -> term
  val dest_concls: term -> term list
  val eq_const: typ -> term
  val mk_eq: term * term -> term
  val dest_eq: term -> term * term
  val all_const: typ -> term
  val mk_all: string * typ * term -> term
  val list_all: (string * typ) list * term -> term
  val exists_const: typ -> term
  val mk_exists: string * typ * term -> term
  val choice_const: typ -> term
  val Collect_const: typ -> term
  val mk_Collect: string * typ * term -> term
  val class_eq: string
  val mk_mem: term * term -> term
  val dest_mem: term -> term * term
  val mk_UNIV: typ -> term
  val mk_binop: string -> term * term -> term
  val mk_binrel: string -> term * term -> term
  val dest_bin: string -> typ -> term -> term * term
  val unitT: typ
  val is_unitT: typ -> bool
  val unit: term
  val is_unit: term -> bool
  val mk_prodT: typ * typ -> typ
  val dest_prodT: typ -> typ * typ
  val pair_const: typ -> typ -> term
  val mk_prod: term * term -> term
  val dest_prod: term -> term * term
  val mk_fst: term -> term
  val mk_snd: term -> term
  val split_const: typ * typ * typ -> term
  val mk_split: term -> term
  val prodT_factors: typ -> typ list
  val mk_tuple: typ -> term list -> term
  val natT: typ
  val zero: term
  val is_zero: term -> bool
  val mk_Suc: term -> term
  val dest_Suc: term -> term
  val Suc_zero: term
  val mk_nat: IntInf.int -> term
  val dest_nat: term -> IntInf.int
  val class_size: string
  val size_const: typ -> term
  val bitT: typ
  val B0_const: term
  val B1_const: term
  val mk_bit: int -> term
  val dest_bit: term -> int
  val intT: typ
  val pls_const: term
  val min_const: term
  val bit_const: term
  val mk_numeral: IntInf.int -> term
  val dest_numeral: term -> IntInf.int
  val number_of_const: typ -> term
  val add_numerals_of: term -> (term * typ) list -> (term * typ) list
  val mk_number: typ -> IntInf.int -> term
  val dest_number: term -> typ * IntInf.int
  val realT: typ
  val nibbleT: typ
  val mk_nibble: int -> term
  val dest_nibble: term -> int
  val charT: typ
  val mk_char: int -> term
  val dest_char: term -> int
  val listT: typ -> typ
  val mk_list: typ -> term list -> term
  val dest_list: term -> term list
  val stringT: typ
  val mk_string: string -> term
  val dest_string: term -> string
end;

structure HOLogic: HOLOGIC =
struct

(* HOL syntax *)

val typeS: sort = ["HOL.type"];
val typeT = TypeInfer.anyT typeS;


(* bool and set *)

val boolN = "bool";
val boolT = Type (boolN, []);

val true_const =  Const ("True", boolT);
val false_const = Const ("False", boolT);

fun mk_setT T = Type ("set", [T]);

fun dest_setT (Type ("set", [T])) = T
  | dest_setT T = raise TYPE ("dest_setT: set type expected", [T], []);


(* logic *)

val Trueprop = Const ("Trueprop", boolT --> propT);

fun mk_Trueprop P = Trueprop $ P;

fun dest_Trueprop (Const ("Trueprop", _) $ P) = P
  | dest_Trueprop t = raise TERM ("dest_Trueprop", [t]);

fun Trueprop_conv conv ct = (case term_of ct of
    Const ("Trueprop", _) $ _ =>
      let val (ct1, ct2) = Thm.dest_comb ct
      in Thm.combination (Thm.reflexive ct1) (conv ct2) end
  | _ => raise TERM ("Trueprop_conv", []));

val conj = Const ("op &", [boolT, boolT] ---> boolT)
and disj = Const ("op |", [boolT, boolT] ---> boolT)
and imp = Const ("op -->", [boolT, boolT] ---> boolT)
and Not = Const ("Not", boolT --> boolT);

fun mk_conj (t1, t2) = conj $ t1 $ t2
and mk_disj (t1, t2) = disj $ t1 $ t2
and mk_imp (t1, t2) = imp $ t1 $ t2
and mk_not t = Not $ t;

fun dest_conj (Const ("op &", _) $ t $ t') = t :: dest_conj t'
  | dest_conj t = [t];

fun dest_disj (Const ("op |", _) $ t $ t') = t :: dest_disj t'
  | dest_disj t = [t];

fun dest_imp (Const("op -->",_) $ A $ B) = (A, B)
  | dest_imp  t = raise TERM ("dest_imp", [t]);

fun dest_not (Const ("Not", _) $ t) = t
  | dest_not t = raise TERM ("dest_not", [t]);

fun imp_concl_of t = imp_concl_of (#2 (dest_imp t)) handle TERM _ => t;
val dest_concls = map imp_concl_of o dest_conj o dest_Trueprop;

fun eq_const T = Const ("op =", [T, T] ---> boolT);
fun mk_eq (t, u) = eq_const (fastype_of t) $ t $ u;

fun dest_eq (Const ("op =", _) $ lhs $ rhs) = (lhs, rhs)
  | dest_eq t = raise TERM ("dest_eq", [t])

fun all_const T = Const ("All", [T --> boolT] ---> boolT);
fun mk_all (x, T, P) = all_const T $ absfree (x, T, P);
fun list_all (xs, t) = fold_rev (fn (x, T) => fn P => all_const T $ Abs (x, T, P)) xs t;

fun exists_const T = Const ("Ex", [T --> boolT] ---> boolT);
fun mk_exists (x, T, P) = exists_const T $ absfree (x, T, P);

fun choice_const T = Const("Hilbert_Choice.Eps", (T --> boolT) --> T);

fun Collect_const T = Const ("Collect", [T --> boolT] ---> mk_setT T);
fun mk_Collect (a, T, t) = Collect_const T $ absfree (a, T, t);

val class_eq = "Code_Generator.eq";

fun mk_mem (x, A) =
  let val setT = fastype_of A in
    Const ("op :", [dest_setT setT, setT] ---> boolT) $ x $ A
  end;

fun dest_mem (Const ("op :", _) $ x $ A) = (x, A)
  | dest_mem t = raise TERM ("dest_mem", [t]);

fun mk_UNIV T = Const ("UNIV", mk_setT T);


(* binary operations and relations *)

fun mk_binop c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> T) $ t $ u
  end;

fun mk_binrel c (t, u) =
  let val T = fastype_of t in
    Const (c, [T, T] ---> boolT) $ t $ u
  end;

(*destruct the application of a binary operator. The dummyT case is a crude
  way of handling polymorphic operators.*)
fun dest_bin c T (tm as Const (c', Type ("fun", [T', _])) $ t $ u) =
      if c = c' andalso (T=T' orelse T=dummyT) then (t, u)
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

fun pair_const T1 T2 = Const ("Pair", [T1, T2] ---> mk_prodT (T1, T2));

fun mk_prod (t1, t2) =
  let val T1 = fastype_of t1 and T2 = fastype_of t2 in
    pair_const T1 T2 $ t1 $ t2
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

fun split_const (A, B, C) =
  Const ("split", (A --> B --> C) --> mk_prodT (A, B) --> C);

fun mk_split t =
  (case Term.fastype_of t of
    T as (Type ("fun", [A, Type ("fun", [B, C])])) =>
      Const ("split", T --> mk_prodT (A, B) --> C) $ t
  | _ => raise TERM ("mk_split: bad body type", [t]));

(*Maps the type T1 * ... * Tn to [T1, ..., Tn], however nested*)
fun prodT_factors (Type ("*", [T1, T2])) = prodT_factors T1 @ prodT_factors T2
  | prodT_factors T = [T];

(*Makes a nested tuple from a list, following the product type structure*)
fun mk_tuple (Type ("*", [T1, T2])) tms =
        mk_prod (mk_tuple T1 tms,
                 mk_tuple T2 (Library.drop (length (prodT_factors T1), tms)))
  | mk_tuple T (t::_) = t;


(* nat *)

val natT = Type ("nat", []);

val zero = Const ("HOL.zero_class.zero", natT);

fun is_zero (Const ("HOL.zero_class.zero", _)) = true
  | is_zero _ = false;

fun mk_Suc t = Const ("Suc", natT --> natT) $ t;

fun dest_Suc (Const ("Suc", _) $ t) = t
  | dest_Suc t = raise TERM ("dest_Suc", [t]);

val Suc_zero = mk_Suc zero;

fun mk_nat n =
  let
    fun mk 0 = zero
      | mk n = mk_Suc (mk (IntInf.- (n, 1)));
  in if IntInf.< (n, 0)
    then error "mk_nat: negative numeral"
    else mk n
  end;

fun dest_nat (Const ("HOL.zero_class.zero", _)) = 0
  | dest_nat (Const ("Suc", _) $ t) = IntInf.+ (dest_nat t, 1)
  | dest_nat t = raise TERM ("dest_nat", [t]);

val class_size = "Nat.size";

fun size_const T = Const ("Nat.size_class.size", T --> natT);


(* bit *)

val bitT = Type ("Numeral.bit", []);

val B0_const = Const ("Numeral.bit.B0", bitT);
val B1_const =  Const ("Numeral.bit.B1", bitT);

fun mk_bit 0 = B0_const
  | mk_bit 1 = B1_const
  | mk_bit _ = raise TERM ("mk_bit", []);

fun dest_bit (Const ("Numeral.bit.B0", _)) = 0
  | dest_bit (Const ("Numeral.bit.B1", _)) = 1
  | dest_bit t = raise TERM ("dest_bit", [t]);


(* binary numerals and int -- non-unique representation due to leading zeros/ones! *)

val intT = Type ("IntDef.int", []);

val pls_const = Const ("Numeral.Pls", intT)
and min_const = Const ("Numeral.Min", intT)
and bit_const = Const ("Numeral.Bit", [intT, bitT] ---> intT);

fun mk_numeral 0 = pls_const
  | mk_numeral ~1 = min_const
  | mk_numeral i =
      let val (q, r) = IntInf.divMod (i, 2)
      in bit_const $ mk_numeral q $ mk_bit (IntInf.toInt r) end;

fun dest_numeral (Const ("Numeral.Pls", _)) = 0
  | dest_numeral (Const ("Numeral.Min", _)) = ~1
  | dest_numeral (Const ("Numeral.Bit", _) $ bs $ b) =
      2 * dest_numeral bs + IntInf.fromInt (dest_bit b)
  | dest_numeral t = raise TERM ("dest_numeral", [t]);

fun number_of_const T = Const ("Numeral.number_class.number_of", intT --> T);

fun add_numerals_of (Const _) =
      I
  | add_numerals_of (Var _) =
      I
  | add_numerals_of (Free _) =
      I
  | add_numerals_of (Bound _) =
      I
  | add_numerals_of (Abs (_, _, t)) =
      add_numerals_of t
  | add_numerals_of (t as _ $ _) =
      case strip_comb t
       of (Const ("Numeral.number_class.number_of",
           Type (_, [_, T])), ts) => fold (cons o rpair T) ts
        | (t', ts) => add_numerals_of t' #> fold add_numerals_of ts;

fun mk_number T 0 = Const ("HOL.zero_class.zero", T)
  | mk_number T 1 = Const ("HOL.one_class.one", T)
  | mk_number T i = number_of_const T $ mk_numeral i;

fun dest_number (Const ("HOL.zero_class.zero", T)) = (T, 0)
  | dest_number (Const ("HOL.one_class.one", T)) = (T, 1)
  | dest_number (Const ("Numeral.number_class.number_of", Type ("fun", [_, T])) $ t) =
      (T, dest_numeral t)
  | dest_number t = raise TERM ("dest_number", [t]);


(* real *)

val realT = Type ("RealDef.real", []);


(* nibble *)

val nibbleT = Type ("List.nibble", []);

fun mk_nibble n =
  let val s =
    if 0 <= n andalso n <= 9 then chr (n + ord "0")
    else if 10 <= n andalso n <= 15 then chr (n + ord "A" - 10)
    else raise TERM ("mk_nibble", [])
  in Const ("List.nibble.Nibble" ^ s, nibbleT) end;

fun dest_nibble t =
  let fun err () = raise TERM ("dest_nibble", [t]) in
    (case try (unprefix "List.nibble.Nibble" o fst o Term.dest_Const) t of
      NONE => err ()
    | SOME c =>
        if size c <> 1 then err ()
        else if "0" <= c andalso c <= "9" then ord c - ord "0"
        else if "A" <= c andalso c <= "F" then ord c - ord "A" + 10
        else err ())
  end;


(* char *)

val charT = Type ("List.char", []);

fun mk_char n =
  if 0 <= n andalso n <= 255 then
    Const ("List.char.Char", nibbleT --> nibbleT --> charT) $
      mk_nibble (n div 16) $ mk_nibble (n mod 16)
  else raise TERM ("mk_char", []);

fun dest_char (Const ("List.char.Char", _) $ t $ u) =
      dest_nibble t * 16 + dest_nibble u
  | dest_char t = raise TERM ("dest_char", [t]);


(* list *)

fun listT T = Type ("List.list", [T]);

fun mk_list T ts =
  let
    val lT = listT T;
    val Nil = Const ("List.list.Nil", lT);
    fun Cons t u = Const ("List.list.Cons", T --> lT --> lT) $ t $ u;
  in fold_rev Cons ts Nil end;

fun dest_list (Const ("List.list.Nil", _)) = []
  | dest_list (Const ("List.list.Cons", _) $ t $ u) = t :: dest_list u
  | dest_list t = raise TERM ("dest_list", [t]);


(* string *)

val stringT = Type ("List.string", []);

val mk_string = mk_list charT o map (mk_char o ord) o explode;
val dest_string = implode o map (chr o dest_char) o dest_list;

end;
