(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge
*)

header {* Binary arithmetic for the natural numbers *}

theory NatBin = IntPower
files ("nat_bin.ML"):

text {*
  This case is simply reduced to that for the non-negative integers.
*}


instance nat :: number ..

defs (overloaded)
  nat_number_of_def: "(number_of::bin => nat) v == nat ((number_of :: bin => int) v)"

use "nat_bin.ML"
setup nat_bin_arith_setup

(* Enable arith to deal with div/mod k where k is a numeral: *)
declare split_div[of _ _ "number_of k", standard, arith_split]
declare split_mod[of _ _ "number_of k", standard, arith_split]

lemma nat_number_of_Pls: "number_of bin.Pls = (0::nat)"
  by (simp add: number_of_Pls nat_number_of_def)

lemma nat_number_of_Min: "number_of bin.Min = (0::nat)"
  apply (simp only: number_of_Min nat_number_of_def nat_zminus_int)
  apply (simp add: neg_nat)
  done

lemma nat_number_of_BIT_True:
  "number_of (w BIT True) =
    (if neg (number_of w) then 0
     else let n = number_of w in Suc (n + n))"
  apply (simp only: nat_number_of_def Let_def split: split_if)
  apply (intro conjI impI)
   apply (simp add: neg_nat neg_number_of_BIT)
  apply (rule int_int_eq [THEN iffD1])
  apply (simp only: not_neg_nat neg_number_of_BIT int_Suc zadd_int [symmetric] simp_thms)
  apply (simp only: number_of_BIT if_True zadd_assoc)
  done

lemma nat_number_of_BIT_False:
    "number_of (w BIT False) = (let n::nat = number_of w in n + n)"
  apply (simp only: nat_number_of_def Let_def)
  apply (cases "neg (number_of w)")
   apply (simp add: neg_nat neg_number_of_BIT)
  apply (rule int_int_eq [THEN iffD1])
  apply (simp only: not_neg_nat neg_number_of_BIT int_Suc zadd_int [symmetric] simp_thms)
  apply (simp only: number_of_BIT if_False zadd_0 zadd_assoc)
  done

lemmas nat_number =
  nat_number_of_Pls nat_number_of_Min
  nat_number_of_BIT_True nat_number_of_BIT_False

lemma Let_Suc [simp]: "Let (Suc n) f == f (Suc n)"
  by (simp add: Let_def)


subsection {* Configuration of the code generator *}

ML {*
infix 7 `*;
infix 6 `+;

val op `* = op * : int * int -> int;
val op `+ = op + : int * int -> int;
val `~ = ~ : int -> int;
*}

types_code
  "int" ("int")

lemmas [code] = int_0 int_Suc

lemma [code]: "nat x = (if x <= 0 then 0 else Suc (nat (x - 1)))"
  by (simp add: Suc_nat_eq_nat_zadd1)

consts_code
  "0" :: "int"                  ("0")
  "1" :: "int"                  ("1")
  "uminus" :: "int => int"      ("`~")
  "op +" :: "int => int => int" ("(_ `+/ _)")
  "op *" :: "int => int => int" ("(_ `*/ _)")
  "neg"                         ("(_ < 0)")

end
