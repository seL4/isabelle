(*  Title:      HOL/NatBin.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Binary arithmetic for the natural numbers

This case is simply reduced to that for the non-negative integers
*)

theory NatBin = IntPower
files ("nat_bin.ML"):

instance  nat :: number ..

defs
  nat_number_of_def:
    "number_of v == nat (number_of v)"
     (*::bin=>nat        ::bin=>int*)

use "nat_bin.ML"	setup nat_bin_arith_setup


subsection {* Configuration of the code generator *}

types_code
  "int" ("int")

lemmas [code] = int_0 int_Suc

lemma [code]: "nat x = (if x <= 0 then 0 else Suc (nat (x - 1)))"
  by (simp add: Suc_nat_eq_nat_zadd1)

consts_code
  "0" :: "int"                  ("0")
  "1" :: "int"                  ("1")
  "uminus" :: "int => int"      ("~")
  "op +" :: "int => int => int" ("(_ +/ _)")
  "op *" :: "int => int => int" ("(_ */ _)")
  "neg"                         ("(_ < 0)")

end
