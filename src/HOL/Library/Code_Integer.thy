(*  Title:      HOL/Library/Code_Integer.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Pretty integer literals for code generation *}

theory Code_Integer
imports Main Code_Natural
begin

text {*
  Representation-ignorant code equations for conversions.
*}

lemma nat_code [code]:
  "nat k = (if k \<le> 0 then 0 else
     let
       (l, j) = divmod_int k 2;
       n = nat l;
       l' = n + n
     in if j = 0 then l' else Suc l')"
proof -
  have "2 = nat 2" by simp
  show ?thesis
    apply (subst nat_mult_2 [symmetric])
    apply (auto simp add: Let_def divmod_int_mod_div not_le
     nat_div_distrib nat_mult_distrib mult_div_cancel mod_2_not_eq_zero_eq_one_int)
    apply (unfold `2 = nat 2`)
    apply (subst nat_mod_distrib [symmetric])
    apply simp_all
  done
qed

lemma (in ring_1) of_int_code:
  "of_int k = (if k = 0 then 0
     else if k < 0 then - of_int (- k)
     else let
       (l, j) = divmod_int k 2;
       l' = 2 * of_int l
     in if j = 0 then l' else l' + 1)"
proof -
  from mod_div_equality have *: "of_int k = of_int (k div 2 * 2 + k mod 2)" by simp
  show ?thesis
    by (simp add: Let_def divmod_int_mod_div mod_2_not_eq_zero_eq_one_int
      of_int_add [symmetric]) (simp add: * mult_commute)
qed

declare of_int_code [code]

text {*
  HOL numeral expressions are mapped to integer literals
  in target languages, using predefined target language
  operations for abstract integer operations.
*}

code_type int
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")
  (Haskell "Integer")
  (Scala "BigInt")
  (Eval "int")

code_instance int :: equal
  (Haskell -)

code_const "0::int"
  (SML "0")
  (OCaml "Big'_int.zero'_big'_int")
  (Haskell "0")
  (Scala "BigInt(0)")

setup {*
  fold (Numeral.add_code @{const_name Int.Pos}
    false Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

setup {*
  fold (Numeral.add_code @{const_name Int.Neg}
    true Code_Printer.literal_numeral) ["SML", "OCaml", "Haskell", "Scala"]
*}

code_const "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")
  (Scala infixl 7 "+")
  (Eval infixl 8 "+")

code_const "uminus \<Colon> int \<Rightarrow> int"
  (SML "IntInf.~")
  (OCaml "Big'_int.minus'_big'_int")
  (Haskell "negate")
  (Scala "!(- _)")
  (Eval "~/ _")

code_const "op - \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.- ((_), (_))")
  (OCaml "Big'_int.sub'_big'_int")
  (Haskell infixl 6 "-")
  (Scala infixl 7 "-")
  (Eval infixl 8 "-")

code_const Int.dup
  (SML "IntInf.*/ (2,/ (_))")
  (OCaml "Big'_int.mult'_big'_int/ 2")
  (Haskell "!(2 * _)")
  (Scala "!(2 * _)")
  (Eval "!(2 * _)")

code_const Int.sub
  (SML "!(raise/ Fail/ \"sub\")")
  (OCaml "failwith/ \"sub\"")
  (Haskell "error/ \"sub\"")
  (Scala "!error(\"sub\")")

code_const "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")
  (Scala infixl 8 "*")
  (Eval infixl 9 "*")

code_const pdivmod
  (SML "IntInf.divMod/ (IntInf.abs _,/ IntInf.abs _)")
  (OCaml "Big'_int.quomod'_big'_int/ (Big'_int.abs'_big'_int _)/ (Big'_int.abs'_big'_int _)")
  (Haskell "divMod/ (abs _)/ (abs _)")
  (Scala "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k.abs '/% l.abs))")
  (Eval "Integer.div'_mod/ (abs _)/ (abs _)")

code_const "HOL.equal \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infix 4 "==")
  (Scala infixl 5 "==")
  (Eval infixl 6 "=")

code_const "op \<le> \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")
  (Scala infixl 4 "<=")
  (Eval infixl 6 "<=")

code_const "op < \<Colon> int \<Rightarrow> int \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")
  (Scala infixl 4 "<")
  (Eval infixl 6 "<")

code_const Code_Numeral.int_of
  (SML "IntInf.fromInt")
  (OCaml "_")
  (Haskell "toInteger")
  (Scala "!_.as'_BigInt")
  (Eval "_")

code_const "Code_Evaluation.term_of \<Colon> int \<Rightarrow> term"
  (Eval "HOLogic.mk'_number/ HOLogic.intT")

end
