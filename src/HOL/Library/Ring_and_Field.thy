(*  Title:      HOL/Library/Ring_and_Field.thy
    ID:         $Id$
    Author:     Gertrud Bauer and Markus Wenzel, TU Muenchen
*)

header {*
  \title{Ring and field structures}
  \author{Gertrud Bauer and Markus Wenzel}
*}

theory Ring_and_Field = Main: 

subsection {* Abstract algebraic structures *}

axclass ring < zero, plus, minus, times, number
  add_assoc: "(a + b) + c = a + (b + c)"
  add_commute: "a + b = b + a"
  left_zero: "0 + a = a"
  right_minus: "a + - a = 0"
  diff_minus: "a - b = a + (-b)"
  zero_number: "0 = #0"

  mult_assoc: "(a * b) * c = a * (b * c)"
  mult_commute: "a * b = b * a"
  left_one: "#1 * a = a"

  left_distrib: "(a + b) * c = a * c + b * c"

axclass ordered_ring < ring, linorder
  add_left_mono: "a \<le> b ==> c + a \<le> c + b"
  mult_strict_left_mono: "a < b ==> 0 < c ==> c * a < c * b"
  abs_if: "\<bar>a\<bar> = (if a < 0 then -a else a)"

axclass field < ring, inverse
  left_inverse: "a \<noteq> 0 ==> inverse a * a = #1"
  divides_inverse: "b \<noteq> 0 ==> a / b = a * inverse b"

axclass ordered_field < ordered_ring, field

subsection {* simplification rules *}

lemma left_minus [simp]: "- (a::'a::field) + a = 0"
  by (simp only: add_commute right_minus)

lemma diff_self [simp]: "a - (a::'a::field) = 0"
  by (simp only: diff_minus right_minus)

subsection {* The ordered ring of integers *}

instance int :: ordered_ring
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)" by simp
  show "i + j = j + i" by simp
  show "0 + i = i" by simp
  show "i + - i = 0" by simp
  show "i - j = i + (-j)" by simp
  show "(i * j) * k = i * (j * k)" by simp
  show "i * j = j * i" by simp
  show "#1 * i = i" by simp
  show "0 = (#0::int)" by simp
  show "(i + j) * k = i * k + j * k" by (simp add: int_distrib)
  show "i \<le> j ==> k + i \<le> k + j" by simp
  show "i < j ==> 0 < k ==> k * i < k * j" by (simp add: zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)" by (simp only: zabs_def)
qed

end
