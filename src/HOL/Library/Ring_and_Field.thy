(*  Title:      HOL/Library/Ring_and_Field.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Muenchen
*)

header {*
  \title{Ring and field structures}
  \author{Gertrud Bauer}
*}

theory Ring_and_Field = Main: 

text {*
 The class @{text ring} models commutative ring structures with $1$.
*}

axclass ring < zero, plus, minus, times, number
  add_assoc: "(a + b) + c = a + (b + c)"
  add_commute: "a + b = b + a"
  left_zero: "0 + a = a"
  left_minus: "(- a) + a = 0"
  diff_minus: "a - b = a + (- b)"
  zero_number: "0 = #0"

  mult_assoc: "(a * b) * c = a * (b * c)"
  mult_commute: "a * b = b * a"
  left_one: "#1 * a = a"

  left_distrib: "(a + b) * c = a * c + b * c"


axclass field < ring, inverse
  left_inverse: "a \<noteq> 0 ==> inverse a * a = #1"
  divides_inverse: "b \<noteq> 0 ==> a / b = a * inverse b"


axclass ordered_field < field, linorder
  add_left_mono: "a \<le> b ==> c + a \<le> c + b"
  mult_left_mono: "a \<le> b ==> 0 < c ==> c * a \<le> c * b"

end
