(*  Title:      HOL/Library/Ring_and_Field.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Muenchen
*)

header {*
  \title{Rings and Fields}
  \author{Gertrud Bauer}
*}

theory Ring_and_Field = Main: 


axclass ring < plus, minus, times, number
  add_assoc: "(a + b) + c = a + (b + c)"
  add_commute: "a + b = b + a"
  left_zero: "#0 + a = a"
  left_neg: "(- a) + a = #0"
  minus_uminus: "a - b = a + (- b)"

  mult_assoc: "(a * b) * c = a * (b * c)"
  mult_commute: "a * b = b * a"
  left_one: "#1 * a = a"

  left_distrib: "(a + b) * c = a * c + b * c"


axclass field < ring, inverse
  left_inverse: "a \<noteq> #0 \<Longrightarrow> inverse a * a = #1"
  divides_inverse: "a / b = a * inverse b"

end