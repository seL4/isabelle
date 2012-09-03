(*  Author:     Bernhard Haeupler *)

header {* Some examples demonstrating the comm-ring method *}

theory Commutative_Ring_Ex
imports "../Commutative_Ring"
begin

lemma "4*(x::int)^5*y^3*x^2*3 + x*z + 3^5 = 12*x^7*y^3 + z*x + 243"
  by comm_ring

lemma "((x::int) + y)^2  = x^2 + y^2 + 2*x*y"
  by comm_ring

lemma "((x::int) + y)^3  = x^3 + y^3 + 3*x^2*y + 3*y^2*x"
  by comm_ring

lemma "((x::int) - y)^3  = x^3 + 3*x*y^2 + (-3)*y*x^2 - y^3"
  by comm_ring

lemma "((x::int) - y)^2  = x^2 + y^2 - 2*x*y"
  by comm_ring

lemma " ((a::int) + b + c)^2 = a^2 + b^2 + c^2 + 2*a*b + 2*b*c + 2*a*c"
  by comm_ring

lemma "((a::int) - b - c)^2 = a^2 + b^2 + c^2 - 2*a*b + 2*b*c - 2*a*c"
  by comm_ring

lemma "(a::int)*b + a*c = a*(b+c)"
  by comm_ring

lemma "(a::int)^2 - b^2 = (a - b) * (a + b)"
  by comm_ring

lemma "(a::int)^3 - b^3 = (a - b) * (a^2 + a*b + b^2)"
  by comm_ring

lemma "(a::int)^3 + b^3 = (a + b) * (a^2 - a*b + b^2)"
  by comm_ring

lemma "(a::int)^4 - b^4 = (a - b) * (a + b)*(a^2 + b^2)"
  by comm_ring

lemma "(a::int)^10 - b^10 =
  (a - b) * (a^9 + a^8*b + a^7*b^2 + a^6*b^3 + a^5*b^4 + a^4*b^5 + a^3*b^6 + a^2*b^7 + a*b^8 + b^9)"
  by comm_ring

end
