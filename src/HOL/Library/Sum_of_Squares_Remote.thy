(*  Title:      HOL/Library/Sum_of_Squares_Remote.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen
*)

header {* Examples with remote CSDP *}

theory Sum_of_Squares_Remote
imports Sum_of_Squares
begin

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x \<Longrightarrow> a < 0"
  by (sos remote_csdp)

lemma "a1 >= 0 & a2 >= 0 \<and> (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) \<and> (a1 * b1 + a2 * b2 = 0) --> a1 * a2 - b1 * b2 >= (0::real)"
  by (sos remote_csdp)

lemma "(3::real) * x + 7 * a < 4 & 3 < 2 * x --> a < 0"
  by (sos remote_csdp)

lemma "(0::real) <= x & x <= 1 & 0 <= y & y <= 1  --> x^2 + y^2 < 1 |(x - 1)^2 + y^2 < 1 | x^2 + (y - 1)^2 < 1 | (x - 1)^2 + (y - 1)^2 < 1"
  by (sos remote_csdp)

lemma "(0::real) <= x & 0 <= y & 0 <= z & x + y + z <= 3 --> x * y + x * z + y * z >= 3 * x * y * z"
  by (sos remote_csdp)

lemma "((x::real)^2 + y^2 + z^2 = 1) --> (x + y + z)^2 <= 3"
  by (sos remote_csdp)

lemma "(w^2 + x^2 + y^2 + z^2 = 1) --> (w + x + y + z)^2 <= (4::real)"
  by (sos remote_csdp)

lemma "(x::real) >= 1 & y >= 1 --> x * y >= x + y - 1"
  by (sos remote_csdp)

end
