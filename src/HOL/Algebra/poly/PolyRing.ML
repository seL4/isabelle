(*
    Instantiate polynomials to form a ring and prove further properties
    $Id$
    Author: Clemens Ballarin, started 22 January 1997
*)

(* Properties of *s:
   Polynomials form a module *)

goal UnivPoly.thy "!!a::'a::ring. (a + b) *s p = a *s p + b *s p";
by (rtac up_eqI 1);
by (simp_tac (simpset() addsimps [l_distr]) 1);
qed "smult_l_distr";

goal UnivPoly.thy "!!a::'a::ring. a *s (p + q) = a *s p + a *s q";
by (rtac up_eqI 1);
by (simp_tac (simpset() addsimps [r_distr]) 1);
qed "smult_r_distr";

goal UnivPoly.thy "!!a::'a::ring. (a * b) *s p = a *s (b *s p)";
by (rtac up_eqI 1);
by (simp_tac (simpset() addsimps [m_assoc]) 1);
qed "smult_assoc1";

goal UnivPoly.thy "(<1>::'a::ring) *s p = p";
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "smult_one";

(* Polynomials form an algebra *)

goal UnivPoly.thy "!!a::'a::ring. (a *s p) * q = a *s (p * q)";
by (rtac up_eqI 1);
by (simp_tac (simpset() addsimps [SUM_rdistr, m_assoc]) 1);
qed "smult_assoc2";

(* the following can be derived from the above ones,
   for generality reasons, it is therefore done *)

Goal "(0::'a::ring) *s p = 0";
by (rtac a_lcancel 1);
by (rtac (smult_l_distr RS sym RS trans) 1);
by (Simp_tac 1);
qed "smult_l_null";

Goal "!!a::'a::ring. a *s 0 = 0";
by (rtac a_lcancel 1);
by (rtac (smult_r_distr RS sym RS trans) 1);
by (Simp_tac 1);
qed "smult_r_null";

Goal "!!a::'a::ring. (-a) *s p = - (a *s p)";
by (rtac a_lcancel 1);
by (rtac (r_neg RS sym RSN (2, trans)) 1);
by (rtac (smult_l_distr RS sym RS trans) 1);
by (simp_tac (simpset() addsimps [smult_l_null, r_neg]) 1);
qed "smult_l_minus";

Goal "!!a::'a::ring. a *s (-p) = - (a *s p)";
by (rtac a_lcancel 1);
by (rtac (r_neg RS sym RSN (2, trans)) 1);
by (rtac (smult_r_distr RS sym RS trans) 1);
by (simp_tac (simpset() addsimps [smult_r_null, r_neg]) 1);
qed "smult_r_minus";

val smult_minus = [smult_l_minus, smult_r_minus];

Addsimps [smult_one, smult_l_null, smult_r_null];
