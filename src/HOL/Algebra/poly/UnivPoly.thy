(*
    Univariate Polynomials
    $Id$
    Author: Clemens Ballarin, started 9 December 1996
*)

UnivPoly = ProtoPoly +

typedef (UP)
  ('a) up = "{f :: nat => 'a::ringS. EX n. bound n f}" (UP_witness)

instance
  up :: (ringS) ringS

consts
  coeff		:: [nat, 'a up] => 'a::ringS
  "*s"		:: ['a::ringS, 'a up] => 'a up		(infixl 70)
  monom		:: nat => ('a::ringS) up
  const		:: 'a::ringS => 'a up

  "*X^"		:: ['a, nat] => 'a up		("(3_*X^/_)" [71, 71] 70)

translations
  "a *X^ n"	== "a *s monom n"
  (* this translation is only nice for non-nested polynomials *)

defs
  coeff_def	"coeff n p == Rep_UP p n"
  up_add_def	"p + q == Abs_UP (%n. Rep_UP p n + Rep_UP q n)"
  up_smult_def	"a *s p == Abs_UP (%n. a * Rep_UP p n)"
  monom_def	"monom m == Abs_UP (%n. if m=n then <1> else <0>)"
  const_def	"const a == Abs_UP (%n. if n=0 then a else <0>)"
  up_mult_def	"p * q == Abs_UP (%n. SUM n
		     (%i. Rep_UP p i * Rep_UP q (n-i)))"

  up_zero_def	"<0> == Abs_UP (%x. <0>)"
  up_one_def	"<1> == monom 0"
  up_uminus_def	"- p == (-<1>) *s p"
  up_power_def	"a ^ n == nat_rec (<1>::('a::ringS) up) (%u b. b * a) n"
end


