(*  Title:      HOL/IMP/Expr.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM

Arithmetic expressions and Boolean expressions.
Not used in the rest of the language, but included for completeness.
*)

open Expr;

val evala_elim_cases = map (evala.mk_cases aexp.simps)
   ["<N(n),sigma> -a-> i", "<X(x),sigma> -a-> i",
    "<Op1 f e,sigma> -a-> i", "<Op2 f a1 a2,sigma>  -a-> i"
   ];

val evalb_elim_cases = map (evalb.mk_cases bexp.simps)
   ["<true,sigma> -b-> x", "<false,sigma> -b-> x",
    "<ROp f a0 a1,sigma> -b-> x", "<noti(b),sigma> -b-> x",
    "<b0 andi b1,sigma> -b-> x", "<b0 ori b1,sigma> -b-> x"
   ];

val evalb_simps = map (fn s => prove_goal Expr.thy s
    (fn _ => [fast_tac (HOL_cs addSIs evalb.intrs addSEs evalb_elim_cases) 1]))
  ["(<true,sigma> -b-> w) = (w=True)",
   "(<false,sigma> -b-> w) = (w=False)",
   "(<ROp f a0 a1,sigma> -b-> w) = \
\   (? m. <a0,sigma> -a-> m & (? n. <a1,sigma> -a-> n & w = f m n))",
   "(<noti(b),sigma> -b-> w) = (? x. <b,sigma> -b-> x & w = (~x))",
   "(<b0 andi b1,sigma> -b-> w) = \
\   (? x. <b0,sigma> -b-> x & (? y. <b1,sigma> -b-> y & w = (x&y)))",
   "(<b0 ori b1,sigma> -b-> w) = \
\   (? x. <b0,sigma> -b-> x & (? y. <b1,sigma> -b-> y & w = (x|y)))"];

goal Expr.thy "!n. (<a,s> -a-> n) = (n = A a s)";
by (aexp.induct_tac "a" 1);                               (* struct. ind. *)
by (ALLGOALS Simp_tac);                                   (* rewr. Den.   *)
by (TRYALL (fast_tac (set_cs addSIs (evala.intrs@prems)
                             addSEs evala_elim_cases)));
qed_spec_mp "aexp_iff";

goal Expr.thy "!w. (<b,s> -b-> w) = (w = B b s)";
by (bexp.induct_tac "b" 1);
by (ALLGOALS(asm_simp_tac (!simpset addcongs [conj_cong]
                                    addsimps (aexp_iff::evalb_simps))));
qed_spec_mp "bexp_iff";
