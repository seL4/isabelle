(*  Title:      HOL/IMP/Com.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

open Com;

val evala_elim_cases = map (evala.mk_cases aexp.simps)
   ["<N(n),sigma> -a-> i", "<X(x),sigma> -a-> i",
    "<Op1 f e,sigma> -a-> i", "<Op2 f a1 a2,sigma>  -a-> i"
   ];

val evalb_elim_cases = map (evalb.mk_cases bexp.simps)
   ["<true,sigma> -b-> x", "<false,sigma> -b-> x",
    "<ROp f a0 a1,sigma> -b-> x", "<noti(b),sigma> -b-> x",
    "<b0 andi b1,sigma> -b-> x", "<b0 ori b1,sigma> -b-> x"
   ];

val evalb_simps = map (fn s => prove_goal Com.thy s
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
