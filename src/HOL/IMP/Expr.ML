(*  Title:      HOL/IMP/Expr.ML
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner & Tobias Nipkow, TUM
    Copyright   1994 TUM

Arithmetic expressions and Boolean expressions.
Not used in the rest of the language, but included for completeness.
*)

val evala_elim_cases = 
    map evala.mk_cases
       ["(N(n),sigma) -a-> i", 
	"(X(x),sigma) -a-> i",
	"(Op1 f e,sigma) -a-> i", 
	"(Op2 f a1 a2,sigma)  -a-> i"];

val evalb_elim_cases = 
    map evalb.mk_cases
       ["(true,sigma) -b-> x", 
	"(false,sigma) -b-> x",
	"(ROp f a0 a1,sigma) -b-> x", 
	"(noti(b),sigma) -b-> x",
	"(b0 andi b1,sigma) -b-> x", 
	"(b0 ori b1,sigma) -b-> x"];

val evalb_simps = map (fn s => prove_goal Expr.thy s
    (fn _ => [fast_tac (HOL_cs addSIs evalb.intrs addSEs evalb_elim_cases) 1]))
  ["((true,sigma) -b-> w) = (w=True)",
   "((false,sigma) -b-> w) = (w=False)",
   "((ROp f a0 a1,sigma) -b-> w) = \
\   (? m. (a0,sigma) -a-> m & (? n. (a1,sigma) -a-> n & w = f m n))",
   "((noti(b),sigma) -b-> w) = (? x. (b,sigma) -b-> x & w = (~x))",
   "((b0 andi b1,sigma) -b-> w) = \
\   (? x. (b0,sigma) -b-> x & (? y. (b1,sigma) -b-> y & w = (x&y)))",
   "((b0 ori b1,sigma) -b-> w) = \
\   (? x. (b0,sigma) -b-> x & (? y. (b1,sigma) -b-> y & w = (x|y)))"];

Goal "!n. ((a,s) -a-> n) = (A a s = n)";
by (induct_tac "a" 1);
by (auto_tac (claset() addSIs evala.intrs addSEs evala_elim_cases,
	      simpset()));
qed_spec_mp "aexp_iff";

Goal "!w. ((b,s) -b-> w) = (B b s = w)";
by (induct_tac "b" 1);
by (auto_tac (claset(), 
	      simpset() addsimps aexp_iff::evalb_simps));
qed_spec_mp "bexp_iff";
