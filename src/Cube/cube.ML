(*  Title: 	Cube/cube
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1990  University of Cambridge

For cube.thy.  The systems of the Lambda-cube that extend simple types
*)

open Cube;

val simple = [s_b,strip_s,strip_b,app,lam_ss,pi_ss];

val L2_thy = extend_theory Cube.thy "L2" ([],[],[],[],[],None)
[
  ("pi_bs",  "[| A:[]; !!x. x:A ==> B(x):* |] ==> Prod(A,B):*"),

  ("lam_bs", "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |] \
\	==> Abs(A,f) : Prod(A,B)")
];

val lam_bs = get_axiom L2_thy "lam_bs";
val pi_bs = get_axiom L2_thy "pi_bs";

val L2 = simple @ [lam_bs,pi_bs];

val Lomega_thy = extend_theory Cube.thy "Lomega" ([],[],[],[],[],None)
[
  ("pi_bb",  "[| A:[]; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"),

  ("lam_bb", "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |] \
\	==> Abs(A,f) : Prod(A,B)")
];

val lam_bb = get_axiom Lomega_thy "lam_bb";
val pi_bb = get_axiom Lomega_thy "pi_bb";
val Lomega = simple @ [lam_bb,pi_bb];

val LOmega_thy = merge_theories(L2_thy,Lomega_thy);
val LOmega = simple @ [lam_bs,pi_bs,lam_bb,pi_bb];

val LP_thy = extend_theory Cube.thy "LP" ([],[],[],[],[],None)
[
  ("pi_sb",  "[| A:*; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"),

  ("lam_sb", "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |] \
\	==> Abs(A,f) : Prod(A,B)")
];

val lam_sb = get_axiom LP_thy "lam_sb";
val pi_sb = get_axiom LP_thy "pi_sb";
val LP = simple @ [lam_sb,pi_sb];

val LP2_thy = merge_theories(L2_thy,LP_thy);
val LP2 = simple @ [lam_bs,pi_bs,lam_sb,pi_sb];

val LPomega_thy = merge_theories(LP_thy,Lomega_thy);
val LPomega = simple @ [lam_bb,pi_bb,lam_sb,pi_sb];

val CC_thy = merge_theories(L2_thy,LPomega_thy);
val CC = simple @ [lam_bs,pi_bs,lam_bb,pi_bb,lam_sb,pi_sb];
