(*  Title:      Cube/Cube.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1990  University of Cambridge

For Cube.thy.  The systems of the Lambda-cube that extend simple types
*)

open Cube;

val simple = [s_b,strip_s,strip_b,app,lam_ss,pi_ss];

val L2_thy =
  Cube.thy
  |> Theory.add_axioms
   [("pi_bs",  "[| A:[]; !!x. x:A ==> B(x):* |] ==> Prod(A,B):*"),
    ("lam_bs", "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |] \
     \  ==> Abs(A,f) : Prod(A,B)")]
  |> Theory.add_name "L2";

val lam_bs = get_axiom L2_thy "lam_bs";
val pi_bs = get_axiom L2_thy "pi_bs";

val L2 = simple @ [lam_bs,pi_bs];

val Lomega_thy =
  Cube.thy
  |> Theory.add_axioms
   [("pi_bb",  "[| A:[]; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"),
    ("lam_bb", "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |] \
     \  ==> Abs(A,f) : Prod(A,B)")]
  |> Theory.add_name "Lomega";

val lam_bb = get_axiom Lomega_thy "lam_bb";
val pi_bb = get_axiom Lomega_thy "pi_bb";
val Lomega = simple @ [lam_bb,pi_bb];

val LOmega_thy = merge_theories(L2_thy,Lomega_thy);
val LOmega = simple @ [lam_bs,pi_bs,lam_bb,pi_bb];

val LP_thy =
  Cube.thy
  |> Theory.add_axioms
   [("pi_sb",  "[| A:*; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"),
    ("lam_sb", "[| A:*; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |] \
     \  ==> Abs(A,f) : Prod(A,B)")]
  |> Theory.add_name "LP";

val lam_sb = get_axiom LP_thy "lam_sb";
val pi_sb = get_axiom LP_thy "pi_sb";
val LP = simple @ [lam_sb,pi_sb];

val LP2_thy = merge_theories(L2_thy,LP_thy);
val LP2 = simple @ [lam_bs,pi_bs,lam_sb,pi_sb];

val LPomega_thy = merge_theories(LP_thy,Lomega_thy);
val LPomega = simple @ [lam_bb,pi_bb,lam_sb,pi_sb];

val CC_thy = merge_theories(L2_thy,LPomega_thy);
val CC = simple @ [lam_bs,pi_bs,lam_bb,pi_bb,lam_sb,pi_sb];
