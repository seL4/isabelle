(*  Title: 	ZF/AC/WO6_WO1.thy
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

The proof of "WO6 ==> WO1".

From the book "Equivalents of the Axiom of Choice" by Rubin & Rubin,
pages 2-5
*)

WO6_WO1 = "rel_is_fun" + AC_Equiv +

consts
(* Auxiliary definitions used in proof *)
  NN       :: "i => i"
  uu       :: "[i, i, i, i] => i"
  vv1, ww1 :: "[i, i, i] => i"
  vv2, ww2 :: "[i, i, i, i] => i"

defs

  NN_def  "NN(y) == {m:nat. EX a. EX f. Ord(a) & domain(f)=a  &  \
\			    (UN b<a. f`b) = y & (ALL b<a. f`b lepoll m)}"

  uu_def  "uu(f, beta, gamma, delta) == (f`beta * f`gamma) Int f`delta"
  
  vv1_def "vv1(f,b,m) == if(f`b ~= 0,   \
\          domain(uu(f,b,   \
\          LEAST g. (EX d. Ord(d) & (domain(uu(f,b,g,d)) ~= 0 &   \
\	   domain(uu(f,b,g,d)) lesspoll m)),   \
\          LEAST d. domain(uu(f,b,   \
\          LEAST g. (EX d. Ord(d) & (domain(uu(f,b,g,d)) ~= 0 &   \
\	   domain(uu(f,b,g,d)) lesspoll m)), d)) ~= 0 &   \
\          domain(uu(f,b,   \
\          LEAST g. (EX d. Ord(d) & (domain(uu(f,b,g,d)) ~= 0 &   \
\	   domain(uu(f,b,g,d)) lesspoll m)), d)) lesspoll m)), 0)"

  ww1_def "ww1(f,b,m) == f`b - vv1(f,b,m)"

  vv2_def "vv2(f,b,g,s) ==   \
\	   if(f`g ~= 0, {uu(f,b,g,LEAST d. uu(f,b,g,d) ~= 0)`s}, 0)"

  ww2_def "ww2(f,b,g,s) == f`g - vv2(f,b,g,s)"

end
