(*  Title: 	ZF/AC/WO6_WO1.thy
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

The proof of "WO6 ==> WO1".

From the book "Equivalents of the Axiom of Choice" by Rubin & Rubin,
pages 2-5
*)

WO6_WO1 = "rel_is_fun" + AC_Equiv + Let +

consts
(* Auxiliary definitions used in proof *)
  NN            :: "i => i"
  uu            :: "[i, i, i, i] => i"
  vv1, ww1, gg1 :: "[i, i, i] => i"
  vv2, ww2, gg2 :: "[i, i, i, i] => i"

defs

  NN_def  "NN(y) == {m:nat. EX a. EX f. Ord(a) & domain(f)=a  &  
			    (UN b<a. f`b) = y & (ALL b<a. f`b lepoll m)}"

  uu_def  "uu(f, beta, gamma, delta) == (f`beta * f`gamma) Int f`delta"

  (*Definitions for case 1*)

  vv1_def "vv1(f,m,b) ==   						
   	   let g = LEAST g. (EX d. Ord(d) & (domain(uu(f,b,g,d)) ~= 0 &	
	                           domain(uu(f,b,g,d)) lepoll m));   	
	       d = LEAST d. domain(uu(f,b,g,d)) ~= 0 &   		
                           domain(uu(f,b,g,d)) lepoll m		
	   in  if(f`b ~= 0, domain(uu(f,b,g,d)), 0)"

  ww1_def "ww1(f,m,b) == f`b - vv1(f,m,b)"

  gg1_def "gg1(f,a,m) == lam b:a++a. if (b<a, vv1(f,m,b), ww1(f,m,b--a))"
  
  (*Definitions for case 2*)

  vv2_def "vv2(f,b,g,s) ==   
	   if(f`g ~= 0, {uu(f, b, g, LEAST d. uu(f,b,g,d) ~= 0)`s}, 0)"

  ww2_def "ww2(f,b,g,s) == f`g - vv2(f,b,g,s)"

  gg2_def "gg2(f,a,b,s) == lam g:a++a. if (g<a, vv2(f,b,g,s), ww2(f,b,g--a,s))"
  
end
