(*  Title:      ZF/AC/WO6_WO1.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of "WO6 ==> WO1".

From the book "Equivalents of the Axiom of Choice" by Rubin & Rubin,
pages 2-5
*)

WO6_WO1 = "rel_is_fun" + AC_Equiv + Let +

consts
(* Auxiliary definitions used in proof *)
  NN            :: i => i
  uu            :: [i, i, i, i] => i
  vv1, ww1, gg1 :: [i, i, i] => i
  vv2, ww2, gg2 :: [i, i, i, i] => i

defs

  NN_def  "NN(y) == {m \\<in> nat. \\<exists>a. \\<exists>f. Ord(a) & domain(f)=a  &  
                            (\\<Union>b<a. f`b) = y & (\\<forall>b<a. f`b lepoll m)}"

  uu_def  "uu(f, beta, gamma, delta) == (f`beta * f`gamma) Int f`delta"

  (*Definitions for case 1*)

  vv1_def "vv1(f,m,b) ==                                                
           let g = LEAST g. (\\<exists>d. Ord(d) & (domain(uu(f,b,g,d)) \\<noteq> 0 & 
                                   domain(uu(f,b,g,d)) lepoll m));      
               d = LEAST d. domain(uu(f,b,g,d)) \\<noteq> 0 &                  
                           domain(uu(f,b,g,d)) lepoll m         
           in  if f`b \\<noteq> 0 then domain(uu(f,b,g,d)) else 0"

  ww1_def "ww1(f,m,b) == f`b - vv1(f,m,b)"

  gg1_def "gg1(f,a,m) == \\<lambda>b \\<in> a++a. if b<a then vv1(f,m,b) else ww1(f,m,b--a)"
  
  (*Definitions for case 2*)

  vv2_def "vv2(f,b,g,s) ==   
           if f`g \\<noteq> 0 then {uu(f, b, g, LEAST d. uu(f,b,g,d) \\<noteq> 0)`s} else 0"

  ww2_def "ww2(f,b,g,s) == f`g - vv2(f,b,g,s)"

  gg2_def "gg2(f,a,b,s) ==
	      \\<lambda>g \\<in> a++a. if g<a then vv2(f,b,g,s) else ww2(f,b,g--a,s)"
  
end
