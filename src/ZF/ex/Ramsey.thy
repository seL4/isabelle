(*  Title: 	ZF/ex/ramsey.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Ramsey's Theorem (finite exponent 2 version)

Based upon the article
    D Basin and M Kaufmann,
    The Boyer-Moore Prover and Nuprl: An Experimental Comparison.
    In G Huet and G Plotkin, editors, Logical Frameworks.
    (CUP, 1991), pages 89--119

See also
    M Kaufmann,
    An example in NQTHM: Ramsey's Theorem
    Internal Note, Computational Logic, Inc., Austin, Texas 78703
    Available from the author: kaufmann@cli.com
*)

Ramsey = Arith +
consts
  Symmetric   		:: i=>o
  Atleast     		:: [i,i]=>o
  Clique,Indept,Ramsey	:: [i,i,i]=>o

defs

  Symmetric_def
    "Symmetric(E) == (ALL x y. <x,y>:E --> <y,x>:E)"

  Clique_def
    "Clique(C,V,E) == (C<=V) & (ALL x:C. ALL y:C. x~=y --> <x,y> : E)"

  Indept_def
    "Indept(I,V,E) == (I<=V) & (ALL x:I. ALL y:I. x~=y --> <x,y> ~: E)"

  Atleast_def
    "Atleast(n,S) == (EX f. f: inj(n,S))"

  Ramsey_def
    "Ramsey(n,i,j) == ALL V E. Symmetric(E) & Atleast(n,V) -->  
         (EX C. Clique(C,V,E) & Atleast(i,C)) |       
         (EX I. Indept(I,V,E) & Atleast(j,I))"

end
