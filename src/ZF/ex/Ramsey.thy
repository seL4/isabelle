(*  Title:      ZF/ex/ramsey.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
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

Ramsey = Main +
consts
  Symmetric             :: i=>o
  Atleast               :: [i,i]=>o
  Clique,Indept,Ramsey  :: [i,i,i]=>o

defs

  Symmetric_def
    "Symmetric(E) == (\\<forall>x y. <x,y>:E --> <y,x>:E)"

  Clique_def
    "Clique(C,V,E) == (C \\<subseteq> V) & (\\<forall>x \\<in> C. \\<forall>y \\<in> C. x\\<noteq>y --> <x,y> \\<in> E)"

  Indept_def
    "Indept(I,V,E) == (I \\<subseteq> V) & (\\<forall>x \\<in> I. \\<forall>y \\<in> I. x\\<noteq>y --> <x,y> \\<notin> E)"

  Atleast_def
    "Atleast(n,S) == (\\<exists>f. f \\<in> inj(n,S))"

  Ramsey_def
    "Ramsey(n,i,j) == \\<forall>V E. Symmetric(E) & Atleast(n,V) -->  
         (\\<exists>C. Clique(C,V,E) & Atleast(i,C)) |       
         (\\<exists>I. Indept(I,V,E) & Atleast(j,I))"

end
