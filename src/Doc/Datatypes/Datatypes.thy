(*  Title:      Doc/Datatypes/Datatypes.thy
    Author:     Jasmin Blanchette, TU Muenchen

Tutorial for (co)datatype definitions with the new package.
*)

theory Datatypes
imports BNF
begin

section {* Introduction *}

text {*
  * Isabelle2013 introduced new definitional package for datatypes and codatatypes

  * datatype support is similar to old package, due to Berghofer \& Wenzel \cite{xxx}
    * indeed, replacing \cmd{datatype} by \cmd{datatype\_new} is usually sufficient
      to port existing specifications to the new package

  * but it is more powerful, because it is now possible to have nested recursion
    through a large class of non-datatypes, notably finite sets:
*}

datatype_new 'a tree = Node 'a "('a tree fset)"

text {*
  * another advantage: it supports local definitions:
*}

context linorder
begin

datatype_new flag = Less | Eq | Greater

end

text {*

 * in a future release, \cmd{datatype\_new} is expected to displace \cmd{datatype}

 * 
*}

section {* Defining Datatypes *}

text {*
  * theory to include
*}

section {* Defining Primitive Recursive Functions *}

section {* Defining Codatatypes *}

section {* Defining Primitive Corecursive Functions *}

section {* Registering Bounded Natural Functors *}

section {* Generating Free Constructor Theorems *}

section {* Conclusion *}

end
