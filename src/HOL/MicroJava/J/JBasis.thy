(*  Title:      HOL/MicroJava/J/JBasis.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TU Muenchen

Some auxiliary definitions.
*)

JBasis = Main + 

constdefs

  unique  :: "('a \\<times> 'b) list \\<Rightarrow> bool"
 "unique  \\<equiv> nodups \\<circ> map fst"

  list_all2 :: "('a \\<Rightarrow> 'b \\<Rightarrow> bool) \\<Rightarrow> ('a list \\<Rightarrow> 'b list \\<Rightarrow> bool)"
 "list_all2 P xs ys \\<equiv> length xs = length ys \\<and> (\\<forall> (x,y)\\<in>set (zip xs ys). P x y)"

end
