(*  Title:      ZF/ex/Data.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Sample datatype definition.  
It has four contructors, of arities 0-3, and two parameters A and B.
*)

Data = Datatype +

consts
  data :: [i,i] => i

datatype
  "data(A,B)" = Con0
              | Con1 ("a \\<in> A")
              | Con2 ("a \\<in> A", "b \\<in> B")
              | Con3 ("a \\<in> A", "b \\<in> B", "d \\<in> data(A,B)")

end
