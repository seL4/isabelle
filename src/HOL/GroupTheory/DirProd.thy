(*  Title:      HOL/GroupTheory/DirProd
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Direct product of two groups
*)

DirProd = Coset +

consts
  ProdGroup :: "(['a grouptype, 'b grouptype] => ('a * 'b) grouptype)"

defs 
  ProdGroup_def "ProdGroup == %G: Group. %G': Group.
    (| carrier = ((G.<cr>) \\<times> (G'.<cr>)),
       bin_op = (%(x, x'): ((G.<cr>) \\<times> (G'.<cr>)). 
                 %(y, y'): ((G.<cr>) \\<times> (G'.<cr>)).
                  ((G.<f>) x y,(G'.<f>) x' y')),
       inverse = (%(x, y): ((G.<cr>) \\<times> (G'.<cr>)). ((G.<inv>) x, (G'.<inv>) y)),
       unit = ((G.<e>),(G'.<e>)) |)"

syntax
  "@Pro" :: "['a grouptype, 'b grouptype] => ('a * 'b) grouptype" ("<|_,_|>" [60,61]60)

translations
  "<| G , G' |>" == "ProdGroup G G'"

locale r_group = group +
  fixes
    G'        :: "'b grouptype"
    e'        :: "'b"
    binop'    :: "'b => 'b => 'b" 	("(_ ##' _)" [80,81]80 )
    INV'      :: "'b => 'b"              ("i' (_)"      [90]91)
  assumes 
    Group_G' "G' : Group"
  defines
    e'_def  "e' == unit G'"
    binop'_def "x ##' y == bin_op G' x y"
    inv'_def "i'(x) == inverse G' x"

locale prodgroup = r_group +
  fixes 
    P :: "('a * 'b) grouptype"
  defines 
    P_def "P == <| G, G' |>"
end
