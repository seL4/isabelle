(*  Title:      HOL/Lex/RegSet.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Regular sets
*)

RegSet = Main +

constdefs
 conc :: 'a list set => 'a list set => 'a list set
"conc A B == {xs@ys | xs ys. xs:A & ys:B}"

consts star :: 'a list set => 'a list set
inductive "star A"
intrs
  NilI   "[] : star A"
  ConsI  "[| a:A; as : star A |] ==> a@as : star A"

end
