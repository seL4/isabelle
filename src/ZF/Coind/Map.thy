(*  Title:      ZF/Coind/Map.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Map = QUniv +

constdefs
  TMap :: [i,i] => i
   "TMap(A,B) == {m \\<in> Pow(A*Union(B)).\\<forall>a \\<in> A. m``{a} \\<in> B}"

  PMap :: [i,i] => i
   "PMap(A,B) == TMap(A,cons(0,B))"

(* Note: 0 \\<in> B ==> TMap(A,B) = PMap(A,B) *)
  
  map_emp :: i
   "map_emp == 0"

  map_owr :: [i,i,i]=>i
   "map_owr(m,a,b) == \\<Sigma>x \\<in> {a} Un domain(m). if x=a then b else m``{x}"
  map_app :: [i,i]=>i
   "map_app(m,a) == m``{a}"
  
end
