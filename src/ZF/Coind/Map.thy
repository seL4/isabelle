(*  Title: 	ZF/Coind/Map.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Map = QUniv +

consts
  TMap :: "[i,i] => i"
  PMap :: "[i,i] => i"
defs
  TMap_def "TMap(A,B) == {m:Pow(A*Union(B)).ALL a:A.m``{a}:B}"
  PMap_def "PMap(A,B) == TMap(A,cons(0,B))"

(* Note: 0:B ==> TMap(A,B) = PMap(A,B) *)
  
consts
  map_emp :: "i"
  map_owr :: "[i,i,i]=>i"
  map_app :: "[i,i]=>i"
defs
  map_emp_def "map_emp == 0"
  map_owr_def "map_owr(m,a,b) == SUM x:{a} Un domain(m).if(x=a,b,m``{x})"
  map_app_def "map_app(m,a) == m``{a}"
  
end
