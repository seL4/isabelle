(*  Title:      HOL/UNITY/PriorityAux
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Auxiliary definitions needed in Priority.thy
*)

PriorityAux = UNITY_Main +

types vertex
arities vertex :: type
  
constdefs
  (* symmetric closure: removes the orientation of a relation *)
  symcl :: "(vertex*vertex)set=>(vertex*vertex)set"
  "symcl r == r Un (r^-1)"

  (* Neighbors of a vertex i *)
  neighbors :: "[vertex, (vertex*vertex)set]=>vertex set"
 "neighbors i r == ((r Un r^-1)``{i}) - {i}"

  R :: "[vertex, (vertex*vertex)set]=>vertex set"
  "R i r == r``{i}"

  A :: "[vertex, (vertex*vertex)set]=>vertex set"
  "A i r == (r^-1)``{i}"

  (* reachable and above vertices: the original notation was R* and A* *)  
  reach :: "[vertex, (vertex*vertex)set]=> vertex set"
  "reach i r == (r^+)``{i}"

  above :: "[vertex, (vertex*vertex)set]=> vertex set"
  "above i r == ((r^-1)^+)``{i}"  

  reverse :: "[vertex, (vertex*vertex) set]=>(vertex*vertex)set"
  "reverse i r == (r - {(x,y). x=i | y=i} Int r) Un ({(x,y). x=i|y=i} Int r)^-1"

  (* The original definition *)
  derive1 :: "[vertex, (vertex*vertex)set, (vertex*vertex)set]=>bool"
  "derive1 i r q == symcl r = symcl q &
                    (ALL k k'. k~=i & k'~=i -->((k,k'):r) = ((k,k'):q)) &
                    A i r = {} & R i q = {}"

  (* Our alternative definition *)
  derive :: "[vertex, (vertex*vertex)set, (vertex*vertex)set]=>bool"
  "derive i r q == A i r = {} & (q = reverse i r)"

rules
  (* we assume that the universe of vertices is finite  *)
  finite_vertex_univ "finite (UNIV :: vertex set)"

end
