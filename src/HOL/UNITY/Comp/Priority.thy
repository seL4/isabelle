(*  Title:      HOL/UNITY/Priority
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

The priority system

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

Priority = PriorityAux +

types state = "(vertex*vertex)set"
types command = "vertex=>(state*state)set"
  
consts
  (* the initial state *)
  init :: "(vertex*vertex)set"  

constdefs
  (* from the definitions given in section 4.4 *)
  (* i has highest priority in r *)
  highest :: "[vertex, (vertex*vertex)set]=>bool"
  "highest i r == A i r = {}"
  
  (* i has lowest priority in r *)
  lowest :: "[vertex, (vertex*vertex)set]=>bool"
  "lowest i r == R i r = {}"

  act :: command
  "act i == {(s, s'). s'=reverse i s & highest i s}"

  (* All components start with the same initial state *)
  Component :: "vertex=>state program"
  "Component i == mk_program({init}, {act i}, UNIV)"

  (* Abbreviations *)
  Highest :: "vertex=>state set"
  "Highest i == {s. highest i s}"

  Lowest :: "vertex=>state set"
  "Lowest i == {s. lowest i s}"

  Acyclic :: "state set"
  "Acyclic == {s. acyclic s}"

  (* Every above set has a maximal vertex: two equivalent defs. *)

  Maximal :: "state set"
  "Maximal == INT i. {s. ~highest i s-->(EX j:above i  s. highest j s)}"

  Maximal' :: "state set"
  "Maximal' == INT i. Highest i Un (UN j. {s. j:above i s} Int Highest j)"

  
  Safety :: "state set"
  "Safety == INT i. {s. highest i s --> (ALL j:neighbors i s. ~highest j s)}"


  (* Composition of a finite set of component;
     the vertex 'UNIV' is finite by assumption *)
  
  system :: "state program"
  "system == JN i. Component i"
end