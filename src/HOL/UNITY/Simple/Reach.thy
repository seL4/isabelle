(*  Title:      HOL/UNITY/Reach.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Reachability in Directed Graphs.  From Chandy and Misra, section 6.4.
*)

Reach = FP + SubstAx +

types   vertex
        state = "vertex=>bool"

arities vertex :: term

consts
  init ::  "vertex"

  edges :: "(vertex*vertex) set"

constdefs

  asgt  :: "[vertex,vertex] => (state*state) set"
    "asgt u v == {(s,s'). s' = s(v:= s u | s v)}"

  Rprg :: state program
    "Rprg == mk_program ({%v. v=init}, UN (u,v): edges. {asgt u v}, UNIV)"

  reach_invariant :: state set
    "reach_invariant == {s. (ALL v. s v --> (init, v) : edges^*) & s init}"

  fixedpoint :: state set
    "fixedpoint == {s. ALL (u,v): edges. s u --> s v}"

  metric :: state => nat
    "metric s == card {v. ~ s v}"

rules

  (*We assume that the set of vertices is finite*)
  finite_graph "finite (UNIV :: vertex set)"
  
end
