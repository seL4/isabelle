(*  Title:      HOL/UNITY/Reachability
    ID:         $Id$
    Author:     Tanja Vos, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Reachability in Graphs

From Chandy and Misra, "Parallel Program Design" (1989), sections 6.2 and 11.3
*)

Reachability = Detects + 

types  edge = "(vertex*vertex)"

record state =
  reach :: vertex => bool
  nmsg  :: edge => nat

consts REACHABLE :: edge set
       root :: vertex
       E :: edge set
       V :: vertex set

inductive "REACHABLE"
  intrs
   base "v : V ==> ((v,v) : REACHABLE)"
   step "((u,v) : REACHABLE) & (v,w) : E ==> ((u,w) : REACHABLE)"

constdefs
  reachable :: vertex => state set
  "reachable p == {s. reach s p}"

  nmsg_eq :: nat => edge  => state set
  "nmsg_eq k == %e. {s. nmsg s e = k}"

  nmsg_gt :: nat => edge  => state set
  "nmsg_gt k  == %e. {s. k < nmsg s e}"

  nmsg_gte :: nat => edge => state set
  "nmsg_gte k == %e. {s. k <= nmsg s e}"

  nmsg_lte  :: nat => edge => state set
  "nmsg_lte k  == %e. {s. nmsg s e <= k}"

  

  final :: state set
  "final == (INTER V (%v. reachable v <==> {s. (root, v) : REACHABLE})) Int (INTER E (nmsg_eq 0))"

rules
    Graph1 "root : V"

    Graph2 "(v,w) : E ==> (v : V) & (w : V)"

    MA1  "F : Always (reachable root)"

    MA2  "[|v:V|] ==> F : Always (- reachable v Un {s. ((root,v) : REACHABLE)})"

    MA3  "[|v:V;w:V|] ==> F : Always (-(nmsg_gt 0 (v,w)) Un (reachable v))"

    MA4  "[|(v,w) : E|] ==> F : Always (-(reachable v) Un (nmsg_gt 0 (v,w)) Un (reachable w))"

    MA5  "[|v:V;w:V|] ==> F : Always (nmsg_gte 0 (v,w) Int nmsg_lte 1' (v,w))"

    MA6  "[|v:V|] ==> F : Stable (reachable v)"

    MA6b "[|v:V;w:W|] ==> F : Stable (reachable v Int nmsg_lte k (v,w))"

    MA7  "[|v:V;w:V|] ==> F : UNIV LeadsTo nmsg_eq 0 (v,w)"

end

