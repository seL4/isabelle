(*  Title:      HOL/ex/PiSets.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

The bijection between elements of the Pi set and functional graphs
*)

PiSets = Group +

constdefs
(* bijection between Pi_sig and Pi_=> *)
  PiBij :: "['a set, 'a => 'b set, 'a => 'b] => ('a * 'b) set"
    "PiBij A B == lam f: Pi A B. {(x, y). x: A & y = f x}"

  Graph ::  "['a set, 'a => 'b set] => ('a * 'b) set set"
   "Graph A B == {f. f \\<in> Pow(Sigma A B) & (\\<forall>x\\<in>A. \\<exists>!y. (x, y) \\<in> f)}"

end
