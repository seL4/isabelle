(*  Title:      HOL/ex/PiSets.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

The bijection between elements of the Pi set and functional graphs

Also the nice -> operator for function space
*)

PiSets = Datatype_Universe + Finite +

syntax
  "->" :: "['a set, 'b set] => ('a => 'b) set"      (infixr 60) 

translations
  "A -> B" == "A funcset B"

constdefs
(* bijection between Pi_sig and Pi_=> *)
  PiBij :: "['a set, 'a => 'b set, 'a => 'b] => ('a * 'b) set"
    "PiBij A B == lam f: Pi A B. {(x, y). x: A & y = f x}"

  Graph ::  "['a set, 'a => 'b set] => ('a * 'b) set set"
   "Graph A B == {f. f: Pow(Sigma A B) & (! x: A. (?! y. (x, y): f))}"

end
