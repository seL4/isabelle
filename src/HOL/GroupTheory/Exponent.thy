(*  Title:      HOL/GroupTheory/Exponent
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   2001  University of Cambridge
*)

Exponent = Main + Primes +

constdefs

  (*??use the one in Fun.thy?*)
  funcset :: "['a set, 'b set] => ('a => 'b) set"   ("_ -> _" [91,90]90)
   "A -> B == {f. \\<forall>x \\<in> A. f(x) \\<in> B}"

  exponent      :: "[nat, nat] => nat"
  "exponent p s == if p \\<in> prime then (GREATEST r. p ^ r dvd s) else 0"

end
