(*  Title:      HOL/GroupTheory/Exponent
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

The combinatorial argument underlying the first Sylow theorem

    exponent p s   yields the greatest power of p that divides s.
*)

Exponent = Main + Primes +

constdefs

  exponent      :: "[nat, nat] => nat"
  "exponent p s == if p \\<in> prime then (GREATEST r. p^r dvd s) else 0"

end
