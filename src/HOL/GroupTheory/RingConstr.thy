(*  Title:      HOL/GroupTheory/RingConstr
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Construction of a ring from a semigroup and an Abelian group 
*)

RingConstr = Homomorphism +

constdefs
  ring_of :: "['a grouptype, 'a semigrouptype] => 'a ringtype"
  "ring_of ==
     %G: AbelianGroup. %S: {M. M \\<in> Semigroup & (M.<cr>) = (G.<cr>)}.
                   (| carrier = (G.<cr>), bin_op = (G.<f>), 
                      inverse = (G.<inv>), unit = (G.<e>), Rmult = (S.<f>) |)"

  ring_constr :: "('a grouptype * 'a semigrouptype *'a ringtype) set"
  "ring_constr ==
    \\<Sigma>G \\<in> AbelianGroup. \\<Sigma>S \\<in> {M. M \\<in> Semigroup & (M.<cr>) = (G.<cr>)}.
	 {R. R = (| carrier = (G.<cr>), bin_op = (G.<f>), 
		     inverse = (G.<inv>), unit = (G.<e>),
		     Rmult = (S.<f>) |) &
	     (\\<forall>x \\<in> (R.<cr>). \\<forall>y \\<in> (R.<cr>). \\<forall>z \\<in> (R.<cr>). 
	     ((R.<m>) x ((R.<f>) y z) = (R.<f>) ((R.<m>) x y) ((R.<m>) x z))) &
(\\<forall>x \\<in> (R.<cr>). \\<forall>y \\<in> (R.<cr>). \\<forall>z \\<in> (R.<cr>). 
	     ((R.<m>) ((R.<f>) y z) x = (R.<f>) ((R.<m>) y x) ((R.<m>) z x)))}"

  ring_from :: "['a grouptype, 'a semigrouptype] => 'a ringtype"
  "ring_from == %G: AbelianGroup. 
     %S: {M. M \\<in> Semigroup & (M.<cr>) = (G.<cr>) &
                distr_l (G.<cr>) (M.<f>) (G.<f>) &
	        distr_r (G.<cr>) (M.<f>) (G.<f>)}.
            (| carrier = (G.<cr>), bin_op = (G.<f>), 
               inverse = (G.<inv>), unit = (G.<e>), Rmult = (S.<f>) |)"

end

