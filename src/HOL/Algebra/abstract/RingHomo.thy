(*
    Ring homomorphism
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

RingHomo = NatSum +

consts
  homo	:: ('a::ringS => 'b::ringS) => bool

defs
  homo_def	"homo f == (ALL a b. f (a + b) = f a + f b &
			      f (a * b) = f a * f b) &
			   f <1> = <1>"

end
