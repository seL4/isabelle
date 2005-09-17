(*
    Ring homomorphism
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

theory RingHomo imports Ring begin

constdefs
  homo  :: "('a::ring => 'b::ring) => bool"
  "homo f == (ALL a b. f (a + b) = f a + f b &
                                   f (a * b) = f a * f b) &
                                   f 1 = 1"

end
