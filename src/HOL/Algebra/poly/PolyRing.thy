(*
    Instantiate polynomials to form a ring and prove further properties
    $Id$
    Author: Clemens Ballarin, started 20 January 1997
*)

PolyRing = UnivPoly +

instance
  up :: (ring) ring
  (up_a_assoc, up_l_zero, up_l_neg, up_a_comm, 
   up_m_assoc, up_l_one, up_l_distr, up_m_comm, up_one_not_zero,
   up_power_def) {| rtac refl 1 |}

end
