(*
    Properties of abstract class field
    $Id$
    Author: Clemens Ballarin, started 15 November 1997
*)

Field = Factor + Ideal +

instance
  field < domain (field_integral)

instance
  field < factorial (TrueI, field_fact_prime)

end
