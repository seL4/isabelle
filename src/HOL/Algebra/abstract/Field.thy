(*
    Properties of abstract class field
    $Id$
    Author: Clemens Ballarin, started 15 November 1997
*)

Field = Factor + PID +

instance
  field < domain (field_one_not_zero, field_integral)

instance
  field < factorial (TrueI, field_fact_prime)

end
