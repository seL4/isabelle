(*
    Properties of abstract class field
    Author: Clemens Ballarin, started 15 November 1997
*)

theory Field imports Factor PID begin

instance field < "domain"
  apply intro_classes
   apply (rule field_one_not_zero)
  apply (erule field_integral)
  done

instance field < factorial
  apply intro_classes
  apply (erule field_fact_prime)
  done

end
