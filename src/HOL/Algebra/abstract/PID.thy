(*
    Principle ideal domains
    $Id$
    Author: Clemens Ballarin, started 5 October 1999
*)

theory PID imports Ideal begin

instance pid < factorial
  apply intro_classes
   apply (rule TrueI)
  apply (erule pid_irred_imp_prime)
  done

end
