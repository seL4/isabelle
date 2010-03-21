(*  Author: Clemens Ballarin, started 5 October 1999

Principle ideal domains.
*)

theory PID
imports Ideal2
begin

instance pid < factorial
  apply intro_classes
  apply (erule pid_irred_imp_prime)
  done

end
