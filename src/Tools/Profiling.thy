(*  Author:     Makarius
    LICENSE:    Isabelle (BSD-3)

Statistics on already loaded theories, intended for dynamic invocation via
"isabelle process".
*)

theory Statistics
  imports Pure
begin

ML_file "statistics.ML"
ML_command \<open>Statistics.main ()\<close>

end
