(*  Title:      Tools/profiling.ML
    Author:     Makarius

Session profiling based on loaded ML image.
*)

theory Profiling
  imports Pure
begin

ML_file "profiling.ML"
ML_command \<open>Profiling.main ()\<close>

end
