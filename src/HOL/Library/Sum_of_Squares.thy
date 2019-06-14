(*  Title:      HOL/Library/Sum_of_Squares.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen
*)

section \<open>A decision procedure for universal multivariate real arithmetic
  with addition, multiplication and ordering using semidefinite programming\<close>

theory Sum_of_Squares
imports Complex_Main
begin

ML_file \<open>Sum_of_Squares/positivstellensatz.ML\<close>
ML_file \<open>Sum_of_Squares/positivstellensatz_tools.ML\<close>
ML_file \<open>Sum_of_Squares/sum_of_squares.ML\<close>
ML_file \<open>Sum_of_Squares/sos_wrapper.ML\<close>

end
