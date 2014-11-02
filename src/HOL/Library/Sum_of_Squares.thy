(*  Title:      HOL/Library/Sum_of_Squares.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen
*)

section {* A decision procedure for universal multivariate real arithmetic
  with addition, multiplication and ordering using semidefinite programming *}

theory Sum_of_Squares
imports Complex_Main
begin

ML_file "positivstellensatz.ML"
ML_file "Sum_of_Squares/sum_of_squares.ML"
ML_file "Sum_of_Squares/positivstellensatz_tools.ML"
ML_file "Sum_of_Squares/sos_wrapper.ML"

end
