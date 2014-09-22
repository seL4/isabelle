(*  Title:      HOL/Library/Sum_of_Squares.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Philipp Meyer, TU Muenchen
*)

header {* A decision method for universal multivariate real arithmetic with addition, 
  multiplication and ordering using semidefinite programming *}

theory Sum_of_Squares
imports Complex_Main
begin

ML_file "positivstellensatz.ML"
ML_file "Sum_of_Squares/sum_of_squares.ML"
ML_file "Sum_of_Squares/positivstellensatz_tools.ML"
ML_file "Sum_of_Squares/sos_wrapper.ML"

text {*
  Proof method sos invocations:
  \begin{itemize}

  \item remote solver: @{text "(sos remote_csdp)"}

  \item local solver: @{text "(sos csdp)"}

  The latter requires a local executable from
  @{url "https://projects.coin-or.org/Csdp"} and the Isabelle settings variable
  variable @{text ISABELLE_CSDP} pointing to it.

  \end{itemize}

  By default, method sos calls @{text remote_csdp}.  This can take of
  the order of a minute for one sos call, because sos calls CSDP
  repeatedly.  If you install CSDP locally, sos calls typically takes
  only a few seconds.

  The sos method generates a certificate which can be used to repeat
  the proof without calling an external prover.
*}

end
