(*  Title:       NSComplexArith
    Author:      Lawrence C. Paulson
    Copyright:   2003  University of Cambridge

Common factor cancellation
*)

theory NSComplexArith = NSComplexBin
files "hcomplex_arith.ML":

subsubsection{*Division By @{term "-1"}*}

lemma hcomplex_divide_minus1 [simp]: "x/-1 = -(x::hcomplex)"
by simp

lemma hcomplex_minus1_divide [simp]: "-1/(x::hcomplex) = - (1/x)"
by (simp add: hcomplex_divide_def inverse_minus_eq)

end
