(*  Title:      Provers/Arith/cancel_sums.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Cancel common literals in balanced expressions:

     i + #m + j ~~ i' + #m' + j'  ==  #(m-m') + i + j ~~ i' + j'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, -).
*)

signature CANCEL_NUMERALS_DATA =
sig
  (*abstract syntax*)
  val mk_numeral: int -> term
  val find_first_numeral: term list -> int * term * term list
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> term * term -> thm option
  val subst_tac: term -> tactic
  val all_simp_tac: tactic
end;

signature CANCEL_NUMERALS =
sig
  val proc: Sign.sg -> thm list -> term -> thm option
end;


functor CancelNumeralsFun(Data: CANCEL_NUMERALS_DATA): CANCEL_NUMERALS =
struct

(*predicting the outputs of other simprocs given a term of the form
   (i + ... #m + ... j) - #n   *)
fun cancelled m n terms =
    if m = n then (*cancel_sums: sort the terms*)
	sort Term.term_ord terms 
    else          (*inverse_fold: subtract, keeping original term order*)
	Data.mk_numeral (m - n) :: terms;

(*the simplification procedure*)
fun proc sg _ t =
  let val (t1,t2) = Data.dest_bal t 
      val (n1, lit1, terms1) = Data.find_first_numeral (Data.dest_sum t1)
      and (n2, lit2, terms2) = Data.find_first_numeral (Data.dest_sum t2)
      val lit_n = if n1<n2 then lit1 else lit2
      and n     = BasisLibrary.Int.min (n1,n2)
          (*having both the literals and their integer values makes it
            more robust against negative natural number literals*)
  in
      Data.prove_conv [Data.subst_tac lit_n, Data.all_simp_tac] sg
	 (t, Data.mk_bal (Data.mk_sum (cancelled n1 n terms1),
			  Data.mk_sum (cancelled n2 n terms2)))
  end
  handle _ => None;

end;
