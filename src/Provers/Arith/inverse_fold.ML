(*  Title:      Provers/Arith/inverse_fold.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

For things like  (i + #m + j) - #n   == #(m-n) + i + j    (n<m)
                                     == i + j - #(n-m)    (m<n)

and maybe        (i * #m * j) div #n == #(m div n) * i * j   (n divides m)

This simproc is needed for cancel_numerals.ML
*)


signature INVERSE_FOLD_DATA =
sig
  (*abstract syntax*)
  val mk_numeral: int -> term
  val dest_numeral: term -> int
  val find_first_numeral: term list -> int * term * term list
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val mk_diff: term * term -> term
  val dest_diff: term -> term * term
  (*rules*)
  val double_diff_eq: thm
  val move_diff_eq: thm
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> term * term -> thm option
  val add_norm_tac: tactic
  val numeral_simp_tac: thm list -> tactic
end;


functor InverseFoldFun(Data: INVERSE_FOLD_DATA): 
		sig
		  val proc: Sign.sg -> thm list -> term -> thm option
		end
=
struct

fun proc sg _ t =
  let val (sum,lit_n) = Data.dest_diff t 
      val terms = Data.dest_sum sum
      val (m, lit_m, terms') = Data.find_first_numeral terms
      val n = Data.dest_numeral lit_n
      and sum' = Data.mk_sum terms'
      val assocs =  (*If needed, rewrite the literal m to the front:
		      i + #m + j + k == #m + i + (j + k) *)
	    [the (Data.prove_conv [Data.add_norm_tac] sg 
		  (sum, Data.mk_sum [lit_m, sum']))]
            handle _ => []
  in
      if m < n then
	    Data.prove_conv 
	     [Data.numeral_simp_tac (Data.double_diff_eq::assocs)] sg
	     (t, Data.mk_diff (sum', Data.mk_numeral (n-m)))
      else (*n < m, since equality would have been cancelled*)
	    Data.prove_conv 
	     [Data.numeral_simp_tac (Data.move_diff_eq::assocs)] sg
	     (t, Data.mk_sum [Data.mk_numeral (m-n), sum'])
  end
  handle _ => None;

end;
