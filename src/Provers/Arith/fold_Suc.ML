(*  Title:      Provers/Arith/fold_Suc.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Simplifies  Suc (i + ... #m + ... j) == #(m+1) + i + ... j
*)


signature FOLD_SUC_DATA =
sig
  (*abstract syntax*)
  val mk_numeral: int -> term
  val find_first_numeral: term list -> int * term * term list
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val dest_Suc: term -> term
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> term * term -> thm option
  val add_norm_tac: tactic
  val numeral_simp_tac: thm list -> tactic
end;


functor FoldSucFun(Data: FOLD_SUC_DATA):
		sig
		  val proc: Sign.sg -> thm list -> term -> thm option
		end
=
struct

fun proc sg _ t =
  let val sum = Data.dest_Suc t 
      val terms = Data.dest_sum sum
      val (m, lit_m, terms') = Data.find_first_numeral terms
      val assocs =  (*If needed, rewrite the literal m to the front:
		     i + #m + j + k == #m + i + (j + k) *)
	  [the (Data.prove_conv [Data.add_norm_tac] sg
		(sum, Data.mk_sum (lit_m::terms')))]
	  handle _ => []
  in
      Data.prove_conv 
        [Data.numeral_simp_tac assocs] sg
	(t, Data.mk_sum (Data.mk_numeral (m+1) :: terms'))
  end
  handle _ => None;

end;
