(*  Title:      Provers/Arith/cancel_numerals.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Cancel common coefficients in balanced expressions:

     i + #m*u + j ~~ i' + #m'*u + j'  ==  #(m-m')*u + i + j ~~ i' + j'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, -).

It works by (a) massaging both sides to bring the selected term to the front:

     #m*u + (i + j) ~~ #m'*u + (i' + j') 

(b) then using bal_add1 or bal_add2 to reach

     #(m-m')*u + i + j ~~ i' + j'       (if m'<=m)

or

     i + j ~~ #(m'-m)*u + i' + j'       (otherwise)
*)

signature CANCEL_NUMERALS_DATA =
sig
  (*abstract syntax*)
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  val mk_coeff: int * term -> term
  val dest_coeff: term -> int * term
  val find_first_coeff: term -> term list -> int * term list
  (*rules*)
  val bal_add1: thm
  val bal_add2: thm
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> term * term -> thm option
  val norm_tac: tactic
  val numeral_simp_tac: tactic
end;


functor CancelNumeralsFun(Data: CANCEL_NUMERALS_DATA):
  sig
  val proc: Sign.sg -> thm list -> term -> thm option
  end 
=
struct

fun listof None = []
  | listof (Some x) = [x];

(*If t = #n*u then put u in the table*)
fun update_by_coeff (tab, t) =
  Termtab.update ((#2 (Data.dest_coeff t), ()), tab)
  handle TERM _ => tab;

(*a left-to-right scan of terms1, seeking a term of the form #n*u, where
  #m*u is in terms2 for some m*)
fun find_common (terms1,terms2) =
  let val tab2 = foldl update_by_coeff (Termtab.empty, terms2)
      fun seek [] = raise TERM("find_common", []) 
	| seek (t::terms) =
	      let val (_,u) = Data.dest_coeff t 
	      in  if is_some (Termtab.lookup (tab2, u)) then u
		  else seek terms
	      end
	      handle TERM _ => seek terms
  in  seek terms1 end;

(*the simplification procedure*)
fun proc sg _ t =
  let val (t1,t2) = Data.dest_bal t 
      val terms1 = Data.dest_sum t1
      and terms2 = Data.dest_sum t2
      val u = find_common (terms1,terms2)
      val (n1, terms1') = Data.find_first_coeff u terms1
      and (n2, terms2') = Data.find_first_coeff u terms2
      fun newshape (i,terms) = Data.mk_sum (Data.mk_coeff(i,u)::terms)
      val reshapes =  (*Move i*u to the front and put j*u into standard form
		      i + #m + j + k == #m + i + (j + k) *)
	    listof (Data.prove_conv [Data.norm_tac] sg 
		    (t, 
		     Data.mk_bal (newshape(n1,terms1'), 
				  newshape(n2,terms2'))))
  in

      if n2<=n1 then 
	  Data.prove_conv 
	     [rewrite_goals_tac reshapes, rtac Data.bal_add1 1,
	      Data.numeral_simp_tac] sg
	     (t, Data.mk_bal (newshape(n1-n2,terms1'), Data.mk_sum terms2'))
      else
	  Data.prove_conv 
	     [rewrite_goals_tac reshapes, rtac Data.bal_add2 1,
	      Data.numeral_simp_tac] sg
	     (t, Data.mk_bal (Data.mk_sum terms1', newshape(n2-n1,terms2')))
  end
  handle TERM _ => None;

end;
