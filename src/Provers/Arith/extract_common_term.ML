(*  Title:      Provers/Arith/extract_common_term.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Extract common terms in balanced expressions:

     i + u + j ~~ i' + u + j'  ==  u + (i + j) ~~ u + (i' + j')
     i + u     ~~ u            ==  u + i       ~~ u + 0

where ~~ is an appropriate balancing operation (e.g. =, <=, <, -) and 0 is a 
suitable identity for +.

This massaged formula is then simplified in a user-specified way.
*)

signature EXTRACT_COMMON_TERM_DATA =
sig
  (*abstract syntax*)
  val mk_sum: typ -> term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  val find_first: term -> term list -> term list
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> 
                  thm list -> string list -> term * term -> thm option
  val norm_tac: tactic                (*proves the result*)
  val simplify_meta_eq: thm -> thm    (*simplifies the result*)
end;


functor ExtractCommonTermFun(Data: EXTRACT_COMMON_TERM_DATA):
  sig
  val proc: Sign.sg -> thm list -> term -> thm option
  end 
=
struct

(*Store the term t in the table*)
fun update_by_coeff (tab, t) = Termtab.update ((t, ()), tab);

(*a left-to-right scan of terms1, seeking a term u that is also in terms2*)
fun find_common (terms1,terms2) =
  let val tab2 = foldl update_by_coeff (Termtab.empty, terms2)
      fun seek [] = raise TERM("find_common", []) 
	| seek (u::terms) =
	      if is_some (Termtab.lookup (tab2, u)) then u
	      else seek terms
  in  seek terms1 end;

(*the simplification procedure*)
fun proc sg hyps t =
  let (*first freeze any Vars in the term to prevent flex-flex problems*)
      val (t', xs) = Term.adhoc_freeze_vars t;
      val (t1,t2) = Data.dest_bal t' 
      val terms1 = Data.dest_sum t1
      and terms2 = Data.dest_sum t2
      val u = find_common (terms1,terms2)
      val terms1' = Data.find_first u terms1
      and terms2' = Data.find_first u terms2
      and T = Term.fastype_of u
      val reshape = 
	    Data.prove_conv [Data.norm_tac] sg hyps xs
	        (t', 
		 Data.mk_bal (Data.mk_sum T (u::terms1'), 
		              Data.mk_sum T (u::terms2')))
  in
      apsome Data.simplify_meta_eq reshape
  end
  handle TERM _ => None
       | TYPE _ => None;   (*Typically (if thy doesn't include Numeral)
			     Undeclared type constructor "Numeral.bin"*)

end;
