(*  Title:      Provers/Arith/abstract_numerals.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Simproc to extend simplification of numeric literals to cover abstract 0 and
1.  For example, in the two-operand case, it eliminates the need to declare
separate rules for the 9 combinations of 0, 1, numeral.  Given a term, it 
replaces all abstract 0s and 1s by the corresponding numerals.  

The resulting equality should immediately be combined with an equation to
force numerical evaluation, since otherwise the literal 0s and 1s will
probably be written back to their abstract forms.
*)

signature ABSTRACT_NUMERALS_DATA =
sig
  (*abstract syntax*)
  val dest_eq: thm -> term * term
  val is_numeral: term -> bool
  (*rules*)
  val numeral_0_eq_0: thm
  val numeral_1_eq_1: thm
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> term * term -> thm option
  val norm_tac: thm list -> tactic    (*proves the initial lemma*)
  val simplify_meta_eq: thm -> thm -> thm    (*simplifies the final theorem*)
end;


(*The returned simproc requires as its first argument a theorem
  of the form f(number_of x, ...) = ...x... *)
functor AbstractNumeralsFun(Data: ABSTRACT_NUMERALS_DATA):
  sig
  val proc: thm -> Sign.sg -> thm list -> term -> thm option
  end 
=
struct

val (numeral0, abstract0) = Data.dest_eq Data.numeral_0_eq_0
val (numeral1, abstract1) = Data.dest_eq Data.numeral_1_eq_1

(*convert abstract numbers to numerals, leave other numerals alone,
  reject other terms*)
fun convert x =
    if Data.is_numeral x then x
    else if x = abstract0 then numeral0
    else if x = abstract1 then numeral1
    else raise TERM("abstract_numerals", []) ;

(*the simplification procedure*)
fun proc f_number_of_eq sg _ t =
  let val (f,args) = strip_comb t
      val t' = list_comb(f, map convert args)
  in
      if t aconv t' then   (*trivial, so do nothing*)
	 raise TERM("abstract_numerals", []) 
      else 
      apsome (Data.simplify_meta_eq f_number_of_eq)
	 (Data.prove_conv 
           [Data.norm_tac [Data.numeral_0_eq_0, Data.numeral_1_eq_1]] sg
                          (t, t'))
  end
  handle TERM _ => None
       | TYPE _ => None;   (*Typically (if thy doesn't include Numeral)
			     Undeclared type constructor "Numeral.bin"*)

end;
