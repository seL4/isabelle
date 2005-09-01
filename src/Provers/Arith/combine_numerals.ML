(*  Title:      Provers/Arith/combine_numerals.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Combine coefficients in expressions:

     i + #m*u + j ... + #n*u + k  ==  #(m+n)*u + (i + (j + k))

It works by (a) massaging the sum to bring the selected terms to the front:

     #m*u + (#n*u + (i + (j + k)))

(b) then using left_distrib to reach

     #(m+n)*u + (i + (j + k))
*)

signature COMBINE_NUMERALS_DATA =
sig
  (*abstract syntax*)
  val add: IntInf.int * IntInf.int -> IntInf.int     (*addition (or multiplication) *)
  val mk_sum: typ -> term list -> term
  val dest_sum: term -> term list
  val mk_coeff: IntInf.int * term -> term
  val dest_coeff: term -> IntInf.int * term
  (*rules*)
  val left_distrib: thm
  (*proof tools*)
  val prove_conv: tactic list -> theory -> string list -> term * term -> thm option
  val trans_tac: simpset -> thm option -> tactic (*applies the initial lemma*)
  val norm_tac: simpset -> tactic                (*proves the initial lemma*)
  val numeral_simp_tac: simpset -> tactic        (*proves the final theorem*)
  val simplify_meta_eq: simpset -> thm -> thm    (*simplifies the final theorem*)
end;


functor CombineNumeralsFun(Data: COMBINE_NUMERALS_DATA):
  sig
  val proc: theory -> simpset -> term -> thm option
  end 
=
struct

(*Remove the first occurrence of #m*u from the term list*)
fun remove (_, _, []) = (*impossible, since #m*u was found by find_repeated*)
      raise TERM("combine_numerals: remove", [])  
  | remove (m, u, t::terms) =
      case try Data.dest_coeff t of
	  SOME(n,v) => if m=n andalso u aconv v then terms
		       else t :: remove (m, u, terms)
	| NONE      =>  t :: remove (m, u, terms);

(*a left-to-right scan of terms, seeking another term of the form #n*u, where
  #m*u is already in terms for some m*)
fun find_repeated (tab, _, []) = raise TERM("find_repeated", []) 
  | find_repeated (tab, past, t::terms) =
      case try Data.dest_coeff t of
	  SOME(n,u) => 
	      (case Termtab.curried_lookup tab u of
		  SOME m => (u, m, n, rev (remove (m,u,past)) @ terms)
		| NONE => find_repeated (Termtab.curried_update (u, n) tab, 
					 t::past,  terms))
	| NONE => find_repeated (tab, t::past, terms);

(*the simplification procedure*)
fun proc thy ss t =
  let (*first freeze any Vars in the term to prevent flex-flex problems*)
      val (t', xs) = Term.adhoc_freeze_vars t
      val (u,m,n,terms) = find_repeated (Termtab.empty, [], Data.dest_sum t')
      val T = Term.fastype_of u
      val reshape =  (*Move i*u to the front and put j*u into standard form
		       i + #m + j + k == #m + i + (j + k) *)
	    if m=0 orelse n=0 then   (*trivial, so do nothing*)
		raise TERM("combine_numerals", []) 
	    else Data.prove_conv [Data.norm_tac ss] thy xs
			(t', 
			 Data.mk_sum T ([Data.mk_coeff(m,u),
				         Data.mk_coeff(n,u)] @ terms))
  in
      Option.map (Data.simplify_meta_eq ss)
	 (Data.prove_conv 
	    [Data.trans_tac ss reshape, rtac Data.left_distrib 1,
	     Data.numeral_simp_tac ss] thy xs
	    (t', Data.mk_sum T (Data.mk_coeff(Data.add(m,n), u) :: terms)))
  end
  handle TERM _ => NONE
       | TYPE _ => NONE;   (*Typically (if thy doesn't include Numeral)
			     Undeclared type constructor "Numeral.bin"*)

end;
