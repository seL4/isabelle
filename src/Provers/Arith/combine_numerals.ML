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
  val mk_sum: term list -> term
  val dest_sum: term -> term list
  val mk_coeff: int * term -> term
  val dest_coeff: term -> int * term
  (*rules*)
  val left_distrib: thm
  (*proof tools*)
  val prove_conv: tactic list -> Sign.sg -> term * term -> thm option
  val trans_tac: thm option -> tactic (*applies the initial lemma*)
  val norm_tac: tactic                (*proves the initial lemma*)
  val numeral_simp_tac: tactic        (*proves the final theorem*)
  val simplify_meta_eq: thm -> thm    (*simplifies the final theorem*)
end;


functor CombineNumeralsFun(Data: COMBINE_NUMERALS_DATA):
  sig
  val proc: Sign.sg -> thm list -> term -> thm option
  end 
=
struct

(*Remove the first occurrence of #m*u from the term list*)
fun remove (_, _, []) = (*impossible, since #m*u was found by find_repeated*)
      raise TERM("combine_numerals: remove", [])  
  | remove (m, u, t::terms) =
      let val (n,v) = Data.dest_coeff t 
      in  if m=n andalso u aconv v then terms
          else t :: remove (m, u, terms)
      end;

(*a left-to-right scan of terms, seeking another term of the form #n*u, where
  #m*u is already in terms for some m*)
fun find_repeated (tab, _, []) = raise TERM("find_repeated", []) 
  | find_repeated (tab, past, t::terms) =
      let val (n,u) = Data.dest_coeff t 
      in  
	  case Termtab.lookup (tab, u) of
	      Some m => (u, m, n, rev (remove (m,u,past)) @ terms)
	    | None => find_repeated (Termtab.update ((u,n), tab), 
				     t::past,  terms)
      end;

(*the simplification procedure*)
fun proc sg _ t =
  let (*first freeze any Vars in the term to prevent flex-flex problems*)
      val rand_s = gensym"_"
      fun mk_inst (var as Var((a,i),T))  = 
	    (var,  Free((a ^ rand_s ^ string_of_int i), T))
      val t' = subst_atomic (map mk_inst (term_vars t)) t
      val (u,m,n,terms) = find_repeated (Termtab.empty, [], Data.dest_sum t')
      val reshape =  (*Move i*u to the front and put j*u into standard form
		       i + #m + j + k == #m + i + (j + k) *)
	    if m=0 orelse n=0 then   (*trivial, so do nothing*)
		raise TERM("combine_numerals", []) 
	    else Data.prove_conv [Data.norm_tac] sg 
			(t', 
			 Data.mk_sum ([Data.mk_coeff(m,u),
				       Data.mk_coeff(n,u)] @ terms))
  in
      apsome Data.simplify_meta_eq
	 (Data.prove_conv 
	    [Data.trans_tac reshape, rtac Data.left_distrib 1,
	     Data.numeral_simp_tac] sg
	    (t', Data.mk_sum (Data.mk_coeff(m+n,u) :: terms)))
  end
  handle TERM _ => None
       | TYPE _ => None;   (*Typically (if thy doesn't include Numeral)
			     Undeclared type constructor "Numeral.bin"*)

end;
