(*  Title:      Provers/Arith/assoc_fold.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Simplification procedure for associative operators + and * on numeric types

Performs constant folding when the literals are separated, as in 3+n+4.
*)


signature ASSOC_FOLD_DATA =
sig
  val ss		: simpset	(*basic simpset of object-logtic*)
  val eq_reflection	: thm		(*object-equality to meta-equality*)
  val sg_ref 		: Sign.sg_ref	(*the operator's signature*)
  val T			: typ		(*the operator's numeric type*)
  val plus		: term		(*the operator being folded*)
  val add_ac		: thm list      (*AC-rewrites for plus*)
end;


functor Assoc_Fold (Data: ASSOC_FOLD_DATA) =
struct

 val assoc_ss = Data.ss addsimps Data.add_ac;

 (*prove while suppressing timing information*)
 fun prove name ct tacf = 
     setmp Library.timing false (prove_goalw_cterm [] ct) tacf
     handle ERROR =>
	 error(name ^ " simproc:\nfailed to prove " ^ string_of_cterm ct);
                
 exception Assoc_fail;

 fun mk_sum []  = raise Assoc_fail
   | mk_sum tms = foldr1 (fn (x,y) => Data.plus $ x $ y) tms;

 (*Separate the literals from the other terms being combined*)
 fun sift_terms (t, (lits,others)) =
     case t of
	  Const("Numeral.number_of", _) $ _ =>
	      (t::lits, others)         (*new literal*)
	| (f as Const _) $ x $ y =>
	      if f = Data.plus 
              then sift_terms (x, sift_terms (y, (lits,others)))
	      else (lits, t::others)    (*arbitrary summand*)
	| _ => (lits, t::others);

 val trace = ref false;

 (*Make a simproc to combine all literals in a associative nest*)
 fun proc sg _ lhs =
   let fun show t = string_of_cterm (Thm.cterm_of sg t)
       val _ = if !trace then tracing ("assoc_fold simproc: LHS = " ^ show lhs)
	       else ()
       val (lits,others) = sift_terms (lhs, ([],[]))
       val _ = if length lits < 2
               then raise Assoc_fail (*we can't reduce the number of terms*)
               else ()  
       val rhs = Data.plus $ mk_sum lits $ mk_sum others
       val _ = if !trace then tracing ("RHS = " ^ show rhs) else ()
       val th = prove "assoc_fold" 
	           (Thm.cterm_of sg (Logic.mk_equals (lhs, rhs)))
		   (fn _ => [rtac Data.eq_reflection 1,
			     simp_tac assoc_ss 1])
   in Some th end
   handle Assoc_fail => None;
 
 val conv = 
     Simplifier.mk_simproc "assoc_fold"
       [Thm.cterm_of (Sign.deref Data.sg_ref)
	             (Data.plus $ Free("x",Data.T) $ Free("y",Data.T))]
       proc;

end;


(*test data:
set timing;

Goal "(#3 * (a * #34)) * (#2 * b * #9) = (x::int)";

Goal "a + b + c + d + e + f + g + h + i + j + k + l + m + n + oo + p + q + r + s + t + u + v + (w + x + y + z + a + #2 + b + #2 + c + #2 + d + #2 + e) + #2 + f + (#2 + g + #2 + h + #2 + i) + #2 + (j + #2 + k + #2 + l + #2 + m + #2) + n + #2 + (oo + #2 + p + #2 + q + #2 + r) + #2 + s + #2 + t + #2 + u + #2 + v + #2 + w + #2 + x + #2 + y + #2 + z + #2 = (uu::nat)";
*)
