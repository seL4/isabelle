(*  Title:      Provers/Arith/combine_coeff.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

Simplification procedure to combine literal coefficients in sums of products

Example, #3*x + y - (x*#2) goes to x + y

For the relations <, <= and =, the difference is simplified

[COULD BE GENERALIZED to products of exponentials?]
*)

signature COMBINE_COEFF_DATA =
sig
  val ss		: simpset	(*basic simpset of object-logtic*)
  val eq_reflection	: thm		(*object-equality to meta-equality*)
  val thy		: theory	(*the theory of the group*)
  val T			: typ		(*the type of group elements*)

  val trans             : thm           (*transitivity of equals*)
  val add_ac		: thm list      (*AC-rules for the addition operator*)
  val diff_def		: thm		(*Defines x-y as x + -y *)
  val minus_add_distrib	: thm           (* -(x+y) = -x + -y *)        
  val minus_minus	: thm           (* - -x = x *)
  val mult_commute 	: thm		(*commutative law for the product*)
  val mult_1_right 	: thm           (*the law x*1=x *)
  val add_mult_distrib  : thm           (*law w*(x+y) = w*x + w*y *)
  val diff_mult_distrib : thm           (*law w*(x-y) = w*x - w*y *)
  val mult_minus_right  : thm           (*law x * -y = -(x*y) *)

  val rel_iff_rel_0_rls : thm list      (*e.g. (x < y) = (x-y < 0) *)
  val dest_eqI		: thm -> term   (*to get patterns from the rel rules*)
end;


functor Combine_Coeff (Data: COMBINE_COEFF_DATA) =
struct

 local open Data 
 in
 val rhs_ss = ss addsimps
                    [add_mult_distrib, diff_mult_distrib,
		     mult_minus_right, mult_1_right];

 val lhs_ss = ss addsimps
		 add_ac @
		 [diff_def, minus_add_distrib, minus_minus, mult_commute];
 end;

 (*prove while suppressing timing information*)
 fun prove name ct tacf = 
     setmp Goals.proof_timing false (prove_goalw_cterm [] ct) tacf
     handle ERROR =>
	 error(name ^ " simproc:\nfailed to prove " ^ string_of_cterm ct);
                
 val plus = Const ("op +", [Data.T,Data.T] ---> Data.T);
 val minus = Const ("op -", [Data.T,Data.T] ---> Data.T);
 val uminus = Const ("uminus", Data.T --> Data.T);
 val times = Const ("op *", [Data.T,Data.T] ---> Data.T);

 val number_of = Const ("Numeral.number_of", 
			Type ("Numeral.bin", []) --> Data.T);

 val zero = number_of $ HOLogic.pls_const;
 val one =  number_of $ (HOLogic.bit_const $ 
			 HOLogic.pls_const $ 
			 HOLogic.true_const);

 (*We map -t to t and (in other cases) t to -t.  No need to check the type of
   uminus, since the simproc is only called on sums of type T.*)
 fun negate (Const("uminus",_) $ t) = t
   | negate t                       = uminus $ t;

 fun mk_sum []  = zero
   | mk_sum tms = foldr1 (fn (x,y) => plus $ x $ y) tms;

 fun attach_coeff (Bound ~1,ns) = mk_sum ns  (*just a literal*)
   | attach_coeff (x,ns) = times $ x $ (mk_sum ns);

 fun add_atom (x, (neg,m)) pairs = 
   let val m' = if neg then negate m else m
   in 
       case gen_assoc (op aconv) (pairs, x) of
	   Some n => gen_overwrite (op aconv) (pairs, (x, m'::n))
	 | None => (x,[m']) :: pairs
   end;

 (**STILL MISSING: a treatment of nested coeffs, e.g. a*(b*3) **)
 (*Convert a formula built from +, * and - (binary and unary) to a
   (atom, coeff) association list.  Handles t+t, t-t, -t, a*n, n*a, n, a
   where n denotes a numeric literal and a is any other term.
   No need to check types PROVIDED they are checked upon entry!*)
 fun add_terms neg (Const("op +", _) $ x $ y, pairs) =
	 add_terms neg (x, add_terms neg (y, pairs))
   | add_terms neg (Const("op -", _) $ x $ y, pairs) =
	 add_terms neg (x, add_terms (not neg) (y, pairs))
   | add_terms neg (Const("uminus", _) $ x, pairs) = 
	 add_terms (not neg) (x, pairs)
   | add_terms neg (lit as Const("Numeral.number_of", _) $ _, pairs) =
	 (*literal: make it the coefficient of a dummy term*)
	 add_atom (Bound ~1, (neg, lit)) pairs
   | add_terms neg (Const("op *", _) $ x 
		             $ (lit as Const("Numeral.number_of", _) $ _),
		    pairs) =
	 (*coefficient on the right*)
	 add_atom (x, (neg, lit)) pairs
   | add_terms neg (Const("op *", _) 
		             $ (lit as Const("Numeral.number_of", _) $ _)
                             $ x, pairs) =
	 (*coefficient on the left*)
	 add_atom (x, (neg, lit)) pairs
   | add_terms neg (x, pairs) = add_atom (x, (neg, one)) pairs;

 fun terms fml = add_terms false (fml, []);

 exception CC_fail;

 (*The number of terms in t, assuming no collapsing takes place*)
 fun term_count (Const("op +", _) $ x $ y) = term_count x + term_count y
   | term_count (Const("op -", _) $ x $ y) = term_count x + term_count y
   | term_count (Const("uminus", _) $ x) = term_count x
   | term_count x = 1;


 val trace = ref false;

 (*The simproc for sums*)
 fun sum_proc sg _ lhs =
   let fun show t = string_of_cterm (Thm.cterm_of sg t)
       val _ = if !trace then writeln 
	                   ("combine_coeff sum simproc: LHS = " ^ show lhs)
	       else ()
       val ts = terms lhs
       val _ = if term_count lhs = length ts 
               then raise CC_fail (*we can't reduce the number of terms*)
               else ()  
       val rhs = mk_sum (map attach_coeff ts)
       val _ = if !trace then writeln ("RHS = " ^ show rhs) else ()
       val th = prove "combine_coeff" 
	           (Thm.cterm_of sg (Logic.mk_equals (lhs, rhs)))
		   (fn _ => [rtac Data.eq_reflection 1,
			     simp_tac rhs_ss 1,
			     IF_UNSOLVED (simp_tac lhs_ss 1)])
   in Some th end
   handle CC_fail => None;

 val sum_conv = 
     Simplifier.mk_simproc "combine_coeff_sums"
       (map (Thm.read_cterm (Theory.sign_of Data.thy)) 
	[("x + y", Data.T), ("x - y", Data.T)])
       sum_proc;


 (*The simproc for relations, which just replaces x<y by x-y<0 and simplifies*)

 val trans_eq_reflection = Data.trans RS Data.eq_reflection |> standard;

 fun rel_proc sg asms (lhs as (rel$lt$rt)) =
   let val _ = if !trace then writeln
                               ("cc_rel simproc: LHS = " ^ 
				string_of_cterm (cterm_of sg lhs))
	       else ()
       val _ = if lt=zero orelse rt=zero then raise CC_fail 
               else ()   (*this simproc can do nothing if either side is zero*)
       val cc_th = the (sum_proc sg asms (minus $ lt $ rt))
                   handle OPTION => raise CC_fail
       val _ = if !trace then 
		 writeln ("cc_th = " ^ string_of_thm cc_th)
	       else ()
       val cc_lr = #2 (Logic.dest_equals (concl_of cc_th))

       val rhs = rel $ cc_lr $ zero
       val _ = if !trace then 
		 writeln ("RHS = " ^ string_of_cterm (Thm.cterm_of sg rhs))
	       else ()
       val ct = Thm.cterm_of sg (Logic.mk_equals (lhs,rhs))

       val th = prove "cc_rel" ct 
                  (fn _ => [rtac trans_eq_reflection 1,
			    resolve_tac Data.rel_iff_rel_0_rls 1,
			    simp_tac (Data.ss addsimps [cc_th]) 1])
   in Some th end
   handle CC_fail => None;

 val rel_conv = 
     Simplifier.mk_simproc "cc_relations"
       (map (Thm.cterm_of (Theory.sign_of Data.thy) o Data.dest_eqI)
            Data.rel_iff_rel_0_rls)
       rel_proc;

end;
