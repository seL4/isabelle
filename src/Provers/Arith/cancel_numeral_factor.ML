(*  Title:      Provers/Arith/cancel_numeral_factor.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Cancel common coefficients in balanced expressions:

     u*#m ~~ u'*#m'  ==  #n*u ~~ #n'*u'

where ~~ is an appropriate balancing operation (e.g. =, <=, <, div, /)
and d = gcd(m,m') and n=m/d and n'=m'/d.

It works by (a) massaging both sides to bring gcd(m,m') to the front:

     u*#m ~~ u'*#m'  ==  #d*(#n*u) ~~ #d*(#n'*u')

(b) then using the rule "cancel" to reach #n*u ~~ #n'*u'.
*)

signature CANCEL_NUMERAL_FACTOR_DATA =
sig
  (*abstract syntax*)
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  val mk_coeff: int * term -> term
  val dest_coeff: term -> int * term
  (*rules*)
  val cancel: thm
  val neg_exchanges: bool  (*true if a negative coeff swaps the two operands,
                             as with < and <= but not = and div*)
  (*proof tools*)
  val prove_conv: tactic list -> Proof.context -> thm list -> term * term -> thm option
  val trans_tac: simpset -> thm option -> tactic (*applies the initial lemma*)
  val norm_tac: simpset -> tactic                (*proves the initial lemma*)
  val numeral_simp_tac: simpset -> tactic        (*proves the final theorem*)
  val simplify_meta_eq: simpset -> thm -> thm    (*simplifies the final theorem*)
end;


functor CancelNumeralFactorFun(Data: CANCEL_NUMERAL_FACTOR_DATA):
  sig
  val proc: simpset -> term -> thm option
  end
=
struct

(*the simplification procedure*)
fun proc ss t =
  let
    val ctxt = Simplifier.the_context ss;
    val prems = prems_of_ss ss;
    val ([t'], ctxt') = Variable.import_terms true [t] ctxt
    val export = singleton (Variable.export ctxt' ctxt)

    val (t1,t2) = Data.dest_bal t'
    val (m1, t1') = Data.dest_coeff t1
    and (m2, t2') = Data.dest_coeff t2
    val d = (*if both are negative, also divide through by ~1*)
      if (m1<0 andalso m2<=0) orelse
         (m1<=0 andalso m2<0) then ~ (abs (Integer.gcd m1 m2)) else abs (Integer.gcd m1 m2)
    val _ = if d=1 then   (*trivial, so do nothing*)
              raise TERM("cancel_numeral_factor", [])
            else ()
    fun newshape (i,t) = Data.mk_coeff(d, Data.mk_coeff(i,t))
    val n1 = m1 div d and n2 = m2 div d
    val rhs = if d<0 andalso Data.neg_exchanges
              then Data.mk_bal (Data.mk_coeff(n2,t2'), Data.mk_coeff(n1,t1'))
              else Data.mk_bal (Data.mk_coeff(n1,t1'), Data.mk_coeff(n2,t2'))
    val reshape =  (*Move d to the front and put the rest into standard form
                       i * #m * j == #d * (#n * (j * k)) *)
      Data.prove_conv [Data.norm_tac ss] ctxt prems
        (t', Data.mk_bal (newshape(n1,t1'), newshape(n2,t2')))
  in
    Option.map (export o Data.simplify_meta_eq ss)
      (Data.prove_conv
         [Data.trans_tac ss reshape, rtac Data.cancel 1,
          Data.numeral_simp_tac ss] ctxt prems (t', rhs))
  end
  (* FIXME avoid handling of generic exceptions *)
  handle TERM _ => NONE
       | TYPE _ => NONE;   (*Typically (if thy doesn't include Numeral)
                             Undeclared type constructor "Numeral.bin"*)

end;
