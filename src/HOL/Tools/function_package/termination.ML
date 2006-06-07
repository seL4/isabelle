(*  Title:      HOL/Tools/function_package/termination.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
Termination goals...
*)


signature FUNDEF_TERMINATION =
sig
    val mk_total_termination_goal : FundefCommon.result_with_names -> term
    val mk_partial_termination_goal : theory -> FundefCommon.result_with_names -> string -> term * term
end

structure FundefTermination : FUNDEF_TERMINATION =
struct


open FundefCommon
open FundefAbbrev

fun mk_total_termination_goal (FundefMResult {R, f, ... }, _, _, _) =
    let
	val domT = domain_type (fastype_of f)
	val x = Free ("x", domT)
    in
	Trueprop (mk_mem (x, Const (acc_const_name, fastype_of R --> HOLogic.mk_setT domT) $ R))
    end

fun mk_partial_termination_goal thy (FundefMResult {R, f, ... }, _, _, _) dom =
    let
	val domT = domain_type (fastype_of f)
	val D = Sign.simple_read_term thy (Logic.varifyT (HOLogic.mk_setT domT)) dom
	val DT = type_of D
	val idomT = HOLogic.dest_setT DT

	val x = Free ("x", idomT)
	val z = Free ("z", idomT)
	val Rname = fst (dest_Const R)
	val iRT = mk_relT (idomT, idomT)
	val iR = Const (Rname, iRT)
		

	val subs = HOLogic.mk_Trueprop 
			 (Const ("Orderings.less_eq", DT --> DT --> boolT) $ D $
				(Const (acc_const_name, iRT --> DT) $ iR))
			 |> Type.freeze

	val dcl = mk_forall x
			    (mk_forall z (Logic.mk_implies (Trueprop (HOLogic.mk_mem (x, D)),
							    Logic.mk_implies (mk_relmem (z, x) iR,
									      Trueprop (mk_mem (z, D))))))
			    |> Type.freeze
    in
	(subs, dcl)
    end

end




