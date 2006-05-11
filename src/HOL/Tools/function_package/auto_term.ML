(*  Title:      HOL/Tools/function_package/auto_term.ML
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen

A package for general recursive function definitions. 
The auto_term method.
*)


signature FUNDEF_AUTO_TERM =
sig
    val setup : theory -> theory
end

structure FundefAutoTerm : FUNDEF_AUTO_TERM = 
struct

open FundefCommon
open FundefAbbrev



fun auto_term_tac tc_intro_rule relstr wf_rules ss =
    (resolve_tac [tc_intro_rule] 1)                    (* produce the usual goals *)
        THEN (instantiate_tac [("R", relstr)])    (* instantiate with the given relation *)
	THEN (ALLGOALS 
		  (fn 1 => REPEAT (ares_tac wf_rules 1)    (* Solve wellfoundedness *)
		    | i => asm_simp_tac ss i))    (* Simplify termination conditions *)

fun mk_termination_meth relstr ctxt =
    let
	val {simps, congs, wfs} = RecdefPackage.get_local_hints ctxt
	val ss = local_simpset_of ctxt addsimps simps
	    
	val intro_rule = ProofContext.get_thm ctxt (Name "termination_intro")
    in
	Method.RAW_METHOD (K (auto_term_tac
				  intro_rule
				  relstr
				  wfs
				  ss))
    end



val setup = Method.add_methods [("auto_term", Method.simple_args Args.name mk_termination_meth, "termination prover for recdef compatibility")]

end




