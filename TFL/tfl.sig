(*  Title:      TFL/tfl
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Main module
*)

signature TFL_sig =
sig

   val trace : bool ref

   val default_simps : thm list      (*simprules used for deriving rules...*)

   val Add_recdef_congs: thm list -> unit
   val Del_recdef_congs: thm list -> unit
   val init: theory -> theory
   val print_recdef_congs: theory -> unit
   val congs : theory -> thm list -> thm list  (*fn to make congruence rules*)

   type pattern

   val mk_functional : theory -> term list
                       -> {functional:term,
                           pats: pattern list}

   val wfrec_definition0 : theory -> string -> term -> term -> theory

   val post_definition : thm list -> theory * (thm * pattern list)
				  -> {theory : theory,
				     rules  : thm,
                                      rows  : int list,
				       TCs  : term list list,
			     full_pats_TCs  : (term * term list) list}

   val wfrec_eqns : theory -> xstring
	             -> thm list (* congruence rules *)
                     -> term list
                     -> {WFR : term,  SV : term list,
                         proto_def : term,
                         extracta :(thm * term list) list,
                         pats  : pattern list}

   val lazyR_def : theory -> xstring
	           -> thm list (* congruence rules *)
                   -> term list
                   -> {theory : theory,
                       rules : thm,
                       R : term, 
                       SV : term list,
                       full_pats_TCs : (term * term list) list, 
                       patterns : pattern list}

   val mk_induction : theory 
                       -> {fconst:term,
                           R : term,
                           SV : term list,
                           pat_TCs_list : (term * term list) list}
                       -> thm

   val postprocess: {WFtac:tactic, terminator:tactic, simplifier:cterm -> thm}
                     -> theory 
                      -> {rules:thm, induction:thm, TCs:term list list}
                       -> {rules:thm, induction:thm, nested_tcs:thm list}
end;
