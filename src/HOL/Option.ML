(*  Title:      Option.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen

Derived rules
*)

open Option;

val opt_exhaustion = #nchotomy (the (datatype_info Option.thy "option")) 
                     RS spec;

(*---------------------------------------------------------------------------
 * Do a case analysis on something of type 'a option. 
 *---------------------------------------------------------------------------*)

fun option_case_tac t =
    (cut_inst_tac [("x",t)] opt_exhaustion 
      THEN' etac disjE 
      THEN' rotate_tac ~1 
      THEN' Asm_full_simp_tac 
      THEN' etac exE
      THEN' rotate_tac ~1 
      THEN' Asm_full_simp_tac);


goal Option.thy "P(case opt of None => a | Some(x) => b(x)) = \
\                ((opt = None --> P a) & (!x. opt = Some x --> P(b(x))))";
by (option.induct_tac "opt" 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed"expand_option_case";
