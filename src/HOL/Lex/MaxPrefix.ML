(*  Title:      HOL/Lex/MaxPrefix.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

Delsplits [expand_if];
goalw thy [is_maxpref_def] "!(ps::'a list) res. \
\ (maxsplit P ps qs res = (xs,ys)) = \
\ (if (? us. us <= qs & P(ps@us)) then xs@ys=ps@qs & is_maxpref P xs (ps@qs) \
\  else (xs,ys)=res)";
by(induct_tac "qs" 1);
 by(simp_tac (simpset() addsplits [expand_if]) 1);
 by(Blast_tac 1);
by(Asm_simp_tac 1);
be thin_rl 1;
by(Clarify_tac 1);
by(case_tac "? us. us <= list & P (ps @ a # us)" 1);
 by(Asm_simp_tac 1);
 by(subgoal_tac "? us. us <= a # list & P (ps @ us)" 1);
  by(Asm_simp_tac 1);
 by(blast_tac (claset() addIs [prefix_Cons RS iffD2]) 1);
by(subgoal_tac "~P(ps@[a])" 1);
 by(Blast_tac 2);
by(Asm_simp_tac 1);
by(case_tac "? us. us <= a#list & P (ps @ us)" 1);
 by(Asm_simp_tac 1);
 by(Clarify_tac 1);
 by(exhaust_tac "us" 1);
  br iffI 1;
   by(asm_full_simp_tac (simpset() addsimps [prefix_Cons,prefix_append]) 1);
   by(Blast_tac 1);
  by(asm_full_simp_tac (simpset() addsimps [prefix_Cons,prefix_append]) 1);
  by(Clarify_tac 1);
  be disjE 1;
   by(fast_tac (claset() addDs [prefix_antisym]) 1);
  by(Clarify_tac 1);
  be disjE 1;
   by(Clarify_tac 1);
   by(Asm_full_simp_tac 1);
  be disjE 1;
   by(Clarify_tac 1);
   by(Asm_full_simp_tac 1);
  by(Blast_tac 1);
 by(Asm_full_simp_tac 1);
by(subgoal_tac "~P(ps)" 1);
by(Asm_simp_tac 1);
by(fast_tac (claset() addss simpset()) 1);
qed_spec_mp "maxsplit_lemma";
Addsplits [expand_if];

goalw thy [is_maxpref_def]
 "!!P. ~(? us. us<=xs & P us) ==> is_maxpref P ps xs = (ps = [])";
by(Blast_tac 1);
qed "is_maxpref_Nil";
Addsimps [is_maxpref_Nil];

goalw thy [is_maxsplitter_def]
 "is_maxsplitter P (%xs. maxsplit P [] xs ([],xs))";
by(simp_tac (simpset() addsimps [maxsplit_lemma]) 1);
by(fast_tac (claset() addss simpset()) 1);
qed "is_maxsplitter_maxsplit";

val maxsplit_eq = rewrite_rule [is_maxsplitter_def] is_maxsplitter_maxsplit;
