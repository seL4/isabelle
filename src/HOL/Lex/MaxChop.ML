(*  Title:      HOL/Lex/MaxChop.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

(* Termination of chop *)

Goalw [reducing_def] "reducing(%qs. maxsplit P ([],qs) [] qs)";
by (asm_full_simp_tac (simpset() addsimps [maxsplit_eq]) 1);
qed "reducing_maxsplit";

val [tc] = chopr.tcs;
goalw_cterm [reducing_def] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop tc));
by (blast_tac (claset() addDs [sym]) 1);
val lemma = result();

val chopr_rule = let val [chopr_rule] = chopr.rules in lemma RS chopr_rule end;

Goalw [chop_def] "reducing splitf ==> \
\ chop splitf xs = (let (pre,post) = splitf xs \
\                   in if pre=[] then ([],xs) \
\                      else let (xss,zs) = chop splitf post \
\                             in (pre#xss,zs))";
by (asm_simp_tac (simpset() addsimps [chopr_rule] addcongs [if_weak_cong]) 1);
by (simp_tac (simpset() addsimps [Let_def] addsplits [split_split]) 1);
qed "chop_rule";

Goalw [is_maxsplitter_def,reducing_def]
 "is_maxsplitter P splitf ==> reducing splitf";
by (Asm_full_simp_tac 1);
qed "is_maxsplitter_reducing";

Goal "is_maxsplitter P splitf ==> \
\ !yss zs. chop splitf xs = (yss,zs) --> xs = concat yss @ zs";
by (res_inst_tac [("xs","xs")] length_induct 1);
by (asm_simp_tac (simpset() delsplits [split_if]
                           addsimps [chop_rule,is_maxsplitter_reducing]
                           addcongs [if_weak_cong]) 1);
by (asm_full_simp_tac (simpset() addsimps [Let_def,is_maxsplitter_def]
                                addsplits [split_split]) 1);
qed_spec_mp "chop_concat";

Goal "is_maxsplitter P splitf ==> \
\ !yss zs. chop splitf xs = (yss,zs) --> (!ys : set yss. ys ~= [])";
by (res_inst_tac [("xs","xs")] length_induct 1);
by (asm_simp_tac (simpset() addsimps [chop_rule,is_maxsplitter_reducing]
                           addcongs [if_weak_cong]) 1);
by (asm_full_simp_tac (simpset() addsimps [Let_def,is_maxsplitter_def]
                                addsplits [split_split]) 1);
by (simp_tac (simpset() addsimps [Let_def,maxsplit_eq]
                       addsplits [split_split]) 1);
by (etac thin_rl 1);
by (strip_tac 1);
by (rtac ballI 1);
by (etac exE 1);
by (etac allE 1);
by Auto_tac;
qed_spec_mp "chop_nonempty";

val [prem] = goalw thy [is_maxchopper_def]
 "is_maxsplitter P splitf ==> is_maxchopper P (chop splitf)";
by (Clarify_tac 1);
by (rtac iffI 1);
 by (rtac conjI 1);
  by (etac (prem RS chop_concat) 1);
 by (rtac conjI 1);
  by (etac (prem RS chop_nonempty) 1);
 by (etac rev_mp 1);
 by (stac (prem RS is_maxsplitter_reducing RS chop_rule) 1);
 by (simp_tac (simpset() addsimps [Let_def,rewrite_rule[is_maxsplitter_def]prem]
                        addsplits [split_split]) 1);
 by (Clarify_tac 1);
 by (rtac conjI 1);
  by (Clarify_tac 1);
 by (Clarify_tac 1);
 by (Asm_full_simp_tac 1);
 by (forward_tac [prem RS chop_concat] 1);
 by (Clarify_tac 1);
by (stac (prem RS is_maxsplitter_reducing RS chop_rule) 1);
by (simp_tac (simpset() addsimps [Let_def,rewrite_rule[is_maxsplitter_def]prem]
                        addsplits [split_split]) 1);
by (Clarify_tac 1);
by (rename_tac "xs1 ys1 xss1 ys" 1);
by (split_asm_tac [list.split_asm] 1);
 by (Asm_full_simp_tac 1);
 by (full_simp_tac (simpset() addsimps [is_maxpref_def]) 1);
 by (blast_tac (claset() addIs [prefix_append RS iffD2]) 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
 by (full_simp_tac (simpset() addsimps [is_maxpref_def]) 1);
 by (blast_tac (claset() addIs [prefix_append RS iffD2]) 1);
by (Clarify_tac 1);
by (rename_tac "us uss" 1);
by (subgoal_tac "xs1=us" 1);
 by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (full_simp_tac (simpset() addsimps [is_maxpref_def]) 1);
by (blast_tac (claset() addIs [prefix_append RS iffD2,prefix_antisym]) 1);
qed "is_maxchopper_chop";
