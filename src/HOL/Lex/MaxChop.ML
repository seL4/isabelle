(*  Title:      HOL/Lex/MaxChop.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

(* Termination of chop *)

goalw thy [reducing_def] "reducing(%qs. maxsplit P ([],qs) [] qs)";
by(asm_full_simp_tac (simpset() addsimps [maxsplit_eq]) 1);
qed "reducing_maxsplit";

val [tc] = chopr.tcs;
goalw_cterm [reducing_def] (cterm_of (sign_of thy) (HOLogic.mk_Trueprop tc));
by(blast_tac (claset() addDs [sym]) 1);
val lemma = result();

val chopr_rule = let val [chopr_rule] = chopr.rules in lemma RS chopr_rule end;

goalw thy [chop_def] "!!splitf. reducing splitf ==> \
\ chop splitf xs = (let (pre,post) = splitf xs \
\                   in if pre=[] then ([],xs) \
\                      else let (xss,zs) = chop splitf post \
\                             in (pre#xss,zs))";
by(asm_simp_tac (simpset() addsimps [chopr_rule] addcongs [if_weak_cong]) 1);
by(simp_tac (simpset() addsimps [Let_def] addsplits [split_split]) 1);
qed "chop_rule";

goalw thy [is_maxsplitter_def,reducing_def]
 "!!splitf. is_maxsplitter P splitf ==> reducing splitf";
by(Asm_full_simp_tac 1);
qed "is_maxsplitter_reducing";

goal thy "!!P. is_maxsplitter P splitf ==> \
\ !yss zs. chop splitf xs = (yss,zs) --> xs = concat yss @ zs";
by(res_inst_tac [("xs","xs")] length_induct 1);
by(asm_simp_tac (simpset() delsplits [split_if]
                           addsimps [chop_rule,is_maxsplitter_reducing]
                           addcongs [if_weak_cong]) 1);
by(asm_full_simp_tac (simpset() addsimps [Let_def,is_maxsplitter_def]
                                addsplits [split_split]) 1);
qed_spec_mp "chop_concat";

goal thy "!!P. is_maxsplitter P splitf ==> \
\ !yss zs. chop splitf xs = (yss,zs) --> (!ys : set yss. ys ~= [])";
by(res_inst_tac [("xs","xs")] length_induct 1);
by(asm_simp_tac (simpset() addsimps [chop_rule,is_maxsplitter_reducing]
                           addcongs [if_weak_cong]) 1);
by(asm_full_simp_tac (simpset() addsimps [Let_def,is_maxsplitter_def]
                                addsplits [split_split]) 1);
by(simp_tac (simpset() addsimps [Let_def,maxsplit_eq]
                       addsplits [split_split]) 1);
be thin_rl 1;
by(strip_tac 1);
br ballI 1;
be exE 1;
be allE 1;
auto();
qed_spec_mp "chop_nonempty";

val [prem] = goalw thy [is_maxchopper_def]
 "is_maxsplitter P splitf ==> is_maxchopper P (chop splitf)";
by(Clarify_tac 1);
br iffI 1;
 br conjI 1;
  be (prem RS chop_concat) 1;
 br conjI 1;
  be (prem RS chop_nonempty) 1;
 be rev_mp 1;
 by(stac (prem RS is_maxsplitter_reducing RS chop_rule) 1);
 by(simp_tac (simpset() addsimps [Let_def,rewrite_rule[is_maxsplitter_def]prem]
                        addsplits [split_split]) 1);
 by(Clarify_tac 1);
 br conjI 1;
  by(Clarify_tac 1);
  by(Asm_full_simp_tac 1);
 by(Clarify_tac 1);
 by(Asm_full_simp_tac 1);
 by(forward_tac [prem RS chop_concat] 1);
 by(Clarify_tac 1);
 ba 1;
by(stac (prem RS is_maxsplitter_reducing RS chop_rule) 1);
 by(simp_tac (simpset() addsimps [Let_def,rewrite_rule[is_maxsplitter_def]prem]
                        addsplits [split_split]) 1);
by(Clarify_tac 1);
br conjI 1;
 by(Clarify_tac 1);
 by(exhaust_tac "yss" 1);
  by(Asm_simp_tac 1);
 by(Asm_full_simp_tac 1);
 by(full_simp_tac (simpset() addsimps [is_maxpref_def]) 1);
 by(blast_tac (claset() addIs [prefix_append RS iffD2]) 1);
by(exhaust_tac "yss" 1);
 by(Asm_full_simp_tac 1);
 by(full_simp_tac (simpset() addsimps [is_maxpref_def]) 1);
 by(blast_tac (claset() addIs [prefix_append RS iffD2]) 1);
by(Clarify_tac 1);
by(Asm_full_simp_tac 1);
by(subgoal_tac "x=a" 1);
 by(Clarify_tac 1);
 by(Asm_full_simp_tac 1);
by(rotate_tac ~2 1);
by(Asm_full_simp_tac 1);
by(full_simp_tac (simpset() addsimps [is_maxpref_def]) 1);
by(blast_tac (claset() addIs [prefix_append RS iffD2,prefix_antisym]) 1);
qed "is_maxchopper_chop";
