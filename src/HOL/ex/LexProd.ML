(*  Title:      HOL/ex/lex-prod.ML
    ID:         $Id$
    Author:     Tobias Nipkow, TU Munich
    Copyright   1993  TU Munich

For lex-prod.thy.
The lexicographic product of two wellfounded relations is again wellfounded.
*)

val prems = goal Prod.thy "!a b. P((a,b)) ==> !p.P(p)";
by (cut_facts_tac prems 1);
by (rtac allI 1);
by (stac surjective_pairing 1);
by (Fast_tac 1);
qed "split_all_pair";

val [wfa,wfb] = goalw LexProd.thy [wf_def,LexProd.lex_prod_def]
 "[| wf(ra); wf(rb) |] ==> wf(ra**rb)";
by (EVERY1 [rtac allI,rtac impI, rtac split_all_pair]);
by (rtac (wfa RS spec RS mp) 1);
by (EVERY1 [rtac allI,rtac impI]);
by (rtac (wfb RS spec RS mp) 1);
by (fast_tac (!claset addSEs [Pair_inject]) 1);
qed "wf_lex_prod";
