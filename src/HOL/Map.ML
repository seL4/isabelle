(*  Title:      HOL/Map.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen

Map lemmas
*)

goalw thy [empty_def] "empty k = None";
by (Simp_tac 1);
qed "empty_def2";
Addsimps [empty_def2];

goalw thy [update_def] "(m[a|->b])x = (if x=a then Some b else m x)";
by (Simp_tac 1);
qed "update_def2";
Addsimps [update_def2];

section "++";

goalw thy [override_def] "m ++ empty = m";
by (Simp_tac 1);
qed "override_empty";
Addsimps [override_empty];

goalw thy [override_def] "empty ++ m = m";
by (Simp_tac 1);
by (rtac ext 1);
by (split_tac [split_option_case] 1);
by (Simp_tac 1);
qed "empty_override";
Addsimps [empty_override];

goalw thy [override_def]
 "((m ++ n) k = Some x) = (n k = Some x | n k = None & m k = Some x)";
by (simp_tac (simpset() addsplits [split_option_case]) 1);
qed_spec_mp "override_Some_iff";

bind_thm("override_SomeD", standard(override_Some_iff RS iffD1));

goalw thy [override_def]
 "((m ++ n) k = None) = (n k = None & m k = None)";
by (simp_tac (simpset() addsplits [split_option_case]) 1);
qed "override_None";
AddIffs [override_None];

goalw thy [override_def] "map_of(xs@ys) = map_of ys ++ map_of xs";
by (induct_tac "xs" 1);
by (Simp_tac 1);
by (rtac ext 1);
by (asm_simp_tac (simpset() addsplits [expand_if,split_option_case]) 1);
qed "map_of_append";
Addsimps [map_of_append];

section "dom";

goalw thy [dom_def] "dom empty = {}";
by (Simp_tac 1);
qed "dom_empty";
Addsimps [dom_empty];

goalw thy [dom_def] "dom(m[a|->b]) = insert a (dom m)";
by (simp_tac (simpset() addsplits [expand_if]) 1);
by (Blast_tac 1);
qed "dom_update";
Addsimps [dom_update];

goalw thy [dom_def] "dom(m++n) = dom n Un dom m";
by (Blast_tac 1);
qed "dom_override";
Addsimps [dom_override];

section "ran";

goalw thy [ran_def] "ran empty = {}";
by (Simp_tac 1);
qed "ran_empty";
Addsimps [ran_empty];
