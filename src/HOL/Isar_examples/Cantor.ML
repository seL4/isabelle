
(* tactic script -- single steps *)

Goal "EX S. S ~: range(f :: 'a => 'a set)";
  br exI 1;
  br notI 1;
  be rangeE 1;
  be equalityCE 1;
  bd CollectD 1;
  by (contr_tac 1);
  by (swap_res_tac [CollectI] 1);
  ba 1;
qed "it";


(* tactic script -- automatic *)

Goal "EX S. S ~: range(f :: 'a => 'a set)";
  by (best_tac (claset() addSEs [equalityCE]) 1);
qed "it";
