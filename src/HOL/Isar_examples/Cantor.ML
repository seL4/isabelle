
(* tactic script -- single steps *)

Goal "EX S. S ~: range(f :: 'a => 'a set)";
  by (rtac exI 1);
  by (rtac notI 1);
  by (etac rangeE 1);
  by (etac equalityCE 1);
  by (dtac CollectD 1);
  by (contr_tac 1);
  by (swap_res_tac [CollectI] 1);
  by (assume_tac 1);
qed "";


(* tactic script -- automatic *)

Goal "EX S. S ~: range(f :: 'a => 'a set)";
  by (best_tac (claset() addSEs [equalityCE]) 1);
qed "";
