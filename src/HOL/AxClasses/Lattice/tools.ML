
(** generic tools **)

val prems = goalw HOL.thy [Ex_def] "EX x. P x ==> P (@x. P x)";
  by (resolve_tac prems 1);
qed "selectI1";

goal HOL.thy "(P & Q) = (Q & P)";
  by (fast_tac prop_cs 1);
qed "conj_commut";
