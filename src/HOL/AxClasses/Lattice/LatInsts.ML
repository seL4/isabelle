
open LatInsts;


goal thy "Inf {x, y} = x && y";
  br (Inf_uniq RS mp) 1;
  by (stac bin_is_Inf_eq 1);
  br inf_is_inf 1;
qed "bin_Inf_eq";

goal thy "Sup {x, y} = x || y";
  br (Sup_uniq RS mp) 1;
  by (stac bin_is_Sup_eq 1);
  br sup_is_sup 1;
qed "bin_Sup_eq";



(* Unions and limits *)

goal thy "Inf (A Un B) = Inf A && Inf B";
  br (Inf_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Inf_def]);
  by (safe_tac set_cs);

  br (conjI RS (le_trans RS mp)) 1;
  br inf_lb1 1;
  be Inf_lb 1;

  br (conjI RS (le_trans RS mp)) 1;
  br inf_lb2 1;
  be Inf_lb 1;

  by (stac le_inf_eq 1);
  br conjI 1;
  br Inf_ub_lbs 1;
  by (fast_tac set_cs 1);
  br Inf_ub_lbs 1;
  by (fast_tac set_cs 1);
qed "Inf_Un_eq";

goal thy "Inf (UN i:A. B i) = Inf {Inf (B i) |i. i:A}";
  br (Inf_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Inf_def]);
  by (safe_tac set_cs);
  (*level 3*)
  br (conjI RS (le_trans RS mp)) 1;
  be Inf_lb 2;
  br (sing_Inf_eq RS subst) 1;
  br (Inf_subset_antimon RS mp) 1;
  by (fast_tac set_cs 1);
  (*level 8*)
  by (stac le_Inf_eq 1);
  by (safe_tac set_cs);
  by (stac le_Inf_eq 1);
  by (fast_tac set_cs 1);
qed "Inf_UN_eq";



goal thy "Sup (A Un B) = Sup A || Sup B";
  br (Sup_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Sup_def]);
  by (safe_tac set_cs);

  br (conjI RS (le_trans RS mp)) 1;
  be Sup_ub 1;
  br sup_ub1 1;

  br (conjI RS (le_trans RS mp)) 1;
  be Sup_ub 1;
  br sup_ub2 1;

  by (stac ge_sup_eq 1);
  br conjI 1;
  br Sup_lb_ubs 1;
  by (fast_tac set_cs 1);
  br Sup_lb_ubs 1;
  by (fast_tac set_cs 1);
qed "Sup_Un_eq";

goal thy "Sup (UN i:A. B i) = Sup {Sup (B i) |i. i:A}";
  br (Sup_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Sup_def]);
  by (safe_tac set_cs);
  (*level 3*)
  br (conjI RS (le_trans RS mp)) 1;
  be Sup_ub 1;
  br (sing_Sup_eq RS subst) 1;
  back();
  br (Sup_subset_mon RS mp) 1;
  by (fast_tac set_cs 1);
  (*level 8*)
  by (stac ge_Sup_eq 1);
  by (safe_tac set_cs);
  by (stac ge_Sup_eq 1);
  by (fast_tac set_cs 1);
qed "Sup_UN_eq";
