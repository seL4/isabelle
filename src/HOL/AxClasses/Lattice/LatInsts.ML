
open LatInsts;


goal thy "Inf {x, y} = x && y";
  by (rtac (Inf_uniq RS mp) 1);
  by (stac bin_is_Inf_eq 1);
  by (rtac inf_is_inf 1);
qed "bin_Inf_eq";

goal thy "Sup {x, y} = x || y";
  by (rtac (Sup_uniq RS mp) 1);
  by (stac bin_is_Sup_eq 1);
  by (rtac sup_is_sup 1);
qed "bin_Sup_eq";



(* Unions and limits *)

goal thy "Inf (A Un B) = Inf A && Inf B";
  by (rtac (Inf_uniq RS mp) 1);
  by (rewtac is_Inf_def);
  by Safe_tac;

  by (rtac (conjI RS (le_trans RS mp)) 1);
  by (rtac inf_lb1 1);
  by (etac Inf_lb 1);

  by (rtac (conjI RS (le_trans RS mp)) 1);
  by (rtac inf_lb2 1);
  by (etac Inf_lb 1);

  by (stac le_inf_eq 1);
  by (rtac conjI 1);
  by (rtac Inf_ub_lbs 1);
  by (Fast_tac 1);
  by (rtac Inf_ub_lbs 1);
  by (Fast_tac 1);
qed "Inf_Un_eq";

goal thy "Inf (UN i:A. B i) = Inf {Inf (B i) |i. i:A}";
  by (rtac (Inf_uniq RS mp) 1);
  by (rewtac is_Inf_def);
  by Safe_tac;
  (*level 3*)
  by (rtac (conjI RS (le_trans RS mp)) 1);
  by (etac Inf_lb 2);
  by (rtac (sing_Inf_eq RS subst) 1);
  by (rtac (Inf_subset_antimon RS mp) 1);
  by (Fast_tac 1);
  (*level 8*)
  by (stac le_Inf_eq 1);
  by Safe_tac;
  by (stac le_Inf_eq 1);
  by (Fast_tac 1);
qed "Inf_UN_eq";



goal thy "Sup (A Un B) = Sup A || Sup B";
  by (rtac (Sup_uniq RS mp) 1);
  by (rewtac is_Sup_def);
  by Safe_tac;

  by (rtac (conjI RS (le_trans RS mp)) 1);
  by (etac Sup_ub 1);
  by (rtac sup_ub1 1);

  by (rtac (conjI RS (le_trans RS mp)) 1);
  by (etac Sup_ub 1);
  by (rtac sup_ub2 1);

  by (stac ge_sup_eq 1);
  by (rtac conjI 1);
  by (rtac Sup_lb_ubs 1);
  by (Fast_tac 1);
  by (rtac Sup_lb_ubs 1);
  by (Fast_tac 1);
qed "Sup_Un_eq";

goal thy "Sup (UN i:A. B i) = Sup {Sup (B i) |i. i:A}";
  by (rtac (Sup_uniq RS mp) 1);
  by (rewtac is_Sup_def);
  by Safe_tac;
  (*level 3*)
  by (rtac (conjI RS (le_trans RS mp)) 1);
  by (etac Sup_ub 1);
  by (rtac (sing_Sup_eq RS subst) 1);
  back();
  by (rtac (Sup_subset_mon RS mp) 1);
  by (Fast_tac 1);
  (*level 8*)
  by (stac ge_Sup_eq 1);
  by Safe_tac;
  by (stac ge_Sup_eq 1);
  by (Fast_tac 1);
qed "Sup_UN_eq";
