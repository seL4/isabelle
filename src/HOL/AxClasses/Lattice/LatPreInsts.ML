
open LatPreInsts;


(** complete lattices **)

goal thy "is_inf x y (Inf {x, y})";
  br (bin_is_Inf_eq RS subst) 1;
  br Inf_is_Inf 1;
qed "Inf_is_inf";

goal thy "is_sup x y (Sup {x, y})";
  br (bin_is_Sup_eq RS subst) 1;
  br Sup_is_Sup 1;
qed "Sup_is_sup";



(** product lattices **)

(* pairs *)

goalw thy [is_inf_def, le_prod_def] "is_inf p q (fst p && fst q, snd p && snd q)";
  by (Simp_tac 1);
  by (safe_tac (claset()));
  by (REPEAT_FIRST (fn i => resolve_tac [inf_lb1, inf_lb2, inf_ub_lbs] i ORELSE atac i));
qed "prod_is_inf";

goalw thy [is_sup_def, le_prod_def] "is_sup p q (fst p || fst q, snd p || snd q)";
  by (Simp_tac 1);
  by (safe_tac (claset()));
  by (REPEAT_FIRST (fn i => resolve_tac [sup_ub1, sup_ub2, sup_lb_ubs] i ORELSE atac i));
qed "prod_is_sup";


(* functions *)

goalw thy [is_inf_def, le_fun_def] "is_inf f g (%x. f x && g x)";
  by (safe_tac (claset()));
  br inf_lb1 1;
  br inf_lb2 1;
  br inf_ub_lbs 1;
  by (REPEAT_FIRST (Fast_tac));
qed "fun_is_inf";

goalw thy [is_sup_def, le_fun_def] "is_sup f g (%x. f x || g x)";
  by (safe_tac (claset()));
  br sup_ub1 1;
  br sup_ub2 1;
  br sup_lb_ubs 1;
  by (REPEAT_FIRST (Fast_tac));
qed "fun_is_sup";



(** dual lattices **)

goalw thy [is_inf_def, le_dual_def] "is_inf x y (Abs_dual (Rep_dual x || Rep_dual y))";
  by (stac Abs_dual_inverse' 1);
  by (safe_tac (claset()));
  br sup_ub1 1;
  br sup_ub2 1;
  br sup_lb_ubs 1;
  ba 1;
  ba 1;
qed "dual_is_inf";

goalw thy [is_sup_def, le_dual_def] "is_sup x y (Abs_dual (Rep_dual x && Rep_dual y))";
  by (stac Abs_dual_inverse' 1);
  by (safe_tac (claset()));
  br inf_lb1 1;
  br inf_lb2 1;
  br inf_ub_lbs 1;
  ba 1;
  ba 1;
qed "dual_is_sup";
