
open LatMorph;


(** monotone functions vs. "&&"- / "||"-semi-morphisms **)

goalw thy [is_mono_def] "is_mono f = (ALL x y. f (x && y) [= f x && f y)";
  by (safe_tac (!claset));
  (*==> (level 1)*)
    by (stac le_inf_eq 1);
    br conjI 1;
    by (Step_tac 1);
    by (Step_tac 1);
    be mp 1;
    br inf_lb1 1;
    by (Step_tac 1);
    by (Step_tac 1);
    be mp 1;
    br inf_lb2 1;
  (*==> (level 11)*)
    br (conjI RS (le_trans RS mp)) 1;
    br inf_lb2 2;
    by (subgoal_tac "x && y = x" 1);
    be subst 1;
    by (Fast_tac 1);
    by (stac inf_connect 1);
    ba 1;
qed "mono_inf_eq";

goalw thy [is_mono_def] "is_mono f = (ALL x y. f x || f y [= f (x || y))";
  by (safe_tac (!claset));
  (*==> (level 1)*)
    by (stac ge_sup_eq 1);
    br conjI 1;
    by (Step_tac 1);
    by (Step_tac 1);
    be mp 1;
    br sup_ub1 1;
    by (Step_tac 1);
    by (Step_tac 1);
    be mp 1;
    br sup_ub2 1;
  (*==> (level 11)*)
    br (conjI RS (le_trans RS mp)) 1;
    br sup_ub1 1;
    by (subgoal_tac "x || y = y" 1);
    be subst 1;
    by (Fast_tac 1);
    by (stac sup_connect 1);
    ba 1;
qed "mono_sup_eq";


