
context HOL.thy;

Goalw [Ex_def] "EX x. P x ==> P (@x. P x)";
  by (assume_tac 1);
qed "selectI1";

context thy;



(** basic properties of "&&" and "||" **)

(* unique existence *)

Goalw [inf_def] "is_inf x y (x && y)";
  by (rtac (ex_inf RS spec RS spec RS selectI1) 1);
qed "inf_is_inf";

Goal "is_inf x y inf --> x && y = inf";
  by (rtac impI 1);
  by (rtac (is_inf_uniq RS mp) 1);
  by (rtac conjI 1);
  by (rtac inf_is_inf 1);
  by (assume_tac 1);
qed "inf_uniq";

Goalw [Ex1_def] "ALL x y. EX! inf::'a::lattice. is_inf x y inf";
  by Safe_tac;
  by (Step_tac 1);
  by (Step_tac 1);
  by (rtac inf_is_inf 1);
  by (rtac (inf_uniq RS mp RS sym) 1);
  by (assume_tac 1);
qed "ex1_inf";


Goalw [sup_def] "is_sup x y (x || y)";
  by (rtac (ex_sup RS spec RS spec RS selectI1) 1);
qed "sup_is_sup";

Goal "is_sup x y sup --> x || y = sup";
  by (rtac impI 1);
  by (rtac (is_sup_uniq RS mp) 1);
  by (rtac conjI 1);
  by (rtac sup_is_sup 1);
  by (assume_tac 1);
qed "sup_uniq";

Goalw [Ex1_def] "ALL x y. EX! sup::'a::lattice. is_sup x y sup";
  by Safe_tac;
  by (Step_tac 1);
  by (Step_tac 1);
  by (rtac sup_is_sup 1);
  by (rtac (sup_uniq RS mp RS sym) 1);
  by (assume_tac 1);
qed "ex1_sup";


(* "&&" yields g.l.bs, "||" yields l.u.bs. --- in pieces *)

val tac =
  cut_facts_tac [inf_is_inf] 1 THEN
  rewrite_goals_tac [inf_def, is_inf_def] THEN
  Fast_tac 1;

Goal "x && y [= x";
  by tac;
qed "inf_lb1";

Goal "x && y [= y";
  by tac;
qed "inf_lb2";

val prems = goal thy "[| z [= x; z [= y |] ==> z [= x && y";
  by (cut_facts_tac prems 1);
  by tac;
qed "inf_ub_lbs";


val tac =
  cut_facts_tac [sup_is_sup] 1 THEN
  rewrite_goals_tac [sup_def, is_sup_def] THEN
  Fast_tac 1;

Goal "x [= x || y";
  by tac;
qed "sup_ub1";

Goal "y [= x || y";
  by tac;
qed "sup_ub2";

val prems = goal thy "[| x [= z; y [= z |] ==> x || y [= z";
  by (cut_facts_tac prems 1);
  by tac;
qed "sup_lb_ubs";



(** some equations concerning "&&" and "||" vs. "[=" **)

(* the Connection Theorems: "[=" expressed via "&&" or "||" *)

Goal "(x && y = x) = (x [= y)";
  by (rtac iffI 1);
  (*==>*)
    by (etac subst 1);
    by (rtac inf_lb2 1);
  (*<==*)
    by (rtac (inf_uniq RS mp) 1);
    by (rewtac is_inf_def);
    by (REPEAT_FIRST (rtac conjI));
    by (rtac le_refl 1);
    by (assume_tac 1);
    by (Fast_tac 1);
qed "inf_connect";

Goal "(x || y = y) = (x [= y)";
  by (rtac iffI 1);
  (*==>*)
    by (etac subst 1);
    by (rtac sup_ub1 1);
  (*<==*)
    by (rtac (sup_uniq RS mp) 1);
    by (rewtac is_sup_def);
    by (REPEAT_FIRST (rtac conjI));
    by (assume_tac 1);
    by (rtac le_refl 1);
    by (Fast_tac 1);
qed "sup_connect";


(* minorized infs / majorized sups *)

Goal "(x [= y && z) = (x [= y & x [= z)";
  by (rtac iffI 1);
  (*==> (level 1)*)
    by (cut_facts_tac [inf_lb1, inf_lb2] 1);
    by (rtac conjI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
  (*<== (level 9)*)
    by (etac conjE 1);
    by (etac inf_ub_lbs 1);
    by (assume_tac 1);
qed "le_inf_eq";

Goal "(x || y [= z) = (x [= z & y [= z)";
  by (rtac iffI 1);
  (*==> (level 1)*)
    by (cut_facts_tac [sup_ub1, sup_ub2] 1);
    by (rtac conjI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
  (*<== (level 9)*)
    by (etac conjE 1);
    by (etac sup_lb_ubs 1);
    by (assume_tac 1);
qed "ge_sup_eq";


(** algebraic properties of "&&" and "||": A, C, I, AB **)

(* associativity *)

Goal "(x && y) && z = x && (y && z)";
  by (stac (inf_uniq RS mp RS sym) 1);
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  by (rtac refl 2);
  by (rtac (is_inf_assoc RS mp) 1);
  by (REPEAT_FIRST (rtac conjI));
  by (REPEAT_FIRST (rtac inf_is_inf));
qed "inf_assoc";

Goal "(x || y) || z = x || (y || z)";
  by (stac (sup_uniq RS mp RS sym) 1);
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  by (rtac refl 2);
  by (rtac (is_sup_assoc RS mp) 1);
  by (REPEAT_FIRST (rtac conjI));
  by (REPEAT_FIRST (rtac sup_is_sup));
qed "sup_assoc";


(* commutativity *)

Goalw [inf_def] "x && y = y && x";
  by (stac (is_inf_commut RS ext) 1);
  by (rtac refl 1);
qed "inf_commut";

Goalw [sup_def] "x || y = y || x";
  by (stac (is_sup_commut RS ext) 1);
  by (rtac refl 1);
qed "sup_commut";


(* idempotency *)

Goal "x && x = x";
  by (stac inf_connect 1);
  by (rtac le_refl 1);
qed "inf_idemp";

Goal "x || x = x";
  by (stac sup_connect 1);
  by (rtac le_refl 1);
qed "sup_idemp";


(* absorption *)

Goal "x || (x && y) = x";
  by (stac sup_commut 1);
  by (stac sup_connect 1);
  by (rtac inf_lb1 1);
qed "sup_inf_absorb";

Goal "x && (x || y) = x";
  by (stac inf_connect 1);
  by (rtac sup_ub1 1);
qed "inf_sup_absorb";


(* monotonicity *)

val prems = goal thy "[| a [= b; x [= y |] ==> a && x [= b && y";
  by (cut_facts_tac prems 1);
  by (stac le_inf_eq 1);
  by (rtac conjI 1);
  by (rtac (le_trans RS mp) 1);
  by (rtac conjI 1);
  by (rtac inf_lb1 1);
  by (assume_tac 1);
  by (rtac (le_trans RS mp) 1);
  by (rtac conjI 1);
  by (rtac inf_lb2 1);
  by (assume_tac 1);
qed "inf_mon";

val prems = goal thy "[| a [= b; x [= y |] ==> a || x [= b || y";
  by (cut_facts_tac prems 1);
  by (stac ge_sup_eq 1);
  by (rtac conjI 1);
  by (rtac (le_trans RS mp) 1);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (rtac sup_ub1 1);
  by (rtac (le_trans RS mp) 1);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (rtac sup_ub2 1);
qed "sup_mon";
