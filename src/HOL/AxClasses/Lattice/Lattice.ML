
open Lattice;


(** basic properties of "&&" and "||" **)

(* unique existence *)

goalw thy [inf_def] "is_inf x y (x && y)";
  br (ex_inf RS spec RS spec RS selectI1) 1;
qed "inf_is_inf";

goal thy "is_inf x y inf --> x && y = inf";
  br impI 1;
  br (is_inf_uniq RS mp) 1;
  br conjI 1;
  br inf_is_inf 1;
  ba 1;
qed "inf_uniq";

goalw thy [Ex1_def] "ALL x y. EX! inf::'a::lattice. is_inf x y inf";
  by (safe_tac HOL_cs);
  by (step_tac HOL_cs 1);
  by (step_tac HOL_cs 1);
  br inf_is_inf 1;
  br (inf_uniq RS mp RS sym) 1;
  ba 1;
qed "ex1_inf";


goalw thy [sup_def] "is_sup x y (x || y)";
  br (ex_sup RS spec RS spec RS selectI1) 1;
qed "sup_is_sup";

goal thy "is_sup x y sup --> x || y = sup";
  br impI 1;
  br (is_sup_uniq RS mp) 1;
  br conjI 1;
  br sup_is_sup 1;
  ba 1;
qed "sup_uniq";

goalw thy [Ex1_def] "ALL x y. EX! sup::'a::lattice. is_sup x y sup";
  by (safe_tac HOL_cs);
  by (step_tac HOL_cs 1);
  by (step_tac HOL_cs 1);
  br sup_is_sup 1;
  br (sup_uniq RS mp RS sym) 1;
  ba 1;
qed "ex1_sup";


(* "&&" yields g.l.bs, "||" yields l.u.bs. --- in pieces *)

val tac =
  cut_facts_tac [inf_is_inf] 1 THEN
  rewrite_goals_tac [inf_def, is_inf_def] THEN
  fast_tac HOL_cs 1;

goal thy "x && y [= x";
  by tac;
qed "inf_lb1";

goal thy "x && y [= y";
  by tac;
qed "inf_lb2";

val prems = goal thy "[| z [= x; z [= y |] ==> z [= x && y";
  by (cut_facts_tac prems 1);
  by tac;
qed "inf_ub_lbs";


val tac =
  cut_facts_tac [sup_is_sup] 1 THEN
  rewrite_goals_tac [sup_def, is_sup_def] THEN
  fast_tac HOL_cs 1;

goal thy "x [= x || y";
  by tac;
qed "sup_ub1";

goal thy "y [= x || y";
  by tac;
qed "sup_ub2";

val prems = goal thy "[| x [= z; y [= z |] ==> x || y [= z";
  by (cut_facts_tac prems 1);
  by tac;
qed "sup_lb_ubs";



(** some equations concerning "&&" and "||" vs. "[=" **)

(* the Connection Theorems: "[=" expressed via "&&" or "||" *)

goal thy "(x && y = x) = (x [= y)";
  br iffI 1;
  (*==>*)
    be subst 1;
    br inf_lb2 1;
  (*<==*)
    br (inf_uniq RS mp) 1;
    by (rewrite_goals_tac [is_inf_def]);
    by (REPEAT_FIRST (rtac conjI));
    br le_refl 1;
    ba 1;
    by (fast_tac HOL_cs 1);
qed "inf_connect";

goal thy "(x || y = y) = (x [= y)";
  br iffI 1;
  (*==>*)
    be subst 1;
    br sup_ub1 1;
  (*<==*)
    br (sup_uniq RS mp) 1;
    by (rewrite_goals_tac [is_sup_def]);
    by (REPEAT_FIRST (rtac conjI));
    ba 1;
    br le_refl 1;
    by (fast_tac HOL_cs 1);
qed "sup_connect";


(* minorized infs / majorized sups *)

goal thy "(x [= y && z) = (x [= y & x [= z)";
  br iffI 1;
  (*==> (level 1)*)
    by (cut_facts_tac [inf_lb1, inf_lb2] 1);
    br conjI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
  (*<== (level 9)*)
    be conjE 1;
    be inf_ub_lbs 1;
    ba 1;
qed "le_inf_eq";

goal thy "(x || y [= z) = (x [= z & y [= z)";
  br iffI 1;
  (*==> (level 1)*)
    by (cut_facts_tac [sup_ub1, sup_ub2] 1);
    br conjI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
  (*<== (level 9)*)
    be conjE 1;
    be sup_lb_ubs 1;
    ba 1;
qed "ge_sup_eq";


(** algebraic properties of "&&" and "||": A, C, I, AB **)

(* associativity *)

goal thy "(x && y) && z = x && (y && z)";
  by (stac (inf_uniq RS mp RS sym) 1);
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  br refl 2;
  br (is_inf_assoc RS mp) 1;
  by (REPEAT_FIRST (rtac conjI));
  by (REPEAT_FIRST (rtac inf_is_inf));
qed "inf_assoc";

goal thy "(x || y) || z = x || (y || z)";
  by (stac (sup_uniq RS mp RS sym) 1);
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  back();
  br refl 2;
  br (is_sup_assoc RS mp) 1;
  by (REPEAT_FIRST (rtac conjI));
  by (REPEAT_FIRST (rtac sup_is_sup));
qed "sup_assoc";


(* commutativity *)

goalw thy [inf_def] "x && y = y && x";
  by (stac (is_inf_commut RS ext) 1);
  br refl 1;
qed "inf_commut";

goalw thy [sup_def] "x || y = y || x";
  by (stac (is_sup_commut RS ext) 1);
  br refl 1;
qed "sup_commut";


(* idempotency *)

goal thy "x && x = x";
  by (stac inf_connect 1);
  br le_refl 1;
qed "inf_idemp";

goal thy "x || x = x";
  by (stac sup_connect 1);
  br le_refl 1;
qed "sup_idemp";


(* absorption *)

goal thy "x || (x && y) = x";
  by (stac sup_commut 1);
  by (stac sup_connect 1);
  br inf_lb1 1;
qed "sup_inf_absorb";

goal thy "x && (x || y) = x";
  by (stac inf_connect 1);
  br sup_ub1 1;
qed "inf_sup_absorb";


(* monotonicity *)

val prems = goal thy "[| a [= b; x [= y |] ==> a && x [= b && y";
  by (cut_facts_tac prems 1);
  by (stac le_inf_eq 1);
  br conjI 1;
  br (le_trans RS mp) 1;
  br conjI 1;
  br inf_lb1 1;
  ba 1;
  br (le_trans RS mp) 1;
  br conjI 1;
  br inf_lb2 1;
  ba 1;
qed "inf_mon";

val prems = goal thy "[| a [= b; x [= y |] ==> a || x [= b || y";
  by (cut_facts_tac prems 1);
  by (stac ge_sup_eq 1);
  br conjI 1;
  br (le_trans RS mp) 1;
  br conjI 1;
  ba 1;
  br sup_ub1 1;
  br (le_trans RS mp) 1;
  br conjI 1;
  ba 1;
  br sup_ub2 1;
qed "sup_mon";
