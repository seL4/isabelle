
open CLattice;


(** basic properties of "Inf" and "Sup" **)

(* unique existence *)

goalw thy [Inf_def] "is_Inf A (Inf A)";
  br (ex_Inf RS spec RS selectI1) 1;
qed "Inf_is_Inf";

goal thy "is_Inf A inf --> Inf A = inf";
  br impI 1;
  br (is_Inf_uniq RS mp) 1;
  br conjI 1;
  br Inf_is_Inf 1;
  ba 1;
qed "Inf_uniq";

goalw thy [Ex1_def] "ALL A. EX! inf::'a::clattice. is_Inf A inf";
  by (safe_tac HOL_cs);
  by (step_tac HOL_cs 1);
  by (step_tac HOL_cs 1);
  br Inf_is_Inf 1;
  br (Inf_uniq RS mp RS sym) 1;
  ba 1;
qed "ex1_Inf";


goalw thy [Sup_def] "is_Sup A (Sup A)";
  br (ex_Sup RS spec RS selectI1) 1;
qed "Sup_is_Sup";

goal thy "is_Sup A sup --> Sup A = sup";
  br impI 1;
  br (is_Sup_uniq RS mp) 1;
  br conjI 1;
  br Sup_is_Sup 1;
  ba 1;
qed "Sup_uniq";

goalw thy [Ex1_def] "ALL A. EX! sup::'a::clattice. is_Sup A sup";
  by (safe_tac HOL_cs);
  by (step_tac HOL_cs 1);
  by (step_tac HOL_cs 1);
  br Sup_is_Sup 1;
  br (Sup_uniq RS mp RS sym) 1;
  ba 1;
qed "ex1_Sup";


(* "Inf" yields g.l.bs, "Sup" yields l.u.bs. --- in pieces *)

val prems = goalw thy [Inf_def] "x:A ==> Inf A [= x";
  by (cut_facts_tac prems 1);
  br selectI2 1;
  br Inf_is_Inf 1;
  by (rewrite_goals_tac [is_Inf_def]);
  by (fast_tac set_cs 1);
qed "Inf_lb";

val [prem] = goalw thy [Inf_def] "(!!x. x:A ==> z [= x) ==> z [= Inf A";
  br selectI2 1;
  br Inf_is_Inf 1;
  by (rewrite_goals_tac [is_Inf_def]);
  by (step_tac HOL_cs 1);
  by (step_tac HOL_cs 1);
  be mp 1;
  br ballI 1;
  be prem 1;
qed "Inf_ub_lbs";


val prems = goalw thy [Sup_def] "x:A ==> x [= Sup A";
  by (cut_facts_tac prems 1);
  br selectI2 1;
  br Sup_is_Sup 1;
  by (rewrite_goals_tac [is_Sup_def]);
  by (fast_tac set_cs 1);
qed "Sup_ub";

val [prem] = goalw thy [Sup_def] "(!!x. x:A ==> x [= z) ==> Sup A [= z";
  br selectI2 1;
  br Sup_is_Sup 1;
  by (rewrite_goals_tac [is_Sup_def]);
  by (step_tac HOL_cs 1);
  by (step_tac HOL_cs 1);
  be mp 1;
  br ballI 1;
  be prem 1;
qed "Sup_lb_ubs";


(** minorized Infs / majorized Sups **)

goal thy "(x [= Inf A) = (ALL y:A. x [= y)";
  br iffI 1;
  (*==>*)
    br ballI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    be Inf_lb 1;
  (*<==*)
    br Inf_ub_lbs 1;
    by (fast_tac set_cs 1);
qed "le_Inf_eq";

goal thy "(Sup A [= x) = (ALL y:A. y [= x)";
  br iffI 1;
  (*==>*)
    br ballI 1;
    br (le_trans RS mp) 1;
    br conjI 1;
    be Sup_ub 1;
    ba 1;
  (*<==*)
    br Sup_lb_ubs 1;
    by (fast_tac set_cs 1);
qed "ge_Sup_eq";



(** Subsets and limits **)

goal thy "A <= B --> Inf B [= Inf A";
  br impI 1;
  by (stac le_Inf_eq 1);
  by (rewrite_goals_tac [Ball_def]);
  by (safe_tac set_cs);
  bd subsetD 1;
  ba 1;
  be Inf_lb 1;
qed "Inf_subset_antimon";

goal thy "A <= B --> Sup A [= Sup B";
  br impI 1;
  by (stac ge_Sup_eq 1);
  by (rewrite_goals_tac [Ball_def]);
  by (safe_tac set_cs);
  bd subsetD 1;
  ba 1;
  be Sup_ub 1;
qed "Sup_subset_mon";


(** singleton / empty limits **)

goal thy "Inf {x} = x";
  br (Inf_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Inf_def]);
  by (safe_tac set_cs);
  br le_refl 1;
  by (fast_tac set_cs 1);
qed "sing_Inf_eq";

goal thy "Sup {x} = x";
  br (Sup_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Sup_def]);
  by (safe_tac set_cs);
  br le_refl 1;
  by (fast_tac set_cs 1);
qed "sing_Sup_eq";


goal thy "Inf {} = Sup {x. True}";
  br (Inf_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Inf_def]);
  by (safe_tac set_cs);
  br (sing_Sup_eq RS subst) 1;
  back();
  br (Sup_subset_mon RS mp) 1;
  by (fast_tac set_cs 1);
qed "empty_Inf_eq";

goal thy "Sup {} = Inf {x. True}";
  br (Sup_uniq RS mp) 1;
  by (rewrite_goals_tac [is_Sup_def]);
  by (safe_tac set_cs);
  br (sing_Inf_eq RS subst) 1;
  br (Inf_subset_antimon RS mp) 1;
  by (fast_tac set_cs 1);
qed "empty_Sup_eq";
