
open CLattice;


(** basic properties of "Inf" and "Sup" **)

(* unique existence *)

goalw thy [Inf_def] "is_Inf A (Inf A)";
  by (rtac (ex_Inf RS spec RS selectI1) 1);
qed "Inf_is_Inf";

goal thy "is_Inf A inf --> Inf A = inf";
  by (rtac impI 1);
  by (rtac (is_Inf_uniq RS mp) 1);
  by (rtac conjI 1);
  by (rtac Inf_is_Inf 1);
  by (assume_tac 1);
qed "Inf_uniq";

goalw thy [Ex1_def] "ALL A. EX! inf::'a::clattice. is_Inf A inf";
  by Safe_tac;
  by (Step_tac 1);
  by (Step_tac 1);
  by (rtac Inf_is_Inf 1);
  by (rtac (Inf_uniq RS mp RS sym) 1);
  by (assume_tac 1);
qed "ex1_Inf";


goalw thy [Sup_def] "is_Sup A (Sup A)";
  by (rtac (ex_Sup RS spec RS selectI1) 1);
qed "Sup_is_Sup";

goal thy "is_Sup A sup --> Sup A = sup";
  by (rtac impI 1);
  by (rtac (is_Sup_uniq RS mp) 1);
  by (rtac conjI 1);
  by (rtac Sup_is_Sup 1);
  by (assume_tac 1);
qed "Sup_uniq";

goalw thy [Ex1_def] "ALL A. EX! sup::'a::clattice. is_Sup A sup";
  by Safe_tac;
  by (Step_tac 1);
  by (Step_tac 1);
  by (rtac Sup_is_Sup 1);
  by (rtac (Sup_uniq RS mp RS sym) 1);
  by (assume_tac 1);
qed "ex1_Sup";


(* "Inf" yields g.l.bs, "Sup" yields l.u.bs. --- in pieces *)

val prems = goalw thy [Inf_def] "x:A ==> Inf A [= x";
  by (cut_facts_tac prems 1);
  by (rtac selectI2 1);
  by (rtac Inf_is_Inf 1);
  by (rewtac is_Inf_def);
  by (Fast_tac 1);
qed "Inf_lb";

val [prem] = goalw thy [Inf_def] "(!!x. x:A ==> z [= x) ==> z [= Inf A";
  by (rtac selectI2 1);
  by (rtac Inf_is_Inf 1);
  by (rewtac is_Inf_def);
  by (Step_tac 1);
  by (Step_tac 1);
  by (etac mp 1);
  by (rtac ballI 1);
  by (etac prem 1);
qed "Inf_ub_lbs";


val prems = goalw thy [Sup_def] "x:A ==> x [= Sup A";
  by (cut_facts_tac prems 1);
  by (rtac selectI2 1);
  by (rtac Sup_is_Sup 1);
  by (rewtac is_Sup_def);
  by (Fast_tac 1);
qed "Sup_ub";

val [prem] = goalw thy [Sup_def] "(!!x. x:A ==> x [= z) ==> Sup A [= z";
  by (rtac selectI2 1);
  by (rtac Sup_is_Sup 1);
  by (rewtac is_Sup_def);
  by (Step_tac 1);
  by (Step_tac 1);
  by (etac mp 1);
  by (rtac ballI 1);
  by (etac prem 1);
qed "Sup_lb_ubs";


(** minorized Infs / majorized Sups **)

goal thy "(x [= Inf A) = (ALL y:A. x [= y)";
  by (rtac iffI 1);
  (*==>*)
    by (rtac ballI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (etac Inf_lb 1);
  (*<==*)
    by (rtac Inf_ub_lbs 1);
    by (Fast_tac 1);
qed "le_Inf_eq";

goal thy "(Sup A [= x) = (ALL y:A. y [= x)";
  by (rtac iffI 1);
  (*==>*)
    by (rtac ballI 1);
    by (rtac (le_trans RS mp) 1);
    by (rtac conjI 1);
    by (etac Sup_ub 1);
    by (assume_tac 1);
  (*<==*)
    by (rtac Sup_lb_ubs 1);
    by (Fast_tac 1);
qed "ge_Sup_eq";



(** Subsets and limits **)

goal thy "A <= B --> Inf B [= Inf A";
  by (rtac impI 1);
  by (stac le_Inf_eq 1);
  by (rewtac Ball_def);
  by Safe_tac;
  by (dtac subsetD 1);
  by (assume_tac 1);
  by (etac Inf_lb 1);
qed "Inf_subset_antimon";

goal thy "A <= B --> Sup A [= Sup B";
  by (rtac impI 1);
  by (stac ge_Sup_eq 1);
  by (rewtac Ball_def);
  by Safe_tac;
  by (dtac subsetD 1);
  by (assume_tac 1);
  by (etac Sup_ub 1);
qed "Sup_subset_mon";


(** singleton / empty limits **)

goal thy "Inf {x} = x";
  by (rtac (Inf_uniq RS mp) 1);
  by (rewtac is_Inf_def);
  by Safe_tac;
  by (rtac le_refl 1);
  by (Fast_tac 1);
qed "sing_Inf_eq";

goal thy "Sup {x} = x";
  by (rtac (Sup_uniq RS mp) 1);
  by (rewtac is_Sup_def);
  by Safe_tac;
  by (rtac le_refl 1);
  by (Fast_tac 1);
qed "sing_Sup_eq";


goal thy "Inf {} = Sup {x. True}";
  by (rtac (Inf_uniq RS mp) 1);
  by (rewtac is_Inf_def);
  by Safe_tac;
  by (rtac (sing_Sup_eq RS subst) 1);
  back();
  by (rtac (Sup_subset_mon RS mp) 1);
  by (Fast_tac 1);
qed "empty_Inf_eq";

goal thy "Sup {} = Inf {x. True}";
  by (rtac (Sup_uniq RS mp) 1);
  by (rewtac is_Sup_def);
  by Safe_tac;
  by (rtac (sing_Inf_eq RS subst) 1);
  by (rtac (Inf_subset_antimon RS mp) 1);
  by (Fast_tac 1);
qed "empty_Sup_eq";
