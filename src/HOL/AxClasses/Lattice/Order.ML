
open Order;


(** basic properties of limits **)

(* uniqueness *)

val tac =
  rtac impI 1 THEN
  rtac (le_antisym RS mp) 1 THEN
  Fast_tac 1;


goalw thy [is_inf_def] "is_inf x y inf & is_inf x y inf' --> inf = inf'";
  by tac;
qed "is_inf_uniq";

goalw thy [is_sup_def] "is_sup x y sup & is_sup x y sup' --> sup = sup'";
  by tac;
qed "is_sup_uniq";


goalw thy [is_Inf_def] "is_Inf A inf & is_Inf A inf' --> inf = inf'";
  by tac;
qed "is_Inf_uniq";

goalw thy [is_Sup_def] "is_Sup A sup & is_Sup A sup' --> sup = sup'";
  by tac;
qed "is_Sup_uniq";



(* commutativity *)

goalw thy [is_inf_def] "is_inf x y inf = is_inf y x inf";
  by (Fast_tac 1);
qed "is_inf_commut";

goalw thy [is_sup_def] "is_sup x y sup = is_sup y x sup";
  by (Fast_tac 1);
qed "is_sup_commut";


(* associativity *)

goalw thy [is_inf_def] "is_inf x y xy & is_inf y z yz & is_inf xy z xyz --> is_inf x yz xyz";
  by Safe_tac;
  (*level 1*)
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
  (*level 4*)
    by (Step_tac 1);
    back();
    by (etac mp 1);
    by (rtac conjI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
    by (assume_tac 1);
  (*level 11*)
    by (Step_tac 1);
    back();
    back();
    by (etac mp 1);
    by (rtac conjI 1);
    by (Step_tac 1);
    by (etac mp 1);
    by (etac conjI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    back();     (* !! *)
    by (assume_tac 1);
qed "is_inf_assoc";


goalw thy [is_sup_def] "is_sup x y xy & is_sup y z yz & is_sup xy z xyz --> is_sup x yz xyz";
  by Safe_tac;
  (*level 1*)
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
  (*level 4*)
    by (Step_tac 1);
    back();
    by (etac mp 1);
    by (rtac conjI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
    by (assume_tac 1);
  (*level 11*)
    by (Step_tac 1);
    back();
    back();
    by (etac mp 1);
    by (rtac conjI 1);
    by (Step_tac 1);
    by (etac mp 1);
    by (etac conjI 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    back();     (* !! *)
    by (assume_tac 1);
    by (rtac (le_trans RS mp) 1);
    by (etac conjI 1);
    by (assume_tac 1);
qed "is_sup_assoc";


(** limits in linear orders **)

goalw thy [minimum_def, is_inf_def] "is_inf (x::'a::linear_order) y (minimum x y)";
  by (stac split_if 1);
  by (REPEAT_FIRST (resolve_tac [conjI, impI]));
  (*case "x [= y"*)
    by (rtac le_refl 1);
    by (assume_tac 1);
    by (Fast_tac 1);
  (*case "~ x [= y"*)
    by (rtac (le_linear RS disjE) 1);
    by (assume_tac 1);
    by (etac notE 1);
    by (assume_tac 1);
    by (rtac le_refl 1);
    by (Fast_tac 1);
qed "min_is_inf";

goalw thy [maximum_def, is_sup_def] "is_sup (x::'a::linear_order) y (maximum x y)";
  by (stac split_if 1);
  by (REPEAT_FIRST (resolve_tac [conjI, impI]));
  (*case "x [= y"*)
    by (assume_tac 1);
    by (rtac le_refl 1);
    by (Fast_tac 1);
  (*case "~ x [= y"*)
    by (rtac le_refl 1);
    by (rtac (le_linear RS disjE) 1);
    by (assume_tac 1);
    by (etac notE 1);
    by (assume_tac 1);
    by (Fast_tac 1);
qed "max_is_sup";



(** general vs. binary limits **)

goalw thy [is_inf_def, is_Inf_def] "is_Inf {x, y} inf = is_inf x y inf";
  by (rtac iffI 1);
  (*==>*)
    by (Fast_tac 1);
  (*<==*)
    by Safe_tac;
    by (Step_tac 1);
    by (etac mp 1);
    by (Fast_tac 1);
qed "bin_is_Inf_eq";

goalw thy [is_sup_def, is_Sup_def] "is_Sup {x, y} sup = is_sup x y sup";
  by (rtac iffI 1);
  (*==>*)
    by (Fast_tac 1);
  (*<==*)
    by Safe_tac;
    by (Step_tac 1);
    by (etac mp 1);
    by (Fast_tac 1);
qed "bin_is_Sup_eq";
