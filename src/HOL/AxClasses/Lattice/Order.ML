
open Order;


(** basic properties of limits **)

(* uniqueness *)

val tac =
  rtac impI 1 THEN
  rtac (le_antisym RS mp) 1 THEN
  fast_tac HOL_cs 1;


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
  by (fast_tac HOL_cs 1);
qed "is_inf_commut";

goalw thy [is_sup_def] "is_sup x y sup = is_sup y x sup";
  by (fast_tac HOL_cs 1);
qed "is_sup_commut";


(* associativity *)

goalw thy [is_inf_def] "is_inf x y xy & is_inf y z yz & is_inf xy z xyz --> is_inf x yz xyz";
  by (safe_tac HOL_cs);
  (*level 1*)
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
  (*level 4*)
    by (step_tac HOL_cs 1);
    back();
    be mp 1;
    br conjI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
    ba 1;
  (*level 11*)
    by (step_tac HOL_cs 1);
    back();
    back();
    be mp 1;
    br conjI 1;
    by (step_tac HOL_cs 1);
    be mp 1;
    be conjI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    back();     (* !! *)
    ba 1;
qed "is_inf_assoc";


goalw thy [is_sup_def] "is_sup x y xy & is_sup y z yz & is_sup xy z xyz --> is_sup x yz xyz";
  by (safe_tac HOL_cs);
  (*level 1*)
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
  (*level 4*)
    by (step_tac HOL_cs 1);
    back();
    be mp 1;
    br conjI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
    ba 1;
  (*level 11*)
    by (step_tac HOL_cs 1);
    back();
    back();
    be mp 1;
    br conjI 1;
    by (step_tac HOL_cs 1);
    be mp 1;
    be conjI 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    back();     (* !! *)
    ba 1;
    br (le_trans RS mp) 1;
    be conjI 1;
    ba 1;
qed "is_sup_assoc";


(** limits in linear orders **)

goalw thy [minimum_def, is_inf_def] "is_inf (x::'a::lin_order) y (minimum x y)";
  by (stac expand_if 1);
  by (REPEAT_FIRST (resolve_tac [conjI, impI]));
  (*case "x [= y"*)
    br le_refl 1;
    ba 1;
    by (fast_tac HOL_cs 1);
  (*case "~ x [= y"*)
    br (le_lin RS disjE) 1;
    ba 1;
    be notE 1;
    ba 1;
    br le_refl 1;
    by (fast_tac HOL_cs 1);
qed "min_is_inf";

goalw thy [maximum_def, is_sup_def] "is_sup (x::'a::lin_order) y (maximum x y)";
  by (stac expand_if 1);
  by (REPEAT_FIRST (resolve_tac [conjI, impI]));
  (*case "x [= y"*)
    ba 1;
    br le_refl 1;
    by (fast_tac HOL_cs 1);
  (*case "~ x [= y"*)
    br le_refl 1;
    br (le_lin RS disjE) 1;
    ba 1;
    be notE 1;
    ba 1;
    by (fast_tac HOL_cs 1);
qed "max_is_sup";



(** general vs. binary limits **)

goalw thy [is_inf_def, is_Inf_def] "is_Inf {x, y} inf = is_inf x y inf";
  br iffI 1;
  (*==>*)
    by (fast_tac set_cs 1);
  (*<==*)
    by (safe_tac set_cs);
    by (step_tac set_cs 1);
    be mp 1;
    by (fast_tac set_cs 1);
qed "bin_is_Inf_eq";

goalw thy [is_sup_def, is_Sup_def] "is_Sup {x, y} sup = is_sup x y sup";
  br iffI 1;
  (*==>*)
    by (fast_tac set_cs 1);
  (*<==*)
    by (safe_tac set_cs);
    by (step_tac set_cs 1);
    be mp 1;
    by (fast_tac set_cs 1);
qed "bin_is_Sup_eq";
