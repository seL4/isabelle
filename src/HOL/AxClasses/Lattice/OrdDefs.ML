
open OrdDefs;


(** lifting of quasi / partial orders **)

(* pairs *)

goalw thy [le_prod_def] "x [= (x::'a::quasi_order*'b::quasi_order)";
  br conjI 1;
  br le_refl 1;
  br le_refl 1;
qed "le_prod_refl";

goalw thy [le_prod_def] "x [= y & y [= z --> x [= (z::'a::quasi_order*'b::quasi_order)";
  by (safe_tac HOL_cs);
  be (conjI RS (le_trans RS mp)) 1;
  ba 1;
  be (conjI RS (le_trans RS mp)) 1;
  ba 1;
qed "le_prod_trans";

goalw thy [le_prod_def] "x [= y & y [= x --> x = (y::'a::order*'b::order)";
  by (safe_tac HOL_cs);
  by (stac Pair_fst_snd_eq 1);
  br conjI 1;
  be (conjI RS (le_antisym RS mp)) 1;
  ba 1;
  be (conjI RS (le_antisym RS mp)) 1;
  ba 1;
qed "le_prod_antisym";


(* functions *)

goalw thy [le_fun_def] "f [= (f::'a=>'b::quasi_order)";
  br allI 1;
  br le_refl 1;
qed "le_fun_refl";

goalw thy [le_fun_def] "f [= g & g [= h --> f [= (h::'a=>'b::quasi_order)";
  by (safe_tac HOL_cs);
  br (le_trans RS mp) 1;
  by (fast_tac HOL_cs 1);
qed "le_fun_trans";

goalw thy [le_fun_def] "f [= g & g [= f --> f = (g::'a=>'b::order)";
  by (safe_tac HOL_cs);
  br ext 1;
  br (le_antisym RS mp) 1;
  by (fast_tac HOL_cs 1);
qed "le_fun_antisym";



(** duals **)

(*"'a dual" is even an isotype*)
goal thy "Rep_dual (Abs_dual y) = y";
  br Abs_dual_inverse 1;
  by (rewrite_goals_tac [dual_def]);
  by (fast_tac set_cs 1);
qed "Abs_dual_inverse'";


goalw thy [le_dual_def] "x [= (x::'a::quasi_order dual)";
  br le_refl 1;
qed "le_dual_refl";

goalw thy [le_dual_def] "x [= y & y [= z --> x [= (z::'a::quasi_order dual)";
  by (stac conj_commut 1);
  br le_trans 1;
qed "le_dual_trans";

goalw thy [le_dual_def] "x [= y & y [= x --> x = (y::'a::order dual)";
  by (safe_tac prop_cs);
  br (Rep_dual_inverse RS subst) 1;
  br sym 1;
  br (Rep_dual_inverse RS subst) 1;
  br arg_cong 1;
  back();
  be (conjI RS (le_antisym RS mp)) 1;
  ba 1;
qed "le_dual_antisym";

goalw thy [le_dual_def] "x [= y | y [= (x::'a::lin_order dual)";
  br le_lin 1;
qed "le_dual_lin";
