
open OrdDefs;


(** lifting of quasi / partial orders **)

(* pairs *)

goalw thy [le_prod_def] "x [= (x::'a::quasi_order*'b::quasi_order)";
  by (rtac conjI 1);
  by (rtac le_refl 1);
  by (rtac le_refl 1);
qed "le_prod_refl";

goalw thy [le_prod_def] "x [= y & y [= z --> x [= (z::'a::quasi_order*'b::quasi_order)";
  by Safe_tac;
  by (etac (conjI RS (le_trans RS mp)) 1);
  by (assume_tac 1);
  by (etac (conjI RS (le_trans RS mp)) 1);
  by (assume_tac 1);
qed "le_prod_trans";

goalw thy [le_prod_def] "x [= y & y [= x --> x = (y::'a::partial_order*'b::partial_order)";
  by Safe_tac;
  by (stac Pair_fst_snd_eq 1);
  by (rtac conjI 1);
  by (etac (conjI RS (le_antisym RS mp)) 1);
  by (assume_tac 1);
  by (etac (conjI RS (le_antisym RS mp)) 1);
  by (assume_tac 1);
qed "le_prod_antisym";


(* functions *)

goalw thy [le_fun_def] "f [= (f::'a=>'b::quasi_order)";
  by (rtac allI 1);
  by (rtac le_refl 1);
qed "le_fun_refl";

goalw thy [le_fun_def] "f [= g & g [= h --> f [= (h::'a=>'b::quasi_order)";
  by Safe_tac;
  by (rtac (le_trans RS mp) 1);
  by (Fast_tac 1);
qed "le_fun_trans";

goalw thy [le_fun_def] "f [= g & g [= f --> f = (g::'a=>'b::partial_order)";
  by Safe_tac;
  by (rtac ext 1);
  by (rtac (le_antisym RS mp) 1);
  by (Fast_tac 1);
qed "le_fun_antisym";



(** duals **)

(*"'a dual" is even an isotype*)
goal thy "Rep_dual (Abs_dual y) = y";
  by (rtac Abs_dual_inverse 1);
  by (rewtac dual_def);
  by (Fast_tac 1);
qed "Abs_dual_inverse'";


goalw thy [le_dual_def] "x [= (x::'a::quasi_order dual)";
  by (rtac le_refl 1);
qed "le_dual_refl";

goalw thy [le_dual_def] "x [= y & y [= z --> x [= (z::'a::quasi_order dual)";
  by (stac conj_commut 1);
  by (rtac le_trans 1);
qed "le_dual_trans";

goalw thy [le_dual_def] "x [= y & y [= x --> x = (y::'a::partial_order dual)";
  by Safe_tac;
  by (rtac (Rep_dual_inverse RS subst) 1);
  by (rtac sym 1);
  by (rtac (Rep_dual_inverse RS subst) 1);
  by (rtac arg_cong 1);
  back();
  by (etac (conjI RS (le_antisym RS mp)) 1);
  by (assume_tac 1);
qed "le_dual_antisym";

goalw thy [le_dual_def] "x [= y | y [= (x::'a::linear_order dual)";
  by (rtac le_linear 1);
qed "le_dual_linear";
