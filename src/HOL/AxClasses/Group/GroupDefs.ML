
open GroupDefs;


(* bool *)

(*this is really overkill - should be rather proven 'inline'*)

goalw thy [times_bool_def] "(x * y) * z = x * (y * (z::bool))";
by (fast_tac HOL_cs 1);
qed "bool_assoc";

goalw thy [times_bool_def, one_bool_def] "1 * x = (x::bool)";
by (fast_tac HOL_cs 1);
qed "bool_left_unit";

goalw thy [times_bool_def, one_bool_def] "x * 1 = (x::bool)";
by (fast_tac HOL_cs 1);
qed "bool_right_unit";

goalw thy [times_bool_def, inv_bool_def, one_bool_def] "inv(x) * x = (1::bool)";
by (fast_tac HOL_cs 1);
qed "bool_left_inv";

goalw thy [times_bool_def] "x * y = (y * (x::bool))";
by (fast_tac HOL_cs 1);
qed "bool_commut";


(* cartesian products *)

val prod_ss = simpset_of "Prod";

goalw thy [times_prod_def] "(x * y) * z = x * (y * (z::'a::semigroup*'b::semigroup))";
by (simp_tac (prod_ss addsimps [assoc]) 1);
qed "prod_assoc";

goalw thy [times_prod_def, one_prod_def] "1 * x = (x::'a::monoid*'b::monoid)";
by (simp_tac (prod_ss addsimps [Monoid.left_unit]) 1);
br (surjective_pairing RS sym) 1;
qed "prod_left_unit";

goalw thy [times_prod_def, one_prod_def] "x * 1 = (x::'a::monoid*'b::monoid)";
by (simp_tac (prod_ss addsimps [Monoid.right_unit]) 1);
br (surjective_pairing RS sym) 1;
qed "prod_right_unit";

goalw thy [times_prod_def, inv_prod_def, one_prod_def] "inv x * x = (1::'a::group*'b::group)";
by (simp_tac (prod_ss addsimps [left_inv]) 1);
qed "prod_left_inv";

goalw thy [times_prod_def] "x * y = y * (x::'a::agroup*'b::agroup)";
by (simp_tac (prod_ss addsimps [commut]) 1);
qed "prod_commut";


(* function spaces *)

goalw thy [times_fun_def] "(x * y) * z = x * (y * (z::'a => 'b::semigroup))";
by (stac expand_fun_eq 1);
br allI 1;
br assoc 1;
qed "fun_assoc";

goalw thy [times_fun_def, one_fun_def] "1 * x = (x::'a => 'b::monoid)";
by (stac expand_fun_eq 1);
br allI 1;
br Monoid.left_unit 1;
qed "fun_left_unit";

goalw thy [times_fun_def, one_fun_def] "x * 1 = (x::'a => 'b::monoid)";
by (stac expand_fun_eq 1);
br allI 1;
br Monoid.right_unit 1;
qed "fun_right_unit";

goalw thy [times_fun_def, inv_fun_def, one_fun_def] "inv x * x = (1::'a => 'b::group)";
by (stac expand_fun_eq 1);
br allI 1;
br left_inv 1;
qed "fun_left_inv";

goalw thy [times_fun_def] "x * y = y * (x::'a => 'b::agroup)";
by (stac expand_fun_eq 1);
br allI 1;
br commut 1;
qed "fun_commut";
