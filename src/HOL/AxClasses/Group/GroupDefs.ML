(* bool *)

(*this is really overkill - should be rather proven 'inline'*)

Goalw [times_bool_def] "(x * y) * z = x * (y * (z::bool))";
by (Fast_tac 1);
qed "bool_assoc";

Goalw [times_bool_def, one_bool_def] "1 * x = (x::bool)";
by (Fast_tac 1);
qed "bool_left_unit";

Goalw [times_bool_def, one_bool_def] "x * 1 = (x::bool)";
by (Fast_tac 1);
qed "bool_right_unit";

Goalw [times_bool_def, inverse_bool_def, one_bool_def]
  "inverse(x) * x = (1::bool)";
by (Fast_tac 1);
qed "bool_left_inverse";

Goalw [times_bool_def] "x * y = (y * (x::bool))";
by (Fast_tac 1);
qed "bool_commut";


(* cartesian products *)

val prod_ss = simpset_of Prod.thy;

Goalw [times_prod_def]
  "(x * y) * z = x * (y * (z::'a::semigroup*'b::semigroup))";
by (simp_tac (prod_ss addsimps [assoc]) 1);
qed "prod_assoc";

Goalw [times_prod_def, one_prod_def] "1 * x = (x::'a::monoid*'b::monoid)";
by (simp_tac (prod_ss addsimps [Monoid.left_unit]) 1);
qed "prod_left_unit";

Goalw [times_prod_def, one_prod_def] "x * 1 = (x::'a::monoid*'b::monoid)";
by (simp_tac (prod_ss addsimps [Monoid.right_unit]) 1);
qed "prod_right_unit";

Goalw [times_prod_def, inverse_prod_def, one_prod_def]
  "inverse x * x = (1::'a::group*'b::group)";
by (simp_tac (prod_ss addsimps [left_inverse]) 1);
qed "prod_left_inverse";

Goalw [times_prod_def] "x * y = y * (x::'a::agroup*'b::agroup)";
by (simp_tac (prod_ss addsimps [commut]) 1);
qed "prod_commut";


(* function spaces *)

Goalw [times_fun_def] "(x * y) * z = x * (y * (z::'a => 'b::semigroup))";
by (stac expand_fun_eq 1);
by (rtac allI 1);
by (rtac assoc 1);
qed "fun_assoc";

Goalw [times_fun_def, one_fun_def] "1 * x = (x::'a => 'b::monoid)";
by (stac expand_fun_eq 1);
by (rtac allI 1);
by (rtac Monoid.left_unit 1);
qed "fun_left_unit";

Goalw [times_fun_def, one_fun_def] "x * 1 = (x::'a => 'b::monoid)";
by (stac expand_fun_eq 1);
by (rtac allI 1);
by (rtac Monoid.right_unit 1);
qed "fun_right_unit";

Goalw [times_fun_def, inverse_fun_def, one_fun_def]
  "inverse x * x = (1::'a => 'b::group)";
by (stac expand_fun_eq 1);
by (rtac allI 1);
by (rtac left_inverse 1);
qed "fun_left_inverse";

Goalw [times_fun_def] "x * y = y * (x::'a => 'b::agroup)";
by (stac expand_fun_eq 1);
by (rtac allI 1);
by (rtac commut 1);
qed "fun_commut";
