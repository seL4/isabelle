(*  Title:      HOL/AxClasses/Group/Group.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some basic theorems of group theory.
*)

open Group;

fun sub r = standard (r RS subst);
fun ssub r = standard (r RS ssubst);


goal thy "x * inv x = (1::'a::group)";
br (sub left_unit) 1;
back();
br (sub assoc) 1;
br (sub left_inv) 1;
back();
back();
br (ssub assoc) 1;
back();
br (ssub left_inv) 1;
br (ssub assoc) 1;
br (ssub left_unit) 1;
br (ssub left_inv) 1;
br refl 1;
qed "right_inv";


goal thy "x * 1 = (x::'a::group)";
br (sub left_inv) 1;
br (sub assoc) 1;
br (ssub right_inv) 1;
br (ssub left_unit) 1;
br refl 1;
qed "right_unit";


goal thy "e * x = x --> e = (1::'a::group)";
br impI 1;
br (sub right_unit) 1;
back();
by (res_inst_tac [("x", "x")] (sub right_inv) 1);
br (sub assoc) 1;
br arg_cong 1;
back();
ba 1;
qed "strong_one_unit";


goal thy "EX! e. ALL x. e * x = (x::'a::group)";
br ex1I 1;
br allI 1;
br left_unit 1;
br mp 1;
br strong_one_unit 1;
be allE 1;
ba 1;
qed "ex1_unit";


goal thy "ALL x. EX! e. e * x = (x::'a::group)";
br allI 1;
br ex1I 1;
br left_unit 1;
br (strong_one_unit RS mp) 1;
ba 1;
qed "ex1_unit'";


goal thy "inj (op * (x::'a::group))";
br injI 1;
br (sub left_unit) 1;
back();
br (sub left_unit) 1;
by (res_inst_tac [("x", "x")] (sub left_inv) 1);
br (ssub assoc) 1;
back();
br (ssub assoc) 1;
br arg_cong 1;
back();
ba 1;
qed "inj_times";


goal thy "y * x = 1 --> y = inv (x::'a::group)";
br impI 1;
br (sub right_unit) 1;
back();
back();
br (sub right_unit) 1;
by (res_inst_tac [("x", "x")] (sub right_inv) 1);
br (sub assoc) 1;
br (sub assoc) 1;
br arg_cong 1;
back();
br (ssub left_inv) 1;
ba 1;
qed "one_inv";


goal thy "ALL x. EX! y. y * x = (1::'a::group)";
br allI 1;
br ex1I 1;
br left_inv 1;
br mp 1;
br one_inv 1;
ba 1;
qed "ex1_inv";


goal thy "inv (x * y) = inv y * inv (x::'a::group)";
br sym 1;
br mp 1;
br one_inv 1;
br (ssub assoc) 1;
br (sub assoc) 1;
back();
br (ssub left_inv) 1;
br (ssub left_unit) 1;
br (ssub left_inv) 1;
br refl 1;
qed "inv_times";


goal thy "inv (inv x) = (x::'a::group)";
br sym 1;
br (one_inv RS mp) 1;
br (ssub right_inv) 1;
br refl 1;
qed "inv_inv";
