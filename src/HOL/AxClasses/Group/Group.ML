(*  Title:      HOL/AxClasses/Group/Group.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some basic theorems of group theory.
*)

open Group;

fun sub r = standard (r RS subst);
fun ssub r = standard (r RS ssubst);


goal thy "x * inv x = (1::'a::group)";
by (rtac (sub left_unit) 1);
back();
by (rtac (sub assoc) 1);
by (rtac (sub left_inv) 1);
back();
back();
by (rtac (ssub assoc) 1);
back();
by (rtac (ssub left_inv) 1);
by (rtac (ssub assoc) 1);
by (rtac (ssub left_unit) 1);
by (rtac (ssub left_inv) 1);
by (rtac refl 1);
qed "right_inv";


goal thy "x * 1 = (x::'a::group)";
by (rtac (sub left_inv) 1);
by (rtac (sub assoc) 1);
by (rtac (ssub right_inv) 1);
by (rtac (ssub left_unit) 1);
by (rtac refl 1);
qed "right_unit";


goal thy "e * x = x --> e = (1::'a::group)";
by (rtac impI 1);
by (rtac (sub right_unit) 1);
back();
by (res_inst_tac [("x", "x")] (sub right_inv) 1);
by (rtac (sub assoc) 1);
by (rtac arg_cong 1);
back();
by (assume_tac 1);
qed "strong_one_unit";


goal thy "EX! e. ALL x. e * x = (x::'a::group)";
by (rtac ex1I 1);
by (rtac allI 1);
by (rtac left_unit 1);
by (rtac mp 1);
by (rtac strong_one_unit 1);
by (etac allE 1);
by (assume_tac 1);
qed "ex1_unit";


goal thy "ALL x. EX! e. e * x = (x::'a::group)";
by (rtac allI 1);
by (rtac ex1I 1);
by (rtac left_unit 1);
by (rtac (strong_one_unit RS mp) 1);
by (assume_tac 1);
qed "ex1_unit'";


goal thy "inj (op * (x::'a::group))";
by (rtac injI 1);
by (rtac (sub left_unit) 1);
back();
by (rtac (sub left_unit) 1);
by (res_inst_tac [("x", "x")] (sub left_inv) 1);
by (rtac (ssub assoc) 1);
back();
by (rtac (ssub assoc) 1);
by (rtac arg_cong 1);
back();
by (assume_tac 1);
qed "inj_times";


goal thy "y * x = 1 --> y = inv (x::'a::group)";
by (rtac impI 1);
by (rtac (sub right_unit) 1);
back();
back();
by (rtac (sub right_unit) 1);
by (res_inst_tac [("x", "x")] (sub right_inv) 1);
by (rtac (sub assoc) 1);
by (rtac (sub assoc) 1);
by (rtac arg_cong 1);
back();
by (rtac (ssub left_inv) 1);
by (assume_tac 1);
qed "one_inv";


goal thy "ALL x. EX! y. y * x = (1::'a::group)";
by (rtac allI 1);
by (rtac ex1I 1);
by (rtac left_inv 1);
by (rtac mp 1);
by (rtac one_inv 1);
by (assume_tac 1);
qed "ex1_inv";


goal thy "inv (x * y) = inv y * inv (x::'a::group)";
by (rtac sym 1);
by (rtac mp 1);
by (rtac one_inv 1);
by (rtac (ssub assoc) 1);
by (rtac (sub assoc) 1);
back();
by (rtac (ssub left_inv) 1);
by (rtac (ssub left_unit) 1);
by (rtac (ssub left_inv) 1);
by (rtac refl 1);
qed "inv_times";


goal thy "inv (inv x) = (x::'a::group)";
by (rtac sym 1);
by (rtac (one_inv RS mp) 1);
by (rtac (ssub right_inv) 1);
by (rtac refl 1);
qed "inv_inv";
