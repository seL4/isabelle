(*  Title:      HOL/Integ/Group.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TU Muenchen
*)

open Group;

Addsimps [zeroL,zeroR,plus_assoc,plus_commute];

goal Group.thy "!!x::'a::add_group. (zero-x)+(x+y) = y";
by (rtac trans 1);
by (rtac (plus_assoc RS sym) 1);
by (stac left_inv 1);
by (rtac zeroL 1);
qed "left_inv2";

goal Group.thy "!!x::'a::add_group. (zero-(zero-x)) = x";
by (rtac trans 1);
by (res_inst_tac [("x","zero-x")] left_inv2 2);
by (stac left_inv 1);
by (rtac (zeroR RS sym) 1);
qed "inv_inv";

goal Group.thy "zero-zero = (zero::'a::add_group)";
by (rtac trans 1);
by (rtac (zeroR RS sym) 1);
by (rtac trans 1);
by (res_inst_tac [("x","zero")] left_inv2 2);
by (Simp_tac 1);
qed "inv_zero";

goal Group.thy "!!x::'a::add_group. x+(zero-x) = zero";
by (rtac trans 1);
by (res_inst_tac [("x","zero-x")] left_inv 2);
by (stac inv_inv 1);
by (rtac refl 1);
qed "right_inv";

goal Group.thy "!!x::'a::add_group. x+((zero-x)+y) = y";
by (rtac trans 1);
by (res_inst_tac [("x","zero-x")] left_inv2 2);
by (stac inv_inv 1);
by (rtac refl 1);
qed "right_inv2";

goal Group.thy "!!x::'a::add_group. x-x = zero";
by (stac minus_inv 1);
by (rtac right_inv 1);
qed "minus_self_zero";
Addsimps [minus_self_zero];

goal Group.thy "!!x::'a::add_group. x-zero = x";
by (stac minus_inv 1);
by (stac inv_zero 1);
by (rtac zeroR 1);
qed "minus_zero";
Addsimps [minus_zero];

val plus_cong = read_instantiate [("f1","op +")] (arg_cong RS cong);

goal Group.thy "!!x::'a::add_group. zero-(x+y) = (zero-y)+(zero-x)";
by (rtac trans 1);
 by (rtac zeroR 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (rtac refl 2);
 by (res_inst_tac [("x","x+y")] right_inv 2);
by (rtac trans 1);
 by (rtac plus_assoc 2);
by (rtac trans 1);
 by (rtac plus_cong 2);
  by (simp_tac (!simpset addsimps [left_inv,left_inv2,right_inv,right_inv2]) 2);
 by (rtac refl 2);
by (rtac (zeroL RS sym) 1);
qed "inv_plus";

goal Group.thy "x+(y+z)=y+(x+z::'a::add_agroup)";
by (rtac trans 1);
by (rtac plus_commute 1);
by (rtac trans 1);
by (rtac plus_assoc 1);
by (Simp_tac 1);
qed "plus_commuteL";
Addsimps [plus_commuteL];

Addsimps [inv_inv,inv_plus];

(* Phase 1 *)

goal Group.thy "!!x::'a::add_agroup. (x+(zero-y))+z = (x+z)+(zero-y)";
by (Simp_tac 1);
val lemma = result();
bind_thm("plus_minusL",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

goal Group.thy "!!x::'a::add_agroup. x+(zero-(y+z)) = (x+(zero-y))+(zero-z)";
by (Simp_tac 1);
val lemma = result();
bind_thm("minus_plusR",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

goal Group.thy "!!x::'a::add_agroup. x+(zero-(y+(zero-z))) = (x+z)+(zero-y)";
by (Simp_tac 1);
val lemma = result();
bind_thm("minus_minusR",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

goal Group.thy "!!x::'a::add_agroup. x+(y+(zero-z)) = (x+y)+(zero-z)";
by (Simp_tac 1);
val lemma = result();
bind_thm("plus_minusR",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

(* Phase 2 *)

goal Group.thy "!!x::'a::add_agroup. (x+y)+(zero-z) = x+(y+(zero-z))";
by (Simp_tac 1);
val lemma = result();
bind_thm("minus_plusL2",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

goal Group.thy "!!x::'a::add_agroup. (x+y)+(zero-x) = y";
by (rtac (plus_assoc RS trans) 1);
by (rtac trans 1);
 by (rtac plus_cong 1);
  by (rtac refl 1);
 by (rtac right_inv2 2);
by (rtac plus_commute 1);
val lemma = result();
bind_thm("minus_plusL3",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

