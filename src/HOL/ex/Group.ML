(*  Title:      HOL/Integ/Group.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997 TU Muenchen
*)

(*** Groups ***)

(* Derives the well-known convergent set of equations for groups
   based on the unary inverse 0-x.
*)

Goal "!!x::'a::add_group. (0-x)+(x+y) = y";
by (rtac trans 1);
by (rtac (plus_assoc RS sym) 1);
by (stac left_inv 1);
by (rtac zeroL 1);
qed "left_inv2";

Goal "!!x::'a::add_group. (0-(0-x)) = x";
by (rtac trans 1);
by (res_inst_tac [("x","0-x")] left_inv2 2);
by (stac left_inv 1);
by (rtac (zeroR RS sym) 1);
qed "inv_inv";

Goal "0-0 = (0::'a::add_group)";
by (rtac trans 1);
by (rtac (zeroR RS sym) 1);
by (rtac trans 1);
by (res_inst_tac [("x","0")] left_inv2 2);
by (simp_tac (simpset() addsimps [zeroR]) 1);
qed "inv_zero";

Goal "!!x::'a::add_group. x+(0-x) = 0";
by (rtac trans 1);
by (res_inst_tac [("x","0-x")] left_inv 2);
by (stac inv_inv 1);
by (rtac refl 1);
qed "right_inv";

Goal "!!x::'a::add_group. x+((0-x)+y) = y";
by (rtac trans 1);
by (res_inst_tac [("x","0-x")] left_inv2 2);
by (stac inv_inv 1);
by (rtac refl 1);
qed "right_inv2";

val plus_cong = read_instantiate [("f1","op +")] (arg_cong RS cong);

Goal "!!x::'a::add_group. 0-(x+y) = (0-y)+(0-x)";
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
  by (simp_tac (simpset() addsimps
        [plus_assoc,left_inv,left_inv2,right_inv,right_inv2]) 2);
 by (rtac refl 2);
by (rtac (zeroL RS sym) 1);
qed "inv_plus";

(*** convergent TRS for groups with unary inverse 0-x ***)
val group1_simps =
  [zeroL,zeroR,plus_assoc,left_inv,left_inv2,right_inv,right_inv2,inv_inv,
   inv_zero,inv_plus];

val group1_tac =
  let val ss = HOL_basic_ss addsimps group1_simps
  in simp_tac ss end;

(* I believe there is no convergent TRS for groups with binary `-',
   unless you have an extra unary `-' and simply define x-y = x+(-y).
   This does not work with only a binary `-' because x-y = x+(0-y) does
   not terminate. Hence we have a special tactic for converting all
   occurrences of x-y into x+(0-y):
*)

local
fun find(Const("op -",Type("fun",[T,_]))$s$t) = [(T,s,t)] @ find s @ find t
  | find(s$t) = find s @ find t
  | find _ = [];

fun subst_tac sg (tacf,(T,s,t)) = 
  let val typinst = [(("'a",0),ctyp_of sg T)];
      val terminst = [(cterm_of sg (Var(("x",0),T)),cterm_of sg s),
                      (cterm_of sg (Var(("y",0),T)),cterm_of sg t)];
  in tacf THEN' rtac ((instantiate(typinst,terminst) minus_inv) RS ssubst) end;

in
val mk_group1_tac = SUBGOAL(fn (t,i) => fn st =>
      let val sg = #sign(rep_thm st)
      in foldl (subst_tac sg) (K all_tac,find t) i st
      end)
end;

(* The following two equations are not used in any of the decision procedures,
   but are still very useful. They also demonstrate mk_group1_tac.
*)
Goal "x-x = (0::'a::add_group)";
by (mk_group1_tac 1);
by (group1_tac 1);
qed "minus_self_zero";

Goal "x-0 = (x::'a::add_group)";
by (mk_group1_tac 1);
by (group1_tac 1);
qed "minus_zero";

(*** Abelian Groups ***)

Goal "x+(y+z)=y+(x+z::'a::add_agroup)";
by (rtac trans 1);
by (rtac plus_commute 1);
by (rtac trans 1);
by (rtac plus_assoc 1);
by (simp_tac (simpset() addsimps [plus_commute]) 1);
qed "plus_commuteL";

(* Convergent TRS for Abelian groups with unary inverse 0-x.
   Requires ordered rewriting
*)

val agroup1_simps = plus_commute::plus_commuteL::group1_simps;

val agroup1_tac =
  let val ss = HOL_basic_ss addsimps agroup1_simps
  in simp_tac ss end;

(* Again, I do not believe there is a convergent TRS for Abelian Groups with
   binary `-'. However, we can still decide the word problem using additional
   rules for 
   1. floating `-' to the top:
      "x + (y - z) = (x + y) - (z::'a::add_group)"
      "(x - y) + z = (x + z) - (y::'a::add_agroup)"
      "(x - y) - z = x - (y + (z::'a::add_agroup))"
      "x - (y - z) = (x + z) - (y::'a::add_agroup)"
   2. and for moving `-' over to the other side:
      (x-y = z) = (x = z+y) and (x = y-z) = (x+z = y)
*)
Goal "x + (y - z) = (x + y) - (z::'a::add_group)";
by (mk_group1_tac 1);
by (group1_tac 1);
qed "plus_minusR";

Goal "(x - y) + z = (x + z) - (y::'a::add_agroup)";
by (mk_group1_tac 1);
by (agroup1_tac 1);
qed "plus_minusL";

Goal "(x - y) - z = x - (y + (z::'a::add_agroup))";
by (mk_group1_tac 1);
by (agroup1_tac 1);
qed "minus_minusL";

Goal "x - (y - z) = (x + z) - (y::'a::add_agroup)";
by (mk_group1_tac 1);
by (agroup1_tac 1);
qed "minus_minusR";

Goal "!!x::'a::add_group. (x-y = z) = (x = z+y)";
by (stac minus_inv 1);
by (fast_tac (claset() addss (HOL_basic_ss addsimps group1_simps)) 1);
qed "minusL_iff";

Goal "!!x::'a::add_group. (x = y-z) = (x+z = y)";
by (stac minus_inv 1);
by (fast_tac (claset() addss (HOL_basic_ss addsimps group1_simps)) 1);
qed "minusR_iff";

val agroup2_simps =
  [zeroL,zeroR,plus_assoc,plus_commute,plus_commuteL,
   plus_minusR,plus_minusL,minus_minusL,minus_minusR,minusL_iff,minusR_iff];

(* This two-phase ordered rewriting tactic works, but agroup_simps are
   simpler. However, agroup_simps is not confluent for arbitrary terms,
   it merely decides equality.
(* Phase 1 *)

Goal "!!x::'a::add_agroup. (x+(0-y))+z = (x+z)+(0-y)";
by (Simp_tac 1);
val lemma = result();
bind_thm("plus_minusL",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

Goal "!!x::'a::add_agroup. x+(0-(y+z)) = (x+(0-y))+(0-z)";
by (Simp_tac 1);
val lemma = result();
bind_thm("minus_plusR",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

Goal "!!x::'a::add_agroup. x+(0-(y+(0-z))) = (x+z)+(0-y)";
by (Simp_tac 1);
val lemma = result();
bind_thm("minus_minusR",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

Goal "!!x::'a::add_agroup. x+(y+(0-z)) = (x+y)+(0-z)";
by (Simp_tac 1);
val lemma = result();
bind_thm("plus_minusR",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

(* Phase 2 *)

Goal "!!x::'a::add_agroup. (x+y)+(0-z) = x+(y+(0-z))";
by (Simp_tac 1);
val lemma = result();
bind_thm("minus_plusL2",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

Goal "!!x::'a::add_agroup. (x+y)+(0-x) = y";
by (rtac (plus_assoc RS trans) 1);
by (rtac trans 1);
 by (rtac plus_cong 1);
  by (rtac refl 1);
 by (rtac right_inv2 2);
by (rtac plus_commute 1);
val lemma = result();
bind_thm("minus_plusL3",rewrite_rule[minus_inv RS sym RS eq_reflection]lemma);

*)
