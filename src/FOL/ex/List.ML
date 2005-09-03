(*  Title:      FOL/ex/list
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge
*)

val prems = goal (the_context ()) "[| P([]);  !!x l. P(x . l) |] ==> All(P)";
by (rtac list_ind 1);
by (REPEAT (resolve_tac (prems@[allI,impI]) 1));
qed "list_exh";

Addsimps [list_distinct1, list_distinct2, app_nil, app_cons,
	  hd_eq, tl_eq, forall_nil, forall_cons, list_free,
	  len_nil, len_cons, at_0, at_succ];

Goal "~l=[] --> hd(l).tl(l) = l";
by (IND_TAC list_exh Simp_tac "l" 1);
result();

Goal "(l1++l2)++l3 = l1++(l2++l3)";
by (IND_TAC list_ind Simp_tac "l1" 1);
qed "append_assoc";

Goal "l++[] = l";
by (IND_TAC list_ind Simp_tac "l" 1);
qed "app_nil_right";

Goal "l1++l2=[] <-> l1=[] & l2=[]";
by (IND_TAC list_exh Simp_tac "l1" 1);
qed "app_eq_nil_iff";

Goal "forall(l++l',P) <-> forall(l,P) & forall(l',P)";
by (IND_TAC list_ind Simp_tac "l" 1);
qed "forall_app";

Goal "forall(l,%x. P(x)&Q(x)) <-> forall(l,P) & forall(l,Q)";
by (IND_TAC list_ind Simp_tac "l" 1);
by (Fast_tac 1);
qed "forall_conj";

Goal "~l=[] --> forall(l,P) <-> P(hd(l)) & forall(tl(l),P)";
by (IND_TAC list_ind Simp_tac "l" 1);
qed "forall_ne";

(*** Lists with natural numbers ***)

Goal "len(l1++l2) = len(l1)+len(l2)";
by (IND_TAC list_ind Simp_tac "l1" 1);
qed "len_app";

Goal "i<len(l1) --> at(l1++l2,i) = at(l1,i)";
by (IND_TAC list_ind Simp_tac "l1" 1);
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (ALL_IND_TAC nat_exh Asm_simp_tac 1);
qed "at_app1";

Goal "at(l1++(x . l2), len(l1)) = x";
by (IND_TAC list_ind Simp_tac "l1" 1);
qed "at_app_hd2";
