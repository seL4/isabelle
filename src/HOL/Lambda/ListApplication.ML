(*  Title:      HOL/Lambda/ListApplication.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TU Muenchen
*)

Goal "(r$$ts = s$$ts) = (r = s)";
by (rev_induct_tac "ts" 1);
by (Auto_tac);
qed "apps_eq_tail_conv";
AddIffs [apps_eq_tail_conv];

Goal "!s. (Var m = s$$ss) = (Var m = s & ss = [])";
by (induct_tac "ss" 1);
by (Auto_tac);
qed_spec_mp "Var_eq_apps_conv";
AddIffs [Var_eq_apps_conv];

Goal "!ss. ((Var m)$$rs = (Var n)$$ss) = (m=n & rs=ss)";
by (rev_induct_tac "rs" 1);
 by (Simp_tac 1);
 by (Blast_tac 1);
by (rtac allI 1);
by (rev_induct_tac "ss" 1);
by (Auto_tac);
qed_spec_mp "Var_apps_eq_Var_apps_conv";
AddIffs [Var_apps_eq_Var_apps_conv];

Goal "(r$s = t$$ts) = \
\     (if ts = [] then r$s = t \
\      else (? ss. ts = ss@[s] & r = t$$ss))";
by (res_inst_tac [("xs","ts")] rev_exhaust 1);
by (Auto_tac);
qed "App_eq_foldl_conv";

Goal "(Abs r = s$$ss) = (Abs r = s & ss=[])";
by (rev_induct_tac "ss" 1);
by (Auto_tac);
qed "Abs_eq_apps_conv";
AddIffs [Abs_eq_apps_conv];

Goal "(s$$ss = Abs r) = (s = Abs r & ss=[])";
by (rev_induct_tac "ss" 1);
by (Auto_tac);
qed "apps_eq_Abs_conv";
AddIffs [apps_eq_Abs_conv];

Goal "!ss. ((Abs r)$$rs = (Abs s)$$ss) = (r=s & rs=ss)";
by (rev_induct_tac "rs" 1);
 by (Simp_tac 1);
 by (Blast_tac 1);
by (rtac allI 1);
by (rev_induct_tac "ss" 1);
by (Auto_tac);
qed_spec_mp "Abs_apps_eq_Abs_apps_conv";
AddIffs [Abs_apps_eq_Abs_apps_conv];

Goal "!s t. Abs s $ t ~= (Var n)$$ss";
by (rev_induct_tac "ss" 1);
by (Auto_tac);
qed_spec_mp "Abs_App_neq_Var_apps";
AddIffs [Abs_App_neq_Var_apps];

Goal "!ts. Var n $$ ts ~= (Abs r)$$ss";
by (rev_induct_tac "ss" 1);
 by (Simp_tac 1);
by (rtac allI 1);
by (rev_induct_tac "ts" 1);
by (Auto_tac);
qed_spec_mp "Var_apps_neq_Abs_apps";
AddIffs [Var_apps_neq_Abs_apps];

Goal "? ts h. t = h$$ts & ((? n. h = Var n) | (? u. h = Abs u))";
by (induct_tac "t" 1);
  by (res_inst_tac[("x","[]")] exI 1);
  by (Simp_tac 1);
 by (Clarify_tac 1);
 by (rename_tac "ts1 ts2 h1 h2" 1);
 by (res_inst_tac[("x","ts1@[h2$$ts2]")] exI 1);
 by (Simp_tac 1);
by (Simp_tac 1);
qed "ex_head_tail";

Goal "size(r$$rs) = size r + foldl (op +) 0 (map size rs) + length rs";
by (rev_induct_tac "rs" 1);
by (Auto_tac);
qed "size_apps";
Addsimps [size_apps];

Goal "[| (0::nat) < k; m <= n |] ==> m < n+k";
by (fast_arith_tac 1);
val lemma0 = result();

(* a customized induction schema for $$ *)

val prems = Goal
"[| !!n ts. !t : set ts. P t ==> P((Var n)$$ts); \
\   !!u ts. [| P u; !t : set ts. P t |] ==> P((Abs u)$$ts) \
\|] ==> !t. size t = n --> P t";
by (res_inst_tac [("n","n")] less_induct 1);
by (rtac allI 1);
by (cut_inst_tac [("t","t")] ex_head_tail 1);
by (Clarify_tac 1);
by (etac disjE 1);
 by (Clarify_tac 1);
 by (resolve_tac prems 1);
 by (Clarify_tac 1);
 by (EVERY[etac allE 1, etac impE 1, etac allE 2, etac mp 2, rtac refl 2]);
 by (Simp_tac 1);
 by (rtac lemma0 1);
  by (Force_tac 1);
 by (rtac elem_le_sum 1);
 by (Force_tac 1);
by (Clarify_tac 1);
by (resolve_tac prems 1);
by (EVERY[etac allE 1, etac impE 1, etac allE 2, etac mp 2, rtac refl 2]);
by (Simp_tac 1);
by (Clarify_tac 1);
by (EVERY[etac allE 1, etac impE 1, etac allE 2, etac mp 2, rtac refl 2]);
by (Simp_tac 1);
by (rtac le_imp_less_Suc 1);
by (rtac trans_le_add1 1);
by (rtac trans_le_add2 1);
by (rtac elem_le_sum 1);
by (Force_tac 1);
val lemma = result() RS spec RS mp;

val prems = Goal
"[| !!n ts. !t : set ts. P t ==> P((Var n)$$ts); \
\   !!u ts. [| P u; !t : set ts. P t |] ==> P((Abs u)$$ts) \
\|] ==> P t";
by (res_inst_tac [("x1","t")] lemma 1);
by (rtac refl 3);
by (REPEAT(ares_tac prems 1));
qed "Apps_dB_induct";
