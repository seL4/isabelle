(*  Title:      HOLCF/Ssum1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Partial ordering for the strict sum ++
*)

local 

fun eq_left s1 s2 = 
        (
        (res_inst_tac [("s",s1),("t",s2)] (inject_Isinl RS subst) 1)
        THEN    (rtac trans 1)
        THEN    (atac 2)
        THEN    (etac sym 1));

fun eq_right s1 s2 = 
        (
        (res_inst_tac [("s",s1),("t",s2)] (inject_Isinr RS subst) 1)
        THEN    (rtac trans 1)
        THEN    (atac 2)
        THEN    (etac sym 1));

fun UU_left s1 = 
        (
        (res_inst_tac [("t",s1)](noteq_IsinlIsinr RS conjunct1 RS ssubst)1)
        THEN (rtac trans 1)
        THEN (atac 2)
        THEN (etac sym 1));

fun UU_right s1 = 
        (
        (res_inst_tac [("t",s1)](noteq_IsinlIsinr RS conjunct2 RS ssubst)1)
        THEN (rtac trans 1)
        THEN (atac 2)
        THEN (etac sym 1))

in

val less_ssum1a = prove_goalw thy [less_ssum_def]
"[|s1=Isinl(x::'a); s2=Isinl(y::'a)|] ==> s1 << s2 = (x << y)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac select_equality 1),
        (dtac conjunct1 2),
        (dtac spec 2),
        (dtac spec 2),
        (etac mp 2),
        (fast_tac HOL_cs 2),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_left "x" "u"),
        (eq_left "y" "xa"),
        (rtac refl 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_left "x"),
        (UU_right "v"),
        (Simp_tac 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_left "x" "u"),
        (UU_left "y"),
        (rtac iffI 1),
        (etac UU_I 1),
        (res_inst_tac [("s","x"),("t","UU::'a")] subst 1),
        (atac 1),
        (rtac refl_less 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_left "x"),
        (UU_right "v"),
        (Simp_tac 1)
        ]);


val less_ssum1b = prove_goalw thy [less_ssum_def]
"[|s1=Isinr(x::'b); s2=Isinr(y::'b)|] ==> s1 << s2 = (x << y)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac select_equality 1),
        (dtac conjunct2 2),
        (dtac conjunct1 2),
        (dtac spec 2),
        (dtac spec 2),
        (etac mp 2),
        (fast_tac HOL_cs 2),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_right "x"),
        (UU_left "u"),
        (Simp_tac 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_right "x" "v"),
        (eq_right "y" "ya"),
        (rtac refl 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_right "x"),
        (UU_left "u"),
        (Simp_tac 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_right "x" "v"),
        (UU_right "y"),
        (rtac iffI 1),
        (etac UU_I 1),
        (res_inst_tac [("s","UU::'b"),("t","x")] subst 1),
        (etac sym 1),
        (rtac refl_less 1)
        ]);


val less_ssum1c = prove_goalw thy [less_ssum_def]
"[|s1=Isinl(x::'a); s2=Isinr(y::'b)|] ==> s1 << s2 = ((x::'a) = UU)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac select_equality 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_left  "x" "u"),
        (UU_left "xa"),
        (rtac iffI 1),
        (res_inst_tac [("s","x"),("t","UU::'a")] subst 1),
        (atac 1),
        (rtac refl_less 1),
        (etac UU_I 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_left "x"),
        (UU_right "v"),
        (Simp_tac 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_left  "x" "u"),
        (rtac refl 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_left "x"),
        (UU_right "v"),
        (Simp_tac 1),
        (dtac conjunct2 1),
        (dtac conjunct2 1),
        (dtac conjunct1 1),
        (dtac spec 1),
        (dtac spec 1),
        (etac mp 1),
        (fast_tac HOL_cs 1)
        ]);


val less_ssum1d = prove_goalw thy [less_ssum_def]
"[|s1=Isinr(x); s2=Isinl(y)|] ==> s1 << s2 = (x = UU)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac select_equality 1),
        (dtac conjunct2 2),
        (dtac conjunct2 2),
        (dtac conjunct2 2),
        (dtac spec 2),
        (dtac spec 2),
        (etac mp 2),
        (fast_tac HOL_cs 2),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_right "x"),
        (UU_left "u"),
        (Simp_tac 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_right "ya"),
        (eq_right "x" "v"),
        (rtac iffI 1),
        (etac UU_I 2),
        (res_inst_tac [("s","UU"),("t","x")] subst 1),
        (etac sym 1),
        (rtac refl_less 1),
        (rtac conjI 1),
        (strip_tac 1),
        (etac conjE 1),
        (UU_right "x"),
        (UU_left "u"),
        (Simp_tac 1),
        (strip_tac 1),
        (etac conjE 1),
        (eq_right "x" "v"),
        (rtac refl 1)
        ])
end;


(* ------------------------------------------------------------------------ *)
(* optimize lemmas about less_ssum                                          *)
(* ------------------------------------------------------------------------ *)

Goal "(Isinl x) << (Isinl y) = (x << y)";
by (rtac less_ssum1a 1);
by (rtac refl 1);
by (rtac refl 1);
qed "less_ssum2a";

Goal "(Isinr x) << (Isinr y) = (x << y)";
by (rtac less_ssum1b 1);
by (rtac refl 1);
by (rtac refl 1);
qed "less_ssum2b";

Goal "(Isinl x) << (Isinr y) = (x = UU)";
by (rtac less_ssum1c 1);
by (rtac refl 1);
by (rtac refl 1);
qed "less_ssum2c";

Goal "(Isinr x) << (Isinl y) = (x = UU)";
by (rtac less_ssum1d 1);
by (rtac refl 1);
by (rtac refl 1);
qed "less_ssum2d";


(* ------------------------------------------------------------------------ *)
(* less_ssum is a partial order on ++                                     *)
(* ------------------------------------------------------------------------ *)

Goal "(p::'a++'b) << p";
by (res_inst_tac [("p","p")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum2a RS iffD2) 1);
by (rtac refl_less 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum2b RS iffD2) 1);
by (rtac refl_less 1);
qed "refl_less_ssum";

Goal "[|(p1::'a++'b) << p2; p2 << p1|] ==> p1=p2";
by (res_inst_tac [("p","p1")] IssumE2 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p2")] IssumE2 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("f","Isinl")] arg_cong 1);
by (rtac antisym_less 1);
by (etac (less_ssum2a RS iffD1) 1);
by (etac (less_ssum2a RS iffD1) 1);
by (hyp_subst_tac 1);
by (etac (less_ssum2d RS iffD1 RS ssubst) 1);
by (etac (less_ssum2c RS iffD1 RS ssubst) 1);
by (rtac strict_IsinlIsinr 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p2")] IssumE2 1);
by (hyp_subst_tac 1);
by (etac (less_ssum2c RS iffD1 RS ssubst) 1);
by (etac (less_ssum2d RS iffD1 RS ssubst) 1);
by (rtac (strict_IsinlIsinr RS sym) 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("f","Isinr")] arg_cong 1);
by (rtac antisym_less 1);
by (etac (less_ssum2b RS iffD1) 1);
by (etac (less_ssum2b RS iffD1) 1);
qed "antisym_less_ssum";

Goal "[|(p1::'a++'b) << p2; p2 << p3|] ==> p1 << p3";
by (res_inst_tac [("p","p1")] IssumE2 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p3")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum2a RS iffD2) 1);
by (res_inst_tac [("p","p2")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac trans_less 1);
by (etac (less_ssum2a RS iffD1) 1);
by (etac (less_ssum2a RS iffD1) 1);
by (hyp_subst_tac 1);
by (etac (less_ssum2c RS iffD1 RS ssubst) 1);
by (rtac minimal 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum2c RS iffD2) 1);
by (res_inst_tac [("p","p2")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac UU_I 1);
by (rtac trans_less 1);
by (etac (less_ssum2a RS iffD1) 1);
by (rtac (antisym_less_inverse RS conjunct1) 1);
by (etac (less_ssum2c RS iffD1) 1);
by (hyp_subst_tac 1);
by (etac (less_ssum2c RS iffD1) 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("p","p3")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum2d RS iffD2) 1);
by (res_inst_tac [("p","p2")] IssumE2 1);
by (hyp_subst_tac 1);
by (etac (less_ssum2d RS iffD1) 1);
by (hyp_subst_tac 1);
by (rtac UU_I 1);
by (rtac trans_less 1);
by (etac (less_ssum2b RS iffD1) 1);
by (rtac (antisym_less_inverse RS conjunct1) 1);
by (etac (less_ssum2d RS iffD1) 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum2b RS iffD2) 1);
by (res_inst_tac [("p","p2")] IssumE2 1);
by (hyp_subst_tac 1);
by (etac (less_ssum2d RS iffD1 RS ssubst) 1);
by (rtac minimal 1);
by (hyp_subst_tac 1);
by (rtac trans_less 1);
by (etac (less_ssum2b RS iffD1) 1);
by (etac (less_ssum2b RS iffD1) 1);
qed "trans_less_ssum";



