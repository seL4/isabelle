(*  Title:      HOL/Quot/HQUOT.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)

(* first prove some helpful lemmas *)
Goalw [quot_def] "{y. y===x}:quot";
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [per_sym]) 1);
qed "per_class_rep_quot";

Goal "Rep_quot a = Rep_quot b ==> a=b";
by (rtac (Rep_quot_inverse RS subst) 1);
by (res_inst_tac [("t","a")] (Rep_quot_inverse RS subst) 1);
by (Asm_simp_tac 1);
qed "quot_eq";

(* prepare induction and exhaustiveness *)
Goal "!s. s:quot --> P (Abs_quot s) ==> P x";
by (rtac (Abs_quot_inverse RS subst) 1);
by (rtac Rep_quot 1);
by (dres_inst_tac [("x","Rep_quot x")] spec 1);
by (asm_full_simp_tac (HOL_ss addsimps [Rep_quot,Rep_quot_inverse]) 1);
qed "all_q";

Goal "? s. s:quot & x=Abs_quot s";
by (res_inst_tac [("x","Rep_quot x")] exI 1);
by (asm_full_simp_tac (HOL_ss addsimps [Rep_quot,Rep_quot_inverse]) 1);
qed "exh_q";

(* some lemmas for the equivalence classes *)

(* equality and symmetry for equivalence classes *)
Goalw [peclass_def] "x===y==><[x]>=<[y]>";
by (res_inst_tac [("f","Abs_quot")] arg_cong 1);
by (rtac Collect_cong 1);
by (rtac iffI 1);
by (etac per_trans 1);by (assume_tac 1);
by (etac per_trans 1);
by (etac per_sym 1);
qed "per_class_eqI";

Goalw [peclass_def] "<[(x::'a::er)]>=<[y]>==>x===y";
by (dres_inst_tac [("f","Rep_quot")] arg_cong 1);
by (asm_full_simp_tac(HOL_ss addsimps [Abs_quot_inverse,per_class_rep_quot])1);
by (dres_inst_tac [("c","x")] equalityCE 1);by (assume_tac 3);
by Safe_tac;
by (blast_tac (claset() addIs [er_refl]) 1);
qed "er_class_eqE";

Goalw [peclass_def] "[|x:D;<[x]>=<[y]>|]==>x===y";
by (dtac DomainD 1);
by (dres_inst_tac [("f","Rep_quot")] arg_cong 1);
by (asm_full_simp_tac(HOL_ss addsimps [Abs_quot_inverse,per_class_rep_quot])1);
by (dres_inst_tac [("c","x")] equalityCE 1);by (assume_tac 3);
by Auto_tac;
qed "per_class_eqE";

Goal "<[(x::'a::er)]>=<[y]>=x===y";
by (rtac iffI 1);
by (etac er_class_eqE 1);
by (etac per_class_eqI 1);
qed "er_class_eq";

Goal "x:D==><[x]>=<[y]>=x===y";
by (rtac iffI 1);
by (etac per_class_eqE 1);by (assume_tac 1);
by (etac per_class_eqI 1);
qed "per_class_eq";

(* inequality *)
Goal "[|x:D;~x===y|]==><[x]>~=<[y]>";
by (rtac notI 1);
by (dtac per_class_eqE 1);
by Auto_tac;
qed "per_class_neqI";

Goal "~(x::'a::er)===y==><[x]>~=<[y]>";
by (rtac notI 1);
by (dtac er_class_eqE 1);
by Auto_tac;
qed "er_class_neqI";

Goal "<[x]>~=<[y]>==>~x===y";
by (rtac notI 1);
by (etac notE 1);
by (etac per_class_eqI 1);
qed "per_class_neqE";

Goal "x:D==><[x]>~=<[y]>=(~x===y)";
by (rtac iffI 1);
by (etac per_class_neqE 1);
by (etac per_class_neqI 1);by (assume_tac 1);
qed "per_class_not";

Goal "<[(x::'a::er)]>~=<[y]>=(~x===y)";
by (rtac iffI 1);
by (etac per_class_neqE 1);
by (etac er_class_neqI 1);
qed "er_class_not";

(* exhaustiveness and induction *)
Goalw [peclass_def] "? s. x=<[s]>";
by (rtac all_q 1);
by (strip_tac 1);
by (asm_full_simp_tac (HOL_ss addsimps [mem_Collect_eq,quot_def]) 1);
by (etac exE 1);
by (res_inst_tac [("x","r")] exI 1);
by (rtac quot_eq 1);
by (subgoal_tac "s:quot" 1);
by (asm_simp_tac(HOL_ss addsimps [Abs_quot_inverse,per_class_rep_quot])1);
by (rtac set_ext 1);
by (Blast_tac 1);
by (asm_full_simp_tac (HOL_ss addsimps [mem_Collect_eq,quot_def]) 1);
by (Blast_tac 1);
qed "per_class_exh";

Goal "!x. P<[x]> ==> P s";
by (cut_facts_tac [read_instantiate[("x","s::'a::per quot")] per_class_exh] 1);
by (Blast_tac 1);
qed "per_class_all";

(* theorems for any_in *)
Goalw [any_in_def,peclass_def] "any_in<[(s::'a::er)]>===s";
by (rtac selectI2 1);
by (rtac refl 1);
by (fold_goals_tac [peclass_def]);
by (etac er_class_eqE 1);
qed "er_any_in_class";

Goalw [any_in_def,peclass_def] "s:D==>any_in<[s]>===s";
by (rtac selectI2 1);
by (rtac refl 1);
by (fold_goals_tac [peclass_def]);
by (rtac per_sym 1);
by (etac per_class_eqE 1);
by (etac sym 1);
qed "per_any_in_class";

Goal "<[any_in (s::'a::er quot)]> = s";
by (rtac per_class_all 1);
by (rtac allI 1);
by (rtac (er_any_in_class RS per_class_eqI) 1);
qed "er_class_any_in";

(* equivalent theorem for per would need !x.x:D *)
Goal "!x::'a::per. x:D==><[any_in (q::'a::per quot)]> = q";
by (rtac per_class_all 1);
by (rtac allI 1);
by (rtac (per_any_in_class RS per_class_eqI) 1);
by (etac spec 1);
qed "per_class_any_in";

(* is like theorem for class er *)
