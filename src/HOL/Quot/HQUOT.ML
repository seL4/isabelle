(*  Title:      HOL/Quot/HQUOT.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open HQUOT;

(* first prove some helpful lemmas *)
goalw thy [quot_def] "{y.y===x}:quot";
by (Asm_simp_tac 1);
by (fast_tac (set_cs addIs [per_sym]) 1);
qed "per_class_rep_quot";

val prems = goal thy "Rep_quot a = Rep_quot b ==> a=b";
by (cut_facts_tac prems 1);
br (Rep_quot_inverse RS subst) 1;
by (res_inst_tac [("t","a")] (Rep_quot_inverse RS subst) 1);
by (Asm_simp_tac 1);
qed "quot_eq";

(* prepare induction and exhaustiveness *)
val prems = goal thy "!s.s:quot --> P (Abs_quot s) ==> P x";
by (cut_facts_tac prems 1);
br (Abs_quot_inverse RS subst) 1;
br Rep_quot 1;
by (dres_inst_tac [("x","Rep_quot x")] spec 1);
by (asm_full_simp_tac (HOL_ss addsimps [Rep_quot,Rep_quot_inverse]) 1);
qed "all_q";

goal thy "? s.s:quot & x=Abs_quot s";
by (res_inst_tac [("x","Rep_quot x")] exI 1);
by (asm_full_simp_tac (HOL_ss addsimps [Rep_quot,Rep_quot_inverse]) 1);
qed "exh_q";

(* some lemmas for the equivalence classes *)

(* equality and symmetry for equivalence classes *)
val prems = goalw thy [peclass_def] "x===y==><[x]>=<[y]>";
by (cut_facts_tac prems 1);
by (res_inst_tac [("f","Abs_quot")] arg_cong 1);
br Collect_cong 1;
br iffI 1;
be per_trans 1;ba 1;
be per_trans 1;
be per_sym 1;
qed "per_class_eqI";

val prems = goalw thy [peclass_def] "<[(x::'a::er)]>=<[y]>==>x===y";
by (cut_facts_tac prems 1);
by (dres_inst_tac [("f","Rep_quot")] arg_cong 1);
by (asm_full_simp_tac(HOL_ss addsimps [Abs_quot_inverse,per_class_rep_quot])1);
by (dres_inst_tac [("c","x")] equalityCE 1);ba 3;
by (safe_tac set_cs);
by (fast_tac (set_cs addIs [er_refl]) 1);
qed "er_class_eqE";

val prems = goalw thy [peclass_def] "[|x:D;<[x]>=<[y]>|]==>x===y";
by (cut_facts_tac prems 1);
bd DomainD 1;
by (dres_inst_tac [("f","Rep_quot")] arg_cong 1);
by (asm_full_simp_tac(HOL_ss addsimps [Abs_quot_inverse,per_class_rep_quot])1);
by (dres_inst_tac [("c","x")] equalityCE 1);ba 3;
by (safe_tac set_cs);
qed "per_class_eqE";

goal thy "<[(x::'a::er)]>=<[y]>=x===y";
br iffI 1;
be er_class_eqE 1;
be per_class_eqI 1;
qed "er_class_eq";

val prems = goal thy "x:D==><[x]>=<[y]>=x===y";
by (cut_facts_tac prems 1);
br iffI 1;
be per_class_eqE 1;ba 1;
be per_class_eqI 1;
qed "per_class_eq";

(* inequality *)
val prems = goal thy "[|x:D;~x===y|]==><[x]>~=<[y]>";
by (cut_facts_tac prems 1);
br notI 1;
bd per_class_eqE 1;
auto();
qed "per_class_neqI";

val prems = goal thy "~(x::'a::er)===y==><[x]>~=<[y]>";
by (cut_facts_tac prems 1);
br notI 1;
bd er_class_eqE 1;
auto();
qed "er_class_neqI";

val prems = goal thy "<[x]>~=<[y]>==>~x===y";
by (cut_facts_tac prems 1);
br notI 1;
be notE 1;
be per_class_eqI 1;
qed "per_class_neqE";

val prems = goal thy "x:D==><[x]>~=<[y]>=(~x===y)";
by (cut_facts_tac prems 1);
br iffI 1;
be per_class_neqE 1;
be per_class_neqI 1;ba 1;
qed "per_class_not";

goal thy "<[(x::'a::er)]>~=<[y]>=(~x===y)";
br iffI 1;
be per_class_neqE 1;
be er_class_neqI 1;
qed "er_class_not";

(* exhaustiveness and induction *)
goalw thy [peclass_def] "? s.x=<[s]>";
br all_q 1;
by (strip_tac 1);
by (asm_full_simp_tac (HOL_ss addsimps [mem_Collect_eq,quot_def]) 1);
be exE 1;
by (res_inst_tac [("x","r")] exI 1);
br quot_eq 1;
by (subgoal_tac "s:quot" 1);
by (asm_simp_tac(HOL_ss addsimps [Abs_quot_inverse,per_class_rep_quot])1);
br set_ext 1;
by (fast_tac set_cs 1);
by (asm_full_simp_tac (HOL_ss addsimps [mem_Collect_eq,quot_def]) 1);
by (fast_tac set_cs 1);
qed "per_class_exh";

val prems = goal thy "!x.P<[x]> ==> P s";
by (cut_facts_tac (prems@[
	read_instantiate[("x","s::'a::per quot")] per_class_exh]) 1);
by (fast_tac set_cs 1);
qed "per_class_all";

(* theorems for any_in *)
goalw thy [any_in_def,peclass_def] "any_in<[(s::'a::er)]>===s";
fr selectI2;
fr refl;
by (fold_goals_tac [peclass_def]);
fe er_class_eqE;
qed "er_any_in_class";

val prems = goalw thy [any_in_def,peclass_def] "s:D==>any_in<[s]>===s";
by (cut_facts_tac prems 1);
fr selectI2;
fr refl;
by (fold_goals_tac [peclass_def]);
fr per_sym;
fe per_class_eqE;
fe sym;
qed "per_any_in_class";

val prems = goal thy "<[any_in (s::'a::er quot)]> = s";
by (cut_facts_tac prems 1);
fr per_class_all;
fr allI;
fr (er_any_in_class RS per_class_eqI);
qed "er_class_any_in";

(* equivalent theorem for per would need !x.x:D *)
val prems = goal thy "!x::'a::per.x:D==><[any_in (q::'a::per quot)]> = q";
by (cut_facts_tac prems 1);
fr per_class_all;
fr allI;
fr (per_any_in_class RS per_class_eqI);
fe spec;
qed "per_class_any_in";

(* is like theorem for class er *)