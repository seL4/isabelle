(*  Title:      HOL/Quot/PER0.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open PER0;

(* derive the characteristic axioms *)
val prems = goalw thy [per_def] "x === y ==> y === x";
by (cut_facts_tac prems 1);
be ax_per_sym 1;
qed "per_sym";

val prems = goalw thy [per_def] "[| x === y; y === z |] ==> x === z";
by (cut_facts_tac prems 1);
be ax_per_trans 1;
ba 1;
qed "per_trans";

goalw thy [per_def] "(x::'a::er) === x";
br ax_er_refl 1;
qed "er_refl";

(* now everything works without axclasses *)

goal thy "x===y=y===x";
br iffI 1;
be per_sym 1;
be per_sym 1;
qed "per_sym2";

val prems = goal  thy "x===y ==> x===x";
by (cut_facts_tac prems 1);
br per_trans 1;ba 1;
be per_sym 1;
qed "sym2refl1";

val prems = goal  thy "x===y ==> y===y";
by (cut_facts_tac prems 1);
br per_trans 1;ba 2;
be per_sym 1;
qed "sym2refl2";

val prems = goalw thy [Domain] "x:D ==> x === x";
by (cut_facts_tac prems 1);
by (fast_tac set_cs 1);
qed "DomainD";

val prems = goalw thy [Domain] "x === x ==> x:D";
by (cut_facts_tac prems 1);
by (fast_tac set_cs 1);
qed "DomainI";

goal thy "x:D = x===x";
br iffI 1;
be DomainD 1;
be DomainI 1;
qed "DomainEq";

goal thy "(~ x === y) = (~ y === x)";
br (per_sym2 RS arg_cong) 1;
qed "per_not_sym";

(* show that PER work only on D *)
val prems = goal thy "x===y ==> x:D";
by (cut_facts_tac prems 1);
be (sym2refl1 RS DomainI) 1;
qed "DomainI_left"; 

val prems = goal thy "x===y ==> y:D";
by (cut_facts_tac prems 1);
be (sym2refl2 RS DomainI) 1;
qed "DomainI_right"; 

val prems = goalw thy [Domain] "x~:D ==> ~x===y";
by (cut_facts_tac prems 1);
by (res_inst_tac [("Q","x===y")] (excluded_middle RS disjE) 1);ba 1;
bd sym2refl1 1;
by (fast_tac set_cs 1);
qed "notDomainE1"; 

val prems = goalw thy [Domain] "x~:D ==> ~y===x";
by (cut_facts_tac prems 1);
by (res_inst_tac [("Q","y===x")] (excluded_middle RS disjE) 1);ba 1;
bd sym2refl2 1;
by (fast_tac set_cs 1);
qed "notDomainE2"; 

(* theorems for equivalence relations *)
goal thy "(x::'a::er) : D";
br DomainI 1;
br er_refl 1;
qed "er_Domain";

(* witnesses for "=>" ::(per,per)per  *)
val prems = goalw thy [fun_per_def]"eqv (x::'a::per => 'b::per) y ==> eqv y x";
by (cut_facts_tac prems 1);
by (safe_tac HOL_cs);
by (asm_full_simp_tac (HOL_ss addsimps [per_sym2]) 1);
qed "per_sym_fun";

val prems = goalw thy [fun_per_def]
	"[| eqv (f::'a::per=>'b::per) g;eqv g h|] ==> eqv f h";
by (cut_facts_tac prems 1);
by (safe_tac HOL_cs);
by (REPEAT (dtac spec 1));
by (res_inst_tac [("y","g y")] per_trans 1);
br mp 1;ba 1;
by (Asm_simp_tac 1);
br mp 1;ba 1;
by (asm_simp_tac (!simpset addsimps [sym2refl2]) 1);
qed "per_trans_fun";


