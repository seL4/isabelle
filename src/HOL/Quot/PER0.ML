(*  Title:      HOL/Quot/PER0.ML
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

*)
open PER0;

(* derive the characteristic axioms *)
Goalw [per_def] "x === y ==> y === x";
by (etac ax_per_sym 1);
qed "per_sym";

Goalw [per_def] "[| x === y; y === z |] ==> x === z";
by (etac ax_per_trans 1);
by (assume_tac 1);
qed "per_trans";

Goalw [per_def] "(x::'a::er) === x";
by (rtac ax_er_refl 1);
qed "er_refl";

(* now everything works without axclasses *)

Goal "x===y=y===x";
by (rtac iffI 1);
by (etac per_sym 1);
by (etac per_sym 1);
qed "per_sym2";

Goal "x===y ==> x===x";
by (rtac per_trans 1);by (assume_tac 1);
by (etac per_sym 1);
qed "sym2refl1";

Goal "x===y ==> y===y";
by (rtac per_trans 1);by (assume_tac 2);
by (etac per_sym 1);
qed "sym2refl2";

Goalw [Dom] "x:D ==> x === x";
by (Blast_tac 1);
qed "DomainD";

Goalw [Dom] "x === x ==> x:D";
by (Blast_tac 1);
qed "DomainI";

Goal "x:D = x===x";
by (rtac iffI 1);
by (etac DomainD 1);
by (etac DomainI 1);
qed "DomainEq";

Goal "(~ x === y) = (~ y === x)";
by (rtac (per_sym2 RS arg_cong) 1);
qed "per_not_sym";

(* show that PER work only on D *)
Goal "x===y ==> x:D";
by (etac (sym2refl1 RS DomainI) 1);
qed "DomainI_left"; 

Goal "x===y ==> y:D";
by (etac (sym2refl2 RS DomainI) 1);
qed "DomainI_right"; 

Goalw [Dom] "x~:D ==> ~x===y";
by (res_inst_tac [("Q","x===y")] (excluded_middle RS disjE) 1);
by (assume_tac 1);
by (dtac sym2refl1 1);
by (Blast_tac 1);
qed "notDomainE1"; 

Goalw [Dom] "x~:D ==> ~y===x";
by (res_inst_tac [("Q","y===x")] (excluded_middle RS disjE) 1);
by (assume_tac 1);
by (dtac sym2refl2 1);
by (Blast_tac 1);
qed "notDomainE2"; 

(* theorems for equivalence relations *)
Goal "(x::'a::er) : D";
by (rtac DomainI 1);
by (rtac er_refl 1);
qed "er_Domain";

(* witnesses for "=>" ::(per,per)per  *)
Goalw [fun_per_def]"eqv (x::'a::per => 'b::per) y ==> eqv y x";
by (auto_tac (claset(), simpset() addsimps [per_sym2]));
qed "per_sym_fun";

Goalw [fun_per_def] "[| eqv (f::'a::per=>'b::per) g;eqv g h|] ==> eqv f h";
by Safe_tac;
by (REPEAT (dtac spec 1));
by (res_inst_tac [("y","g y")] per_trans 1);
by (rtac mp 1);by (assume_tac 1);
by (Asm_simp_tac 1);
by (rtac mp 1);by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [sym2refl2]) 1);
qed "per_trans_fun";


