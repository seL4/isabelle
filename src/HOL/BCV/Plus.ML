(*  Title:      HOL/BCV/Plus.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

(** option **)

Goalw [plus_option] "x+None = x";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "plus_None";
Addsimps [plus_None];

Goalw [plus_option] "None+x = x";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "None_plus";
Addsimps [None_plus];

Goalw [plus_option] "Some x + Some y = Some(x+y)";
by(Simp_tac 1);
qed "Some_plus_Some";
Addsimps [Some_plus_Some];

Goalw [plus_option] "? y. Some x + opt = Some y";
by(simp_tac (simpset() addsplits [option.split]) 1);
qed "plus_option_Some_Some";

(** list **)

Goal "list_plus xs [] = xs";
by(induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_simp_tac (simpset() addsplits [list.split]) 1);
qed "list_plus_Nil2";
Addsimps [list_plus_Nil2];

Goal "!ys. length(list_plus xs ys) = max(length xs) (length ys)";
by(induct_tac "xs" 1);
 by(Simp_tac 1);
by(asm_simp_tac (simpset() addsplits [list.split]) 1);
qed_spec_mp "length_list_plus";
Addsimps [length_list_plus];

Goalw [plus_list]
 "length(ts+us) = max (length ts) (length us)";
by(Simp_tac 1);
qed "length_plus_list";
Addsimps [length_plus_list];
