(*  Title:      HOL/BCV/SemiLattice.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

Goalw [semilat_def] "[| x:A; y:A; semilat A |] ==> x <= x+y";
by(Blast_tac 1);
qed "semilat_ub1";

Goalw [semilat_def] "[| x:A; y:A; semilat A |] ==> y <= x+y";
by(Blast_tac 1);
qed "semilat_ub2";

Goalw [semilat_def] "[| x:A; y:A; z:A; x <= z; y <= z; semilat A |] ==> x+y <= z";
by(Blast_tac 1);
qed "semilat_lub";

Goalw [semilat_def] "[| x:A; y:A; semilat A |] ==> x+y : A";
by(Blast_tac 1);
qed "semilat_plus";

Addsimps [semilat_ub1,semilat_ub2,semilat_lub,semilat_plus];

Goal "[| x:A; y:A; semilat A |] ==> (x <= y) = (x+y = y)";
br iffI 1;
 by(REPEAT(ares_tac [order_antisym,semilat_lub,order_refl,semilat_ub2] 1));
be subst 1;
by(Asm_simp_tac 1);
qed "le_iff_plus_unchanged";

Goal "[| x:A; y:A; semilat A |] ==> (x <= y) = (y = x+y)";
br iffI 1;
 by(REPEAT(ares_tac [order_antisym,semilat_lub,order_refl,semilat_ub2] 1));
be ssubst 1;
by(Asm_simp_tac 1);
qed "le_iff_plus_unchanged2";

Goal "[| x:A; y:A; z:A; semilat A; x <= y | x <= z |] ==> x <= y+z";
by(blast_tac (claset() addIs [order_trans,semilat_ub1,semilat_ub2]) 1);
qed "plus_mono";

Goal "[| x:A; semilat A |] ==> x+x = x";
by(REPEAT(ares_tac [order_refl RSN (4,le_iff_plus_unchanged RS iffD1)] 1));
qed "semilat_idemp";
Addsimps [semilat_idemp];

Goal "[| x:A; y:A; z:A; semilat A |] ==> (x+y)+z = x+(y+z)";
by(blast_tac (HOL_cs addSIs [order_refl,order_antisym,semilat_lub,semilat_plus]
                     addIs [plus_mono]) 1);
qed "semilat_assoc";

Goal "[| x:A; y:A; semilat A |] ==> x+(x+y) = x+y";
by(asm_simp_tac (simpset() addsimps [semilat_assoc RS sym]) 1);
qed "semilat_assoc_idemp";
Addsimps [semilat_assoc_idemp];

Goal "[| x:A; y:A; z:A; semilat A |] ==> (x+y <= z) = (x <= z & y <= z)";
by(blast_tac (claset() addIs [semilat_ub1,semilat_ub2,semilat_lub,order_trans]) 1);
qed "plus_le_conv";
Addsimps [plus_le_conv];


(** option **)

Goal "semilat A ==> semilat (option A)";
by(simp_tac (simpset() addsimps [semilat_def,le_option,plus_option]
                       addsplits [option.split]) 1);
by(blast_tac (claset() addIs [semilat_ub1,semilat_ub2,semilat_lub,semilat_plus]) 1);
qed "semilat_option";
Addsimps [semilat_option];
AddSIs [semilat_option];

(** list **)
Goalw [plus_list] "[] + [] = []";
by(Simp_tac 1);
qed "plus_Nil_Nil";
Addsimps [plus_Nil_Nil];

Goalw [plus_list] "(x#xs) + (y#ys) = (x+y)#(xs+ys)";
by(Simp_tac 1);
qed "plus_Cons_Cons";
Addsimps [plus_Cons_Cons];

Goal
 "!xs ys i. length xs = n--> length ys = n--> i<n--> (xs+ys)!i = xs!i + ys!i";
by(induct_tac "n" 1);
 by(Simp_tac 1);
by(Clarify_tac 1);
by(exhaust_tac "xs" 1);
 by(Asm_full_simp_tac 1);
by(exhaust_tac "ys" 1);
 by(Asm_full_simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
qed_spec_mp "nth_plus";
Addsimps [nth_plus];

Goalw [le_list]
 "semilat A ==> !xs:listsn n A. !ys:listsn n A. xs <= xs+ys";
by(asm_simp_tac (simpset() addsimps [le_max_iff_disj]) 1);
by(Clarify_tac 1);
by(blast_tac (HOL_cs addIs [nth_in,nth_plus,listsnE_length,listsnE_set,semilat_ub1]) 1);
qed_spec_mp "plus_list_ub1";

Goalw [le_list]
 "semilat A ==> !xs:listsn n A. !ys:listsn n A. ys <= xs+ys";
by(asm_simp_tac (simpset() addsimps [le_max_iff_disj]) 1);
by(Clarify_tac 1);
by(blast_tac (HOL_cs addIs [nth_in,nth_plus,listsnE_length,listsnE_set,semilat_ub2]) 1);
qed_spec_mp "plus_list_ub2";

Goalw [le_list]
 "semilat A ==> !xs:listsn n A. !ys:listsn n A. !zs:listsn n A. \
\              xs <= zs & ys <= zs --> xs+ys <= zs";
by(asm_simp_tac (simpset() addsimps [le_max_iff_disj] addcongs [conj_cong]) 1);
by(Clarify_tac 1);
by(blast_tac (HOL_cs addIs [nth_in,nth_plus,listsnE_length,listsnE_set,semilat_lub]) 1);
qed_spec_mp "plus_list_lub";

Goalw [listsn_def]
 "semilat A ==> !xs:listsn n A. !ys:listsn n A. xs+ys : listsn n A";
by(induct_tac "n" 1);
 by(Simp_tac 1);
by(Asm_full_simp_tac 1);
by(Clarify_tac 1);
by(exhaust_tac "xs" 1);
 by(Asm_full_simp_tac 1);
by(exhaust_tac "ys" 1);
 by(Asm_full_simp_tac 1);
by(Asm_full_simp_tac 1);
by(blast_tac (claset() addIs [semilat_plus]) 1);
qed_spec_mp "plus_list_closed";

Goal "semilat A ==> semilat (listsn n A)";
by(simp_tac (HOL_basic_ss addsimps [semilat_def]) 1);
by(asm_simp_tac (HOL_ss addsimps [plus_list_ub1,plus_list_ub2,plus_list_lub,plus_list_closed]) 1);
qed "semilat_listsn";
Addsimps [semilat_listsn];
AddSIs [semilat_listsn];

Goalw [le_list]
 "!i xs. xs : listsn n A --> x:A --> semilat A --> i<n --> xs <= xs[i := x + xs!i]";
by(Simp_tac 1);
by(induct_tac "n" 1);
 by(Simp_tac 1);
by(asm_simp_tac (simpset() addsimps [in_listsn_Suc_iff]) 1);
by(Clarify_tac 1);
by(asm_simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
qed_spec_mp "list_update_incr";

(* product *)

Goalw [semilat_def,plus_prod] "[| semilat A; semilat B |] ==> semilat (A Times B)";
by(Asm_simp_tac 1);
qed "semilat_Times";
