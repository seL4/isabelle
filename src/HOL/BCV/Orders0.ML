(*  Title:      HOL/BCV/Orders0.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM
*)

(** option **)
section "option";

Goalw [le_option] "(o1::('a::order)option) <= o1";
by (simp_tac (simpset() addsplits [option.split]) 1);
qed "le_option_refl";

Goalw [le_option] "(o1::('a::order)option) <= o2 --> o2<=o3 --> o1<=o3";
by (simp_tac (simpset() addsplits [option.split]) 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed_spec_mp "le_option_trans";

Goalw [le_option] "(o1::('a::order)option) <= o2 --> o2<=o1 --> o1=o2";
by (simp_tac (simpset() addsplits [option.split]) 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed_spec_mp "le_option_antisym";

Goalw [less_option] "(o1::('a::ord)option) < o2 = (o1<=o2 & o1 ~= o2)";
by (rtac refl 1);
qed "less_le_option";

Goalw [le_option] "Some x <= opt = (? y. opt = Some y & x <= y)";
by (simp_tac (simpset() addsplits [option.split]) 1);
qed_spec_mp "Some_le_conv";
AddIffs [Some_le_conv];

Goalw [le_option] "None <= opt";
by (simp_tac (simpset() addsplits [option.split]) 1);
qed "None_le";
AddIffs [None_le];


(** list **)
section "list";

Goalw [le_list] "[| xs <= ys; p < size xs |] ==> xs!p <= ys!p";
by (Blast_tac 1);
qed "le_listD";

Goalw [le_list] "([] <= ys) = (ys = [])";
by (Simp_tac 1);
qed "Nil_le_conv";
AddIffs [Nil_le_conv];

Goalw [le_list] "(xs::('a::order)list) <= xs";
by (induct_tac "xs" 1);
by (Auto_tac);
qed "le_list_refl";

Goalw [le_list]
 "!ys zs.(xs::('a::order)list) <= ys --> ys <= zs --> xs <= zs";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (rtac allI 1);
by (case_tac "ys" 1);
 by (hyp_subst_tac 1);
 by (Simp_tac 1);
by (rtac allI 1);
by (case_tac "zs" 1);
 by (hyp_subst_tac 1);
 by (Simp_tac 1);
by (hyp_subst_tac 1);
by (simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (REPEAT(EVERY1[etac allE, etac conjE, etac impE, rtac refl]));
 by (blast_tac (claset() addIs [order_trans]) 1);
by (Clarify_tac 1);
by (EVERY[etac allE 1, etac allE 1, etac impE 1, etac impE 2]);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (Blast_tac 1);
 by (rtac conjI 1);
 by (assume_tac 1);
 by (Blast_tac 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "le_list_trans";

Goalw [le_list]
 "!ys. (xs::('a::order)list) <= ys --> ys <= xs --> xs = ys";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (rtac allI 1);
by (case_tac "ys" 1);
 by (hyp_subst_tac 1);
 by (Simp_tac 1);
by (hyp_subst_tac 1);
by (simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (blast_tac (claset() addIs [order_antisym]) 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "le_list_antisym";

Goalw [less_list] "(xs::('a::ord)list) < ys = (xs<=ys & xs ~= ys)";
by (rtac refl 1);
qed "less_le_list";

(** product **)
section "product";

Goalw [le_prod] "(p1::('a::order * 'b::order)) <= p1";
by (Simp_tac 1);
qed "le_prod_refl";

Goalw [le_prod]
 "[| (p1::('a::order * 'b::order)) <= p2; p2<=p3 |] ==> p1<=p3";
by (blast_tac (claset() addIs [order_trans]) 1);
qed "le_prod_trans";

Goalw [le_prod]
 "[| (p1::('a::order * 'b::order)) <= p2; p2 <= p1 |] ==> p1 = p2";
by (blast_tac (claset() addIs [order_antisym,trans,surjective_pairing,sym]) 1);
qed_spec_mp "le_prod_antisym";

Goalw [less_prod] "(p1::('a::order * 'b::order)) < p2 = (p1<=p2 & p1 ~= p2)";
by (rtac refl 1);
qed "less_le_prod";

Goalw [le_prod] "((a,b) <= (c,d)) = (a <= c & b <= d)";
by (Simp_tac 1);
qed "le_prod_iff";
AddIffs [le_prod_iff];
