(*  Title:      HOL/BCV/Listn.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Addsimps [set_update_subsetI];

Goalw [lesub_def] "xs <=[r] ys == Listn.le r xs ys";
by (Simp_tac 1);
qed "unfold_lesub_list";

Goalw [lesub_def,Listn.le_def] "([] <=[r] ys) = (ys = [])";
by (Simp_tac 1);
qed "Nil_le_conv";

Goalw [lesub_def,Listn.le_def] "~ x#xs <=[r] []";
by (Simp_tac 1);
qed "Cons_notle_Nil";

AddIffs [Nil_le_conv,Cons_notle_Nil];

Goalw [lesub_def,Listn.le_def] "x#xs <=[r] y#ys = (x <=_r y & xs <=[r] ys)";
by (Simp_tac 1);
qed "Cons_le_Cons";
AddIffs [Cons_le_Cons];

Goalw [lesssub_def] "order r ==> \
\ x#xs <_(Listn.le r) y#ys = \
\ (x <_r y & xs <=[r] ys  |  x = y & xs <_(Listn.le r) ys)";
by (Blast_tac 1);
qed "Cons_less_Cons";
Addsimps [Cons_less_Cons];

Goalw [unfold_lesub_list]
 "[| i<size xs; xs <=[r] ys; x <=_r y |] ==> xs[i:=x] <=[r] ys[i:=y]";
by (rewtac Listn.le_def);
by (asm_full_simp_tac (simpset() addsimps [list_all2_conv_all_nth,nth_list_update]) 1);
qed "list_update_le_cong";


Goalw [Listn.le_def,lesub_def]
 "[| xs <=[r] ys; p < size xs |] ==> xs!p <=_r ys!p";
by (asm_full_simp_tac (simpset() addsimps [list_all2_conv_all_nth]) 1);
qed "le_listD";

Goalw [unfold_lesub_list] "!x. x <=_r x ==> xs <=[r] xs";
by (asm_simp_tac (simpset() addsimps [Listn.le_def,list_all2_conv_all_nth]) 1);
qed "le_list_refl";

Goalw [unfold_lesub_list]
 "[| order r; xs <=[r] ys; ys <=[r] zs |] ==> xs <=[r] zs";
by (asm_full_simp_tac(simpset()addsimps[Listn.le_def,list_all2_conv_all_nth])1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed "le_list_trans";

Goalw [unfold_lesub_list]
 "[| order r; xs <=[r] ys; ys <=[r] xs |] ==> xs = ys";
by (asm_full_simp_tac(simpset()addsimps[Listn.le_def,list_all2_conv_all_nth])1);
by (rtac nth_equalityI 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed "le_list_antisym";

Goal "order r ==> order(Listn.le r)";
by (stac order_def 1);
by (blast_tac (claset() addIs [le_list_refl,le_list_trans,le_list_antisym]
                       addDs [order_refl]) 1);
qed "order_listI";
Addsimps [order_listI];
AddSIs [order_listI];


Goalw [Listn.le_def,lesub_def] "xs <=[r] ys ==> size ys = size xs";
by (asm_full_simp_tac(simpset()addsimps[list_all2_conv_all_nth])1);
qed "lesub_list_impl_same_size";
Addsimps [lesub_list_impl_same_size];

Goalw [lesssub_def] "xs <_(Listn.le r) ys ==> size ys = size xs";
by (Auto_tac);
qed "lesssub_list_impl_same_size";

Goalw [list_def] "[| length xs = n; set xs <= A |] ==> xs : list n A";
by (Blast_tac 1);
qed "listI";

Goalw [list_def] "xs : list n A ==> length xs = n";
by (Blast_tac 1);
qed "listE_length";
Addsimps [listE_length];

Goal "[| xs : list n A; p < n |] ==> p < length xs";
by (Asm_simp_tac 1);
qed "less_lengthI";

Goalw [list_def] "xs : list n A ==> set xs <= A";
by (Blast_tac 1);
qed "listE_set";
Addsimps [listE_set];

Goalw [list_def] "list 0 A = {[]}";
by (Auto_tac); 
qed "list_0";
Addsimps [list_0];

Goalw [list_def]
 "(xs : list (Suc n) A) = (? y:A. ? ys:list n A. xs = y#ys)";
by (case_tac "xs" 1);
by (Auto_tac);
qed "in_list_Suc_iff";

Goal "(x#xs : list (Suc n) A) = (x:A & xs : list n A)";
by (simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
qed "Cons_in_list_Suc";
AddIffs [Cons_in_list_Suc];

Goal "? a. a:A ==> ? xs. xs : list n A";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Blast_tac 1);
qed "list_not_empty";


Goal "!i n. length xs = n --> set xs <= A --> i < n --> (xs!i) : A";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
qed_spec_mp "nth_in";
Addsimps [nth_in];

Goal "[| xs : list n A; i < n |] ==> (xs!i) : A";
by (blast_tac (HOL_cs addIs [nth_in,listE_length,listE_set]) 1);
qed "listE_nth_in";

Goalw [list_def]
 "[| xs : list n A; x:A |] ==> xs[i := x] : list n A";
by (Asm_full_simp_tac 1);
qed "list_update_in_list";
Addsimps [list_update_in_list];
AddSIs [list_update_in_list];

Goalw [plussub_def,map2_def] "[] +[f] xs = []";
by (Simp_tac 1);
qed "plus_list_Nil";
Addsimps [plus_list_Nil];

Goal
 "(x#xs) +[f] ys = (case ys of [] => [] | y#ys => (x +_f y)#(xs +[f] ys))";
by (simp_tac (simpset() addsimps [plussub_def,map2_def] addsplits [list.split]) 1);
qed "plus_list_Cons";
Addsimps [plus_list_Cons];

Goal "!ys. length(xs +[f] ys) = min(length xs) (length ys)";
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsplits [list.split]) 1);
qed_spec_mp "length_plus_list";
Addsimps [length_plus_list];

Goal
 "!xs ys i. length xs = n --> length ys = n --> i<n --> \
\           (xs +[f] ys)!i = (xs!i) +_f (ys!i)";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (case_tac "xs" 1);
 by (Asm_full_simp_tac 1);
by (force_tac (claset(),simpset() addsimps [nth_Cons]
       addsplits [list.split,nat.split]) 1);
qed_spec_mp "nth_plus_list";
Addsimps [nth_plus_list];

Goalw [unfold_lesub_list]
 "[| semilat(A,r,f); set xs <= A; set ys <= A; size xs = size ys |] \
\ ==> xs <=[r] xs +[f] ys";
by (asm_full_simp_tac(simpset()addsimps[Listn.le_def,list_all2_conv_all_nth])1);
qed_spec_mp "plus_list_ub1";

Goalw [unfold_lesub_list]
 "[| semilat(A,r,f); set xs <= A; set ys <= A; size xs = size ys |] \
\ ==> ys <=[r] xs +[f] ys";
by (asm_full_simp_tac(simpset()addsimps[Listn.le_def,list_all2_conv_all_nth])1);
qed_spec_mp "plus_list_ub2";

Goalw [unfold_lesub_list]
 "semilat(A,r,f) ==> !xs ys zs. set xs <= A --> set ys <= A --> set zs <= A \
\ --> size xs = n & size ys = n --> \
\              xs <=[r] zs & ys <=[r] zs --> xs +[f] ys <=[r] zs";
by (asm_full_simp_tac(simpset()addsimps[Listn.le_def,list_all2_conv_all_nth])1);
qed_spec_mp "plus_list_lub";

Goalw [unfold_lesub_list]
 "[| semilat(A,r,f); x:A |] ==> set xs <= A --> \
\ (!i. i<size xs --> xs <=[r] xs[i := x +_f xs!i])";
by (simp_tac(simpset()addsimps[Listn.le_def,list_all2_conv_all_nth])1);
by (induct_tac "xs" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsimps [nth_Cons] addsplits [nat.split]) 1);
qed_spec_mp "list_update_incr";

Goalw [acc_def] "[| order r; acc r |] ==> acc(Listn.le r)";
by (subgoal_tac
 "wf(UN n. {(ys,xs). size xs = n & size ys = n & xs <_(Listn.le r) ys})" 1);
 by (etac wf_subset 1);
 by (blast_tac (claset() addIs [lesssub_list_impl_same_size]) 1);
by (rtac wf_UN 1);
 by (Clarify_tac 2);
 by (rename_tac "m n" 2);
 by (case_tac "m=n" 2);
  by (Asm_full_simp_tac 2);
 by (rtac conjI 2);
  by (fast_tac (claset() addSIs [equals0I] addDs [not_sym]) 2);
 by (fast_tac (claset() addSIs [equals0I] addDs [not_sym]) 2);
by (Clarify_tac 1);
by (rename_tac "n" 1);
by (induct_tac "n" 1);
 by (simp_tac (simpset() addsimps [lesssub_def] addcongs [conj_cong]) 1);
by (rename_tac "k" 1);
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by (simp_tac (simpset() addsimps [length_Suc_conv] addcongs [conj_cong]) 1);
by (Clarify_tac 1);
by (rename_tac "M m" 1);
by (case_tac "? x xs. size xs = k & x#xs : M" 1);
 by (etac thin_rl 2);
 by (etac thin_rl 2);
 by (Blast_tac 2);
by (eres_inst_tac [("x","{a. ? xs. size xs = k & a#xs:M}")] allE 1);
by (etac impE 1);
 by (Blast_tac 1);
by (thin_tac "? x xs. ?P x xs" 1);
by (Clarify_tac 1);
by (rename_tac "maxA xs" 1);
by (eres_inst_tac [("x","{ys. size ys = size xs & maxA#ys : M}")] allE 1);
by (etac impE 1);
 by (Blast_tac 1);
by (Clarify_tac 1);
by (thin_tac "m : M" 1);
by (thin_tac "maxA#xs : M" 1);
by (rtac bexI 1);
 by (assume_tac 2);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Blast_tac 1);
qed "acc_le_listI";
AddSIs [acc_le_listI];


Goalw [closed_def]
 "closed S f ==> closed (list n S) (map2 f)";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (Simp_tac 1);
by (Blast_tac 1);
qed "closed_listI";


Goalw [Listn.sl_def]
 "!!L. semilat L ==> semilat (Listn.sl n L)";
by (split_all_tac 1);
by (simp_tac (HOL_basic_ss addsimps [semilat_Def, split_conv]) 1);
by (rtac conjI 1);
 by (Asm_simp_tac 1);
by (rtac conjI 1);
 by (asm_simp_tac(HOL_basic_ss addsimps [semilatDclosedI,closed_listI]) 1);
by (simp_tac (HOL_basic_ss addsimps [list_def]) 1);
by (asm_simp_tac (simpset() addsimps [plus_list_ub1,plus_list_ub2,plus_list_lub]) 1);
qed "semilat_Listn_sl";


Goal "!xes. xes : list n (err A) --> coalesce xes : err(list n A)";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (simp_tac (simpset() addsimps [plussub_def,Err.sup_def,lift2_def] addsplits [err.split]) 1);
by (Force_tac 1);
qed_spec_mp "coalesce_in_err_list";


Goal "x +_(op #) xs = x#xs";
by (simp_tac (simpset() addsimps [plussub_def]) 1);
val lemma = result();

Goal
 "semilat(err A, Err.le r, lift2 f) ==> \
\ !xs. xs : list n A --> (!ys. ys : list n A --> \
\      (!zs. coalesce (xs +[f] ys) = OK zs --> xs <=[r] zs))";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsplits [err.split_asm] addsimps [lemma,Err.sup_def,lift2_def]) 1);
by (force_tac (claset(), simpset() addsimps [semilat_le_err_OK1]) 1);
qed_spec_mp "coalesce_eq_OK1_D";

Goal
 "semilat(err A, Err.le r, lift2 f) ==> \
\ !xs. xs : list n A --> (!ys. ys : list n A --> \
\      (!zs. coalesce (xs +[f] ys) = OK zs --> ys <=[r] zs))";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsplits [err.split_asm] addsimps [lemma,Err.sup_def,lift2_def]) 1);
by (force_tac (claset(), simpset() addsimps [semilat_le_err_OK2]) 1);
qed_spec_mp "coalesce_eq_OK2_D";

Goalw [semilat_Def,plussub_def,err_def]
 "[| semilat(err A, Err.le r, lift2 f); x:A; y:A; x +_f y = OK z; \
\    u:A; x <=_r u; y <=_r u |] ==> z <=_r u";
by (asm_full_simp_tac (simpset() addsimps [lift2_def]) 1);
by (Clarify_tac 1);
by (rotate_tac ~3 1);
by (etac thin_rl 1);
by (etac thin_rl 1);
by (Force_tac 1);
qed "lift2_le_ub";

Goal
 "semilat(err A, Err.le r, lift2 f) ==> \
\ !xs. xs : list n A --> (!ys. ys : list n A --> \
\      (!zs us. coalesce (xs +[f] ys) = OK zs & xs <=[r] us & ys <=[r] us \
\               & us : list n A --> zs <=[r] us))";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsplits [err.split_asm] addsimps [lemma,Err.sup_def,lift2_def]) 1);
by (Clarify_tac 1);
by (rtac conjI 1);
 by (Blast_tac 2);
by (blast_tac (claset() addIs [lift2_le_ub]) 1);
qed_spec_mp "coalesce_eq_OK_ub_D";

Goal
 "[| x +_f y = Err; semilat(err A, Err.le r, lift2 f); x:A; y:A |] \
\ ==> ~(? u:A. x <=_r u & y <=_r u)";
by (asm_simp_tac (simpset() addsimps [OK_plus_OK_eq_Err_conv RS iffD1]) 1);
qed "lift2_eq_ErrD";

Goal
 "[| semilat(err A, Err.le r, lift2 f)  \
\ |] ==> !xs. xs:list n A --> (!ys. ys:list n A --> \
\  coalesce (xs +[f] ys) = Err --> \
\ ~(? zs:list n A. xs <=[r] zs & ys <=[r] zs))";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsplits [err.split_asm] addsimps [lemma,Err.sup_def,lift2_def]) 1);
 by (blast_tac (claset() addDs [lift2_eq_ErrD]) 1);
by (Blast_tac 1);
qed_spec_mp "coalesce_eq_Err_D";


Goalw [closed_def]
 "closed (err A) (lift2 f) = (!x:A. !y:A. x +_f y : err A)";
by (simp_tac (simpset() addsimps [err_def]) 1);
qed "closed_err_lift2_conv";

Goalw [map2_def]
 "closed (err A) (lift2 f) ==> \
\ !xs. xs : list n A --> (!ys. ys : list n A --> \
\     map2 f xs ys : list n (err A))";
by (induct_tac "n" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [in_list_Suc_iff]) 1);
by (Clarify_tac 1);
by (full_simp_tac (simpset() addsimps [plussub_def,closed_err_lift2_conv]) 1);
by (Blast_tac 1);
qed_spec_mp "closed_map2_list";

Goal
 "closed (err A) (lift2 f) ==> \
\ closed (err (list n A)) (lift2 (sup f))";
by (fast_tac (claset() addss (simpset() addsimps
 [closed_def,plussub_def,sup_def,lift2_def,
  coalesce_in_err_list,closed_map2_list]
 addsplits [err.split])) 1);
qed "closed_lift2_sup";

Goalw [Err.sl_def]
 "err_semilat (A,r,f) ==> \
\ err_semilat (list n A, Listn.le r, sup f)";
by (asm_full_simp_tac (HOL_basic_ss addsimps [split_conv]) 1);
by (simp_tac (HOL_basic_ss addsimps [semilat_Def,plussub_def]) 1);
by (asm_simp_tac(HOL_basic_ss addsimps [semilatDclosedI,closed_lift2_sup]) 1);
by (rtac conjI 1);
 by (dtac semilatDorderI 1);
 by (Asm_full_simp_tac 1);
by (simp_tac (HOL_basic_ss addsimps
     [unfold_lesub_err,Err.le_def,err_def,sup_def,lift2_def]) 1);
by (asm_simp_tac (simpset() addsimps
     [coalesce_eq_OK1_D,coalesce_eq_OK2_D] addsplits [err.split]) 1);
by (blast_tac (claset()addIs[coalesce_eq_OK_ub_D] addDs [coalesce_eq_Err_D]) 1);
qed "err_semilat_sup";

Goalw [Listn.upto_esl_def]
 "!!L. err_semilat L ==> err_semilat(upto_esl m L)";
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
by (fast_tac (claset()
  addSIs [err_semilat_UnionI,err_semilat_sup]
  addDs [lesub_list_impl_same_size] addss (simpset()
  addsimps [plussub_def,Listn.sup_def])) 1);
qed "err_semilat_upto_esl";
