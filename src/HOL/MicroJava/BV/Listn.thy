(*  Title:      HOL/BCV/Listn.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Lists of a fixed length
*)

header "Fixed Length Lists"

theory Listn = Err:

constdefs

 list :: "nat => 'a set => 'a list set"
"list n A == {xs. length xs = n & set xs <= A}"

 le :: "'a ord => ('a list)ord"
"le r == list_all2 (%x y. x <=_r y)"

syntax "@lesublist" :: "'a list => 'a ord => 'a list => bool"
       ("(_ /<=[_] _)" [50, 0, 51] 50)
syntax "@lesssublist" :: "'a list => 'a ord => 'a list => bool"
       ("(_ /<[_] _)" [50, 0, 51] 50)
translations
 "x <=[r] y" == "x <=_(Listn.le r) y"
 "x <[r] y"  == "x <_(Listn.le r) y"

constdefs
 map2 :: "('a => 'b => 'c) => 'a list => 'b list => 'c list"
"map2 f == (%xs ys. map (split f) (zip xs ys))"

syntax "@plussublist" :: "'a list => ('a => 'b => 'c) => 'b list => 'c list"
       ("(_ /+[_] _)" [65, 0, 66] 65)
translations  "x +[f] y" == "x +_(map2 f) y"

consts coalesce :: "'a err list => 'a list err"
primrec
"coalesce [] = OK[]"
"coalesce (ex#exs) = Err.sup (op #) ex (coalesce exs)"

constdefs
 sl :: "nat => 'a sl => 'a list sl"
"sl n == %(A,r,f). (list n A, le r, map2 f)"

 sup :: "('a => 'b => 'c err) => 'a list => 'b list => 'c list err"
"sup f == %xs ys. if size xs = size ys then coalesce(xs +[f] ys) else Err"

 upto_esl :: "nat => 'a esl => 'a list esl"
"upto_esl m == %(A,r,f). (Union{list n A |n. n <= m}, le r, sup f)"

lemmas [simp] = set_update_subsetI

lemma unfold_lesub_list:
  "xs <=[r] ys == Listn.le r xs ys"
  by (simp add: lesub_def)

lemma Nil_le_conv [iff]:
  "([] <=[r] ys) = (ys = [])"
apply (unfold lesub_def Listn.le_def)
apply simp
done

lemma Cons_notle_Nil [iff]: 
  "~ x#xs <=[r] []"
apply (unfold lesub_def Listn.le_def)
apply simp
done


lemma Cons_le_Cons [iff]:
  "x#xs <=[r] y#ys = (x <=_r y & xs <=[r] ys)"
apply (unfold lesub_def Listn.le_def)
apply simp
done

lemma Cons_less_Conss [simp]:
  "order r ==> 
  x#xs <_(Listn.le r) y#ys = 
  (x <_r y & xs <=[r] ys  |  x = y & xs <_(Listn.le r) ys)"
apply (unfold lesssub_def)
apply blast
done  

lemma list_update_le_cong:
  "[| i<size xs; xs <=[r] ys; x <=_r y |] ==> xs[i:=x] <=[r] ys[i:=y]";
apply (unfold unfold_lesub_list)
apply (unfold Listn.le_def)
apply (simp add: list_all2_conv_all_nth nth_list_update)
done


lemma le_listD:
  "[| xs <=[r] ys; p < size xs |] ==> xs!p <=_r ys!p"
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_conv_all_nth)
done

lemma le_list_refl:
  "!x. x <=_r x ==> xs <=[r] xs"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done

lemma le_list_trans:
  "[| order r; xs <=[r] ys; ys <=[r] zs |] ==> xs <=[r] zs"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply clarify
apply simp
apply (blast intro: order_trans)
done

lemma le_list_antisym:
  "[| order r; xs <=[r] ys; ys <=[r] xs |] ==> xs = ys"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply (rule nth_equalityI)
 apply blast
apply clarify
apply simp
apply (blast intro: order_antisym)
done

lemma order_listI [simp, intro!]:
  "order r ==> order(Listn.le r)"
apply (subst order_def)
apply (blast intro: le_list_refl le_list_trans le_list_antisym
             dest: order_refl)
done


lemma lesub_list_impl_same_size [simp]:
  "xs <=[r] ys ==> size ys = size xs"  
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_conv_all_nth)
done 

lemma lesssub_list_impl_same_size:
  "xs <_(Listn.le r) ys ==> size ys = size xs"
apply (unfold lesssub_def)
apply auto
done  

lemma listI:
  "[| length xs = n; set xs <= A |] ==> xs : list n A"
apply (unfold list_def)
apply blast
done

lemma listE_length [simp]:
   "xs : list n A ==> length xs = n"
apply (unfold list_def)
apply blast
done 

lemma less_lengthI:
  "[| xs : list n A; p < n |] ==> p < length xs"
  by simp

lemma listE_set [simp]:
  "xs : list n A ==> set xs <= A"
apply (unfold list_def)
apply blast
done 

lemma list_0 [simp]:
  "list 0 A = {[]}"
apply (unfold list_def)
apply auto
done 

lemma in_list_Suc_iff: 
  "(xs : list (Suc n) A) = (? y:A. ? ys:list n A. xs = y#ys)"
apply (unfold list_def)
apply (case_tac "xs")
apply auto
done 

lemma Cons_in_list_Suc [iff]:
  "(x#xs : list (Suc n) A) = (x:A & xs : list n A)";
apply (simp add: in_list_Suc_iff)
done 

lemma list_not_empty:
  "? a. a:A ==> ? xs. xs : list n A";
apply (induct "n")
 apply simp
apply (simp add: in_list_Suc_iff)
apply blast
done


lemma nth_in [rule_format, simp]:
  "!i n. length xs = n --> set xs <= A --> i < n --> (xs!i) : A"
apply (induct "xs")
 apply simp
apply (simp add: nth_Cons split: nat.split)
done

lemma listE_nth_in:
  "[| xs : list n A; i < n |] ==> (xs!i) : A"
  by auto

lemma listt_update_in_list [simp, intro!]:
  "[| xs : list n A; x:A |] ==> xs[i := x] : list n A"
apply (unfold list_def)
apply simp
done 

lemma plus_list_Nil [simp]:
  "[] +[f] xs = []"
apply (unfold plussub_def map2_def)
apply simp
done 

lemma plus_list_Cons [simp]:
  "(x#xs) +[f] ys = (case ys of [] => [] | y#ys => (x +_f y)#(xs +[f] ys))"
  by (simp add: plussub_def map2_def split: list.split)

lemma length_plus_list [rule_format, simp]:
  "!ys. length(xs +[f] ys) = min(length xs) (length ys)"
apply (induct xs)
 apply simp
apply clarify
apply (simp (no_asm_simp) split: list.split)
done

lemma nth_plus_list [rule_format, simp]:
  "!xs ys i. length xs = n --> length ys = n --> i<n --> 
  (xs +[f] ys)!i = (xs!i) +_f (ys!i)"
apply (induct n)
 apply simp
apply clarify
apply (case_tac xs)
 apply simp
apply (force simp add: nth_Cons split: list.split nat.split)
done


lemma plus_list_ub1 [rule_format]:
  "[| semilat(A,r,f); set xs <= A; set ys <= A; size xs = size ys |] 
  ==> xs <=[r] xs +[f] ys"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done

lemma plus_list_ub2:
  "[| semilat(A,r,f); set xs <= A; set ys <= A; size xs = size ys |]
  ==> ys <=[r] xs +[f] ys"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done 

lemma plus_list_lub [rule_format]:
  "semilat(A,r,f) ==> !xs ys zs. set xs <= A --> set ys <= A --> set zs <= A 
  --> size xs = n & size ys = n --> 
  xs <=[r] zs & ys <=[r] zs --> xs +[f] ys <=[r] zs"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done 

lemma list_update_incr [rule_format]:
  "[| semilat(A,r,f); x:A |] ==> set xs <= A --> 
  (!i. i<size xs --> xs <=[r] xs[i := x +_f xs!i])"
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply (induct xs)
 apply simp
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp add: nth_Cons split: nat.split)
done 

lemma acc_le_listI [intro!]:
  "[| order r; acc r |] ==> acc(Listn.le r)"
apply (unfold acc_def)
apply (subgoal_tac
 "wf(UN n. {(ys,xs). size xs = n & size ys = n & xs <_(Listn.le r) ys})")
 apply (erule wf_subset)
 apply (blast intro: lesssub_list_impl_same_size)
apply (rule wf_UN)
 prefer 2
 apply clarify
 apply (rename_tac m n)
 apply (case_tac "m=n")
  apply simp
 apply (rule conjI)
  apply (fast intro!: equals0I dest: not_sym)
 apply (fast intro!: equals0I dest: not_sym)
apply clarify
apply (rename_tac n)
apply (induct_tac n)
 apply (simp add: lesssub_def cong: conj_cong)
apply (rename_tac k)
apply (simp add: wf_eq_minimal)
apply (simp (no_asm) add: length_Suc_conv cong: conj_cong)
apply clarify
apply (rename_tac M m)
apply (case_tac "? x xs. size xs = k & x#xs : M")
 prefer 2
 apply (erule thin_rl)
 apply (erule thin_rl)
 apply blast
apply (erule_tac x = "{a. ? xs. size xs = k & a#xs:M}" in allE)
apply (erule impE)
 apply blast
apply (thin_tac "? x xs. ?P x xs")
apply clarify
apply (rename_tac maxA xs)
apply (erule_tac x = "{ys. size ys = size xs & maxA#ys : M}" in allE)
apply (erule impE)
 apply blast
apply clarify
apply (thin_tac "m : M")
apply (thin_tac "maxA#xs : M")
apply (rule bexI)
 prefer 2
 apply assumption
apply clarify
apply simp
apply blast
done 

lemma closed_listI:
  "closed S f ==> closed (list n S) (map2 f)"
apply (unfold closed_def)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply simp
done 


lemma semilat_Listn_sl:
  "!!L. semilat L ==> semilat (Listn.sl n L)"
apply (unfold Listn.sl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp (no_asm) only: semilat_Def split_conv)
apply (rule conjI)
 apply simp
apply (rule conjI)
 apply (simp only: semilatDclosedI closed_listI)
apply (simp (no_asm) only: list_def)
apply (simp (no_asm_simp) add: plus_list_ub1 plus_list_ub2 plus_list_lub)
done  


lemma coalesce_in_err_list [rule_format]:
  "!xes. xes : list n (err A) --> coalesce xes : err(list n A)"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp (no_asm) add: plussub_def Err.sup_def lift2_def split: err.split)
apply force
done 

lemma lem: "!!x xs. x +_(op #) xs = x#xs"
  by (simp add: plussub_def)

lemma coalesce_eq_OK1_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) ==> 
  !xs. xs : list n A --> (!ys. ys : list n A --> 
  (!zs. coalesce (xs +[f] ys) = OK zs --> xs <=[r] zs))"
apply (induct n)
  apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK1)
done

lemma coalesce_eq_OK2_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) ==> 
  !xs. xs : list n A --> (!ys. ys : list n A --> 
  (!zs. coalesce (xs +[f] ys) = OK zs --> ys <=[r] zs))"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK2)
done 

lemma lift2_le_ub:
  "[| semilat(err A, Err.le r, lift2 f); x:A; y:A; x +_f y = OK z; 
      u:A; x <=_r u; y <=_r u |] ==> z <=_r u"
apply (unfold semilat_Def plussub_def err_def)
apply (simp add: lift2_def)
apply clarify
apply (rotate_tac -3)
apply (erule thin_rl)
apply (erule thin_rl)
apply force
done 

lemma coalesce_eq_OK_ub_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) ==> 
  !xs. xs : list n A --> (!ys. ys : list n A --> 
  (!zs us. coalesce (xs +[f] ys) = OK zs & xs <=[r] us & ys <=[r] us 
           & us : list n A --> zs <=[r] us))"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp (no_asm_use) split: err.split_asm add: lem Err.sup_def lift2_def)
apply clarify
apply (rule conjI)
 apply (blast intro: lift2_le_ub)
apply blast
done 

lemma lift2_eq_ErrD:
  "[| x +_f y = Err; semilat(err A, Err.le r, lift2 f); x:A; y:A |] 
  ==> ~(? u:A. x <=_r u & y <=_r u)"
  by (simp add: OK_plus_OK_eq_Err_conv [THEN iffD1])


lemma coalesce_eq_Err_D [rule_format]:
  "[| semilat(err A, Err.le r, lift2 f) |] 
  ==> !xs. xs:list n A --> (!ys. ys:list n A --> 
      coalesce (xs +[f] ys) = Err --> 
      ~(? zs:list n A. xs <=[r] zs & ys <=[r] zs))"
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
 apply (blast dest: lift2_eq_ErrD)
apply blast
done 

lemma closed_err_lift2_conv:
  "closed (err A) (lift2 f) = (!x:A. !y:A. x +_f y : err A)"
apply (unfold closed_def)
apply (simp add: err_def)
done 

lemma closed_map2_list [rule_format]:
  "closed (err A) (lift2 f) ==> 
  !xs. xs : list n A --> (!ys. ys : list n A --> 
  map2 f xs ys : list n (err A))"
apply (unfold map2_def)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp add: plussub_def closed_err_lift2_conv)
done 

lemma closed_lift2_sup:
  "closed (err A) (lift2 f) ==> 
  closed (err (list n A)) (lift2 (sup f))"
  by (fastsimp  simp add: closed_def plussub_def sup_def lift2_def
                          coalesce_in_err_list closed_map2_list
                split: err.split)

lemma err_semilat_sup:
  "err_semilat (A,r,f) ==> 
  err_semilat (list n A, Listn.le r, sup f)"
apply (unfold Err.sl_def)
apply (simp only: split_conv)
apply (simp (no_asm) only: semilat_Def plussub_def)
apply (simp (no_asm_simp) only: semilatDclosedI closed_lift2_sup)
apply (rule conjI)
 apply (drule semilatDorderI)
 apply simp
apply (simp (no_asm) only: unfold_lesub_err Err.le_def err_def sup_def lift2_def)
apply (simp (no_asm_simp) add: coalesce_eq_OK1_D coalesce_eq_OK2_D split: err.split)
apply (blast intro: coalesce_eq_OK_ub_D dest: coalesce_eq_Err_D)
done 

lemma err_semilat_upto_esl:
  "!!L. err_semilat L ==> err_semilat(upto_esl m L)"
apply (unfold Listn.upto_esl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (fastsimp intro!: err_semilat_UnionI err_semilat_sup
                dest: lesub_list_impl_same_size 
                simp add: plussub_def Listn.sup_def)
done

end
