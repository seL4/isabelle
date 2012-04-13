(*  Title:      HOL/Matrix_LP/SparseMatrix.thy
    Author:     Steven Obua
*)

theory SparseMatrix
imports Matrix
begin

type_synonym 'a spvec = "(nat * 'a) list"
type_synonym 'a spmat = "'a spvec spvec"

definition sparse_row_vector :: "('a::ab_group_add) spvec \<Rightarrow> 'a matrix"
  where "sparse_row_vector arr = foldl (% m x. m + (singleton_matrix 0 (fst x) (snd x))) 0 arr"

definition sparse_row_matrix :: "('a::ab_group_add) spmat \<Rightarrow> 'a matrix"
  where "sparse_row_matrix arr = foldl (% m r. m + (move_matrix (sparse_row_vector (snd r)) (int (fst r)) 0)) 0 arr"

code_datatype sparse_row_vector sparse_row_matrix

lemma sparse_row_vector_empty [simp]: "sparse_row_vector [] = 0"
  by (simp add: sparse_row_vector_def)

lemma sparse_row_matrix_empty [simp]: "sparse_row_matrix [] = 0"
  by (simp add: sparse_row_matrix_def)

lemmas [code] = sparse_row_vector_empty [symmetric]

lemma foldl_distrstart: "! a x y. (f (g x y) a = g x (f y a)) \<Longrightarrow> (foldl f (g x y) l = g x (foldl f y l))"
  by (induct l arbitrary: x y, auto)

lemma sparse_row_vector_cons[simp]:
  "sparse_row_vector (a # arr) = (singleton_matrix 0 (fst a) (snd a)) + (sparse_row_vector arr)"
  apply (induct arr)
  apply (auto simp add: sparse_row_vector_def)
  apply (simp add: foldl_distrstart [of "\<lambda>m x. m + singleton_matrix 0 (fst x) (snd x)" "\<lambda>x m. singleton_matrix 0 (fst x) (snd x) + m"])
  done

lemma sparse_row_vector_append[simp]:
  "sparse_row_vector (a @ b) = (sparse_row_vector a) + (sparse_row_vector b)"
  by (induct a) auto

lemma nrows_spvec[simp]: "nrows (sparse_row_vector x) <= (Suc 0)"
  apply (induct x)
  apply (simp_all add: add_nrows)
  done

lemma sparse_row_matrix_cons: "sparse_row_matrix (a#arr) = ((move_matrix (sparse_row_vector (snd a)) (int (fst a)) 0)) + sparse_row_matrix arr"
  apply (induct arr)
  apply (auto simp add: sparse_row_matrix_def)
  apply (simp add: foldl_distrstart[of "\<lambda>m x. m + (move_matrix (sparse_row_vector (snd x)) (int (fst x)) 0)" 
    "% a m. (move_matrix (sparse_row_vector (snd a)) (int (fst a)) 0) + m"])
  done

lemma sparse_row_matrix_append: "sparse_row_matrix (arr@brr) = (sparse_row_matrix arr) + (sparse_row_matrix brr)"
  apply (induct arr)
  apply (auto simp add: sparse_row_matrix_cons)
  done

primrec sorted_spvec :: "'a spvec \<Rightarrow> bool"
where
  "sorted_spvec [] = True"
| sorted_spvec_step: "sorted_spvec (a#as) = (case as of [] \<Rightarrow> True | b#bs \<Rightarrow> ((fst a < fst b) & (sorted_spvec as)))" 

primrec sorted_spmat :: "'a spmat \<Rightarrow> bool"
where
  "sorted_spmat [] = True"
| "sorted_spmat (a#as) = ((sorted_spvec (snd a)) & (sorted_spmat as))"

declare sorted_spvec.simps [simp del]

lemma sorted_spvec_empty[simp]: "sorted_spvec [] = True"
by (simp add: sorted_spvec.simps)

lemma sorted_spvec_cons1: "sorted_spvec (a#as) \<Longrightarrow> sorted_spvec as"
apply (induct as)
apply (auto simp add: sorted_spvec.simps)
done

lemma sorted_spvec_cons2: "sorted_spvec (a#b#t) \<Longrightarrow> sorted_spvec (a#t)"
apply (induct t)
apply (auto simp add: sorted_spvec.simps)
done

lemma sorted_spvec_cons3: "sorted_spvec(a#b#t) \<Longrightarrow> fst a < fst b"
apply (auto simp add: sorted_spvec.simps)
done

lemma sorted_sparse_row_vector_zero[rule_format]: "m <= n \<Longrightarrow> sorted_spvec ((n,a)#arr) \<longrightarrow> Rep_matrix (sparse_row_vector arr) j m = 0"
apply (induct arr)
apply (auto)
apply (frule sorted_spvec_cons2,simp)+
apply (frule sorted_spvec_cons3, simp)
done

lemma sorted_sparse_row_matrix_zero[rule_format]: "m <= n \<Longrightarrow> sorted_spvec ((n,a)#arr) \<longrightarrow> Rep_matrix (sparse_row_matrix arr) m j = 0"
  apply (induct arr)
  apply (auto)
  apply (frule sorted_spvec_cons2, simp)
  apply (frule sorted_spvec_cons3, simp)
  apply (simp add: sparse_row_matrix_cons)
  done

primrec minus_spvec :: "('a::ab_group_add) spvec \<Rightarrow> 'a spvec"
where
  "minus_spvec [] = []"
| "minus_spvec (a#as) = (fst a, -(snd a))#(minus_spvec as)"

primrec abs_spvec :: "('a::lattice_ab_group_add_abs) spvec \<Rightarrow> 'a spvec"
where
  "abs_spvec [] = []"
| "abs_spvec (a#as) = (fst a, abs (snd a))#(abs_spvec as)"

lemma sparse_row_vector_minus: 
  "sparse_row_vector (minus_spvec v) = - (sparse_row_vector v)"
  apply (induct v)
  apply (simp_all add: sparse_row_vector_cons)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  done

instance matrix :: (lattice_ab_group_add_abs) lattice_ab_group_add_abs
apply default
unfolding abs_matrix_def .. (*FIXME move*)

lemma sparse_row_vector_abs:
  "sorted_spvec (v :: 'a::lattice_ring spvec) \<Longrightarrow> sparse_row_vector (abs_spvec v) = abs (sparse_row_vector v)"
  apply (induct v)
  apply simp_all
  apply (frule_tac sorted_spvec_cons1, simp)
  apply (simp only: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply auto
  apply (subgoal_tac "Rep_matrix (sparse_row_vector v) 0 a = 0")
  apply (simp)
  apply (rule sorted_sparse_row_vector_zero)
  apply auto
  done

lemma sorted_spvec_minus_spvec:
  "sorted_spvec v \<Longrightarrow> sorted_spvec (minus_spvec v)"
  apply (induct v)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_spvec_abs_spvec:
  "sorted_spvec v \<Longrightarrow> sorted_spvec (abs_spvec v)"
  apply (induct v)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done
  
definition "smult_spvec y = map (% a. (fst a, y * snd a))"  

lemma smult_spvec_empty[simp]: "smult_spvec y [] = []"
  by (simp add: smult_spvec_def)

lemma smult_spvec_cons: "smult_spvec y (a#arr) = (fst a, y * (snd a)) # (smult_spvec y arr)"
  by (simp add: smult_spvec_def)

fun addmult_spvec :: "('a::ring) \<Rightarrow> 'a spvec \<Rightarrow> 'a spvec \<Rightarrow> 'a spvec"
where
  "addmult_spvec y arr [] = arr"
| "addmult_spvec y [] brr = smult_spvec y brr"
| "addmult_spvec y ((i,a)#arr) ((j,b)#brr) = (
    if i < j then ((i,a)#(addmult_spvec y arr ((j,b)#brr))) 
    else (if (j < i) then ((j, y * b)#(addmult_spvec y ((i,a)#arr) brr))
    else ((i, a + y*b)#(addmult_spvec y arr brr))))"
(* Steven used termination "measure (% (y, a, b). length a + (length b))" *)

lemma addmult_spvec_empty1[simp]: "addmult_spvec y [] a = smult_spvec y a"
  by (induct a) auto

lemma addmult_spvec_empty2[simp]: "addmult_spvec y a [] = a"
  by (induct a) auto

lemma sparse_row_vector_map: "(! x y. f (x+y) = (f x) + (f y)) \<Longrightarrow> (f::'a\<Rightarrow>('a::lattice_ring)) 0 = 0 \<Longrightarrow> 
  sparse_row_vector (map (% x. (fst x, f (snd x))) a) = apply_matrix f (sparse_row_vector a)"
  apply (induct a)
  apply (simp_all add: apply_matrix_add)
  done

lemma sparse_row_vector_smult: "sparse_row_vector (smult_spvec y a) = scalar_mult y (sparse_row_vector a)"
  apply (induct a)
  apply (simp_all add: smult_spvec_cons scalar_mult_add)
  done

lemma sparse_row_vector_addmult_spvec: "sparse_row_vector (addmult_spvec (y::'a::lattice_ring) a b) = 
  (sparse_row_vector a) + (scalar_mult y (sparse_row_vector b))"
  apply (induct y a b rule: addmult_spvec.induct)
  apply (simp add: scalar_mult_add smult_spvec_cons sparse_row_vector_smult singleton_matrix_add)+
  done

lemma sorted_smult_spvec: "sorted_spvec a \<Longrightarrow> sorted_spvec (smult_spvec y a)"
  apply (auto simp add: smult_spvec_def)
  apply (induct a)
  apply (auto simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_spvec_addmult_spvec_helper: "\<lbrakk>sorted_spvec (addmult_spvec y ((a, b) # arr) brr); aa < a; sorted_spvec ((a, b) # arr); 
  sorted_spvec ((aa, ba) # brr)\<rbrakk> \<Longrightarrow> sorted_spvec ((aa, y * ba) # addmult_spvec y ((a, b) # arr) brr)"  
  apply (induct brr)
  apply (auto simp add: sorted_spvec.simps)
  done

lemma sorted_spvec_addmult_spvec_helper2: 
 "\<lbrakk>sorted_spvec (addmult_spvec y arr ((aa, ba) # brr)); a < aa; sorted_spvec ((a, b) # arr); sorted_spvec ((aa, ba) # brr)\<rbrakk>
       \<Longrightarrow> sorted_spvec ((a, b) # addmult_spvec y arr ((aa, ba) # brr))"
  apply (induct arr)
  apply (auto simp add: smult_spvec_def sorted_spvec.simps)
  done

lemma sorted_spvec_addmult_spvec_helper3[rule_format]:
  "sorted_spvec (addmult_spvec y arr brr) \<longrightarrow> sorted_spvec ((aa, b) # arr) \<longrightarrow> sorted_spvec ((aa, ba) # brr)
     \<longrightarrow> sorted_spvec ((aa, b + y * ba) # (addmult_spvec y arr brr))"
  apply (induct y arr brr rule: addmult_spvec.induct)
  apply (simp_all add: sorted_spvec.simps smult_spvec_def split:list.split)
  done

lemma sorted_addmult_spvec: "sorted_spvec a \<Longrightarrow> sorted_spvec b \<Longrightarrow> sorted_spvec (addmult_spvec y a b)"
  apply (induct y a b rule: addmult_spvec.induct)
  apply (simp_all add: sorted_smult_spvec)
  apply (rule conjI, intro strip)
  apply (case_tac "~(i < j)")
  apply (simp_all)
  apply (frule_tac as=brr in sorted_spvec_cons1)
  apply (simp add: sorted_spvec_addmult_spvec_helper)
  apply (intro strip | rule conjI)+
  apply (frule_tac as=arr in sorted_spvec_cons1)
  apply (simp add: sorted_spvec_addmult_spvec_helper2)
  apply (intro strip)
  apply (frule_tac as=arr in sorted_spvec_cons1)
  apply (frule_tac as=brr in sorted_spvec_cons1)
  apply (simp)
  apply (simp_all add: sorted_spvec_addmult_spvec_helper3)
  done

fun mult_spvec_spmat :: "('a::lattice_ring) spvec \<Rightarrow> 'a spvec \<Rightarrow> 'a spmat  \<Rightarrow> 'a spvec"
where
(* recdef mult_spvec_spmat "measure (% (c, arr, brr). (length arr) + (length brr))" *)
  "mult_spvec_spmat c [] brr = c"
| "mult_spvec_spmat c arr [] = c"
| "mult_spvec_spmat c ((i,a)#arr) ((j,b)#brr) = (
     if (i < j) then mult_spvec_spmat c arr ((j,b)#brr)
     else if (j < i) then mult_spvec_spmat c ((i,a)#arr) brr 
     else mult_spvec_spmat (addmult_spvec a c b) arr brr)"

lemma sparse_row_mult_spvec_spmat[rule_format]: "sorted_spvec (a::('a::lattice_ring) spvec) \<longrightarrow> sorted_spvec B \<longrightarrow> 
  sparse_row_vector (mult_spvec_spmat c a B) = (sparse_row_vector c) + (sparse_row_vector a) * (sparse_row_matrix B)"
proof -
  have comp_1: "!! a b. a < b \<Longrightarrow> Suc 0 <= nat ((int b)-(int a))" by arith
  have not_iff: "!! a b. a = b \<Longrightarrow> (~ a) = (~ b)" by simp
  have max_helper: "!! a b. ~ (a <= max (Suc a) b) \<Longrightarrow> False"
    by arith
  {
    fix a 
    fix v
    assume a:"a < nrows(sparse_row_vector v)"
    have b:"nrows(sparse_row_vector v) <= 1" by simp
    note dummy = less_le_trans[of a "nrows (sparse_row_vector v)" 1, OF a b]   
    then have "a = 0" by simp
  }
  note nrows_helper = this
  show ?thesis
    apply (induct c a B rule: mult_spvec_spmat.induct)
    apply simp+
    apply (rule conjI)
    apply (intro strip)
    apply (frule_tac as=brr in sorted_spvec_cons1)
    apply (simp add: algebra_simps sparse_row_matrix_cons)
    apply (simplesubst Rep_matrix_zero_imp_mult_zero) 
    apply (simp)
    apply (rule disjI2)
    apply (intro strip)
    apply (subst nrows)
    apply (rule  order_trans[of _ 1])
    apply (simp add: comp_1)+
    apply (subst Rep_matrix_zero_imp_mult_zero)
    apply (intro strip)
    apply (case_tac "k <= j")
    apply (rule_tac m1 = k and n1 = i and a1 = a in ssubst[OF sorted_sparse_row_vector_zero])
    apply (simp_all)
    apply (rule disjI2)
    apply (rule nrows)
    apply (rule order_trans[of _ 1])
    apply (simp_all add: comp_1)
    
    apply (intro strip | rule conjI)+
    apply (frule_tac as=arr in sorted_spvec_cons1)
    apply (simp add: algebra_simps)
    apply (subst Rep_matrix_zero_imp_mult_zero)
    apply (simp)
    apply (rule disjI2)
    apply (intro strip)
    apply (simp add: sparse_row_matrix_cons)
    apply (case_tac "i <= j")  
    apply (erule sorted_sparse_row_matrix_zero)  
    apply (simp_all)
    apply (intro strip)
    apply (case_tac "i=j")
    apply (simp_all)
    apply (frule_tac as=arr in sorted_spvec_cons1)
    apply (frule_tac as=brr in sorted_spvec_cons1)
    apply (simp add: sparse_row_matrix_cons algebra_simps sparse_row_vector_addmult_spvec)
    apply (rule_tac B1 = "sparse_row_matrix brr" in ssubst[OF Rep_matrix_zero_imp_mult_zero])
    apply (auto)
    apply (rule sorted_sparse_row_matrix_zero)
    apply (simp_all)
    apply (rule_tac A1 = "sparse_row_vector arr" in ssubst[OF Rep_matrix_zero_imp_mult_zero])
    apply (auto)
    apply (rule_tac m=k and n = j and a = a and arr=arr in sorted_sparse_row_vector_zero)
    apply (simp_all)
    apply (drule nrows_notzero)
    apply (drule nrows_helper)
    apply (arith)
    
    apply (subst Rep_matrix_inject[symmetric])
    apply (rule ext)+
    apply (simp)
    apply (subst Rep_matrix_mult)
    apply (rule_tac j1=j in ssubst[OF foldseq_almostzero])
    apply (simp_all)
    apply (intro strip, rule conjI)
    apply (intro strip)
    apply (drule_tac max_helper)
    apply (simp)
    apply (auto)
    apply (rule zero_imp_mult_zero)
    apply (rule disjI2)
    apply (rule nrows)
    apply (rule order_trans[of _ 1])
    apply (simp)
    apply (simp)
    done
qed

lemma sorted_mult_spvec_spmat[rule_format]: 
  "sorted_spvec (c::('a::lattice_ring) spvec) \<longrightarrow> sorted_spmat B \<longrightarrow> sorted_spvec (mult_spvec_spmat c a B)"
  apply (induct c a B rule: mult_spvec_spmat.induct)
  apply (simp_all add: sorted_addmult_spvec)
  done

primrec mult_spmat :: "('a::lattice_ring) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat"
where
  "mult_spmat [] A = []"
| "mult_spmat (a#as) A = (fst a, mult_spvec_spmat [] (snd a) A)#(mult_spmat as A)"

lemma sparse_row_mult_spmat: 
  "sorted_spmat A \<Longrightarrow> sorted_spvec B \<Longrightarrow>
   sparse_row_matrix (mult_spmat A B) = (sparse_row_matrix A) * (sparse_row_matrix B)"
  apply (induct A)
  apply (auto simp add: sparse_row_matrix_cons sparse_row_mult_spvec_spmat algebra_simps move_matrix_mult)
  done

lemma sorted_spvec_mult_spmat[rule_format]:
  "sorted_spvec (A::('a::lattice_ring) spmat) \<longrightarrow> sorted_spvec (mult_spmat A B)"
  apply (induct A)
  apply (auto)
  apply (drule sorted_spvec_cons1, simp)
  apply (case_tac A)
  apply (auto simp add: sorted_spvec.simps)
  done

lemma sorted_spmat_mult_spmat:
  "sorted_spmat (B::('a::lattice_ring) spmat) \<Longrightarrow> sorted_spmat (mult_spmat A B)"
  apply (induct A)
  apply (auto simp add: sorted_mult_spvec_spmat) 
  done


fun add_spvec :: "('a::lattice_ab_group_add) spvec \<Rightarrow> 'a spvec \<Rightarrow> 'a spvec"
where
(* "measure (% (a, b). length a + (length b))" *)
  "add_spvec arr [] = arr"
| "add_spvec [] brr = brr"
| "add_spvec ((i,a)#arr) ((j,b)#brr) = (
     if i < j then (i,a)#(add_spvec arr ((j,b)#brr)) 
     else if (j < i) then (j,b) # add_spvec ((i,a)#arr) brr
     else (i, a+b) # add_spvec arr brr)"

lemma add_spvec_empty1[simp]: "add_spvec [] a = a"
by (cases a, auto)

lemma sparse_row_vector_add: "sparse_row_vector (add_spvec a b) = (sparse_row_vector a) + (sparse_row_vector b)"
  apply (induct a b rule: add_spvec.induct)
  apply (simp_all add: singleton_matrix_add)
  done

fun add_spmat :: "('a::lattice_ab_group_add) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat"
where
(* "measure (% (A,B). (length A)+(length B))" *)
  "add_spmat [] bs = bs"
| "add_spmat as [] = as"
| "add_spmat ((i,a)#as) ((j,b)#bs) = (
    if i < j then 
      (i,a) # add_spmat as ((j,b)#bs)
    else if j < i then
      (j,b) # add_spmat ((i,a)#as) bs
    else
      (i, add_spvec a b) # add_spmat as bs)"

lemma add_spmat_Nil2[simp]: "add_spmat as [] = as"
by(cases as) auto

lemma sparse_row_add_spmat: "sparse_row_matrix (add_spmat A B) = (sparse_row_matrix A) + (sparse_row_matrix B)"
  apply (induct A B rule: add_spmat.induct)
  apply (auto simp add: sparse_row_matrix_cons sparse_row_vector_add move_matrix_add)
  done

lemmas [code] = sparse_row_add_spmat [symmetric]
lemmas [code] = sparse_row_vector_add [symmetric]

lemma sorted_add_spvec_helper1[rule_format]: "add_spvec ((a,b)#arr) brr = (ab, bb) # list \<longrightarrow> (ab = a | (brr \<noteq> [] & ab = fst (hd brr)))"
  proof - 
    have "(! x ab a. x = (a,b)#arr \<longrightarrow> add_spvec x brr = (ab, bb) # list \<longrightarrow> (ab = a | (ab = fst (hd brr))))"
      by (induct brr rule: add_spvec.induct) (auto split:if_splits)
    then show ?thesis
      by (case_tac brr, auto)
  qed

lemma sorted_add_spmat_helper1[rule_format]: "add_spmat ((a,b)#arr) brr = (ab, bb) # list \<longrightarrow> (ab = a | (brr \<noteq> [] & ab = fst (hd brr)))"
  proof - 
    have "(! x ab a. x = (a,b)#arr \<longrightarrow> add_spmat x brr = (ab, bb) # list \<longrightarrow> (ab = a | (ab = fst (hd brr))))"
      by (rule add_spmat.induct) (auto split:if_splits)
    then show ?thesis
      by (case_tac brr, auto)
  qed

lemma sorted_add_spvec_helper: "add_spvec arr brr = (ab, bb) # list \<Longrightarrow> ((arr \<noteq> [] & ab = fst (hd arr)) | (brr \<noteq> [] & ab = fst (hd brr)))"
  apply (induct arr brr rule: add_spvec.induct)
  apply (auto split:if_splits)
  done

lemma sorted_add_spmat_helper: "add_spmat arr brr = (ab, bb) # list \<Longrightarrow> ((arr \<noteq> [] & ab = fst (hd arr)) | (brr \<noteq> [] & ab = fst (hd brr)))"
  apply (induct arr brr rule: add_spmat.induct)
  apply (auto split:if_splits)
  done

lemma add_spvec_commute: "add_spvec a b = add_spvec b a"
by (induct a b rule: add_spvec.induct) auto

lemma add_spmat_commute: "add_spmat a b = add_spmat b a"
  apply (induct a b rule: add_spmat.induct)
  apply (simp_all add: add_spvec_commute)
  done
  
lemma sorted_add_spvec_helper2: "add_spvec ((a,b)#arr) brr = (ab, bb) # list \<Longrightarrow> aa < a \<Longrightarrow> sorted_spvec ((aa, ba) # brr) \<Longrightarrow> aa < ab"
  apply (drule sorted_add_spvec_helper1)
  apply (auto)
  apply (case_tac brr)
  apply (simp_all)
  apply (drule_tac sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_add_spmat_helper2: "add_spmat ((a,b)#arr) brr = (ab, bb) # list \<Longrightarrow> aa < a \<Longrightarrow> sorted_spvec ((aa, ba) # brr) \<Longrightarrow> aa < ab"
  apply (drule sorted_add_spmat_helper1)
  apply (auto)
  apply (case_tac brr)
  apply (simp_all)
  apply (drule_tac sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_spvec_add_spvec[rule_format]: "sorted_spvec a \<longrightarrow> sorted_spvec b \<longrightarrow> sorted_spvec (add_spvec a b)"
  apply (induct a b rule: add_spvec.induct)
  apply (simp_all)
  apply (rule conjI)
  apply (clarsimp)
  apply (frule_tac as=brr in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (clarsimp simp: sorted_add_spvec_helper2 split: list.split)
  apply (clarify)
  apply (rule conjI)
  apply (clarify)
  apply (frule_tac as=arr in sorted_spvec_cons1, simp)
  apply (subst sorted_spvec_step)
  apply (clarsimp simp: sorted_add_spvec_helper2 add_spvec_commute split: list.split)
  apply (clarify)
  apply (frule_tac as=arr in sorted_spvec_cons1)
  apply (frule_tac as=brr in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarsimp)
  apply (drule_tac sorted_add_spvec_helper)
  apply (auto simp: neq_Nil_conv)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_spvec_add_spmat[rule_format]: "sorted_spvec A \<longrightarrow> sorted_spvec B \<longrightarrow> sorted_spvec (add_spmat A B)"
  apply (induct A B rule: add_spmat.induct)
  apply (simp_all)
  apply (rule conjI)
  apply (intro strip)
  apply (simp)
  apply (frule_tac as=bs in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (simp add: sorted_add_spmat_helper2)
  apply (clarify)
  apply (rule conjI)
  apply (clarify)
  apply (frule_tac as=as in sorted_spvec_cons1, simp)
  apply (subst sorted_spvec_step)
  apply (clarsimp simp: sorted_add_spmat_helper2 add_spmat_commute split: list.split)
  apply (clarsimp)
  apply (frule_tac as=as in sorted_spvec_cons1)
  apply (frule_tac as=bs in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (drule_tac sorted_add_spmat_helper)
  apply (auto simp:neq_Nil_conv)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_spmat_add_spmat[rule_format]: "sorted_spmat A \<Longrightarrow> sorted_spmat B \<Longrightarrow> sorted_spmat (add_spmat A B)"
  apply (induct A B rule: add_spmat.induct)
  apply (simp_all add: sorted_spvec_add_spvec)
  done

fun le_spvec :: "('a::lattice_ab_group_add) spvec \<Rightarrow> 'a spvec \<Rightarrow> bool"
where
(* "measure (% (a,b). (length a) + (length b))" *)
  "le_spvec [] [] = True"
| "le_spvec ((_,a)#as) [] = (a <= 0 & le_spvec as [])"
| "le_spvec [] ((_,b)#bs) = (0 <= b & le_spvec [] bs)"
| "le_spvec ((i,a)#as) ((j,b)#bs) = (
    if (i < j) then a <= 0 & le_spvec as ((j,b)#bs)
    else if (j < i) then 0 <= b & le_spvec ((i,a)#as) bs
    else a <= b & le_spvec as bs)"

fun le_spmat :: "('a::lattice_ab_group_add) spmat \<Rightarrow> 'a spmat \<Rightarrow> bool"
where
(* "measure (% (a,b). (length a) + (length b))" *)
  "le_spmat [] [] = True"
| "le_spmat ((i,a)#as) [] = (le_spvec a [] & le_spmat as [])"
| "le_spmat [] ((j,b)#bs) = (le_spvec [] b & le_spmat [] bs)"
| "le_spmat ((i,a)#as) ((j,b)#bs) = (
    if i < j then (le_spvec a [] & le_spmat as ((j,b)#bs))
    else if j < i then (le_spvec [] b & le_spmat ((i,a)#as) bs)
    else (le_spvec a b & le_spmat as bs))"

definition disj_matrices :: "('a::zero) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool" where
  "disj_matrices A B \<longleftrightarrow>
    (! j i. (Rep_matrix A j i \<noteq> 0) \<longrightarrow> (Rep_matrix B j i = 0)) & (! j i. (Rep_matrix B j i \<noteq> 0) \<longrightarrow> (Rep_matrix A j i = 0))"  

declare [[simp_depth_limit = 6]]

lemma disj_matrices_contr1: "disj_matrices A B \<Longrightarrow> Rep_matrix A j i \<noteq> 0 \<Longrightarrow> Rep_matrix B j i = 0"
   by (simp add: disj_matrices_def)

lemma disj_matrices_contr2: "disj_matrices A B \<Longrightarrow> Rep_matrix B j i \<noteq> 0 \<Longrightarrow> Rep_matrix A j i = 0"
   by (simp add: disj_matrices_def)


lemma disj_matrices_add: "disj_matrices A B \<Longrightarrow> disj_matrices C D \<Longrightarrow> disj_matrices A D \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (A + B <= C + D) = (A <= C & B <= (D::('a::lattice_ab_group_add) matrix))"
  apply (auto)
  apply (simp (no_asm_use) only: le_matrix_def disj_matrices_def)
  apply (intro strip)
  apply (erule conjE)+
  apply (drule_tac j=j and i=i in spec2)+
  apply (case_tac "Rep_matrix B j i = 0")
  apply (case_tac "Rep_matrix D j i = 0")
  apply (simp_all)
  apply (simp (no_asm_use) only: le_matrix_def disj_matrices_def)
  apply (intro strip)
  apply (erule conjE)+
  apply (drule_tac j=j and i=i in spec2)+
  apply (case_tac "Rep_matrix A j i = 0")
  apply (case_tac "Rep_matrix C j i = 0")
  apply (simp_all)
  apply (erule add_mono)
  apply (assumption)
  done

lemma disj_matrices_zero1[simp]: "disj_matrices 0 B"
by (simp add: disj_matrices_def)

lemma disj_matrices_zero2[simp]: "disj_matrices A 0"
by (simp add: disj_matrices_def)

lemma disj_matrices_commute: "disj_matrices A B = disj_matrices B A"
by (auto simp add: disj_matrices_def)

lemma disj_matrices_add_le_zero: "disj_matrices A B \<Longrightarrow>
  (A + B <= 0) = (A <= 0 & (B::('a::lattice_ab_group_add) matrix) <= 0)"
by (rule disj_matrices_add[of A B 0 0, simplified])
 
lemma disj_matrices_add_zero_le: "disj_matrices A B \<Longrightarrow>
  (0 <= A + B) = (0 <= A & 0 <= (B::('a::lattice_ab_group_add) matrix))"
by (rule disj_matrices_add[of 0 0 A B, simplified])

lemma disj_matrices_add_x_le: "disj_matrices A B \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (A <= B + C) = (A <= C & 0 <= (B::('a::lattice_ab_group_add) matrix))"
by (auto simp add: disj_matrices_add[of 0 A B C, simplified])

lemma disj_matrices_add_le_x: "disj_matrices A B \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (B + A <= C) = (A <= C &  (B::('a::lattice_ab_group_add) matrix) <= 0)"
by (auto simp add: disj_matrices_add[of B A 0 C,simplified] disj_matrices_commute)

lemma disj_sparse_row_singleton: "i <= j \<Longrightarrow> sorted_spvec((j,y)#v) \<Longrightarrow> disj_matrices (sparse_row_vector v) (singleton_matrix 0 i x)"
  apply (simp add: disj_matrices_def)
  apply (rule conjI)
  apply (rule neg_imp)
  apply (simp)
  apply (intro strip)
  apply (rule sorted_sparse_row_vector_zero)
  apply (simp_all)
  apply (intro strip)
  apply (rule sorted_sparse_row_vector_zero)
  apply (simp_all)
  done 

lemma disj_matrices_x_add: "disj_matrices A B \<Longrightarrow> disj_matrices A C \<Longrightarrow> disj_matrices (A::('a::lattice_ab_group_add) matrix) (B+C)"
  apply (simp add: disj_matrices_def)
  apply (auto)
  apply (drule_tac j=j and i=i in spec2)+
  apply (case_tac "Rep_matrix B j i = 0")
  apply (case_tac "Rep_matrix C j i = 0")
  apply (simp_all)
  done

lemma disj_matrices_add_x: "disj_matrices A B \<Longrightarrow> disj_matrices A C \<Longrightarrow> disj_matrices (B+C) (A::('a::lattice_ab_group_add) matrix)" 
  by (simp add: disj_matrices_x_add disj_matrices_commute)

lemma disj_singleton_matrices[simp]: "disj_matrices (singleton_matrix j i x) (singleton_matrix u v y) = (j \<noteq> u | i \<noteq> v | x = 0 | y = 0)" 
  by (auto simp add: disj_matrices_def)

lemma disj_move_sparse_vec_mat[simplified disj_matrices_commute]: 
  "j <= a \<Longrightarrow> sorted_spvec((a,c)#as) \<Longrightarrow> disj_matrices (move_matrix (sparse_row_vector b) (int j) i) (sparse_row_matrix as)"
  apply (auto simp add: disj_matrices_def)
  apply (drule nrows_notzero)
  apply (drule less_le_trans[OF _ nrows_spvec])
  apply (subgoal_tac "ja = j")
  apply (simp add: sorted_sparse_row_matrix_zero)
  apply (arith)
  apply (rule nrows)
  apply (rule order_trans[of _ 1 _])
  apply (simp)
  apply (case_tac "nat (int ja - int j) = 0")
  apply (case_tac "ja = j")
  apply (simp add: sorted_sparse_row_matrix_zero)
  apply arith+
  done

lemma disj_move_sparse_row_vector_twice:
  "j \<noteq> u \<Longrightarrow> disj_matrices (move_matrix (sparse_row_vector a) j i) (move_matrix (sparse_row_vector b) u v)"
  apply (auto simp add: disj_matrices_def)
  apply (rule nrows, rule order_trans[of _ 1], simp, drule nrows_notzero, drule less_le_trans[OF _ nrows_spvec], arith)+
  done

lemma le_spvec_iff_sparse_row_le[rule_format]: "(sorted_spvec a) \<longrightarrow> (sorted_spvec b) \<longrightarrow> (le_spvec a b) = (sparse_row_vector a <= sparse_row_vector b)"
  apply (induct a b rule: le_spvec.induct)
  apply (simp_all add: sorted_spvec_cons1 disj_matrices_add_le_zero disj_matrices_add_zero_le 
    disj_sparse_row_singleton[OF order_refl] disj_matrices_commute)
  apply (rule conjI, intro strip)
  apply (simp add: sorted_spvec_cons1)
  apply (subst disj_matrices_add_x_le)
  apply (simp add: disj_sparse_row_singleton[OF less_imp_le] disj_matrices_x_add disj_matrices_commute)
  apply (simp add: disj_sparse_row_singleton[OF order_refl] disj_matrices_commute)
  apply (simp, blast)
  apply (intro strip, rule conjI, intro strip)
  apply (simp add: sorted_spvec_cons1)
  apply (subst disj_matrices_add_le_x)
  apply (simp_all add: disj_sparse_row_singleton[OF order_refl] disj_sparse_row_singleton[OF less_imp_le] disj_matrices_commute disj_matrices_x_add)
  apply (blast)
  apply (intro strip)
  apply (simp add: sorted_spvec_cons1)
  apply (case_tac "a=b", simp_all)
  apply (subst disj_matrices_add)
  apply (simp_all add: disj_sparse_row_singleton[OF order_refl] disj_matrices_commute)
  done

lemma le_spvec_empty2_sparse_row[rule_format]: "sorted_spvec b \<longrightarrow> le_spvec b [] = (sparse_row_vector b <= 0)"
  apply (induct b)
  apply (simp_all add: sorted_spvec_cons1)
  apply (intro strip)
  apply (subst disj_matrices_add_le_zero)
  apply (auto simp add: disj_matrices_commute disj_sparse_row_singleton[OF order_refl] sorted_spvec_cons1)
  done

lemma le_spvec_empty1_sparse_row[rule_format]: "(sorted_spvec b) \<longrightarrow> (le_spvec [] b = (0 <= sparse_row_vector b))"
  apply (induct b)
  apply (simp_all add: sorted_spvec_cons1)
  apply (intro strip)
  apply (subst disj_matrices_add_zero_le)
  apply (auto simp add: disj_matrices_commute disj_sparse_row_singleton[OF order_refl] sorted_spvec_cons1)
  done

lemma le_spmat_iff_sparse_row_le[rule_format]: "(sorted_spvec A) \<longrightarrow> (sorted_spmat A) \<longrightarrow> (sorted_spvec B) \<longrightarrow> (sorted_spmat B) \<longrightarrow> 
  le_spmat A B = (sparse_row_matrix A <= sparse_row_matrix B)"
  apply (induct A B rule: le_spmat.induct)
  apply (simp add: sparse_row_matrix_cons disj_matrices_add_le_zero disj_matrices_add_zero_le disj_move_sparse_vec_mat[OF order_refl] 
    disj_matrices_commute sorted_spvec_cons1 le_spvec_empty2_sparse_row le_spvec_empty1_sparse_row)+ 
  apply (rule conjI, intro strip)
  apply (simp add: sorted_spvec_cons1)
  apply (subst disj_matrices_add_x_le)
  apply (rule disj_matrices_add_x)
  apply (simp add: disj_move_sparse_row_vector_twice)
  apply (simp add: disj_move_sparse_vec_mat[OF less_imp_le] disj_matrices_commute)
  apply (simp add: disj_move_sparse_vec_mat[OF order_refl] disj_matrices_commute)
  apply (simp, blast)
  apply (intro strip, rule conjI, intro strip)
  apply (simp add: sorted_spvec_cons1)
  apply (subst disj_matrices_add_le_x)
  apply (simp add: disj_move_sparse_vec_mat[OF order_refl])
  apply (rule disj_matrices_x_add)
  apply (simp add: disj_move_sparse_row_vector_twice)
  apply (simp add: disj_move_sparse_vec_mat[OF less_imp_le] disj_matrices_commute)
  apply (simp, blast)
  apply (intro strip)
  apply (case_tac "i=j")
  apply (simp_all)
  apply (subst disj_matrices_add)
  apply (simp_all add: disj_matrices_commute disj_move_sparse_vec_mat[OF order_refl])
  apply (simp add: sorted_spvec_cons1 le_spvec_iff_sparse_row_le)
  done

declare [[simp_depth_limit = 999]]

primrec abs_spmat :: "('a::lattice_ring) spmat \<Rightarrow> 'a spmat"
where
  "abs_spmat [] = []"
| "abs_spmat (a#as) = (fst a, abs_spvec (snd a))#(abs_spmat as)"

primrec minus_spmat :: "('a::lattice_ring) spmat \<Rightarrow> 'a spmat"
where
  "minus_spmat [] = []"
| "minus_spmat (a#as) = (fst a, minus_spvec (snd a))#(minus_spmat as)"

lemma sparse_row_matrix_minus:
  "sparse_row_matrix (minus_spmat A) = - (sparse_row_matrix A)"
  apply (induct A)
  apply (simp_all add: sparse_row_vector_minus sparse_row_matrix_cons)
  apply (subst Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  done

lemma Rep_sparse_row_vector_zero: "x \<noteq> 0 \<Longrightarrow> Rep_matrix (sparse_row_vector v) x y = 0"
proof -
  assume x:"x \<noteq> 0"
  have r:"nrows (sparse_row_vector v) <= Suc 0" by (rule nrows_spvec)
  show ?thesis
    apply (rule nrows)
    apply (subgoal_tac "Suc 0 <= x")
    apply (insert r)
    apply (simp only:)
    apply (insert x)
    apply arith
    done
qed
    
lemma sparse_row_matrix_abs:
  "sorted_spvec A \<Longrightarrow> sorted_spmat A \<Longrightarrow> sparse_row_matrix (abs_spmat A) = abs (sparse_row_matrix A)"
  apply (induct A)
  apply (simp_all add: sparse_row_vector_abs sparse_row_matrix_cons)
  apply (frule_tac sorted_spvec_cons1, simp)
  apply (simplesubst Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply auto
  apply (case_tac "x=a")
  apply (simp)
  apply (simplesubst sorted_sparse_row_matrix_zero)
  apply auto
  apply (simplesubst Rep_sparse_row_vector_zero)
  apply simp_all
  done

lemma sorted_spvec_minus_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec (minus_spmat A)"
  apply (induct A)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done 

lemma sorted_spvec_abs_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec (abs_spmat A)" 
  apply (induct A)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_spmat_minus_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat (minus_spmat A)"
  apply (induct A)
  apply (simp_all add: sorted_spvec_minus_spvec)
  done

lemma sorted_spmat_abs_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat (abs_spmat A)"
  apply (induct A)
  apply (simp_all add: sorted_spvec_abs_spvec)
  done

definition diff_spmat :: "('a::lattice_ring) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat"
  where "diff_spmat A B = add_spmat A (minus_spmat B)"

lemma sorted_spmat_diff_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat B \<Longrightarrow> sorted_spmat (diff_spmat A B)"
  by (simp add: diff_spmat_def sorted_spmat_minus_spmat sorted_spmat_add_spmat)

lemma sorted_spvec_diff_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec B \<Longrightarrow> sorted_spvec (diff_spmat A B)"
  by (simp add: diff_spmat_def sorted_spvec_minus_spmat sorted_spvec_add_spmat)

lemma sparse_row_diff_spmat: "sparse_row_matrix (diff_spmat A B ) = (sparse_row_matrix A) - (sparse_row_matrix B)"
  by (simp add: diff_spmat_def sparse_row_add_spmat sparse_row_matrix_minus)

definition sorted_sparse_matrix :: "'a spmat \<Rightarrow> bool"
  where "sorted_sparse_matrix A \<longleftrightarrow> sorted_spvec A & sorted_spmat A"

lemma sorted_sparse_matrix_imp_spvec: "sorted_sparse_matrix A \<Longrightarrow> sorted_spvec A"
  by (simp add: sorted_sparse_matrix_def)

lemma sorted_sparse_matrix_imp_spmat: "sorted_sparse_matrix A \<Longrightarrow> sorted_spmat A"
  by (simp add: sorted_sparse_matrix_def)

lemmas sorted_sp_simps = 
  sorted_spvec.simps
  sorted_spmat.simps
  sorted_sparse_matrix_def

lemma bool1: "(\<not> True) = False"  by blast
lemma bool2: "(\<not> False) = True"  by blast
lemma bool3: "((P\<Colon>bool) \<and> True) = P" by blast
lemma bool4: "(True \<and> (P\<Colon>bool)) = P" by blast
lemma bool5: "((P\<Colon>bool) \<and> False) = False" by blast
lemma bool6: "(False \<and> (P\<Colon>bool)) = False" by blast
lemma bool7: "((P\<Colon>bool) \<or> True) = True" by blast
lemma bool8: "(True \<or> (P\<Colon>bool)) = True" by blast
lemma bool9: "((P\<Colon>bool) \<or> False) = P" by blast
lemma bool10: "(False \<or> (P\<Colon>bool)) = P" by blast
lemmas boolarith = bool1 bool2 bool3 bool4 bool5 bool6 bool7 bool8 bool9 bool10

lemma if_case_eq: "(if b then x else y) = (case b of True => x | False => y)" by simp

primrec pprt_spvec :: "('a::{lattice_ab_group_add}) spvec \<Rightarrow> 'a spvec"
where
  "pprt_spvec [] = []"
| "pprt_spvec (a#as) = (fst a, pprt (snd a)) # (pprt_spvec as)"

primrec nprt_spvec :: "('a::{lattice_ab_group_add}) spvec \<Rightarrow> 'a spvec"
where
  "nprt_spvec [] = []"
| "nprt_spvec (a#as) = (fst a, nprt (snd a)) # (nprt_spvec as)"

primrec pprt_spmat :: "('a::{lattice_ab_group_add}) spmat \<Rightarrow> 'a spmat"
where
  "pprt_spmat [] = []"
| "pprt_spmat (a#as) = (fst a, pprt_spvec (snd a))#(pprt_spmat as)"

primrec nprt_spmat :: "('a::{lattice_ab_group_add}) spmat \<Rightarrow> 'a spmat"
where
  "nprt_spmat [] = []"
| "nprt_spmat (a#as) = (fst a, nprt_spvec (snd a))#(nprt_spmat as)"


lemma pprt_add: "disj_matrices A (B::(_::lattice_ring) matrix) \<Longrightarrow> pprt (A+B) = pprt A + pprt B"
  apply (simp add: pprt_def sup_matrix_def)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  apply (case_tac "Rep_matrix A x xa \<noteq> 0")
  apply (simp_all add: disj_matrices_contr1)
  done

lemma nprt_add: "disj_matrices A (B::(_::lattice_ring) matrix) \<Longrightarrow> nprt (A+B) = nprt A + nprt B"
  apply (simp add: nprt_def inf_matrix_def)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  apply (case_tac "Rep_matrix A x xa \<noteq> 0")
  apply (simp_all add: disj_matrices_contr1)
  done

lemma pprt_singleton[simp]: "pprt (singleton_matrix j i (x::_::lattice_ring)) = singleton_matrix j i (pprt x)"
  apply (simp add: pprt_def sup_matrix_def)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  done

lemma nprt_singleton[simp]: "nprt (singleton_matrix j i (x::_::lattice_ring)) = singleton_matrix j i (nprt x)"
  apply (simp add: nprt_def inf_matrix_def)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  done

lemma less_imp_le: "a < b \<Longrightarrow> a <= (b::_::order)" by (simp add: less_def)

lemma sparse_row_vector_pprt: "sorted_spvec (v :: 'a::lattice_ring spvec) \<Longrightarrow> sparse_row_vector (pprt_spvec v) = pprt (sparse_row_vector v)"
  apply (induct v)
  apply (simp_all)
  apply (frule sorted_spvec_cons1, auto)
  apply (subst pprt_add)
  apply (subst disj_matrices_commute)
  apply (rule disj_sparse_row_singleton)
  apply auto
  done

lemma sparse_row_vector_nprt: "sorted_spvec (v :: 'a::lattice_ring spvec) \<Longrightarrow> sparse_row_vector (nprt_spvec v) = nprt (sparse_row_vector v)"
  apply (induct v)
  apply (simp_all)
  apply (frule sorted_spvec_cons1, auto)
  apply (subst nprt_add)
  apply (subst disj_matrices_commute)
  apply (rule disj_sparse_row_singleton)
  apply auto
  done
  
  
lemma pprt_move_matrix: "pprt (move_matrix (A::('a::lattice_ring) matrix) j i) = move_matrix (pprt A) j i"
  apply (simp add: pprt_def)
  apply (simp add: sup_matrix_def)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply (simp)
  done

lemma nprt_move_matrix: "nprt (move_matrix (A::('a::lattice_ring) matrix) j i) = move_matrix (nprt A) j i"
  apply (simp add: nprt_def)
  apply (simp add: inf_matrix_def)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply (simp)
  done

lemma sparse_row_matrix_pprt: "sorted_spvec (m :: 'a::lattice_ring spmat) \<Longrightarrow> sorted_spmat m \<Longrightarrow> sparse_row_matrix (pprt_spmat m) = pprt (sparse_row_matrix m)"
  apply (induct m)
  apply simp
  apply simp
  apply (frule sorted_spvec_cons1)
  apply (simp add: sparse_row_matrix_cons sparse_row_vector_pprt)
  apply (subst pprt_add)
  apply (subst disj_matrices_commute)
  apply (rule disj_move_sparse_vec_mat)
  apply auto
  apply (simp add: sorted_spvec.simps)
  apply (simp split: list.split)
  apply auto
  apply (simp add: pprt_move_matrix)
  done

lemma sparse_row_matrix_nprt: "sorted_spvec (m :: 'a::lattice_ring spmat) \<Longrightarrow> sorted_spmat m \<Longrightarrow> sparse_row_matrix (nprt_spmat m) = nprt (sparse_row_matrix m)"
  apply (induct m)
  apply simp
  apply simp
  apply (frule sorted_spvec_cons1)
  apply (simp add: sparse_row_matrix_cons sparse_row_vector_nprt)
  apply (subst nprt_add)
  apply (subst disj_matrices_commute)
  apply (rule disj_move_sparse_vec_mat)
  apply auto
  apply (simp add: sorted_spvec.simps)
  apply (simp split: list.split)
  apply auto
  apply (simp add: nprt_move_matrix)
  done

lemma sorted_pprt_spvec: "sorted_spvec v \<Longrightarrow> sorted_spvec (pprt_spvec v)"
  apply (induct v)
  apply (simp)
  apply (frule sorted_spvec_cons1)
  apply simp
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_nprt_spvec: "sorted_spvec v \<Longrightarrow> sorted_spvec (nprt_spvec v)"
  apply (induct v)
  apply (simp)
  apply (frule sorted_spvec_cons1)
  apply simp
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_spvec_pprt_spmat: "sorted_spvec m \<Longrightarrow> sorted_spvec (pprt_spmat m)"
  apply (induct m)
  apply (simp)
  apply (frule sorted_spvec_cons1)
  apply simp
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_spvec_nprt_spmat: "sorted_spvec m \<Longrightarrow> sorted_spvec (nprt_spmat m)"
  apply (induct m)
  apply (simp)
  apply (frule sorted_spvec_cons1)
  apply simp
  apply (simp add: sorted_spvec.simps split:list.split_asm)
  done

lemma sorted_spmat_pprt_spmat: "sorted_spmat m \<Longrightarrow> sorted_spmat (pprt_spmat m)"
  apply (induct m)
  apply (simp_all add: sorted_pprt_spvec)
  done

lemma sorted_spmat_nprt_spmat: "sorted_spmat m \<Longrightarrow> sorted_spmat (nprt_spmat m)"
  apply (induct m)
  apply (simp_all add: sorted_nprt_spvec)
  done

definition mult_est_spmat :: "('a::lattice_ring) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat" where
  "mult_est_spmat r1 r2 s1 s2 =
  add_spmat (mult_spmat (pprt_spmat s2) (pprt_spmat r2)) (add_spmat (mult_spmat (pprt_spmat s1) (nprt_spmat r2)) 
  (add_spmat (mult_spmat (nprt_spmat s2) (pprt_spmat r1)) (mult_spmat (nprt_spmat s1) (nprt_spmat r1))))"  

lemmas sparse_row_matrix_op_simps =
  sorted_sparse_matrix_imp_spmat sorted_sparse_matrix_imp_spvec
  sparse_row_add_spmat sorted_spvec_add_spmat sorted_spmat_add_spmat
  sparse_row_diff_spmat sorted_spvec_diff_spmat sorted_spmat_diff_spmat
  sparse_row_matrix_minus sorted_spvec_minus_spmat sorted_spmat_minus_spmat
  sparse_row_mult_spmat sorted_spvec_mult_spmat sorted_spmat_mult_spmat
  sparse_row_matrix_abs sorted_spvec_abs_spmat sorted_spmat_abs_spmat
  le_spmat_iff_sparse_row_le
  sparse_row_matrix_pprt sorted_spvec_pprt_spmat sorted_spmat_pprt_spmat
  sparse_row_matrix_nprt sorted_spvec_nprt_spmat sorted_spmat_nprt_spmat

lemmas sparse_row_matrix_arith_simps = 
  mult_spmat.simps mult_spvec_spmat.simps 
  addmult_spvec.simps 
  smult_spvec_empty smult_spvec_cons
  add_spmat.simps add_spvec.simps
  minus_spmat.simps minus_spvec.simps
  abs_spmat.simps abs_spvec.simps
  diff_spmat_def
  le_spmat.simps le_spvec.simps
  pprt_spmat.simps pprt_spvec.simps
  nprt_spmat.simps nprt_spvec.simps
  mult_est_spmat_def


(*lemma spm_linprog_dual_estimate_1:
  assumes  
  "sorted_sparse_matrix A1"
  "sorted_sparse_matrix A2"
  "sorted_sparse_matrix c1"
  "sorted_sparse_matrix c2"
  "sorted_sparse_matrix y"
  "sorted_spvec b"
  "sorted_spvec r"
  "le_spmat ([], y)"
  "A * x \<le> sparse_row_matrix (b::('a::lattice_ring) spmat)"
  "sparse_row_matrix A1 <= A"
  "A <= sparse_row_matrix A2"
  "sparse_row_matrix c1 <= c"
  "c <= sparse_row_matrix c2"
  "abs x \<le> sparse_row_matrix r"
  shows
  "c * x \<le> sparse_row_matrix (add_spmat (mult_spmat y b, mult_spmat (add_spmat (add_spmat (mult_spmat y (diff_spmat A2 A1), 
  abs_spmat (diff_spmat (mult_spmat y A1) c1)), diff_spmat c2 c1)) r))"
  by (insert prems, simp add: sparse_row_matrix_op_simps linprog_dual_estimate_1[where A=A])
*)

end
