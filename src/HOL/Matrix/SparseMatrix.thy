theory SparseMatrix = Matrix:

types 
  'a spvec = "(nat * 'a) list"
  'a spmat = "('a spvec) spvec"

consts
  sparse_row_vector :: "('a::lordered_ring) spvec \<Rightarrow> 'a matrix"
  sparse_row_matrix :: "('a::lordered_ring) spmat \<Rightarrow> 'a matrix"

defs
  sparse_row_vector_def : "sparse_row_vector arr == foldl (% m x. m + (singleton_matrix 0 (fst x) (snd x))) 0 arr"
  sparse_row_matrix_def : "sparse_row_matrix arr == foldl (% m r. m + (move_matrix (sparse_row_vector (snd r)) (int (fst r)) 0)) 0 arr"

lemma sparse_row_vector_empty[simp]: "sparse_row_vector [] = 0"
  by (simp add: sparse_row_vector_def)

lemma sparse_row_matrix_empty[simp]: "sparse_row_matrix [] = 0"
  by (simp add: sparse_row_matrix_def)

lemma foldl_distrstart[rule_format]: "! a x y. (f (g x y) a = g x (f y a)) \<Longrightarrow> ! x y. (foldl f (g x y) l = g x (foldl f y l))"
  by (induct l, auto)

lemma sparse_row_vector_cons[simp]: "sparse_row_vector (a#arr) = (singleton_matrix 0 (fst a) (snd a)) + (sparse_row_vector arr)"
  apply (induct arr)
  apply (auto simp add: sparse_row_vector_def)
  apply (simp add: foldl_distrstart[of "\<lambda>m x. m + singleton_matrix 0 (fst x) (snd x)" "\<lambda>x m. singleton_matrix 0 (fst x) (snd x) + m"])
  done

lemma sparse_row_vector_append[simp]: "sparse_row_vector (a @ b) = (sparse_row_vector a) + (sparse_row_vector b)"
  by (induct a, auto)

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

consts
  sorted_spvec :: "'a spvec \<Rightarrow> bool"
  sorted_spmat :: "'a spmat \<Rightarrow> bool"

primrec
  "sorted_spmat [] = True"
  "sorted_spmat (a#as) = ((sorted_spvec (snd a)) & (sorted_spmat as))"

primrec
  "sorted_spvec [] = True"
sorted_spvec_step:  "sorted_spvec (a#as) = (case as of [] \<Rightarrow> True | b#bs \<Rightarrow> ((fst a < fst b) & (sorted_spvec as)))" 

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

lemma sorted_sparse_row_vector_zero[rule_format]: "m <= n \<longrightarrow> sorted_spvec ((n,a)#arr) \<longrightarrow> Rep_matrix (sparse_row_vector arr) j m = 0"
apply (induct arr)
apply (auto)
apply (frule sorted_spvec_cons2,simp)+
apply (frule sorted_spvec_cons3, simp)
done

lemma sorted_sparse_row_matrix_zero[rule_format]: "m <= n \<longrightarrow> sorted_spvec ((n,a)#arr) \<longrightarrow> Rep_matrix (sparse_row_matrix arr) m j = 0"
  apply (induct arr)
  apply (auto)
  apply (frule sorted_spvec_cons2, simp)
  apply (frule sorted_spvec_cons3, simp)
  apply (simp add: sparse_row_matrix_cons neg_def)
  done

consts
  abs_spvec :: "('a::lordered_ring) spvec \<Rightarrow> 'a spvec"
  minus_spvec ::  "('a::lordered_ring) spvec \<Rightarrow> 'a spvec"
  smult_spvec :: "('a::lordered_ring) \<Rightarrow> 'a spvec \<Rightarrow> 'a spvec" 
  addmult_spvec :: "('a::lordered_ring) * 'a spvec * 'a spvec \<Rightarrow> 'a spvec"

primrec 
  "minus_spvec [] = []"
  "minus_spvec (a#as) = (fst a, -(snd a))#(minus_spvec as)"

primrec 
  "abs_spvec [] = []"
  "abs_spvec (a#as) = (fst a, abs (snd a))#(abs_spvec as)"

lemma sparse_row_vector_minus: 
  "sparse_row_vector (minus_spvec v) = - (sparse_row_vector v)"
  apply (induct v)
  apply (simp_all add: sparse_row_vector_cons)
  apply (simp add: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply simp
  done

lemma sparse_row_vector_abs:
  "sorted_spvec v \<Longrightarrow> sparse_row_vector (abs_spvec v) = abs (sparse_row_vector v)"
  apply (induct v)
  apply (simp_all add: sparse_row_vector_cons)
  apply (frule_tac sorted_spvec_cons1, simp)
  apply (simp only: Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply auto
  apply (subgoal_tac "Rep_matrix (sparse_row_vector list) 0 a = 0")
  apply (simp)
  apply (rule sorted_sparse_row_vector_zero)
  apply auto
  done

lemma sorted_spvec_minus_spvec:
  "sorted_spvec v \<Longrightarrow> sorted_spvec (minus_spvec v)"
  apply (induct v)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps)
  apply (case_tac list)
  apply (simp_all)
  done

lemma sorted_spvec_abs_spvec:
  "sorted_spvec v \<Longrightarrow> sorted_spvec (abs_spvec v)"
  apply (induct v)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps)
  apply (case_tac list)
  apply (simp_all)
  done
  
defs
  smult_spvec_def: "smult_spvec y arr == map (% a. (fst a, y * snd a)) arr"  

lemma smult_spvec_empty[simp]: "smult_spvec y [] = []"
  by (simp add: smult_spvec_def)

lemma smult_spvec_cons: "smult_spvec y (a#arr) = (fst a, y * (snd a)) # (smult_spvec y arr)"
  by (simp add: smult_spvec_def)

recdef addmult_spvec "measure (% (y, a, b). length a + (length b))"
  "addmult_spvec (y, arr, []) = arr"
  "addmult_spvec (y, [], brr) = smult_spvec y brr"
  "addmult_spvec (y, a#arr, b#brr) = (
    if (fst a) < (fst b) then (a#(addmult_spvec (y, arr, b#brr))) 
    else (if (fst b < fst a) then ((fst b, y * (snd b))#(addmult_spvec (y, a#arr, brr)))
    else ((fst a, (snd a)+ y*(snd b))#(addmult_spvec (y, arr,brr)))))"

lemma addmult_spvec_empty1[simp]: "addmult_spvec (y, [], a) = smult_spvec y a"
  by (induct a, auto)

lemma addmult_spvec_empty2[simp]: "addmult_spvec (y, a, []) = a"
  by (induct a, auto)

lemma sparse_row_vector_map: "(! x y. f (x+y) = (f x) + (f y)) \<Longrightarrow> (f::'a\<Rightarrow>('a::lordered_ring)) 0 = 0 \<Longrightarrow> 
  sparse_row_vector (map (% x. (fst x, f (snd x))) a) = apply_matrix f (sparse_row_vector a)"
  apply (induct a)
  apply (simp_all add: apply_matrix_add)
  done

lemma sparse_row_vector_smult: "sparse_row_vector (smult_spvec y a) = scalar_mult y (sparse_row_vector a)"
  apply (induct a)
  apply (simp_all add: smult_spvec_cons scalar_mult_add)
  done

lemma sparse_row_vector_addmult_spvec: "sparse_row_vector (addmult_spvec (y::'a::lordered_ring, a, b)) = 
  (sparse_row_vector a) + (scalar_mult y (sparse_row_vector b))"
  apply (rule addmult_spvec.induct[of _ y])
  apply (simp add: scalar_mult_add smult_spvec_cons sparse_row_vector_smult singleton_matrix_add)+
  done

lemma sorted_smult_spvec[rule_format]: "sorted_spvec a \<Longrightarrow> sorted_spvec (smult_spvec y a)"
  apply (auto simp add: smult_spvec_def)
  apply (induct a)
  apply (auto simp add: sorted_spvec.simps)
  apply (case_tac list)
  apply (auto)
  done

lemma sorted_spvec_addmult_spvec_helper: "\<lbrakk>sorted_spvec (addmult_spvec (y, (a, b) # arr, brr)); aa < a; sorted_spvec ((a, b) # arr); 
  sorted_spvec ((aa, ba) # brr)\<rbrakk> \<Longrightarrow> sorted_spvec ((aa, y * ba) # addmult_spvec (y, (a, b) # arr, brr))"  
  apply (induct brr)
  apply (auto simp add: sorted_spvec.simps)
  apply (simp split: list.split)
  apply (auto)
  apply (simp split: list.split)
  apply (auto)
  done

lemma sorted_spvec_addmult_spvec_helper2: 
 "\<lbrakk>sorted_spvec (addmult_spvec (y, arr, (aa, ba) # brr)); a < aa; sorted_spvec ((a, b) # arr); sorted_spvec ((aa, ba) # brr)\<rbrakk>
       \<Longrightarrow> sorted_spvec ((a, b) # addmult_spvec (y, arr, (aa, ba) # brr))"
  apply (induct arr)
  apply (auto simp add: smult_spvec_def sorted_spvec.simps)
  apply (simp split: list.split)
  apply (auto)
  done

lemma sorted_spvec_addmult_spvec_helper3[rule_format]:
  "sorted_spvec (addmult_spvec (y, arr, brr)) \<longrightarrow> sorted_spvec ((aa, b) # arr) \<longrightarrow> sorted_spvec ((aa, ba) # brr)
     \<longrightarrow> sorted_spvec ((aa, b + y * ba) # (addmult_spvec (y, arr, brr)))"
  apply (rule addmult_spvec.induct[of _ y arr brr])
  apply (simp_all add: sorted_spvec.simps smult_spvec_def)
  done

lemma sorted_addmult_spvec[rule_format]: "sorted_spvec a \<longrightarrow> sorted_spvec b \<longrightarrow> sorted_spvec (addmult_spvec (y, a, b))"
  apply (rule addmult_spvec.induct[of _ y a b])
  apply (simp_all add: sorted_smult_spvec)
  apply (rule conjI, intro strip)
  apply (case_tac "~(a < aa)")
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
  apply (case_tac "a=aa")
  apply (simp_all add: sorted_spvec_addmult_spvec_helper3)
  done

consts 
  mult_spvec_spmat :: "('a::lordered_ring) spvec * 'a spvec * 'a spmat  \<Rightarrow> 'a spvec"

recdef mult_spvec_spmat "measure (% (c, arr, brr). (length arr) + (length brr))"
  "mult_spvec_spmat (c, [], brr) = c"
  "mult_spvec_spmat (c, arr, []) = c"
  "mult_spvec_spmat (c, a#arr, b#brr) = (
     if ((fst a) < (fst b)) then (mult_spvec_spmat (c, arr, b#brr))
     else (if ((fst b) < (fst a)) then (mult_spvec_spmat (c, a#arr, brr)) 
     else (mult_spvec_spmat (addmult_spvec (snd a, c, snd b), arr, brr))))"

lemma sparse_row_mult_spvec_spmat[rule_format]: "sorted_spvec (a::('a::lordered_ring) spvec) \<longrightarrow> sorted_spvec B \<longrightarrow> 
  sparse_row_vector (mult_spvec_spmat (c, a, B)) = (sparse_row_vector c) + (sparse_row_vector a) * (sparse_row_matrix B)"
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
    apply (rule mult_spvec_spmat.induct)
    apply simp+
    apply (rule conjI)
    apply (intro strip)
    apply (frule_tac as=brr in sorted_spvec_cons1)
    apply (simp add: ring_eq_simps sparse_row_matrix_cons)
    apply (subst Rep_matrix_zero_imp_mult_zero) 
    apply (simp)
    apply (intro strip)
    apply (rule disjI2)
    apply (intro strip)
    apply (subst nrows)
    apply (rule  order_trans[of _ 1])
    apply (simp add: comp_1)+
    apply (subst Rep_matrix_zero_imp_mult_zero)
    apply (intro strip)
    apply (case_tac "k <= aa")
    apply (rule_tac m1 = k and n1 = a and a1 = b in ssubst[OF sorted_sparse_row_vector_zero])
    apply (simp_all)
    apply (rule impI)
    apply (rule disjI2)
    apply (rule nrows)
    apply (rule order_trans[of _ 1])
    apply (simp_all add: comp_1)
    
    apply (intro strip | rule conjI)+
    apply (frule_tac as=arr in sorted_spvec_cons1)
    apply (simp add: ring_eq_simps)
    apply (subst Rep_matrix_zero_imp_mult_zero)
    apply (simp)
    apply (rule disjI2)
    apply (intro strip)
    apply (simp add: sparse_row_matrix_cons neg_def)
    apply (case_tac "a <= aa")  
    apply (erule sorted_sparse_row_matrix_zero)  
    apply (simp_all)
    apply (intro strip)
    apply (case_tac "a=aa")
    apply (simp_all)
    apply (frule_tac as=arr in sorted_spvec_cons1)
    apply (frule_tac as=brr in sorted_spvec_cons1)
    apply (simp add: sparse_row_matrix_cons ring_eq_simps sparse_row_vector_addmult_spvec)
    apply (rule_tac B1 = "sparse_row_matrix brr" in ssubst[OF Rep_matrix_zero_imp_mult_zero])
    apply (auto)
    apply (rule sorted_sparse_row_matrix_zero)
    apply (simp_all)
    apply (rule_tac A1 = "sparse_row_vector arr" in ssubst[OF Rep_matrix_zero_imp_mult_zero])
    apply (auto)
    apply (rule_tac m=k and n = aa and a = b and arr=arr in sorted_sparse_row_vector_zero)
    apply (simp_all)
    apply (simp add: neg_def)
    apply (drule nrows_notzero)
    apply (drule nrows_helper)
    apply (arith)
    
    apply (subst Rep_matrix_inject[symmetric])
    apply (rule ext)+
    apply (simp)
    apply (subst Rep_matrix_mult)
    apply (rule_tac j1=aa in ssubst[OF foldseq_almostzero])
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
  "sorted_spvec (c::('a::lordered_ring) spvec) \<longrightarrow> sorted_spmat B \<longrightarrow> sorted_spvec (mult_spvec_spmat (c, a, B))"
  apply (rule mult_spvec_spmat.induct[of _ c a B])
  apply (simp_all add: sorted_addmult_spvec)
  done

consts 
  mult_spmat :: "('a::lordered_ring) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat"

primrec 
  "mult_spmat [] A = []"
  "mult_spmat (a#as) A = (fst a, mult_spvec_spmat ([], snd a, A))#(mult_spmat as A)"

lemma sparse_row_mult_spmat[rule_format]: 
  "sorted_spmat A \<longrightarrow> sorted_spvec B \<longrightarrow> sparse_row_matrix (mult_spmat A B) = (sparse_row_matrix A) * (sparse_row_matrix B)"
  apply (induct A)
  apply (auto simp add: sparse_row_matrix_cons sparse_row_mult_spvec_spmat ring_eq_simps move_matrix_mult)
  done

lemma sorted_spvec_mult_spmat[rule_format]:
  "sorted_spvec (A::('a::lordered_ring) spmat) \<longrightarrow> sorted_spvec (mult_spmat A B)"
  apply (induct A)
  apply (auto)
  apply (drule sorted_spvec_cons1, simp)
  apply (case_tac list)
  apply (auto simp add: sorted_spvec.simps)
  done

lemma sorted_spmat_mult_spmat[rule_format]:
  "sorted_spmat (B::('a::lordered_ring) spmat) \<longrightarrow> sorted_spmat (mult_spmat A B)"
  apply (induct A)
  apply (auto simp add: sorted_mult_spvec_spmat) 
  done

consts
  add_spvec :: "('a::lordered_ab_group) spvec * 'a spvec \<Rightarrow> 'a spvec"
  add_spmat :: "('a::lordered_ab_group) spmat * 'a spmat \<Rightarrow> 'a spmat"

recdef add_spvec "measure (% (a, b). length a + (length b))"
  "add_spvec (arr, []) = arr"
  "add_spvec ([], brr) = brr"
  "add_spvec (a#arr, b#brr) = (
  if (fst a) < (fst b) then (a#(add_spvec (arr, b#brr))) 
     else (if (fst b < fst a) then (b#(add_spvec (a#arr, brr)))
     else ((fst a, (snd a)+(snd b))#(add_spvec (arr,brr)))))"

lemma add_spvec_empty1[simp]: "add_spvec ([], a) = a"
  by (induct a, auto)

lemma add_spvec_empty2[simp]: "add_spvec (a, []) = a"
  by (induct a, auto)

lemma sparse_row_vector_add: "sparse_row_vector (add_spvec (a,b)) = (sparse_row_vector a) + (sparse_row_vector b)"
  apply (rule add_spvec.induct[of _ a b])
  apply (simp_all add: singleton_matrix_add)
  done

recdef add_spmat "measure (% (A,B). (length A)+(length B))"
  "add_spmat ([], bs) = bs"
  "add_spmat (as, []) = as"
  "add_spmat (a#as, b#bs) = (
  if fst a < fst b then 
    (a#(add_spmat (as, b#bs)))
  else (if fst b < fst a then
    (b#(add_spmat (a#as, bs)))
  else
    ((fst a, add_spvec (snd a, snd b))#(add_spmat (as, bs)))))"

lemma sparse_row_add_spmat: "sparse_row_matrix (add_spmat (A, B)) = (sparse_row_matrix A) + (sparse_row_matrix B)"
  apply (rule add_spmat.induct)
  apply (auto simp add: sparse_row_matrix_cons sparse_row_vector_add move_matrix_add)
  done

lemma sorted_add_spvec_helper1[rule_format]: "add_spvec ((a,b)#arr, brr) = (ab, bb) # list \<longrightarrow> (ab = a | (brr \<noteq> [] & ab = fst (hd brr)))"
  proof - 
    have "(! x ab a. x = (a,b)#arr \<longrightarrow> add_spvec (x, brr) = (ab, bb) # list \<longrightarrow> (ab = a | (ab = fst (hd brr))))"
      by (rule add_spvec.induct[of _ _ brr], auto)
    then show ?thesis
      by (case_tac brr, auto)
  qed

lemma sorted_add_spmat_helper1[rule_format]: "add_spmat ((a,b)#arr, brr) = (ab, bb) # list \<longrightarrow> (ab = a | (brr \<noteq> [] & ab = fst (hd brr)))"
  proof - 
    have "(! x ab a. x = (a,b)#arr \<longrightarrow> add_spmat (x, brr) = (ab, bb) # list \<longrightarrow> (ab = a | (ab = fst (hd brr))))"
      by (rule add_spmat.induct[of _ _ brr], auto)
    then show ?thesis
      by (case_tac brr, auto)
  qed

lemma sorted_add_spvec_helper[rule_format]: "add_spvec (arr, brr) = (ab, bb) # list \<longrightarrow> ((arr \<noteq> [] & ab = fst (hd arr)) | (brr \<noteq> [] & ab = fst (hd brr)))"
  apply (rule add_spvec.induct[of _ arr brr])
  apply (auto)
  done

lemma sorted_add_spmat_helper[rule_format]: "add_spmat (arr, brr) = (ab, bb) # list \<longrightarrow> ((arr \<noteq> [] & ab = fst (hd arr)) | (brr \<noteq> [] & ab = fst (hd brr)))"
  apply (rule add_spmat.induct[of _ arr brr])
  apply (auto)
  done

lemma add_spvec_commute: "add_spvec (a, b) = add_spvec (b, a)"
  by (rule add_spvec.induct[of _ a b], auto)

lemma add_spmat_commute: "add_spmat (a, b) = add_spmat (b, a)"
  apply (rule add_spmat.induct[of _ a b])
  apply (simp_all add: add_spvec_commute)
  done
  
lemma sorted_add_spvec_helper2: "add_spvec ((a,b)#arr, brr) = (ab, bb) # list \<Longrightarrow> aa < a \<Longrightarrow> sorted_spvec ((aa, ba) # brr) \<Longrightarrow> aa < ab"
  apply (drule sorted_add_spvec_helper1)
  apply (auto)
  apply (case_tac brr)
  apply (simp_all)
  apply (drule_tac sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_add_spmat_helper2: "add_spmat ((a,b)#arr, brr) = (ab, bb) # list \<Longrightarrow> aa < a \<Longrightarrow> sorted_spvec ((aa, ba) # brr) \<Longrightarrow> aa < ab"
  apply (drule sorted_add_spmat_helper1)
  apply (auto)
  apply (case_tac brr)
  apply (simp_all)
  apply (drule_tac sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_spvec_add_spvec[rule_format]: "sorted_spvec a \<longrightarrow> sorted_spvec b \<longrightarrow> sorted_spvec (add_spvec (a, b))"
  apply (rule add_spvec.induct[of _ a b])
  apply (simp_all)
  apply (rule conjI)
  apply (intro strip)
  apply (simp)
  apply (frule_tac as=brr in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (simp add: sorted_add_spvec_helper2)
  apply (clarify)
  apply (rule conjI)
  apply (case_tac "a=aa")
  apply (simp)
  apply (clarify)
  apply (frule_tac as=arr in sorted_spvec_cons1, simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (simp add: sorted_add_spvec_helper2 add_spvec_commute)
  apply (case_tac "a=aa")
  apply (simp_all)
  apply (clarify)
  apply (frule_tac as=arr in sorted_spvec_cons1)
  apply (frule_tac as=brr in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (drule_tac sorted_add_spvec_helper)
  apply (auto)
  apply (case_tac arr)
  apply (simp_all)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  apply (case_tac brr)
  apply (simp_all)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_spvec_add_spmat[rule_format]: "sorted_spvec A \<longrightarrow> sorted_spvec B \<longrightarrow> sorted_spvec (add_spmat (A, B))"
  apply (rule add_spmat.induct[of _ A B])
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
  apply (case_tac "a=aa")
  apply (simp)
  apply (clarify)
  apply (frule_tac as=as in sorted_spvec_cons1, simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (simp add: sorted_add_spmat_helper2 add_spmat_commute)
  apply (case_tac "a=aa")
  apply (simp_all)
  apply (clarify)
  apply (frule_tac as=as in sorted_spvec_cons1)
  apply (frule_tac as=bs in sorted_spvec_cons1)
  apply (simp)
  apply (subst sorted_spvec_step)
  apply (simp split: list.split)
  apply (clarify, simp)
  apply (drule_tac sorted_add_spmat_helper)
  apply (auto)
  apply (case_tac as)
  apply (simp_all)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  apply (case_tac bs)
  apply (simp_all)
  apply (drule sorted_spvec_cons3)
  apply (simp)
  done

lemma sorted_spmat_add_spmat[rule_format]: "sorted_spmat A \<longrightarrow> sorted_spmat B \<longrightarrow> sorted_spmat (add_spmat (A, B))"
  apply (rule add_spmat.induct[of _ A B])
  apply (simp_all add: sorted_spvec_add_spvec)
  done

consts
  le_spvec :: "('a::lordered_ab_group) spvec * 'a spvec \<Rightarrow> bool" 
  le_spmat :: "('a::lordered_ab_group) spmat * 'a spmat \<Rightarrow> bool" 

recdef le_spvec "measure (% (a,b). (length a) + (length b))" 
  "le_spvec ([], []) = True"
  "le_spvec (a#as, []) = ((snd a <= 0) & (le_spvec (as, [])))"
  "le_spvec ([], b#bs) = ((0 <= snd b) & (le_spvec ([], bs)))"
  "le_spvec (a#as, b#bs) = (
  if (fst a < fst b) then 
    ((snd a <= 0) & (le_spvec (as, b#bs)))
  else (if (fst b < fst a) then
    ((0 <= snd b) & (le_spvec (a#as, bs)))
  else 
    ((snd a <= snd b) & (le_spvec (as, bs)))))"

recdef le_spmat "measure (% (a,b). (length a) + (length b))"
  "le_spmat ([], []) = True"
  "le_spmat (a#as, []) = (le_spvec (snd a, []) & (le_spmat (as, [])))"
  "le_spmat ([], b#bs) = (le_spvec ([], snd b) & (le_spmat ([], bs)))"
  "le_spmat (a#as, b#bs) = (
  if fst a < fst b then
    (le_spvec(snd a,[]) & le_spmat(as, b#bs))
  else (if (fst b < fst a) then 
    (le_spvec([], snd b) & le_spmat(a#as, bs))
  else
    (le_spvec(snd a, snd b) & le_spmat (as, bs))))"

constdefs
  disj_matrices :: "('a::zero) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool"
  "disj_matrices A B == (! j i. (Rep_matrix A j i \<noteq> 0) \<longrightarrow> (Rep_matrix B j i = 0)) & (! j i. (Rep_matrix B j i \<noteq> 0) \<longrightarrow> (Rep_matrix A j i = 0))"  

ML {* simp_depth_limit := 2 *}

lemma disj_matrices_add: "disj_matrices A B \<Longrightarrow> disj_matrices C D \<Longrightarrow> disj_matrices A D \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (A + B <= C + D) = (A <= C & B <= (D::('a::lordered_ab_group) matrix))"
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
  (A + B <= 0) = (A <= 0 & (B::('a::lordered_ab_group) matrix) <= 0)"
by (rule disj_matrices_add[of A B 0 0, simplified])
 
lemma disj_matrices_add_zero_le: "disj_matrices A B \<Longrightarrow>
  (0 <= A + B) = (0 <= A & 0 <= (B::('a::lordered_ab_group) matrix))"
by (rule disj_matrices_add[of 0 0 A B, simplified])

lemma disj_matrices_add_x_le: "disj_matrices A B \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (A <= B + C) = (A <= C & 0 <= (B::('a::lordered_ab_group) matrix))"
by (auto simp add: disj_matrices_add[of 0 A B C, simplified])

lemma disj_matrices_add_le_x: "disj_matrices A B \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (B + A <= C) = (A <= C &  (B::('a::lordered_ab_group) matrix) <= 0)"
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

lemma disj_matrices_x_add: "disj_matrices A B \<Longrightarrow> disj_matrices A C \<Longrightarrow> disj_matrices (A::('a::lordered_ab_group) matrix) (B+C)"
  apply (simp add: disj_matrices_def)
  apply (auto)
  apply (drule_tac j=j and i=i in spec2)+
  apply (case_tac "Rep_matrix B j i = 0")
  apply (case_tac "Rep_matrix C j i = 0")
  apply (simp_all)
  done

lemma disj_matrices_add_x: "disj_matrices A B \<Longrightarrow> disj_matrices A C \<Longrightarrow> disj_matrices (B+C) (A::('a::lordered_ab_group) matrix)" 
  by (simp add: disj_matrices_x_add disj_matrices_commute)

lemma disj_singleton_matrices[simp]: "disj_matrices (singleton_matrix j i x) (singleton_matrix u v y) = (j \<noteq> u | i \<noteq> v | x = 0 | y = 0)" 
  by (auto simp add: disj_matrices_def)

lemma disj_move_sparse_vec_mat[simplified disj_matrices_commute]: 
  "j <= a \<Longrightarrow> sorted_spvec((a,c)#as) \<Longrightarrow> disj_matrices (move_matrix (sparse_row_vector b) (int j) i) (sparse_row_matrix as)"
  apply (auto simp add: neg_def disj_matrices_def)
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
  apply (auto simp add: neg_def disj_matrices_def)
  apply (rule nrows, rule order_trans[of _ 1], simp, drule nrows_notzero, drule less_le_trans[OF _ nrows_spvec], arith)+
  done

lemma le_spvec_iff_sparse_row_le[rule_format]: "(sorted_spvec a) \<longrightarrow> (sorted_spvec b) \<longrightarrow> (le_spvec (a,b)) = (sparse_row_vector a <= sparse_row_vector b)"
  apply (rule le_spvec.induct)
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
  apply (case_tac "a=aa", simp_all)
  apply (subst disj_matrices_add)
  apply (simp_all add: disj_sparse_row_singleton[OF order_refl] disj_matrices_commute)
  done

lemma le_spvec_empty2_sparse_row[rule_format]: "(sorted_spvec b) \<longrightarrow> (le_spvec (b,[]) = (sparse_row_vector b <= 0))"
  apply (induct b)
  apply (simp_all add: sorted_spvec_cons1)
  apply (intro strip)
  apply (subst disj_matrices_add_le_zero)
  apply (simp add: disj_matrices_commute disj_sparse_row_singleton sorted_spvec_cons1)
  apply (rule_tac y = "snd a" in disj_sparse_row_singleton[OF order_refl])
  apply (simp_all)
  done

lemma le_spvec_empty1_sparse_row[rule_format]: "(sorted_spvec b) \<longrightarrow> (le_spvec ([],b) = (0 <= sparse_row_vector b))"
  apply (induct b)
  apply (simp_all add: sorted_spvec_cons1)
  apply (intro strip)
  apply (subst disj_matrices_add_zero_le)
  apply (simp add: disj_matrices_commute disj_sparse_row_singleton sorted_spvec_cons1)
  apply (rule_tac y = "snd a" in disj_sparse_row_singleton[OF order_refl])
  apply (simp_all)
  done

lemma le_spmat_iff_sparse_row_le[rule_format]: "(sorted_spvec A) \<longrightarrow> (sorted_spmat A) \<longrightarrow> (sorted_spvec B) \<longrightarrow> (sorted_spmat B) \<longrightarrow> 
  le_spmat(A, B) = (sparse_row_matrix A <= sparse_row_matrix B)"
  apply (rule le_spmat.induct)
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
  apply (case_tac "a=aa")
  apply (simp_all)
  apply (subst disj_matrices_add)
  apply (simp_all add: disj_matrices_commute disj_move_sparse_vec_mat[OF order_refl])
  apply (simp add: sorted_spvec_cons1 le_spvec_iff_sparse_row_le)
  done

ML {* simp_depth_limit := 999 *}

consts 
   abs_spmat :: "('a::lordered_ring) spmat \<Rightarrow> 'a spmat"
   minus_spmat :: "('a::lordered_ring) spmat \<Rightarrow> 'a spmat"

primrec
  "abs_spmat [] = []"
  "abs_spmat (a#as) = (fst a, abs_spvec (snd a))#(abs_spmat as)"

primrec
  "minus_spmat [] = []"
  "minus_spmat (a#as) = (fst a, minus_spvec (snd a))#(minus_spmat as)"

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
  apply (subst Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply auto
  apply (case_tac "x=a")
  apply (simp)
  apply (subst sorted_sparse_row_matrix_zero)
  apply auto
  apply (subst Rep_sparse_row_vector_zero)
  apply (simp_all add: neg_def)
  done

lemma sorted_spvec_minus_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec (minus_spmat A)"
  apply (induct A)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps)
  apply (case_tac list)
  apply (simp_all)
  done 

lemma sorted_spvec_abs_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec (abs_spmat A)" 
  apply (induct A)
  apply (simp)
  apply (frule sorted_spvec_cons1, simp)
  apply (simp add: sorted_spvec.simps)
  apply (case_tac list)
  apply (simp_all)
  done

lemma sorted_spmat_minus_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat (minus_spmat A)"
  apply (induct A)
  apply (simp_all add: sorted_spvec_minus_spvec)
  done

lemma sorted_spmat_abs_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat (abs_spmat A)"
  apply (induct A)
  apply (simp_all add: sorted_spvec_abs_spvec)
  done

constdefs
  diff_spmat :: "('a::lordered_ring) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat"
  "diff_spmat A B == add_spmat (A, minus_spmat B)"

lemma sorted_spmat_diff_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat B \<Longrightarrow> sorted_spmat (diff_spmat A B)"
  by (simp add: diff_spmat_def sorted_spmat_minus_spmat sorted_spmat_add_spmat)

lemma sorted_spvec_diff_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec B \<Longrightarrow> sorted_spvec (diff_spmat A B)"
  by (simp add: diff_spmat_def sorted_spvec_minus_spmat sorted_spvec_add_spmat)

lemma sparse_row_diff_spmat: "sparse_row_matrix (diff_spmat A B ) = (sparse_row_matrix A) - (sparse_row_matrix B)"
  by (simp add: diff_spmat_def sparse_row_add_spmat sparse_row_matrix_minus)

constdefs
  sorted_sparse_matrix :: "'a spmat \<Rightarrow> bool"
  "sorted_sparse_matrix A == (sorted_spvec A) & (sorted_spmat A)"

lemma sorted_sparse_matrix_imp_spvec: "sorted_sparse_matrix A \<Longrightarrow> sorted_spvec A"
  by (simp add: sorted_sparse_matrix_def)

lemma sorted_sparse_matrix_imp_spmat: "sorted_sparse_matrix A \<Longrightarrow> sorted_spmat A"
  by (simp add: sorted_sparse_matrix_def)

lemmas sparse_row_matrix_op_simps =
  sorted_sparse_matrix_imp_spmat sorted_sparse_matrix_imp_spvec
  sparse_row_add_spmat sorted_spvec_add_spmat sorted_spmat_add_spmat
  sparse_row_diff_spmat sorted_spvec_diff_spmat sorted_spmat_diff_spmat
  sparse_row_matrix_minus sorted_spvec_minus_spmat sorted_spmat_minus_spmat
  sparse_row_mult_spmat sorted_spvec_mult_spmat sorted_spmat_mult_spmat
  sparse_row_matrix_abs sorted_spvec_abs_spmat sorted_spmat_abs_spmat
  le_spmat_iff_sparse_row_le

lemma zero_eq_Numeral0: "(0::_::number_ring) = Numeral0" by simp

lemmas sparse_row_matrix_arith_simps[simplified zero_eq_Numeral0] = 
  mult_spmat.simps mult_spvec_spmat.simps 
  addmult_spvec.simps 
  smult_spvec_empty smult_spvec_cons
  add_spmat.simps add_spvec.simps
  minus_spmat.simps minus_spvec.simps
  abs_spmat.simps abs_spvec.simps
  diff_spmat_def
  le_spmat.simps le_spvec.simps

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

lemma spm_linprog_dual_estimate_1:
  assumes  
  "sorted_sparse_matrix A1"
  "sorted_sparse_matrix A2"
  "sorted_sparse_matrix c1"
  "sorted_sparse_matrix c2"
  "sorted_sparse_matrix y"
  "sorted_spvec b"
  "sorted_spvec r"
  "le_spmat ([], y)"
  "A * x \<le> sparse_row_matrix (b::('a::lordered_ring) spmat)"
  "sparse_row_matrix A1 <= A"
  "A <= sparse_row_matrix A2"
  "sparse_row_matrix c1 <= c"
  "c <= sparse_row_matrix c2"
  "abs x \<le> sparse_row_matrix r"
  shows
  "c * x \<le> sparse_row_matrix (add_spmat (mult_spmat y b, mult_spmat (add_spmat (add_spmat (mult_spmat y (diff_spmat A2 A1), 
  abs_spmat (diff_spmat (mult_spmat y A1) c1)), diff_spmat c2 c1)) r))"
  by (insert prems, simp add: sparse_row_matrix_op_simps linprog_dual_estimate_1[where A=A])

end
