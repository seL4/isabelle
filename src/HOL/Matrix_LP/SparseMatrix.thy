(*  Title:      HOL/Matrix_LP/SparseMatrix.thy
    Author:     Steven Obua; updated to Isar by LCP
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

lemma [code]:
  \<open>0 = sparse_row_vector []\<close>
  by simp

lemma foldl_distrstart: "\<forall>a x y. (f (g x y) a = g x (f y a)) \<Longrightarrow> (foldl f (g x y) l = g x (foldl f y l))"
  by (induct l arbitrary: x y, auto)

lemma sparse_row_vector_cons[simp]:
  "sparse_row_vector (a # arr) = (singleton_matrix 0 (fst a) (snd a)) + (sparse_row_vector arr)"
  by (induct arr) (auto simp: foldl_distrstart sparse_row_vector_def)

lemma sparse_row_vector_append[simp]:
  "sparse_row_vector (a @ b) = (sparse_row_vector a) + (sparse_row_vector b)"
  by (induct a) auto

lemma nrows_spvec[simp]: "nrows (sparse_row_vector x) \<le> (Suc 0)"
  by (induct x) (auto simp: add_nrows)

lemma sparse_row_matrix_cons: "sparse_row_matrix (a#arr) = ((move_matrix (sparse_row_vector (snd a)) (int (fst a)) 0)) + sparse_row_matrix arr"
  by (induct arr) (auto simp: foldl_distrstart sparse_row_matrix_def)

lemma sparse_row_matrix_append: "sparse_row_matrix (arr@brr) = (sparse_row_matrix arr) + (sparse_row_matrix brr)"
  by (induct arr) (auto simp: sparse_row_matrix_cons)

fun sorted_spvec :: "'a spvec \<Rightarrow> bool"
where
  "sorted_spvec [] = True"
| sorted_spvec_step1: "sorted_spvec [a] = True" 
| sorted_spvec_step: "sorted_spvec ((m,x)#(n,y)#bs) =  ((m < n) \<and> (sorted_spvec ((n,y)#bs)))" 

primrec sorted_spmat :: "'a spmat \<Rightarrow> bool"
where
  "sorted_spmat [] = True"
| "sorted_spmat (a#as) = ((sorted_spvec (snd a)) \<and> (sorted_spmat as))"

declare sorted_spvec.simps [simp del]

lemma sorted_spvec_empty[simp]: "sorted_spvec [] = True"
  by (simp add: sorted_spvec.simps)

lemma sorted_spvec_cons1: "sorted_spvec (a#as) \<Longrightarrow> sorted_spvec as"
  using sorted_spvec.elims(2) sorted_spvec_empty by blast

lemma sorted_spvec_cons2: "sorted_spvec (a#b#t) \<Longrightarrow> sorted_spvec (a#t)"
  by (smt (verit, del_insts) sorted_spvec_step order.strict_trans list.inject sorted_spvec.elims(3) surj_pair)

lemma sorted_spvec_cons3: "sorted_spvec(a#b#t) \<Longrightarrow> fst a < fst b"
  by (metis sorted_spvec_step prod.collapse)

lemma sorted_sparse_row_vector_zero: 
  assumes "m \<le> n"
  shows "sorted_spvec ((n,a)#arr) \<Longrightarrow> Rep_matrix (sparse_row_vector arr) j m = 0"
proof (induct arr)
  case Nil
  then show ?case by auto
next
  case (Cons a arr)
  with assms show ?case
    by (auto dest: sorted_spvec_cons2 sorted_spvec_cons3)
qed

lemma sorted_sparse_row_matrix_zero[rule_format]: 
  assumes "m \<le> n"
  shows "sorted_spvec ((n,a)#arr) \<Longrightarrow> Rep_matrix (sparse_row_matrix arr) m j = 0"
proof (induct arr)
  case Nil
  then show ?case by auto
next
  case (Cons a arr)
  with assms show ?case
    unfolding sparse_row_matrix_cons
    by (auto dest: sorted_spvec_cons2 sorted_spvec_cons3)
qed

primrec minus_spvec :: "('a::ab_group_add) spvec \<Rightarrow> 'a spvec"
where
  "minus_spvec [] = []"
| "minus_spvec (a#as) = (fst a, -(snd a))#(minus_spvec as)"

primrec abs_spvec :: "('a::lattice_ab_group_add_abs) spvec \<Rightarrow> 'a spvec"
where
  "abs_spvec [] = []"
| "abs_spvec (a#as) = (fst a, \<bar>snd a\<bar>)#(abs_spvec as)"

lemma sparse_row_vector_minus: 
  "sparse_row_vector (minus_spvec v) = - (sparse_row_vector v)"
proof (induct v)
  case Nil
  then show ?case
    by auto
next
  case (Cons a v)
  then have "singleton_matrix 0 (fst a) (- snd a) = - singleton_matrix 0 (fst a) (snd a)"
    by (simp add: Rep_matrix_inject minus_matrix_def)
  then show ?case
    by (simp add: local.Cons)
qed

lemma sparse_row_vector_abs:
  "sorted_spvec (v :: 'a::lattice_ring spvec) \<Longrightarrow> sparse_row_vector (abs_spvec v) = \<bar>sparse_row_vector v\<bar>"
proof (induct v)
  case Nil
  then show ?case
    by simp
next
  case (Cons ab v)
  then have v: "sorted_spvec v"
    using sorted_spvec_cons1 by blast
  show ?case
  proof (cases ab)
    case (Pair a b)
    then have 0: "Rep_matrix (sparse_row_vector v) 0 a = 0"
      using Cons.prems sorted_sparse_row_vector_zero by blast
    with v Cons show ?thesis
      by (fastforce simp: Pair simp flip: Rep_matrix_inject)
  qed
qed

lemma sorted_spvec_minus_spvec:
  "sorted_spvec v \<Longrightarrow> sorted_spvec (minus_spvec v)"
  by (induct v rule: sorted_spvec.induct) (auto simp: sorted_spvec_step1 sorted_spvec_step)

lemma sorted_spvec_abs_spvec:
  "sorted_spvec v \<Longrightarrow> sorted_spvec (abs_spvec v)"
  by (induct v rule: sorted_spvec.induct) (auto simp: sorted_spvec_step1 sorted_spvec_step)
  
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
  by simp

lemma sparse_row_vector_map: "(\<forall>x y. f (x+y) = (f x) + (f y)) \<Longrightarrow> (f::'a\<Rightarrow>('a::lattice_ring)) 0 = 0 \<Longrightarrow> 
  sparse_row_vector (map (% x. (fst x, f (snd x))) a) = apply_matrix f (sparse_row_vector a)"
  by (induct a) (simp_all add: apply_matrix_add)

lemma sparse_row_vector_smult: "sparse_row_vector (smult_spvec y a) = scalar_mult y (sparse_row_vector a)"
  by (induct a) (simp_all add: smult_spvec_cons scalar_mult_add)

lemma sparse_row_vector_addmult_spvec: "sparse_row_vector (addmult_spvec (y::'a::lattice_ring) a b) = 
  (sparse_row_vector a) + (scalar_mult y (sparse_row_vector b))"
  by (induct y a b rule: addmult_spvec.induct)
     (simp_all add: scalar_mult_add smult_spvec_cons sparse_row_vector_smult singleton_matrix_add)

lemma sorted_smult_spvec: "sorted_spvec a \<Longrightarrow> sorted_spvec (smult_spvec y a)"
  by (induct a rule: sorted_spvec.induct) (auto simp: smult_spvec_def sorted_spvec_step1 sorted_spvec_step)

lemma sorted_spvec_addmult_spvec_helper: "\<lbrakk>sorted_spvec (addmult_spvec y ((a, b) # arr) brr); aa < a; sorted_spvec ((a, b) # arr); 
  sorted_spvec ((aa, ba) # brr)\<rbrakk> \<Longrightarrow> sorted_spvec ((aa, y * ba) # addmult_spvec y ((a, b) # arr) brr)"  
  by (induct brr) (auto simp: sorted_spvec.simps)

lemma sorted_spvec_addmult_spvec_helper2: 
 "\<lbrakk>sorted_spvec (addmult_spvec y arr ((aa, ba) # brr)); a < aa; sorted_spvec ((a, b) # arr); sorted_spvec ((aa, ba) # brr)\<rbrakk>
       \<Longrightarrow> sorted_spvec ((a, b) # addmult_spvec y arr ((aa, ba) # brr))"
  by (induct arr) (auto simp: smult_spvec_def sorted_spvec.simps)

lemma sorted_spvec_addmult_spvec_helper3[rule_format]:
  "sorted_spvec (addmult_spvec y arr brr) \<Longrightarrow> 
   sorted_spvec ((aa, b) # arr) \<Longrightarrow> 
  sorted_spvec ((aa, ba) # brr) \<Longrightarrow>
   sorted_spvec ((aa, b + y * ba) # (addmult_spvec y arr brr))"
  by (smt (verit, ccfv_threshold) sorted_spvec_step addmult_spvec.simps(1) list.distinct(1) list.sel(3) sorted_spvec.elims(1) sorted_spvec_addmult_spvec_helper2)

lemma sorted_addmult_spvec: "sorted_spvec a \<Longrightarrow> sorted_spvec b \<Longrightarrow> sorted_spvec (addmult_spvec y a b)"
proof (induct y a b rule: addmult_spvec.induct)
  case (1 y arr)
  then show ?case
    by simp
next
  case (2 y v va)
  then show ?case 
    by (simp add: sorted_smult_spvec)
next
  case (3 y i a arr j b brr)
  show ?case 
  proof (cases i j rule: linorder_cases)
    case less
    with 3 show ?thesis
      by (simp add: sorted_spvec_addmult_spvec_helper2 sorted_spvec_cons1)
  next
    case equal
    with 3 show ?thesis 
      by (simp add: sorted_spvec_addmult_spvec_helper3 sorted_spvec_cons1)
  next
    case greater
    with 3 show ?thesis 
      by (simp add: sorted_spvec_addmult_spvec_helper sorted_spvec_cons1)
  qed
qed

fun mult_spvec_spmat :: "('a::lattice_ring) spvec \<Rightarrow> 'a spvec \<Rightarrow> 'a spmat  \<Rightarrow> 'a spvec"
where
  "mult_spvec_spmat c [] brr = c"
| "mult_spvec_spmat c arr [] = c"
| "mult_spvec_spmat c ((i,a)#arr) ((j,b)#brr) = (
     if (i < j) then mult_spvec_spmat c arr ((j,b)#brr)
     else if (j < i) then mult_spvec_spmat c ((i,a)#arr) brr 
     else mult_spvec_spmat (addmult_spvec a c b) arr brr)"

lemma sparse_row_mult_spvec_spmat: 
  assumes "sorted_spvec (a::('a::lattice_ring) spvec)" "sorted_spvec B"
  shows "sparse_row_vector (mult_spvec_spmat c a B) = (sparse_row_vector c) + (sparse_row_vector a) * (sparse_row_matrix B)"
proof -
  have comp_1: "!! a b. a < b \<Longrightarrow> Suc 0 \<le> nat ((int b)-(int a))" by arith
  have not_iff: "!! a b. a = b \<Longrightarrow> (~ a) = (~ b)" by simp
  {
    fix a 
    fix v :: "(nat \<times> 'a) list"
    assume a: "a < nrows(sparse_row_vector v)"
    have "nrows(sparse_row_vector v) \<le> 1" by simp
    then have "a = 0"
      using a dual_order.strict_trans1 by blast
  }
  note nrows_helper = this
  show ?thesis
    using assms
  proof (induct c a B rule: mult_spvec_spmat.induct)
    case (1 c brr)
    then show ?case
      by simp
  next
    case (2 c v va)
    then show ?case
      by simp
  next
    case (3 c i a arr j b brr)
    then have abrr: "sorted_spvec arr" "sorted_spvec brr"
      using sorted_spvec_cons1 by blast+
    have "\<And>m n. \<lbrakk>a \<noteq> 0; 0 < m\<rbrakk>
           \<Longrightarrow> a * Rep_matrix (sparse_row_vector b) m n = 0"
      by (metis mult_zero_right neq0_conv nrows_helper nrows_notzero)
    then have \<dagger>: "scalar_mult a (sparse_row_vector b) =
            singleton_matrix 0 j a * move_matrix (sparse_row_vector b) (int j) 0"
      apply (intro matrix_eqI)
      apply (simp)
      apply (subst Rep_matrix_mult)
      apply (subst foldseq_almostzero, auto)
      done
    show ?case
    proof (cases i j rule: linorder_cases)
      case less
      with 3 abrr \<dagger> show ?thesis
        apply (simp add: algebra_simps sparse_row_matrix_cons Rep_matrix_zero_imp_mult_zero)
        by (metis Rep_matrix_zero_imp_mult_zero Rep_singleton_matrix less_imp_le_nat sorted_sparse_row_matrix_zero)
    next
      case equal
      with 3 abrr \<dagger> show ?thesis
        apply (simp add: sparse_row_matrix_cons algebra_simps sparse_row_vector_addmult_spvec)
        apply (subst Rep_matrix_zero_imp_mult_zero)
        using sorted_sparse_row_matrix_zero apply fastforce
        apply (subst Rep_matrix_zero_imp_mult_zero)
         apply (metis Rep_move_matrix comp_1 nrows_le nrows_spvec sorted_sparse_row_vector_zero verit_comp_simplify1(3))
        apply simp
        done
    next
      case greater
      have "Rep_matrix (sparse_row_vector arr) j' k = 0 \<or>
           Rep_matrix (move_matrix (sparse_row_vector b) (int j) 0) k
            i' = 0"
        if "sorted_spvec ((i, a) # arr)" for j' i' k
      proof (cases "k \<le> j")
        case True
        with greater that show ?thesis
          by (meson order.trans nat_less_le sorted_sparse_row_vector_zero)
      qed (use nrows_helper nrows_notzero in force)
      then have "sparse_row_vector arr * move_matrix (sparse_row_vector b) (int j) 0 = 0"
        using greater 3 
        by (simp add: Rep_matrix_zero_imp_mult_zero)
      with greater 3 abrr show ?thesis
        apply (simp add: algebra_simps sparse_row_matrix_cons)
        by (metis Rep_matrix_zero_imp_mult_zero Rep_move_matrix Rep_singleton_matrix comp_1 nrows_le nrows_spvec)
    qed
  qed
qed

lemma sorted_mult_spvec_spmat: 
  "sorted_spvec (c::('a::lattice_ring) spvec) \<Longrightarrow> sorted_spmat B \<Longrightarrow> sorted_spvec (mult_spvec_spmat c a B)"
  by (induct c a B rule: mult_spvec_spmat.induct) (simp_all add: sorted_addmult_spvec)

primrec mult_spmat :: "('a::lattice_ring) spmat \<Rightarrow> 'a spmat \<Rightarrow> 'a spmat"
where
  "mult_spmat [] A = []"
| "mult_spmat (a#as) A = (fst a, mult_spvec_spmat [] (snd a) A)#(mult_spmat as A)"

lemma sparse_row_mult_spmat: 
  "sorted_spmat A \<Longrightarrow> sorted_spvec B \<Longrightarrow>
   sparse_row_matrix (mult_spmat A B) = (sparse_row_matrix A) * (sparse_row_matrix B)"
  by (induct A) (auto simp: sparse_row_matrix_cons sparse_row_mult_spvec_spmat algebra_simps move_matrix_mult)

lemma sorted_spvec_mult_spmat:
  fixes A :: "('a::lattice_ring) spmat"
  shows "sorted_spvec A \<Longrightarrow> sorted_spvec (mult_spmat A B)"
by (induct A rule: sorted_spvec.induct) (auto simp: sorted_spvec.simps)

lemma sorted_spmat_mult_spmat:
  "sorted_spmat (B::('a::lattice_ring) spmat) \<Longrightarrow> sorted_spmat (mult_spmat A B)"
  by (induct A) (auto simp: sorted_mult_spvec_spmat) 


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
  by (induct a b rule: add_spvec.induct) (simp_all add: singleton_matrix_add)

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
  by (induct A B rule: add_spmat.induct) (auto simp: sparse_row_matrix_cons sparse_row_vector_add move_matrix_add)

lemma [code]:
  \<open>sparse_row_matrix A + sparse_row_matrix B = sparse_row_matrix (add_spmat A B)\<close>
  \<open>sparse_row_vector a + sparse_row_vector b = sparse_row_vector (add_spvec a b)\<close>
  by (simp_all add: sparse_row_add_spmat sparse_row_vector_add)

lemma sorted_add_spvec_helper1[rule_format]: "add_spvec ((a,b)#arr) brr = (ab, bb) # list \<longrightarrow> (ab = a | (brr \<noteq> [] & ab = fst (hd brr)))"
proof - 
  have "(\<forall>x ab a. x = (a,b)#arr \<longrightarrow> add_spvec x brr = (ab, bb) # list \<longrightarrow> (ab = a | (ab = fst (hd brr))))"
    by (induct brr rule: add_spvec.induct) (auto split:if_splits)
  then show ?thesis
    by (case_tac brr, auto)
qed

lemma sorted_add_spmat_helper1[rule_format]:
  "add_spmat ((a,b)#arr) brr = (ab, bb) # list \<Longrightarrow> (ab = a | (brr \<noteq> [] & ab = fst (hd brr)))"
  by (smt (verit) add_spmat.elims fst_conv list.distinct(1) list.sel(1))

lemma sorted_add_spvec_helper: "add_spvec arr brr = (ab, bb) # list \<Longrightarrow> ((arr \<noteq> [] & ab = fst (hd arr)) | (brr \<noteq> [] & ab = fst (hd brr)))"
  by (induct arr brr rule: add_spvec.induct) (auto split:if_splits)

lemma sorted_add_spmat_helper: "add_spmat arr brr = (ab, bb) # list \<Longrightarrow> ((arr \<noteq> [] & ab = fst (hd arr)) | (brr \<noteq> [] & ab = fst (hd brr)))"
  by (induct arr brr rule: add_spmat.induct) (auto split:if_splits)

lemma add_spvec_commute: "add_spvec a b = add_spvec b a"
by (induct a b rule: add_spvec.induct) auto

lemma add_spmat_commute: "add_spmat a b = add_spmat b a"
  by (induct a b rule: add_spmat.induct) (simp_all add: add_spvec_commute)
  
lemma sorted_add_spvec_helper2: "add_spvec ((a,b)#arr) brr = (ab, bb) # list \<Longrightarrow> aa < a \<Longrightarrow> sorted_spvec ((aa, ba) # brr) \<Longrightarrow> aa < ab"
  by (smt (verit, best) add_spvec.elims fst_conv list.sel(1) sorted_spvec_cons3)

lemma sorted_add_spmat_helper2: "add_spmat ((a,b)#arr) brr = (ab, bb) # list \<Longrightarrow> aa < a \<Longrightarrow> sorted_spvec ((aa, ba) # brr) \<Longrightarrow> aa < ab"
  by (metis (no_types, opaque_lifting) add_spmat.simps(1) list.sel(1) neq_Nil_conv sorted_add_spmat_helper sorted_spvec_cons3)

lemma sorted_spvec_add_spvec: "sorted_spvec a \<Longrightarrow> sorted_spvec b \<Longrightarrow> sorted_spvec (add_spvec a b)"
proof (induct a b rule: add_spvec.induct)
  case (3 i a arr j b brr)
  then have "sorted_spvec arr" "sorted_spvec brr"
    using sorted_spvec_cons1 by blast+
  with 3 show ?case
    apply simp
    by (smt (verit, ccfv_SIG) add_spvec.simps(2) list.sel(3) sorted_add_spvec_helper sorted_spvec.elims(1))
qed auto

lemma sorted_spvec_add_spmat:
  "sorted_spvec A \<Longrightarrow> sorted_spvec B \<Longrightarrow> sorted_spvec (add_spmat A B)"
proof (induct A B rule: add_spmat.induct)
  case (1 bs)
  then show ?case by auto
next
  case (2 v va)
  then show ?case by auto
next
  case (3 i a as j b bs)
  then have "sorted_spvec as" "sorted_spvec bs"
    using sorted_spvec_cons1 by blast+
  with 3 show ?case
    apply simp
    by (smt (verit) Pair_inject add_spmat.elims list.discI list.inject sorted_spvec.elims(1))
qed

lemma sorted_spmat_add_spmat[rule_format]: "sorted_spmat A \<Longrightarrow> sorted_spmat B \<Longrightarrow> sorted_spmat (add_spmat A B)"
  by (induct A B rule: add_spmat.induct) (simp_all add: sorted_spvec_add_spvec)

fun le_spvec :: "('a::lattice_ab_group_add) spvec \<Rightarrow> 'a spvec \<Rightarrow> bool"
where
(* "measure (% (a,b). (length a) + (length b))" *)
  "le_spvec [] [] = True"
| "le_spvec ((_,a)#as) [] = (a \<le> 0 & le_spvec as [])"
| "le_spvec [] ((_,b)#bs) = (0 \<le> b & le_spvec [] bs)"
| "le_spvec ((i,a)#as) ((j,b)#bs) = (
    if (i < j) then a \<le> 0 & le_spvec as ((j,b)#bs)
    else if (j < i) then 0 \<le> b & le_spvec ((i,a)#as) bs
    else a \<le> b & le_spvec as bs)"

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
    (\<forall>j i. (Rep_matrix A j i \<noteq> 0) \<longrightarrow> (Rep_matrix B j i = 0)) & (\<forall>j i. (Rep_matrix B j i \<noteq> 0) \<longrightarrow> (Rep_matrix A j i = 0))"  

lemma disj_matrices_contr1: "disj_matrices A B \<Longrightarrow> Rep_matrix A j i \<noteq> 0 \<Longrightarrow> Rep_matrix B j i = 0"
   by (simp add: disj_matrices_def)

lemma disj_matrices_contr2: "disj_matrices A B \<Longrightarrow> Rep_matrix B j i \<noteq> 0 \<Longrightarrow> Rep_matrix A j i = 0"
   by (simp add: disj_matrices_def)


lemma disj_matrices_add:
  fixes A :: "('a::lattice_ab_group_add) matrix"
  shows  "disj_matrices A B \<Longrightarrow> disj_matrices C D \<Longrightarrow> disj_matrices A D 
       \<Longrightarrow> disj_matrices B C \<Longrightarrow> (A + B \<le> C + D) = (A \<le> C \<and> B \<le> D)"
  apply (intro iffI conjI)
  unfolding le_matrix_def disj_matrices_def
  apply (metis Rep_matrix_add group_cancel.rule0 order_refl)
  apply (metis (no_types, lifting) Rep_matrix_add add_cancel_right_left dual_order.refl)
  by (meson add_mono le_matrix_def)

lemma disj_matrices_zero1[simp]: "disj_matrices 0 B"
  by (simp add: disj_matrices_def)

lemma disj_matrices_zero2[simp]: "disj_matrices A 0"
  by (simp add: disj_matrices_def)

lemma disj_matrices_commute: "disj_matrices A B = disj_matrices B A"
  by (auto simp: disj_matrices_def)

lemma disj_matrices_add_le_zero: "disj_matrices A B \<Longrightarrow>
  (A + B \<le> 0) = (A \<le> 0 & (B::('a::lattice_ab_group_add) matrix) \<le> 0)"
  by (rule disj_matrices_add[of A B 0 0, simplified])

lemma disj_matrices_add_zero_le: "disj_matrices A B \<Longrightarrow>
  (0 \<le> A + B) = (0 \<le> A & 0 \<le> (B::('a::lattice_ab_group_add) matrix))"
  by (rule disj_matrices_add[of 0 0 A B, simplified])

lemma disj_matrices_add_x_le: "disj_matrices A B \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (A \<le> B + C) = (A \<le> C & 0 \<le> (B::('a::lattice_ab_group_add) matrix))"
  by (auto simp: disj_matrices_add[of 0 A B C, simplified])

lemma disj_matrices_add_le_x: "disj_matrices A B \<Longrightarrow> disj_matrices B C \<Longrightarrow> 
  (B + A \<le> C) = (A \<le> C &  (B::('a::lattice_ab_group_add) matrix) \<le> 0)"
  by (auto simp: disj_matrices_add[of B A 0 C,simplified] disj_matrices_commute)

lemma disj_sparse_row_singleton: "i \<le> j \<Longrightarrow> sorted_spvec((j,y)#v) \<Longrightarrow> disj_matrices (sparse_row_vector v) (singleton_matrix 0 i x)"
  apply (simp add: disj_matrices_def)
  using sorted_sparse_row_vector_zero by blast

lemma disj_matrices_x_add: "disj_matrices A B \<Longrightarrow> disj_matrices A C \<Longrightarrow> disj_matrices (A::('a::lattice_ab_group_add) matrix) (B+C)"
  by (smt (verit, ccfv_SIG) Rep_matrix_add add_0 disj_matrices_def)

lemma disj_matrices_add_x: "disj_matrices A B \<Longrightarrow> disj_matrices A C \<Longrightarrow> disj_matrices (B+C) (A::('a::lattice_ab_group_add) matrix)" 
  by (simp add: disj_matrices_x_add disj_matrices_commute)

lemma disj_singleton_matrices[simp]: "disj_matrices (singleton_matrix j i x) (singleton_matrix u v y) = (j \<noteq> u | i \<noteq> v | x = 0 | y = 0)" 
  by (auto simp: disj_matrices_def)

lemma disj_move_sparse_vec_mat:
  assumes "j \<le> a" and "sorted_spvec ((a, c) # as)"
  shows "disj_matrices (sparse_row_matrix as) (move_matrix (sparse_row_vector b) (int j) i)"
proof -
  have "Rep_matrix (sparse_row_vector b) (n-j) (nat (int m - i)) = 0"
    if "\<not> n<j" and nz: "Rep_matrix (sparse_row_matrix as) n m \<noteq> 0"
    for n m
  proof -
    have "n \<noteq> j"
      using assms sorted_sparse_row_matrix_zero nz by blast
    with that have "j < n"  by auto
    then show ?thesis
      by (metis One_nat_def Suc_diff_Suc nrows nrows_spvec plus_1_eq_Suc trans_le_add1)
  qed
  then show ?thesis
    by (auto simp: disj_matrices_def nat_minus_as_int)
qed

lemma disj_move_sparse_row_vector_twice:
  "j \<noteq> u \<Longrightarrow> disj_matrices (move_matrix (sparse_row_vector a) j i) (move_matrix (sparse_row_vector b) u v)"
  unfolding disj_matrices_def
  by (smt (verit, ccfv_SIG) One_nat_def Rep_move_matrix of_nat_1 le_nat_iff nrows nrows_spvec of_nat_le_iff)

lemma le_spvec_iff_sparse_row_le:
  "sorted_spvec a \<Longrightarrow> sorted_spvec b \<Longrightarrow> (le_spvec a b) \<longleftrightarrow> (sparse_row_vector a \<le> sparse_row_vector b)"
proof (induct a b rule: le_spvec.induct)
  case 1
  then show ?case
    by auto
next
  case (2 uu a as)
  then have "sorted_spvec as"
    by (metis sorted_spvec_cons1)
  with 2 show ?case
    apply (simp add: add.commute)
    by (metis disj_matrices_add_le_zero disj_sparse_row_singleton le_refl singleton_le_zero)
next
  case (3 uv b bs)
  then have "sorted_spvec bs"
    by (metis sorted_spvec_cons1)
  with 3 show ?case
    apply (simp add: add.commute)
    by (metis disj_matrices_add_zero_le disj_sparse_row_singleton le_refl singleton_ge_zero)
next
  case (4 i a as j b bs)
  then obtain \<section>: "sorted_spvec as" "sorted_spvec bs"
    by (metis sorted_spvec_cons1)
  show ?case
  proof (cases i j rule: linorder_cases)
    case less
    with 4 \<section> show ?thesis
      apply (simp add: )
      by (metis disj_matrices_add_le_x disj_matrices_add_x disj_matrices_commute disj_singleton_matrices disj_sparse_row_singleton less_imp_le_nat singleton_le_zero not_le)
  next
    case equal
    with 4 \<section> show ?thesis
      apply (simp add: )
      by (metis disj_matrices_add disj_matrices_commute disj_sparse_row_singleton order_refl singleton_matrix_le)
  next
    case greater
    with 4 \<section> show ?thesis
      apply (simp add: )
      by (metis disj_matrices_add_x disj_matrices_add_x_le disj_matrices_commute disj_singleton_matrices disj_sparse_row_singleton le_refl order_less_le singleton_ge_zero)
  qed
qed

lemma le_spvec_empty2_sparse_row: 
  "sorted_spvec b \<Longrightarrow> le_spvec b [] = (sparse_row_vector b \<le> 0)"
  by (simp add: le_spvec_iff_sparse_row_le)

lemma le_spvec_empty1_sparse_row: 
  "(sorted_spvec b) \<Longrightarrow> (le_spvec [] b = (0 \<le> sparse_row_vector b))"
  by (simp add: le_spvec_iff_sparse_row_le)

lemma le_spmat_iff_sparse_row_le:
  "\<lbrakk>sorted_spvec A; sorted_spmat A; sorted_spvec B; sorted_spmat B\<rbrakk> \<Longrightarrow> 
  le_spmat A B = (sparse_row_matrix A \<le> sparse_row_matrix B)"
proof (induct A B rule: le_spmat.induct)
  case (4 i a as j b bs)
  then obtain \<section>: "sorted_spvec as" "sorted_spvec bs"
    by (metis sorted_spvec_cons1)
  show ?case
  proof (cases i j rule: linorder_cases)
    case less
    with 4 \<section> show ?thesis
      apply (simp add: sparse_row_matrix_cons le_spvec_empty2_sparse_row)
      by (metis disj_matrices_add_le_x disj_matrices_add_x disj_matrices_commute disj_move_sparse_row_vector_twice disj_move_sparse_vec_mat int_eq_iff less_not_refl move_matrix_le_zero order_le_less)
  next
    case equal
    with 4 \<section> show ?thesis
      by (simp add: sparse_row_matrix_cons le_spvec_iff_sparse_row_le disj_matrices_commute disj_move_sparse_vec_mat[OF order_refl] disj_matrices_add)
  next
    case greater
    with 4 \<section> show ?thesis
      apply (simp add: sparse_row_matrix_cons le_spvec_empty1_sparse_row)
      by (metis disj_matrices_add_x disj_matrices_add_x_le disj_matrices_commute disj_move_sparse_row_vector_twice disj_move_sparse_vec_mat move_matrix_zero_le nat_int nat_less_le of_nat_0_le_iff order_refl)
  qed
qed (auto simp add: sparse_row_matrix_cons disj_matrices_add_le_zero disj_matrices_add_zero_le disj_move_sparse_vec_mat[OF order_refl] 
    disj_matrices_commute sorted_spvec_cons1 le_spvec_empty2_sparse_row le_spvec_empty1_sparse_row)


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
proof (induct A)
  case Nil
  then show ?case by auto
next
  case (Cons a A)
  then show ?case
    by (simp add: sparse_row_vector_minus sparse_row_matrix_cons matrix_eqI)
qed

lemma Rep_sparse_row_vector_zero:
  assumes "x \<noteq> 0"
    shows "Rep_matrix (sparse_row_vector v) x y = 0"
  by (metis Suc_leI assms le0 le_eq_less_or_eq nrows_le nrows_spvec)
    
lemma sparse_row_matrix_abs:
  "sorted_spvec A \<Longrightarrow> sorted_spmat A \<Longrightarrow> sparse_row_matrix (abs_spmat A) = \<bar>sparse_row_matrix A\<bar>"
proof (induct A)
  case Nil
  then show ?case by auto
next
  case (Cons ab A)
  then have A: "sorted_spvec A"
    using sorted_spvec_cons1 by blast
  show ?case 
  proof (cases ab)
    case (Pair a b)
    show ?thesis
      unfolding Pair
    proof (intro matrix_eqI)
      fix m n
      show "Rep_matrix (sparse_row_matrix (abs_spmat ((a,b) # A))) m n 
          = Rep_matrix \<bar>sparse_row_matrix ((a,b) # A)\<bar> m n"
        using Cons Pair A 
        apply (simp add: sparse_row_vector_abs sparse_row_matrix_cons)
        apply (cases "m=a")
        using sorted_sparse_row_matrix_zero apply fastforce
        by (simp add: Rep_sparse_row_vector_zero)
    qed
  qed
qed

lemma sorted_spvec_minus_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec (minus_spmat A)"
by (induct A rule: sorted_spvec.induct) (auto simp: sorted_spvec.simps)

lemma sorted_spvec_abs_spmat: "sorted_spvec A \<Longrightarrow> sorted_spvec (abs_spmat A)" 
  by (induct A rule: sorted_spvec.induct) (auto simp: sorted_spvec.simps)

lemma sorted_spmat_minus_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat (minus_spmat A)"
  by (induct A) (simp_all add: sorted_spvec_minus_spvec)

lemma sorted_spmat_abs_spmat: "sorted_spmat A \<Longrightarrow> sorted_spmat (abs_spmat A)"
  by (induct A) (simp_all add: sorted_spvec_abs_spvec)

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
lemma bool3: "((P::bool) \<and> True) = P" by blast
lemma bool4: "(True \<and> (P::bool)) = P" by blast
lemma bool5: "((P::bool) \<and> False) = False" by blast
lemma bool6: "(False \<and> (P::bool)) = False" by blast
lemma bool7: "((P::bool) \<or> True) = True" by blast
lemma bool8: "(True \<or> (P::bool)) = True" by blast
lemma bool9: "((P::bool) \<or> False) = P" by blast
lemma bool10: "(False \<or> (P::bool)) = P" by blast
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
  apply (intro matrix_eqI)
  by (smt (verit, del_insts) Rep_combine_matrix Rep_zero_matrix_def add.commute comm_monoid_add_class.add_0 disj_matrices_def plus_matrix_def sup.idem)

lemma nprt_add: "disj_matrices A (B::(_::lattice_ring) matrix) \<Longrightarrow> nprt (A+B) = nprt A + nprt B"
  unfolding nprt_def inf_matrix_def
  apply (intro matrix_eqI)
  by (smt (verit, ccfv_threshold) Rep_combine_matrix Rep_matrix_add add.commute add_cancel_right_right add_eq_inf_sup disj_matrices_contr2 sup.idem)

lemma pprt_singleton[simp]: 
  fixes x:: "_::lattice_ring"
  shows "pprt (singleton_matrix j i x) = singleton_matrix j i (pprt x)"
  unfolding pprt_def sup_matrix_def
  by (simp add: matrix_eqI)

lemma nprt_singleton[simp]:
  fixes x:: "_::lattice_ring"
  shows "nprt (singleton_matrix j i x) = singleton_matrix j i (nprt x)"
  by (metis add_left_imp_eq pprt_singleton prts singleton_matrix_add)

lemma sparse_row_vector_pprt:
  fixes v:: "_::lattice_ring spvec"
  shows "sorted_spvec v \<Longrightarrow> sparse_row_vector (pprt_spvec v) = pprt (sparse_row_vector v)"
proof (induct v rule: sorted_spvec.induct)
  case (3 m x n y bs)
  then show ?case
    apply simp
    apply (subst pprt_add)
     apply (metis disj_matrices_commute disj_sparse_row_singleton order.refl fst_conv prod.sel(2) sparse_row_vector_cons)
    by (metis pprt_singleton sorted_spvec_cons1)
qed auto

lemma sparse_row_vector_nprt:
  fixes v:: "_::lattice_ring spvec"
  shows "sorted_spvec v \<Longrightarrow> sparse_row_vector (nprt_spvec v) = nprt (sparse_row_vector v)"
proof (induct v rule: sorted_spvec.induct)
  case (3 m x n y bs)
  then show ?case
    apply simp
    apply (subst nprt_add)
    apply (metis disj_matrices_commute disj_sparse_row_singleton dual_order.refl fst_conv prod.sel(2) sparse_row_vector_cons)
    using sorted_spvec_cons1 by force
qed auto
  
  
lemma pprt_move_matrix: "pprt (move_matrix (A::('a::lattice_ring) matrix) j i) = move_matrix (pprt A) j i"
  by (simp add: pprt_def sup_matrix_def matrix_eqI)

lemma nprt_move_matrix: "nprt (move_matrix (A::('a::lattice_ring) matrix) j i) = move_matrix (nprt A) j i"
  by (simp add: nprt_def inf_matrix_def matrix_eqI)

lemma sparse_row_matrix_pprt: 
  fixes m:: "'a::lattice_ring spmat"
  shows "sorted_spvec m \<Longrightarrow> sorted_spmat m \<Longrightarrow> sparse_row_matrix (pprt_spmat m) = pprt (sparse_row_matrix m)"
proof (induct m rule: sorted_spvec.induct)
  case (2 a)
  then show ?case
    by (simp add: pprt_move_matrix sparse_row_matrix_cons sparse_row_vector_pprt)
next
  case (3 m x n y bs)
  then show ?case 
    apply (simp add: sparse_row_matrix_cons sparse_row_vector_pprt)
    apply (subst pprt_add)
     apply (subst disj_matrices_commute)
     apply (metis disj_move_sparse_vec_mat eq_imp_le fst_conv prod.sel(2) sparse_row_matrix_cons)
    apply (simp add: sorted_spvec.simps pprt_move_matrix)
    done
qed auto

lemma sparse_row_matrix_nprt:
  fixes m:: "'a::lattice_ring spmat"
  shows "sorted_spvec m \<Longrightarrow> sorted_spmat m \<Longrightarrow> sorted_spmat m \<Longrightarrow> sparse_row_matrix (nprt_spmat m) = nprt (sparse_row_matrix m)"
proof (induct m rule: sorted_spvec.induct)
  case (2 a)
  then show ?case
    by (simp add: nprt_move_matrix sparse_row_matrix_cons sparse_row_vector_nprt)
next
  case (3 m x n y bs)
  then show ?case
    apply (simp add: sparse_row_matrix_cons sparse_row_vector_nprt)
    apply (subst nprt_add)
     apply (subst disj_matrices_commute)
     apply (metis disj_move_sparse_vec_mat fst_conv nle_le prod.sel(2) sparse_row_matrix_cons)
    apply (simp add: sorted_spvec.simps nprt_move_matrix)
    done
qed auto

lemma sorted_pprt_spvec: "sorted_spvec v \<Longrightarrow> sorted_spvec (pprt_spvec v)"
proof (induct v rule: sorted_spvec.induct)
  case 1
  then show ?case by auto
next
  case (2 a)
  then show ?case 
    by (simp add: sorted_spvec_step1)
next
  case (3 m x n y bs)
  then show ?case
    by (simp add: sorted_spvec_step)
qed

lemma sorted_nprt_spvec: "sorted_spvec v \<Longrightarrow> sorted_spvec (nprt_spvec v)"
  by (induct v rule: sorted_spvec.induct) (simp_all add: sorted_spvec.simps split:list.split_asm)

lemma sorted_spvec_pprt_spmat: "sorted_spvec m \<Longrightarrow> sorted_spvec (pprt_spmat m)"
  by (induct m rule: sorted_spvec.induct) (simp_all add: sorted_spvec.simps split:list.split_asm)

lemma sorted_spvec_nprt_spmat: "sorted_spvec m \<Longrightarrow> sorted_spvec (nprt_spmat m)"
by (induct m rule: sorted_spvec.induct) (simp_all add: sorted_spvec.simps split:list.split_asm)

lemma sorted_spmat_pprt_spmat: "sorted_spmat m \<Longrightarrow> sorted_spmat (pprt_spmat m)"
  by (induct m) (simp_all add: sorted_pprt_spvec)

lemma sorted_spmat_nprt_spmat: "sorted_spmat m \<Longrightarrow> sorted_spmat (nprt_spmat m)"
  by (induct m) (simp_all add: sorted_nprt_spvec)

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
  "sparse_row_matrix A1 \<le> A"
  "A \<le> sparse_row_matrix A2"
  "sparse_row_matrix c1 \<le> c"
  "c \<le> sparse_row_matrix c2"
  "\<bar>x\<bar> \<le> sparse_row_matrix r"
  shows
  "c * x \<le> sparse_row_matrix (add_spmat (mult_spmat y b, mult_spmat (add_spmat (add_spmat (mult_spmat y (diff_spmat A2 A1), 
  abs_spmat (diff_spmat (mult_spmat y A1) c1)), diff_spmat c2 c1)) r))"
  by (insert prems, simp add: sparse_row_matrix_op_simps linprog_dual_estimate_1[where A=A])
*)

end
