(*  Title:      HOL/Matrix/Matrix.thy
    ID:         $Id$
    Author:     Steven Obua
*)

theory Matrix=MatrixGeneral:

instance matrix :: (minus) minus 
by intro_classes

instance matrix :: (plus) plus
by (intro_classes)

instance matrix :: ("{plus,times}") times
by (intro_classes)

defs (overloaded)
  plus_matrix_def: "A + B == combine_matrix (op +) A B"
  diff_matrix_def: "A - B == combine_matrix (op -) A B"
  minus_matrix_def: "- A == apply_matrix uminus A"
  times_matrix_def: "A * B == mult_matrix (op *) (op +) A B"

lemma is_meet_combine_matrix_meet: "is_meet (combine_matrix meet)"
by (simp_all add: is_meet_def le_matrix_def meet_left_le meet_right_le meet_imp_le)

instance matrix :: (lordered_ab_group) lordered_ab_group_meet
proof 
  fix A B C :: "('a::lordered_ab_group) matrix"
  show "A + B + C = A + (B + C)"    
    apply (simp add: plus_matrix_def)
    apply (rule combine_matrix_assoc[simplified associative_def, THEN spec, THEN spec, THEN spec])
    apply (simp_all add: add_assoc)
    done
  show "A + B = B + A"
    apply (simp add: plus_matrix_def)
    apply (rule combine_matrix_commute[simplified commutative_def, THEN spec, THEN spec])
    apply (simp_all add: add_commute)
    done
  show "0 + A = A"
    apply (simp add: plus_matrix_def)
    apply (rule combine_matrix_zero_l_neutral[simplified zero_l_neutral_def, THEN spec])
    apply (simp)
    done
  show "- A + A = 0" 
    by (simp add: plus_matrix_def minus_matrix_def Rep_matrix_inject[symmetric] ext)
  show "A - B = A + - B" 
    by (simp add: plus_matrix_def diff_matrix_def minus_matrix_def Rep_matrix_inject[symmetric] ext)
  show "\<exists>m\<Colon>'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix. is_meet m"
    by (auto intro: is_meet_combine_matrix_meet)
  assume "A <= B"
  then show "C + A <= C + B"
    apply (simp add: plus_matrix_def)
    apply (rule le_left_combine_matrix)
    apply (simp_all)
    done
qed

defs (overloaded)
  abs_matrix_def: "abs (A::('a::lordered_ab_group) matrix) == join A (- A)"

instance matrix :: (lordered_ring) lordered_ring
proof
  fix A B C :: "('a :: lordered_ring) matrix"
  show "A * B * C = A * (B * C)"
    apply (simp add: times_matrix_def)
    apply (rule mult_matrix_assoc)
    apply (simp_all add: associative_def ring_eq_simps)
    done
  show "(A + B) * C = A * C + B * C"
    apply (simp add: times_matrix_def plus_matrix_def)
    apply (rule l_distributive_matrix[simplified l_distributive_def, THEN spec, THEN spec, THEN spec])
    apply (simp_all add: associative_def commutative_def ring_eq_simps)
    done
  show "A * (B + C) = A * B + A * C"
    apply (simp add: times_matrix_def plus_matrix_def)
    apply (rule r_distributive_matrix[simplified r_distributive_def, THEN spec, THEN spec, THEN spec])
    apply (simp_all add: associative_def commutative_def ring_eq_simps)
    done  
  show "abs A = join A (-A)" 
    by (simp add: abs_matrix_def)
  assume a: "A \<le> B"
  assume b: "0 \<le> C"
  from a b show "C * A \<le> C * B"
    apply (simp add: times_matrix_def)
    apply (rule le_left_mult)
    apply (simp_all add: add_mono mult_left_mono)
    done
  from a b show "A * C \<le> B * C"
    apply (simp add: times_matrix_def)
    apply (rule le_right_mult)
    apply (simp_all add: add_mono mult_right_mono)
    done
qed

lemma Rep_matrix_add[simp]: "Rep_matrix ((a::('a::lordered_ab_group)matrix)+b) j i  = (Rep_matrix a j i) + (Rep_matrix b j i)"
by (simp add: plus_matrix_def)

lemma Rep_matrix_mult: "Rep_matrix ((a::('a::lordered_ring) matrix) * b) j i = 
  foldseq (op +) (% k.  (Rep_matrix a j k) * (Rep_matrix b k i)) (max (ncols a) (nrows b))"
apply (simp add: times_matrix_def)
apply (simp add: Rep_mult_matrix)
done
 

lemma apply_matrix_add: "! x y. f (x+y) = (f x) + (f y) \<Longrightarrow> f 0 = (0::'a) \<Longrightarrow> apply_matrix f ((a::('a::lordered_ab_group) matrix) + b) = (apply_matrix f a) + (apply_matrix f b)"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (simp)
done

lemma singleton_matrix_add: "singleton_matrix j i ((a::_::lordered_ab_group)+b) = (singleton_matrix j i a) + (singleton_matrix j i b)"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (simp)
done

lemma nrows_mult: "nrows ((A::('a::lordered_ring) matrix) * B) <= nrows A"
by (simp add: times_matrix_def mult_nrows)

lemma ncols_mult: "ncols ((A::('a::lordered_ring) matrix) * B) <= ncols B"
by (simp add: times_matrix_def mult_ncols)

constdefs
  one_matrix :: "nat \<Rightarrow> ('a::{zero,one}) matrix"
  "one_matrix n == Abs_matrix (% j i. if j = i & j < n then 1 else 0)"

lemma Rep_one_matrix[simp]: "Rep_matrix (one_matrix n) j i = (if (j = i & j < n) then 1 else 0)"
apply (simp add: one_matrix_def)
apply (subst RepAbs_matrix)
apply (rule exI[of _ n], simp add: split_if)+
by (simp add: split_if, arith)

lemma nrows_one_matrix[simp]: "nrows ((one_matrix n) :: ('a::axclass_0_neq_1)matrix) = n" (is "?r = _")
proof -
  have "?r <= n" by (simp add: nrows_le)
  moreover have "n <= ?r" by (simp add:le_nrows, arith)
  ultimately show "?r = n" by simp
qed

lemma ncols_one_matrix[simp]: "ncols ((one_matrix n) :: ('a::axclass_0_neq_1)matrix) = n" (is "?r = _")
proof -
  have "?r <= n" by (simp add: ncols_le)
  moreover have "n <= ?r" by (simp add: le_ncols, arith)
  ultimately show "?r = n" by simp
qed

lemma one_matrix_mult_right[simp]: "ncols A <= n \<Longrightarrow> (A::('a::{lordered_ring,ring_1}) matrix) * (one_matrix n) = A"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply (simp add: times_matrix_def Rep_mult_matrix)
apply (rule_tac j1="xa" in ssubst[OF foldseq_almostzero])
apply (simp_all)
by (simp add: max_def ncols)

lemma one_matrix_mult_left[simp]: "nrows A <= n \<Longrightarrow> (one_matrix n) * A = (A::('a::{lordered_ring, ring_1}) matrix)"
apply (subst Rep_matrix_inject[THEN sym])
apply (rule ext)+
apply (simp add: times_matrix_def Rep_mult_matrix)
apply (rule_tac j1="x" in ssubst[OF foldseq_almostzero])
apply (simp_all)
by (simp add: max_def nrows)

lemma transpose_matrix_mult: "transpose_matrix ((A::('a::{lordered_ring,comm_ring}) matrix)*B) = (transpose_matrix B) * (transpose_matrix A)"
apply (simp add: times_matrix_def)
apply (subst transpose_mult_matrix)
apply (simp_all add: mult_commute)
done

lemma transpose_matrix_add: "transpose_matrix ((A::('a::lordered_ab_group) matrix)+B) = transpose_matrix A + transpose_matrix B"
by (simp add: plus_matrix_def transpose_combine_matrix)

lemma transpose_matrix_diff: "transpose_matrix ((A::('a::lordered_ab_group) matrix)-B) = transpose_matrix A - transpose_matrix B"
by (simp add: diff_matrix_def transpose_combine_matrix)

lemma transpose_matrix_minus: "transpose_matrix (-(A::('a::lordered_ring) matrix)) = - transpose_matrix (A::('a::lordered_ring) matrix)"
by (simp add: minus_matrix_def transpose_apply_matrix)

constdefs 
  right_inverse_matrix :: "('a::{lordered_ring, ring_1}) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool"
  "right_inverse_matrix A X == (A * X = one_matrix (max (nrows A) (ncols X))) \<and> nrows X \<le> ncols A" 
  left_inverse_matrix :: "('a::{lordered_ring, ring_1}) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool"
  "left_inverse_matrix A X == (X * A = one_matrix (max(nrows X) (ncols A))) \<and> ncols X \<le> nrows A" 
  inverse_matrix :: "('a::{lordered_ring, ring_1}) matrix \<Rightarrow> 'a matrix \<Rightarrow> bool"
  "inverse_matrix A X == (right_inverse_matrix A X) \<and> (left_inverse_matrix A X)"

lemma right_inverse_matrix_dim: "right_inverse_matrix A X \<Longrightarrow> nrows A = ncols X"
apply (insert ncols_mult[of A X], insert nrows_mult[of A X])
by (simp add: right_inverse_matrix_def)

lemma left_inverse_matrix_dim: "left_inverse_matrix A Y \<Longrightarrow> ncols A = nrows Y"
apply (insert ncols_mult[of Y A], insert nrows_mult[of Y A]) 
by (simp add: left_inverse_matrix_def)

lemma left_right_inverse_matrix_unique: 
  assumes "left_inverse_matrix A Y" "right_inverse_matrix A X"
  shows "X = Y"
proof -
  have "Y = Y * one_matrix (nrows A)" 
    apply (subst one_matrix_mult_right)
    apply (insert prems)
    by (simp_all add: left_inverse_matrix_def)
  also have "\<dots> = Y * (A * X)" 
    apply (insert prems)
    apply (frule right_inverse_matrix_dim)
    by (simp add: right_inverse_matrix_def)
  also have "\<dots> = (Y * A) * X" by (simp add: mult_assoc)
  also have "\<dots> = X" 
    apply (insert prems)
    apply (frule left_inverse_matrix_dim)
    apply (simp_all add:  left_inverse_matrix_def right_inverse_matrix_def one_matrix_mult_left)
    done
  ultimately show "X = Y" by (simp)
qed

lemma inverse_matrix_inject: "\<lbrakk> inverse_matrix A X; inverse_matrix A Y \<rbrakk> \<Longrightarrow> X = Y"
  by (auto simp add: inverse_matrix_def left_right_inverse_matrix_unique)

lemma one_matrix_inverse: "inverse_matrix (one_matrix n) (one_matrix n)"
  by (simp add: inverse_matrix_def left_inverse_matrix_def right_inverse_matrix_def)

lemma zero_imp_mult_zero: "(a::'a::ring) = 0 | b = 0 \<Longrightarrow> a * b = 0"
by auto

lemma Rep_matrix_zero_imp_mult_zero:
  "! j i k. (Rep_matrix A j k = 0) | (Rep_matrix B k i) = 0  \<Longrightarrow> A * B = (0::('a::lordered_ring) matrix)"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (auto simp add: Rep_matrix_mult foldseq_zero zero_imp_mult_zero)
done

lemma add_nrows: "nrows (A::('a::comm_monoid_add) matrix) <= u \<Longrightarrow> nrows B <= u \<Longrightarrow> nrows (A + B) <= u"
apply (simp add: plus_matrix_def)
apply (rule combine_nrows)
apply (simp_all)
done

lemma move_matrix_row_mult: "move_matrix ((A::('a::lordered_ring) matrix) * B) j 0 = (move_matrix A j 0) * B"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (auto simp add: Rep_matrix_mult foldseq_zero)
apply (rule_tac foldseq_zerotail[symmetric])
apply (auto simp add: nrows zero_imp_mult_zero max2)
apply (rule order_trans)
apply (rule ncols_move_matrix_le)
apply (simp add: max1)
done

lemma move_matrix_col_mult: "move_matrix ((A::('a::lordered_ring) matrix) * B) 0 i = A * (move_matrix B 0 i)"
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (auto simp add: Rep_matrix_mult foldseq_zero)
apply (rule_tac foldseq_zerotail[symmetric])
apply (auto simp add: ncols zero_imp_mult_zero max1)
apply (rule order_trans)
apply (rule nrows_move_matrix_le)
apply (simp add: max2)
done

lemma move_matrix_add: "((move_matrix (A + B) j i)::(('a::lordered_ab_group) matrix)) = (move_matrix A j i) + (move_matrix B j i)" 
apply (subst Rep_matrix_inject[symmetric])
apply (rule ext)+
apply (simp)
done

lemma move_matrix_mult: "move_matrix ((A::('a::lordered_ring) matrix)*B) j i = (move_matrix A j 0) * (move_matrix B 0 i)"
by (simp add: move_matrix_ortho[of "A*B"] move_matrix_col_mult move_matrix_row_mult)

constdefs
  scalar_mult :: "('a::lordered_ring) \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix"
  "scalar_mult a m == apply_matrix (op * a) m"

lemma scalar_mult_zero[simp]: "scalar_mult y 0 = 0" 
  by (simp add: scalar_mult_def)

lemma scalar_mult_add: "scalar_mult y (a+b) = (scalar_mult y a) + (scalar_mult y b)"
  by (simp add: scalar_mult_def apply_matrix_add ring_eq_simps)

lemma Rep_scalar_mult[simp]: "Rep_matrix (scalar_mult y a) j i = y * (Rep_matrix a j i)" 
  by (simp add: scalar_mult_def)

lemma scalar_mult_singleton[simp]: "scalar_mult y (singleton_matrix j i x) = singleton_matrix j i (y * x)"
  apply (subst Rep_matrix_inject[symmetric])
  apply (rule ext)+
  apply (auto)
  done




end
