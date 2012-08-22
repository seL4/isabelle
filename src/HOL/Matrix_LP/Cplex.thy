(*  Title:      HOL/Matrix_LP/Cplex.thy
    Author:     Steven Obua
*)

theory Cplex 
imports SparseMatrix LP ComputeFloat ComputeNumeral
begin

ML_file "Cplex_tools.ML"
ML_file "CplexMatrixConverter.ML"
ML_file "FloatSparseMatrixBuilder.ML"
ML_file "fspmlp.ML"

lemma spm_mult_le_dual_prts: 
  assumes
  "sorted_sparse_matrix A1"
  "sorted_sparse_matrix A2"
  "sorted_sparse_matrix c1"
  "sorted_sparse_matrix c2"
  "sorted_sparse_matrix y"
  "sorted_sparse_matrix r1"
  "sorted_sparse_matrix r2"
  "sorted_spvec b"
  "le_spmat [] y"
  "sparse_row_matrix A1 \<le> A"
  "A \<le> sparse_row_matrix A2"
  "sparse_row_matrix c1 \<le> c"
  "c \<le> sparse_row_matrix c2"
  "sparse_row_matrix r1 \<le> x"
  "x \<le> sparse_row_matrix r2"
  "A * x \<le> sparse_row_matrix (b::('a::lattice_ring) spmat)"
  shows
  "c * x \<le> sparse_row_matrix (add_spmat (mult_spmat y b)
  (let s1 = diff_spmat c1 (mult_spmat y A2); s2 = diff_spmat c2 (mult_spmat y A1) in 
  add_spmat (mult_spmat (pprt_spmat s2) (pprt_spmat r2)) (add_spmat (mult_spmat (pprt_spmat s1) (nprt_spmat r2)) 
  (add_spmat (mult_spmat (nprt_spmat s2) (pprt_spmat r1)) (mult_spmat (nprt_spmat s1) (nprt_spmat r1))))))"
  apply (simp add: Let_def)
  apply (insert assms)
  apply (simp add: sparse_row_matrix_op_simps algebra_simps)  
  apply (rule mult_le_dual_prts[where A=A, simplified Let_def algebra_simps])
  apply (auto)
  done

lemma spm_mult_le_dual_prts_no_let: 
  assumes
  "sorted_sparse_matrix A1"
  "sorted_sparse_matrix A2"
  "sorted_sparse_matrix c1"
  "sorted_sparse_matrix c2"
  "sorted_sparse_matrix y"
  "sorted_sparse_matrix r1"
  "sorted_sparse_matrix r2"
  "sorted_spvec b"
  "le_spmat [] y"
  "sparse_row_matrix A1 \<le> A"
  "A \<le> sparse_row_matrix A2"
  "sparse_row_matrix c1 \<le> c"
  "c \<le> sparse_row_matrix c2"
  "sparse_row_matrix r1 \<le> x"
  "x \<le> sparse_row_matrix r2"
  "A * x \<le> sparse_row_matrix (b::('a::lattice_ring) spmat)"
  shows
  "c * x \<le> sparse_row_matrix (add_spmat (mult_spmat y b)
  (mult_est_spmat r1 r2 (diff_spmat c1 (mult_spmat y A2)) (diff_spmat c2 (mult_spmat y A1))))"
  by (simp add: assms mult_est_spmat_def spm_mult_le_dual_prts[where A=A, simplified Let_def])

ML_file "matrixlp.ML"

end

