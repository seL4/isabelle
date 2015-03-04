(*  Title:      HOL/Matrix_LP/matrixlp.ML
    Author:     Steven Obua
*)

signature MATRIX_LP =
sig
  val matrix_compute : cterm -> thm
  val matrix_simplify : thm -> thm
end

structure MatrixLP : MATRIX_LP =
struct

val compute_thms = ComputeHOL.prep_thms @{thms "ComputeHOL.compute_case_list" "ComputeHOL.compute_let"
  "ComputeHOL.compute_if" "ComputeFloat.arith" "SparseMatrix.sparse_row_matrix_arith_simps"
  "ComputeHOL.compute_bool" "ComputeHOL.compute_pair"
  "SparseMatrix.sorted_sp_simps"
  "ComputeNumeral.natnorm"}; (*"ComputeNumeral.number_norm"*)

val computer = PCompute.make Compute.SML @{theory} compute_thms []

fun matrix_compute c = hd (PCompute.rewrite computer [c])

fun matrix_simplify th =
  let
    val simp_th = matrix_compute (Thm.cprop_of th)
    val th = Thm.strip_shyps (Thm.equal_elim simp_th th)
    fun removeTrue th = removeTrue (Thm.implies_elim th TrueI) handle THM _ => th
  in
    removeTrue th
  end

end
