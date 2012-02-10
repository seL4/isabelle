(*  Title:      HOL/Matrix/matrixlp.ML
    Author:     Steven Obua
*)

signature MATRIX_LP =
sig
  val matrix_compute : cterm -> thm
  val matrix_simplify : thm -> thm
  val prove_bound : string -> int -> thm
  val float2real : string * string -> Real.real
end

structure MatrixLP : MATRIX_LP =
struct

val compute_thms = ComputeHOL.prep_thms @{thms "ComputeHOL.compute_list_case" "ComputeHOL.compute_let"
  "ComputeHOL.compute_if" "ComputeFloat.arith" "SparseMatrix.sparse_row_matrix_arith_simps"
  "ComputeHOL.compute_bool" "ComputeHOL.compute_pair"
  "SparseMatrix.sorted_sp_simps"
  "ComputeNumeral.natnorm"}; (*"ComputeNumeral.number_norm"*)

val spm_mult_le_dual_prts_no_let_real = @{thm "spm_mult_le_dual_prts_no_let" [where ?'a = real]}

fun lp_dual_estimate_prt lptfile prec =
  let
    val cert = cterm_of @{theory}
    fun var s x = (cert (Var ((s, 0), FloatSparseMatrixBuilder.spmatT)), x)
    val l = Fspmlp.load lptfile prec false
    val (y, (A1, A2), (c1, c2), b, (r1, r2)) =
      let
        open Fspmlp
      in
        (y l |> cert, A l |> pairself cert, c l |> pairself cert, b l |> cert, r12 l |> pairself cert)
      end
  in
    Thm.instantiate ([],
      [var "A1" A1, var "A2" A2, var "y" y, var "c1" c1, var "c2" c2, var "r1" r1, var "r2" r2, var "b" b])
      spm_mult_le_dual_prts_no_let_real
  end

val computer = PCompute.make Compute.SML @{theory} compute_thms []

fun matrix_compute c = hd (PCompute.rewrite computer [c])

fun matrix_simplify th =
  let
    val simp_th = matrix_compute (cprop_of th)
    val th = Thm.strip_shyps (Thm.equal_elim simp_th th)
    fun removeTrue th = removeTrue (Thm.implies_elim th TrueI) handle THM _ => th
  in
    removeTrue th
  end

val prove_bound = matrix_simplify oo lp_dual_estimate_prt;

val realFromStr = the o Real.fromString;
fun float2real (x, y) = realFromStr x * Math.pow (2.0, realFromStr y);

end
