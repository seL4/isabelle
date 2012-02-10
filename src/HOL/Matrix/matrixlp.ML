(*  Title:      HOL/Matrix/matrixlp.ML
    Author:     Steven Obua
*)

signature MATRIX_LP =
sig
  val lp_dual_estimate_prt : string -> int -> thm
  val lp_dual_estimate_prt_primitive :
    cterm * (cterm * cterm) * (cterm * cterm) * cterm * (cterm * cterm) -> thm
  val matrix_compute : cterm -> thm
  val matrix_simplify : thm -> thm
  val prove_bound : string -> int -> thm
  val float2real : string * string -> Real.real
end

structure MatrixLP : MATRIX_LP =
struct

fun inst_real thm =
  let val certT = ctyp_of (Thm.theory_of_thm thm) in
    Drule.export_without_context (Thm.instantiate
      ([(certT (TVar (hd (Misc_Legacy.term_tvars (prop_of thm)))), certT HOLogic.realT)], []) thm)
  end

local

val cert =  cterm_of @{theory}

in

fun lp_dual_estimate_prt_primitive (y, (A1, A2), (c1, c2), b, (r1, r2)) =
  let
    val th = inst_real @{thm "spm_mult_le_dual_prts_no_let"}
    fun var s x = (cert (Var ((s,0), FloatSparseMatrixBuilder.spmatT)), x)
    val th = Thm.instantiate ([], [var "A1" A1, var "A2" A2, var "y" y, var "c1" c1, var "c2" c2,
                                   var "r1" r1, var "r2" r2, var "b" b]) th
  in th end

fun lp_dual_estimate_prt lptfile prec =
    let
        val certificate =
            let
                open Fspmlp
                val l = load lptfile prec false
            in
                (y l |> cert, A l |> pairself cert, c l |> pairself cert, b l |> cert, r12 l |> pairself cert)
            end
    in
        lp_dual_estimate_prt_primitive certificate
    end

end

local
    val ths = ComputeHOL.prep_thms @{thms "ComputeHOL.compute_list_case" "ComputeHOL.compute_let"
      "ComputeHOL.compute_if" "ComputeFloat.arith" "SparseMatrix.sparse_row_matrix_arith_simps"
      "ComputeHOL.compute_bool" "ComputeHOL.compute_pair"
      "SparseMatrix.sorted_sp_simps" "ComputeNumeral.number_norm"
      "ComputeNumeral.natnorm"};
    val computer = PCompute.make Compute.SML @{theory} ths []
in

fun matrix_compute c = hd (PCompute.rewrite computer [c])

end
        
fun matrix_simplify th =
    let
        val simp_th = matrix_compute (cprop_of th)
        val th = Thm.strip_shyps (Thm.equal_elim simp_th th)
        fun removeTrue th = removeTrue (Thm.implies_elim th TrueI) handle THM _ => th
    in
        removeTrue th
    end

fun prove_bound lptfile prec =
    let
        val th = lp_dual_estimate_prt lptfile prec
    in
        matrix_simplify th
    end

val realFromStr = the o Real.fromString;
fun float2real (x, y) = realFromStr x * Math.pow (2.0, realFromStr y);

end
