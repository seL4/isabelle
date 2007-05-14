(*  Title:      HOL/Matrix/cplex/MatrixLP.ML
    ID:         $Id$
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
    standard (Thm.instantiate
      ([(certT (TVar (hd (term_tvars (prop_of thm)))), certT HOLogic.realT)], []) thm)
  end

val spm_mult_le_dual_prts_no_let = thm "SparseMatrix.spm_mult_le_dual_prts_no_let";
val cert = cterm_of (Thm.theory_of_thm spm_mult_le_dual_prts_no_let);

fun lp_dual_estimate_prt_primitive (y, (A1, A2), (c1, c2), b, (r1, r2)) =
  let
    val th = inst_real spm_mult_le_dual_prts_no_let
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
                (y l |> cert, A l |> pairself cert, c l |> pairself cert, b l |> cert, r12 l |> pairself  cert)
            end
    in
        lp_dual_estimate_prt_primitive certificate
    end

fun is_meta_eq th =
    let
        fun check ((Const ("==", _)) $ _ $ _) = true
          | check _ = false
    in
        check (concl_of th)
    end

fun prep ths = filter is_meta_eq ths @ map (standard o mk_meta_eq) (filter_out is_meta_eq ths)

fun inst_tvar ty thm =
    let
        val certT = Thm.ctyp_of (Thm.theory_of_thm thm);
        val ord = prod_ord (prod_ord string_ord int_ord) (list_ord string_ord)
        val v = TVar (hd (sort ord (term_tvars (prop_of thm))))
    in
        standard (Thm.instantiate ([(certT v, certT ty)], []) thm)
    end

fun inst_tvars [] thms = thms
  | inst_tvars (ty::tys) thms = inst_tvars tys (map (inst_tvar ty) thms)

val matrix_compute =
    let
        val spvecT = FloatSparseMatrixBuilder.spvecT
        val spmatT = FloatSparseMatrixBuilder.spmatT
        val spvecT_elem = HOLogic.mk_prodT (HOLogic.natT, HOLogic.realT)
        val spmatT_elem = HOLogic.mk_prodT (HOLogic.natT, spvecT)
        val case_compute = map thm ["list_case_compute", "list_case_compute_empty", "list_case_compute_cons"]
        val ths =
            prep (
            (inst_tvars [HOLogic.intT, HOLogic.natT] (thms "Let_compute"))
            @ (inst_tvars [HOLogic.intT, HOLogic.intT] (thms "Let_compute"))
            @ (map (fn t => inst_tvar t (thm "If_True")) [HOLogic.intT, HOLogic.natT, HOLogic.realT, spvecT, spmatT, HOLogic.boolT])
            @ (map (fn t => inst_tvar t (thm "If_False")) [HOLogic.intT, HOLogic.natT, HOLogic.realT, spvecT, spmatT, HOLogic.boolT])
            @ (thms "MatrixLP.float_arith")
            @ (map (inst_tvar HOLogic.realT) (thms "MatrixLP.sparse_row_matrix_arith_simps"))
            @ (thms "MatrixLP.boolarith")
            @ (inst_tvars [HOLogic.natT, HOLogic.realT] [thm "fst_compute", thm "snd_compute"])
            @ (inst_tvars [HOLogic.natT, FloatSparseMatrixBuilder.spvecT] [thm "fst_compute", thm "snd_compute"])
            @ (inst_tvars [HOLogic.boolT, spmatT_elem] case_compute)
            @ (inst_tvars [HOLogic.boolT, spvecT_elem] case_compute)
            @ (inst_tvars [HOLogic.boolT, HOLogic.realT] case_compute)
            @ (inst_tvars [spvecT] (thms "MatrixLP.sorted_sp_simps"))
            @ (inst_tvars [HOLogic.realT] (thms "MatrixLP.sorted_sp_simps"))
            @ [thm "zero_eq_Numeral0_nat", thm "one_eq_Numeral1_nat"]
            @ (inst_tvars [HOLogic.intT] [thm "zero_eq_Numeral0_nring", thm "one_eq_Numeral1_nring"])
            @ (inst_tvars [HOLogic.realT] [thm "zero_eq_Numeral0_nring", thm "one_eq_Numeral1_nring"]))

        val c = Compute.basic_make (the_context ()) ths
    in
        Compute.rewrite c
    end

fun matrix_simplify th =
    let
        val simp_th = matrix_compute (cprop_of th)
        val th = strip_shyps (equal_elim simp_th th)
        fun removeTrue th = removeTrue (implies_elim th TrueI) handle _ => th
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
