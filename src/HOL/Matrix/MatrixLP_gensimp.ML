open BasisLibrary;

use "Cplex.ML";
use "CplexMatrixConverter.ML";
use "ExactFloatingPoint.ML";
use "FloatArith.ML";
use "FloatSparseMatrixBuilder.ML";
use "fspmlp.ML";
use "codegen_prep.ML";
use "eq_codegen.ML";
use "conv.ML";


val th = theory "MatrixLP"
val sg = sign_of th
	 
fun prep x = standard (mk_meta_eq x)
	     
fun inst_real thm = standard (Thm.instantiate ([(fst (hd (term_tvars (prop_of thm))),
						 ctyp_of sg HOLogic.realT)], []) thm);
    
val spm_lp_dual_estimate_simp = 
    (thms "Float.arith_no_let") @ 
    (map inst_real (thms "SparseMatrix.sparse_row_matrix_arith_simps")) @ 
    (thms "SparseMatrix.sorted_sp_simps") @ 
    [thm "Product_Type.fst_conv", thm "Product_Type.snd_conv"] @ 
    (thms "SparseMatrix.boolarith") 
    
val simp_with = Simplifier.simplify (HOL_basic_ss addsimps [thm "SparseMatrix.if_case_eq", thm "Float.norm_0_1"])
		
val spm_lp_dual_estimate_simp = map simp_with spm_lp_dual_estimate_simp
				
val geninput = codegen_prep.prepare_thms spm_lp_dual_estimate_simp

val _ = SimprocsCodegen.use_simprocs_code sg geninput
