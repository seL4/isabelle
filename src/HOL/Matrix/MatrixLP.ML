use "MatrixLP_gensimp.ML";

signature MATRIX_LP = 
sig
  val lp_dual_estimate : string -> int -> thm
  val simplify : thm -> thm
end

structure MatrixLP : MATRIX_LP =
struct

val _ = SimprocsCodegen.use_simprocs_code sg geninput

val simp_le_spmat = simp_SparseMatrix_le_spmat_'_mult__'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real'''''_'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real'''''_bool'
val simp_add_spmat = simp_SparseMatrix_add_spmat_'_mult__'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real'''''_'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real'''''_List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real'''''
val simp_diff_spmat = simp_SparseMatrix_diff_spmat_'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''_List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''_List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''' 
val simp_abs_spmat = simp_SparseMatrix_abs_spmat_'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''_List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''' 
val simp_mult_spmat = simp_SparseMatrix_mult_spmat_'List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''_List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real''''_List_list_'_mult__'nat'_'List_list_'_mult__'nat'_'RealDef_real'''''
val simp_sorted_sparse_matrix = simp_SparseMatrix_sorted_sparse_matrix
val simp_sorted_spvec = simp_SparseMatrix_sorted_spvec
	   
fun single_arg simp ct = snd (simp (snd (Thm.dest_comb ct)))

fun double_arg simp ct =  
	let
	    val (a, y) = Thm.dest_comb ct
	    val (_, x) = Thm.dest_comb a
	in
	    snd (simp x y)
	end      

fun spmc ct =
    (case term_of ct of	 
	 ((Const ("SparseMatrix.le_spmat", _)) $ _) =>
	 single_arg simp_le_spmat ct
       | ((Const ("SparseMatrix.add_spmat", _)) $ _) =>
	 single_arg simp_add_spmat ct
       | ((Const ("SparseMatrix.diff_spmat", _)) $ _ $ _) =>
	 double_arg simp_diff_spmat ct
       | ((Const ("SparseMatrix.abs_spmat", _)) $ _) =>
	 single_arg simp_abs_spmat ct
       | ((Const ("SparseMatrix.mult_spmat", _)) $ _ $ _) =>
	 double_arg simp_mult_spmat ct
       | ((Const ("SparseMatrix.sorted_sparse_matrix", _)) $ _) =>
	 single_arg simp_sorted_sparse_matrix ct
       | ((Const ("SparseMatrix.sorted_spvec", ty)) $ _) =>
	 single_arg simp_sorted_spvec ct 
      | _ => raise Fail_conv)

fun lp_dual_estimate lptfile prec =
    let
	val th = inst_real (thm "SparseMatrix.spm_linprog_dual_estimate_1")
	val sg = sign_of (theory "MatrixLP")
	val (y, (A1, A2), (c1, c2), b, r) = 
	    let
		open fspmlp
		val l = load lptfile prec false
	    in
		(y l, A l, c l, b l, r l)
	    end		
	fun var s x = (cterm_of sg (Var ((s,0), FloatSparseMatrixBuilder.real_spmatT)), x)
	val th = Thm.instantiate ([], [var "A1" A1, var "A2" A2, var "y" y, var "c1" c1, var "c2" c2, var "r" r, var "b" b]) th
    in
	th
    end

fun simplify th = 
    let
	val simp_th = botc spmc (cprop_of th)
	val th = strip_shyps (equal_elim simp_th th)
	fun removeTrue th = removeTrue (implies_elim th TrueI) handle _ => th
    in
	removeTrue th
    end

fun float2real (x,y) = (Real.fromInt x) * (Math.pow (2.0, Real.fromInt y))

end

val result = ref ([]:thm list)

fun run c = timeit (fn () => (result := [MatrixLP.simplify c]; ()))

