signature FSPMLP = 
sig
    type linprog

    val y : linprog -> cterm
    val A : linprog -> cterm * cterm
    val b : linprog -> cterm
    val c : linprog -> cterm * cterm
    val r : linprog -> cterm

    exception Load of string
		       
    val load : string -> int -> bool -> linprog
end

structure fspmlp : FSPMLP = 
struct

type linprog = cterm * (cterm * cterm) * cterm * (cterm * cterm) * cterm 

fun y (c1, c2, c3, c4, c5) = c1
fun A (c1, c2, c3, c4, c5) = c2
fun b (c1, c2, c3, c4, c5) = c3
fun c (c1, c2, c3, c4, c5) = c4
fun r (c1, c2, c3, c4, c5) = c5

structure CplexFloatSparseMatrixConverter = 
MAKE_CPLEX_MATRIX_CONVERTER(structure cplex = Cplex and matrix_builder = FloatSparseMatrixBuilder);

datatype bound_type = LOWER | UPPER

fun intbound_ord ((i1, b1),(i2,b2)) = 
    if i1 < i2 then LESS
    else if i1 = i2 then 
	(if b1 = b2 then EQUAL else if b1=LOWER then LESS else GREATER)
    else GREATER

structure Inttab = TableFun(type key = int val ord = (rev_order o int_ord));

structure VarGraph = TableFun(type key = int*bound_type val ord = intbound_ord);
(* key -> (float option) * (int -> (float * (((float * float) * key) list)))) *)
(* dest_key -> (sure_bound * (row_index -> (row_bound * (((coeff_lower * coeff_upper) * src_key) list)))) *)

exception Internal of string;

fun add_row_bound g dest_key row_index row_bound = 
    let 
	val x = 
	    case VarGraph.lookup (g, dest_key) of
		NONE => (NONE, Inttab.update ((row_index, (row_bound, [])), Inttab.empty))
	      | SOME (sure_bound, f) =>
		(sure_bound,
		 case Inttab.lookup (f, row_index) of
		     NONE => Inttab.update ((row_index, (row_bound, [])), f)
		   | SOME _ => raise (Internal "add_row_bound"))				     
    in
	VarGraph.update ((dest_key, x), g)
    end    

fun update_sure_bound g (key as (_, btype)) bound = 
    let
	val x = 
	    case VarGraph.lookup (g, key) of
		NONE => (SOME bound, Inttab.empty)
	      | SOME (NONE, f) => (SOME bound, f)
	      | SOME (SOME old_bound, f) => 
		(SOME ((case btype of 
			    UPPER => FloatArith.min 
			  | LOWER => FloatArith.max) 
			   old_bound bound), f)
    in
	VarGraph.update ((key, x), g)
    end

fun get_sure_bound g key = 
    case VarGraph.lookup (g, key) of 
	NONE => NONE
      | SOME (sure_bound, _) => sure_bound

(*fun get_row_bound g key row_index = 
    case VarGraph.lookup (g, key) of
	NONE => NONE
      | SOME (sure_bound, f) =>
	(case Inttab.lookup (f, row_index) of 
	     NONE => NONE
	   | SOME (row_bound, _) => (sure_bound, row_bound))*)
    
fun add_edge g src_key dest_key row_index coeff = 
    case VarGraph.lookup (g, dest_key) of
	NONE => raise (Internal "add_edge: dest_key not found")
      | SOME (sure_bound, f) =>
	(case Inttab.lookup (f, row_index) of
	     NONE => raise (Internal "add_edge: row_index not found")
	   | SOME (row_bound, sources) => 
	     VarGraph.update ((dest_key, (sure_bound, Inttab.update ((row_index, (row_bound, (coeff, src_key) :: sources)), f))), g))

fun split_graph g = 
    let
	fun split ((r1, r2), (key, (sure_bound, _))) = 
	    case sure_bound of
		NONE => (r1, r2)
	      | SOME bound => 
		(case key of
		     (u, UPPER) => (r1, Inttab.update ((u, bound), r2))
		   | (u, LOWER) => (Inttab.update ((u, bound), r1), r2))
    in
	VarGraph.foldl split ((Inttab.empty, Inttab.empty), g)
    end

fun it2list t = 
    let
	fun tolist (l, a) = a::l
    in
	Inttab.foldl tolist ([], t)
    end

(* If safe is true, termination is guaranteed, but the sure bounds may be not optimal (relative to the algorithm).
   If safe is false, termination is not guaranteed, but on termination the sure bounds are optimal (relative to the algorithm) *)
fun propagate_sure_bounds safe names g = 
    let		 	    	
	(* returns NONE if no new sure bound could be calculated, otherwise the new sure bound is returned *)
	fun calc_sure_bound_from_sources g (key as (_, btype)) = 
	    let		
		fun mult_upper x (lower, upper) = 
		    if FloatArith.is_negative x then
			FloatArith.mul x lower
		    else
			FloatArith.mul x upper
			
		fun mult_lower x (lower, upper) = 
		    if FloatArith.is_negative x then
			FloatArith.mul x upper
		    else
			FloatArith.mul x lower

		val mult_btype = case btype of UPPER => mult_upper | LOWER => mult_lower

		fun calc_sure_bound (sure_bound, (row_index, (row_bound, sources))) = 
		    let
			fun add_src_bound (sum, (coeff, src_key)) = 
			    case sum of 
				NONE => NONE
			      | SOME x => 
				(case get_sure_bound g src_key of
				     NONE => NONE
				   | SOME src_sure_bound => SOME (FloatArith.add x (mult_btype src_sure_bound coeff)))
		    in
			case foldl add_src_bound (SOME row_bound, sources) of
			    NONE => sure_bound
			  | new_sure_bound as (SOME new_bound) => 
			    (case sure_bound of 
				 NONE => new_sure_bound
			       | SOME old_bound => 
				 SOME (case btype of 
					   UPPER => FloatArith.min old_bound new_bound
					 | LOWER => FloatArith.max old_bound new_bound))				 
		    end		
	    in
		case VarGraph.lookup (g, key) of
		    NONE => NONE
		  | SOME (sure_bound, f) =>
		    let
			val x = Inttab.foldl calc_sure_bound (sure_bound, f) 
		    in
			if x = sure_bound then NONE else x
		    end		
    	    end

	fun propagate ((g, b), (key, _)) = 
	    case calc_sure_bound_from_sources g key of 
		NONE => (g,b)
	      | SOME bound => (update_sure_bound g key bound, 
			       if safe then 
				   case get_sure_bound g key of
				       NONE => true
				     | _ => b
			       else
				   true)

	val (g, b) = VarGraph.foldl propagate ((g, false), g) 
    in
	if b then propagate_sure_bounds safe names g else g	
    end	    
    		
exception Load of string;

fun calcr safe_propagation xlen names prec A b = 
    let
	val empty = Inttab.empty

	fun instab t i x = Inttab.update ((i,x), t)

	fun isnegstr x = String.isPrefix "-" x
	fun negstr x = if isnegstr x then String.extract (x, 1, NONE) else "-"^x

	fun test_1 (lower, upper) = 
	    if lower = upper then
		(if FloatArith.is_equal lower (IntInf.fromInt ~1, FloatArith.izero) then ~1 
		 else if FloatArith.is_equal lower (IntInf.fromInt 1, FloatArith.izero) then 1
		 else 0)
	    else 0	

	fun calcr (g, (row_index, a)) = 
	    let				
		val b =  FloatSparseMatrixBuilder.v_elem_at b row_index
		val (_, b2) = ExactFloatingPoint.approx_decstr_by_bin prec (case b of NONE => "0" | SOME b => b)
		val approx_a = FloatSparseMatrixBuilder.v_fold (fn (l, (i,s)) => 
								   (i, ExactFloatingPoint.approx_decstr_by_bin prec s)::l) [] a
			       
		fun fold_dest_nodes (g, (dest_index, dest_value)) = 
		    let		
			val dest_test = test_1 dest_value
		    in
			if dest_test = 0 then
			    g
			else let
				val (dest_key as (_, dest_btype), row_bound) = 
				    if dest_test = ~1 then 
					((dest_index, LOWER), FloatArith.neg b2)
				    else
					((dest_index, UPPER), b2)
					
				fun fold_src_nodes (g, (src_index, src_value as (src_lower, src_upper))) = 
				    if src_index = dest_index then g
				    else
					let
					    val coeff = case dest_btype of 
							    UPPER => (FloatArith.neg src_upper, FloatArith.neg src_lower)
							  | LOWER => src_value
					in
					    if FloatArith.is_negative src_lower then
						add_edge g (src_index, UPPER) dest_key row_index coeff
					    else
						add_edge g (src_index, LOWER) dest_key row_index coeff
					end
			    in	    
				foldl fold_src_nodes ((add_row_bound g dest_key row_index row_bound), approx_a)
			    end
		    end
	    in
		case approx_a of
		    [] => g
		  | [(u, a)] => 
		    let
			val atest = test_1 a
		    in
			if atest = ~1 then 			  
			    update_sure_bound g (u, LOWER) (FloatArith.neg b2)
			else if atest = 1 then
			    update_sure_bound g (u, UPPER) b2
			else
			    g
		    end
		  | _ => foldl fold_dest_nodes (g, approx_a)
	    end
	
	val g = FloatSparseMatrixBuilder.m_fold calcr VarGraph.empty A
	val g = propagate_sure_bounds safe_propagation names g

	val (r1, r2) = split_graph g
	
	fun abs_estimate i r1 r2 = 
	    if i = 0 then FloatSparseMatrixBuilder.empty_spmat
	    else
		let
		    val index = xlen-i
		    val r = abs_estimate (i-1) r1 r2 
		    val b1 = case Inttab.lookup (r1, index) of NONE => raise (Load ("x-value not bounded from below: "^(names index))) | SOME x => x
		    val b2 = case Inttab.lookup (r2, index) of NONE => raise (Load ("x-value not bounded from above: "^(names index))) | SOME x => x
		    val abs_max = FloatArith.max (FloatArith.neg (FloatArith.negative_part b1)) (FloatArith.positive_part b2)    
		    val vec = FloatSparseMatrixBuilder.cons_spvec (FloatSparseMatrixBuilder.mk_spvec_entry 0 abs_max) FloatSparseMatrixBuilder.empty_spvec
		in
		    FloatSparseMatrixBuilder.cons_spmat (FloatSparseMatrixBuilder.mk_spmat_entry index vec) r
		end		    		    
    in
	FloatSparseMatrixBuilder.sign_term (abs_estimate xlen r1 r2)
    end
	    
fun load filename prec safe_propagation =
    let
	val prog = Cplex.load_cplexFile filename
	val prog = Cplex.elim_nonfree_bounds prog
	val prog = Cplex.relax_strict_ineqs prog
	val (maximize, c, A, b, (xlen, names, _)) = CplexFloatSparseMatrixConverter.convert_prog prog
	val r = calcr safe_propagation xlen names prec A b
	val _ = if maximize then () else raise Load "sorry, cannot handle minimization problems"			
	val (dualprog, indexof) = FloatSparseMatrixBuilder.dual_cplexProg c A b
	val results = Cplex.solve dualprog
	val (optimal,v) = CplexFloatSparseMatrixConverter.convert_results results indexof
	val A = FloatSparseMatrixBuilder.cut_matrix v NONE A
	fun id x = x
	val v = FloatSparseMatrixBuilder.set_vector FloatSparseMatrixBuilder.empty_matrix 0 v
	val b = FloatSparseMatrixBuilder.transpose_matrix (FloatSparseMatrixBuilder.set_vector FloatSparseMatrixBuilder.empty_matrix 0 b)
	val c = FloatSparseMatrixBuilder.set_vector FloatSparseMatrixBuilder.empty_matrix 0 c
	val (y1, _) = FloatSparseMatrixBuilder.approx_matrix prec FloatArith.positive_part v
	val A = FloatSparseMatrixBuilder.approx_matrix prec id A
	val (_,b2) = FloatSparseMatrixBuilder.approx_matrix prec id b
	val c = FloatSparseMatrixBuilder.approx_matrix prec id c
    in
	(y1, A, b2, c, r)
    end handle CplexFloatSparseMatrixConverter.Converter s => (raise (Load ("Converter: "^s)))

end