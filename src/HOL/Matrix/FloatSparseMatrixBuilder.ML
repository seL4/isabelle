structure FloatSparseMatrixBuilder :
sig
    include MATRIX_BUILDER

    structure cplex : CPLEX

    type float = IntInf.int*IntInf.int
    type floatfunc = float -> float


    val float2cterm : IntInf.int * IntInf.int -> cterm
       
    val approx_value : int -> floatfunc -> string -> cterm * cterm
    val approx_vector : int -> floatfunc -> vector -> cterm * cterm
    val approx_matrix : int -> floatfunc -> matrix -> cterm * cterm

    val mk_spvec_entry : int -> float -> term
    val empty_spvec : term
    val cons_spvec : term -> term -> term
    val empty_spmat : term
    val mk_spmat_entry : int -> term -> term
    val cons_spmat : term -> term -> term
    val sign_term : term -> cterm

    val v_elem_at : vector -> int -> string option
    val m_elem_at : matrix -> int -> vector option
    val v_only_elem : vector -> int option
    val v_fold : ('a * (int * string) -> 'a) -> 'a -> vector -> 'a
    val m_fold : ('a * (int * vector) -> 'a) -> 'a -> matrix -> 'a
				   
    val transpose_matrix : matrix -> matrix

    val cut_vector : int -> vector -> vector
    val cut_matrix : vector -> (int option) -> matrix -> matrix
    
    (* cplexProg c A b *)
    val cplexProg : vector -> matrix -> vector -> (cplex.cplexProg * (string -> int))
    (* dual_cplexProg c A b *)
    val dual_cplexProg : vector -> matrix -> vector -> (cplex.cplexProg * (string -> int))

    val real_spmatT : typ
    val real_spvecT : typ
end 
= 
struct


structure Inttab = TableFun(type key = int val ord = (rev_order o int_ord));

type vector = string Inttab.table
type matrix = vector Inttab.table
type float = IntInf.int*IntInf.int
type floatfunc = float -> float

val th = theory "Float"
val sg = sign_of th
	 
fun readtype s = Sign.intern_tycon sg s
fun readterm s = Sign.intern_const sg s
		 
val ty_list = readtype "list"
val term_Nil = readterm "Nil"
val term_Cons = readterm "Cons"
		
val spvec_elemT = HOLogic.mk_prodT (HOLogic.natT, HOLogic.realT)
val spvecT = Type (ty_list, [spvec_elemT])
val spmat_elemT = HOLogic.mk_prodT (HOLogic.natT, spvecT)
val spmatT = Type (ty_list, [spmat_elemT])

val real_spmatT = spmatT
val real_spvecT = spvecT

val empty_matrix_const = Const (term_Nil, spmatT)
val empty_vector_const = Const (term_Nil, spvecT)

val Cons_spvec_const = Const (term_Cons, spvec_elemT --> spvecT --> spvecT)
val Cons_spmat_const = Const (term_Cons, spmat_elemT --> spmatT --> spmatT) 
			 
val float_const = Const (readterm "float", HOLogic.mk_prodT (HOLogic.intT, HOLogic.intT) --> HOLogic.realT)
		  
val zero = IntInf.fromInt 0
val minus_one = IntInf.fromInt ~1
val two = IntInf.fromInt 2
	  
fun mk_intinf ty n =
    let
	fun mk_bit n = if n = zero then HOLogic.false_const else HOLogic.true_const
								 
	fun bin_of n = 
	    if n = zero then HOLogic.pls_const
	    else if n = minus_one then HOLogic.min_const
	    else 
		let 
		    (*val (q,r) = IntInf.divMod (n, two): doesn't work in SML 10.0.7, but in newer versions!!!*)
	            val q = IntInf.div (n, two)
		    val r = IntInf.mod (n, two)
		in
		    HOLogic.bit_const $ bin_of q $ mk_bit r
		end
    in 
	HOLogic.number_of_const ty $ (bin_of n)
    end

fun mk_float (a,b) = 
    float_const $ (HOLogic.mk_prod ((mk_intinf HOLogic.intT a), (mk_intinf HOLogic.intT b)))

fun float2cterm (a,b) = cterm_of sg (mk_float (a,b))

fun approx_value_term prec f value = 
    let
	val (flower, fupper) = ExactFloatingPoint.approx_decstr_by_bin prec value
	val (flower, fupper) = (f flower, f fupper)
    in
	(mk_float flower, mk_float fupper)
    end

fun approx_value prec pprt value = 
    let
	val (flower, fupper) = approx_value_term prec pprt value			       
    in
	(cterm_of sg flower, cterm_of sg fupper)
    end

fun sign_term t = cterm_of sg t

val empty_spvec = empty_vector_const

val empty_spmat = empty_matrix_const

fun mk_spvec_entry i f = 
    let
	val term_i = mk_intinf HOLogic.natT (IntInf.fromInt i)
	val term_f = mk_float f
    in 
	HOLogic.mk_prod (term_i, term_f)
    end

fun mk_spmat_entry i e = 
    let
	val term_i = mk_intinf HOLogic.natT (IntInf.fromInt i)
    in
	HOLogic.mk_prod (term_i, e)
    end

fun cons_spvec h t = Cons_spvec_const $ h $ t

fun cons_spmat h t = Cons_spmat_const $ h $ t 

fun approx_vector_term prec pprt vector = 
    let 	 
	fun app ((vlower, vupper), (index, s)) = 
	    let
		val (flower, fupper) = approx_value_term prec pprt s
		val index = mk_intinf HOLogic.natT (IntInf.fromInt index)
		val elower = HOLogic.mk_prod (index, flower)
		val eupper = HOLogic.mk_prod (index, fupper)
	    in
		(Cons_spvec_const $ elower $ vlower,
		 Cons_spvec_const $ eupper $ vupper)	
	    end
    in
	Inttab.foldl app ((empty_vector_const, empty_vector_const), vector)	
    end

fun approx_matrix_term prec pprt matrix =
    let 	 
	fun app ((mlower, mupper), (index, vector)) = 
	    let
		val (vlower, vupper) = approx_vector_term prec pprt vector  
		val index = mk_intinf HOLogic.natT (IntInf.fromInt index)
		val elower = HOLogic.mk_prod (index, vlower)
		val eupper = HOLogic.mk_prod (index, vupper)
	    in
		(Cons_spmat_const $ elower $ mlower,
		 Cons_spmat_const $ eupper $ mupper)		
	    end
		
	val (mlower, mupper) = Inttab.foldl app ((empty_matrix_const, empty_matrix_const), matrix)
    in
	Inttab.foldl app ((empty_matrix_const, empty_matrix_const), matrix)	
    end

fun approx_vector prec pprt vector =
    let
	val (l, u) = approx_vector_term prec pprt vector
    in
	(cterm_of sg l, cterm_of sg u)
    end

fun approx_matrix prec pprt matrix = 
    let
	val (l, u) = approx_matrix_term prec pprt matrix
    in
	(cterm_of sg l, cterm_of sg u)
    end


exception Nat_expected of int;

val zero_interval = approx_value_term 1 I "0"

fun set_elem vector index str = 
    if index < 0 then 
	raise (Nat_expected index)
    else if (approx_value_term 1 I str) = zero_interval then 
	vector
    else  
	Inttab.update ((index, str), vector)

fun set_vector matrix index vector = 
    if index < 0 then
	raise (Nat_expected index)
    else if Inttab.is_empty vector then
	matrix
    else
	Inttab.update ((index, vector), matrix)

val empty_matrix = Inttab.empty
val empty_vector = Inttab.empty

(* dual stuff *)

structure cplex = Cplex

fun transpose_matrix matrix = 
    let
	fun upd m j i x =
	    case Inttab.lookup (m, j) of
		SOME v => Inttab.update ((j, Inttab.update ((i, x), v)), m)
	      | NONE => Inttab.update ((j, Inttab.update ((i, x), Inttab.empty)), m) 

	fun updv j (m, (i, s)) = upd m i j s

	fun updm (m, (j, v)) = Inttab.foldl (updv j) (m, v)
    in
	Inttab.foldl updm (empty_matrix, matrix)
    end

exception No_name of string;

exception Superfluous_constr_right_hand_sides

fun cplexProg c A b = 
    let
	val ytable = ref Inttab.empty
	fun indexof s = 
	    if String.size s = 0 then raise (No_name s)
	    else case Int.fromString (String.extract(s, 1, NONE)) of 
		     SOME i => i | NONE => raise (No_name s)
				     
	fun nameof i = 
	    let 
		val s = "x"^(Int.toString i)
		val _ = ytable := (Inttab.update ((i, s), !ytable))
	    in
		s
	    end
	    
	fun split_numstr s = 
	    if String.isPrefix "-" s then (false,String.extract(s, 1, NONE))
	    else if String.isPrefix "+" s then (true, String.extract(s, 1, NONE))
	    else (true, s)

	fun mk_term index s =
	    let 
		val (p, s) = split_numstr s
		val prod = cplex.cplexProd (cplex.cplexNum s, cplex.cplexVar (nameof index))
	    in
		if p then prod else cplex.cplexNeg prod
	    end

	fun vec2sum vector =
	    cplex.cplexSum (Inttab.foldl (fn (list, (index, s)) => (mk_term index s)::list) ([], vector))
		       		       
	fun mk_constr index vector c = 
	    let 
		val s = case Inttab.lookup (c, index) of SOME s => s | NONE => "0"
		val (p, s) = split_numstr s
		val num = if p then cplex.cplexNum s else cplex.cplexNeg (cplex.cplexNum s)
	    in
		(NONE, cplex.cplexConstr (cplex.cplexLeq, (vec2sum vector, num)))
	    end

	fun delete index c = Inttab.delete index c handle Inttab.UNDEF _ => c

	val (list, b) = Inttab.foldl 
			    (fn ((list, c), (index, v)) => ((mk_constr index v c)::list, delete index c))
			    (([], b), A)
	val _ = if Inttab.is_empty b then () else raise Superfluous_constr_right_hand_sides

	fun mk_free y = cplex.cplexBounds (cplex.cplexNeg cplex.cplexInf, cplex.cplexLeq, 
					   cplex.cplexVar y, cplex.cplexLeq,
					   cplex.cplexInf)

	val yvars = Inttab.foldl (fn (l, (i, y)) => (mk_free y)::l) ([], !ytable)

	val prog = cplex.cplexProg ("original", cplex.cplexMaximize (vec2sum c), list, yvars)
    in
	(prog, indexof)
    end


fun dual_cplexProg c A b = 
    let
	fun indexof s = 
	    if String.size s = 0 then raise (No_name s)
	    else case Int.fromString (String.extract(s, 1, NONE)) of 
		     SOME i => i | NONE => raise (No_name s)
				     
	fun nameof i = "y"^(Int.toString i)
	    
	fun split_numstr s = 
	    if String.isPrefix "-" s then (false,String.extract(s, 1, NONE))
	    else if String.isPrefix "+" s then (true, String.extract(s, 1, NONE))
	    else (true, s)

	fun mk_term index s =
	    let 
		val (p, s) = split_numstr s
		val prod = cplex.cplexProd (cplex.cplexNum s, cplex.cplexVar (nameof index))
	    in
		if p then prod else cplex.cplexNeg prod
	    end

	fun vec2sum vector =
	    cplex.cplexSum (Inttab.foldl (fn (list, (index, s)) => (mk_term index s)::list) ([], vector))
		       		       
	fun mk_constr index vector c = 
	    let 
		val s = case Inttab.lookup (c, index) of SOME s => s | NONE => "0"
		val (p, s) = split_numstr s
		val num = if p then cplex.cplexNum s else cplex.cplexNeg (cplex.cplexNum s)
	    in
		(NONE, cplex.cplexConstr (cplex.cplexEq, (vec2sum vector, num)))
	    end

	fun delete index c = Inttab.delete index c handle Inttab.UNDEF _ => c

	val (list, c) = Inttab.foldl 
			    (fn ((list, c), (index, v)) => ((mk_constr index v c)::list, delete index c))
			    (([], c), transpose_matrix A)
	val _ = if Inttab.is_empty c then () else raise Superfluous_constr_right_hand_sides

	val prog = cplex.cplexProg ("dual", cplex.cplexMinimize (vec2sum b), list, [])
    in
	(prog, indexof)
    end

fun cut_vector size v = 
    let
	val count = ref 0 
	fun app (v, (i, s)) = 
	    if (!count < size) then
		(count := !count +1 ; Inttab.update ((i,s),v))
	    else
		v
    in
	Inttab.foldl app (empty_vector, v)
    end

fun cut_matrix vfilter vsize m = 
    let 
	fun app (m, (i, v)) = 
	    if (Inttab.lookup (vfilter, i) = NONE) then 
		m 
	    else 
		case vsize of
		    NONE => Inttab.update ((i,v), m)
		  | SOME s => Inttab.update((i, cut_vector s v),m)
    in
	Inttab.foldl app (empty_matrix, m)
    end
		 
fun v_elem_at v i = Inttab.lookup (v,i)
fun m_elem_at m i = Inttab.lookup (m,i)

fun v_only_elem v = 
    case Inttab.min_key v of
	NONE => NONE
      | SOME vmin => (case Inttab.max_key v of
			  NONE => SOME vmin
			| SOME vmax => if vmin = vmax then SOME vmin else NONE)

fun v_fold f a v = Inttab.foldl f (a,v) 

fun m_fold f a m = Inttab.foldl f (a,m)

end;
