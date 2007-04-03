(*  Title:      HOL/Matrix/cplex/FloatSparseMatrixBuilder.ML
    ID:         $Id$
    Author:     Steven Obua
*)

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
    val v_fold : (int * string -> 'a -> 'a) -> vector -> 'a -> 'a
    val m_fold : (int * vector -> 'a -> 'a) -> matrix -> 'a -> 'a

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

val th = theory "FloatSparseMatrix"
	 
fun readtype s = Sign.intern_type th s
fun readterm s = Sign.intern_const th s
		 
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

val float_const = Float.float_const

val zero = IntInf.fromInt 0
val minus_one = IntInf.fromInt ~1
val two = IntInf.fromInt 2

val mk_intinf = Float.mk_intinf

val mk_float  = Float.mk_float 

fun float2cterm (a,b) = cterm_of th (mk_float (a,b))

fun approx_value_term prec f = Float.approx_float prec (fn (x, y) => (f x, f y))

fun approx_value prec pprt value = 
  let
    val (flower, fupper) = approx_value_term prec pprt value
  in
    (cterm_of th flower, cterm_of th fupper)
  end

fun sign_term t = cterm_of th t

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
	fun app (index, s) (vlower, vupper) = 
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
	Inttab.fold app vector (empty_vector_const, empty_vector_const)
    end

fun approx_matrix_term prec pprt matrix =
  let
    fun app (index, vector) (mlower, mupper) =
      let
        val (vlower, vupper) = approx_vector_term prec pprt vector  
        val index = mk_intinf HOLogic.natT (IntInf.fromInt index)
        val elower = HOLogic.mk_prod (index, vlower)
        val eupper = HOLogic.mk_prod (index, vupper)
      in
        (Cons_spmat_const $ elower $ mlower, Cons_spmat_const $ eupper $ mupper)
      end
    val (mlower, mupper) = Inttab.fold app matrix (empty_matrix_const, empty_matrix_const)
  in Inttab.fold app matrix (empty_matrix_const, empty_matrix_const) end;

fun approx_vector prec pprt vector =
    let
	val (l, u) = approx_vector_term prec pprt vector
    in
	(cterm_of th l, cterm_of th u)
    end

fun approx_matrix prec pprt matrix = 
    let
	val (l, u) = approx_matrix_term prec pprt matrix
    in
	(cterm_of th l, cterm_of th u)
    end


exception Nat_expected of int;

val zero_interval = approx_value_term 1 I "0"

fun set_elem vector index str = 
    if index < 0 then 
	raise (Nat_expected index)
    else if (approx_value_term 1 I str) = zero_interval then 
	vector
    else  
	Inttab.update (index, str) vector

fun set_vector matrix index vector = 
    if index < 0 then
	raise (Nat_expected index)
    else if Inttab.is_empty vector then
	matrix
    else
	Inttab.update (index, vector) matrix

val empty_matrix = Inttab.empty
val empty_vector = Inttab.empty

(* dual stuff *)

structure cplex = Cplex

fun transpose_matrix matrix = 
  let
    fun upd j (i, s) =
      Inttab.map_default (i, Inttab.empty) (Inttab.update (j, s));
    fun updm (j, v) = Inttab.fold (upd j) v;
  in Inttab.fold updm matrix empty_matrix end;

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
		val _ = change ytable (Inttab.update (i, s))
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
	    cplex.cplexSum (Inttab.fold (fn (index, s) => fn list => (mk_term index s) :: list) vector [])
		       		       
	fun mk_constr index vector c = 
	    let 
		val s = case Inttab.lookup c index of SOME s => s | NONE => "0"
		val (p, s) = split_numstr s
		val num = if p then cplex.cplexNum s else cplex.cplexNeg (cplex.cplexNum s)
	    in
		(NONE, cplex.cplexConstr (cplex.cplexLeq, (vec2sum vector, num)))
	    end

	fun delete index c = Inttab.delete index c handle Inttab.UNDEF _ => c

	val (list, b) = Inttab.fold
			    (fn (index, v) => fn (list, c) => ((mk_constr index v c)::list, delete index c))
			    A ([], b)
	val _ = if Inttab.is_empty b then () else raise Superfluous_constr_right_hand_sides

	fun mk_free y = cplex.cplexBounds (cplex.cplexNeg cplex.cplexInf, cplex.cplexLeq, 
					   cplex.cplexVar y, cplex.cplexLeq,
					   cplex.cplexInf)

	val yvars = Inttab.fold (fn (i, y) => fn l => (mk_free y)::l) (!ytable) []

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
	    cplex.cplexSum (Inttab.fold (fn (index, s) => fn list => (mk_term index s)::list) vector [])
		       		       
	fun mk_constr index vector c = 
	    let 
		val s = case Inttab.lookup c index of SOME s => s | NONE => "0"
		val (p, s) = split_numstr s
		val num = if p then cplex.cplexNum s else cplex.cplexNeg (cplex.cplexNum s)
	    in
		(NONE, cplex.cplexConstr (cplex.cplexEq, (vec2sum vector, num)))
	    end

	fun delete index c = Inttab.delete index c handle Inttab.UNDEF _ => c

	val (list, c) = Inttab.fold 
			    (fn (index, v) => fn (list, c) => ((mk_constr index v c)::list, delete index c))
			    (transpose_matrix A) ([], c)
	val _ = if Inttab.is_empty c then () else raise Superfluous_constr_right_hand_sides

	val prog = cplex.cplexProg ("dual", cplex.cplexMinimize (vec2sum b), list, [])
    in
	(prog, indexof)
    end

fun cut_vector size v = 
  let
    val count = ref 0;
    fun app (i, s) =  if (!count < size) then
        (count := !count +1 ; Inttab.update (i, s))
      else I
  in
    Inttab.fold app v empty_vector
  end

fun cut_matrix vfilter vsize m = 
  let
    fun app (i, v) = 
      if is_none (Inttab.lookup vfilter i) then I
      else case vsize
       of NONE => Inttab.update (i, v)
        | SOME s => Inttab.update (i, cut_vector s v)
  in Inttab.fold app m empty_matrix end

fun v_elem_at v i = Inttab.lookup v i
fun m_elem_at m i = Inttab.lookup m i

fun v_only_elem v = 
    case Inttab.min_key v of
	NONE => NONE
      | SOME vmin => (case Inttab.max_key v of
			  NONE => SOME vmin
			| SOME vmax => if vmin = vmax then SOME vmin else NONE)

fun v_fold f = Inttab.fold f;
fun m_fold f = Inttab.fold f;

end;
