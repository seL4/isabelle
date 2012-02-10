(*  Title:      HOL/Matrix/FloatSparseMatrixBuilder.ML
    Author:     Steven Obua
*)

signature FLOAT_SPARSE_MATIRX_BUILDER =
sig
  include MATRIX_BUILDER

  structure cplex : CPLEX

  type float = Float.float
  val approx_value : int -> (float -> float) -> string -> term * term
  val approx_vector : int -> (float -> float) -> vector -> term * term
  val approx_matrix : int -> (float -> float) -> matrix -> term * term

  val mk_spvec_entry : int -> float -> term
  val mk_spvec_entry' : int -> term -> term
  val mk_spmat_entry : int -> term -> term
  val spvecT: typ
  val spmatT: typ
  
  val v_elem_at : vector -> int -> string option
  val m_elem_at : matrix -> int -> vector option
  val v_only_elem : vector -> int option
  val v_fold : (int * string -> 'a -> 'a) -> vector -> 'a -> 'a
  val m_fold : (int * vector -> 'a -> 'a) -> matrix -> 'a -> 'a

  val transpose_matrix : matrix -> matrix

  val cut_vector : int -> vector -> vector
  val cut_matrix : vector -> int option -> matrix -> matrix

  val delete_matrix : int list -> matrix -> matrix
  val cut_matrix' : int list -> matrix -> matrix 
  val delete_vector : int list -> vector -> vector
  val cut_vector' : int list -> vector -> vector

  val indices_of_matrix : matrix -> int list
  val indices_of_vector : vector -> int list

  (* cplexProg c A b *)
  val cplexProg : vector -> matrix -> vector -> cplex.cplexProg * (string -> int)
  (* dual_cplexProg c A b *)
  val dual_cplexProg : vector -> matrix -> vector -> cplex.cplexProg * (string -> int)
end;

structure FloatSparseMatrixBuilder : FLOAT_SPARSE_MATIRX_BUILDER =
struct

type float = Float.float
structure Inttab = Table(type key = int val ord = rev_order o int_ord);

type vector = string Inttab.table
type matrix = vector Inttab.table

val spvec_elemT = HOLogic.mk_prodT (HOLogic.natT, HOLogic.realT);
val spvecT = HOLogic.listT spvec_elemT;
val spmat_elemT = HOLogic.mk_prodT (HOLogic.natT, spvecT);
val spmatT = HOLogic.listT spmat_elemT;

fun approx_value prec f =
  FloatArith.approx_float prec (fn (x, y) => (f x, f y));

fun mk_spvec_entry i f =
  HOLogic.mk_prod (HOLogic.mk_number HOLogic.natT i, FloatArith.mk_float f);

fun mk_spvec_entry' i x =
  HOLogic.mk_prod (HOLogic.mk_number HOLogic.natT i, x);

fun mk_spmat_entry i e =
  HOLogic.mk_prod (HOLogic.mk_number HOLogic.natT i, e);

fun approx_vector prec pprt vector =
  let
    fun app (index, s) (lower, upper) =
      let
        val (flower, fupper) = approx_value prec pprt s
        val index = HOLogic.mk_number HOLogic.natT index
        val elower = HOLogic.mk_prod (index, flower)
        val eupper = HOLogic.mk_prod (index, fupper)
      in (elower :: lower, eupper :: upper) end;
  in
    pairself (HOLogic.mk_list spvec_elemT) (Inttab.fold app vector ([], []))
  end;

fun approx_matrix prec pprt vector =
  let
    fun app (index, v) (lower, upper) =
      let
        val (flower, fupper) = approx_vector prec pprt v
        val index = HOLogic.mk_number HOLogic.natT index
        val elower = HOLogic.mk_prod (index, flower)
        val eupper = HOLogic.mk_prod (index, fupper)
      in (elower :: lower, eupper :: upper) end;
  in
    pairself (HOLogic.mk_list spmat_elemT) (Inttab.fold app vector ([], []))
  end;

exception Nat_expected of int;

val zero_interval = approx_value 1 I "0"

fun set_elem vector index str =
    if index < 0 then
        raise (Nat_expected index)
    else if (approx_value 1 I str) = zero_interval then
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
        val ytable = Unsynchronized.ref Inttab.empty
        fun indexof s =
            if String.size s = 0 then raise (No_name s)
            else case Int.fromString (String.extract(s, 1, NONE)) of
                     SOME i => i | NONE => raise (No_name s)

        fun nameof i =
            let
                val s = "x" ^ string_of_int i
                val _ = Unsynchronized.change ytable (Inttab.update (i, s))
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

        val yvars = Inttab.fold (fn (_, y) => fn l => (mk_free y)::l) (!ytable) []

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

        fun nameof i = "y" ^ string_of_int i

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
    val count = Unsynchronized.ref 0;
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

fun indices_of_vector v = Inttab.keys v
fun indices_of_matrix m = Inttab.keys m
fun delete_vector indices v = fold Inttab.delete indices v
fun delete_matrix indices m = fold Inttab.delete indices m
fun cut_matrix' indices _ = fold (fn i => fn m => (case Inttab.lookup m i of NONE => m | SOME v => Inttab.update (i, v) m)) indices Inttab.empty
fun cut_vector' indices _ = fold (fn i => fn v => (case Inttab.lookup v i of NONE => v | SOME x => Inttab.update (i, x) v)) indices Inttab.empty



end;
