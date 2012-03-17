(*  Title:      HOL/Matrix/fspmlp.ML
    Author:     Steven Obua
*)

signature FSPMLP =
sig
    type linprog
    type vector = FloatSparseMatrixBuilder.vector
    type matrix = FloatSparseMatrixBuilder.matrix

    val y : linprog -> term
    val A : linprog -> term * term
    val b : linprog -> term
    val c : linprog -> term * term
    val r12 : linprog -> term * term

    exception Load of string

    val load : string -> int -> bool -> linprog
end

structure Fspmlp : FSPMLP =
struct

type vector = FloatSparseMatrixBuilder.vector
type matrix = FloatSparseMatrixBuilder.matrix

type linprog = term * (term * term) * term * (term * term) * (term * term)

fun y (c1, _, _, _, _) = c1
fun A (_, c2, _, _, _) = c2
fun b (_, _, c3, _, _) = c3
fun c (_, _, _, c4, _) = c4
fun r12 (_, _, _, _, c6) = c6

structure CplexFloatSparseMatrixConverter =
MAKE_CPLEX_MATRIX_CONVERTER(structure cplex = Cplex and matrix_builder = FloatSparseMatrixBuilder);

datatype bound_type = LOWER | UPPER

fun intbound_ord ((i1: int, b1),(i2,b2)) =
    if i1 < i2 then LESS
    else if i1 = i2 then
        (if b1 = b2 then EQUAL else if b1=LOWER then LESS else GREATER)
    else GREATER

structure Inttab = Table(type key = int val ord = (rev_order o int_ord));

structure VarGraph = Table(type key = int*bound_type val ord = intbound_ord);
(* key -> (float option) * (int -> (float * (((float * float) * key) list)))) *)
(* dest_key -> (sure_bound * (row_index -> (row_bound * (((coeff_lower * coeff_upper) * src_key) list)))) *)

exception Internal of string;

fun add_row_bound g dest_key row_index row_bound =
    let
        val x =
            case VarGraph.lookup g dest_key of
                NONE => (NONE, Inttab.update (row_index, (row_bound, [])) Inttab.empty)
              | SOME (sure_bound, f) =>
                (sure_bound,
                 case Inttab.lookup f row_index of
                     NONE => Inttab.update (row_index, (row_bound, [])) f
                   | SOME _ => raise (Internal "add_row_bound"))
    in
        VarGraph.update (dest_key, x) g
    end

fun update_sure_bound g (key as (_, btype)) bound =
    let
        val x =
            case VarGraph.lookup g key of
                NONE => (SOME bound, Inttab.empty)
              | SOME (NONE, f) => (SOME bound, f)
              | SOME (SOME old_bound, f) =>
                (SOME ((case btype of
                            UPPER => Float.min
                          | LOWER => Float.max)
                           old_bound bound), f)
    in
        VarGraph.update (key, x) g
    end

fun get_sure_bound g key =
    case VarGraph.lookup g key of
        NONE => NONE
      | SOME (sure_bound, _) => sure_bound

(*fun get_row_bound g key row_index =
    case VarGraph.lookup g key of
        NONE => NONE
      | SOME (sure_bound, f) =>
        (case Inttab.lookup f row_index of
             NONE => NONE
           | SOME (row_bound, _) => (sure_bound, row_bound))*)

fun add_edge g src_key dest_key row_index coeff =
    case VarGraph.lookup g dest_key of
        NONE => raise (Internal "add_edge: dest_key not found")
      | SOME (sure_bound, f) =>
        (case Inttab.lookup f row_index of
             NONE => raise (Internal "add_edge: row_index not found")
           | SOME (row_bound, sources) =>
             VarGraph.update (dest_key, (sure_bound, Inttab.update (row_index, (row_bound, (coeff, src_key) :: sources)) f)) g)

fun split_graph g =
  let
    fun split (key, (sure_bound, _)) (r1, r2) = case sure_bound
     of NONE => (r1, r2)
      | SOME bound =>  (case key
         of (u, UPPER) => (r1, Inttab.update (u, bound) r2)
          | (u, LOWER) => (Inttab.update (u, bound) r1, r2))
  in VarGraph.fold split g (Inttab.empty, Inttab.empty) end

(* If safe is true, termination is guaranteed, but the sure bounds may be not optimal (relative to the algorithm).
   If safe is false, termination is not guaranteed, but on termination the sure bounds are optimal (relative to the algorithm) *)
fun propagate_sure_bounds safe names g =
    let
        (* returns NONE if no new sure bound could be calculated, otherwise the new sure bound is returned *)
        fun calc_sure_bound_from_sources g (key as (_, btype)) =
            let
                fun mult_upper x (lower, upper) =
                    if Float.sign x = LESS then
                        Float.mult x lower
                    else
                        Float.mult x upper

                fun mult_lower x (lower, upper) =
                    if Float.sign x = LESS then
                        Float.mult x upper
                    else
                        Float.mult x lower

                val mult_btype = case btype of UPPER => mult_upper | LOWER => mult_lower

                fun calc_sure_bound (_, (row_bound, sources)) sure_bound =
                    let
                        fun add_src_bound (coeff, src_key) sum =
                            case sum of
                                NONE => NONE
                              | SOME x =>
                                (case get_sure_bound g src_key of
                                     NONE => NONE
                                   | SOME src_sure_bound => SOME (Float.add x (mult_btype src_sure_bound coeff)))
                    in
                        case fold add_src_bound sources (SOME row_bound) of
                            NONE => sure_bound
                          | new_sure_bound as (SOME new_bound) =>
                            (case sure_bound of
                                 NONE => new_sure_bound
                               | SOME old_bound =>
                                 SOME (case btype of
                                           UPPER => Float.min old_bound new_bound
                                         | LOWER => Float.max old_bound new_bound))
                    end
            in
                case VarGraph.lookup g key of
                    NONE => NONE
                  | SOME (sure_bound, f) =>
                    let
                        val x = Inttab.fold calc_sure_bound f sure_bound
                    in
                        if x = sure_bound then NONE else x
                    end
                end

        fun propagate (key, _) (g, b) =
            case calc_sure_bound_from_sources g key of
                NONE => (g,b)
              | SOME bound => (update_sure_bound g key bound,
                               if safe then
                                   case get_sure_bound g key of
                                       NONE => true
                                     | _ => b
                               else
                                   true)

        val (g, b) = VarGraph.fold propagate g (g, false)
    in
        if b then propagate_sure_bounds safe names g else g
    end

exception Load of string;

val empty_spvec = @{term "Nil :: real spvec"};
fun cons_spvec x xs = @{term "Cons :: nat * real => real spvec => real spvec"} $ x $ xs;
val empty_spmat = @{term "Nil :: real spmat"};
fun cons_spmat x xs = @{term "Cons :: nat * real spvec => real spmat => real spmat"} $ x $ xs;

fun calcr safe_propagation xlen names prec A b =
    let
        fun test_1 (lower, upper) =
            if lower = upper then
                (if Float.eq (lower, (~1, 0)) then ~1
                 else if Float.eq (lower, (1, 0)) then 1
                 else 0)
            else 0

        fun calcr (row_index, a) g =
            let
                val b =  FloatSparseMatrixBuilder.v_elem_at b row_index
                val (_, b2) = FloatArith.approx_decstr_by_bin prec (case b of NONE => "0" | SOME b => b)
                val approx_a = FloatSparseMatrixBuilder.v_fold (fn (i, s) => fn l =>
                                                                   (i, FloatArith.approx_decstr_by_bin prec s)::l) a []

                fun fold_dest_nodes (dest_index, dest_value) g =
                    let
                        val dest_test = test_1 dest_value
                    in
                        if dest_test = 0 then
                            g
                        else let
                                val (dest_key as (_, dest_btype), row_bound) =
                                    if dest_test = ~1 then
                                        ((dest_index, LOWER), Float.neg b2)
                                    else
                                        ((dest_index, UPPER), b2)

                                fun fold_src_nodes (src_index, src_value as (src_lower, src_upper)) g =
                                    if src_index = dest_index then g
                                    else
                                        let
                                            val coeff = case dest_btype of
                                                            UPPER => (Float.neg src_upper, Float.neg src_lower)
                                                          | LOWER => src_value
                                        in
                                            if Float.sign src_lower = LESS then
                                                add_edge g (src_index, UPPER) dest_key row_index coeff
                                            else
                                                add_edge g (src_index, LOWER) dest_key row_index coeff
                                        end
                            in
                                fold fold_src_nodes approx_a (add_row_bound g dest_key row_index row_bound)
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
                            update_sure_bound g (u, LOWER) (Float.neg b2)
                        else if atest = 1 then
                            update_sure_bound g (u, UPPER) b2
                        else
                            g
                    end
                  | _ => fold fold_dest_nodes approx_a g
            end

        val g = FloatSparseMatrixBuilder.m_fold calcr A VarGraph.empty

        val g = propagate_sure_bounds safe_propagation names g

        val (r1, r2) = split_graph g

        fun add_row_entry m index f vname value =
            let
                val v = (case value of 
                             SOME value => FloatSparseMatrixBuilder.mk_spvec_entry 0 value
                           | NONE => FloatSparseMatrixBuilder.mk_spvec_entry' 0 (f $ (Var ((vname,0), HOLogic.realT))))
                val vec = cons_spvec v empty_spvec
            in
                cons_spmat (FloatSparseMatrixBuilder.mk_spmat_entry index vec) m
            end

        fun abs_estimate i r1 r2 =
            if i = 0 then
                let val e = empty_spmat in (e, e) end
            else
                let
                    val index = xlen-i
                    val (r12_1, r12_2) = abs_estimate (i-1) r1 r2
                    val b1 = Inttab.lookup r1 index
                    val b2 = Inttab.lookup r2 index
                in
                    (add_row_entry r12_1 index @{term "lbound :: real => real"} ((names index)^"l") b1, 
                     add_row_entry r12_2 index @{term "ubound :: real => real"} ((names index)^"u") b2)
                end

        val (r1, r2) = abs_estimate xlen r1 r2

    in
        (r1, r2)
    end

fun load filename prec safe_propagation =
    let
        val prog = Cplex.load_cplexFile filename
        val prog = Cplex.elim_nonfree_bounds prog
        val prog = Cplex.relax_strict_ineqs prog
        val (maximize, c, A, b, (xlen, names, _)) = CplexFloatSparseMatrixConverter.convert_prog prog                       
        val (r1, r2) = calcr safe_propagation xlen names prec A b
        val _ = if maximize then () else raise Load "sorry, cannot handle minimization problems"
        val (dualprog, indexof) = FloatSparseMatrixBuilder.dual_cplexProg c A b
        val results = Cplex.solve dualprog
        val (_, v) = CplexFloatSparseMatrixConverter.convert_results results indexof
        (*val A = FloatSparseMatrixBuilder.cut_matrix v NONE A*)
        fun id x = x
        val v = FloatSparseMatrixBuilder.set_vector FloatSparseMatrixBuilder.empty_matrix 0 v
        val b = FloatSparseMatrixBuilder.transpose_matrix (FloatSparseMatrixBuilder.set_vector FloatSparseMatrixBuilder.empty_matrix 0 b)
        val c = FloatSparseMatrixBuilder.set_vector FloatSparseMatrixBuilder.empty_matrix 0 c
        val (y1, _) = FloatSparseMatrixBuilder.approx_matrix prec Float.positive_part v
        val A = FloatSparseMatrixBuilder.approx_matrix prec id A
        val (_,b2) = FloatSparseMatrixBuilder.approx_matrix prec id b
        val c = FloatSparseMatrixBuilder.approx_matrix prec id c
    in
        (y1, A, b2, c, (r1, r2))
    end handle CplexFloatSparseMatrixConverter.Converter s => (raise (Load ("Converter: "^s)))

end
