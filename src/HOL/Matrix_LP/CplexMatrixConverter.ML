(*  Title:      HOL/Matrix_LP/CplexMatrixConverter.ML
    Author:     Steven Obua
*)

signature MATRIX_BUILDER =
sig
    type vector
    type matrix
    
    val empty_vector : vector
    val empty_matrix : matrix

    exception Nat_expected of int
    val set_elem : vector -> int -> string -> vector
    val set_vector : matrix -> int -> vector -> matrix
end;

signature CPLEX_MATRIX_CONVERTER = 
sig
    structure cplex : CPLEX
    structure matrix_builder : MATRIX_BUILDER 
    type vector = matrix_builder.vector
    type matrix = matrix_builder.matrix
    type naming = int * (int -> string) * (string -> int)
    
    exception Converter of string

    (* program must fulfill is_normed_cplexProg and must be an element of the image of elim_nonfree_bounds *)
    (* convert_prog maximize c A b naming *)
    val convert_prog : cplex.cplexProg -> bool * vector * matrix * vector * naming

    (* results must be optimal, converts_results returns the optimal value as string and the solution as vector *)
    (* convert_results results name2index *)
    val convert_results : cplex.cplexResult -> (string -> int) -> string * vector
end;

functor MAKE_CPLEX_MATRIX_CONVERTER (structure cplex: CPLEX and matrix_builder: MATRIX_BUILDER) : CPLEX_MATRIX_CONVERTER =
struct

structure cplex = cplex
structure matrix_builder = matrix_builder
type matrix = matrix_builder.matrix
type vector = matrix_builder.vector
type naming = int * (int -> string) * (string -> int)

open matrix_builder 
open cplex

exception Converter of string;

fun neg_term (cplexNeg t) = t
  | neg_term (cplexSum ts) = cplexSum (map neg_term ts)
  | neg_term t = cplexNeg t 

fun convert_prog (cplexProg (_, goal, constrs, bounds)) = 
    let        
        fun build_naming index i2s s2i [] = (index, i2s, s2i)
          | build_naming index i2s s2i (cplexBounds (cplexNeg cplexInf, cplexLeq, cplexVar v, cplexLeq, cplexInf)::bounds)
            = build_naming (index+1) (Inttab.update (index, v) i2s) (Symtab.update_new (v, index) s2i) bounds
          | build_naming _ _ _ _ = raise (Converter "nonfree bound")

        val (varcount, i2s_tab, s2i_tab) = build_naming 0 Inttab.empty Symtab.empty bounds

        fun i2s i = case Inttab.lookup i2s_tab i of NONE => raise (Converter "index not found")
                                                     | SOME n => n
        fun s2i s = case Symtab.lookup s2i_tab s of NONE => raise (Converter ("name not found: "^s))
                                                     | SOME i => i
        fun num2str positive (cplexNeg t) = num2str (not positive) t
          | num2str positive (cplexNum num) = if positive then num else "-"^num                        
          | num2str _ _ = raise (Converter "term is not a (possibly signed) number")

        fun setprod vec positive (cplexNeg t) = setprod vec (not positive) t  
          | setprod vec positive (cplexVar v) = set_elem vec (s2i v) (if positive then "1" else "-1")
          | setprod vec positive (cplexProd (cplexNum num, cplexVar v)) = 
            set_elem vec (s2i v) (if positive then num else "-"^num)
          | setprod _ _ _ = raise (Converter "term is not a normed product")        

        fun sum2vec (cplexSum ts) = fold (fn t => fn vec => setprod vec true t) ts empty_vector
          | sum2vec t = setprod empty_vector true t                                                

        fun constrs2Ab j A b [] = (A, b)
          | constrs2Ab j A b ((_, cplexConstr (cplexLeq, (t1,t2)))::cs) = 
            constrs2Ab (j+1) (set_vector A j (sum2vec t1)) (set_elem b j (num2str true t2)) cs
          | constrs2Ab j A b ((_, cplexConstr (cplexGeq, (t1,t2)))::cs) = 
            constrs2Ab (j+1) (set_vector A j (sum2vec (neg_term t1))) (set_elem b j (num2str true (neg_term t2))) cs
          | constrs2Ab j A b ((_, cplexConstr (cplexEq, (t1,t2)))::cs) =
            constrs2Ab j A b ((NONE, cplexConstr (cplexLeq, (t1,t2)))::
                              (NONE, cplexConstr (cplexGeq, (t1, t2)))::cs)
          | constrs2Ab _ _ _ _ = raise (Converter "no strict constraints allowed")

        val (A, b) = constrs2Ab 0 empty_matrix empty_vector constrs
                                                                 
        val (goal_maximize, goal_term) = 
            case goal of
                (cplexMaximize t) => (true, t)
              | (cplexMinimize t) => (false, t)                                     
    in          
        (goal_maximize, sum2vec goal_term, A, b, (varcount, i2s, s2i))
    end

fun convert_results (cplex.Optimal (opt, entries)) name2index =
    let
        fun setv (name, value) v = matrix_builder.set_elem v (name2index name) value
    in
        (opt, fold setv entries (matrix_builder.empty_vector))
    end
  | convert_results _ _ = raise (Converter "No optimal result")

end;

structure SimpleMatrixBuilder : MATRIX_BUILDER = 
struct
type vector = (int * string) list
type matrix = (int * vector) list

val empty_matrix = []
val empty_vector = []

exception Nat_expected of int;

fun set_elem v i s = v @ [(i, s)] 

fun set_vector m i v = m @ [(i, v)]

end;

structure SimpleCplexMatrixConverter =
  MAKE_CPLEX_MATRIX_CONVERTER(structure cplex = Cplex and matrix_builder = SimpleMatrixBuilder);
