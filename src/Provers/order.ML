(*
  Title:	Transitivity reasoner for partial and linear orders
  Id:		$Id$
  Author:	Oliver Kutter
  Copyright:	TU Muenchen
*)

(* TODO: reduce number of input thms, reduce code duplication *)

(*

The packages provides tactics partial_tac and linear_tac that use all
premises of the form

  t = u, t ~= u, t < u, t <= u, ~(t < u) and ~(t <= u)

to
1. either derive a contradiction,
   in which case the conclusion can be any term,
2. or prove the conclusion, which must be of the same form as the
   premises (excluding ~(t < u) and ~(t <= u) for partial orders)

The package is implemented as an ML functor and thus not limited to the
relation <= and friends.  It can be instantiated to any partial and/or
linear order --- for example, the divisibility relation "dvd".  In
order to instantiate the package for a partial order only, supply
dummy theorems to the rules for linear orders, and don't use
linear_tac!

*)

signature LESS_ARITH =
sig
  (* Theorems for partial orders *)
  val less_reflE: thm  (* x < x ==> P *)
  val le_refl: thm  (* x <= x *)
  val less_imp_le: thm (* x < y ==> x <= y *)
  val eqI: thm (* [| x <= y; y <= x |] ==> x = y *)
  val eqD1: thm (* x = y ==> x <= y *)
  val eqD2: thm (* x = y ==> y <= x *)
  val less_trans: thm  (* [| x <= y; y <= z |] ==> x <= z *)
  val less_le_trans: thm  (* [| x <= y; y < z |] ==> x < z *)
  val le_less_trans: thm  (* [| x < y; y <= z |] ==> x < z *)
  val le_trans: thm  (* [| x < y; y < z |] ==> x < z *)
  val le_neq_trans : thm (* [| x <= y ; x ~= y |] ==> x < y *)
  val neq_le_trans : thm (* [| x ~= y ; x <= y |] ==> x < y *)

  (* Additional theorems for linear orders *)
  val not_lessD: thm (* ~(x < y) ==> y <= x *)
  val not_leD: thm (* ~(x <= y) ==> y < x *)
  val not_lessI: thm (* y <= x  ==> ~(x < y) *)
  val not_leI: thm (* y < x  ==> ~(x <= y) *)

  (* Additional theorems for subgoals of form x ~= y *)
  val less_imp_neq : thm (* x < y ==> x ~= y *)
  val eq_neq_eq_imp_neq : thm (* [| x = u ; u ~= v ; v = z|] ==> x ~= z *)

  (* Analysis of premises and conclusion *)
  (* decomp_x (`x Rel y') should yield (x, Rel, y)
       where Rel is one of "<", "<=", "~<", "~<=", "=" and "~=",
       other relation symbols cause an error message *)
  val decomp_part: Sign.sg -> term -> (term * string * term) option
  val decomp_lin: Sign.sg -> term -> (term * string * term) option
end;

signature TRANS_TAC  =
sig
  val partial_tac: int -> tactic
  val linear_tac:  int -> tactic
end;

functor Trans_Tac_Fun (Less: LESS_ARITH): TRANS_TAC =
struct

(* Extract subgoal with signature *)

fun SUBGOAL goalfun i st =
  goalfun (List.nth(prems_of st, i-1),  i, sign_of_thm st) st
                             handle Subscript => Seq.empty;

(* Internal datatype for the proof *)
datatype proof
  = Asm of int 
  | Thm of proof list * thm; 
  
exception Cannot;
  (* Internal exception, raised if conclusion cannot be derived from
     assumptions. *)
exception Contr of proof;
  (* Internal exception, raised if contradiction ( x < x ) was derived *)

fun prove asms = 
  let fun pr (Asm i) = nth_elem (i, asms)
  |       pr (Thm (prfs, thm)) = (map pr prfs) MRS thm
  in pr end;

(* Internal datatype for inequalities *)
datatype less 
   = Less  of term * term * proof 
   | Le    of term * term * proof
   | NotEq of term * term * proof; 

   
(* Misc functions for datatype less *)
fun lower (Less (x, _, _)) = x
  | lower (Le (x, _, _)) = x
  | lower (NotEq (x,_,_)) = x;

fun upper (Less (_, y, _)) = y
  | upper (Le (_, y, _)) = y
  | upper (NotEq (_,y,_)) = y;

fun getprf   (Less (_, _, p)) = p
|   getprf   (Le   (_, _, p)) = p
|   getprf   (NotEq (_,_, p)) = p;


(* ************************************************************************ *)
(*                                                                          *)
(* mkasm_partial sign (t, n) : Sign.sg -> (Term.term * int) -> less         *)
(*                                                                          *)
(* Tuple (t, n) (t an assumption, n its index in the assumptions) is        *)
(* translated to an element of type less.                                   *)
(* Partial orders only.                                                     *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkasm_partial sign (t, n) =
  case Less.decomp_part sign t of
    Some (x, rel, y) => (case rel of
      "<"   => if (x aconv y) then raise Contr (Thm ([Asm n], Less.less_reflE)) 
               else [Less (x, y, Asm n)]
    | "~<"  => []
    | "<="  => [Le (x, y, Asm n)]
    | "~<=" => [] 
    | "="   => [Le (x, y, Thm ([Asm n], Less.eqD1)),
                Le (y, x, Thm ([Asm n], Less.eqD2))]
    | "~="  => if (x aconv y) then 
                  raise Contr (Thm ([(Thm ([(Thm ([], Less.le_refl)) ,(Asm n)], Less.le_neq_trans))], Less.less_reflE))
               else [ NotEq (x, y, Asm n),
                      NotEq (y, x,Thm ( [Asm n], thm "not_sym"))] (* Le (x, x, Thm ([],Less.le_refl))]*) 
    | _     => error ("partial_tac: unknown relation symbol ``" ^ rel ^
                 "''returned by decomp_part."))
  | None => [];



(* ************************************************************************ *)
(*                                                                          *)
(* mkasm_linear sign (t, n) : Sign.sg -> (Term.term * int) -> less          *)
(*                                                                          *)
(* Tuple (t, n) (t an assumption, n its index in the assumptions) is        *)
(* translated to an element of type less.                                   *)
(* Linear orders only.                                                      *)
(*                                                                          *)
(* ************************************************************************ *)
 
fun mkasm_linear sign (t, n) =
  case Less.decomp_lin sign t of
    Some (x, rel, y) => (case rel of
      "<"   => if (x aconv y) then raise Contr (Thm ([Asm n], Less.less_reflE)) 
               else [Less (x, y, Asm n)]
    | "~<"  => [Le (y, x, Thm ([Asm n], Less.not_lessD))]
    | "<="  => [Le (x, y, Asm n)]
    | "~<=" => if (x aconv y) then 
                  raise (Contr (Thm ([Thm ([Asm n], Less.not_leD)], Less.less_reflE))) 
               else [Less (y, x, Thm ([Asm n], Less.not_leD))] 
    | "="   => [Le (x, y, Thm ([Asm n], Less.eqD1)),
                Le (y, x, Thm ([Asm n], Less.eqD2))]
    | "~="  => if (x aconv y) then 
                  raise Contr (Thm ([(Thm ([(Thm ([], Less.le_refl)) ,(Asm n)], Less.le_neq_trans))], Less.less_reflE))
               else [ NotEq (x, y, Asm n),
                      NotEq (y, x,Thm ( [Asm n], thm "not_sym"))] 
    | _     => error ("linear_tac: unknown relation symbol ``" ^ rel ^
                 "''returned by decomp_lin."))
  | None => [];


(* ************************************************************************ *)
(*                                                                          *)
(* mkconcl_partial sign t : Sign.sg -> Term.term -> less                    *)
(*                                                                          *)
(* Translates conclusion t to an element of type less.                      *)
(* Partial orders only.                                                     *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkconcl_partial sign t =
  case Less.decomp_part sign t of
    Some (x, rel, y) => (case rel of
      "<"   => ([Less (x, y, Asm ~1)], Asm 0)
    | "<="  => ([Le (x, y, Asm ~1)], Asm 0)
    | "="   => ([Le (x, y, Asm ~1), Le (y, x, Asm ~1)],
                 Thm ([Asm 0, Asm 1], Less.eqI))
    | "~="  => ([NotEq (x,y, Asm ~1)], Asm 0)
    | _  => raise Cannot)
  | None => raise Cannot;


(* ************************************************************************ *)
(*                                                                          *)
(* mkconcl_linear sign t : Sign.sg -> Term.term -> less                     *)
(*                                                                          *)
(* Translates conclusion t to an element of type less.                      *)
(* Linear orders only.                                                      *)
(*                                                                          *)
(* ************************************************************************ *)

fun mkconcl_linear sign t =
  case Less.decomp_lin sign t of
    Some (x, rel, y) => (case rel of
      "<"   => ([Less (x, y, Asm ~1)], Asm 0)
    | "~<"  => ([Le (y, x, Asm ~1)], Thm ([Asm 0], Less.not_lessI))
    | "<="  => ([Le (x, y, Asm ~1)], Asm 0)
    | "~<=" => ([Less (y, x, Asm ~1)], Thm ([Asm 0], Less.not_leI))
    | "="   => ([Le (x, y, Asm ~1), Le (y, x, Asm ~1)],
                 Thm ([Asm 0, Asm 1], Less.eqI))
    | "~="  => ([NotEq (x,y, Asm ~1)], Asm 0)
    | _  => raise Cannot)
  | None => raise Cannot;
 


(* ******************************************************************* *)
(*                                                                     *)
(* mergeLess (less1,less2):  less * less -> less                       *)
(*                                                                     *)
(* Merge to elements of type less according to the following rules     *)
(*                                                                     *)
(* x <  y && y <  z ==> x < z                                          *)
(* x <  y && y <= z ==> x < z                                          *)
(* x <= y && y <  z ==> x < z                                          *)
(* x <= y && y <= z ==> x <= z                                         *)
(* x <= y && x ~= y ==> x < y                                          *)
(* x ~= y && x <= y ==> x < y                                          *)
(* x <  y && x ~= y ==> x < y                                          *)
(* x ~= y && x <  y ==> x < y                                          *)
(*                                                                     *)
(* ******************************************************************* *)

fun mergeLess (Less (x, _, p) , Less (_ , z, q)) =
      Less (x, z, Thm ([p,q] , Less.less_trans))
|   mergeLess (Less (x, _, p) , Le (_ , z, q)) =
      Less (x, z, Thm ([p,q] , Less.less_le_trans))
|   mergeLess (Le (x, _, p) , Less (_ , z, q)) =
      Less (x, z, Thm ([p,q] , Less.le_less_trans))
|   mergeLess (Le (x, z, p) , NotEq (x', z', q)) =
      if (x aconv x' andalso z aconv z' ) 
      then Less (x, z, Thm ([p,q] , Less.le_neq_trans))
      else error "linear/partial_tac: internal error le_neq_trans"
|   mergeLess (NotEq (x, z, p) , Le (x' , z', q)) =
      if (x aconv x' andalso z aconv z') 
      then Less (x, z, Thm ([p,q] , Less.neq_le_trans))
      else error "linear/partial_tac: internal error neq_le_trans"
|   mergeLess (NotEq (x, z, p) , Less (x' , z', q)) =
      if (x aconv x' andalso z aconv z') 
      then Less ((x' , z', q))
      else error "linear/partial_tac: internal error neq_less_trans"
|   mergeLess (Less (x, z, p) , NotEq (x', z', q)) =
      if (x aconv x' andalso z aconv z') 
      then Less (x, z, p)
      else error "linear/partial_tac: internal error less_neq_trans"
|   mergeLess (Le (x, _, p) , Le (_ , z, q)) =
      Le (x, z, Thm ([p,q] , Less.le_trans))
|   mergeLess (_, _) =
      error "linear/partial_tac: internal error: undefined case";


(* ******************************************************************** *)
(* tr checks for valid transitivity step                                *)
(* ******************************************************************** *)

infix tr;
fun (Less (_, y, _)) tr (Le (x', _, _))   = ( y aconv x' )
  | (Le   (_, y, _)) tr (Less (x', _, _)) = ( y aconv x' )
  | (Less (_, y, _)) tr (Less (x', _, _)) = ( y aconv x' )
  | (Le (_, y, _))   tr (Le (x', _, _))   = ( y aconv x' )
  | _ tr _ = false;
  
  
(* ******************************************************************* *)
(*                                                                     *)
(* transPath (Lesslist, Less): (less list * less) -> less              *)
(*                                                                     *)
(* If a path represented by a list of elements of type less is found,  *)
(* this needs to be contracted to a single element of type less.       *)
(* Prior to each transitivity step it is checked whether the step is   *)
(* valid.                                                              *)
(*                                                                     *)
(* ******************************************************************* *)

fun transPath ([],lesss) = lesss
|   transPath (x::xs,lesss) =
      if lesss tr x then transPath (xs, mergeLess(lesss,x))
      else error "linear/partial_tac: internal error transpath";
  
(* ******************************************************************* *)
(*                                                                     *)
(* less1 subsumes less2 : less -> less -> bool                         *)
(*                                                                     *)
(* subsumes checks whether less1 implies less2                         *)
(*                                                                     *)
(* ******************************************************************* *)
  
infix subsumes;
fun (Less (x, y, _)) subsumes (Le (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Less (x, y, _)) subsumes (Less (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Le (x, y, _)) subsumes (Le (x', y', _)) =
      (x aconv x' andalso y aconv y')
  | (Less (x, y, _)) subsumes (NotEq (x', y', _)) =
      (x aconv x' andalso y aconv y') orelse (y aconv x' andalso x aconv y')
  | (NotEq (x, y, _)) subsumes (NotEq (x', y', _)) =
      (x aconv x' andalso y aconv y') orelse (y aconv x' andalso x aconv y')
  | (Le _) subsumes (Less _) =
      error "linear/partial_tac: internal error: Le cannot subsume Less"
  | _ subsumes _ = false;

(* ******************************************************************* *)
(*                                                                     *)
(* triv_solv less1 : less ->  proof Library.option                     *)
(*                                                                     *)
(* Solves trivial goal x <= x.                                         *)
(*                                                                     *)
(* ******************************************************************* *)

fun triv_solv (Le (x, x', _)) =
    if x aconv x' then  Some (Thm ([], Less.le_refl)) 
    else None
|   triv_solv _ = None;

(* ********************************************************************* *)
(* Graph functions                                                       *)
(* ********************************************************************* *)



(* ******************************************************************* *)
(*                                                                     *)
(* General:                                                            *)
(*                                                                     *)
(* Inequalities are represented by various types of graphs.            *)
(*                                                                     *)
(* 1. (Term.term * Term.term list) list                                *)
(*    - Graph of this type is generated from the assumptions,          *)
(*      does not contain information on which edge stems from which    *)
(*      assumption.                                                    *)
(*    - Used to compute strong components.                             *)
(*                                                                     *)
(* 2. (Term.term * (Term.term * less) list) list                       *)
(*    - Graph of this type is generated from the assumptions,          *)
(*      it does contain information on which edge stems from which     *)
(*      assumption.                                                    *)
(*    - Used to reconstruct paths.                                     *)
(*                                                                     *)
(* 3. (int * (int * less) list ) list                                  *)
(*    - Graph of this type is generated from the strong components of  *)
(*      graph of type 2.  It consists of the strong components of      *)
(*      graph 2, where nodes are indices of the components.            *)
(*      Only edges between components are part of this graph.          *)
(*    - Used to reconstruct paths between several components.          *)
(*                                                                     *)
(* 4. (int * int list) list                                            *)
(*    - Graph of this type is generated from graph of type 3, but      *)
(*      edge information of type less is removed.                      *)
(*    - Used to                                                        *)
(*      - Compute transposed graphs of type 4.                         *)
(*      - Compute list of components reachable from a component.       *)
(*                                                                     *)
(*                                                                     *)
(* ******************************************************************* *)

   
(* *********************************************************** *)
(* Functions for constructing graphs                           *)
(* *********************************************************** *)

fun addLessEdge (v,d,[]) = [(v,d)]
|   addLessEdge (v,d,((u,dl)::el)) = if v aconv u then ((v,d@dl)::el)
    else (u,dl):: (addLessEdge(v,d,el));

fun addTermEdge (v,u,[]) = [(v,[u])]
|   addTermEdge (v,u,((x,adj)::el)) = if v aconv x then (v,u::adj)::el
    else    (x,adj) :: addTermEdge (v,u,el);
    
(* ********************************************************************* *)
(*                                                                       *)
(* buildGraphs constructs three graphs from a list of type less:         *)
(*   g1: graph for the <= relation                                       *)
(*   g2: graph for the <= relation with additional information for       *)
(*       proof reconstruction                                            *)
(*   neqEdges: all edges that are candidates for a ~=                    *)
(*                                                                       *)
(* ********************************************************************* *)


fun buildGraphs ([],g1,g2,neqEdges) = (g1, g2, neqEdges)
|   buildGraphs (l::ls,g1,g2,neqEdges) = case l of 
(Less (x,y,p)) =>(
      let val g1' = addTermEdge (x,y,g1)
       and g2' = addLessEdge (x,[(y,(Less (x, y, p)))],g2)
      in buildGraphs (ls,g1',g2',l::neqEdges) end)
| (Le (x,y,p)) =>
( let val g1' = addTermEdge (x,y,g1)
       and g2' = addLessEdge (x,[(y,(Le (x, y,p)))],g2)
  in buildGraphs (ls,g1',g2',neqEdges) end)
| (NotEq  (x,y,p)) => (   buildGraphs (ls,g1,g2,l::neqEdges) )


(* *********************************************************************** *)
(*                                                                         *)
(* adjacent_term g u : (Term.term * 'a list ) list -> Term.term -> 'a list *)
(*                                                                         *)
(*                                                                         *)
(* *********************************************************************** *)

fun adjacent_term ((v,adj)::el) u = 
    if u aconv v then adj else adjacent_term el u
|   adjacent_term nil _ = []

(* *********************************************************************** *)
(*                                                                         *)
(* adjacent_term g u : (''a * 'b list ) list -> ''a -> 'b list             *)
(*                                                                         *)
(* List of successors of u in graph g                                      *)
(*                                                                         *)
(* *********************************************************************** *)
 
fun adjacent ((v,adj)::el) u = 
    if u = v then adj else adjacent el u
|   adjacent nil _ = []  
  

(* *********************************************************************** *)
(*                                                                         *)
(* transpose_term g:                                                       *)
(* (Term.term * Term.term list) list -> (Term.term * Term.term list) list  *)
(*                                                                         *)
(* Computes transposed graph g' from g                                     *)
(* by reversing all edges u -> v to v -> u                                 *)
(*                                                                         *)
(* *********************************************************************** *)

 fun transpose_term g =
  let
   (* Compute list of reversed edges for each adjacency list *)
   fun flip (u,v::el) = (v,u) :: flip (u,el)
     | flip (_,nil) = nil

   (* Compute adjacency list for node u from the list of edges
      and return a likewise reduced list of edges.  The list of edges
      is searches for edges starting from u, and these edges are removed. *)
   fun gather (u,(v,w)::el) =
    let
     val (adj,edges) = gather (u,el)
    in
      if u aconv v then (w::adj,edges)
      else (adj,(v,w)::edges)
    end
   | gather (_,nil) = (nil,nil)

   (* For every node in the input graph, call gather to find all reachable
      nodes in the list of edges *)
   fun assemble ((u,_)::el) edges =
       let val (adj,edges) = gather (u,edges)
       in (u,adj) :: assemble el edges
       end
     | assemble nil _ = nil

   (* Compute, for each adjacency list, the list with reversed edges,
      and concatenate these lists. *)
   val flipped = foldr (op @) ((map flip g),nil)
      
 in assemble g flipped  end    
      
(* *********************************************************************** *)
(*                                                                         *)
(* transpose g:                                                            *)
(* (''a * ''a list) list -> (''a * ''a list) list                          *)
(*                                                                         *)
(* Computes transposed graph g' from g                                     *)
(* by reversing all edges u -> v to v -> u                                 *)
(*                                                                         *)
(* *********************************************************************** *)

fun transpose g =
  let
   (* Compute list of reversed edges for each adjacency list *)
   fun flip (u,v::el) = (v,u) :: flip (u,el)
     | flip (_,nil) = nil
   
   (* Compute adjacency list for node u from the list of edges
      and return a likewise reduced list of edges.  The list of edges
      is searches for edges starting from u, and these edges are removed. *)
   fun gather (u,(v,w)::el) =
    let
     val (adj,edges) = gather (u,el)
    in
     if u = v then (w::adj,edges)
     else (adj,(v,w)::edges)
    end
   | gather (_,nil) = (nil,nil)

   (* For every node in the input graph, call gather to find all reachable
      nodes in the list of edges *)
   fun assemble ((u,_)::el) edges =
       let val (adj,edges) = gather (u,edges)
       in (u,adj) :: assemble el edges
       end
     | assemble nil _ = nil

   (* Compute, for each adjacency list, the list with reversed edges,
      and concatenate these lists. *)
   val flipped = foldr (op @) ((map flip g),nil)
 
 in assemble g flipped end    
      
      
(* scc_term : (term * term list) list -> term list list *)

(* The following is based on the algorithm for finding strongly
   connected components described in Introduction to Algorithms,
   by Cormon, Leiserson, and Rivest, section 23.5. The input G
   is an adjacency list description of a directed graph. The
   output is a list of the strongly connected components (each a
   list of vertices). *)          
     
fun scc_term G =
     let
  (* Ordered list of the vertices that DFS has finished with;
     most recently finished goes at the head. *)
  val finish : term list ref = ref nil

  (* List of vertices which have been visited. *)
  val visited : term list ref = ref nil
  
  fun been_visited v = exists (fn w => w aconv v) (!visited)
  
  (* Given the adjacency list rep of a graph (a list of pairs),
     return just the first element of each pair, yielding the 
     vertex list. *)
  val members = map (fn (v,_) => v)

  (* Returns the nodes in the DFS tree rooted at u in g *)
  fun dfs_visit g u : term list =
      let
   val _ = visited := u :: !visited
   val descendents =
       foldr (fn (v,ds) => if been_visited v then ds
            else v :: dfs_visit g v @ ds)
        ((adjacent_term g u) ,nil)
      in
   finish := u :: !finish;
   descendents
      end
     in

  (* DFS on the graph; apply dfs_visit to each vertex in
     the graph, checking first to make sure the vertex is
     as yet unvisited. *)
  app (fn u => if been_visited u then ()
        else (dfs_visit G u; ()))  (members G);
  visited := nil;

  (* We don't reset finish because its value is used by
     revfold below, and it will never be used again (even
     though dfs_visit will continue to modify it). *)

  (* DFS on the transpose. The vertices returned by
     dfs_visit along with u form a connected component. We
     collect all the connected components together in a
     list, which is what is returned. *)
  foldl (fn (comps,u) =>  
      if been_visited u then comps
      else ((u :: dfs_visit (transpose_term G) u) :: comps))  (nil,(!finish))
end;


(* *********************************************************************** *)
(*                                                                         *)
(* dfs_int_reachable g u:                                                  *)
(* (int * int list) list -> int -> int list                                *) 
(*                                                                         *)
(* Computes list of all nodes reachable from u in g.                       *)
(*                                                                         *)
(* *********************************************************************** *)


fun dfs_int_reachable g u = 
 let
  (* List of vertices which have been visited. *)
  val visited : int list ref = ref nil
  
  fun been_visited v = exists (fn w => w = v) (!visited)

  fun dfs_visit g u : int list =
      let
   val _ = visited := u :: !visited
   val descendents =
       foldr (fn (v,ds) => if been_visited v then ds
            else v :: dfs_visit g v @ ds)
        ( ((adjacent g u)) ,nil)
   in  descendents end
 
 in u :: dfs_visit g u end;

    
fun indexComps components = 
    ListPair.map (fn (a,b) => (b,a)) (components, 0 upto (length components -1));

fun indexNodes IndexComp = 
    flat (map (fn (index, comp) => (map (fn v => (v,index)) comp)) IndexComp);
    
fun getIndex v [] = ~1
|   getIndex v ((v',k)::vs) = if v aconv v' then k else getIndex v vs; 
    

(* ***************************************************************** *)
(*                                                                   *)
(* evalcompgraph components g ntc :                                  *)
(* Term.term list list ->                                            *)
(* (Term.term * (Term.term * less) list) list ->                     *)
(* (Term.term * int) list ->  (int * (int * less) list) list         *)
(*                                                                   *)
(*                                                                   *)
(* Computes, from graph g, list of all its components and the list   *)
(* ntc (nodes, index of component) a graph whose nodes are the       *)
(* indices of the components of g.  Egdes of the new graph are       *)
(* only the edges of g linking two components.                       *)
(*                                                                   *)
(* ***************************************************************** *)

fun evalcompgraph components g ntc = 
    let
    (* Liste (Index der Komponente, Komponente *)
    val IndexComp = indexComps components;

    (* Compute new graph with the property that it only contains edges
       between components. *)
  
    (* k is index of current start component. *)   
       
    fun processComponent (k, comp) = 
     let
         (* all edges pointing away from the component *)
	   (* (Term.term * less) list *)
	       val allEdges = flat (map (adjacent_term g) comp);

		(* choose those edges pointing to nodes outside
                   the current component *)
		
		fun selectEdges  [] = []
		|   selectEdges  ((v,l)::es) = let val k' = getIndex v ntc in 
		    if k' = k then selectEdges es else (k', l) :: (selectEdges  es) end;

		 (* Insert edge into sorted list of edges, where edge is
                    only added if
                    - it is found for the first time
                    - it is a <= edge and no parallel < edge was found earlier
                    - it is a < edge
                 *)
		     
		 fun insert (h,l) [] = [(h,l)]
		 |   insert (h,l) ((k',l')::es) = if h = k' then (
		     case l of (Less (_, _, _)) => (h,l)::es
		     | _  => (case l' of (Less (_, _, _)) => (h,l')::es
	                      | _ => (k',l)::es) )
		     else (k',l'):: insert (h,l) es;

		 (* Reorganise list of edges such that
                    - duplicate edges are removed
                    - if a < edge and a <= edge exist at the same time,
                      remove <= edge *)
		     
		 fun sortEdges [] sorted = sorted: (int * less) list
		 |   sortEdges (e::es) sorted = sortEdges es (insert e sorted); 
		    
     in 
       (k, (sortEdges (selectEdges allEdges) []))
     end; 
     
	     			       
in map processComponent IndexComp end; 

(* Remove ``less'' edge info from graph *)
(* type ('a * ('a * less) list) list *)
fun stripOffLess g = map (fn (v, desc) => (v,map (fn (u,l) => u) desc)) g;



(* *********************************************************************** *)
(*                                                                         *)
(* dfs_term g u v:                                                         *)
(* (Term.term  *(Term.term * less) list) list ->                           *)
(* Term.term -> Term.term -> (bool * less list)                            *) 
(*                                                                         *)
(* Depth first search of v from u.                                         *)
(* Returns (true, path(u, v)) if successful, otherwise (false, []).        *)
(*                                                                         *)
(* *********************************************************************** *)


fun dfs_term g u v = 
 let 
(* TODO: this comment is unclear *)
    (* Liste der gegangenen Kanten, 
       die Kante e die zum Vorgaenger eines Knoten u gehoert ist jene 
       für die gilt (upper e) = u *)
    val pred :  less list ref = ref nil;
    val visited: term list ref = ref nil;
    
    fun been_visited v = exists (fn w => w aconv v) (!visited)
    
    fun dfs_visit u' = 
    let val _ = visited := u' :: (!visited)
    
    fun update l = let val _ = pred := l ::(!pred) in () end;
    
    in if been_visited v then () 
       else (app (fn (v',l) => if been_visited v' then () else (
        update l; 
        dfs_visit v'; ()) )) (adjacent_term g u')
    end
   
  in 
    dfs_visit u; 
    if (been_visited v) then (true, (!pred)) else (false , [])   
  end;

  
(* *********************************************************************** *)
(*                                                                         *)
(* completeTermPath u v g:                                                 *)
(* Term.term -> Term.term -> (Term.term * (Term.term * less) list) list    *) 
(* -> less list                                                            *)
(*                                                                         *)
(* Complete the path from u to v in graph g.  Path search is performed     *)
(* with dfs_term g u v.  This yields for each node v' its predecessor u'   *)
(* and the edge u' -> v'.  Allows traversing graph backwards from v and    *)
(* finding the path u -> v.                                                *)
(*                                                                         *)
(* *********************************************************************** *)

  
fun completeTermPath u v g = 
  let 
   
   val (found, pred) = dfs_term g u v;

   fun path x y  =
      let
 
      (* find predecessor u of node v and the edge u -> v *)

      fun lookup v [] = raise Cannot
      |   lookup v (e::es) = if (upper e) aconv v then e else lookup v es;

      (* traverse path backwards and return list of visited edges *)   
      fun rev_path v = 
       let val l = lookup v pred
           val u = lower l;
       in
        if u aconv x then [l]
        else (rev_path u) @ [l] 
       end
     in rev_path y end;
       
  in 
  if found then (if u aconv v then [(Le (u, v, (Thm ([], Less.le_refl))))]
  else path u v ) else raise Cannot
end;  


(* *********************************************************************** *)
(*                                                                         *)
(* dfs_int g u v:                                                          *)
(* (int  *(int * less) list) list -> int -> int                            *)
(* -> (bool *(int*  less) list)                                            *) 
(*                                                                         *)
(* Depth first search of v from u.                                         *)
(* Returns (true, path(u, v)) if successful, otherwise (false, []).        *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs_int g u v = 
 let 
    val pred : (int * less ) list ref = ref nil;
    val visited: int list ref = ref nil;
    
    fun been_visited v = exists (fn w => w = v) (!visited)
    
    fun dfs_visit u' = 
    let val _ = visited := u' :: (!visited)
    
    fun update (x,l) = let val _ = pred := (x,l) ::(!pred) in () end;
    
    in if been_visited v then () 
    else (app (fn (v',l) => if been_visited v' then () else (
       update (v',l); 
       dfs_visit v'; ()) )) (adjacent g u')
    
    end
   
  in 
    dfs_visit u; 
    if (been_visited v) then (true, (!pred)) else (false , [])   
  end;
  
     
(* *********************************************************************** *)
(*                                                                         *)
(* findProof (g2,  cg2, neqEdges, components, ntc) subgoal:                *)
(* (Term.term * (Term.term * less) list) list *                            *)
(* (int * (int * less) list) list * less list *  Term.term list list       *)
(* * ( (Term.term * int) -> proof                                          *)
(*                                                                         *)
(* findProof constructs from graphs (g2, cg2) and neqEdges a proof for     *)
(* subgoal.  Raises exception Cannot if this is not possible.              *)
(*                                                                         *)
(* *********************************************************************** *)
     
fun findProof (g2, cg2, neqEdges, components, ntc ) subgoal =
let
   
 (* complete path x y from component graph *)
 fun completeComponentPath x y predlist = 
   let         
	  val xi = getIndex x ntc
	  val yi = getIndex y ntc 
	  
	  fun lookup k [] =  raise Cannot
	  |   lookup k ((h,l)::us) = if k = h then l else lookup k us;	  
	  
	  fun rev_completeComponentPath y' = 
	   let val edge = lookup (getIndex y' ntc) predlist
	       val u = lower edge
	       val v = upper edge
	   in
             if (getIndex u ntc) = xi then 
	       (completeTermPath x u g2)@[edge]@(completeTermPath v y' g2)
	     else (rev_completeComponentPath u)@[edge]@(completeTermPath v y' g2)
           end
   in  
      if x aconv y then 
        [(Le (x, y, (Thm ([], Less.le_refl))))]
      else ( if xi = yi then completeTermPath x y g2
             else rev_completeComponentPath y )  
   end;

(* ******************************************************************* *) 
(* findLess e x y xi yi xreachable yreachable                          *)
(*                                                                     *)
(* Find a path from x through e to y, of weight <                      *)
(* ******************************************************************* *) 
 
 fun findLess e x y xi yi Xreachable Yreachable = 
  let val u = lower e 
      val v = upper e
      val ui = getIndex u ntc
      val vi = getIndex v ntc
            
  in 
      if ui mem Xreachable andalso vi mem Xreachable andalso 
         ui mem Yreachable andalso vi mem Yreachable then (
       
  (case e of (Less (_, _, _)) =>  
       let
        val (xufound, xupred) = dfs_int cg2 xi (getIndex u ntc)
	    in 
	     if xufound then (
	      let 
	       val (vyfound, vypred) = dfs_int cg2 (getIndex v ntc) yi 
	      in 
	       if vyfound then (
	        let 
	         val xypath = (completeComponentPath x u xupred)@[e]@(completeComponentPath v y vypred)
	         val xyLesss = transPath (tl xypath, hd xypath)
	        in 
		 if xyLesss subsumes subgoal then Some (getprf xyLesss) 
                 else None
	       end)
	       else None
	      end)
	     else None
	    end
       |  _   => 
         let val (xufound, xupred) = dfs_int cg2 xi (getIndex u ntc)
             in 
	      if xufound then (
	       let 
	        val (uvfound, uvpred) = dfs_int cg2 (getIndex u ntc) (getIndex v ntc)
	       in
		if uvfound then (
		 let 
		  val (vyfound, vypred) = dfs_int cg2 (getIndex v ntc) yi
		 in 
		  if vyfound then (
		   let
		    val uvpath = completeComponentPath u v uvpred
		    val uvLesss = mergeLess ( transPath (tl uvpath, hd uvpath), e)
		    val xypath = (completeComponentPath  x u xupred)@[uvLesss]@(completeComponentPath v y vypred)
		    val xyLesss = transPath (tl xypath, hd xypath)
		   in 
		    if xyLesss subsumes subgoal then Some (getprf xyLesss)
                    else None
		   end )
		  else None   
	         end)
		else None
	       end ) 
	      else None
	     end )
    ) else None
end;  
   
         
in
  (* looking for x <= y: any path from x to y is sufficient *)
  case subgoal of (Le (x, y, _)) => (
  
   let 
    val xi = getIndex x ntc
    val yi = getIndex y ntc
    (* sucht im Komponentengraphen einen Weg von der Komponente in der x liegt
       zu der in der y liegt *)
    val (found, pred) = dfs_int cg2 xi yi
   in 
    if found then (
       let val xypath = completeComponentPath x y pred 
           val xyLesss = transPath (tl xypath, hd xypath) 
       in  
	  (case xyLesss of
	    (Less (_, _, q)) => if xyLesss subsumes subgoal then (Thm ([q], Less.less_imp_le))  
				else raise Cannot
	     | _   => if xyLesss subsumes subgoal then (getprf xyLesss) 
	              else raise Cannot)
       end )
     else raise Cannot 
   end 
   
   )
 (* looking for x < y: particular path required, which is not necessarily
    found by normal dfs *)
 |   (Less (x, y, _)) => (
   let 
    val xi = getIndex x ntc
    val yi = getIndex y ntc
    val cg2' = stripOffLess cg2
    val cg2'_transpose = transpose cg2'
    (* alle von x aus erreichbaren Komponenten *)
    val xreachable = dfs_int_reachable cg2' xi
    (* all comonents reachable from y in the transposed graph cg2' *)
    val yreachable = dfs_int_reachable cg2'_transpose yi
    (* for all edges u ~= v or u < v check if they are part of path x < y *)
    fun processNeqEdges [] = raise Cannot 
    |   processNeqEdges (e::es) = 
      case  (findLess e x y xi yi xreachable yreachable) of (Some prf) => prf  
      | _ => processNeqEdges es
        
    in 
       processNeqEdges neqEdges 
    end
 
 )
| (NotEq (x, y, _)) => (
  
  let val xi = getIndex x ntc 
        val yi = getIndex y ntc
	val cg2' = stripOffLess cg2
	val cg2'_transpose = transpose cg2'
        val xreachable = dfs_int_reachable cg2' xi
	val yreachable = dfs_int_reachable cg2'_transpose yi
	
	fun processNeqEdges [] = raise Cannot  
  	|   processNeqEdges (e::es) = (
	    let val u = lower e 
	        val v = upper e
		val ui = getIndex u ntc
		val vi = getIndex v ntc
		
	    in  
	        (* if x ~= y follows from edge e *)
	    	         if e subsumes subgoal then (
		     case e of (Less (u, v, q)) => (
		       if u aconv x andalso v aconv y then (Thm ([q], Less.less_imp_neq))
		       else (Thm ([(Thm ([q], Less.less_imp_neq))], thm "not_sym"))
		     )
		     |    (NotEq (u,v, q)) => (
		       if u aconv x andalso v aconv y then q
		       else (Thm ([q],  thm "not_sym"))
		     )
		 )
                (* if SCC_x is linked to SCC_y via edge e *)
		 else if ui = xi andalso vi = yi then (
                   case e of (Less (_, _,_)) => (
		        let val xypath = (completeTermPath x u g2) @ [e] @ (completeTermPath v y g2)
			    val xyLesss = transPath (tl xypath, hd xypath)
			in  (Thm ([getprf xyLesss], Less.less_imp_neq)) end)
		   | _ => (   
		        let val xupath = completeTermPath x u g2
			    val uxpath = completeTermPath u x g2
			    val vypath = completeTermPath v y g2
			    val yvpath = completeTermPath y v g2
			    val xuLesss = transPath (tl xupath, hd xupath)     
			    val uxLesss = transPath (tl uxpath, hd uxpath)			    
			    val vyLesss = transPath (tl vypath, hd vypath)			
			    val yvLesss = transPath (tl yvpath, hd yvpath)
			    val x_eq_u =  (Thm ([(getprf xuLesss),(getprf uxLesss)], Less.eqI))
			    val v_eq_y =  (Thm ([(getprf vyLesss),(getprf yvLesss)], Less.eqI))
			in 
                           (Thm ([x_eq_u , (getprf e), v_eq_y ], Less.eq_neq_eq_imp_neq)) 
			end
			)       
		  ) else if ui = yi andalso vi = xi then (
		     case e of (Less (_, _,_)) => (
		        let val xypath = (completeTermPath y u g2) @ [e] @ (completeTermPath v x g2)
			    val xyLesss = transPath (tl xypath, hd xypath)
			in (Thm ([(Thm ([getprf xyLesss], Less.less_imp_neq))] , thm "not_sym")) end ) 
		     | _ => (
		        
			let val yupath = completeTermPath y u g2
			    val uypath = completeTermPath u y g2
			    val vxpath = completeTermPath v x g2
			    val xvpath = completeTermPath x v g2
			    val yuLesss = transPath (tl yupath, hd yupath)     
			    val uyLesss = transPath (tl uypath, hd uypath)			    
			    val vxLesss = transPath (tl vxpath, hd vxpath)			
			    val xvLesss = transPath (tl xvpath, hd xvpath)
			    val y_eq_u =  (Thm ([(getprf yuLesss),(getprf uyLesss)], Less.eqI))
			    val v_eq_x =  (Thm ([(getprf vxLesss),(getprf xvLesss)], Less.eqI))
			in
			    (Thm ([(Thm ([y_eq_u , (getprf e), v_eq_x ], Less.eq_neq_eq_imp_neq))], thm "not_sym"))
		        end
		       )
		  ) else (
                       (* there exists a path x < y or y < x such that
                          x ~= y may be concluded *)
	        	case  (findLess e x y xi yi xreachable yreachable) of 
		              (Some prf) =>  (Thm ([prf], Less.less_imp_neq))  
                             | None =>  (
		               let 
		                val yr = dfs_int_reachable cg2' yi
	                        val xr = dfs_int_reachable cg2'_transpose xi
		               in 
		                case  (findLess e y x yi xi yr xr) of 
		                      (Some prf) => (Thm ([(Thm ([prf], Less.less_imp_neq))], thm "not_sym")) 
                                      | _ => processNeqEdges es
		               end)
		 ) end) 
     in processNeqEdges neqEdges end
  )    
end;


(* *********************************************************************** *)
(*                                                                         *)
(* checkComponents g components ntc neqEdges:                              *)
(* (Term.term * (Term.term * less) list) list -> Term.term list list  ->   *)
(* (Term.term * int) -> less list -> bool                                  *)
(*                                                                         *)
(* For each edge in the list neqEdges check if it leads to a contradiction.*)
(* We have a contradiction for edge u ~= v and u < v if:                   *)
(* - u and v are in the same component,                                    *)
(*   that is, a path u <= v and a path v <= u exist, hence u = v.          *)
(* From irreflexivity of < follows u < u or v < v.  Ex false quodlibet.    *)
(*                                                                         *)
(*                                                                         *)
(* *********************************************************************** *)


fun checkComponents g components ntc neqEdges = 
 let
    (* Construct proof by contradiction for edge *)
    fun handleContr edge  = 
       (case edge of 
          (Less  (x, y, _)) => (
	    let 
	     val xxpath = edge :: (completeTermPath y x g)
	     val xxLesss = transPath (tl xxpath, hd xxpath)
	     val q = getprf xxLesss
	    in 
	     raise (Contr (Thm ([q], Less.less_reflE ))) 
	    end 
	  )
        | (NotEq (x, y, _)) => (
	    let 
	     val xypath = (completeTermPath x y g)
	     val yxpath = (completeTermPath y x g)
	     val xyLesss = transPath (tl xypath, hd xypath)
	     val yxLesss = transPath (tl yxpath, hd yxpath)
             val q = getprf (mergeLess ((mergeLess (edge, xyLesss)),yxLesss )) 
	    in 
	     raise (Contr (Thm ([q], Less.less_reflE )))
	    end  
	 )
	| _ =>  error "trans_tac/checkCompoents/handleContr: invalid Contradiction");

   (* Check each edge in neqEdges for contradiction.
      If there is a contradiction, call handleContr, otherwise do nothing. *)
    fun checkNeqEdges [] = () 
    |   checkNeqEdges (e::es) = 
        (case e of (Less (u, v, _)) => 
	  if (getIndex u ntc) = (getIndex v ntc) then handleContr e g
          else checkNeqEdges es
        | (NotEq (u, v, _)) =>  
	  if (getIndex u ntc) = (getIndex v ntc) then handleContr e g
          else checkNeqEdges es
        | _ => checkNeqEdges es)
     
 in if g = [] then () else checkNeqEdges neqEdges end;

(* *********************************************************************** *)
(*                                                                         *)
(* solvePartialOrder sign (asms,concl) :                                   *)
(* Sign.sg -> less list * Term.term -> proof list                          *)
(*                                                                         *)
(* Find proof if possible for partial orders.                              *)
(*                                                                         *)
(* *********************************************************************** *)

fun solvePartialOrder sign (asms, concl) =
 let 
  val (g1, g2, neqEdges) = buildGraphs (asms, [], [],[])
  val components = scc_term g1
  val ntc = indexNodes (indexComps components)
  val cg2 = evalcompgraph components g2 ntc
 in
 (* Check for contradiction within assumptions  *)
  checkComponents g2 components ntc neqEdges;
  let 
   val (subgoals, prf) = mkconcl_partial sign concl
   fun solve facts less =
       (case triv_solv less of None => findProof (g2, cg2, neqEdges, components, ntc) less
       | Some prf => prf )
  in
   map (solve asms) subgoals
  end
 end;

(* *********************************************************************** *)
(*                                                                         *)
(* solveTotalOrder sign (asms,concl) :                                     *)
(* Sign.sg -> less list * Term.term -> proof list                          *)
(*                                                                         *)
(* Find proof if possible for linear orders.                               *)
(*                                                                         *)
(* *********************************************************************** *)

fun solveTotalOrder sign (asms, concl) =
 let 
  val (g1, g2, neqEdges) = buildGraphs (asms, [], [],[])
  val components = scc_term g1   
  val ntc = indexNodes (indexComps components)
  val cg2 = evalcompgraph components g2 ntc
 in
  checkComponents g2 components ntc neqEdges;
  let 
   val (subgoals, prf) = mkconcl_linear sign concl
   fun solve facts less =
      (case triv_solv less of None => findProof (g2, cg2, neqEdges, components, ntc) less
      | Some prf => prf )
  in
   map (solve asms) subgoals
  end
 end;

  
(* partial_tac - solves linear/total orders *)
  
val partial_tac = SUBGOAL (fn (A, n, sign) =>
 let
  val rfrees = map Free (rename_wrt_term A (Logic.strip_params A))
  val Hs = map (fn H => subst_bounds (rfrees, H)) (Logic.strip_assums_hyp A)
  val C = subst_bounds (rfrees, Logic.strip_assums_concl A)
  val lesss = flat (ListPair.map (mkasm_partial sign) (Hs, 0 upto (length Hs - 1)))
  val prfs = solvePartialOrder sign (lesss, C);
  val (subgoals, prf) = mkconcl_partial sign C;
 in
  METAHYPS (fn asms =>
    let val thms = map (prove asms) prfs
    in rtac (prove thms prf) 1 end) n
 end
 handle Contr p => METAHYPS (fn asms => rtac (prove asms p) 1) n
      | Cannot  => no_tac
      );
       
(* linear_tac - solves linear/total orders *)
  
val linear_tac = SUBGOAL (fn (A, n, sign) =>
 let
  val rfrees = map Free (rename_wrt_term A (Logic.strip_params A))
  val Hs = map (fn H => subst_bounds (rfrees, H)) (Logic.strip_assums_hyp A)
  val C = subst_bounds (rfrees, Logic.strip_assums_concl A)
  val lesss = flat (ListPair.map (mkasm_linear sign) (Hs, 0 upto (length Hs - 1)))
  val prfs = solveTotalOrder sign (lesss, C);
  val (subgoals, prf) = mkconcl_linear sign C;
 in
  METAHYPS (fn asms =>
    let val thms = map (prove asms) prfs
    in rtac (prove thms prf) 1 end) n
 end
 handle Contr p => METAHYPS (fn asms => rtac (prove asms p) 1) n
      | Cannot  => no_tac);
       
end;

