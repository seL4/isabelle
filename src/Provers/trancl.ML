(*
  Title:	Transitivity reasoner for partial and linear orders
  Id:		$Id$
  Author:	Oliver Kutter
  Copyright:	TU Muenchen
*)

signature TRANCL_ARITH = 
sig

  (* theorems for transitive closure *)

  val r_into_trancl : thm
      (* (a,b) : r ==> (a,b) : r^+ *)
  val trancl_trans : thm
      (* [| (a,b) : r^+ ; (b,c) : r^+ |] ==> (a,c) : r^+ *)

  (* additional theorems for reflexive-transitive closure *)

  val rtrancl_refl : thm
      (* (a,a): r^* *)
  val r_into_rtrancl : thm
      (* (a,b) : r ==> (a,b) : r^* *)
  val trancl_into_rtrancl : thm
      (* (a,b) : r^+ ==> (a,b) : r^* *)
  val rtrancl_trancl_trancl : thm
      (* [| (a,b) : r^* ; (b,c) : r^+ |] ==> (a,c) : r^+ *)
  val trancl_rtrancl_trancl : thm
      (* [| (a,b) : r^+ ; (b,c) : r^* |] ==> (a,c) : r^+ *)
  val rtrancl_trans : thm
      (* [| (a,b) : r^* ; (b,c) : r^* |] ==> (a,c) : r^* *)

  val decomp: term ->  (term * term * term * string) option 

end;

signature TRANCL_TAC = 
sig
  val trancl_tac: int -> tactic;
  val rtrancl_tac: int -> tactic;
end;

functor Trancl_Tac_Fun (Cls : TRANCL_ARITH): TRANCL_TAC = 
struct

 
 datatype proof
  = Asm of int 
  | Thm of proof list * thm; 

 exception Cannot;

 fun prove asms = 
  let fun pr (Asm i) = nth_elem (i, asms)
  |       pr (Thm (prfs, thm)) = (map pr prfs) MRS thm
  in pr end;

  
(* Internal datatype for inequalities *)
datatype rel 
   = R      of term * term * proof  (* just a unknown relation R *)
   | Trans  of term * term * proof  (* R^+ *)
   | RTrans of term * term * proof; (* R^* *)
   
 (* Misc functions for datatype rel *)
fun lower (R (x, _, _)) = x
  | lower (Trans (x, _, _)) = x
  | lower (RTrans (x,_,_)) = x;

fun upper (R (_, y, _)) = y
  | upper (Trans (_, y, _)) = y
  | upper (RTrans (_,y,_)) = y;

fun getprf   (R (_, _, p)) = p
|   getprf   (Trans   (_, _, p)) = p
|   getprf   (RTrans (_,_, p)) = p; 
 
fun mkasm_trancl  Rel  (t, n) =
  case Cls.decomp t of
    Some (x, y, rel,r) => if rel aconv Rel then  
    
    (case r of
      "r"   => [Trans (x,y, Thm([Asm n], Cls.r_into_trancl))]
    | "r+"  => [Trans (x,y, Asm n)]
    | "r*"  => []
    | _     => error ("trancl_tac: unknown relation symbol"))
    else [] 
  | None => [];
  
fun mkasm_rtrancl Rel (t, n) =
  case Cls.decomp t of
   Some (x, y, rel, r) => if rel aconv Rel then
    (case r of
      "r"   => [ Trans (x,y, Thm([Asm n], Cls.r_into_trancl))]
    | "r+"  => [ Trans (x,y, Asm n)]
    | "r*"  => [ RTrans(x,y, Asm n)]
    | _     => error ("rtrancl_tac: unknown relation symbol" ))
   else [] 
  | None => [];

fun mkconcl_trancl  t =
  case Cls.decomp t of
    Some (x, y, rel, r) => (case r of
      "r+"  => (rel, Trans (x,y, Asm ~1), Asm 0)
    | _     => raise Cannot)
  | None => raise Cannot;

fun mkconcl_rtrancl  t =
  case Cls.decomp t of
    Some (x,  y, rel,r ) => (case r of
      "r+"  => (rel, Trans (x,y, Asm ~1),  Asm 0)
    | "r*"  => (rel, RTrans (x,y, Asm ~1), Asm 0)
    | _     => raise Cannot)
  | None => raise Cannot;

(* trans. cls. rules *)
fun makeStep (Trans (a,_,p), Trans(_,c,q))  = Trans (a,c, Thm ([p,q], Cls.trancl_trans))
(* refl. + trans. cls. rules *)
|   makeStep (RTrans (a,_,p), Trans(_,c,q))  = Trans (a,c, Thm ([p,q], Cls.rtrancl_trancl_trancl))
|   makeStep (Trans (a,_,p), RTrans(_,c,q))  = Trans (a,c, Thm ([p,q], Cls.trancl_rtrancl_trancl))   
|   makeStep (RTrans (a,_,p), RTrans(_,c,q))  = RTrans (a,c, Thm ([p,q], Cls.rtrancl_trans))  
|   makeStep (a,b) = error ("makeStep: internal error: undefined case\n"^(makestring a) ^"\n" ^ (makestring b));

(* ******************************************************************* *)
(*                                                                     *)
(* transPath (Clslist, Cls): (rel  list * rel) -> rel                  *)
(*                                                                     *)
(* If a path represented by a list of elements of type rel is found,   *)
(* this needs to be contracted to a single element of type rel.        *)
(* Prior to each transitivity step it is checked whether the step is   *)
(* valid.                                                              *)
(*                                                                     *)
(* ******************************************************************* *)

fun transPath ([],acc) = acc
|   transPath (x::xs,acc) = transPath (xs, makeStep(acc,x))
      
(* ********************************************************************* *)
(* Graph functions                                                       *)
(* ********************************************************************* *)

(* *********************************************************** *)
(* Functions for constructing graphs                           *)
(* *********************************************************** *)

fun addEdge (v,d,[]) = [(v,d)]
|   addEdge (v,d,((u,dl)::el)) = if v aconv u then ((v,d@dl)::el)
    else (u,dl):: (addEdge(v,d,el));
    
(* ********************************************************************** *)
(*                                                                        *)
(* mkGraph constructs from a list of objects of type rel  a graph g       *)
(*                                                                        *)
(* ********************************************************************** *)

fun mkGraph [] = ([],[])
|   mkGraph ys =  
 let
  fun buildGraph ([],g,zs) = (g,zs)
  |   buildGraph (x::xs, g, zs) = 
        case x of (Trans (_,_,_)) => 
	       buildGraph (xs, addEdge((upper x), [],(addEdge ((lower x),[((upper x),x)],g))), x::zs) 
	| _ => buildGraph (xs, addEdge((upper x), [],(addEdge ((lower x),[((upper x),x)],g))), zs)
in buildGraph (ys, [], []) end;

(* *********************************************************************** *)
(*                                                                         *)
(* adjacent g u : (''a * 'b list ) list -> ''a -> 'b list                  *)
(*                                                                         *)
(* List of successors of u in graph g                                      *)
(*                                                                         *)
(* *********************************************************************** *)
 
fun adjacent eq_comp ((v,adj)::el) u = 
    if eq_comp (u, v) then adj else adjacent eq_comp el u
|   adjacent _  []  _ = []  

(* *********************************************************************** *)
(*                                                                         *)
(* dfs eq_comp g u v:                                                      *)
(* ('a * 'a -> bool) -> ('a  *( 'a * rel) list) list ->                    *)
(* 'a -> 'a -> (bool * ('a * rel) list)                                    *) 
(*                                                                         *)
(* Depth first search of v from u.                                         *)
(* Returns (true, path(u, v)) if successful, otherwise (false, []).        *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs eq_comp g u v = 
 let 
    val pred = ref nil;
    val visited = ref nil;
    
    fun been_visited v = exists (fn w => eq_comp (w, v)) (!visited)
    
    fun dfs_visit u' = 
    let val _ = visited := u' :: (!visited)
    
    fun update (x,l) = let val _ = pred := (x,l) ::(!pred) in () end;
    
    in if been_visited v then () 
    else (app (fn (v',l) => if been_visited v' then () else (
       update (v',l); 
       dfs_visit v'; ()) )) (adjacent eq_comp g u')
     end
  in 
    dfs_visit u; 
    if (been_visited v) then (true, (!pred)) else (false , [])   
  end;

(* *********************************************************************** *)
(*                                                                         *)
(* transpose g:                                                            *)
(* (''a * ''a list) list -> (''a * ''a list) list                          *)
(*                                                                         *)
(* Computes transposed graph g' from g                                     *)
(* by reversing all edges u -> v to v -> u                                 *)
(*                                                                         *)
(* *********************************************************************** *)

fun transpose eq_comp g =
  let
   (* Compute list of reversed edges for each adjacency list *)
   fun flip (u,(v,l)::el) = (v,(u,l)) :: flip (u,el)
     | flip (_,nil) = nil
   
   (* Compute adjacency list for node u from the list of edges
      and return a likewise reduced list of edges.  The list of edges
      is searches for edges starting from u, and these edges are removed. *)
   fun gather (u,(v,w)::el) =
    let
     val (adj,edges) = gather (u,el)
    in
     if eq_comp (u, v) then (w::adj,edges)
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
 
(* *********************************************************************** *)
(*                                                                         *)
(* dfs_reachable eq_comp g u:                                              *)
(* (int * int list) list -> int -> int list                                *) 
(*                                                                         *)
(* Computes list of all nodes reachable from u in g.                       *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs_reachable eq_comp g u = 
 let
  (* List of vertices which have been visited. *)
  val visited  = ref nil;
  
  fun been_visited v = exists (fn w => eq_comp (w, v)) (!visited)

  fun dfs_visit g u  =
      let
   val _ = visited := u :: !visited
   val descendents =
       foldr (fn ((v,l),ds) => if been_visited v then ds
            else v :: dfs_visit g v @ ds)
        ( ((adjacent eq_comp g u)) ,nil)
   in  descendents end
 
 in u :: dfs_visit g u end;

(* *********************************************************************** *)
(*                                                                         *)
(* dfs_term_reachable g u:                                                  *)
(* (term * term list) list -> term -> term list                            *) 
(*                                                                         *)
(* Computes list of all nodes reachable from u in g.                       *)
(*                                                                         *)
(* *********************************************************************** *)

fun dfs_term_reachable g u = dfs_reachable (op aconv) g u;

(* ************************************************************************ *) 
(*                                                                          *)
(* findPath x y g: Term.term -> Term.term ->                                *)
(*                  (Term.term * (Term.term * rel list) list) ->            *) 
(*                  (bool, rel list)                                        *)
(*                                                                          *)
(*  Searches a path from vertex x to vertex y in Graph g, returns true and  *)
(*  the list of edges of edges if path is found, otherwise false and nil.   *)
(*                                                                          *)
(* ************************************************************************ *) 
 
fun findPath x y g = 
  let 
   val (found, tmp) =  dfs (op aconv) g x y ;
   val pred = map snd tmp;
	 
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
	  if u aconv x then [l] else (rev_path u) @ [l] 
	end
       
    in rev_path y end;
		
   in 

     
      if found then ( (found, (path x y) )) else (found,[])
   
     

   end;


fun findRtranclProof g tranclEdges subgoal = 
   (* simple case first *)
   case subgoal of (RTrans (x,y,_)) => if x aconv y then [Thm ([], Cls.rtrancl_refl)] else (
     let val (found, path) = findPath (lower subgoal) (upper subgoal) g
     in 
       if found then (
          let val path' = (transPath (tl path, hd path))
	  in 
	   
	    case path' of (Trans (_,_,p)) => [Thm ([p], Cls.trancl_into_rtrancl )] 
	    | _ => [getprf path']
	   
	  end
       )
       else raise Cannot
     end
   )
   
| (Trans (x,y,_)) => (
 
  let
   val Vx = dfs_term_reachable g x;
   val g' = transpose (op aconv) g;
   val Vy = dfs_term_reachable g' y;
   
   fun processTranclEdges [] = raise Cannot
   |   processTranclEdges (e::es) = 
          if (upper e) mem Vx andalso (lower e) mem Vx
	  andalso (upper e) mem Vy andalso (lower e) mem Vy
	  then (
	      
	   
	    if (lower e) aconv x then (
	      if (upper e) aconv y then (
	          [(getprf e)] 
	      )
	      else (
	          let 
		    val (found,path) = findPath (upper e) y g
		  in

		   if found then ( 
		       [getprf (transPath (path, e))]
		      ) else processTranclEdges es
		  
		  end 
	      )   
	    )
	    else if (upper e) aconv y then (
	       let val (xufound,xupath) = findPath x (lower e) g
	       in 
	       
	          if xufound then (
		  	    
		    let val xuRTranclEdge = transPath (tl xupath, hd xupath)
			    val xyTranclEdge = makeStep(xuRTranclEdge,e)
				
				in [getprf xyTranclEdge] end
				
	         ) else processTranclEdges es
	       
	       end
	    )
	    else ( 
	   
	        let val (xufound,xupath) = findPath x (lower e) g
		    val (vyfound,vypath) = findPath (upper e) y g
		 in 
		    if xufound then (
		         if vyfound then ( 
			    let val xuRTranclEdge = transPath (tl xupath, hd xupath)
			        val vyRTranclEdge = transPath (tl vypath, hd vypath)
				val xyTranclEdge = makeStep (makeStep(xuRTranclEdge,e),vyRTranclEdge)
				
				in [getprf xyTranclEdge] end
				
			 ) else processTranclEdges es
		    ) 
		    else processTranclEdges es
		 end
	    )
	  )
	  else processTranclEdges es;
   in processTranclEdges tranclEdges end )
| _ => raise Cannot

   
fun solveTrancl (asms, concl) = 
 let val (g,_) = mkGraph asms
 in
  let val (_, subgoal, _) = mkconcl_trancl concl
      val (found, path) = findPath (lower subgoal) (upper subgoal) g
  in

   
    if found then  [getprf (transPath (tl path, hd path))]
    else raise Cannot 
   
  end
 end;
  

 
fun solveRtrancl (asms, concl) = 
 let val (g,tranclEdges) = mkGraph asms
     val (_, subgoal, _) = mkconcl_rtrancl concl
in
  findRtranclProof g tranclEdges subgoal
end;
 
   
val trancl_tac =   SUBGOAL (fn (A, n) =>
 let
  val Hs = Logic.strip_assums_hyp A;
  val C = Logic.strip_assums_concl A;
  val (rel,subgoals, prf) = mkconcl_trancl C;
  val prems = flat (ListPair.map (mkasm_trancl rel) (Hs, 0 upto (length Hs - 1)))
  val prfs = solveTrancl (prems, C);

 in
  METAHYPS (fn asms =>
    let val thms = map (prove asms) prfs
    in rtac (prove thms prf) 1 end) n
 end
handle  Cannot  => no_tac);

 
 
val rtrancl_tac =   SUBGOAL (fn (A, n) =>
 let
  val Hs = Logic.strip_assums_hyp A;
  val C = Logic.strip_assums_concl A;
  val (rel,subgoals, prf) = mkconcl_rtrancl C;

  val prems = flat (ListPair.map (mkasm_rtrancl rel) (Hs, 0 upto (length Hs - 1)))
  val prfs = solveRtrancl (prems, C);
 in
  METAHYPS (fn asms =>
    let val thms = map (prove asms) prfs
    in rtac (prove thms prf) 1 end) n
 end
handle  Cannot  => no_tac);

end;

