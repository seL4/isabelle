(*  Title: 	astar
    ID:         $Id$
    Author: 	Norbert Voelker, FernUniversitaet Hagen
    Remarks:    Implementation of A*-like proof procedure by modification
		of the existing code for BEST_FIRST and best_tac so that the 
		current level of search is taken into account.
*)		
		
(*Insertion into priority queue of states, marked with level *)
fun insert_with_level (lnth: int*int*thm, []) = [lnth]
  | insert_with_level ((l,m,th), (l',n,th')::nths) = 
      if  n<m then (l',n,th') :: insert_with_level ((l,m,th), nths)
      else if  n=m andalso eq_thm(th,th')
              then (l',n,th')::nths
              else (l,m,th)::(l',n,th')::nths;

(*For creating output sequence*)
fun some_of_list []     = None
  | some_of_list (x::l) = Some (x, Sequence.seqof (fn () => some_of_list l));

infix THEN_ASTAR;
val trace_ASTAR = ref false; 

fun tf0 THEN_ASTAR (satp, costf, tac) = 
  let val tf = tracify trace_ASTAR tac;   
      fun bfs (news,nprfs,level) =
      let fun cost thm = (level,costf level thm,thm)
      in (case  partition satp news  of
            ([],nonsats) 
		 => next (foldr insert_with_level (map cost nonsats, nprfs))
          | (sats,_)  => some_of_list sats)
      end and    
      next []  = None
        | next ((level,n,prf)::nprfs)  =
            (if !trace_ASTAR 
               then writeln("level = " ^ string_of_int level ^
			 "  cost = " ^ string_of_int n ^ 
                         "  queue length =" ^ string_of_int (length nprfs))  
               else ();
             bfs (Sequence.list_of_s (tf prf), nprfs,level+1))
      fun tf st = bfs (Sequence.list_of_s (tf0 st), [], 0)
  in traced_tac tf end;

(*Ordinary ASTAR, with no initial tactic*)
fun ASTAR (satp,costf) tac = all_tac THEN_ASTAR (satp,costf,tac);

(* ASTAR with weight weight_ASTAR as a classical prover *) 
val weight_ASTAR = ref 5; 

fun astar_tac cs = 
  SELECT_GOAL ( ASTAR (has_fewer_prems 1
	      , fn level =>(fn thm =>size_of_thm thm + !weight_ASTAR *level)) 
	      (step_tac cs 1));

fun slow_astar_tac cs = 
  SELECT_GOAL ( ASTAR (has_fewer_prems 1
	      , fn level =>(fn thm =>size_of_thm thm + !weight_ASTAR *level)) 
	      (slow_step_tac cs 1));

