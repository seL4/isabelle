(*  Title:      Pure/deriv.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Derivations (proof objects) and functions for examining them
*)

signature DERIV = 
  sig
  (*Object-level rules*)
  datatype orule = Subgoal of cterm
		 | Asm of int
		 | Res of deriv
		 | Equal of deriv
		 | Thm   of theory * string
		 | Other of deriv;

  val size : deriv -> int
  val drop : 'a mtree * int -> 'a mtree
  val linear : deriv -> deriv list
  val tree : deriv -> orule mtree
  end;  

structure Deriv : DERIV =
struct

fun size (Join(Theorem _, _)) = 1
  | size (Join(_, ders)) = foldl op+ (1, map size ders);

(*Conversion to linear format.  Children of a node are the LIST of inferences
  justifying ONE of the premises*)
fun rev_deriv (Join (rl, [])) 	= [Join(rl,[])]
  | rev_deriv (Join (Theorem arg, _)) 	= [Join(Theorem arg, [])]
  | rev_deriv (Join (Assumption arg, [der])) = 
              Join(Assumption arg,[]) :: rev_deriv der
  | rev_deriv (Join (Bicompose arg, [rder, sder])) =
	Join (Bicompose arg, linear rder) :: rev_deriv sder
  | rev_deriv (Join (_, [der]))	= rev_deriv der
  | rev_deriv (Join (rl, der::ders)) =	(*catch-all case; doubtful?*)
        Join(rl, flat (map linear ders)) :: rev_deriv der
and linear der 	= rev (rev_deriv der);


(*** Conversion of object-level proof trees ***)

(*Object-level rules*)
datatype orule = Subgoal of cterm
	       | Asm of int
               | Res of deriv
               | Equal of deriv
               | Thm   of theory * string
               | Other of deriv;

(*At position i, splice in value x, removing ngoal elements*)
fun splice (i,x,ngoal,prfs) =
    let val prfs0 = take(i-1,prfs)
        and prfs1 = drop(i-1,prfs)
        val prfs2 = Join (x, take(ngoal, prfs1)) :: drop(ngoal, prfs1)
    in  prfs0 @ prfs2  end;

(*Deletes trivial uses of Equal_elim; hides derivations of Theorems*)
fun simp_deriv (Join (Equal_elim, [Join (Rewrite_cterm _, []), der])) =
      simp_deriv der
  | simp_deriv (Join (Equal_elim, [Join (Reflexive _, []), der])) =
      simp_deriv der
  | simp_deriv (Join (rule as Theorem arg, [_])) = Join (rule, [])
  | simp_deriv (Join (rule, ders)) = Join (rule, map simp_deriv ders);

(*Proof term is an equality: first premise of equal_elim.
  Attempt to decode proof terms made by Drule.goals_conv.
  Subgoal numbers are returned; they are wrong if original subgoal
	had flexflex pairs!
  NEGATIVE i means "could affect all subgoals starting from i"*)
fun scan_equals (i, Join (Combination, 
			   [Join (Combination, [_, der1]), der2])) =
    (case der1 of	(*ignore trivial cases*)
         Join (Reflexive _, _)      => scan_equals (i+1, der2)
       | Join (Rewrite_cterm _, []) => scan_equals (i+1, der2)
       | Join (Rewrite_cterm _, _)  => (i,der1) :: scan_equals (i+1, der2)
       | _ (*impossible in gconv*)  => [])
  | scan_equals (i, Join (Reflexive _, [])) = []
  | scan_equals (i, Join (Rewrite_cterm _, [])) = []
	(*Anything else could affect ALL following goals*)
  | scan_equals (i, der) = [(~i,der)];

(*Record uses of equality reasoning on 1 or more subgoals*)
fun update_equals ((i,der), prfs) = 
      if i>0 then splice (i, Equal (simp_deriv der), 1, prfs)
      else take (~i-1, prfs) @
	   map (fn prf => Join (Equal (simp_deriv der), [prf])) 
	       (drop (~i-1, prfs));

fun delift (Join (Lift_rule _, [der])) = der
  | delift der = der;

(*Conversion to an object-level proof tree.
  Uses embedded Lift_rules to "annotate" the proof tree with subgoals;
    -- assumes that Lift_rule never occurs except with resolution
    -- may contain Vars that, in fact, are instantiated in that step*)
fun tree_aux (Join (Trivial ct, []), prfs) = Join(Subgoal ct, prfs)
  | tree_aux (Join (Assumption(i,_), [der]), prfs) = 
      tree_aux (der, splice (i, Asm i, 0, prfs))
  | tree_aux (Join (Equal_elim, [der1,der2]), prfs) = 
      tree_aux (der2, foldr update_equals (scan_equals (1, der1), prfs))
  | tree_aux (Join (Bicompose (match,true,i,ngoal,env), ders), prfs) =
		(*change eresolve_tac to proof by assumption*)
      tree_aux (Join (Assumption(i, Some env), 
			 [Join (Bicompose (match,false,i,ngoal,env), ders)]),
		   prfs)
  | tree_aux (Join (Lift_rule (ct,i), [der]), prfs) = 
      tree_aux (der, splice (i, Subgoal ct, 1, prfs))
  | tree_aux (Join (Bicompose arg, 
		       [Join (Instantiate _, [rder]), sder]), prfs) =
		(*Ignore Instantiate*)
      tree_aux (Join (Bicompose arg, [rder, sder]), prfs)
  | tree_aux (Join (Bicompose arg, 
		       [Join (Lift_rule larg, [rder]), sder]), prfs) =
		(*Move Lift_rule: to make a Subgoal on the result*)
      tree_aux (Join (Bicompose arg, [rder, 
					 Join(Lift_rule larg, [sder])]), prfs)
  | tree_aux (Join (Bicompose (match,ef,i,ngoal,env), 
		       [Join (Bicompose (match',ef',i',ngoal',env'),
			      [der1,der2]), 
			der3]), prfs) =
		(*associate resolutions to the right*)
      tree_aux (Join (Bicompose (match', ef', i'+i-1, ngoal', env'), 
			 [delift der1,	(*This Lift_rule would be wrong!*)
			  Join (Bicompose (match, ef, i, ngoal-ngoal'+1, env),
				[der2, der3])]), prfs)
  | tree_aux (Join (Bicompose (arg as (_,_,i,ngoal,_)), 
		       [rder, sder]), prfs) =
		(*resolution with basic rule/assumption -- we hope!*)
      tree_aux (sder, splice (i, Res (simp_deriv rder), ngoal, prfs))
  | tree_aux (Join (Theorem arg, _), prfs)	= Join(Thm arg, prfs)
  | tree_aux (Join (_, [der]), prfs)	= tree_aux (der,prfs)
  | tree_aux (der, prfs) = Join(Other (simp_deriv der), prfs);


fun tree der = tree_aux (der,[]);

(*Currently declared at end, to avoid conflicting with library's drop
  Can put it after "size" once we switch to List.drop*)
fun drop (der,0) = der
  | drop (Join (_, der::_), n) = drop (der, n-1);

end;


(*We do NOT open this structure*)
