(*  Title: 	LK/lk.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Tactics and lemmas for lk.thy (thanks also to Philippe de Groote)  
*)

open LK;

(*Higher precedence than := facilitates use of references*)
infix 4 add_safes add_unsafes;

(*Cut and thin, replacing the right-side formula*)
fun cutR_tac (sP: string) i = 
    res_inst_tac [ ("P",sP) ] cut i  THEN  rtac thinR i;

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac (sP: string) i = 
    res_inst_tac [ ("P",sP) ] cut i  THEN  rtac thinL (i+1);


(** If-and-only-if rules **)
qed_goalw "iffR" LK.thy [iff_def]
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P <-> Q, $F"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[conjR,impR]) 1)) ]);

qed_goalw "iffL" LK.thy [iff_def]
   "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P <-> Q, $G |- $E"
 (fn prems=> [ (REPEAT (resolve_tac (prems@[conjL,impL,basic]) 1)) ]);

qed_goalw "TrueR" LK.thy [True_def]
    "$H |- $E, True, $F"
 (fn _=> [ rtac impR 1, rtac basic 1 ]);


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

qed_goal "allL_thin" LK.thy 
    "$H, P(x), $G |- $E ==> $H, ALL x.P(x), $G |- $E"
 (fn prems=> [ (rtac allL 1), (rtac thinL 1), (resolve_tac prems 1) ]);

qed_goal "exR_thin" LK.thy 
    "$H |- $E, P(x), $F ==> $H |- $E, EX x.P(x), $F"
 (fn prems=> [ (rtac exR 1), (rtac thinR 1), (resolve_tac prems 1) ]);

(* Symmetry of equality in hypotheses *)
qed_goal "symL" LK.thy 
    "$H, $G, B = A |- $E ==> $H, A = B, $G |- $E" 
 (fn prems=>
  [ (rtac cut 1),
    (rtac thinL 2),
    (resolve_tac prems 2),
    (resolve_tac [basic RS sym] 1) ]);


(**** Theorem Packs ****)

datatype pack = Pack of thm list * thm list;

(*A theorem pack has the form  (safe rules, unsafe rules)
  An unsafe rule is incomplete or introduces variables in subgoals,
  and is tried only when the safe rules are not applicable.  *)

fun less (rl1,rl2) = (nprems_of rl1) < (nprems_of rl2);

val empty_pack = Pack([],[]);

fun (Pack(safes,unsafes)) add_safes ths   = 
    Pack(sort less (ths@safes), unsafes);

fun (Pack(safes,unsafes)) add_unsafes ths = 
    Pack(safes, sort less (ths@unsafes));

(*The rules of LK*)
val prop_pack = empty_pack add_safes 
	        [basic, refl, conjL, conjR, disjL, disjR, impL, impR, 
		 notL, notR, iffL, iffR];

val LK_pack = prop_pack add_safes   [allR, exL] 
			add_unsafes [allL_thin, exR_thin];

val LK_dup_pack = prop_pack add_safes   [allR, exL] 
			    add_unsafes [allL, exR];



(*Returns the list of all formulas in the sequent*)
fun forms_of_seq (Const("Seqof",_) $ P $ u) = P :: forms_of_seq u
  | forms_of_seq (H $ u) = forms_of_seq u
  | forms_of_seq _ = [];

(*Tests whether two sequences (left or right sides) could be resolved.
  seqp is a premise (subgoal), seqc is a conclusion of an object-rule.
  Assumes each formula in seqc is surrounded by sequence variables
  -- checks that each concl formula looks like some subgoal formula.
  It SHOULD check order as well, using recursion rather than forall/exists*)
fun could_res (seqp,seqc) =
      forall (fn Qc => exists (fn Qp => could_unify (Qp,Qc)) 
                              (forms_of_seq seqp))
             (forms_of_seq seqc);

(*Tests whether two sequents G|-H could be resolved, comparing each side.*)
fun could_resolve_seq (prem,conc) =
  case (prem,conc) of
      (_ $ Abs(_,_,leftp) $ Abs(_,_,rightp),
       _ $ Abs(_,_,leftc) $ Abs(_,_,rightc)) =>
	  could_res (leftp,leftc)  andalso  could_res (rightp,rightc)
    | _ => false;


(*Like filt_resolve_tac, using could_resolve_seq
  Much faster than resolve_tac when there are many rules.
  Resolve subgoal i using the rules, unless more than maxr are compatible. *)
fun filseq_resolve_tac rules maxr = SUBGOAL(fn (prem,i) =>
  let val rls = filter_thms could_resolve_seq (maxr+1, prem, rules)
  in  if length rls > maxr  then  no_tac  else resolve_tac rls i
  end);


(*Predicate: does the rule have n premises? *)
fun has_prems n rule =  (nprems_of rule = n);

(*Continuation-style tactical for resolution.
  The list of rules is partitioned into 0, 1, 2 premises.
  The resulting tactic, gtac, tries to resolve with rules.
  If successful, it recursively applies nextac to the new subgoals only.
  Else fails.  (Treatment of goals due to Ph. de Groote) 
  Bind (RESOLVE_THEN rules) to a variable: it preprocesses the rules. *)

(*Takes rule lists separated in to 0, 1, 2, >2 premises.
  The abstraction over state prevents needless divergence in recursion.
  The 9999 should be a parameter, to delay treatment of flexible goals. *)
fun RESOLVE_THEN rules =
  let val [rls0,rls1,rls2] = partition_list has_prems 0 2 rules;
      fun tac nextac i = STATE (fn state =>  
	  filseq_resolve_tac rls0 9999 i 
	  ORELSE
	  (DETERM(filseq_resolve_tac rls1 9999 i) THEN  TRY(nextac i))
	  ORELSE
	  (DETERM(filseq_resolve_tac rls2 9999 i) THEN  TRY(nextac(i+1))
					THEN  TRY(nextac i)) )
  in  tac  end;


(*repeated resolution applied to the designated goal*)
fun reresolve_tac rules = 
  let val restac = RESOLVE_THEN rules;  (*preprocessing done now*)
      fun gtac i = restac gtac i
  in  gtac  end; 

(*tries the safe rules repeatedly before the unsafe rules. *)
fun repeat_goal_tac (Pack(safes,unsafes)) = 
  let val restac  =    RESOLVE_THEN safes
      and lastrestac = RESOLVE_THEN unsafes;
      fun gtac i = restac gtac i  ORELSE  lastrestac gtac i
  in  gtac  end; 


(*Tries safe rules only*)
fun safe_goal_tac (Pack(safes,unsafes)) = reresolve_tac safes;

(*Tries a safe rule or else a unsafe rule.  Single-step for tracing. *)
fun step_tac (thm_pack as Pack(safes,unsafes)) =
    safe_goal_tac thm_pack  ORELSE'
    filseq_resolve_tac unsafes 9999;


(* Tactic for reducing a goal, using Predicate Calculus rules.
   A decision procedure for Propositional Calculus, it is incomplete
   for Predicate-Calculus because of allL_thin and exR_thin.  
   Fails if it can do nothing.      *)
fun pc_tac thm_pack = SELECT_GOAL (DEPTH_SOLVE (repeat_goal_tac thm_pack 1));

(*The following two tactics are analogous to those provided by 
  Provers/classical.  In fact, pc_tac is usually FASTER than fast_tac!*)
fun fast_tac thm_pack =
  SELECT_GOAL (DEPTH_SOLVE (step_tac thm_pack 1));

fun best_tac thm_pack  = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, size_of_thm) 
	       (step_tac thm_pack 1));

(** Contraction.  Useful since some rules are not complete. **)

qed_goal "conR" LK.thy 
    "$H |- $E, P, $F, P ==> $H |- $E, P, $F"
 (fn prems=>
  [ (rtac cut 1), (REPEAT (resolve_tac (prems@[basic]) 1)) ]);

qed_goal "conL" LK.thy 
    "$H, P, $G, P |- $E ==> $H, P, $G |- $E"
 (fn prems=>
  [ (rtac cut 1), (REPEAT (resolve_tac (prems@[basic]) 1)) ]);
