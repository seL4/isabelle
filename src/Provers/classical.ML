(*  Title: 	Provers/classical
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Theorem prover for classical reasoning, including predicate calculus, set
theory, etc.

Rules must be classified as intr, elim, safe, hazardous.

A rule is unsafe unless it can be applied blindly without harmful results.
For a rule to be safe, its premises and conclusion should be logically
equivalent.  There should be no variables in the premises that are not in
the conclusion.
*)

signature CLASSICAL_DATA =
  sig
  val mp: thm    		(* [| P-->Q;  P |] ==> Q *)
  val not_elim: thm		(* [| ~P;  P |] ==> R *)
  val swap: thm			(* ~P ==> (~Q ==> P) ==> Q *)
  val sizef : thm -> int	(* size function for BEST_FIRST *)
  val hyp_subst_tacs: (int -> tactic) list
  end;

(*Higher precedence than := facilitates use of references*)
infix 4 addSIs addSEs addSDs addIs addEs addDs;


signature CLASSICAL =
  sig
  type claset
  val empty_cs: claset
  val addDs : claset * thm list -> claset
  val addEs : claset * thm list -> claset
  val addIs : claset * thm list -> claset
  val addSDs: claset * thm list -> claset
  val addSEs: claset * thm list -> claset
  val addSIs: claset * thm list -> claset
  val print_cs: claset -> unit
  val rep_claset: claset -> 
      {safeIs: thm list, safeEs: thm list, hazIs: thm list, hazEs: thm list}
  val best_tac : claset -> int -> tactic
  val chain_tac : int -> tactic
  val contr_tac : int -> tactic
  val eq_mp_tac: int -> tactic
  val fast_tac : claset -> int -> tactic
  val joinrules : thm list * thm list -> (bool * thm) list
  val mp_tac: int -> tactic
  val safe_tac : claset -> tactic
  val safe_step_tac : claset -> int -> tactic
  val slow_step_tac : claset -> int -> tactic
  val slow_best_tac : claset -> int -> tactic
  val slow_tac : claset -> int -> tactic
  val step_tac : claset -> int -> tactic
  val swapify : thm list -> thm list
  val swap_res_tac : thm list -> int -> tactic
  val inst_step_tac : claset -> int -> tactic
  end;


functor ClassicalFun(Data: CLASSICAL_DATA): CLASSICAL = 
struct

local open Data in

(** Useful tactics for classical reasoning **)

val imp_elim = make_elim mp;

(*Solve goal that assumes both P and ~P. *)
val contr_tac = eresolve_tac [not_elim]  THEN'  assume_tac;

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac i = eresolve_tac ([not_elim,imp_elim]) i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = ematch_tac ([not_elim,imp_elim]) i  THEN  eq_assume_tac i;

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [swap]);

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac rls = 
    let fun addrl (rl,brls) = (false, rl) :: (true, rl RSN (2,swap)) :: brls
    in  assume_tac 	ORELSE' 
	contr_tac 	ORELSE' 
        biresolve_tac (foldr addrl (rls,[]))
    end;

(*Given assumption P-->Q, reduces subgoal Q to P [deletes the implication!] *)
fun chain_tac i =
    eresolve_tac [imp_elim] i  THEN
    (assume_tac (i+1)  ORELSE  contr_tac (i+1));

(*** Classical rule sets ***)

type netpair = (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net;

datatype claset =
  CS of {safeIs		: thm list,
	 safeEs		: thm list,
	 hazIs		: thm list,
	 hazEs		: thm list,
	 safe0_netpair	: netpair,
	 safep_netpair	: netpair,
	 haz_netpair  	: netpair};

fun rep_claset (CS{safeIs,safeEs,hazIs,hazEs,...}) = 
    {safeIs=safeIs, safeEs=safeEs, hazIs=hazIs, hazEs=hazEs};

(*For use with biresolve_tac.  Combines intrs with swap to catch negated
  assumptions; pairs elims with true; sorts. *)
fun joinrules (intrs,elims) =  
  sort lessb 
    (map (pair true) (elims @ swapify intrs)  @
     map (pair false) intrs);

(*Make a claset from the four kinds of rules*)
fun make_cs {safeIs,safeEs,hazIs,hazEs} =
  let val (safe0_brls, safep_brls) = (*0 subgoals vs 1 or more*)
          take_prefix (fn brl => subgoals_of_brl brl=0)
             (joinrules(safeIs, safeEs))
  in CS{safeIs = safeIs, 
        safeEs = safeEs,
	hazIs = hazIs,
	hazEs = hazEs,
	safe0_netpair = build_netpair safe0_brls,
	safep_netpair = build_netpair safep_brls,
	haz_netpair = build_netpair (joinrules(hazIs, hazEs))}
  end;

(*** Manipulation of clasets ***)

val empty_cs = make_cs{safeIs=[], safeEs=[], hazIs=[], hazEs=[]};

fun print_cs (CS{safeIs,safeEs,hazIs,hazEs,...}) =
 (writeln"Introduction rules";  prths hazIs;
  writeln"Safe introduction rules";  prths safeIs;
  writeln"Elimination rules";  prths hazEs;
  writeln"Safe elimination rules";  prths safeEs;
  ());

fun (CS{safeIs,safeEs,hazIs,hazEs,...}) addSIs ths =
  make_cs {safeIs=ths@safeIs, safeEs=safeEs, hazIs=hazIs, hazEs=hazEs};

fun (CS{safeIs,safeEs,hazIs,hazEs,...}) addSEs ths =
  make_cs {safeIs=safeIs, safeEs=ths@safeEs, hazIs=hazIs, hazEs=hazEs};

fun cs addSDs ths = cs addSEs (map make_elim ths);

fun (CS{safeIs,safeEs,hazIs,hazEs,...}) addIs ths =
  make_cs {safeIs=safeIs, safeEs=safeEs, hazIs=ths@hazIs, hazEs=hazEs};

fun (CS{safeIs,safeEs,hazIs,hazEs,...}) addEs ths =
  make_cs {safeIs=safeIs, safeEs=safeEs, hazIs=hazIs, hazEs=ths@hazEs};

fun cs addDs ths = cs addEs (map make_elim ths);

(*** Simple tactics for theorem proving ***)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun safe_step_tac (CS{safe0_netpair,safep_netpair,...}) = 
  FIRST' [eq_assume_tac,
	  eq_mp_tac,
	  bimatch_from_nets_tac safe0_netpair,
	  FIRST' hyp_subst_tacs,
	  bimatch_from_nets_tac safep_netpair] ;

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun safe_tac cs = DETERM (REPEAT_FIRST (safe_step_tac cs));

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac (CS{safe0_netpair,safep_netpair,...}) =
  assume_tac 			  APPEND' 
  contr_tac 			  APPEND' 
  biresolve_from_nets_tac safe0_netpair APPEND' 
  biresolve_from_nets_tac safep_netpair;

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac (cs as (CS{haz_netpair,...})) i = 
  FIRST [safe_tac cs,
         inst_step_tac cs i,
         biresolve_from_nets_tac haz_netpair i];

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac (cs as (CS{haz_netpair,...})) i = 
    safe_tac cs ORELSE 
    (inst_step_tac cs i APPEND biresolve_from_nets_tac haz_netpair i);

(*** The following tactics all fail unless they solve one goal ***)

(*Dumb but fast*)
fun fast_tac cs = SELECT_GOAL (DEPTH_SOLVE (step_tac cs 1));

(*Slower but smarter than fast_tac*)
fun best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (step_tac cs 1));

fun slow_tac cs = SELECT_GOAL (DEPTH_SOLVE (slow_step_tac cs 1));

fun slow_best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (slow_step_tac cs 1));

end; 
end;
