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

infix 1 THEN_MAYBE;

signature CLASSICAL_DATA =
  sig
  val mp	: thm    	(* [| P-->Q;  P |] ==> Q *)
  val not_elim	: thm		(* [| ~P;  P |] ==> R *)
  val classical	: thm		(* (~P ==> P) ==> P *)
  val sizef 	: thm -> int	(* size function for BEST_FIRST *)
  val hyp_subst_tacs: (int -> tactic) list
  end;

(*Higher precedence than := facilitates use of references*)
infix 4 addSIs addSEs addSDs addIs addEs addDs 
        setwrapper compwrapper addbefore addafter;


signature CLASSICAL =
  sig
  type claset
  val empty_cs		: claset
  val addDs 		: claset * thm list -> claset
  val addEs 		: claset * thm list -> claset
  val addIs 		: claset * thm list -> claset
  val addSDs		: claset * thm list -> claset
  val addSEs		: claset * thm list -> claset
  val addSIs		: claset * thm list -> claset
  val setwrapper 	: claset * (tactic->tactic) -> claset
  val compwrapper 	: claset * (tactic->tactic) -> claset
  val addbefore 	: claset * tactic -> claset
  val addafter 		: claset * tactic -> claset

  val print_cs		: claset -> unit
  val rep_claset	: claset -> {safeIs: thm list, safeEs: thm list, 
				     hazIs: thm list, hazEs: thm list,
				     wrapper: tactic -> tactic}
  val getwrapper	: claset -> tactic -> tactic
  val THEN_MAYBE	: tactic * tactic -> tactic

  val best_tac 		: claset -> int -> tactic
  val contr_tac 	: int -> tactic
  val depth_tac		: claset -> int -> int -> tactic
  val deepen_tac	: claset -> int -> int -> tactic
  val dup_elim		: thm -> thm
  val dup_intr		: thm -> thm
  val dup_step_tac	: claset -> int -> tactic
  val eq_mp_tac		: int -> tactic
  val fast_tac 		: claset -> int -> tactic
  val haz_step_tac 	: claset -> int -> tactic
  val joinrules 	: thm list * thm list -> (bool * thm) list
  val mp_tac		: int -> tactic
  val safe_tac 		: claset -> tactic
  val safe_step_tac 	: claset -> int -> tactic
  val slow_step_tac 	: claset -> int -> tactic
  val slow_best_tac 	: claset -> int -> tactic
  val slow_tac 		: claset -> int -> tactic
  val step_tac 		: claset -> int -> tactic
  val swap		: thm                 (* ~P ==> (~Q ==> P) ==> Q *)
  val swapify 		: thm list -> thm list
  val swap_res_tac 	: thm list -> int -> tactic
  val inst_step_tac 	: claset -> int -> tactic
  val inst0_step_tac 	: claset -> int -> tactic
  val instp_step_tac 	: claset -> int -> tactic
  end;


functor ClassicalFun(Data: CLASSICAL_DATA): CLASSICAL = 
struct

local open Data in

(** Useful tactics for classical reasoning **)

val imp_elim = make_elim mp;

(*Solve goal that assumes both P and ~P. *)
val contr_tac = eresolve_tac [not_elim]  THEN'  assume_tac;

(*Finds P-->Q and P in the assumptions, replaces implication by Q.
  Could do the same thing for P<->Q and P... *)
fun mp_tac i = eresolve_tac [not_elim, imp_elim] i  THEN  assume_tac i;

(*Like mp_tac but instantiates no variables*)
fun eq_mp_tac i = ematch_tac [not_elim, imp_elim] i  THEN  eq_assume_tac i;

val swap = rule_by_tactic (etac thin_rl 1) (not_elim RS classical);

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

(*Duplication of hazardous rules, for complete provers*)
fun dup_intr th = standard (th RS classical);

fun dup_elim th = th RSN (2, revcut_rl) |> assumption 2 |> Sequence.hd |> 
                  rule_by_tactic (TRYALL (etac revcut_rl));

(*** Classical rule sets ***)

type netpair = (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net;

datatype claset =
  CS of {safeIs		: thm list,		(*safe introduction rules*)
	 safeEs		: thm list,		(*safe elimination rules*)
	 hazIs		: thm list,		(*unsafe introduction rules*)
	 hazEs		: thm list,		(*unsafe elimination rules*)
	 wrapper	: tactic->tactic,	(*for transforming step_tac*)
	 safe0_netpair	: netpair,		(*nets for trivial cases*)
	 safep_netpair	: netpair,		(*nets for >0 subgoals*)
	 haz_netpair  	: netpair,		(*nets for unsafe rules*)
	 dup_netpair	: netpair};		(*nets for duplication*)

fun rep_claset (CS{safeIs,safeEs,hazIs,hazEs,wrapper,...}) = 
    {safeIs=safeIs, safeEs=safeEs, hazIs=hazIs, hazEs=hazEs, wrapper=wrapper};

fun getwrapper (CS{wrapper,...}) = wrapper;

(*For use with biresolve_tac.  Combines intr rules with swap to handle negated
  assumptions.  Pairs elim rules with true.  Sorts the list of pairs by 
  the number of new subgoals generated. *)
fun joinrules (intrs,elims) =  
  sort lessb 
    (map (pair true) (elims @ swapify intrs)  @
     map (pair false) intrs);

val build = build_netpair(Net.empty,Net.empty);

(*Make a claset from the four kinds of rules*)
fun make_cs {safeIs,safeEs,hazIs,hazEs,wrapper} =
  let val (safe0_brls, safep_brls) = (*0 subgoals vs 1 or more*)
          take_prefix (fn brl => subgoals_of_brl brl=0)
             (joinrules(safeIs, safeEs))
  in CS{safeIs = safeIs, 
        safeEs = safeEs,
	hazIs = hazIs,
	hazEs = hazEs,
	wrapper = wrapper,
	safe0_netpair = build safe0_brls,
	safep_netpair = build safep_brls,
	haz_netpair = build (joinrules(hazIs, hazEs)),
	dup_netpair = build (joinrules(map dup_intr hazIs, 
				       map dup_elim hazEs))}
  end;

(*** Manipulation of clasets ***)

val empty_cs = make_cs{safeIs=[], safeEs=[], hazIs=[], hazEs=[], wrapper=I};

fun print_cs (CS{safeIs,safeEs,hazIs,hazEs,...}) =
 (writeln"Introduction rules";  prths hazIs;
  writeln"Safe introduction rules";  prths safeIs;
  writeln"Elimination rules";  prths hazEs;
  writeln"Safe elimination rules";  prths safeEs;
  ());

(** Adding new (un)safe introduction or elimination rules 
    In case of overlap, new rules are tried BEFORE old ones
**)

fun (CS{safeIs,safeEs,hazIs,hazEs,wrapper,...}) addSIs ths =
  make_cs {safeIs=ths@safeIs, 
	   safeEs=safeEs, hazIs=hazIs, hazEs=hazEs, wrapper=wrapper};

fun (CS{safeIs,safeEs,hazIs,hazEs,wrapper,...}) addSEs ths =
  make_cs {safeEs=ths@safeEs, 
	   safeIs=safeIs, hazIs=hazIs, hazEs=hazEs, wrapper=wrapper};

fun cs addSDs ths = cs addSEs (map make_elim ths);

fun (CS{safeIs,safeEs,hazIs,hazEs,wrapper,...}) addIs ths =
  make_cs {hazIs=ths@hazIs, 
	   safeIs=safeIs, safeEs=safeEs, hazEs=hazEs, wrapper=wrapper};

fun (CS{safeIs,safeEs,hazIs,hazEs,wrapper,...}) addEs ths =
  make_cs {hazEs=ths@hazEs,
	   safeIs=safeIs, safeEs=safeEs, hazIs=hazIs, wrapper=wrapper};

fun cs addDs ths = cs addEs (map make_elim ths);

(** Setting or modifying the wrapper tactical **)

(*Set a new wrapper*)
fun (CS{safeIs,safeEs,hazIs,hazEs,...}) setwrapper wrapper =
  make_cs {wrapper=wrapper,
	   safeIs=safeIs, safeEs=safeEs, hazIs=hazIs, hazEs=hazEs};

(*Compose a tactical with the existing wrapper*)
fun cs compwrapper wrapper' = cs setwrapper (wrapper' o getwrapper cs);

(*Execute tac1, but only execute tac2 if there are at least as many subgoals
  as before.  This ensures that tac2 is only applied to an outcome of tac1.*)
fun tac1 THEN_MAYBE tac2 = 
  STATE (fn state =>
	 tac1  THEN  
	 COND (has_fewer_prems (nprems_of state)) all_tac tac2);

(*Cause a tactic to be executed before/after the step tactic*)
fun cs addbefore tac2 = cs compwrapper (fn tac1 => tac2 THEN_MAYBE tac1);
fun cs addafter tac2  = cs compwrapper (fn tac1 => tac1 THEN_MAYBE tac2);



(*** Simple tactics for theorem proving ***)

(*Attack subgoals using safe inferences -- matching, not resolution*)
fun safe_step_tac (CS{safe0_netpair,safep_netpair,...}) = 
  FIRST' [eq_assume_tac,
	  eq_mp_tac,
	  bimatch_from_nets_tac safe0_netpair,
	  FIRST' hyp_subst_tacs,
	  bimatch_from_nets_tac safep_netpair] ;

(*Repeatedly attack subgoals using safe inferences -- it's deterministic!*)
fun safe_tac cs = REPEAT_DETERM_FIRST (safe_step_tac cs);

(*But these unsafe steps at least solve a subgoal!*)
fun inst0_step_tac (CS{safe0_netpair,safep_netpair,...}) =
  assume_tac 			  APPEND' 
  contr_tac 			  APPEND' 
  biresolve_from_nets_tac safe0_netpair;

(*These are much worse since they could generate more and more subgoals*)
fun instp_step_tac (CS{safep_netpair,...}) =
  biresolve_from_nets_tac safep_netpair;

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac cs = inst0_step_tac cs APPEND' instp_step_tac cs;

fun haz_step_tac (CS{haz_netpair,...}) = 
  biresolve_from_nets_tac haz_netpair;

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac cs i = 
  getwrapper cs 
    (FIRST [safe_tac cs, inst_step_tac cs i, haz_step_tac cs i]);

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac cs i = 
  getwrapper cs 
    (safe_tac cs ORELSE (inst_step_tac cs i APPEND haz_step_tac cs i));

(*** The following tactics all fail unless they solve one goal ***)

(*Dumb but fast*)
fun fast_tac cs = SELECT_GOAL (DEPTH_SOLVE (step_tac cs 1));

(*Slower but smarter than fast_tac*)
fun best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (step_tac cs 1));

fun slow_tac cs = SELECT_GOAL (DEPTH_SOLVE (slow_step_tac cs 1));

fun slow_best_tac cs = 
  SELECT_GOAL (BEST_FIRST (has_fewer_prems 1, sizef) (slow_step_tac cs 1));


(*** Complete tactic, loosely based upon LeanTaP.  This tactic is the outcome
  of much experimentation!  Changing APPEND to ORELSE below would prove
  easy theorems faster, but loses completeness -- and many of the harder
  theorems such as 43. ***)

(*Non-deterministic!  Could always expand the first unsafe connective.
  That's hard to implement and did not perform better in experiments, due to
  greater search depth required.*)
fun dup_step_tac (cs as (CS{dup_netpair,...})) = 
  biresolve_from_nets_tac dup_netpair;

(*Searching to depth m.*)
fun depth_tac cs m i = STATE(fn state => 
  SELECT_GOAL 
    (REPEAT_DETERM1 (safe_step_tac cs 1) THEN_ELSE
     (DEPTH_SOLVE (depth_tac cs m 1),
      inst0_step_tac cs 1  APPEND
      COND (K(m=0)) no_tac
        ((instp_step_tac cs 1 APPEND dup_step_tac cs 1)
	 THEN DEPTH_SOLVE (depth_tac cs (m-1) 1))))
  i);

(*Iterative deepening tactical.  Allows us to "deepen" any search tactic*)
fun DEEPEN tacf m i = STATE(fn state => 
   if has_fewer_prems i state then no_tac
   else (writeln ("Depth = " ^ string_of_int m);
	 tacf m i  ORELSE  DEEPEN tacf (m+2) i));

fun safe_depth_tac cs m = 
  SUBGOAL 
    (fn (prem,i) =>
      let val deti =
	  (*No Vars in the goal?  No need to backtrack between goals.*)
	  case term_vars prem of
	      []	=> DETERM 
	    | _::_	=> I
      in  SELECT_GOAL (TRY (safe_tac cs) THEN 
		       DEPTH_SOLVE (deti (depth_tac cs m 1))) i
      end);

fun deepen_tac cs = DEEPEN (safe_depth_tac cs);

end; 
end;
