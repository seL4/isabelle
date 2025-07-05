(*  Title:      FOLP/classical.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Like Provers/classical but modified because match_tac is unsuitable for
proof objects.

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
  val mp: thm                   (* [| P-->Q;  P |] ==> Q *)
  val not_elim: thm             (* [| ~P;  P |] ==> R *)
  val swap: thm                 (* ~P ==> (~Q ==> P) ==> Q *)
  val sizef : thm -> int        (* size function for BEST_FIRST *)
  val hyp_subst_tacs: Proof.context -> (int -> tactic) list
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
  val print_cs: Proof.context -> claset -> unit
  val rep_cs: claset -> 
      {safeIs: thm list, safeEs: thm list, hazIs: thm list, hazEs: thm list, 
       safe0_brls:(bool*thm)list, safep_brls: (bool*thm)list,
       haz_brls: (bool*thm)list}
  val best_tac : Proof.context -> claset -> int -> tactic
  val contr_tac : Proof.context -> int -> tactic
  val fast_tac : Proof.context -> claset -> int -> tactic
  val inst_step_tac : Proof.context -> int -> tactic
  val joinrules : thm list * thm list -> (bool * thm) list
  val mp_tac: Proof.context -> int -> tactic
  val safe_tac : Proof.context -> claset -> tactic
  val safe_step_tac : Proof.context -> claset -> int -> tactic
  val slow_step_tac : Proof.context -> claset -> int -> tactic
  val step_tac : Proof.context -> claset -> int -> tactic
  val swapify : thm list -> thm list
  val swap_res_tac : Proof.context -> thm list -> int -> tactic
  val uniq_mp_tac: Proof.context -> int -> tactic
  end;


functor Classical(Data: CLASSICAL_DATA): CLASSICAL = 
struct

local open Data in

(** Useful tactics for classical reasoning **)

val imp_elim = make_elim mp;

(*Solve goal that assumes both P and ~P. *)
fun contr_tac ctxt = eresolve_tac ctxt [not_elim] THEN'  assume_tac ctxt;

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
fun mp_tac ctxt i = eresolve_tac ctxt ([not_elim,imp_elim]) i  THEN  assume_tac ctxt i;

(*Like mp_tac but instantiates no variables*)
fun uniq_mp_tac ctxt i = ematch_tac ctxt ([not_elim,imp_elim]) i  THEN  uniq_assume_tac ctxt i;

(*Creates rules to eliminate ~A, from rules to introduce A*)
fun swapify intrs = intrs RLN (2, [swap]);

(*Uses introduction rules in the normal way, or on negated assumptions,
  trying rules in order. *)
fun swap_res_tac ctxt rls = 
    let fun tacf rl = resolve_tac ctxt [rl] ORELSE' eresolve_tac ctxt [rl RSN (2, swap)]
    in  assume_tac ctxt ORELSE' contr_tac ctxt ORELSE' FIRST' (map tacf rls)
    end;


(*** Classical rule sets ***)

datatype claset =
 CS of {safeIs: thm list,
        safeEs: thm list,
        hazIs: thm list,
        hazEs: thm list,
        (*the following are computed from the above*)
        safe0_brls: (bool*thm)list,
        safep_brls: (bool*thm)list,
        haz_brls: (bool*thm)list};
  
fun rep_cs (CS x) = x;

(*For use with biresolve_tac.  Combines intrs with swap to catch negated
  assumptions.  Also pairs elims with true. *)
fun joinrules (intrs,elims) =  
  map (pair true) (elims @ swapify intrs)  @  map (pair false) intrs;

(*Note that allE precedes exI in haz_brls*)
fun make_cs {safeIs,safeEs,hazIs,hazEs} =
  let val (safe0_brls, safep_brls) = (*0 subgoals vs 1 or more*)
          List.partition Bires.no_subgoals
             (sort Bires.subgoals_ord (joinrules(safeIs, safeEs)))
  in CS{safeIs=safeIs, safeEs=safeEs, hazIs=hazIs, hazEs=hazEs,
        safe0_brls=safe0_brls, safep_brls=safep_brls,
        haz_brls = sort Bires.subgoals_ord (joinrules(hazIs, hazEs))}
  end;

(*** Manipulation of clasets ***)

val empty_cs = make_cs{safeIs=[], safeEs=[], hazIs=[], hazEs=[]};

fun print_cs ctxt (CS{safeIs,safeEs,hazIs,hazEs,...}) =
  writeln (cat_lines
   (["Introduction rules"] @ map (Thm.string_of_thm ctxt) hazIs @
    ["Safe introduction rules"] @ map (Thm.string_of_thm ctxt) safeIs @
    ["Elimination rules"] @ map (Thm.string_of_thm ctxt) hazEs @
    ["Safe elimination rules"] @ map (Thm.string_of_thm ctxt) safeEs));

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

(*Attack subgoals using safe inferences*)
fun safe_step_tac ctxt (CS{safe0_brls,safep_brls,...}) = 
  FIRST' [uniq_assume_tac ctxt,
          uniq_mp_tac ctxt,
          biresolve_tac ctxt safe0_brls,
          FIRST' (hyp_subst_tacs ctxt),
          biresolve_tac ctxt safep_brls] ;

(*Repeatedly attack subgoals using safe inferences*)
fun safe_tac ctxt cs = DETERM (REPEAT_FIRST (safe_step_tac ctxt cs));

(*These steps could instantiate variables and are therefore unsafe.*)
fun inst_step_tac ctxt = assume_tac ctxt APPEND' contr_tac ctxt;

(*Single step for the prover.  FAILS unless it makes progress. *)
fun step_tac ctxt (cs as (CS{haz_brls,...})) i = 
  FIRST [safe_tac ctxt cs,
         inst_step_tac ctxt i,
         biresolve_tac ctxt haz_brls i];

(*** The following tactics all fail unless they solve one goal ***)

(*Dumb but fast*)
fun fast_tac ctxt cs = SELECT_GOAL (DEPTH_SOLVE (step_tac ctxt cs 1));

(*Slower but smarter than fast_tac*)
fun best_tac ctxt cs = 
  SELECT_GOAL (BEST_FIRST (Thm.no_prems, sizef) (step_tac ctxt cs 1));

(*Using a "safe" rule to instantiate variables is unsafe.  This tactic
  allows backtracking from "safe" rules to "unsafe" rules here.*)
fun slow_step_tac ctxt (cs as (CS{haz_brls,...})) i = 
    safe_tac ctxt cs ORELSE (assume_tac ctxt i APPEND biresolve_tac ctxt haz_brls i);

end; 
end;
