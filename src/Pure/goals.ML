(*  Title: 	Pure/goals.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Goal stack package.  The goal stack initially holds a dummy proof, and can
never become empty.  Each goal stack consists of a list of levels.  The
undo list is a list of goal stacks.  Finally, there may be a stack of
pending proofs.
*)


signature GOALS =
  sig
  structure Tactical: TACTICAL
  local open Tactical Tactical.Thm in
  type proof
  val ba		: int -> unit
  val back		: unit -> unit
  val bd		: thm -> int -> unit
  val bds		: thm list -> int -> unit
  val be		: thm -> int -> unit
  val bes		: thm list -> int -> unit
  val br		: thm -> int -> unit
  val brs		: thm list -> int -> unit
  val bw		: thm -> unit
  val bws		: thm list -> unit
  val by		: tactic -> unit
  val byev		: tactic list -> unit
  val chop		: unit -> unit
  val choplev		: int -> unit
  val fa		: unit -> unit
  val fd		: thm -> unit
  val fds		: thm list -> unit
  val fe		: thm -> unit
  val fes		: thm list -> unit
  val filter_goal	: (term*term->bool) -> thm list -> int -> thm list
  val fr		: thm -> unit
  val frs		: thm list -> unit
  val getgoal		: int -> term
  val gethyps		: int -> thm list
  val goal		: theory -> string -> thm list
  val goalw		: theory -> thm list -> string -> thm list
  val goalw_cterm	: thm list -> cterm -> thm list
  val pop_proof		: unit -> thm list
  val pr		: unit -> unit
  val premises		: unit -> thm list
  val prin		: term -> unit
  val printyp		: typ -> unit
  val pprint_term	: term -> pprint_args -> unit
  val pprint_typ	: typ -> pprint_args -> unit
  val print_exn		: exn -> 'a
  val print_sign_exn	: Sign.sg -> exn -> 'a
  val prlev		: int -> unit
  val proof_timing	: bool ref
  val prove_goal	: theory -> string -> (thm list -> tactic list) -> thm
  val prove_goalw      : theory->thm list->string->(thm list->tactic list)->thm
  val prove_goalw_cterm	: thm list->cterm->(thm list->tactic list)->thm
  val push_proof	: unit -> unit
  val read		: string -> term
  val ren		: string -> int -> unit
  val restore_proof	: proof -> thm list
  val result		: unit -> thm  
  val rotate_proof	: unit -> thm list
  val uresult		: unit -> thm  
  val save_proof	: unit -> proof
  val topthm		: unit -> thm
  val undo		: unit -> unit
  end
  end;

functor GoalsFun (structure Logic: LOGIC and Drule: DRULE and Tactic: TACTIC
                        and Pattern:PATTERN
	  sharing type Pattern.type_sig = Drule.Thm.Sign.Type.type_sig
              and Drule.Thm = Tactic.Tactical.Thm) : GOALS =
struct
structure Tactical = Tactic.Tactical
local open Tactic Tactic.Tactical Tactic.Tactical.Thm Drule
in

(*Each level of goal stack includes a proof state and alternative states,
  the output of the tactic applied to the preceeding level.  *)
type gstack = (thm * thm Sequence.seq) list;

datatype proof = Proof of gstack list * thm list * (bool*thm->thm);

(*** References ***)

(*Should process time be printed after proof steps?*)
val proof_timing = ref false;

(*Current assumption list -- set by "goal".*)
val curr_prems = ref([] : thm list);

(*Return assumption list -- useful if you didn't save "goal"'s result. *)
fun premises() = !curr_prems;

(*Current result maker -- set by "goal", used by "result".  *)
val curr_mkresult = 
    ref((fn _=> error"No goal has been supplied in subgoal module") 
       : bool*thm->thm);

val dummy = trivial(read_cterm Sign.pure 
    ("PROP No_goal_has_been_supplied",propT));

(*List of previous goal stacks, for the undo operation.  Set by setstate. 
  A list of lists!*)
val undo_list = ref([[(dummy, Sequence.null)]] : gstack list);

(* Stack of proof attempts *)
val proofstack = ref([]: proof list);


(*** Setting up goal-directed proof ***)

(*Generates the list of new theories when the proof state's signature changes*)
fun sign_error (sign,sign') =
  let val stamps = #stamps(Sign.rep_sg sign') \\ 
                   #stamps(Sign.rep_sg sign)
  in  case stamps of
        [stamp] => "\nNew theory: " ^ !stamp
      | _       => "\nNew theories: " ^ space_implode ", " (map ! stamps)
  end;

(*Common treatment of "goal" and "prove_goal":
  Return assumptions, initial proof state, and function to make result. *)
fun prepare_proof rths chorn =
  let val {sign, t=horn,...} = rep_cterm chorn;
      val (_,As,B) = Logic.strip_horn(horn);
      val cAs = map (cterm_of sign) As;
      val p_rew = if null rths then I else rewrite_rule rths;
      val c_rew = if null rths then I else rewrite_goals_rule rths;
      val prems = map (p_rew o forall_elim_vars(0) o assume) cAs
      and st0 = c_rew (trivial (cterm_of sign B))
      fun result_error state msg = 
        (writeln ("Bad final proof state:");
 	 !print_goals_ref (!goals_limit) state;
	 error msg)
      (*discharges assumptions from state in the order they appear in goal;
	checks (if requested) that resulting theorem is equivalent to goal. *)
      fun mkresult (check,state) =
        let val state = Sequence.hd (flexflex_rule state)
	    		handle _ => state   (*smash flexflex pairs*)
	    val ngoals = nprems_of state
            val th = implies_intr_list cAs state
            val {hyps,prop,sign=sign',...} = rep_thm th
        in  if not check then standard th
	    else if not (Sign.eq_sg(sign,sign')) then result_error state
		("Signature of proof state has changed!" ^
		 sign_error (sign,sign'))
            else if ngoals>0 then result_error state
		(string_of_int ngoals ^ " unsolved goals!")
            else if not (null hyps) then result_error state
                ("Additional hypotheses:\n" ^ 
                 cat_lines (map (Sign.string_of_term sign) hyps))
	    else if Pattern.matches (#tsig(Sign.rep_sg sign)) 
			            (term_of chorn, prop)
		 then  standard th 
	    else  result_error state "proved a different theorem"
        end
  in
     if Sign.eq_sg(sign, #sign(rep_thm st0))
     then (prems, st0, mkresult)
     else error ("Definitions would change the proof state's signature" ^
		 sign_error (sign, #sign(rep_thm st0)))
  end
  handle THM(s,_,_) => error("prepare_proof: exception THM was raised!\n" ^ s);

(*Prints exceptions readably to users*)
fun print_sign_exn_unit sign e = 
  case e of
     THM (msg,i,thms) =>
	 (writeln ("Exception THM " ^ string_of_int i ^ " raised:\n" ^ msg);
	  seq print_thm thms)
   | THEORY (msg,thys) =>
	 (writeln ("Exception THEORY raised:\n" ^ msg);
	  seq print_theory thys)
   | TERM (msg,ts) =>
	 (writeln ("Exception TERM raised:\n" ^ msg);
	  seq (writeln o Sign.string_of_term sign) ts)
   | TYPE (msg,Ts,ts) =>
	 (writeln ("Exception TYPE raised:\n" ^ msg);
	  seq (writeln o Sign.string_of_typ sign) Ts;
	  seq (writeln o Sign.string_of_term sign) ts)
   | e => raise e;

(*Prints an exception, then fails*)
fun print_sign_exn sign e = (print_sign_exn_unit sign e; raise ERROR);

(** the prove_goal.... commands
    Prove theorem using the listed tactics; check it has the specified form.
    Augment signature with all type assignments of goal.
    Syntax is similar to "goal" command for easy keyboard use. **)

(*Version taking the goal as a cterm*)
fun prove_goalw_cterm rths chorn tacsf =
  let val (prems, st0, mkresult) = prepare_proof rths chorn
      val tac = EVERY (tacsf prems)
      fun statef() = 
	  (case Sequence.pull (tapply(tac,st0)) of 
	       Some(st,_) => st
	     | _ => error ("prove_goal: tactic failed"))
  in  mkresult (true, cond_timeit (!proof_timing) statef)  end
  handle e => (print_sign_exn_unit (#sign (rep_cterm chorn)) e;
	       error ("The exception above was raised for\n" ^ 
		      string_of_cterm chorn));


(*Version taking the goal as a string*)
fun prove_goalw thy rths agoal tacsf =
  let val sign = sign_of thy
      val chorn = read_cterm sign (agoal,propT)
  in  prove_goalw_cterm rths chorn tacsf end
  handle ERROR => error (*from read_cterm?*)
		("The error above occurred for " ^ quote agoal);

(*String version with no meta-rewrite-rules*)
fun prove_goal thy = prove_goalw thy [];


(*** Commands etc ***)

(*Return the current goal stack, if any, from undo_list*)
fun getstate() : gstack = case !undo_list of 
      []   => error"No current state in subgoal module"
    | x::_ => x;

(*Pops the given goal stack*)
fun pop [] = error"Cannot go back past the beginning of the proof!"
  | pop (pair::pairs) = (pair,pairs);


(*Print a level of the goal stack.*)
fun print_top ((th,_), pairs) = 
   (prs("Level " ^ string_of_int(length pairs) ^ "\n"); 
    !print_goals_ref (!goals_limit) th);

(*Printing can raise exceptions, so the assignment occurs last.
  Can do   setstate[(st,Sequence.null)]  to set st as the state.  *)
fun setstate newgoals = 
  (print_top (pop newgoals);  undo_list := newgoals :: !undo_list);

(*Given a proof state transformation, return a command that updates
    the goal stack*)
fun make_command com = setstate (com (pop (getstate())));

(*Apply a function on proof states to the current goal stack*)
fun apply_fun f = f (pop(getstate()));

(*Return the top theorem, representing the proof state*)
fun topthm () = apply_fun  (fn ((th,_), _) => th);

(*Return the final result.  *)
fun result () = !curr_mkresult (true, topthm());

(*Return the result UNCHECKED that it equals the goal -- for synthesis,
  answer extraction, or other instantiation of Vars *)
fun uresult () = !curr_mkresult (false, topthm());

(*Get subgoal i from goal stack*)
fun getgoal i = 
      (case  drop (i-1, prems_of (topthm()))  of
	    [] => error"getgoal: Goal number out of range"
	  | Q::_ => Q);

(*Return subgoal i's hypotheses as meta-level assumptions.
  For debugging uses of METAHYPS*)
local exception GETHYPS of thm list
in
fun gethyps i = 
    (tapply(METAHYPS (fn hyps => raise (GETHYPS hyps)) i, topthm());  [])
    handle GETHYPS hyps => hyps
end;

(*Which thms could apply to goal i? (debugs tactics involving filter_thms) *)
fun filter_goal could ths i = filter_thms could (999, getgoal i, ths);

(*For inspecting earlier levels of the backward proof*)
fun chop_level n (pair,pairs) = 
  let val level = length pairs
  in  if 0<=n andalso n<= level
      then  drop (level - n, pair::pairs) 
      else  error ("Level number must lie between 0 and " ^ 
		   string_of_int level)
  end;

(*Print the given level of the proof*)
fun prlev n = apply_fun (print_top o pop o (chop_level n));
fun pr () = apply_fun print_top;

(** the goal.... commands
    Read main goal.  Set global variables curr_prems, curr_mkresult. 
    Initial subgoal and premises are rewritten using rths. **)

(*Version taking the goal as a cterm; if you have a term t and theory thy, use
    goalw_cterm rths (cterm_of (sign_of thy) t);      *)
fun goalw_cterm rths chorn = 
  let val (prems, st0, mkresult) = prepare_proof rths chorn
  in  undo_list := [];
      setstate [ (st0, Sequence.null) ];  
      curr_prems := prems;
      curr_mkresult := mkresult;
      prems
  end;

(*Version taking the goal as a string*)
fun goalw thy rths agoal = 
  goalw_cterm rths (read_cterm(sign_of thy)(agoal,propT))
  handle ERROR => error (*from type_assign, etc via prepare_proof*)
	    ("The error above occurred for " ^ quote agoal);

(*String version with no meta-rewrite-rules*)
fun goal thy = goalw thy [];

(*Proof step "by" the given tactic -- apply tactic to the proof state*)
fun by_com tac ((th,ths), pairs) : gstack =
  (case  Sequence.pull(tapply(tac, th))  of
     None      => error"by: tactic failed"
   | Some(th2,ths2) => 
       (if eq_thm(th,th2) 
	  then writeln"Warning: same as previous level"
	  else if eq_thm_sg(th,th2) then ()
	  else writeln("Warning: signature of proof state has changed" ^
		       sign_error (#sign(rep_thm th), #sign(rep_thm th2)));
       ((th2,ths2)::(th,ths)::pairs)));

fun by tac = cond_timeit (!proof_timing) 
    (fn() => make_command (by_com tac));

(* byev[tac1,...,tacn] applies tac1 THEN ... THEN tacn.
   Good for debugging proofs involving prove_goal.*)
val byev = by o EVERY;


(*Backtracking means find an alternative result from a tactic.
  If none at this level, try earlier levels*)
fun backtrack [] = error"back: no alternatives"
  | backtrack ((th,thstr) :: pairs) =
     (case Sequence.pull thstr of
	  None      => (writeln"Going back a level..."; backtrack pairs)
	| Some(th2,thstr2) =>  
	   (if eq_thm(th,th2) 
	      then writeln"Warning: same as previous choice at this level"
	      else if eq_thm_sg(th,th2) then ()
	      else writeln"Warning: signature of proof state has changed";
	    (th2,thstr2)::pairs));

fun back() = setstate (backtrack (getstate()));

(*Chop back to previous level of the proof*)
fun choplev n = make_command (chop_level n);

(*Chopping back the goal stack*)
fun chop () = make_command (fn (_,pairs) => pairs);

(*Restore the previous proof state;  discard current state. *)
fun undo() = case !undo_list of
      [] => error"No proof state"
    | [_] => error"Already at initial state"
    | _::newundo =>  (undo_list := newundo;  pr()) ;


(*** Managing the proof stack ***)

fun save_proof() = Proof(!undo_list, !curr_prems, !curr_mkresult);

fun restore_proof(Proof(ul,prems,mk)) =
 (undo_list:= ul;  curr_prems:= prems;  curr_mkresult := mk;  prems);


fun top_proof() = case !proofstack of
	[] => error("Stack of proof attempts is empty!")
    | p::ps => (p,ps);

(*  push a copy of the current proof state on to the stack *)
fun push_proof() = (proofstack := (save_proof() :: !proofstack));

(* discard the top proof state of the stack *)
fun pop_proof() = 
  let val (p,ps) = top_proof()
      val prems = restore_proof p
  in proofstack := ps;  pr();  prems end;

(* rotate the stack so that the top element goes to the bottom *)
fun rotate_proof() = let val (p,ps) = top_proof()
		    in proofstack := ps@[save_proof()];
		       restore_proof p;
		       pr();
		       !curr_prems
		    end;


(** Shortcuts for commonly-used tactics **)

fun bws rls = by (rewrite_goals_tac rls);
fun bw rl = bws [rl];

fun brs rls i = by (resolve_tac rls i);
fun br rl = brs [rl];

fun bes rls i = by (eresolve_tac rls i);
fun be rl = bes [rl];

fun bds rls i = by (dresolve_tac rls i);
fun bd rl = bds [rl];

fun ba i = by (assume_tac i);

fun ren str i = by (rename_tac str i);

(** Shortcuts to work on the first applicable subgoal **)

fun frs rls = by (FIRSTGOAL (trace_goalno_tac (resolve_tac rls)));
fun fr rl = frs [rl];

fun fes rls = by (FIRSTGOAL (trace_goalno_tac (eresolve_tac rls)));
fun fe rl = fes [rl];

fun fds rls = by (FIRSTGOAL (trace_goalno_tac (dresolve_tac rls)));
fun fd rl = fds [rl];

fun fa() = by (FIRSTGOAL (trace_goalno_tac assume_tac));

(** Reading and printing terms wrt the current theory **)

fun top_sg() = #sign(rep_thm(topthm()));

fun read s = term_of (read_cterm (top_sg())
			                   (s, (TVar(("DUMMY",0),[]))));

(*Print a term under the current signature of the proof state*)
fun prin t = writeln (Sign.string_of_term (top_sg()) t);

fun printyp T = writeln (Sign.string_of_typ (top_sg()) T);

fun pprint_term t = Sign.pprint_term (top_sg()) t;

fun pprint_typ T = Sign.pprint_typ (top_sg()) T;

(*Prints exceptions nicely at top level; 
  raises the exception in order to have a polymorphic type!*)
fun print_exn e = (print_sign_exn_unit (top_sg()) e;  raise e);

end;
end;
