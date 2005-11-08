(*  Title:      Pure/old_goals.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Old-style goal stack package.  The goal stack initially holds a dummy
proof, and can never become empty.  Each goal stack consists of a list
of levels.  The undo list is a list of goal stacks.  Finally, there
may be a stack of pending proofs.
*)

signature GOALS =
sig
  val premises: unit -> thm list
  val prove_goal: theory -> string -> (thm list -> tactic list) -> thm
  val prove_goalw: theory -> thm list -> string -> (thm list -> tactic list) -> thm
  val disable_pr: unit -> unit
  val enable_pr: unit -> unit
  val topthm: unit -> thm
  val result: unit -> thm
  val uresult: unit -> thm
  val getgoal: int -> term
  val gethyps: int -> thm list
  val prlev: int -> unit
  val pr: unit -> unit
  val prlim: int -> unit
  val goal: theory -> string -> thm list
  val goalw: theory -> thm list -> string -> thm list
  val Goal: string -> thm list
  val Goalw: thm list -> string -> thm list
  val by: tactic -> unit
  val back: unit -> unit
  val choplev: int -> unit
  val chop: unit -> unit
  val undo: unit -> unit
  val bind_thm: string * thm -> unit
  val bind_thms: string * thm list -> unit
  val qed: string -> unit
  val qed_goal: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw: string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val qed_spec_mp: string -> unit
  val qed_goal_spec_mp: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw_spec_mp: string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val no_qed: unit -> unit
  val thms_containing: xstring list -> (string * thm) list
end;

signature OLD_GOALS =
sig
  include GOALS
  val legacy: bool ref
  type proof
  val reset_goals: unit -> unit
  val result_error_fn: (thm -> string -> thm) ref
  val print_sign_exn: theory -> exn -> 'a
  val prove_goalw_cterm: thm list->cterm->(thm list->tactic list)->thm
  val prove_goalw_cterm_nocheck: thm list->cterm->(thm list->tactic list)->thm
  val quick_and_dirty_prove_goalw_cterm: theory -> thm list -> cterm
    -> (thm list -> tactic list) -> thm
  val print_exn: exn -> 'a
  val filter_goal: (term*term->bool) -> thm list -> int -> thm list
  val goalw_cterm: thm list -> cterm -> thm list
  val simple_prove_goal_cterm: cterm->(thm list->tactic list)->thm
  val byev: tactic list -> unit
  val save_proof: unit -> proof
  val restore_proof: proof -> thm list
  val push_proof: unit -> unit
  val pop_proof: unit -> thm list
  val rotate_proof: unit -> thm list
  val bws: thm list -> unit
  val bw: thm -> unit
  val brs: thm list -> int -> unit
  val br: thm -> int -> unit
  val bes: thm list -> int -> unit
  val be: thm -> int -> unit
  val bds: thm list -> int -> unit
  val bd: thm -> int -> unit
  val ba: int -> unit
  val ren: string -> int -> unit
  val frs: thm list -> unit
  val fr: thm -> unit
  val fes: thm list -> unit
  val fe: thm -> unit
  val fds: thm list -> unit
  val fd: thm -> unit
  val fa: unit -> unit
end;

structure OldGoals: OLD_GOALS =
struct

val legacy = ref false;
fun warn_obsolete () = if ! legacy then () else warning "Obsolete goal command encountered";


(*** Goal package ***)

(*Each level of goal stack includes a proof state and alternative states,
  the output of the tactic applied to the preceeding level.  *)
type gstack = (thm * thm Seq.seq) list;

datatype proof = Proof of gstack list * thm list * (bool*thm->thm);


(*** References ***)

(*Current assumption list -- set by "goal".*)
val curr_prems = ref([] : thm list);

(*Return assumption list -- useful if you didn't save "goal"'s result. *)
fun premises() = !curr_prems;

(*Current result maker -- set by "goal", used by "result".  *)
fun init_mkresult _ = error "No goal has been supplied in subgoal module";
val curr_mkresult = ref (init_mkresult: bool*thm->thm);

val dummy = Thm.trivial (read_cterm ProtoPure.thy ("PROP No_goal_has_been_supplied", propT));

(*List of previous goal stacks, for the undo operation.  Set by setstate.
  A list of lists!*)
val undo_list = ref([[(dummy, Seq.empty)]] : gstack list);

(* Stack of proof attempts *)
val proofstack = ref([]: proof list);

(*reset all refs*)
fun reset_goals () =
  (curr_prems := []; curr_mkresult := init_mkresult;
    undo_list := [[(dummy, Seq.empty)]]);


(*** Setting up goal-directed proof ***)

(*Generates the list of new theories when the proof state's theory changes*)
fun thy_error (thy,thy') =
  let val names = Context.names_of thy' \\ Context.names_of thy
  in  case names of
        [name] => "\nNew theory: " ^ name
      | _       => "\nNew theories: " ^ space_implode ", " names
  end;

(*Default action is to print an error message; could be suppressed for
  special applications.*)
fun result_error_default state msg : thm =
  Pretty.str "Bad final proof state:" :: Display.pretty_goals (!goals_limit) state @
    [Pretty.str msg, Pretty.str "Proof failed!"] |> Pretty.chunks |> Pretty.string_of |> error;

val result_error_fn = ref result_error_default;


(*Common treatment of "goal" and "prove_goal":
  Return assumptions, initial proof state, and function to make result.
  "atomic" indicates if the goal should be wrapped up in the function
  "Goal::prop=>prop" to avoid assumptions being returned separately.
*)
fun prepare_proof atomic rths chorn =
  let
      val _ = warn_obsolete ();
      val {thy, t=horn,...} = rep_cterm chorn;
      val _ = Term.no_dummy_patterns horn handle TERM (msg, _) => error msg;
      val (As, B) = Logic.strip_horn horn;
      val atoms = atomic andalso
            forall (fn t => not(Logic.is_implies t orelse Logic.is_all t)) As;
      val (As,B) = if atoms then ([],horn) else (As,B);
      val cAs = map (cterm_of thy) As;
      val prems = map (rewrite_rule rths o forall_elim_vars 0 o Thm.assume) cAs;
      val cB = cterm_of thy B;
      val st0 = let val st = Goal.init cB |> fold Thm.weaken cAs
                in  rewrite_goals_rule rths st end
      (*discharges assumptions from state in the order they appear in goal;
        checks (if requested) that resulting theorem is equivalent to goal. *)
      fun mkresult (check,state) =
        let val state = Seq.hd (flexflex_rule state)
                        handle THM _ => state   (*smash flexflex pairs*)
            val ngoals = nprems_of state
            val ath = implies_intr_list cAs state
            val th = Goal.conclude ath
            val {hyps,prop,thy=thy',...} = rep_thm th
            val final_th = standard th
        in  if not check then final_th
            else if not (eq_thy(thy,thy')) then !result_error_fn state
                ("Theory of proof state has changed!" ^
                 thy_error (thy,thy'))
            else if ngoals>0 then !result_error_fn state
                (string_of_int ngoals ^ " unsolved goals!")
            else if not (null hyps) then !result_error_fn state
                ("Additional hypotheses:\n" ^
                 cat_lines (map (Sign.string_of_term thy) hyps))
            else if Pattern.matches thy
                                    (Envir.beta_norm (term_of chorn), Envir.beta_norm prop)
                 then final_th
            else  !result_error_fn state "proved a different theorem"
        end
  in
     if eq_thy(thy, Thm.theory_of_thm st0)
     then (prems, st0, mkresult)
     else error ("Definitions would change the proof state's theory" ^
                 thy_error (thy, Thm.theory_of_thm st0))
  end
  handle THM(s,_,_) => error("prepare_proof: exception THM was raised!\n" ^ s);

(*Prints exceptions readably to users*)
fun print_sign_exn_unit thy e =
  case e of
     THM (msg,i,thms) =>
         (writeln ("Exception THM " ^ string_of_int i ^ " raised:\n" ^ msg);
          List.app print_thm thms)
   | THEORY (msg,thys) =>
         (writeln ("Exception THEORY raised:\n" ^ msg);
          List.app (writeln o Context.str_of_thy) thys)
   | TERM (msg,ts) =>
         (writeln ("Exception TERM raised:\n" ^ msg);
          List.app (writeln o Sign.string_of_term thy) ts)
   | TYPE (msg,Ts,ts) =>
         (writeln ("Exception TYPE raised:\n" ^ msg);
          List.app (writeln o Sign.string_of_typ thy) Ts;
          List.app (writeln o Sign.string_of_term thy) ts)
   | e => raise e;

(*Prints an exception, then fails*)
fun print_sign_exn thy e = (print_sign_exn_unit thy e; raise ERROR);

(** the prove_goal.... commands
    Prove theorem using the listed tactics; check it has the specified form.
    Augment theory with all type assignments of goal.
    Syntax is similar to "goal" command for easy keyboard use. **)

(*Version taking the goal as a cterm*)
fun prove_goalw_cterm_general check rths chorn tacsf =
  let val (prems, st0, mkresult) = prepare_proof false rths chorn
      val tac = EVERY (tacsf prems)
      fun statef() =
          (case Seq.pull (tac st0) of
               SOME(st,_) => st
             | _ => error ("prove_goal: tactic failed"))
  in  mkresult (check, cond_timeit (!Output.timing) statef)  end
  handle e => (print_sign_exn_unit (#thy (rep_cterm chorn)) e;
               writeln ("The exception above was raised for\n" ^
                      Display.string_of_cterm chorn); raise e);

(*Two variants: one checking the result, one not.
  Neither prints runtime messages: they are for internal packages.*)
fun prove_goalw_cterm rths chorn =
        setmp Output.timing false (prove_goalw_cterm_general true rths chorn)
and prove_goalw_cterm_nocheck rths chorn =
        setmp Output.timing false (prove_goalw_cterm_general false rths chorn);


(*Version taking the goal as a string*)
fun prove_goalw thy rths agoal tacsf =
  let val chorn = read_cterm thy (agoal, propT)
  in prove_goalw_cterm_general true rths chorn tacsf end
  handle ERROR => error (*from read_cterm?*)
                ("The error(s) above occurred for " ^ quote agoal);

(*String version with no meta-rewrite-rules*)
fun prove_goal thy = prove_goalw thy [];

(*quick and dirty version (conditional)*)
fun quick_and_dirty_prove_goalw_cterm thy rews ct tacs =
  prove_goalw_cterm rews ct
    (if ! quick_and_dirty then (K [SkipProof.cheat_tac thy]) else tacs);


(*** Commands etc ***)

(*Return the current goal stack, if any, from undo_list*)
fun getstate() : gstack = case !undo_list of
      []   => error"No current state in subgoal module"
    | x::_ => x;

(*Pops the given goal stack*)
fun pop [] = error"Cannot go back past the beginning of the proof!"
  | pop (pair::pairs) = (pair,pairs);


(* Print a level of the goal stack -- subject to quiet mode *)

val quiet = ref false;
fun disable_pr () = quiet := true;
fun enable_pr () = quiet := false;

fun print_top ((th, _), pairs) =
  if ! quiet then ()
  else ! Display.print_current_goals_fn (length pairs) (! goals_limit) th;

(*Printing can raise exceptions, so the assignment occurs last.
  Can do   setstate[(st,Seq.empty)]  to set st as the state.  *)
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
fun getgoal i = Logic.get_goal (prop_of (topthm())) i;

(*Return subgoal i's hypotheses as meta-level assumptions.
  For debugging uses of METAHYPS*)
local exception GETHYPS of thm list
in
fun gethyps i =
    (METAHYPS (fn hyps => raise (GETHYPS hyps)) i (topthm());  [])
    handle GETHYPS hyps => hyps
end;

(*Prints exceptions nicely at top level;
  raises the exception in order to have a polymorphic type!*)
fun print_exn e = (print_sign_exn_unit (Thm.theory_of_thm (topthm())) e;  raise e);

(*Which thms could apply to goal i? (debugs tactics involving filter_thms) *)
fun filter_goal could ths i = filter_thms could (999, getgoal i, ths);

(*For inspecting earlier levels of the backward proof*)
fun chop_level n (pair,pairs) =
  let val level = length pairs
  in  if n<0 andalso ~n <= level
      then  List.drop (pair::pairs, ~n)
      else if 0<=n andalso n<= level
      then  List.drop (pair::pairs, level - n)
      else  error ("Level number must lie between 0 and " ^
                   string_of_int level)
  end;

(*Print the given level of the proof; prlev ~1 prints previous level*)
fun prlev n = (enable_pr (); apply_fun (print_top o pop o (chop_level n)));
fun pr () = (enable_pr (); apply_fun print_top);

(*Set goals_limit and print again*)
fun prlim n = (goals_limit:=n; pr());

(** the goal.... commands
    Read main goal.  Set global variables curr_prems, curr_mkresult.
    Initial subgoal and premises are rewritten using rths. **)

(*Version taking the goal as a cterm; if you have a term t and theory thy, use
    goalw_cterm rths (cterm_of thy t);      *)
fun agoalw_cterm atomic rths chorn =
  let val (prems, st0, mkresult) = prepare_proof atomic rths chorn
  in  undo_list := [];
      setstate [ (st0, Seq.empty) ];
      curr_prems := prems;
      curr_mkresult := mkresult;
      prems
  end;

val goalw_cterm = agoalw_cterm false;

(*Version taking the goal as a string*)
fun agoalw atomic thy rths agoal =
    agoalw_cterm atomic rths (read_cterm thy (agoal, propT))
    handle ERROR => error (*from type_assign, etc via prepare_proof*)
        ("The error(s) above occurred for " ^ quote agoal);

val goalw = agoalw false;
fun goal thy = goalw thy [];

(*now the versions that wrap the goal up in `Goal' to make it atomic*)
fun Goalw thms s = agoalw true (Context.the_context ()) thms s;
val Goal = Goalw [];

(*simple version with minimal amount of checking and postprocessing*)
fun simple_prove_goal_cterm G f =
  let
    val _ = warn_obsolete ();
    val As = Drule.strip_imp_prems G;
    val B = Drule.strip_imp_concl G;
    val asms = map (Goal.norm_hhf o Thm.assume) As;
    fun check NONE = error "prove_goal: tactic failed"
      | check (SOME (thm, _)) = (case nprems_of thm of
            0 => thm
          | i => !result_error_fn thm (string_of_int i ^ " unsolved goals!"))
  in
    standard (implies_intr_list As
      (check (Seq.pull (EVERY (f asms) (trivial B)))))
  end;


(*Proof step "by" the given tactic -- apply tactic to the proof state*)
fun by_com tac ((th,ths), pairs) : gstack =
  (case  Seq.pull(tac th)  of
     NONE      => error"by: tactic failed"
   | SOME(th2,ths2) =>
       (if eq_thm(th,th2)
          then warning "Warning: same as previous level"
          else if eq_thm_thy(th,th2) then ()
          else warning ("Warning: theory of proof state has changed" ^
                       thy_error (Thm.theory_of_thm th, Thm.theory_of_thm th2));
       ((th2,ths2)::(th,ths)::pairs)));

fun by tac = cond_timeit (!Output.timing)
    (fn() => make_command (by_com tac));

(* byev[tac1,...,tacn] applies tac1 THEN ... THEN tacn.
   Good for debugging proofs involving prove_goal.*)
val byev = by o EVERY;


(*Backtracking means find an alternative result from a tactic.
  If none at this level, try earlier levels*)
fun backtrack [] = error"back: no alternatives"
  | backtrack ((th,thstr) :: pairs) =
     (case Seq.pull thstr of
          NONE      => (writeln"Going back a level..."; backtrack pairs)
        | SOME(th2,thstr2) =>
           (if eq_thm(th,th2)
              then warning "Warning: same as previous choice at this level"
              else if eq_thm_thy(th,th2) then ()
              else warning "Warning: theory of proof state has changed";
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


(** theorem database operations **)

(* store *)

fun bind_thm (name, thm) = ThmDatabase.ml_store_thm (name, standard thm);
fun bind_thms (name, thms) = ThmDatabase.ml_store_thms (name, map standard thms);

fun qed name = ThmDatabase.ml_store_thm (name, result ());
fun qed_goal name thy goal tacsf = ThmDatabase.ml_store_thm (name, prove_goal thy goal tacsf);
fun qed_goalw name thy rews goal tacsf =
  ThmDatabase.ml_store_thm (name, prove_goalw thy rews goal tacsf);
fun qed_spec_mp name =
  ThmDatabase.ml_store_thm (name, ObjectLogic.rulify_no_asm (result ()));
fun qed_goal_spec_mp name thy s p =
  bind_thm (name, ObjectLogic.rulify_no_asm (prove_goal thy s p));
fun qed_goalw_spec_mp name thy defs s p =
  bind_thm (name, ObjectLogic.rulify_no_asm (prove_goalw thy defs s p));

fun no_qed () = ();


(* retrieve *)

fun thms_containing raw_consts =
  let
    val thy = Thm.theory_of_thm (topthm ());
    val consts = map (Sign.intern_const thy) raw_consts;
  in
    (case List.filter (is_none o Sign.const_type thy) consts of
      [] => ()
    | cs => error ("thms_containing: undeclared consts " ^ commas_quote cs));
    PureThy.thms_containing_consts thy consts
  end;

end;

structure Goals: GOALS = OldGoals;
open Goals;
