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
  type proof
  val reset_goals       : unit -> unit
  val atomic_goal	: theory -> string -> thm list
  val atomic_goalw	: theory -> thm list -> string -> thm list
  val Goal		: string -> thm list
  val Goalw		: thm list -> string -> thm list
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
  val export_thy        : theory -> thm -> thm
  val export            : thm -> thm
  val Export		: thm -> thm
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
  val disable_pr        : unit -> unit
  val enable_pr         : unit -> unit
  val prlev		: int -> unit
  val prlim		: int -> unit
  val premises		: unit -> thm list
  val prin		: term -> unit
  val printyp		: typ -> unit
  val pprint_term	: term -> pprint_args -> unit
  val pprint_typ	: typ -> pprint_args -> unit
  val print_exn		: exn -> 'a
  val print_sign_exn	: Sign.sg -> exn -> 'a
  val prove_goal	: theory -> string -> (thm list -> tactic list) -> thm
  val prove_goalw      : theory->thm list->string->(thm list->tactic list)->thm
  val prove_goalw_cterm	: thm list->cterm->(thm list->tactic list)->thm
  val prove_goalw_cterm_nocheck	: thm list->cterm->(thm list->tactic list)->thm
  val quick_and_dirty_prove_goalw_cterm: theory -> thm list -> cterm
    -> (thm list -> tactic list) -> thm
  val push_proof	: unit -> unit
  val read		: string -> term
  val ren		: string -> int -> unit
  val restore_proof	: proof -> thm list
  val result		: unit -> thm  
  val result_error_fn   : (thm -> string -> thm) ref
  val rotate_proof	: unit -> thm list
  val uresult		: unit -> thm  
  val save_proof	: unit -> proof
  val topthm		: unit -> thm
  val undo		: unit -> unit
  val bind_thm          : string * thm -> unit
  val bind_thms         : string * thm list -> unit
  val qed               : string -> unit
  val qed_goal          : string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw         : string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val qed_spec_mp       : string -> unit
  val qed_goal_spec_mp  : string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw_spec_mp : string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val no_qed: unit -> unit
  val thms_containing   : xstring list -> (string * thm) list
  val findI             : int -> (string * thm) list
  val findEs            : int -> (string * thm) list
  val findE             : int -> int -> (string * thm) list
end;

structure Goals : GOALS =
struct

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

val dummy = trivial(read_cterm (Theory.sign_of ProtoPure.thy)
    ("PROP No_goal_has_been_supplied",propT));

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

(*Generates the list of new theories when the proof state's signature changes*)
fun sign_error (sign,sign') =
  let val names = Sign.stamp_names_of sign' \\ Sign.stamp_names_of sign
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

(* alternative to standard: this function does not discharge the hypotheses
   first. Is used for locales, in the following function prepare_proof *)
fun varify th =
  let val {maxidx,...} = rep_thm th
  in
    th |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
       |> Drule.strip_shyps_warning
       |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;

(** exporting a theorem out of a locale means turning all meta-hyps into assumptions
    and expand and cancel the locale definitions. 
    export goes through all levels in case of nested locales, whereas
    export_thy just goes one up. **)

fun get_top_scope_thms thy = 
   let val sc = (Locale.get_scope_sg (Theory.sign_of thy))
   in if (null sc) then (warning "No locale in theory"; [])
      else map (#prop o rep_thm) (map #2 (#thms(snd(hd sc))))
   end;

fun implies_intr_some_hyps thy A_set th = 
   let 
       val sign = Theory.sign_of thy;
       val used_As = A_set inter #hyps(rep_thm(th));
       val ctl = map (cterm_of sign) used_As
   in foldl (fn (x, y) => Thm.implies_intr y x) (th, ctl)
   end; 

fun standard_some thy A_set th =
  let val {maxidx,...} = rep_thm th
  in
    th |> implies_intr_some_hyps thy A_set
       |> forall_intr_frees |> forall_elim_vars (maxidx + 1)
       |> Drule.strip_shyps_warning
       |> zero_var_indexes |> Thm.varifyT |> Thm.compress
  end;

fun export_thy thy th = 
  let val A_set = get_top_scope_thms thy
  in
     standard_some thy [] (Seq.hd ((REPEAT (FIRSTGOAL (rtac reflexive_thm))) (standard_some thy A_set th)))
  end;

val export = standard o Seq.hd o (REPEAT (FIRSTGOAL (rtac reflexive_thm))) o standard;

fun Export th = export_thy (the_context ()) th;


(*Common treatment of "goal" and "prove_goal":
  Return assumptions, initial proof state, and function to make result.
  "atomic" indicates if the goal should be wrapped up in the function
  "Goal::prop=>prop" to avoid assumptions being returned separately.
*)
fun prepare_proof atomic rths chorn =
  let val {sign, t=horn,...} = rep_cterm chorn;
      val _ = Term.no_dummy_patterns horn handle TERM (msg, _) => error msg;
      val (_,As,B) = Logic.strip_horn(horn);
      val atoms = atomic andalso
            forall (fn t => not(Logic.is_implies t orelse Logic.is_all t)) As;
      val (As,B) = if atoms then ([],horn) else (As,B);
      val cAs = map (cterm_of sign) As;
      val prems = map (rewrite_rule rths o forall_elim_vars 0 o Thm.assume) cAs;
      val cB = cterm_of sign B;
      val st0 = let val st = Drule.impose_hyps cAs (Drule.mk_triv_goal cB)
                in  rewrite_goals_rule rths st end
      (*discharges assumptions from state in the order they appear in goal;
	checks (if requested) that resulting theorem is equivalent to goal. *)
      fun mkresult (check,state) =
        let val state = Seq.hd (flexflex_rule state)
	    		handle THM _ => state   (*smash flexflex pairs*)
	    val ngoals = nprems_of state
            val ath = implies_intr_list cAs state
            val th = ath RS Drule.rev_triv_goal
            val {hyps,prop,sign=sign',...} = rep_thm th
            val final_th = if (null(hyps)) then standard th else varify th
        in  if not check then final_th
	    else if not (Sign.eq_sg(sign,sign')) then !result_error_fn state
		("Signature of proof state has changed!" ^
		 sign_error (sign,sign'))
            else if ngoals>0 then !result_error_fn state
		(string_of_int ngoals ^ " unsolved goals!")
            else if (not (null hyps) andalso (not (Locale.in_locale hyps sign)))
		 then !result_error_fn state
                  ("Additional hypotheses:\n" ^ 
		   cat_lines 
		    (map (Sign.string_of_term sign) 
		     (filter (fn x => (not (Locale.in_locale [x] sign))) 
		      hyps)))
	    else if Pattern.matches (#tsig(Sign.rep_sg sign)) 
			            (Envir.beta_norm (term_of chorn), Envir.beta_norm prop)
		 then final_th
	    else  !result_error_fn state "proved a different theorem"
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
	  seq (Pretty.writeln o Display.pretty_theory) thys)
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
fun prove_goalw_cterm_general check rths chorn tacsf =
  let val (prems, st0, mkresult) = prepare_proof false rths chorn
      val tac = EVERY (tacsf prems)
      fun statef() = 
	  (case Seq.pull (tac st0) of 
	       Some(st,_) => st
	     | _ => error ("prove_goal: tactic failed"))
  in  mkresult (check, cond_timeit (!Library.timing) statef)  end
  handle e => (print_sign_exn_unit (#sign (rep_cterm chorn)) e;
	       writeln ("The exception above was raised for\n" ^ 
		      Display.string_of_cterm chorn); raise e);

(*Two variants: one checking the result, one not.  
  Neither prints runtime messages: they are for internal packages.*)
fun prove_goalw_cterm rths chorn = 
	setmp Library.timing false (prove_goalw_cterm_general true rths chorn)
and prove_goalw_cterm_nocheck rths chorn = 
	setmp Library.timing false (prove_goalw_cterm_general false rths chorn);


(*Version taking the goal as a string*)
fun prove_goalw thy rths agoal tacsf =
  let val sign = Theory.sign_of thy
      val chorn = read_cterm sign (agoal,propT)
  in  prove_goalw_cterm_general true rths chorn tacsf end
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
fun getgoal i = List.nth (prems_of (topthm()), i-1)
                handle Subscript => error"getgoal: Goal number out of range";

(*Return subgoal i's hypotheses as meta-level assumptions.
  For debugging uses of METAHYPS*)
local exception GETHYPS of thm list
in
fun gethyps i = 
    (METAHYPS (fn hyps => raise (GETHYPS hyps)) i (topthm());  [])
    handle GETHYPS hyps => hyps
end;

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
    goalw_cterm rths (cterm_of (Theory.sign_of thy) t);      *)
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
    agoalw_cterm atomic rths (Locale.read_cterm(Theory.sign_of thy)(agoal,propT))
    handle ERROR => error (*from type_assign, etc via prepare_proof*)
	("The error(s) above occurred for " ^ quote agoal);

val goalw = agoalw false;

(*String version with no meta-rewrite-rules*)
fun agoal atomic thy = agoalw atomic thy [];
val goal = agoal false;

(*now the versions that wrap the goal up in `Goal' to make it atomic*)
val atomic_goalw = agoalw true;
val atomic_goal = agoal true;

(*implicit context versions*)
fun Goal s = atomic_goal (Context.the_context ()) s;
fun Goalw thms s = atomic_goalw (Context.the_context ()) thms s;


(*Proof step "by" the given tactic -- apply tactic to the proof state*)
fun by_com tac ((th,ths), pairs) : gstack =
  (case  Seq.pull(tac th)  of
     None      => error"by: tactic failed"
   | Some(th2,ths2) => 
       (if eq_thm(th,th2) 
	  then warning "Warning: same as previous level"
	  else if eq_thm_sg(th,th2) then ()
	  else warning ("Warning: signature of proof state has changed" ^
		       sign_error (#sign(rep_thm th), #sign(rep_thm th2)));
       ((th2,ths2)::(th,ths)::pairs)));

fun by tac = cond_timeit (!Library.timing) 
    (fn() => make_command (by_com tac));

(* byev[tac1,...,tacn] applies tac1 THEN ... THEN tacn.
   Good for debugging proofs involving prove_goal.*)
val byev = by o EVERY;


(*Backtracking means find an alternative result from a tactic.
  If none at this level, try earlier levels*)
fun backtrack [] = error"back: no alternatives"
  | backtrack ((th,thstr) :: pairs) =
     (case Seq.pull thstr of
	  None      => (writeln"Going back a level..."; backtrack pairs)
	| Some(th2,thstr2) =>  
	   (if eq_thm(th,th2) 
	      then warning "Warning: same as previous choice at this level"
	      else if eq_thm_sg(th,th2) then ()
	      else warning "Warning: signature of proof state has changed";
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

fun read s = term_of (read_cterm (top_sg()) (s, TypeInfer.logicT));

(*Print a term under the current signature of the proof state*)
fun prin t = writeln (Sign.string_of_term (top_sg()) t);

fun printyp T = writeln (Sign.string_of_typ (top_sg()) T);

fun pprint_term t = Sign.pprint_term (top_sg()) t;

fun pprint_typ T = Sign.pprint_typ (top_sg()) T;


(*Prints exceptions nicely at top level; 
  raises the exception in order to have a polymorphic type!*)
fun print_exn e = (print_sign_exn_unit (top_sg()) e;  raise e);



(** theorem database operations **)

(* storing *)

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


(* retrieval *)

fun theory_of_goal () = ThyInfo.theory_of_sign (Thm.sign_of_thm (topthm ()));

fun thms_containing raw_consts =
  let
    val thy = theory_of_goal ();
    val consts = map (Sign.intern_const (Theory.sign_of thy)) raw_consts;
  in ThmDatabase.thms_containing thy consts end;


(*top_const: main constant, ignoring Trueprop*)
fun top_const (_ $ t) = (case head_of t of Const (c, _) => Some c | _ => None)
  | top_const _ = None;

val intro_const = top_const o concl_of;

fun elim_const thm = case prems_of thm of [] => None | p::_ => top_const p;

(* In case faster access is necessary, the thm db should provide special
functions

index_intros, index_elims: string -> (string * thm) list

where thm [| A1 ; ...; An |] ==> B is returned by
- index_intros c if B  is of the form c t1 ... tn
- index_elims c  if A1 is of the form c t1 ... tn
*)

(* could be provided by thm db *)
fun index_intros c =
  let fun topc(_,thm) = intro_const thm = Some(c);
      val named_thms = ThmDatabase.thms_containing (theory_of_goal ()) [c]
  in filter topc named_thms end;

(* could be provided by thm db *)
fun index_elims c =
  let fun topc(_,thm) = elim_const thm = Some(c);
      val named_thms = ThmDatabase.thms_containing (theory_of_goal ()) [c]
  in filter topc named_thms end;

(*assume that parameters have unique names; reverse them for substitution*)
fun goal_params i =
  let val gi = getgoal i
      val rfrees = rev(map Free (Logic.strip_params gi))
  in (gi,rfrees) end;

fun concl_of_goal i =
  let val (gi,rfrees) = goal_params i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(rfrees,B) end;

fun prems_of_goal i =
  let val (gi,rfrees) = goal_params i
      val As = Logic.strip_assums_hyp gi
  in map (fn A => subst_bounds(rfrees,A)) As end;

(*returns all those named_thms whose subterm extracted by extract can be
  instantiated to obj; the list is sorted according to the number of premises
  and the size of the required substitution.*)
fun select_match(obj, signobj, named_thms, extract) =
  let fun matches(prop, tsig) =
            case extract prop of
              None => false
            | Some pat => Pattern.matches tsig (pat, obj);

      fun substsize(prop, tsig) =
            let val Some pat = extract prop
                val (_,subst) = Pattern.match tsig (pat,obj)
            in foldl op+
                (0, map (fn (_,t) => size_of_term t) subst)
            end

      fun thm_ord ((p0,s0,_),(p1,s1,_)) =
            prod_ord (int_ord o pairself (fn 0 => 0 | x => 1)) int_ord ((p0,s0),(p1,s1));

      fun select((p as (_,thm))::named_thms, sels) =
            let val {prop, sign, ...} = rep_thm thm
            in select(named_thms,
                      if Sign.subsig(sign, signobj) andalso
                         matches(prop,#tsig(Sign.rep_sg signobj))
                      then
                        (nprems_of thm,substsize(prop,#tsig(Sign.rep_sg signobj)),p)::sels
                      else sels)
            end
        | select([],sels) = sels

  in map (fn (_,_,t) => t) (sort thm_ord (select(named_thms, []))) end;

fun find_matching(prop,sign,index,extract) =
  (case top_const prop of
     Some c => select_match(prop,sign,index c,extract)
   | _      => []);

fun find_intros(prop,sign) =
  find_matching(prop,sign,index_intros,Some o Logic.strip_imp_concl);

fun find_elims sign prop =
  let fun major prop = case Logic.strip_imp_prems prop of
                         [] => None | p::_ => Some p
  in find_matching(prop,sign,index_elims,major) end;

fun findI i = find_intros(concl_of_goal i,#sign(rep_thm(topthm())));

fun findEs i =
  let fun eq_nth((n1,th1),(n2,th2)) = n1=n2 andalso eq_thm(th1,th2);
      val sign = #sign(rep_thm(topthm()))
      val thmss = map (find_elims sign) (prems_of_goal i)
  in foldl (gen_union eq_nth) ([],thmss) end;

fun findE i j =
  let val sign = #sign(rep_thm(topthm()))
  in find_elims sign (nth_elem(j-1, prems_of_goal i)) end;

end;

open Goals;
