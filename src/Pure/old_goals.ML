(*  Title:      Pure/old_goals.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Old-style goal stack package.  The goal stack initially holds a dummy
proof, and can never become empty.  Each goal stack consists of a list
of levels.  The undo list is a list of goal stacks.  Finally, there
may be a stack of pending proofs.
*)

signature OLD_GOALS =
sig
  val strip_context: term -> (string * typ) list * term list * term
  val metahyps_thms: int -> thm -> thm list option
  val METAHYPS: (thm list -> tactic) -> int -> tactic
  val simple_read_term: theory -> typ -> string -> term
  val read_term: theory -> string -> term
  val read_prop: theory -> string -> term
  type proof
  val premises: unit -> thm list
  val reset_goals: unit -> unit
  val result_error_fn: (thm -> string -> thm) Unsynchronized.ref
  val print_sign_exn: theory -> exn -> 'a
  val prove_goalw_cterm: thm list->cterm->(thm list->tactic list)->thm
  val prove_goalw_cterm_nocheck: thm list->cterm->(thm list->tactic list)->thm
  val prove_goalw: theory -> thm list -> string -> (thm list -> tactic list) -> thm
  val prove_goal: theory -> string -> (thm list -> tactic list) -> thm
  val topthm: unit -> thm
  val result: unit -> thm
  val uresult: unit -> thm
  val getgoal: int -> term
  val gethyps: int -> thm list
  val print_exn: exn -> 'a
  val filter_goal: (term*term->bool) -> thm list -> int -> thm list
  val prlev: int -> unit
  val pr: unit -> unit
  val prlim: int -> unit
  val goalw_cterm: thm list -> cterm -> thm list
  val goalw: theory -> thm list -> string -> thm list
  val goal: theory -> string -> thm list
  val Goalw: thm list -> string -> thm list
  val Goal: string -> thm list
  val simple_prove_goal_cterm: cterm->(thm list->tactic list)->thm
  val by: tactic -> unit
  val byev: tactic list -> unit
  val back: unit -> unit
  val choplev: int -> unit
  val chop: unit -> unit
  val undo: unit -> unit
  val save_proof: unit -> proof
  val restore_proof: proof -> thm list
  val push_proof: unit -> unit
  val pop_proof: unit -> thm list
  val rotate_proof: unit -> thm list
  val qed: string -> unit
  val qed_goal: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw: string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
  val qed_spec_mp: string -> unit
  val qed_goal_spec_mp: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw_spec_mp: string -> theory -> thm list -> string
    -> (thm list -> tactic list) -> unit
end;

structure OldGoals: OLD_GOALS =
struct

(**** METAHYPS -- tactical for using hypotheses as meta-level assumptions
       METAHYPS (fn prems => tac prems) i

converts subgoal i, of the form !!x1...xm. [| A1;...;An] ==> A into a new
proof state A==>A, supplying A1,...,An as meta-level assumptions (in
"prems").  The parameters x1,...,xm become free variables.  If the
resulting proof state is [| B1;...;Bk] ==> C (possibly assuming A1,...,An)
then it is lifted back into the original context, yielding k subgoals.

Replaces unknowns in the context by Frees having the prefix METAHYP_
New unknowns in [| B1;...;Bk] ==> C are lifted over x1,...,xm.
DOES NOT HANDLE TYPE UNKNOWNS.


NOTE: This version does not observe the proof context, and thus cannot
work reliably.  See also Subgoal.SUBPROOF and Subgoal.FOCUS for
properly localized variants of the same idea.
****)

(*Strips assumptions in goal yielding  ( [x1,...,xm], [H1,...,Hn], B )
    H1,...,Hn are the hypotheses;  x1...xm are variants of the parameters.
  Main difference from strip_assums concerns parameters:
    it replaces the bound variables by free variables.  *)
fun strip_context_aux (params, Hs, Const ("==>", _) $ H $ B) =
      strip_context_aux (params, H :: Hs, B)
  | strip_context_aux (params, Hs, Const ("all",_) $ Abs (a, T, t)) =
      let val (b, u) = Syntax.variant_abs (a, T, t)
      in strip_context_aux ((b, T) :: params, Hs, u) end
  | strip_context_aux (params, Hs, B) = (rev params, rev Hs, B);

fun strip_context A = strip_context_aux ([], [], A);

local

  (*Left-to-right replacements: ctpairs = [...,(vi,ti),...].
    Instantiates distinct free variables by terms of same type.*)
  fun free_instantiate ctpairs =
    forall_elim_list (map snd ctpairs) o forall_intr_list (map fst ctpairs);

  fun free_of s ((a, i), T) =
    Free (s ^ (case i of 0 => a | _ => a ^ "_" ^ string_of_int i), T)

  fun mk_inst v = (Var v, free_of "METAHYP1_" v)
in

(*Common code for METAHYPS and metahyps_thms*)
fun metahyps_split_prem prem =
  let (*find all vars in the hyps -- should find tvars also!*)
      val hyps_vars = fold Term.add_vars (Logic.strip_assums_hyp prem) []
      val insts = map mk_inst hyps_vars
      (*replace the hyps_vars by Frees*)
      val prem' = subst_atomic insts prem
      val (params,hyps,concl) = strip_context prem'
  in (insts,params,hyps,concl)  end;

fun metahyps_aux_tac tacf (prem,gno) state =
  let val (insts,params,hyps,concl) = metahyps_split_prem prem
      val maxidx = Thm.maxidx_of state
      val cterm = Thm.cterm_of (Thm.theory_of_thm state)
      val chyps = map cterm hyps
      val hypths = map assume chyps
      val subprems = map (Thm.forall_elim_vars 0) hypths
      val fparams = map Free params
      val cparams = map cterm fparams
      fun swap_ctpair (t,u) = (cterm u, cterm t)
      (*Subgoal variables: make Free; lift type over params*)
      fun mk_subgoal_inst concl_vars (v, T) =
          if member (op =) concl_vars (v, T)
          then ((v, T), true, free_of "METAHYP2_" (v, T))
          else ((v, T), false, free_of "METAHYP2_" (v, map #2 params ---> T))
      (*Instantiate subgoal vars by Free applied to params*)
      fun mk_ctpair (v, in_concl, u) =
          if in_concl then (cterm (Var v), cterm u)
          else (cterm (Var v), cterm (list_comb (u, fparams)))
      (*Restore Vars with higher type and index*)
      fun mk_subgoal_swap_ctpair (((a, i), T), in_concl, u as Free (_, U)) =
          if in_concl then (cterm u, cterm (Var ((a, i), T)))
          else (cterm u, cterm (Var ((a, i + maxidx), U)))
      (*Embed B in the original context of params and hyps*)
      fun embed B = list_all_free (params, Logic.list_implies (hyps, B))
      (*Strip the context using elimination rules*)
      fun elim Bhyp = implies_elim_list (forall_elim_list cparams Bhyp) hypths
      (*A form of lifting that discharges assumptions.*)
      fun relift st =
        let val prop = Thm.prop_of st
            val subgoal_vars = (*Vars introduced in the subgoals*)
              fold Term.add_vars (Logic.strip_imp_prems prop) []
            and concl_vars = Term.add_vars (Logic.strip_imp_concl prop) []
            val subgoal_insts = map (mk_subgoal_inst concl_vars) subgoal_vars
            val st' = Thm.instantiate ([], map mk_ctpair subgoal_insts) st
            val emBs = map (cterm o embed) (prems_of st')
            val Cth  = implies_elim_list st' (map (elim o assume) emBs)
        in  (*restore the unknowns to the hypotheses*)
            free_instantiate (map swap_ctpair insts @
                              map mk_subgoal_swap_ctpair subgoal_insts)
                (*discharge assumptions from state in same order*)
                (implies_intr_list emBs
                  (forall_intr_list cparams (implies_intr_list chyps Cth)))
        end
      (*function to replace the current subgoal*)
      fun next st = Thm.bicompose false (false, relift st, nprems_of st) gno state
  in Seq.maps next (tacf subprems (trivial (cterm concl))) end;

end;

(*Returns the theorem list that METAHYPS would supply to its tactic*)
fun metahyps_thms i state =
  let val prem = Logic.nth_prem (i, Thm.prop_of state)
      and cterm = cterm_of (Thm.theory_of_thm state)
      val (_,_,hyps,_) = metahyps_split_prem prem
  in SOME (map (Thm.forall_elim_vars 0 o Thm.assume o cterm) hyps) end
  handle TERM ("nth_prem", [A]) => NONE;

local

fun print_vars_terms thy (n,thm) =
  let
    fun typed ty = " has type: " ^ Syntax.string_of_typ_global thy ty;
    fun find_vars thy (Const (c, ty)) =
          if null (Term.add_tvarsT ty []) then I
          else insert (op =) (c ^ typed ty)
      | find_vars thy (Var (xi, ty)) = insert (op =) (Term.string_of_vname xi ^ typed ty)
      | find_vars _ (Free _) = I
      | find_vars _ (Bound _) = I
      | find_vars thy (Abs (_, _, t)) = find_vars thy t
      | find_vars thy (t1 $ t2) =
          find_vars thy t1 #> find_vars thy t1;
    val prem = Logic.nth_prem (n, Thm.prop_of thm)
    val tms = find_vars thy prem []
  in
    (warning "Found schematic vars in assumptions:"; warning (cat_lines tms))
  end;

in

fun METAHYPS tacf n thm = SUBGOAL (metahyps_aux_tac tacf) n thm
  handle THM("assume: variables",_,_) => (print_vars_terms (theory_of_thm thm) (n,thm); Seq.empty)

end;


(* old ways of reading terms *)

fun simple_read_term thy T s =
  let
    val ctxt = ProofContext.init thy
      |> ProofContext.allow_dummies
      |> ProofContext.set_mode ProofContext.mode_schematic;
    val parse = if T = propT then Syntax.parse_prop else Syntax.parse_term;
  in parse ctxt s |> TypeInfer.constrain T |> Syntax.check_term ctxt end;

fun read_term thy = simple_read_term thy dummyT;
fun read_prop thy = simple_read_term thy propT;



(*** Goal package ***)

(*Each level of goal stack includes a proof state and alternative states,
  the output of the tactic applied to the preceeding level.  *)
type gstack = (thm * thm Seq.seq) list;

datatype proof = Proof of gstack list * thm list * (bool*thm->thm);


(*** References ***)

(*Current assumption list -- set by "goal".*)
val curr_prems = Unsynchronized.ref([] : thm list);

(*Return assumption list -- useful if you didn't save "goal"'s result. *)
fun premises() = !curr_prems;

(*Current result maker -- set by "goal", used by "result".  *)
fun init_mkresult _ = error "No goal has been supplied in subgoal module";
val curr_mkresult = Unsynchronized.ref (init_mkresult: bool*thm->thm);

(*List of previous goal stacks, for the undo operation.  Set by setstate.
  A list of lists!*)
val undo_list = Unsynchronized.ref([[(asm_rl, Seq.empty)]] : gstack list);

(* Stack of proof attempts *)
val proofstack = Unsynchronized.ref([]: proof list);

(*reset all refs*)
fun reset_goals () =
  (curr_prems := []; curr_mkresult := init_mkresult;
    undo_list := [[(asm_rl, Seq.empty)]]);


(*** Setting up goal-directed proof ***)

(*Generates the list of new theories when the proof state's theory changes*)
fun thy_error (thy,thy') =
  let val names = Context.display_names thy' \\ Context.display_names thy
  in  case names of
        [name] => "\nNew theory: " ^ name
      | _       => "\nNew theories: " ^ space_implode ", " names
  end;

(*Default action is to print an error message; could be suppressed for
  special applications.*)
fun result_error_default state msg : thm =
  Pretty.str "Bad final proof state:" ::
      Goal_Display.pretty_goals_without_context (!goals_limit) state @
    [Pretty.str msg, Pretty.str "Proof failed!"] |> Pretty.chunks |> Pretty.string_of |> error;

val result_error_fn = Unsynchronized.ref result_error_default;


(*Common treatment of "goal" and "prove_goal":
  Return assumptions, initial proof state, and function to make result.
  "atomic" indicates if the goal should be wrapped up in the function
  "Goal::prop=>prop" to avoid assumptions being returned separately.
*)
fun prepare_proof atomic rths chorn =
  let
      val _ = legacy_feature "Old goal command";
      val thy = Thm.theory_of_cterm chorn;
      val horn = Thm.term_of chorn;
      val _ = Term.no_dummy_patterns horn handle TERM (msg, _) => error msg;
      val (As, B) = Logic.strip_horn horn;
      val atoms = atomic andalso
            forall (fn t => not (can Logic.dest_implies t orelse Logic.is_all t)) As;
      val (As,B) = if atoms then ([],horn) else (As,B);
      val cAs = map (cterm_of thy) As;
      val prems = map (rewrite_rule rths o Thm.forall_elim_vars 0 o Thm.assume) cAs;
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
            val thy' = Thm.theory_of_thm th
            val {hyps, prop, ...} = Thm.rep_thm th
            val final_th = standard th
        in  if not check then final_th
            else if not (Theory.eq_thy(thy,thy')) then !result_error_fn state
                ("Theory of proof state has changed!" ^
                 thy_error (thy,thy'))
            else if ngoals>0 then !result_error_fn state
                (string_of_int ngoals ^ " unsolved goals!")
            else if not (null hyps) then !result_error_fn state
                ("Additional hypotheses:\n" ^
                 cat_lines (map (Syntax.string_of_term_global thy) hyps))
            else if Pattern.matches thy
                                    (Envir.beta_norm (term_of chorn), Envir.beta_norm prop)
                 then final_th
            else  !result_error_fn state "proved a different theorem"
        end
  in
     if Theory.eq_thy(thy, Thm.theory_of_thm st0)
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
          List.app (writeln o Display.string_of_thm_global thy) thms)
   | THEORY (msg,thys) =>
         (writeln ("Exception THEORY raised:\n" ^ msg);
          List.app (writeln o Context.str_of_thy) thys)
   | TERM (msg,ts) =>
         (writeln ("Exception TERM raised:\n" ^ msg);
          List.app (writeln o Syntax.string_of_term_global thy) ts)
   | TYPE (msg,Ts,ts) =>
         (writeln ("Exception TYPE raised:\n" ^ msg);
          List.app (writeln o Syntax.string_of_typ_global thy) Ts;
          List.app (writeln o Syntax.string_of_term_global thy) ts)
   | e => raise e;

(*Prints an exception, then fails*)
fun print_sign_exn thy e = (print_sign_exn_unit thy e; raise ERROR "");

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
  in  mkresult (check, cond_timeit (!Output.timing) "" statef)  end;

(*Two variants: one checking the result, one not.
  Neither prints runtime messages: they are for internal packages.*)
fun prove_goalw_cterm rths chorn =
        setmp Output.timing false (prove_goalw_cterm_general true rths chorn)
and prove_goalw_cterm_nocheck rths chorn =
        setmp Output.timing false (prove_goalw_cterm_general false rths chorn);


(*Version taking the goal as a string*)
fun prove_goalw thy rths agoal tacsf =
  let val chorn = cterm_of thy (read_prop thy agoal)
  in prove_goalw_cterm_general true rths chorn tacsf end
  handle ERROR msg => cat_error msg (*from read_prop?*)
                ("The error(s) above occurred for " ^ quote agoal);

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


(* Print a level of the goal stack *)

fun print_top ((th, _), pairs) =
  let
    val n = length pairs;
    val m = (! goals_limit);
    val ngoals = nprems_of th;
  in
    [Pretty.str ("Level " ^ string_of_int n ^
      (if ngoals > 0 then " (" ^ string_of_int ngoals ^ " subgoal" ^
        (if ngoals <> 1 then "s" else "") ^ ")"
      else ""))] @
    Goal_Display.pretty_goals_without_context m th
  end |> Pretty.chunks |> Pretty.writeln;

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
fun prlev n = apply_fun (print_top o pop o (chop_level n));
fun pr () = apply_fun print_top;

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
    agoalw_cterm atomic rths (cterm_of thy (read_prop thy agoal))
    handle ERROR msg => cat_error msg (*from type_assign, etc via prepare_proof*)
        ("The error(s) above occurred for " ^ quote agoal);

val goalw = agoalw false;
fun goal thy = goalw thy [];

(*now the versions that wrap the goal up in `Goal' to make it atomic*)
fun Goalw thms s = agoalw true (ML_Context.the_global_context ()) thms s;
val Goal = Goalw [];

(*simple version with minimal amount of checking and postprocessing*)
fun simple_prove_goal_cterm G f =
  let
    val _ = legacy_feature "Old goal command";
    val As = Drule.strip_imp_prems G;
    val B = Drule.strip_imp_concl G;
    val asms = map Assumption.assume As;
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
       (if Thm.eq_thm(th,th2)
          then warning "Warning: same as previous level"
          else if Thm.eq_thm_thy(th,th2) then ()
          else warning ("Warning: theory of proof state has changed" ^
                       thy_error (Thm.theory_of_thm th, Thm.theory_of_thm th2));
       ((th2,ths2)::(th,ths)::pairs)));

fun by tac = cond_timeit (!Output.timing) ""
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
           (if Thm.eq_thm(th,th2)
              then warning "Warning: same as previous choice at this level"
              else if Thm.eq_thm_thy(th,th2) then ()
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
fun rotate_proof() =
  let val (p,ps) = top_proof()
  in proofstack := ps@[save_proof()];
     restore_proof p;
     pr();
     !curr_prems
  end;


(** theorem bindings **)

fun qed name = ML_Context.ml_store_thm (name, result ());
fun qed_goal name thy goal tacsf = ML_Context.ml_store_thm (name, prove_goal thy goal tacsf);
fun qed_goalw name thy rews goal tacsf =
  ML_Context.ml_store_thm (name, prove_goalw thy rews goal tacsf);
fun qed_spec_mp name =
  ML_Context.ml_store_thm (name, ObjectLogic.rulify_no_asm (result ()));
fun qed_goal_spec_mp name thy s p =
  bind_thm (name, ObjectLogic.rulify_no_asm (prove_goal thy s p));
fun qed_goalw_spec_mp name thy defs s p =
  bind_thm (name, ObjectLogic.rulify_no_asm (prove_goalw thy defs s p));

end;

