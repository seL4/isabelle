(*  Title:      tctical
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Tacticals
*)

infix 1 THEN THEN' THEN_ALL_NEW;
infix 0 ORELSE APPEND INTLEAVE ORELSE' APPEND' INTLEAVE';
infix 0 THEN_ELSE;


signature TACTICAL =
  sig
  type tactic  (* = thm -> thm Seq.seq*)
  val all_tac           : tactic
  val ALLGOALS          : (int -> tactic) -> tactic   
  val APPEND            : tactic * tactic -> tactic
  val APPEND'           : ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val CHANGED           : tactic -> tactic
  val CHANGED_GOAL	: (int -> tactic) -> int -> tactic
  val COND              : (thm -> bool) -> tactic -> tactic -> tactic   
  val DETERM            : tactic -> tactic
  val EVERY             : tactic list -> tactic   
  val EVERY'            : ('a -> tactic) list -> 'a -> tactic
  val EVERY1            : (int -> tactic) list -> tactic
  val FILTER            : (thm -> bool) -> tactic -> tactic
  val FIRST             : tactic list -> tactic   
  val FIRST'            : ('a -> tactic) list -> 'a -> tactic
  val FIRST1            : (int -> tactic) list -> tactic
  val FIRSTGOAL         : (int -> tactic) -> tactic
  val goals_limit       : int ref
  val INTLEAVE          : tactic * tactic -> tactic
  val INTLEAVE'         : ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val METAHYPS          : (thm list -> tactic) -> int -> tactic
  val no_tac            : tactic
  val ORELSE            : tactic * tactic -> tactic
  val ORELSE'           : ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val pause_tac         : tactic
  val print_tac         : string -> tactic
  val REPEAT            : tactic -> tactic
  val REPEAT1           : tactic -> tactic
  val REPEAT_FIRST      : (int -> tactic) -> tactic
  val REPEAT_SOME       : (int -> tactic) -> tactic
  val REPEAT_DETERM_N   : int -> tactic -> tactic
  val REPEAT_DETERM     : tactic -> tactic
  val REPEAT_DETERM1    : tactic -> tactic
  val REPEAT_DETERM_FIRST: (int -> tactic) -> tactic
  val REPEAT_DETERM_SOME: (int -> tactic) -> tactic
  val DETERM_UNTIL      : (thm -> bool) -> tactic -> tactic
  val SELECT_GOAL       : tactic -> int -> tactic
  val SOMEGOAL          : (int -> tactic) -> tactic   
  val strip_context     : term -> (string * typ) list * term list * term
  val SUBGOAL           : ((term*int) -> tactic) -> int -> tactic
  val suppress_tracing  : bool ref
  val THEN              : tactic * tactic -> tactic
  val THEN'             : ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val THEN_ALL_NEW	: (int -> tactic) * (int -> tactic) -> int -> tactic
  val REPEAT_ALL_NEW	: (int -> tactic) -> int -> tactic
  val THEN_ELSE         : tactic * (tactic*tactic) -> tactic
  val traced_tac        : (thm -> (thm * thm Seq.seq) option) -> tactic
  val tracify           : bool ref -> tactic -> tactic
  val trace_REPEAT      : bool ref
  val TRY               : tactic -> tactic
  val TRYALL            : (int -> tactic) -> tactic   
  end;


structure Tactical : TACTICAL = 
struct

(**** Tactics ****)

(*A tactic maps a proof tree to a sequence of proof trees:
    if length of sequence = 0 then the tactic does not apply;
    if length > 1 then backtracking on the alternatives can occur.*)

type tactic = thm -> thm Seq.seq;


(*** LCF-style tacticals ***)

(*the tactical THEN performs one tactic followed by another*)
fun (tac1 THEN tac2) st = Seq.flat (Seq.map tac2 (tac1 st));


(*The tactical ORELSE uses the first tactic that returns a nonempty sequence.
  Like in LCF, ORELSE commits to either tac1 or tac2 immediately.
  Does not backtrack to tac2 if tac1 was initially chosen. *)
fun (tac1 ORELSE tac2) st =
    case Seq.pull(tac1 st) of
        None       => tac2 st
      | sequencecell => Seq.make(fn()=> sequencecell);


(*The tactical APPEND combines the results of two tactics.
  Like ORELSE, but allows backtracking on both tac1 and tac2.
  The tactic tac2 is not applied until needed.*)
fun (tac1 APPEND tac2) st = 
  Seq.append(tac1 st,
                  Seq.make(fn()=> Seq.pull (tac2 st)));

(*Like APPEND, but interleaves results of tac1 and tac2.*)
fun (tac1 INTLEAVE tac2) st = 
    Seq.interleave(tac1 st,
                        Seq.make(fn()=> Seq.pull (tac2 st)));

(*Conditional tactic.
        tac1 ORELSE tac2 = tac1 THEN_ELSE (all_tac, tac2)
        tac1 THEN tac2   = tac1 THEN_ELSE (tac2, no_tac)
*)
fun (tac THEN_ELSE (tac1, tac2)) st = 
    case Seq.pull(tac st) of
        None    => tac2 st              (*failed; try tactic 2*)
      | seqcell => Seq.flat       (*succeeded; use tactic 1*)
                    (Seq.map tac1 (Seq.make(fn()=> seqcell)));


(*Versions for combining tactic-valued functions, as in
     SOMEGOAL (resolve_tac rls THEN' assume_tac) *)
fun (tac1 THEN' tac2) x = tac1 x THEN tac2 x;
fun (tac1 ORELSE' tac2) x = tac1 x ORELSE tac2 x;
fun (tac1 APPEND' tac2) x = tac1 x APPEND tac2 x;
fun (tac1 INTLEAVE' tac2) x = tac1 x INTLEAVE tac2 x;

(*passes all proofs through unchanged;  identity of THEN*)
fun all_tac st = Seq.single st;

(*passes no proofs through;  identity of ORELSE and APPEND*)
fun no_tac st  = Seq.empty;


(*Make a tactic deterministic by chopping the tail of the proof sequence*)
fun DETERM tac st =  
      case Seq.pull (tac st) of
              None => Seq.empty
            | Some(x,_) => Seq.cons(x, Seq.empty);


(*Conditional tactical: testfun controls which tactic to use next.
  Beware: due to eager evaluation, both thentac and elsetac are evaluated.*)
fun COND testfun thenf elsef = (fn prf =>
    if testfun prf then  thenf prf   else  elsef prf);

(*Do the tactic or else do nothing*)
fun TRY tac = tac ORELSE all_tac;

(*** List-oriented tactics ***)

local
  (*This version of EVERY avoids backtracking over repeated states*)

  fun EVY (trail, []) st = 
	Seq.make (fn()=> Some(st, 
			Seq.make (fn()=> Seq.pull (evyBack trail))))
    | EVY (trail, tac::tacs) st = 
	  case Seq.pull(tac st) of
	      None    => evyBack trail              (*failed: backtrack*)
	    | Some(st',q) => EVY ((st',q,tacs)::trail, tacs) st'
  and evyBack [] = Seq.empty (*no alternatives*)
    | evyBack ((st',q,tacs)::trail) =
	  case Seq.pull q of
	      None        => evyBack trail
	    | Some(st,q') => if eq_thm (st',st) 
			     then evyBack ((st',q',tacs)::trail)
			     else EVY ((st,q',tacs)::trail, tacs) st
in

(* EVERY [tac1,...,tacn]   equals    tac1 THEN ... THEN tacn   *)
fun EVERY tacs = EVY ([], tacs);
end;


(* EVERY' [tac1,...,tacn] i  equals    tac1 i THEN ... THEN tacn i   *)
fun EVERY' tacs i = EVERY (map (fn f => f i) tacs);

(*Apply every tactic to 1*)
fun EVERY1 tacs = EVERY' tacs 1;

(* FIRST [tac1,...,tacn]   equals    tac1 ORELSE ... ORELSE tacn   *)
fun FIRST tacs = foldr (op ORELSE) (tacs, no_tac);

(* FIRST' [tac1,...,tacn] i  equals    tac1 i ORELSE ... ORELSE tacn i   *)
fun FIRST' tacs = foldr (op ORELSE') (tacs, K no_tac);

(*Apply first tactic to 1*)
fun FIRST1 tacs = FIRST' tacs 1;


(*** Tracing tactics ***)

(*Max number of goals to print -- set by user*)
val goals_limit = ref 10;

(*Print the current proof state and pass it on.*)
fun print_tac msg = 
    (fn st => 
     (writeln msg;
      print_goals (!goals_limit) st; Seq.single st));

(*Pause until a line is typed -- if non-empty then fail. *)
fun pause_tac st =  
  (writeln "** Press RETURN to continue:";
   if TextIO.inputLine TextIO.stdIn = "\n" then Seq.single st
   else (writeln "Goodbye";  Seq.empty));

exception TRACE_EXIT of thm
and TRACE_QUIT;

(*Tracing flags*)
val trace_REPEAT= ref false
and suppress_tracing = ref false;

(*Handle all tracing commands for current state and tactic *)
fun exec_trace_command flag (tac, st) = 
   case TextIO.inputLine(TextIO.stdIn) of
       "\n" => tac st
     | "f\n" => Seq.empty
     | "o\n" => (flag:=false;  tac st)
     | "s\n" => (suppress_tracing:=true;  tac st)
     | "x\n" => (writeln "Exiting now";  raise (TRACE_EXIT st))
     | "quit\n" => raise TRACE_QUIT
     | _     => (writeln
"Type RETURN to continue or...\n\
\     f    - to fail here\n\
\     o    - to switch tracing off\n\
\     s    - to suppress tracing until next entry to a tactical\n\
\     x    - to exit at this point\n\
\     quit - to abort this tracing run\n\
\** Well? "     ;  exec_trace_command flag (tac, st));


(*Extract from a tactic, a thm->thm seq function that handles tracing*)
fun tracify flag tac st =
  if !flag andalso not (!suppress_tracing)
           then (print_goals (!goals_limit) st;
                 writeln "** Press RETURN to continue:";
                 exec_trace_command flag (tac,st))
  else tac st;

(*Create a tactic whose outcome is given by seqf, handling TRACE_EXIT*)
fun traced_tac seqf st = 
    (suppress_tracing := false;
     Seq.make (fn()=> seqf st
                         handle TRACE_EXIT st' => Some(st', Seq.empty)));


(*Deterministic DO..UNTIL: only retains the first outcome; tail recursive.
  Forces repitition until predicate on state is fulfilled.*)
fun DETERM_UNTIL p tac = 
let val tac = tracify trace_REPEAT tac
    fun drep st = if p st then Some (st, Seq.empty)
                          else (case Seq.pull(tac st) of
                                  None        => None
                                | Some(st',_) => drep st')
in  traced_tac drep  end;

(*Deterministic REPEAT: only retains the first outcome; 
  uses less space than REPEAT; tail recursive.
  If non-negative, n bounds the number of repetitions.*)
fun REPEAT_DETERM_N n tac = 
  let val tac = tracify trace_REPEAT tac
      fun drep 0 st = Some(st, Seq.empty)
        | drep n st =
           (case Seq.pull(tac st) of
                None       => Some(st, Seq.empty)
              | Some(st',_) => drep (n-1) st')
  in  traced_tac (drep n)  end;

(*Allows any number of repetitions*)
val REPEAT_DETERM = REPEAT_DETERM_N ~1;

(*General REPEAT: maintains a stack of alternatives; tail recursive*)
fun REPEAT tac = 
  let val tac = tracify trace_REPEAT tac
      fun rep qs st = 
        case Seq.pull(tac st) of
            None       => Some(st, Seq.make(fn()=> repq qs))
          | Some(st',q) => rep (q::qs) st'
      and repq [] = None
        | repq(q::qs) = case Seq.pull q of
            None       => repq qs
          | Some(st,q) => rep (q::qs) st
  in  traced_tac (rep [])  end;

(*Repeat 1 or more times*)
fun REPEAT_DETERM1 tac = DETERM tac THEN REPEAT_DETERM tac;
fun REPEAT1 tac = tac THEN REPEAT tac;


(** Filtering tacticals **)

(*Returns all states satisfying the predicate*)
fun FILTER pred tac st = Seq.filter pred (tac st);

(*Returns all changed states*)
fun CHANGED tac st = 
    let fun diff st' = not (eq_thm(st,st'))
    in  Seq.filter diff (tac st)  end;


(*** Tacticals based on subgoal numbering ***)

(*For n subgoals, performs tac(n) THEN ... THEN tac(1) 
  Essential to work backwards since tac(i) may add/delete subgoals at i. *)
fun ALLGOALS tac st = 
  let fun doall 0 = all_tac
        | doall n = tac(n) THEN doall(n-1)
  in  doall(nprems_of st)st  end;

(*For n subgoals, performs tac(n) ORELSE ... ORELSE tac(1)  *)
fun SOMEGOAL tac st = 
  let fun find 0 = no_tac
        | find n = tac(n) ORELSE find(n-1)
  in  find(nprems_of st)st  end;

(*For n subgoals, performs tac(1) ORELSE ... ORELSE tac(n).
  More appropriate than SOMEGOAL in some cases.*)
fun FIRSTGOAL tac st = 
  let fun find (i,n) = if i>n then no_tac else  tac(i) ORELSE find (i+1,n)
  in  find(1, nprems_of st)st  end;

(*Repeatedly solve some using tac. *)
fun REPEAT_SOME tac = REPEAT1 (SOMEGOAL (REPEAT1 o tac));
fun REPEAT_DETERM_SOME tac = REPEAT_DETERM1 (SOMEGOAL (REPEAT_DETERM1 o tac));

(*Repeatedly solve the first possible subgoal using tac. *)
fun REPEAT_FIRST tac = REPEAT1 (FIRSTGOAL (REPEAT1 o tac));
fun REPEAT_DETERM_FIRST tac = REPEAT_DETERM1 (FIRSTGOAL (REPEAT_DETERM1 o tac));

(*For n subgoals, tries to apply tac to n,...1  *)
fun TRYALL tac = ALLGOALS (TRY o tac);


(*Make a tactic for subgoal i, if there is one.  *)
fun SUBGOAL goalfun i st = goalfun (List.nth(prems_of st, i-1),  i) st
                             handle Subscript => Seq.empty;

(*Returns all states that have changed in subgoal i, counted from the LAST
  subgoal.  For stac, for example.*)
fun CHANGED_GOAL tac i st = 
    let val np = nprems_of st
        val d = np-i                 (*distance from END*)
        val t = List.nth(prems_of st, i-1)
        fun diff st' = 
	    nprems_of st' - d <= 0   (*the subgoal no longer exists*)
	    orelse 
             not (Pattern.aeconv (t,
				  List.nth(prems_of st', 
					   nprems_of st' - d - 1)))
    in  Seq.filter diff (tac i st)  end
    handle Subscript => Seq.empty  (*no subgoal i*);

fun (tac1 THEN_ALL_NEW tac2) i st =
  st |> (tac1 i THEN (fn st' => Seq.INTERVAL tac2 i (i + nprems_of st' - nprems_of st) st'));

(*repeatedly dig into any emerging subgoals*)
fun REPEAT_ALL_NEW tac =
  tac THEN_ALL_NEW (TRY o (fn i => REPEAT_ALL_NEW tac i));


(*** SELECT_GOAL ***)

(*Tactical for restricting the effect of a tactic to subgoal i.
  Works by making a new state from subgoal i, applying tac to it, and
  composing the resulting metathm with the original state.
  The "main goal" of the new state will not be atomic, some tactics may fail!
  DOES NOT work if tactic affects the main goal other than by instantiation.*)

(*SELECT_GOAL optimization: replace the conclusion by a variable X,
  to avoid copying.  Proof states have X==concl as an assuption.*)

val prop_equals = cterm_of (Theory.sign_of ProtoPure.thy) 
                    (Const("==", propT-->propT-->propT));

fun mk_prop_equals(t,u) = Thm.capply (Thm.capply prop_equals t) u;

(*Like trivial but returns [ct==X] ct==>X instead of ct==>ct, if possible.
  It is paired with a function to undo the transformation.  If ct contains
  Vars then it returns ct==>ct.*)

fun eq_trivial ct =
  let val xfree = cterm_of (Theory.sign_of ProtoPure.thy)
                           (Free (gensym"EQ_TRIVIAL_", propT))
      val ct_eq_x = mk_prop_equals (ct, xfree)
      and refl_ct = reflexive ct
      fun restore th = 
          implies_elim 
            (forall_elim ct (forall_intr xfree (implies_intr ct_eq_x th)))
            refl_ct
  in  (equal_elim
         (combination (combination refl_implies refl_ct) (assume ct_eq_x))
         (Drule.mk_triv_goal ct),
       restore)
  end  (*Fails if there are Vars or TVars*)
    handle THM _ => (Drule.mk_triv_goal ct, I);


(*Does the work of SELECT_GOAL. *)
fun select tac st i =
  let val (eq_cprem, restore) = (*we hope maxidx goes to ~1*)
	  eq_trivial (adjust_maxidx (List.nth(cprems_of st, i-1)))
      fun next st' = 
	  let val np' = nprems_of st'
              (*rename the ?A in rev_triv_goal*)
	      val {maxidx,...} = rep_thm st'
              val ct = cterm_of (Theory.sign_of ProtoPure.thy)
		                (Var(("A",maxidx+1), propT))
	      val rev_triv_goal' = instantiate' [] [Some ct] Drule.rev_triv_goal
              fun bic th = bicompose false (false, th, np')
          in  bic (Seq.hd (bic (restore st') 1 rev_triv_goal')) i st  end 
  in  Seq.flat (Seq.map next (tac eq_cprem))
  end;

fun SELECT_GOAL tac i st = 
  let val np = nprems_of st
  in  if 1<=i andalso i<=np then 
          (*If only one subgoal, then just apply tactic*)
	  if np=1 then tac st else select tac st i
      else Seq.empty
  end;


(*Strips assumptions in goal yielding  ( [x1,...,xm], [H1,...,Hn], B )
    H1,...,Hn are the hypotheses;  x1...xm are variants of the parameters. 
  Main difference from strip_assums concerns parameters: 
    it replaces the bound variables by free variables.  *)
fun strip_context_aux (params, Hs, Const("==>", _) $ H $ B) = 
        strip_context_aux (params, H::Hs, B)
  | strip_context_aux (params, Hs, Const("all",_)$Abs(a,T,t)) =
        let val (b,u) = variant_abs(a,T,t)
        in  strip_context_aux ((b,T)::params, Hs, u)  end
  | strip_context_aux (params, Hs, B) = (rev params, rev Hs, B);

fun strip_context A = strip_context_aux ([],[],A);


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
****)

local 

  (*Left-to-right replacements: ctpairs = [...,(vi,ti),...].
    Instantiates distinct free variables by terms of same type.*)
  fun free_instantiate ctpairs = 
      forall_elim_list (map snd ctpairs) o forall_intr_list (map fst ctpairs);

  fun free_of s ((a,i), T) =
        Free(s ^ (case i of 0 => a | _ => a ^ "_" ^ string_of_int i),
             T)

  fun mk_inst (var as Var(v,T))  = (var,  free_of "METAHYP1_" (v,T))
in

fun metahyps_aux_tac tacf (prem,i) state = 
  let val {sign,maxidx,...} = rep_thm state
      val cterm = cterm_of sign
      (*find all vars in the hyps -- should find tvars also!*)
      val hyps_vars = foldr add_term_vars (Logic.strip_assums_hyp prem, [])
      val insts = map mk_inst hyps_vars
      (*replace the hyps_vars by Frees*)
      val prem' = subst_atomic insts prem
      val (params,hyps,concl) = strip_context prem'
      val fparams = map Free params
      val cparams = map cterm fparams
      and chyps = map cterm hyps
      val hypths = map assume chyps
      fun swap_ctpair (t,u) = (cterm u, cterm t)
      (*Subgoal variables: make Free; lift type over params*)
      fun mk_subgoal_inst concl_vars (var as Var(v,T)) = 
          if var mem concl_vars 
          then (var, true, free_of "METAHYP2_" (v,T))
          else (var, false,
                free_of "METAHYP2_" (v, map #2 params --->T))
      (*Instantiate subgoal vars by Free applied to params*)
      fun mk_ctpair (t,in_concl,u) = 
          if in_concl then (cterm t,  cterm u)
          else (cterm t,  cterm (list_comb (u,fparams)))
      (*Restore Vars with higher type and index*)
      fun mk_subgoal_swap_ctpair 
                (t as Var((a,i),_), in_concl, u as Free(_,U)) = 
          if in_concl then (cterm u, cterm t)
          else (cterm u, cterm(Var((a, i+maxidx), U)))
      (*Embed B in the original context of params and hyps*)
      fun embed B = list_all_free (params, Logic.list_implies (hyps, B))
      (*Strip the context using elimination rules*)
      fun elim Bhyp = implies_elim_list (forall_elim_list cparams Bhyp) hypths
      (*Embed an ff pair in the original params*)
      fun embed_ff(t,u) = Logic.mk_flexpair (list_abs_free (params, t), 
                                             list_abs_free (params, u))
      (*Remove parameter abstractions from the ff pairs*)
      fun elim_ff ff = flexpair_abs_elim_list cparams ff
      (*A form of lifting that discharges assumptions.*)
      fun relift st = 
        let val prop = #prop(rep_thm st)
            val subgoal_vars = (*Vars introduced in the subgoals*)
                  foldr add_term_vars (Logic.strip_imp_prems prop, [])
            and concl_vars = add_term_vars (Logic.strip_imp_concl prop, [])
            val subgoal_insts = map (mk_subgoal_inst concl_vars) subgoal_vars
            val st' = instantiate ([], map mk_ctpair subgoal_insts) st
            val emBs = map (cterm o embed) (prems_of st')
            and ffs = map (cterm o embed_ff) (tpairs_of st')
            val Cth  = implies_elim_list st' 
                            (map (elim_ff o assume) ffs @
                             map (elim o assume) emBs)
        in  (*restore the unknowns to the hypotheses*)
            free_instantiate (map swap_ctpair insts @
                              map mk_subgoal_swap_ctpair subgoal_insts)
                (*discharge assumptions from state in same order*)
                (implies_intr_list (ffs@emBs)
                  (forall_intr_list cparams (implies_intr_list chyps Cth)))
        end
      val subprems = map (forall_elim_vars 0) hypths
      and st0 = trivial (cterm concl)
      (*function to replace the current subgoal*)
      fun next st = bicompose false (false, relift st, nprems_of st)
                    i state
  in  Seq.flat (Seq.map next (tacf subprems st0))
  end;
end;

fun METAHYPS tacf = SUBGOAL (metahyps_aux_tac tacf);

end;

open Tactical;
