(*  Title: 	tctical
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Tacticals
*)

infix 1 THEN THEN' THEN_BEST_FIRST;
infix 0 ORELSE APPEND INTLEAVE ORELSE' APPEND' INTLEAVE';

infix 0 THEN_ELSE;


signature TACTICAL =
  sig
  structure Thm : THM
  local open Thm  in
  datatype tactic = Tactic of thm -> thm Sequence.seq
  val all_tac		: tactic
  val ALLGOALS		: (int -> tactic) -> tactic   
  val APPEND		: tactic * tactic -> tactic
  val APPEND'		: ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val BEST_FIRST	: (thm -> bool) * (thm -> int) -> tactic -> tactic
  val BREADTH_FIRST	: (thm -> bool) -> tactic -> tactic
  val CHANGED		: tactic -> tactic
  val COND		: (thm -> bool) -> tactic -> tactic -> tactic   
  val DEPTH_FIRST	: (thm -> bool) -> tactic -> tactic
  val DEPTH_SOLVE	: tactic -> tactic
  val DEPTH_SOLVE_1	: tactic -> tactic
  val DETERM		: tactic -> tactic
  val EVERY		: tactic list -> tactic   
  val EVERY'		: ('a -> tactic) list -> 'a -> tactic
  val EVERY1		: (int -> tactic) list -> tactic
  val FILTER		: (thm -> bool) -> tactic -> tactic
  val FIRST		: tactic list -> tactic   
  val FIRST'		: ('a -> tactic) list -> 'a -> tactic
  val FIRST1		: (int -> tactic) list -> tactic
  val FIRSTGOAL		: (int -> tactic) -> tactic
  val goals_limit	: int ref
  val has_fewer_prems	: int -> thm -> bool   
  val IF_UNSOLVED	: tactic -> tactic
  val INTLEAVE		: tactic * tactic -> tactic
  val INTLEAVE'		: ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val METAHYPS		: (thm list -> tactic) -> int -> tactic
  val no_tac		: tactic
  val ORELSE		: tactic * tactic -> tactic
  val ORELSE'		: ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val pause_tac		: tactic
  val print_tac		: tactic
  val REPEAT1		: tactic -> tactic
  val REPEAT		: tactic -> tactic
  val REPEAT_DETERM	: tactic -> tactic
  val REPEAT_FIRST	: (int -> tactic) -> tactic
  val REPEAT_SOME	: (int -> tactic) -> tactic
  val SELECT_GOAL	: tactic -> int -> tactic
  val SOMEGOAL		: (int -> tactic) -> tactic   
  val STATE		: (thm -> tactic) -> tactic
  val strip_context	: term -> (string * typ) list * term list * term
  val SUBGOAL		: ((term*int) -> tactic) -> int -> tactic
  val suppress_tracing	: bool ref
  val tapply		: tactic * thm -> thm Sequence.seq
  val THEN		: tactic * tactic -> tactic
  val THEN'		: ('a -> tactic) * ('a -> tactic) -> 'a -> tactic
  val THEN_BEST_FIRST	: tactic * ((thm->bool) * (thm->int) * tactic) 
			  -> tactic
  val THEN_ELSE		: tactic * (tactic*tactic) -> tactic
  val traced_tac	: (thm -> (thm * thm Sequence.seq) option) -> tactic
  val tracify		: bool ref -> tactic -> thm -> thm Sequence.seq
  val trace_BEST_FIRST	: bool ref
  val trace_DEPTH_FIRST	: bool ref
  val trace_REPEAT	: bool ref
  val TRY		: tactic -> tactic
  val TRYALL		: (int -> tactic) -> tactic   
  end
  end;


functor TacticalFun (structure Logic: LOGIC and Drule: DRULE) : TACTICAL = 
struct
structure Thm = Drule.Thm;
structure Sequence = Thm.Sequence;
structure Sign = Thm.Sign;
local open Drule Thm
in

(**** Tactics ****)

(*A tactic maps a proof tree to a sequence of proof trees:
    if length of sequence = 0 then the tactic does not apply;
    if length > 1 then backtracking on the alternatives can occur.*)

datatype tactic = Tactic of thm -> thm Sequence.seq;

fun tapply(Tactic tf, state) = tf (state);

(*Makes a tactic from one that uses the components of the state.*)
fun STATE tacfun = Tactic (fn state => tapply(tacfun state, state));


(*** LCF-style tacticals ***)

(*the tactical THEN performs one tactic followed by another*)
fun (Tactic tf1)  THEN  (Tactic tf2) = 
  Tactic (fn state => Sequence.flats (Sequence.maps tf2 (tf1 state)));


(*The tactical ORELSE uses the first tactic that returns a nonempty sequence.
  Like in LCF, ORELSE commits to either tac1 or tac2 immediately.
  Does not backtrack to tac2 if tac1 was initially chosen. *)
fun (Tactic tf1)  ORELSE  (Tactic tf2) = 
  Tactic (fn state =>  
    case Sequence.pull(tf1 state) of
	None       => tf2 state
      | sequencecell => Sequence.seqof(fn()=> sequencecell));


(*The tactical APPEND combines the results of two tactics.
  Like ORELSE, but allows backtracking on both tac1 and tac2.
  The tactic tac2 is not applied until needed.*)
fun (Tactic tf1)  APPEND  (Tactic tf2) = 
  Tactic (fn state =>  Sequence.append(tf1 state,
                          Sequence.seqof(fn()=> Sequence.pull (tf2 state))));

(*Like APPEND, but interleaves results of tac1 and tac2.*)
fun (Tactic tf1)  INTLEAVE  (Tactic tf2) = 
  Tactic (fn state =>  Sequence.interleave(tf1 state,
                          Sequence.seqof(fn()=> Sequence.pull (tf2 state))));

(*Conditional tactic.
	tac1 ORELSE tac2 = tac1 THEN_ELSE (all_tac, tac2)
	tac1 THEN tac2   = tac1 THEN_ELSE (tac2, no_tac)
*)
fun (Tactic tf) THEN_ELSE (Tactic tf1, Tactic tf2) = 
  Tactic (fn state =>  
    case Sequence.pull(tf state) of
	None    => tf2 state		(*failed; try tactic 2*)
      | seqcell => Sequence.flats 	(*succeeded; use tactic 1*)
	            (Sequence.maps tf1 (Sequence.seqof(fn()=> seqcell))));


(*Versions for combining tactic-valued functions, as in
     SOMEGOAL (resolve_tac rls THEN' assume_tac) *)
fun tac1 THEN' tac2 = fn x => tac1 x THEN tac2 x;
fun tac1 ORELSE' tac2 = fn x => tac1 x ORELSE tac2 x;
fun tac1 APPEND' tac2 = fn x => tac1 x APPEND tac2 x;
fun tac1 INTLEAVE' tac2 = fn x => tac1 x INTLEAVE tac2 x;

(*passes all proofs through unchanged;  identity of THEN*)
val all_tac = Tactic (fn state => Sequence.single state);

(*passes no proofs through;  identity of ORELSE and APPEND*)
val no_tac  = Tactic (fn state => Sequence.null);


(*Make a tactic deterministic by chopping the tail of the proof sequence*)
fun DETERM (Tactic tf) = Tactic (fn state => 
      case Sequence.pull (tf state) of
	      None => Sequence.null
            | Some(x,_) => Sequence.cons(x, Sequence.null));


(*Conditional tactical: testfun controls which tactic to use next.
  Beware: due to eager evaluation, both thentac and elsetac are evaluated.*)
fun COND testfun (Tactic thenf) (Tactic elsef) = Tactic (fn prf =>
    if testfun prf then  thenf prf   else  elsef prf);

(*Do the tactic or else do nothing*)
fun TRY tac = tac ORELSE all_tac;


(*** List-oriented tactics ***)

(* EVERY [tac1,...,tacn]   equals    tac1 THEN ... THEN tacn   *)
fun EVERY tacs = foldr (op THEN) (tacs, all_tac);

(* EVERY' [tf1,...,tfn] i  equals    tf1 i THEN ... THEN tfn i   *)
fun EVERY' tfs = foldr (op THEN') (tfs, K all_tac);

(*Apply every tactic to 1*)
fun EVERY1 tfs = EVERY' tfs 1;

(* FIRST [tac1,...,tacn]   equals    tac1 ORELSE ... ORELSE tacn   *)
fun FIRST tacs = foldr (op ORELSE) (tacs, no_tac);

(* FIRST' [tf1,...,tfn] i  equals    tf1 i ORELSE ... ORELSE tfn i   *)
fun FIRST' tfs = foldr (op ORELSE') (tfs, K no_tac);

(*Apply first tactic to 1*)
fun FIRST1 tfs = FIRST' tfs 1;


(*** Tracing tactics ***)

(*Max number of goals to print -- set by user*)
val goals_limit = ref 10;

(*Print the current proof state and pass it on.*)
val print_tac = Tactic 
    (fn state => 
     (!print_goals_ref (!goals_limit) state;   Sequence.single state));

(*Pause until a line is typed -- if non-empty then fail. *)
val pause_tac = Tactic (fn state => 
  (prs"** Press RETURN to continue: ";
   if input(std_in,1) = "\n" then Sequence.single state
   else (prs"Goodbye\n";  Sequence.null)));

exception TRACE_EXIT of thm
and TRACE_QUIT;

(*Tracing flags*)
val trace_REPEAT= ref false
and trace_DEPTH_FIRST = ref false
and trace_BEST_FIRST = ref false
and suppress_tracing = ref false;

(*Handle all tracing commands for current state and tactic *)
fun exec_trace_command flag (tf, state) = 
   case input_line(std_in) of
       "\n" => tf state
     | "f\n" => Sequence.null
     | "o\n" => (flag:=false;  tf state)
     | "s\n" => (suppress_tracing:=true;  tf state)
     | "x\n" => (prs"Exiting now\n";  raise (TRACE_EXIT state))
     | "quit\n" => raise TRACE_QUIT
     | _     => (prs
"Type RETURN to continue or...\n\
\     f    - to fail here\n\
\     o    - to switch tracing off\n\
\     s    - to suppress tracing until next entry to a tactical\n\
\     x    - to exit at this point\n\
\     quit - to abort this tracing run\n\
\** Well? "     ;  exec_trace_command flag (tf, state));


(*Extract from a tactic, a thm->thm seq function that handles tracing*)
fun tracify flag (Tactic tf) state =
  if !flag andalso not (!suppress_tracing)
           then (!print_goals_ref (!goals_limit) state;  
		 prs"** Press RETURN to continue: ";
		 exec_trace_command flag (tf,state))
  else tf state;

(*Create a tactic whose outcome is given by seqf, handling TRACE_EXIT*)
fun traced_tac seqf = Tactic (fn st =>
    (suppress_tracing := false;
     Sequence.seqof (fn()=> seqf st
		         handle TRACE_EXIT st' => Some(st', Sequence.null))));


(*Deterministic REPEAT: only retains the first outcome; 
  uses less space than REPEAT; tail recursive*)
fun REPEAT_DETERM tac = 
  let val tf = tracify trace_REPEAT tac
      fun drep st =
        case Sequence.pull(tf st) of
  	    None       => Some(st, Sequence.null)
          | Some(st',_) => drep st'
  in  traced_tac drep  end;

(*General REPEAT: maintains a stack of alternatives; tail recursive*)
fun REPEAT tac = 
  let val tf = tracify trace_REPEAT tac
      fun rep qs st = 
	case Sequence.pull(tf st) of
  	    None       => Some(st, Sequence.seqof(fn()=> repq qs))
          | Some(st',q) => rep (q::qs) st'
      and repq [] = None
        | repq(q::qs) = case Sequence.pull q of
  	    None       => repq qs
          | Some(st,q) => rep (q::qs) st
  in  traced_tac (rep [])  end;

(*Repeat 1 or more times*)
fun REPEAT1 tac = tac THEN REPEAT tac;


(** Search tacticals **)

(*Seaarches "satp" reports proof tree as satisfied*)
fun DEPTH_FIRST satp tac = 
 let val tf = tracify trace_DEPTH_FIRST tac
     fun depth [] = None
       | depth(q::qs) =
	  case Sequence.pull q of
	      None         => depth qs
	    | Some(st,stq) => 
		if satp st then Some(st, Sequence.seqof(fn()=> depth(stq::qs)))
		else depth (tf st :: stq :: qs)
  in  traced_tac (fn st => depth([Sequence.single st]))  end;


(*Predicate: Does the rule have fewer than n premises?*)
fun has_fewer_prems n rule = (nprems_of rule < n);

(*Apply a tactic if subgoals remain, else do nothing.*)
val IF_UNSOLVED = COND (has_fewer_prems 1) all_tac;

(*Tactical to reduce the number of premises by 1.
  If no subgoals then it must fail! *)
fun DEPTH_SOLVE_1 tac = STATE
 (fn state => 
    (case nprems_of state of
	0 => no_tac
      | n => DEPTH_FIRST (has_fewer_prems n) tac));

(*Uses depth-first search to solve ALL subgoals*)
val DEPTH_SOLVE = DEPTH_FIRST (has_fewer_prems 1);

(*** Best-first search ***)

(*Insertion into priority queue of states *)
fun insert (nth: int*thm, []) = [nth]
  | insert ((m,th), (n,th')::nths) = 
      if  n<m then (n,th') :: insert ((m,th), nths)
      else if  n=m andalso eq_thm(th,th')
              then (n,th')::nths
              else (m,th)::(n,th')::nths;

(*For creating output sequence*)
fun some_of_list []     = None
  | some_of_list (x::l) = Some (x, Sequence.seqof (fn () => some_of_list l));


(* Best-first search for a state that satisfies satp (incl initial state)
  Function sizef estimates size of problem remaining (smaller means better).
  tactic tf0 sets up the initial priority queue, which is searched by tac. *)
fun (Tactic tf0) THEN_BEST_FIRST (satp, sizef, tac) = 
  let val tf = tracify trace_BEST_FIRST tac
      fun pairsize th = (sizef th, th);
      fun bfs (news,nprfs) =
	   (case  partition satp news  of
		([],nonsats) => next(foldr insert
					(map pairsize nonsats, nprfs)) 
	      | (sats,_)  => some_of_list sats)
      and next [] = None
        | next ((n,prf)::nprfs) =
	    (if !trace_BEST_FIRST 
	       then writeln("state size = " ^ string_of_int n ^ 
		         "  queue length =" ^ string_of_int (length nprfs))  
               else ();
	     bfs (Sequence.list_of_s (tf prf), nprfs))
      fun tf st = bfs (Sequence.list_of_s (tf0 st),  [])
  in traced_tac tf end;

(*Ordinary best-first search, with no initial tactic*)
fun BEST_FIRST (satp,sizef) tac = all_tac THEN_BEST_FIRST (satp,sizef,tac);

(*Breadth-first search to satisfy satpred (including initial state) 
  SLOW -- SHOULD NOT USE APPEND!*)
fun BREADTH_FIRST satpred (Tactic tf) = 
  let val tacf = Sequence.list_of_s o tf;
      fun bfs prfs =
	 (case  partition satpred prfs  of
	      ([],[]) => []
	    | ([],nonsats) => 
		  (prs("breadth=" ^ string_of_int(length nonsats) ^ "\n");
		   bfs (flat (map tacf nonsats)))
	    | (sats,_)  => sats)
  in Tactic (fn state => Sequence.s_of_list (bfs [state])) end;


(** Filtering tacticals **)

(*Returns all states satisfying the predicate*)
fun FILTER pred (Tactic tf) = Tactic
      (fn state => Sequence.filters pred (tf state));

(*Returns all changed states*)
fun CHANGED (Tactic tf)  = 
  Tactic (fn state => 
    let fun diff st = not (eq_thm(state,st))
    in  Sequence.filters diff (tf state)
    end );


(*** Tacticals based on subgoal numbering ***)

(*For n subgoals, performs tf(n) THEN ... THEN tf(1) 
  Essential to work backwards since tf(i) may add/delete subgoals at i. *)
fun ALLGOALS tf = 
  let fun tac 0 = all_tac
	| tac n = tf(n) THEN tac(n-1)
  in  Tactic(fn state => tapply(tac(nprems_of state), state))  end;

(*For n subgoals, performs tf(n) ORELSE ... ORELSE tf(1)  *)
fun SOMEGOAL tf = 
  let fun tac 0 = no_tac
	| tac n = tf(n) ORELSE tac(n-1)
  in  Tactic(fn state => tapply(tac(nprems_of state), state))  end;

(*For n subgoals, performs tf(1) ORELSE ... ORELSE tf(n).
  More appropriate than SOMEGOAL in some cases.*)
fun FIRSTGOAL tf = 
  let fun tac (i,n) = if i>n then no_tac else  tf(i) ORELSE tac (i+1,n)
  in  Tactic(fn state => tapply(tac(1, nprems_of state), state))  end;

(*Repeatedly solve some using tf. *)
fun REPEAT_SOME tf = REPEAT1 (SOMEGOAL (REPEAT1 o tf));

(*Repeatedly solve the first possible subgoal using tf. *)
fun REPEAT_FIRST tf = REPEAT1 (FIRSTGOAL (REPEAT1 o tf));

(*For n subgoals, tries to apply tf to n,...1  *)
fun TRYALL tf = ALLGOALS (TRY o tf);


(*Make a tactic for subgoal i, if there is one.  *)
fun SUBGOAL goalfun i = Tactic(fn state =>
  case drop(i-1, prems_of state) of
      [] => Sequence.null
    | prem::_ => tapply(goalfun (prem,i), state));

(*Tactical for restricting the effect of a tactic to subgoal i.
  Works by making a new state from subgoal i, applying tf to it, and
  composing the resulting metathm with the original state.
  The "main goal" of the new state will not be atomic, some tactics may fail!
  DOES NOT work if tactic affects the main goal other than by instantiation.*)

(* (!!x. PROP ?V) ==> PROP ?V ;  contains NO TYPE VARIABLES.*)
val dummy_quant_rl = 
  standard (forall_elim_var 0 (assume 
                  (read_cterm Sign.pure ("!!x::prop. PROP V",propT))));

(* Prevent the subgoal's assumptions from becoming additional subgoals in the
   new proof state by enclosing them by a universal quantification *)
fun protect_subgoal state i =
  case Sequence.chop (1, bicompose false (false,dummy_quant_rl,1) i state) of
      ([state'],_) => state'
    | _            => error"SELECT_GOAL -- impossible error???";

(*Does the work of SELECT_GOAL. *)
fun select (Tactic tf) state i =
  let val prem::_ = drop(i-1, prems_of state)
      val st0 = trivial (cterm_of (#sign(rep_thm state)) prem);
      fun next st = bicompose false (false, st, nprems_of st) i state
  in  Sequence.flats (Sequence.maps next (tf st0))
  end;

fun SELECT_GOAL tac i = Tactic (fn state =>
  case (i, drop(i-1, prems_of state)) of
      (_,[]) => Sequence.null
    | (1,[_]) => tapply(tac,state)  (*If i=1 and only one subgoal do nothing!*)
    | (_, (Const("==>",_)$_$_) :: _) => select tac (protect_subgoal state i) i
    | (_, _::_) => select tac state i);


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
       METAHYPS (fn prems => tac (prems)) i

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
  open Logic 

  (*Left-to-right replacements: ctpairs = [...,(vi,ti),...].
    Instantiates distinct free variables by terms of same type.*)
  fun free_instantiate ctpairs = 
      forall_elim_list (map snd ctpairs) o forall_intr_list (map fst ctpairs);

  fun free_of s ((a,i), T) =
        Free(s ^ (case i of 0 => a | _ => a ^ "_" ^ string_of_int i),
	     T)

  fun mk_inst (var as Var(v,T))  = (var,  free_of "METAHYP1_" (v,T))
in

fun metahyps_aux_tac tacf (prem,i) = Tactic (fn state =>
  let val {sign,maxidx,...} = rep_thm state
      val cterm = cterm_of sign
      (*find all vars in the hyps -- should find tvars also!*)
      val hyps_vars = foldr add_term_vars (strip_assums_hyp prem, [])
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
      fun embed B = list_all_free (params, list_implies (hyps, B))
      (*Strip the context using elimination rules*)
      fun elim Bhyp = implies_elim_list (forall_elim_list cparams Bhyp) hypths
      (*Embed an ff pair in the original params*)
      fun embed_ff(t,u) = 
	  mk_flexpair (list_abs_free (params, t), list_abs_free (params, u))
      (*Remove parameter abstractions from the ff pairs*)
      fun elim_ff ff = flexpair_abs_elim_list cparams ff
      (*A form of lifting that discharges assumptions.*)
      fun relift st = 
	let val prop = #prop(rep_thm st)
	    val subgoal_vars = (*Vars introduced in the subgoals*)
		  foldr add_term_vars (strip_imp_prems prop, [])
	    and concl_vars = add_term_vars (strip_imp_concl prop, [])
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
  in  Sequence.flats (Sequence.maps next (tapply(tacf subprems, st0)))
  end);
end;

fun METAHYPS tacf = SUBGOAL (metahyps_aux_tac tacf);

end;
end;
