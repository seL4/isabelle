(*  Title: 	Provers/blast
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Generic tableau prover with proof reconstruction

  SKOLEMIZES ReplaceI WRONGLY: allow new vars in prems, or forbid such rules??
  Needs explicit instantiation of assumptions?


Blast_tac is often more powerful than fast_tac, but has some limitations.
Blast_tac...
  * ignores addss, addbefore, addafter; this restriction is intrinsic
  * ignores elimination rules that don't have the correct format
	(conclusion must be a formula variable)
  * ignores types, which can make HOL proofs fail
  * rules must not require higher-order unification, e.g. apply_type in ZF
    + message "Function Var's argument not a bound variable" relates to this
  * its proof strategy is more general but can actually be slower

Known problems:
  "Recursive" chains of rules can sometimes exclude other unsafe formulae
	from expansion.  This happens because newly-created formulae always
	have priority over existing ones.  But obviously recursive rules 
	such as transitivity are treated specially to prevent this.

  With overloading:
        Overloading can't follow all chains of type dependencies.  Cannot
        prove "In1 x ~: Part A In0" because PartE introducees the polymorphic
	equality In1 x = In0 y, when the corresponding rule uses the (distinct)
	set equality.  Workaround: supply a type instance of the rule that
	creates new equalities (e.g. PartE in HOL/ex/Simult)
	==> affects freeness reasoning about Sexp constants (since they have
		type ... set)

  With substition for equalities (hyp_subst_tac):
        When substitution affects a haz formula or literal, it is moved
        back to the list of safe formulae.
        But there's no way of putting it in the right place.  A "moved" or
        "no DETERM" flag would prevent proofs failing here.
*)


(*Should be a type abbreviation?*)
type netpair = (int*(bool*thm)) Net.net * (int*(bool*thm)) Net.net;


(*Assumptions about constants:
  --The negation symbol is "Not"
  --The equality symbol is "op ="
  --The is-true judgement symbol is "Trueprop"
  --There are no constants named "*Goal* or "*False*"
*)
signature BLAST_DATA =
  sig
  type claset
  val notE		: thm		(* [| ~P;  P |] ==> R *)
  val ccontr		: thm		
  val contr_tac 	: int -> tactic
  val dup_intr		: thm -> thm
  val vars_gen_hyp_subst_tac : bool -> int -> tactic
  val claset		: claset ref
  val rep_claset	: 
      claset -> {safeIs: thm list, safeEs: thm list, 
		 hazIs: thm list, hazEs: thm list,
		 uwrapper: (int -> tactic) -> (int -> tactic),
		 swrapper: (int -> tactic) -> (int -> tactic),
		 safe0_netpair: netpair, safep_netpair: netpair,
		 haz_netpair: netpair, dup_netpair: netpair}
  end;


signature BLAST =
  sig
  type claset 
  datatype term = 
      Const of string
    | OConst of string * int
    | Skolem of string * term option ref list
    | Free  of string
    | Var   of term option ref
    | Bound of int
    | Abs   of string*term
    | $  of term*term;
  type branch
  val depth_tac 	: claset -> int -> int -> tactic
  val blast_tac 	: claset -> int -> tactic
  val Blast_tac 	: int -> tactic
  val declConsts 	: string list * thm list -> unit
  (*debugging tools*)
  val trace	        : bool ref
  val fullTrace	        : branch list list ref
  val fromTerm	        : Type.type_sig -> Term.term -> term
  val fromSubgoal       : Type.type_sig -> Term.term -> term
  val toTerm	        : int -> term -> Term.term
  val readGoal          : Sign.sg -> string -> term
  val tryInThy		: theory -> int -> string ->
		  (int->tactic) list * branch list list * (int*int*exn) list
  val trygl		: claset -> int -> int ->
		  (int->tactic) list * branch list list * (int*int*exn) list
  val Trygl		: int -> int -> 
                  (int->tactic) list * branch list list * (int*int*exn) list
  val normBr		: branch -> branch
  end;


functor BlastFun(Data: BLAST_DATA) : BLAST = 
struct

type claset = Data.claset;

val trace = ref false;

datatype term = 
    Const of string
  | OConst of string * int
  | Skolem of string * term option ref list
  | Free  of string
  | Var   of term option ref
  | Bound of int
  | Abs   of string*term
  | op $  of term*term;


(** Basic syntactic operations **)

fun is_Var (Var _) = true
  | is_Var _ = false;

fun dest_Var (Var x) =  x;


fun rand (f$x) = x;

(* maps   (f, [t1,...,tn])  to  f(t1,...,tn) *)
val list_comb : term * term list -> term = foldl (op $);


(* maps   f(t1,...,tn)  to  (f, [t1,...,tn]) ; naturally tail-recursive*)
fun strip_comb u : term * term list = 
    let fun stripc (f$t, ts) = stripc (f, t::ts)
        |   stripc  x =  x 
    in  stripc(u,[])  end;


(* maps   f(t1,...,tn)  to  f , which is never a combination *)
fun head_of (f$t) = head_of f
  | head_of u = u;


(** Particular constants **)

fun negate P = Const"Not" $ P;

fun mkGoal P = Const"*Goal*" $ P;

fun isGoal (Const"*Goal*" $ _) = true
  | isGoal _                   = false;

val Trueprop = Term.Const("Trueprop", Type("o",[])-->propT);
fun mk_tprop P = Term.$ (Trueprop, P);

fun isTrueprop (Term.Const("Trueprop",_)) = true
  | isTrueprop _                          = false;


(** Dealing with overloaded constants **)

(*Result is a symbol table, indexed by names of overloaded constants.
  Each constant maps to a list of (pattern,Blast.Const) pairs.
  Any Term.Const that matches a pattern gets replaced by the Blast.Const.
*)
fun addConsts (t as Term.Const(a,_), tab) =
     (case Symtab.lookup (tab,a) of
	  None    => tab  (*ignore: not a constant that we are looking for*)
	| Some patList => 
	      (case gen_assoc (op aconv) (patList, t) of
		  None => Symtab.update
		           ((a, (t, OConst (a, length patList)) :: patList), 
			    tab)
		 | _    => tab))
  | addConsts (Term.Abs(_,_,body), tab) = addConsts (body, tab)
  | addConsts (Term.$ (t,u), tab) = addConsts (t, addConsts (u, tab))
  | addConsts (_,            tab) = tab (*ignore others*);


fun addRules (rls,tab) = foldr addConsts (map (#prop o rep_thm) rls, tab);

fun declConst (a,tab) = 
    case Symtab.lookup (tab,a) of
	None   => Symtab.update((a,[]), tab)	(*create a brand new entry*)
      | Some _ => tab				(*preserve old entry*);

(*maps the name of each overloaded constant to a list of archetypal constants,
  which may be polymorphic.*)
local
val overLoadTab = ref (Symtab.null : (Term.term * term) list Symtab.table)
    (*The alists in this table should only be increased*)
in

fun declConsts (names, rls) =
    overLoadTab := addRules (rls, foldr declConst (names, !overLoadTab));


(*Convert a possibly overloaded Term.Const to a Blast.Const*)
fun fromConst tsig (t as Term.Const (a,_)) =
  let fun find []                  = Const a
	| find ((pat,t')::patList) =
		if Pattern.matches tsig (pat,t) then t' 
		else find patList
  in  case Symtab.lookup(!overLoadTab, a) of
	   None         => Const a
	 | Some patList => find patList
  end;
end;


(*Tests whether 2 terms are alpha-convertible; chases instantiations*)
fun (Const a)      aconv (Const b)      = a=b
  | (OConst ai)    aconv (OConst bj)    = ai=bj
  | (Skolem (a,_)) aconv (Skolem (b,_)) = a=b  (*arglists must then be equal*)
  | (Free a)       aconv (Free b)       = a=b
  | (Var(ref(Some t))) aconv u          = t aconv u
  | t aconv (Var(ref(Some u)))          = t aconv u
  | (Var v)        aconv (Var w)        = v=w	(*both Vars are un-assigned*)
  | (Bound i)      aconv (Bound j)      = i=j
  | (Abs(_,t))     aconv (Abs(_,u))     = t aconv u
  | (f$t)          aconv (g$u)          = (f aconv g) andalso (t aconv u)
  | _ aconv _  =  false;


fun mem_term (_, [])     = false
  | mem_term (t, t'::ts) = t aconv t' orelse mem_term(t,ts);

fun ins_term(t,ts) = if mem_term(t,ts) then ts else t :: ts;

fun mem_var (v: term option ref, []) = false
  | mem_var (v, v'::vs)              = v=v' orelse mem_var(v,vs);

fun ins_var(v,vs) = if mem_var(v,vs) then vs else v :: vs;


(** Vars **)

(*Accumulates the Vars in the term, suppressing duplicates*)
fun add_term_vars (Skolem(a,args),	vars) = add_vars_vars(args,vars)
  | add_term_vars (Var (v as ref None),	vars) = ins_var (v, vars)
  | add_term_vars (Var (ref (Some u)), vars)  = add_term_vars(u,vars)
  | add_term_vars (Abs (_,body),	vars) = add_term_vars(body,vars)
  | add_term_vars (f$t,	vars) =  add_term_vars (f, add_term_vars(t, vars))
  | add_term_vars (_,	vars) = vars
(*Term list version.  [The fold functionals are slow]*)
and add_terms_vars ([],    vars) = vars
  | add_terms_vars (t::ts, vars) = add_terms_vars (ts, add_term_vars(t,vars))
(*Var list version.*)
and add_vars_vars ([],    vars) = vars
  | add_vars_vars (ref (Some u) :: vs, vars) = 
	add_vars_vars (vs, add_term_vars(u,vars))
  | add_vars_vars (v::vs, vars) =   (*v must be a ref None*)
	add_vars_vars (vs, ins_var (v, vars));


(*Chase assignments in "vars"; return a list of unassigned variables*)
fun vars_in_vars vars = add_vars_vars(vars,[]);



(*increment a term's non-local bound variables
     inc is  increment for bound variables
     lev is  level at which a bound variable is considered 'loose'*)
fun incr_bv (inc, lev, u as Bound i) = if i>=lev then Bound(i+inc) else u 
  | incr_bv (inc, lev, Abs(a,body)) = Abs(a, incr_bv(inc,lev+1,body))
  | incr_bv (inc, lev, f$t) = incr_bv(inc,lev,f) $ incr_bv(inc,lev,t)
  | incr_bv (inc, lev, u) = u;

fun incr_boundvars  0  t = t
  | incr_boundvars inc t = incr_bv(inc,0,t);


(*Accumulate all 'loose' bound vars referring to level 'lev' or beyond.
   (Bound 0) is loose at level 0 *)
fun add_loose_bnos (Bound i, lev, js)   = if i<lev then js  
					  else  (i-lev) ins_int js
  | add_loose_bnos (Abs (_,t), lev, js) = add_loose_bnos (t, lev+1, js)
  | add_loose_bnos (f$t, lev, js)       =
	        add_loose_bnos (f, lev, add_loose_bnos (t, lev, js)) 
  | add_loose_bnos (_, _, js)           = js;

fun loose_bnos t = add_loose_bnos (t, 0, []);

fun subst_bound (arg, t) : term = 
  let fun subst (t as Bound i, lev) =
 	    if i<lev then  t    (*var is locally bound*)
	    else  if i=lev then incr_boundvars lev arg
		           else Bound(i-1)  (*loose: change it*)
	| subst (Abs(a,body), lev) = Abs(a, subst(body,lev+1))
	| subst (f$t, lev) =  subst(f,lev)  $  subst(t,lev)
	| subst (t,lev)    = t
  in  subst (t,0)  end;


(*Normalize...but not the bodies of ABSTRACTIONS*)
fun norm t = case t of
    Skolem (a,args)      => Skolem(a, vars_in_vars args)
  | (Var (ref None))     => t
  | (Var (ref (Some u))) => norm u
  | (f $ u) => (case norm f of
                    Abs(_,body) => norm (subst_bound (u, body))
                  | nf => nf $ norm u)
  | _ => t;


(*Weak (one-level) normalize for use in unification*)
fun wkNormAux t = case t of
    (Var v) => (case !v of
		    Some u => wkNorm u
		  | None   => t)
  | (f $ u) => (case wkNormAux f of
		    Abs(_,body) => wkNorm (subst_bound (u, body))
		  | nf          => nf $ u)
  | Abs (a,body) =>	(*eta-contract if possible*)
	(case wkNormAux body of
	     nb as (f $ t) => 
		 if (0 mem_int loose_bnos f) orelse wkNorm t <> Bound 0
		 then Abs(a,nb)
		 else wkNorm (incr_boundvars ~1 f)
	   | nb => Abs (a,nb))
  | _ => t
and wkNorm t = case head_of t of
    Const _        => t
  | OConst _       => t
  | Skolem(a,args) => t
  | Free _         => t
  | _              => wkNormAux t;


(*Does variable v occur in u?  For unification.*)
fun varOccur v = 
  let fun occL [] = false	(*same as (exists occ), but faster*)
	| occL (u::us) = occ u orelse occL us
      and occ (Var w) = 
	      v=w orelse
              (case !w of None   => false
	                | Some u => occ u)
        | occ (Skolem(_,args)) = occL (map Var args)
        | occ (Abs(_,u)) = occ u
        | occ (f$u)      = occ u  orelse  occ f
        | occ (_)        = false;
  in  occ  end;

exception UNIFY;

val trail = ref [] : term option ref list ref;
val ntrail = ref 0;


(*Restore the trail to some previous state: for backtracking*)
fun clearTo n =
    while !ntrail<>n do
	(hd(!trail) := None;
	 trail := tl (!trail);
	 ntrail := !ntrail - 1);


(*First-order unification with bound variables.  
  "vars" is a list of variables local to the rule and NOT to be put
	on the trail (no point in doing so)
*)
fun unify(allowClash,vars,t,u) =
    let val n = !ntrail 
	fun update (t as Var v, u) =
	    if t aconv u then ()
	    else if varOccur v u then raise UNIFY 
	    else if mem_var(v, vars) then v := Some u
		 else (*avoid updating Vars in the branch if possible!*)
		      if is_Var u andalso mem_var(dest_Var u, vars)
		      then dest_Var u := Some t
		      else (v := Some u;
			    trail := v :: !trail;  ntrail := !ntrail + 1)
	fun unifyAux (t,u) = 
	    case (wkNorm t,  wkNorm u) of
		(nt as Var v,  nu) => update(nt,nu)
	      | (nu,  nt as Var v) => update(nt,nu)
	      | (Const a, OConst(b,_))  => if allowClash andalso a=b then ()
		                           else raise UNIFY
	      | (OConst(a,_), Const b)  => if allowClash andalso a=b then ()
		                           else raise UNIFY
	      | (Abs(_,t'),  Abs(_,u')) => unifyAux(t',u')
		    (*NB: can yield unifiers having dangling Bound vars!*)
	      | (f$t',  g$u') => (unifyAux(f,g); unifyAux(t',u'))
	      | (nt,  nu)    => if nt aconv nu then () else raise UNIFY
    in  (unifyAux(t,u); true) handle UNIFY => (clearTo n; false)
    end;


(*Convert from "real" terms to prototerms; eta-contract*)
fun fromTerm tsig t =
  let val alist = ref []
      fun from (t as Term.Const _) = fromConst tsig t
	| from (Term.Free  (a,_)) = Free a
	| from (Term.Bound i)     = Bound i
	| from (Term.Var (ixn,T)) = 
	      (case (assoc_string_int(!alist,ixn)) of
		   None => let val t' = Var(ref None)
		           in  alist := (ixn, (t', T)) :: !alist;  t'
			   end
		 | Some (v,_) => v)
	| from (Term.Abs (a,_,u)) = 
	      (case  from u  of
		u' as (f $ Bound 0) => 
		  if (0 mem_int loose_bnos f) then Abs(a,u')
		  else incr_boundvars ~1 f 
	      | u' => Abs(a,u'))
	| from (Term.$ (f,u)) = from f $ from u
  in  from t  end;

(* A1==>...An==>B  goes to  [A1,...,An], where B is not an implication *)
fun strip_imp_prems (Const"==>" $ (Const"Trueprop" $ A) $ B) = 
           A :: strip_imp_prems B
  | strip_imp_prems (Const"==>" $ A $ B) = A :: strip_imp_prems B
  | strip_imp_prems _ = [];

(* A1==>...An==>B  goes to B, where B is not an implication *)
fun strip_imp_concl (Const"==>" $ A $ B) = strip_imp_concl B
  | strip_imp_concl (Const"Trueprop" $ A) = A
  | strip_imp_concl A = A : term;


(*** Conversion of Elimination Rules to Tableau Operations ***)

(*The conclusion becomes the goal/negated assumption *False*: delete it!*)
fun squash_nots [] = []
  | squash_nots (Const "*Goal*" $ (Var (ref (Some (Const"*False*")))) :: Ps) =
	squash_nots Ps
  | squash_nots (Const "Not" $ (Var (ref (Some (Const"*False*")))) :: Ps) =
	squash_nots Ps
  | squash_nots (P::Ps) = P :: squash_nots Ps;

fun skoPrem vars (Const "all" $ Abs (_, P)) =
        skoPrem vars (subst_bound (Skolem (gensym "S_", vars), P))
  | skoPrem vars P = P;

fun convertPrem t = 
    squash_nots (mkGoal (strip_imp_concl t) :: strip_imp_prems t);

(*Expects elimination rules to have a formula variable as conclusion*)
fun convertRule vars t =
  let val (P::Ps) = strip_imp_prems t
      val Var v   = strip_imp_concl t
  in  v := Some (Const"*False*");
      (P, map (convertPrem o skoPrem vars) Ps) 
  end;


(*Like dup_elim, but puts the duplicated major premise FIRST*)
fun rev_dup_elim th = th RSN (2, revcut_rl) |> assumption 2 |> Sequence.hd;


(*Count new hyps so that they can be rotated*)
fun nNewHyps []                         = 0
  | nNewHyps (Const "*Goal*" $ _ :: Ps) = nNewHyps Ps
  | nNewHyps (P::Ps)                    = 1 + nNewHyps Ps;

fun rot_subgoals_tac [] i st      = Sequence.single st
  | rot_subgoals_tac (k::ks) i st =
      rot_subgoals_tac ks (i+1) (Sequence.hd (rotate_tac (~k) i st))
      handle OPTION _ => Sequence.null;

fun TRACE rl tac st i = if !trace then (prth rl; tac st i) else tac st i;

(*Tableau rule from elimination rule.  Flag "dup" requests duplication of the
  affected formula.*)
fun fromRule vars rl = 
  let val {tsig,...} = Sign.rep_sg (#sign (rep_thm rl))
      val trl = rl |> rep_thm |> #prop |> fromTerm tsig |> convertRule vars
      fun tac dup i = 
	  TRACE rl (etac (if dup then rev_dup_elim rl else rl)) i
	  THEN rot_subgoals_tac (map nNewHyps (#2 trl)) i
	  
  in Option.SOME (trl, tac) end
  handle Bind => (*reject: conclusion is not just a variable*)
   (if !trace then (writeln"Warning: ignoring ill-formed elimination rule";
		    print_thm rl)
    else ();
    Option.NONE);


(*** Conversion of Introduction Rules ***)

fun convertIntrPrem t = mkGoal (strip_imp_concl t) :: strip_imp_prems t;

fun convertIntrRule vars t =
  let val Ps = strip_imp_prems t
      val P  = strip_imp_concl t
  in  (mkGoal P, map (convertIntrPrem o skoPrem vars) Ps) 
  end;

(*Tableau rule from introduction rule.  Since haz rules are now delayed, 
  "dup" is always FALSE for introduction rules.*)
fun fromIntrRule vars rl = 
  let val {tsig,...} = Sign.rep_sg (#sign (rep_thm rl))
      val trl = rl |> rep_thm |> #prop |> fromTerm tsig |> convertIntrRule vars
      fun tac dup i = 
	  TRACE rl (DETERM o (rtac (if dup then Data.dup_intr rl else rl))) i
	  THEN rot_subgoals_tac (map nNewHyps (#2 trl)) i
  in (trl, tac) end;


val dummyVar = Term.Var (("etc",0), dummyT);

(*Convert from prototerms to ordinary terms with dummy types
  Ignore abstractions; identify all Vars; STOP at given depth*)
fun toTerm 0 _             = dummyVar
  | toTerm d (Const a)     = Term.Const (a,dummyT)
  | toTerm d (OConst(a,_)) = Term.Const (a,dummyT)
  | toTerm d (Skolem(a,_)) = Term.Const (a,dummyT)
  | toTerm d (Free a)      = Term.Free  (a,dummyT)
  | toTerm d (Bound i)     = Term.Bound i
  | toTerm d (Var _)       = dummyVar
  | toTerm d (Abs(a,_))    = dummyVar
  | toTerm d (f $ u)       = Term.$ (toTerm d f, toTerm (d-1) u);


fun netMkRules P vars (nps: netpair list) =
  case P of
      (Const "*Goal*" $ G) =>
	let val pG = mk_tprop (toTerm 2 G)
	    val intrs = List.concat 
		             (map (fn (inet,_) => Net.unify_term inet pG) 
			      nps)
	in  map (fromIntrRule vars o #2) (orderlist intrs)  end
    | _ =>
	let val pP = mk_tprop (toTerm 3 P)
	    val elims = List.concat 
		             (map (fn (_,enet) => Net.unify_term enet pP) 
			      nps)
	in  List.mapPartial (fromRule vars o #2) (orderlist elims)  end;

(**
end;
**)


(*Pending formulae carry md (may duplicate) flags*)
type branch = ((term*bool) list *	(*safe formulae on this level*)
               (term*bool) list) list * (*haz formulae  on this level*)
	      term list *               (*literals: irreducible formulae*)
	      term option ref list *    (*variables occurring in branch*)
	      int;                      (*resource limit*)

val fullTrace = ref[] : branch list list ref;

(*Normalize a branch--for tracing*)
fun norm2 (G,md) = (norm G, md);

fun normLev (Gs,Hs) = (map norm2 Gs, map norm2 Hs);

fun normBr (br, lits, vars, lim) =
     (map normLev br, map norm lits, vars, lim);


val dummyVar2 = Term.Var(("var",0), dummyT);

(*Convert from prototerms to ordinary terms with dummy types for tracing*)
fun showTerm d (Const a)     = Term.Const (a,dummyT)
  | showTerm d (OConst(a,_)) = Term.Const (a,dummyT)
  | showTerm d (Skolem(a,_)) = Term.Const (a,dummyT)
  | showTerm d (Free a)      = Term.Free  (a,dummyT)
  | showTerm d (Bound i)     = Term.Bound i
  | showTerm d (Var(ref(Some u))) = showTerm d u
  | showTerm d (Var(ref None))    = dummyVar2
  | showTerm d (Abs(a,t))    = if d=0 then dummyVar
			       else Term.Abs(a, dummyT, showTerm (d-1) t)
  | showTerm d (f $ u)       = if d=0 then dummyVar
			       else Term.$ (showTerm d f, showTerm (d-1) u);


fun traceTerm sign t = Sign.string_of_term sign (showTerm 8 (norm t));


(*Print tracing information at each iteration of prover*)
fun tracing sign brs = 
  let fun printPairs (((G,_)::_,_)::_)  = prs(traceTerm sign G)
	| printPairs (([],(H,_)::_)::_) = prs(traceTerm sign H ^ "\t (Unsafe)")
	| printPairs _                 = ()
      fun printBrs (brs0 as (pairs, lits, _, lim) :: brs) =
	    (fullTrace := brs0 :: !fullTrace;
	     seq (fn _ => prs "+") brs;
	     prs (" [" ^ Int.toString lim ^ "] ");
	     printPairs pairs;
	     writeln"")
  in if !trace then printBrs (map normBr brs) else ()
  end;

(*Tracing: variables updated in the last branch operation?*)
fun traceVars ntrl =
    if !trace then 
       (case !ntrail-ntrl of
	    0 => writeln""
	  | 1 => writeln"\t1 variable updated"
	  | n => writeln("\t" ^ Int.toString n ^ " variables updated"))
    else ();

(*Tracing: how many new branches are created?*)
fun traceNew prems =
    if !trace then 
        case length prems of
	    0 => prs"branch closed by rule"
	  | 1 => prs"branch extended (1 new subgoal)"
	  | n => prs("branch split: "^ Int.toString n ^ " new subgoals")
    else ();



(*** Code for handling equality: naive substitution, like hyp_subst_tac ***)

(*Replace the ATOMIC term "old" by "new" in t*)  
fun subst_atomic (old,new) t =
    let fun subst (Var(ref(Some u))) = subst u
	  | subst (Abs(a,body))      = Abs(a, subst body)
	  | subst (f$t)              = subst f $ subst t
	  | subst t                  = if t aconv old then new else t
    in  subst t  end;

(*Eta-contract a term from outside: just enough to reduce it to an atom*)
fun eta_contract_atom (t0 as Abs(a, body)) = 
      (case  eta_contract2 body  of
        f $ Bound 0 => if (0 mem_int loose_bnos f) then t0
		       else eta_contract_atom (incr_boundvars ~1 f)
      | _ => t0)
  | eta_contract_atom t = t
and eta_contract2 (f$t) = f $ eta_contract_atom t
  | eta_contract2 t     = eta_contract_atom t;


(*When can we safely delete the equality?
    Not if it equates two constants; consider 0=1.
    Not if it resembles x=t[x], since substitution does not eliminate x.
    Not if it resembles ?x=0; another goal could instantiate ?x to Suc(i)
  Prefer to eliminate Bound variables if possible.
  Result:  true = use as is,  false = reorient first *)

(*Does t occur in u?  For substitution.  
  Does NOT check args of Skolem terms: substitution does not affect them.
  NOT reflexive since hyp_subst_tac fails on x=x.*)
fun substOccur t = 
  let fun occEq u = (t aconv u) orelse occ u
      and occ (Var(ref None))    = false
	| occ (Var(ref(Some u))) = occEq u
        | occ (Abs(_,u))         = occEq u
        | occ (f$u)              = occEq u  orelse  occEq f
        | occ (_)                = false;
  in  occEq  end;

exception DEST_EQ;

(*Take apart an equality (plain or overloaded).  NO constant Trueprop*)
fun dest_eq (Const  "op ="     $ t $ u) = 
		(eta_contract_atom t, eta_contract_atom u)
  | dest_eq (OConst("op =",_)  $ t $ u) = 
		(eta_contract_atom t, eta_contract_atom u)
  | dest_eq _                           = raise DEST_EQ;

fun check (t,u,v) = if substOccur t u then raise DEST_EQ else v;

(*IF the goal is an equality with a substitutable variable 
  THEN orient that equality ELSE raise exception DEST_EQ*)
fun orientGoal (t,u) = case (t,u) of
       (Skolem _, _) => check(t,u,(t,u))	(*eliminates t*)
     | (_, Skolem _) => check(u,t,(u,t))	(*eliminates u*)
     | (Free _, _)   => check(t,u,(t,u))	(*eliminates t*)
     | (_, Free _)   => check(u,t,(u,t))	(*eliminates u*)
     | _             => raise DEST_EQ;

(*Substitute through the branch if an equality goal (else raise DEST_EQ).
  Moves affected literals back into the branch, but it is not clear where
  they should go: this could make proofs fail.  ??? *)
fun equalSubst sign (G, pairs, lits, vars, lim) = 
  let val (t,u) = orientGoal(dest_eq G)
      val subst = subst_atomic (t,u)
      fun subst2(G,md) = (subst G, md)
      (*substitute throughout Haz list; move affected ones to Safe part*)
      fun subHazs ([], Gs, nHs)         = (Gs,nHs)
	| subHazs ((H,md)::Hs, Gs, nHs) =
	    let val nH = subst H
	    in  if nH aconv H then subHazs (Hs, Gs, (H,md)::nHs)
		              else subHazs (Hs, (nH,md)::Gs, nHs)
            end
      val pairs' = map (fn(Gs,Hs) => subHazs(rev Hs, map subst2 Gs, [])) pairs
      (*substitute throughout literals; move affected ones to Safe part*)
      fun subLits ([], [], nlits) =          (pairs', nlits, vars, lim)
	| subLits ([], Gs, nlits) = ((Gs,[])::pairs', nlits, vars, lim)
	| subLits (lit::lits, Gs, nlits) =
	    let val nlit = subst lit
	    in  if nlit aconv lit then subLits (lits, Gs, nlit::nlits)
		                  else subLits (lits, (nlit,true)::Gs, nlits)
            end
  in  if !trace then writeln ("Substituting " ^ traceTerm sign u ^
			      " for " ^ traceTerm sign t ^ " in branch" )
      else ();
      subLits (rev lits, [], [])  
  end;


exception NEWBRANCHES and CLOSEF;

exception PROVE;

val eq_contr_tac = eresolve_tac [Data.notE]  THEN'  eq_assume_tac;

val eContr_tac  = TRACE Data.notE (eq_contr_tac ORELSE' Data.contr_tac);
val eAssume_tac = TRACE asm_rl   (eq_assume_tac ORELSE' assume_tac);

(*Try to unify complementary literals and return the corresponding tactic. *) 
fun tryClose (Const"*Goal*" $ G,  L) = 
	if unify(true,[],G,L) then Some eAssume_tac else None
  | tryClose (G,  Const"*Goal*" $ L) = 
	if unify(true,[],G,L) then Some eAssume_tac else None
  | tryClose (Const"Not" $ G,  L)    = 
	if unify(true,[],G,L) then Some eContr_tac else None
  | tryClose (G,  Const"Not" $ L)    = 
	if unify(true,[],G,L) then Some eContr_tac else None
  | tryClose _                       = None;


(*Were there Skolem terms in the premise?  Must NOT chase Vars*)
fun hasSkolem (Skolem _)     = true
  | hasSkolem (Abs (_,body)) = hasSkolem body 
  | hasSkolem (f$t)          =  hasSkolem f orelse hasSkolem t
  | hasSkolem _              = false;

(*Attach the right "may duplicate" flag to new formulae: if they contain
  Skolem terms then allow duplication.*)
fun joinMd md [] = []
  | joinMd md (G::Gs) = (G, hasSkolem G orelse md) :: joinMd md Gs;

(*Convert a Goal to an ordinary Not.  Used also in dup_intr, where a goal like
  Ex(P) is duplicated as the assumption ~Ex(P). *)
fun negOfGoal (Const"*Goal*" $ G) = negate G
  | negOfGoal G                   = G;

fun negOfGoal2 (G,md) = (negOfGoal G, md);

(*Converts all Goals to Nots in the safe parts of a branch.  They could
  have been moved there from the literals list after substitution (equalSubst).
  There can be at most one--this function could be made more efficient.*)
fun negOfGoals pairs = map (fn (Gs,haz) => (map negOfGoal2 Gs, haz)) pairs;

(*Tactic.  Convert *Goal* to negated assumption in FIRST position*)
val negOfGoal_tac = rtac Data.ccontr THEN' rotate_tac ~1;


(** Backtracking and Pruning **)

(*clashVar vars (n,trail) determines whether any of the last n elements
  of "trail" occur in "vars" OR in their instantiations*)
fun clashVar [] = (fn _ => false)
  | clashVar vars =
      let fun clash (0, _)     = false
	    | clash (_, [])    = false
	    | clash (n, v::vs) = exists (varOccur v) vars orelse clash(n-1,vs)
      in  clash  end;


(*nbrs = # of branches just prior to closing this one.  Delete choice points
  for goals proved by the latest inference, provided NO variables in the
  next branch have been updated.*)
fun prune (1, nxtVars, choices) = choices  (*DON'T prune at very end: allow 
					     backtracking over bad proofs*)
  | prune (nbrs, nxtVars, choices) =
      let fun traceIt last =
		let val ll = length last
		    and lc = length choices
		in if !trace andalso ll<lc then
		    (writeln("Pruning " ^ Int.toString(lc-ll) ^ " levels"); 
		     last)
		   else last
		end
	  fun pruneAux (last, _, _, []) = last
	    | pruneAux (last, ntrl, trl, (ntrl',nbrs',exn) :: choices) =
		if nbrs' < nbrs 
		then last  (*don't backtrack beyond first solution of goal*)
		else if nbrs' > nbrs then pruneAux (last, ntrl, trl, choices)
		else (* nbrs'=nbrs *)
		     if clashVar nxtVars (ntrl-ntrl', trl) then last
		     else (*no clashes: can go back at least this far!*)
			  pruneAux(choices, ntrl', List.drop(trl, ntrl-ntrl'), 
				   choices)
  in  traceIt (pruneAux (choices, !ntrail, !trail, choices))  end;

fun nextVars ((br, lits, vars, lim) :: _) = map Var vars
  | nextVars []                           = [];

fun backtrack (choices as (ntrl, nbrs, exn)::_) = 
      (if !trace then (writeln ("Backtracking; now there are " ^ 
				Int.toString nbrs ^ " branches"))
                 else (); 
       raise exn)
  | backtrack _ = raise PROVE;

(*Add the literal G, handling *Goal* and detecting duplicates.*)
fun addLit (Const "*Goal*" $ G, lits) = 
      (*New literal is a *Goal*, so change all other Goals to Nots*)
      let fun bad (Const"*Goal*" $ _) = true
	    | bad (Const"Not" $ G')   = G aconv G'
	    | bad _                   = false;
	  fun change [] = []
	    | change (Const"*Goal*" $ G' :: lits) = 
		  if G aconv G' then change lits
		  else Const"Not" $ G' :: change lits
	    | change (Const"Not" $ G' :: lits)    = 
		  if G aconv G' then change lits
		  else Const"Not" $ G' :: change lits
	    | change (lit::lits) = lit :: change lits
      in
	Const "*Goal*" $ G :: (if exists bad lits then change lits else lits)
      end
  | addLit (G,lits) = ins_term(G, lits)


(*For calculating the "penalty" to assess on a branching factor of n
  log2 seems a little too severe*)
fun log n = if n<4 then 0 else 1 + log(n div 4);


(*match(t,u) says whether the term u might be an instance of the pattern t
  Used to detect "recursive" rules such as transitivity*)
fun match (Var _) u   = true
  | match (Const"*Goal*") (Const"Not") = true
  | match (Const"Not") (Const"*Goal*") = true
  | match (Const a) (Const b) = (a=b)
  | match (OConst ai) (OConst bj) = (ai=bj)
  | match (Free a) (Free b) = (a=b)
  | match (Bound i) (Bound j) = (i=j)
  | match (Abs(_,t)) (Abs(_,u)) = match t u
  | match (f$t) (g$u) = match f g andalso match t u
  | match t u   = false;


(*Tableau prover based on leanTaP.  Argument is a list of branches.  Each 
  branch contains a list of unexpanded formulae, a list of literals, and a 
  bound on unsafe expansions.*)
fun prove (sign, cs, brs, cont) =
 let val {safe0_netpair, safep_netpair, haz_netpair, ...} = Data.rep_claset cs
     val safeList = [safe0_netpair, safep_netpair]
     and hazList  = [haz_netpair]
     fun prv (tacs, trs, choices, []) = cont (tacs, trs, choices)
       | prv (tacs, trs, choices, 
	      brs0 as (((G,md)::br, haz)::pairs, lits, vars, lim) :: brs) =
	  let exception PRV (*backtrack to precisely this recursion!*)
	      val ntrl = !ntrail 
	      val nbrs = length brs0
              val nxtVars = nextVars brs
	      val G = norm G
	      val rules = netMkRules G vars safeList
	      (*Make a new branch, decrementing "lim" if instantiations occur*)
	      fun newBr (vars',lim') prems =
		  map (fn prem => 
		       if (exists isGoal prem) 
		       then (((joinMd md prem, []) :: 
			      negOfGoals ((br, haz)::pairs)),
			     map negOfGoal lits, 
			     vars', lim') 
		       else (((joinMd md prem, []) :: (br, haz) :: pairs),
			     lits, vars', lim'))
		  prems @
		  brs		  
	      (*Seek a matching rule.  If unifiable then add new premises
                to branch.*)
	      fun deeper [] = raise NEWBRANCHES
		| deeper (((P,prems),tac)::grls) =
		    if unify(false, add_term_vars(P,[]), P, G) 
		    then  (*P comes from the rule; G comes from the branch.*)
		     let val ntrl' = !ntrail
			 val lim' = if ntrl < !ntrail 
				    then lim - (1+log(length rules))
				    else lim   (*discourage branching updates*)
			 val vars  = vars_in_vars vars
			 val vars' = foldr add_terms_vars (prems, vars)
			 val choices' = (ntrl, nbrs, PRV) :: choices
			 val tacs' = (DETERM o (tac false)) :: tacs 
					 (*no duplication*)
		     in
			 traceNew prems;  traceVars ntrl;
			 (if null prems then (*closed the branch: prune!*)
			    prv(tacs',  brs0::trs, 
				prune (nbrs, nxtVars, choices'),
				brs)
			  else
			  if lim'<0 (*faster to kill ALL the alternatives*)
			  then raise NEWBRANCHES
			  else
			    prv(tacs',  brs0::trs, choices',
				newBr (vars',lim') prems))
                         handle PRV => 
			   if ntrl < ntrl' (*Vars have been updated*)
			      then
				(*Backtrack at this level.
				  Reset Vars and try another rule*)
				(clearTo ntrl;  deeper grls)
			   else (*backtrack to previous level*)
				backtrack choices
		     end
		    else deeper grls
	      (*Try to close branch by unifying with head goal*)
	      fun closeF [] = raise CLOSEF
		| closeF (L::Ls) = 
		    case tryClose(G,L) of
			None     => closeF Ls
		      | Some tac => 
			    let val choices' = 
				    (if !trace then (prs"branch closed";
						     traceVars ntrl)
				               else ();
				     prune (nbrs, nxtVars, 
					    (ntrl, nbrs, PRV) :: choices))
			    in  prv (tac::tacs, brs0::trs, choices', brs)  
				handle PRV => 
				    (*reset Vars and try another literal
				      [this handler is pruned if possible!]*)
				 (clearTo ntrl;  closeF Ls)
			    end
	      fun closeFl [] = raise CLOSEF
		| closeFl ((br, haz)::pairs) =
		    closeF (map fst br)
		      handle CLOSEF => closeF (map fst haz)
			handle CLOSEF => closeFl pairs
	  in tracing sign brs0; 
	     if lim<0 then backtrack choices
	     else
	     prv ((TRY  o  Data.vars_gen_hyp_subst_tac false)  ::  tacs, 
		  (*The TRY above allows the substitution to fail, e.g. if
		    the real version is z = f(?x z).  Rest of proof might
		    still succeed!*)
		  brs0::trs,  choices,
		  equalSubst sign (G, (br,haz)::pairs, lits, vars, lim) :: brs)
	     handle DEST_EQ => closeF lits
	      handle CLOSEF => closeFl ((br,haz)::pairs)
	        handle CLOSEF => 
		 deeper rules
		  handle NEWBRANCHES => 
		   (case netMkRules G vars hazList of
		       [] => (*no plausible rules: move G to literals*)
			   prv (tacs, brs0::trs, choices,
				((br,haz)::pairs, addLit(G,lits), vars, lim)
				::brs)
		    | _ => (*G admits some haz rules: try later*)
			   prv (if isGoal G then negOfGoal_tac :: tacs
				else tacs, 
				brs0::trs,  choices,
				((br, haz@[(negOfGoal G, md)])::pairs,
				 lits, vars, lim)  ::  brs))
	  end
       | prv (tacs, trs, choices, 
	      (([],haz)::(Gs,haz')::pairs, lits, vars, lim) :: brs) =
	     (*no more "safe" formulae: transfer haz down a level*)
	   prv (tacs, trs, choices, 
		((Gs,haz@haz')::pairs, lits, vars, lim) :: brs)
       | prv (tacs, trs, choices, 
	      brs0 as ([([], (H,md)::Hs)], lits, vars, lim) :: brs) =
   	     (*no safe steps possible at any level: apply a haz rule*)
	  let exception PRV (*backtrack to precisely this recursion!*)
	      val H = norm H
	      val ntrl = !ntrail
	      val rules = netMkRules H vars hazList
	      (*new premises of haz rules may NOT be duplicated*)
	      fun newPrem (vars,recur,dup,lim') prem = 
		  let val Gs' = map (fn P => (P,false)) prem
		      and Hs' = if dup then Hs @ [(negOfGoal H, md)] else Hs
                  in  (if recur then [(Gs',Hs')] else [(Gs',[]), ([],Hs')], 
		       lits, vars, lim')
		  end
	      fun newBr x prems = map (newPrem x) prems  @  brs
	      (*Seek a matching rule.  If unifiable then add new premises
                to branch.*)
	      fun deeper [] = raise NEWBRANCHES
		| deeper (((P,prems),tac)::grls) =
		    if unify(false, add_term_vars(P,[]), P, H)
		    then
		     let val ntrl' = !ntrail
			 val vars  = vars_in_vars vars
			 val vars' = foldr add_terms_vars (prems, vars)
			    (*duplicate H if md and the subgoal has new vars*)
			 val dup = md andalso vars' <> vars
			     (*any instances of P in the subgoals?*)
			 and recur = exists (exists (match P)) prems
			 val lim' = (*Decrement "lim" extra if updates occur*)
			     if ntrl < !ntrail then lim - (1+log(length rules))
			     else lim-1 
				 (*It is tempting to leave "lim" UNCHANGED if
				   both dup and recur are false.  Proofs are
				   found at shallower depths, but looping
				   occurs too often...*)
			 val mayUndo = not(null grls)   (*other rules to try?*)
				     orelse ntrl < ntrl' (*variables updated?*)
				     orelse vars=vars'   (*no new Vars?*)
			 val tac' = if mayUndo then tac dup
				    else DETERM o (tac dup) 
		     in
		       if lim'<0 andalso not (null prems)
		       then (*it's faster to kill ALL the alternatives*)
			   raise NEWBRANCHES
		       else 
			 traceNew prems;  traceVars ntrl;
			 prv(tac dup :: tacs, 
			       (*FIXME: if recur then the tactic should not
				 call rotate_tac: new formulae should be last*)
			     brs0::trs, 
			     (ntrl, length brs0, PRV) :: choices, 
			     newBr (vars', recur, dup, lim') prems)
			  handle PRV => 
			      if mayUndo
			      then (*reset Vars and try another rule*)
				   (clearTo ntrl;  deeper grls)
			      else (*backtrack to previous level*)
				   backtrack choices
		     end
		    else deeper grls
	  in tracing sign brs0; 
	     if lim<1 then backtrack choices
	     else deeper rules
	     handle NEWBRANCHES => 
		 (*cannot close branch: move H to literals*)
		 prv (tacs,  brs0::trs,  choices,
		      ([([], Hs)], H::lits, vars, lim)::brs)
	  end
       | prv (tacs, trs, choices, _ :: brs) = backtrack choices
 in prv ([], [], [(!ntrail, length brs, PROVE)], brs) end;


(*Construct an initial branch.*)
fun initBranch (ts,lim) = 
    ([(map (fn t => (t,true)) ts, [])],
     [], add_terms_vars (ts,[]), lim);


(*** Conversion & Skolemization of the Isabelle proof state ***)

(*Make a list of all the parameters in a subgoal, even if nested*)
local open Term 
in
fun discard_foralls (Const("all",_)$Abs(a,T,t)) = discard_foralls t
  | discard_foralls t = t;
end;


(*List of variables not appearing as arguments to the given parameter*)
fun getVars []                  i = []
  | getVars ((_,(v,is))::alist) i =
	if i mem is then getVars alist i
	else v :: getVars alist i;


(*Conversion of a subgoal: Skolemize all parameters*)
fun fromSubgoal tsig t =
  let val alist = ref []
      fun hdvar ((ix,(v,is))::_) = v
      fun from lev t =
	let val (ht,ts) = Term.strip_comb t
	    fun apply u = list_comb (u, map (from lev) ts)
	    fun bounds [] = []
	      | bounds (Term.Bound i::ts) = 
		  if i<lev then error"Function Var's argument not a parameter"
		  else i-lev :: bounds ts
	      | bounds ts = error"Function Var's argument not a bound variable"
        in
	  case ht of 
	      t as Term.Const _ => apply (fromConst tsig t)	    
	    | Term.Free  (a,_) => apply (Free a)
	    | Term.Bound i     => apply (Bound i)
	    | Term.Var (ix,_) => 
		  (case (assoc_string_int(!alist,ix)) of
		       None => (alist := (ix, (ref None, bounds ts))
					  :: !alist;
				Var (hdvar(!alist)))
		     | Some(v,is) => if is=bounds ts then Var v
			    else error("Discrepancy among occurrences of ?"
				       ^ Syntax.string_of_vname ix))
	    | Term.Abs (a,_,body) => 
		  if null ts then Abs(a, from (lev+1) body)
		  else error "fromSubgoal: argument not in normal form"
        end

      val npars = length (Logic.strip_params t)

      (*Skolemize a subgoal from a proof state*)
      fun skoSubgoal i t =
	  if i<npars then 
	      skoSubgoal (i+1)
		(subst_bound (Skolem (gensym "T_", getVars (!alist) i), 
			      t))
	  else t

  in  skoSubgoal 0 (from 0 (discard_foralls t))  end;


(*Tactic using tableau engine and proof reconstruction.  
 "lim" is depth limit.*)
fun depth_tac cs lim i st = 
    (fullTrace:=[];  trail := [];  ntrail := 0;
     let val {sign,...} = rep_thm st
	 val {tsig,...} = Sign.rep_sg sign
	 val skoprem = fromSubgoal tsig (List.nth(prems_of st, i-1))
         val hyps  = strip_imp_prems skoprem
         and concl = strip_imp_concl skoprem
         fun cont (tacs,_,choices) = 
	     (case Sequence.pull(EVERY' (rev tacs) i st) of
		  None => (writeln ("PROOF FAILED for depth " ^
				    Int.toString lim);
			   backtrack choices)
		| cell => Sequence.seqof(fn()=> cell))
     in prove (sign, cs, [initBranch (mkGoal concl :: hyps, lim)], cont)
     end
     handle Subscript => Sequence.null
	  | PROVE     => Sequence.null);

fun blast_tac cs = (DEEPEN (1,20) (depth_tac cs) 0);

fun Blast_tac i = blast_tac (!Data.claset) i;


(*** For debugging: these apply the prover to a subgoal and return 
     the resulting tactics, trace, etc.                            ***)

(*Translate subgoal i from a proof state*)
fun trygl cs lim i = 
    (fullTrace:=[];  trail := [];  ntrail := 0;
     let val st = topthm()
         val {sign,...} = rep_thm st
	 val {tsig,...} = Sign.rep_sg sign
	 val skoprem = fromSubgoal tsig (List.nth(prems_of st, i-1))
         val hyps  = strip_imp_prems skoprem
         and concl = strip_imp_concl skoprem
     in timeap prove
	 (sign, cs, [initBranch (mkGoal concl :: hyps, lim)], I)
     end
     handle Subscript => error("There is no subgoal " ^ Int.toString i));

fun Trygl lim i = trygl (!Data.claset) lim i;

(*Read a string to make an initial, singleton branch*)
fun readGoal sign s = read_cterm sign (s,propT) |>
                      term_of |> fromTerm (#tsig(Sign.rep_sg sign)) |> 
		      rand |> mkGoal;

fun tryInThy thy lim s = 
    (fullTrace:=[];  trail := [];  ntrail := 0;
     timeap prove (sign_of thy, 
		   !Data.claset, 
		   [initBranch ([readGoal (sign_of thy) s], lim)], 
		   I));


end;

