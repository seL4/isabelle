(*  Title: 	Provers/blast.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Generic tableau prover with proof reconstruction

  SKOLEMIZES ReplaceI WRONGLY: allow new vars in prems, or forbid such rules??
  Needs explicit instantiation of assumptions?


Blast_tac is often more powerful than fast_tac, but has some limitations.
Blast_tac...
  * ignores wrappers (addss, addbefore, addafter, addWrapper, ...); 
    this restriction is intrinsic
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
	such as transitivity are treated specially to prevent this.  Sometimes
	the formulae get into the wrong order (see WRONG below).

  With overloading:
        Calls to Blast.overloaded (see HOL/Set.ML for examples) are needed
	to tell Blast_tac when to retain some type information.  Make sure
	you know the constant's internal name, which might be "op <=" or 
	"Relation.op ^^".

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
  val hyp_subst_tac     : bool ref -> int -> tactic
  val claset		: unit -> claset
  val rep_cs	: (* dependent on classical.ML *)
      claset -> {safeIs: thm list, safeEs: thm list, 
		 hazIs: thm list, hazEs: thm list,
		 swrappers: (string * wrapper) list, 
		 uwrappers: (string * wrapper) list,
		 safe0_netpair: netpair, safep_netpair: netpair,
		 haz_netpair: netpair, dup_netpair: netpair, xtra_netpair: netpair}
  val cla_modifiers: (Args.T list -> (Method.modifier * Args.T list)) list
  val cla_meth': (claset -> int -> tactic) -> thm list -> Proof.context -> Proof.method
  end;


signature BLAST =
  sig
  type claset 
  exception TRANS of string    (*reports translation errors*)
  datatype term = 
      Const of string
    | TConst of string * term
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
  val overloaded 	: string * (Term.typ -> Term.typ) -> unit
  val get_overloads	: unit -> (string * (Term.typ -> Term.typ)) list
  val setup		: (theory -> theory) list
  (*debugging tools*)
  val stats	        : bool ref
  val trace	        : bool ref
  val fullTrace	        : branch list list ref
  val fromType	        : (indexname * term) list ref -> Term.typ -> term
  val fromTerm	        : Term.term -> term
  val fromSubgoal       : Term.term -> term
  val instVars          : term -> (unit -> unit)
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

val trace = ref false
and stats = ref false;   (*for runtime and search statistics*)

datatype term = 
    Const  of string
  | TConst of string * term    (*type of overloaded constant--as a term!*)
  | Skolem of string * term option ref list
  | Free   of string
  | Var    of term option ref
  | Bound  of int
  | Abs    of string*term
  | op $   of term*term;


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


(*** Dealing with overloaded constants ***)

(*alist is a map from TVar names to Vars.  We need to unify the TVars
  faithfully in order to track overloading*)
fun fromType alist (Term.Type(a,Ts)) = list_comb (Const a, 
						  map (fromType alist) Ts)
  | fromType alist (Term.TFree(a,_)) = Free a
  | fromType alist (Term.TVar (ixn,_)) =
	      (case (assoc_string_int(!alist,ixn)) of
		   None => let val t' = Var(ref None)
		           in  alist := (ixn, t') :: !alist;  t'
			   end
		 | Some v => v)

local
val overloads = ref ([]: (string * (Term.typ -> Term.typ)) list)
in

fun overloaded arg = (overloads := arg :: (!overloads));

fun get_overloads() = !overloads;

(*Convert a possibly overloaded Term.Const to a Blast.Const or Blast.TConst,
  converting its type to a Blast.term in the latter case.*)
fun fromConst alist (a,T) =
  case assoc_string (!overloads, a) of
      None   => Const a		(*not overloaded*)
    | Some f => 
	let val T' = f T
		     handle Match => error
                ("Blast_tac: unexpected type for overloaded constant " ^ a)
        in  TConst(a, fromType alist T')  end;

end;


(*Tests whether 2 terms are alpha-convertible; chases instantiations*)
fun (Const a)      aconv (Const b)      = a=b
  | (TConst (a,ta)) aconv (TConst (b,tb)) = a=b andalso ta aconv tb
  | (Skolem (a,_)) aconv (Skolem (b,_)) = a=b  (*arglists must then be equal*)
  | (Free a)       aconv (Free b)       = a=b
  | (Var(ref(Some t))) aconv u          = t aconv u
  | t          aconv (Var(ref(Some u))) = t aconv u
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
  | add_term_vars (TConst (_,t),	vars) = add_term_vars(t,vars)
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
  | TConst(a,aT)         => TConst(a, norm aT)
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
  | TConst _       => t
  | Skolem(a,args) => t
  | Free _         => t
  | _              => wkNormAux t;


(*Does variable v occur in u?  For unification.  
  Dangling bound vars are also forbidden.*)
fun varOccur v = 
  let fun occL lev [] = false	(*same as (exists occ), but faster*)
	| occL lev (u::us) = occ lev u orelse occL lev us
      and occ lev (Var w) = 
	      v=w orelse
              (case !w of None   => false
	                | Some u => occ lev u)
        | occ lev (Skolem(_,args)) = occL lev (map Var args)
            (*ignore TConst, since term variables can't occur in types (?) *)
        | occ lev (Bound i)  = lev <= i
        | occ lev (Abs(_,u)) = occ (lev+1) u
        | occ lev (f$u)      = occ lev u  orelse  occ lev f
        | occ lev _          = false;
  in  occ 0  end;

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
fun unify(vars,t,u) =
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
	      | (TConst(a,at), TConst(b,bt)) => if a=b then unifyAux(at,bt)
		                                else raise UNIFY
	      | (Abs(_,t'),  Abs(_,u')) => unifyAux(t',u')
		    (*NB: can yield unifiers having dangling Bound vars!*)
	      | (f$t',  g$u') => (unifyAux(f,g); unifyAux(t',u'))
	      | (nt,  nu)    => if nt aconv nu then () else raise UNIFY
    in  (unifyAux(t,u); true) handle UNIFY => (clearTo n; false)
    end;


(*Convert from "real" terms to prototerms; eta-contract
  Code is duplicated with fromSubgoal.  Correct this?*)
fun fromTerm t =
  let val alistVar = ref []
      and alistTVar = ref []
      fun from (Term.Const aT) = fromConst alistTVar aT
	| from (Term.Free  (a,_)) = Free a
	| from (Term.Bound i)     = Bound i
	| from (Term.Var (ixn,T)) = 
	      (case (assoc_string_int(!alistVar,ixn)) of
		   None => let val t' = Var(ref None)
		           in  alistVar := (ixn, t') :: !alistVar;  t'
			   end
		 | Some v => v)
	| from (Term.Abs (a,_,u)) = 
	      (case  from u  of
		u' as (f $ Bound 0) => 
		  if (0 mem_int loose_bnos f) then Abs(a,u')
		  else incr_boundvars ~1 f 
	      | u' => Abs(a,u'))
	| from (Term.$ (f,u)) = from f $ from u
  in  from t  end;

(*A debugging function: replaces all Vars by dummy Frees for visual inspection
  of whether they are distinct.  Function revert undoes the assignments.*)
fun instVars t =
  let val name = ref "A"
      val updated = ref []
      fun inst (TConst(a,t)) = inst t
	| inst (Var(v as ref None)) = (updated := v :: (!updated);
				       v       := Some (Free ("?" ^ !name)); 
				       name    := bump_string (!name))
	| inst (Abs(a,t))    = inst t
	| inst (f $ u)       = (inst f; inst u)
	| inst _             = ()
      fun revert() = seq (fn v => v:=None) (!updated)
  in  inst t; revert  end;


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

exception ElimBadConcl and ElimBadPrem;

(*The conclusion becomes the goal/negated assumption *False*: delete it!
  If we don't find it then the premise is ill-formed and could cause 
  PROOF FAILED*)
fun delete_concl [] = raise ElimBadPrem
  | delete_concl (Const "*Goal*" $ (Var (ref (Some (Const"*False*")))) :: Ps) =
	Ps
  | delete_concl (Const "Not" $ (Var (ref (Some (Const"*False*")))) :: Ps) =
	Ps
  | delete_concl (P::Ps) = P :: delete_concl Ps;

fun skoPrem vars (Const "all" $ Abs (_, P)) =
        skoPrem vars (subst_bound (Skolem (gensym "S_", vars), P))
  | skoPrem vars P = P;

fun convertPrem t = 
    delete_concl (mkGoal (strip_imp_concl t) :: strip_imp_prems t);

(*Expects elimination rules to have a formula variable as conclusion*)
fun convertRule vars t =
  let val (P::Ps) = strip_imp_prems t
      val Var v   = strip_imp_concl t
  in  v := Some (Const"*False*");
      (P, map (convertPrem o skoPrem vars) Ps) 
  end
  handle Bind => raise ElimBadConcl;


(*Like dup_elim, but puts the duplicated major premise FIRST*)
fun rev_dup_elim th = th RSN (2, revcut_rl) |> assumption 2 |> Seq.hd;


(*Rotate the assumptions in all new subgoals for the LIFO discipline*)
local
  (*Count new hyps so that they can be rotated*)
  fun nNewHyps []                         = 0
    | nNewHyps (Const "*Goal*" $ _ :: Ps) = nNewHyps Ps
    | nNewHyps (P::Ps)                    = 1 + nNewHyps Ps;

  fun rot_tac [] i st      = Seq.single st
    | rot_tac (0::ks) i st = rot_tac ks (i+1) st
    | rot_tac (k::ks) i st = rot_tac ks (i+1) (rotate_rule (~k) i st);
in
fun rot_subgoals_tac (rot, rl) =
     rot_tac (if rot then map nNewHyps rl else []) 
end;


fun TRACE rl tac st i = if !trace then (prth rl; tac st i) else tac st i;

(*Resolution/matching tactics: if upd then the proof state may be updated.
  Matching makes the tactics more deterministic in the presence of Vars.*)
fun emtac upd rl = TRACE rl (if upd then etac rl else ematch_tac [rl]);
fun rmtac upd rl = TRACE rl (if upd then rtac rl else match_tac [rl]);

(*Tableau rule from elimination rule.  
  Flag "upd" says that the inference updated the branch.
  Flag "dup" requests duplication of the affected formula.*)
fun fromRule vars rl = 
  let val trl = rl |> rep_thm |> #prop |> fromTerm |> convertRule vars
      fun tac (upd, dup,rot) i = 
	emtac upd (if dup then rev_dup_elim rl else rl) i
	THEN
	rot_subgoals_tac (rot, #2 trl) i
  in Option.SOME (trl, tac) end
  handle ElimBadPrem => (*reject: prems don't preserve conclusion*)
	    (warning("Ignoring weak elimination rule\n" ^ string_of_thm rl);
	     Option.NONE)
       | ElimBadConcl => (*ignore: conclusion is not just a variable*)
	   (if !trace then (warning("Ignoring ill-formed elimination rule:\n" ^
       	               "conclusion should be a variable\n" ^ string_of_thm rl))
	    else ();
	    Option.NONE);


(*** Conversion of Introduction Rules ***)

fun convertIntrPrem t = mkGoal (strip_imp_concl t) :: strip_imp_prems t;

fun convertIntrRule vars t =
  let val Ps = strip_imp_prems t
      val P  = strip_imp_concl t
  in  (mkGoal P, map (convertIntrPrem o skoPrem vars) Ps) 
  end;

(*Tableau rule from introduction rule.  
  Flag "upd" says that the inference updated the branch.
  Flag "dup" requests duplication of the affected formula.
  Since haz rules are now delayed, "dup" is always FALSE for
  introduction rules.*)
fun fromIntrRule vars rl = 
  let val trl = rl |> rep_thm |> #prop |> fromTerm |> convertIntrRule vars
      fun tac (upd,dup,rot) i = 
	 rmtac upd (if dup then Data.dup_intr rl else rl) i
	 THEN
	 rot_subgoals_tac (rot, #2 trl) i
  in (trl, tac) end;


val dummyVar = Term.Var (("etc",0), dummyT);

(*Convert from prototerms to ordinary terms with dummy types
  Ignore abstractions; identify all Vars; STOP at given depth*)
fun toTerm 0 _             = dummyVar
  | toTerm d (Const a)     = Term.Const (a,dummyT)
  | toTerm d (TConst(a,_)) = Term.Const (a,dummyT)  (*no need to convert type*)
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
	in  map (fromIntrRule vars o #2) (Tactic.orderlist intrs)  end
    | _ =>
	let val pP = mk_tprop (toTerm 3 P)
	    val elims = List.concat 
		             (map (fn (_,enet) => Net.unify_term enet pP) 
			      nps)
	in  List.mapPartial (fromRule vars o #2) (Tactic.orderlist elims)  end;


(*Pending formulae carry md (may duplicate) flags*)
type branch = 
    {pairs: ((term*bool) list *	(*safe formulae on this level*)
               (term*bool) list) list,  (*haz formulae  on this level*)
     lits:   term list,                 (*literals: irreducible formulae*)
     vars:   term option ref list,      (*variables occurring in branch*)
     lim:    int};                      (*resource limit*)

val fullTrace = ref[] : branch list list ref;

(*Normalize a branch--for tracing*)
fun norm2 (G,md) = (norm G, md);

fun normLev (Gs,Hs) = (map norm2 Gs, map norm2 Hs);

fun normBr {pairs, lits, vars, lim} =
     {pairs = map normLev pairs, 
      lits  = map norm lits, 
      vars  = vars, 
      lim   = lim};


val dummyTVar = Term.TVar(("a",0), []);
val dummyVar2 = Term.Var(("var",0), dummyT);

(*convert Blast_tac's type representation to real types for tracing*)
fun showType (Free a)  = Term.TFree (a,[])
  | showType (Var _)   = dummyTVar
  | showType t         =
      (case strip_comb t of
	   (Const a, us) => Term.Type(a, map showType us)
	 | _ => dummyT);

(*Display top-level overloading if any*)
fun topType (TConst(a,t)) = Some (showType t)
  | topType (Abs(a,t))    = topType t
  | topType (f $ u)       = (case topType f of
				 None => topType u
			       | some => some)
  | topType _             = None;


(*Convert from prototerms to ordinary terms with dummy types for tracing*)
fun showTerm d (Const a)     = Term.Const (a,dummyT)
  | showTerm d (TConst(a,_)) = Term.Const (a,dummyT)
  | showTerm d (Skolem(a,_)) = Term.Const (a,dummyT)
  | showTerm d (Free a)      = Term.Free  (a,dummyT)
  | showTerm d (Bound i)     = Term.Bound i
  | showTerm d (Var(ref(Some u))) = showTerm d u
  | showTerm d (Var(ref None))    = dummyVar2
  | showTerm d (Abs(a,t))    = if d=0 then dummyVar
			       else Term.Abs(a, dummyT, showTerm (d-1) t)
  | showTerm d (f $ u)       = if d=0 then dummyVar
			       else Term.$ (showTerm d f, showTerm (d-1) u);

fun string_of sign d t = Sign.string_of_term sign (showTerm d t);

fun traceTerm sign t = 
  let val t' = norm t
      val stm = string_of sign 8 t'
  in  
      case topType t' of
	  None   => stm   (*no type to attach*)
	| Some T => stm ^ "\t:: " ^ Sign.string_of_typ sign T
  end;


val prs = std_output;

(*Print tracing information at each iteration of prover*)
fun tracing sign brs = 
  let fun printPairs (((G,_)::_,_)::_)  = prs(traceTerm sign G)
	| printPairs (([],(H,_)::_)::_) = prs(traceTerm sign H ^ "\t (Unsafe)")
	| printPairs _                 = ()
      fun printBrs (brs0 as {pairs, lits, lim, ...} :: brs) =
	    (fullTrace := brs0 :: !fullTrace;
	     seq (fn _ => prs "+") brs;
	     prs (" [" ^ Int.toString lim ^ "] ");
	     printPairs pairs;
	     writeln"")
  in if !trace then printBrs (map normBr brs) else ()
  end;

fun traceMsg s = if !trace then writeln s else ();

(*Tracing: variables updated in the last branch operation?*)
fun traceVars sign ntrl =
  if !trace then 
      (case !ntrail-ntrl of
	    0 => ()
	  | 1 => prs"\t1 variable UPDATED:"
	  | n => prs("\t" ^ Int.toString n ^ " variables UPDATED:");
       (*display the instantiations themselves, though no variable names*)
       seq (fn v => prs("   " ^ string_of sign 4 (the (!v))))
           (List.take(!trail, !ntrail-ntrl));
       writeln"")
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

(*Can t occur in u?  For substitution.  
  Does NOT examine the args of Skolem terms: substitution does not affect them.
  REFLEXIVE because hyp_subst_tac fails on x=x.*)
fun substOccur t = 
  let (*NO vars are permitted in u except the arguments of t, if it is 
        a Skolem term.  This ensures that no equations are deleted that could
        be instantiated to a cycle.  For example, x=?a is rejected because ?a
	could be instantiated to Suc(x).*)
      val vars = case t of
                     Skolem(_,vars) => vars
		   | _ => []
      fun occEq u = (t aconv u) orelse occ u
      and occ (Var(ref(Some u))) = occEq u
        | occ (Var v)            = not (mem_var (v, vars))
	| occ (Abs(_,u))         = occEq u
        | occ (f$u)              = occEq u  orelse  occEq f
        | occ (_)                = false;
  in  occEq  end;

exception DEST_EQ;

(*Take apart an equality (plain or overloaded).  NO constant Trueprop*)
fun dest_eq (Const  "op ="     $ t $ u) = 
		(eta_contract_atom t, eta_contract_atom u)
  | dest_eq (TConst("op =",_)  $ t $ u) = 
		(eta_contract_atom t, eta_contract_atom u)
  | dest_eq _                           = raise DEST_EQ;

(*Reject the equality if u occurs in (or equals!) t*)
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
  they should go: this could make proofs fail.*)
fun equalSubst sign (G, {pairs, lits, vars, lim}) = 
  let val (t,u) = orientGoal(dest_eq G)
      val subst = subst_atomic (t,u)
      fun subst2(G,md) = (subst G, md)
      (*substitute throughout list; extract affected formulae*)
      fun subForm ((G,md), (changed, pairs)) =
	    let val nG = subst G
	    in  if nG aconv G then (changed, (G,md)::pairs)
		              else ((nG,md)::changed, pairs)
            end
      (*substitute throughout "stack frame"; extract affected formulae*)
      fun subFrame ((Gs,Hs), (changed, frames)) =
	    let val (changed', Gs') = foldr subForm (Gs, (changed, []))
                val (changed'', Hs') = foldr subForm (Hs, (changed', []))
            in  (changed'', (Gs',Hs')::frames)  end
      (*substitute throughout literals; extract affected ones*)
      fun subLit (lit, (changed, nlits)) =
	    let val nlit = subst lit
	    in  if nlit aconv lit then (changed, nlit::nlits)
		                  else ((nlit,true)::changed, nlits)
            end
      val (changed, lits') = foldr subLit (lits, ([], []))
      val (changed', pairs') = foldr subFrame (pairs, (changed, []))
  in  if !trace then writeln ("Substituting " ^ traceTerm sign u ^
			      " for " ^ traceTerm sign t ^ " in branch" )
      else ();
      {pairs = (changed',[])::pairs',	(*affected formulas, and others*)
       lits  = lits',			(*unaffected literals*)
       vars  = vars, 
       lim   = lim}
  end;


exception NEWBRANCHES and CLOSEF;

exception PROVE;

(*Trying eq_contr_tac first INCREASES the effort, slowing reconstruction*)
val contr_tac = ematch_tac [Data.notE] THEN' 
                (eq_assume_tac ORELSE' assume_tac);

val eContr_tac  = TRACE Data.notE contr_tac;
val eAssume_tac = TRACE asm_rl   (eq_assume_tac ORELSE' assume_tac);

(*Try to unify complementary literals and return the corresponding tactic. *) 
fun tryClose (Const"*Goal*" $ G,  L) = 
	if unify([],G,L) then Some eAssume_tac else None
  | tryClose (G,  Const"*Goal*" $ L) = 
	if unify([],G,L) then Some eAssume_tac else None
  | tryClose (Const"Not" $ G,  L)    = 
	if unify([],G,L) then Some eContr_tac else None
  | tryClose (G,  Const"Not" $ L)    = 
	if unify([],G,L) then Some eContr_tac else None
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
fun negOfGoal_tac i = TRACE Data.ccontr (rtac Data.ccontr) i THEN
                      rotate_tac ~1 i;


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

fun nextVars ({pairs, lits, vars, lim} :: _) = map Var vars
  | nextVars []                              = [];

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
  | match (Const"*Goal*") (Const"Not")    = true
  | match (Const"Not")    (Const"*Goal*") = true
  | match (Const a)       (Const b)       = (a=b)
  | match (TConst (a,ta)) (TConst (b,tb)) = a=b andalso match ta tb
  | match (Free a)        (Free b)        = (a=b)
  | match (Bound i)       (Bound j)       = (i=j)
  | match (Abs(_,t))      (Abs(_,u))      = match t u
  | match (f$t)           (g$u)           = match f g andalso match t u
  | match t               u   = false;


(*Branches closed: number of branches closed during the search
  Branches tried:  number of branches created by splitting (counting from 1)*)
val nclosed = ref 0
and ntried  = ref 1;

fun printStats (b, start, tacs) =
  if b then
    writeln (endTiming start ^ " for search.  Closed: " 
	     ^ Int.toString (!nclosed) ^
             " tried: " ^ Int.toString (!ntried) ^
             " tactics: " ^ Int.toString (length tacs))
  else ();


(*Tableau prover based on leanTaP.  Argument is a list of branches.  Each 
  branch contains a list of unexpanded formulae, a list of literals, and a 
  bound on unsafe expansions.
 "start" is CPU time at start, for printing search time
*)
fun prove (sign, start, cs, brs, cont) =
 let val {safe0_netpair, safep_netpair, haz_netpair, ...} = Data.rep_cs cs
     val safeList = [safe0_netpair, safep_netpair]
     and hazList  = [haz_netpair]
     fun prv (tacs, trs, choices, []) = 
	        (printStats (!trace orelse !stats, start, tacs); 
		 cont (tacs, trs, choices))   (*all branches closed!*)
       | prv (tacs, trs, choices, 
	      brs0 as {pairs = ((G,md)::br, haz)::pairs, 
		       lits, vars, lim} :: brs) =
   	     (*apply a safe rule only (possibly allowing instantiation);
               defer any haz formulae*)
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
		       then {pairs = ((joinMd md prem, []) :: 
				      negOfGoals ((br, haz)::pairs)),
			     lits  = map negOfGoal lits, 
			     vars  = vars', 
			     lim   = lim'}
		       else {pairs = ((joinMd md prem, []) :: 
				      (br, haz) :: pairs),
			     lits = lits, 
			     vars = vars', 
			     lim  = lim'})
		  prems @
		  brs		  
	      (*Seek a matching rule.  If unifiable then add new premises
                to branch.*)
	      fun deeper [] = raise NEWBRANCHES
		| deeper (((P,prems),tac)::grls) =
		    if unify(add_term_vars(P,[]), P, G) 
		    then  (*P comes from the rule; G comes from the branch.*)
		     let val updated = ntrl < !ntrail (*branch updated*)
			 val lim' = if updated
				    then lim - (1+log(length rules))
				    else lim   (*discourage branching updates*)
			 val vars  = vars_in_vars vars
			 val vars' = foldr add_terms_vars (prems, vars)
			 val choices' = (ntrl, nbrs, PRV) :: choices
			 val tacs' = (tac(updated,false,true)) 
                                     :: tacs  (*no duplication; rotate*)
		     in
			 traceNew prems;  traceVars sign ntrl;
			 (if null prems then (*closed the branch: prune!*)
			    (nclosed := !nclosed + 1;
			     prv(tacs',  brs0::trs, 
				 prune (nbrs, nxtVars, choices'),
				 brs))
			  else (*prems non-null*)
			  if lim'<0 (*faster to kill ALL the alternatives*)
			  then (traceMsg"Excessive branching: KILLED";
			        clearTo ntrl;  raise NEWBRANCHES)
			  else
			    (ntried := !ntried + length prems - 1;
			     prv(tacs',  brs0::trs, choices',
				 newBr (vars',lim') prems)))
                         handle PRV => 
			   if updated then
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
						     traceVars sign ntrl)
				               else ();
				     prune (nbrs, nxtVars, 
					    (ntrl, nbrs, PRV) :: choices))
			    in  nclosed := !nclosed + 1;
				prv (tac::tacs, brs0::trs, choices', brs)  
				handle PRV => 
				    (*reset Vars and try another literal
				      [this handler is pruned if possible!]*)
				 (clearTo ntrl;  closeF Ls)
			    end
	      (*Try to unify a queued formula (safe or haz) with head goal*)
	      fun closeFl [] = raise CLOSEF
		| closeFl ((br, haz)::pairs) =
		    closeF (map fst br)
		      handle CLOSEF => closeF (map fst haz)
			handle CLOSEF => closeFl pairs
	  in tracing sign brs0; 
	     if lim<0 then (traceMsg "Limit reached.  "; backtrack choices)
	     else
	     prv (Data.hyp_subst_tac trace :: tacs, 
		  brs0::trs,  choices,
		  equalSubst sign
		    (G, {pairs = (br,haz)::pairs, 
			 lits  = lits, vars  = vars, lim   = lim}) 
		    :: brs)
	     handle DEST_EQ =>   closeF lits
	      handle CLOSEF =>   closeFl ((br,haz)::pairs)
	        handle CLOSEF => deeper rules
		  handle NEWBRANCHES => 
		   (case netMkRules G vars hazList of
		       [] => (*there are no plausible haz rules*)
			     (traceMsg "moving formula to literals";
			      prv (tacs, brs0::trs, choices,
				   {pairs = (br,haz)::pairs, 
				    lits  = addLit(G,lits), 
				    vars  = vars, 
				    lim   = lim}  :: brs))
		    | _ => (*G admits some haz rules: try later*)
			   (traceMsg "moving formula to haz list";
			    prv (if isGoal G then negOfGoal_tac :: tacs
				             else tacs, 
				 brs0::trs,  
				 choices,
				 {pairs = (br, haz@[(negOfGoal G, md)])::pairs,
				  lits  = lits,
				  vars  = vars, 
				  lim   = lim}  :: brs)))
	  end
       | prv (tacs, trs, choices, 
	      {pairs = ([],haz)::(Gs,haz')::pairs, lits, vars, lim} :: brs) =
	     (*no more "safe" formulae: transfer haz down a level*)
	   prv (tacs, trs, choices, 
		{pairs = (Gs,haz@haz')::pairs, 
		 lits  = lits, 
		 vars  = vars, 
		 lim    = lim} :: brs)
       | prv (tacs, trs, choices, 
	      brs0 as {pairs = [([], (H,md)::Hs)],
		       lits, vars, lim} :: brs) =
   	     (*no safe steps possible at any level: apply a haz rule*)
	  let exception PRV (*backtrack to precisely this recursion!*)
	      val H = norm H
	      val ntrl = !ntrail
	      val rules = netMkRules H vars hazList
	      (*new premises of haz rules may NOT be duplicated*)
	      fun newPrem (vars,P,dup,lim') prem = 
		  let val Gs' = map (fn Q => (Q,false)) prem
		      and Hs' = if dup then Hs @ [(negOfGoal H, md)] else Hs
		      and lits' = if (exists isGoal prem) 
			          then map negOfGoal lits
				  else lits
                  in  {pairs = if exists (match P) prem then [(Gs',Hs')] 
			       (*Recursive in this premise.  Don't make new
				 "stack frame".  New haz premises will end up
				 at the BACK of the queue, preventing
				 exclusion of others*)
			    else [(Gs',[]), ([],Hs')], 
		       lits = lits', 
		       vars = vars, 
		       lim  = lim'}
		  end
	      fun newBr x prems = map (newPrem x) prems  @  brs
	      (*Seek a matching rule.  If unifiable then add new premises
                to branch.*)
	      fun deeper [] = raise NEWBRANCHES
		| deeper (((P,prems),tac)::grls) =
		    if unify(add_term_vars(P,[]), P, H)
		    then
		     let val updated = ntrl < !ntrail (*branch updated*)
			 val vars  = vars_in_vars vars
			 val vars' = foldr add_terms_vars (prems, vars)
			    (*duplicate H if md permits*)
			 val dup = md (*earlier had "andalso vars' <> vars":
                                  duplicate only if the subgoal has new vars*)
			     (*any instances of P in the subgoals?
			       NB: boolean "recur" affects tracing only!*)
			 and recur = exists (exists (match P)) prems
			 val lim' = (*Decrement "lim" extra if updates occur*)
			     if updated then lim - (1+log(length rules))
			     else lim-1 
				 (*It is tempting to leave "lim" UNCHANGED if
				   both dup and recur are false.  Proofs are
				   found at shallower depths, but looping
				   occurs too often...*)
			 val mayUndo = 
			     (*Allowing backtracking from a rule application
			       if other matching rules exist, if the rule
			       updated variables, or if the rule did not
			       introduce new variables.  This latter condition
			       means it is not a standard "gamma-rule" but
			       some other form of unsafe rule.  Aim is to
			       emulate Fast_tac, which allows all unsafe steps
			       to be undone.*)
			     not(null grls)   (*other rules to try?*)
			     orelse updated
			     orelse vars=vars'   (*no new Vars?*)
			 val tac' = tac(updated, dup, true)
		       (*if recur then perhaps shouldn't call rotate_tac: new
                         formulae should be last, but that's WRONG if the new
                         formulae are Goals, since they remain in the first
                         position*)

		     in
		       if lim'<0 andalso not (null prems)
		       then (*it's faster to kill ALL the alternatives*)
			   (traceMsg"Excessive branching: KILLED";
			    clearTo ntrl;  raise NEWBRANCHES)
		       else 
			 traceNew prems;  
			 if !trace andalso dup then prs" (duplicating)"
					         else ();
			 if !trace andalso recur then prs" (recursive)"
					         else ();
			 traceVars sign ntrl;
			 if null prems then nclosed := !nclosed + 1
			 else ntried := !ntried + length prems - 1;
			 prv(tac' :: tacs, 
			     brs0::trs, 
			     (ntrl, length brs0, PRV) :: choices, 
			     newBr (vars', P, dup, lim') prems)
			  handle PRV => 
			      if mayUndo
			      then (*reset Vars and try another rule*)
				   (clearTo ntrl;  deeper grls)
			      else (*backtrack to previous level*)
				   backtrack choices
		     end
		    else deeper grls
	  in tracing sign brs0; 
	     if lim<1 then (traceMsg "Limit reached.  "; backtrack choices)
	     else deeper rules
	     handle NEWBRANCHES => 
		 (*cannot close branch: move H to literals*)
		 prv (tacs,  brs0::trs,  choices,
		      {pairs = [([], Hs)], 
		       lits  = H::lits, 
		       vars  = vars, 
		       lim   = lim}  :: brs)
	  end
       | prv (tacs, trs, choices, _ :: brs) = backtrack choices
 in prv ([], [], [(!ntrail, length brs, PROVE)], brs) end;


(*Construct an initial branch.*)
fun initBranch (ts,lim) = 
    {pairs = [(map (fn t => (t,true)) ts, [])],
     lits  = [], 
     vars  = add_terms_vars (ts,[]), 
     lim   = lim};


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

exception TRANS of string;

(*Translation of a subgoal: Skolemize all parameters*)
fun fromSubgoal t =
  let val alistVar = ref []
      and alistTVar = ref []
      fun hdvar ((ix,(v,is))::_) = v
      fun from lev t =
	let val (ht,ts) = Term.strip_comb t
	    fun apply u = list_comb (u, map (from lev) ts)
	    fun bounds [] = []
	      | bounds (Term.Bound i::ts) = 
		  if i<lev then raise TRANS
		      "Function unknown's argument not a parameter"
		  else i-lev :: bounds ts
	      | bounds ts = raise TRANS
		      "Function unknown's argument not a bound variable"
        in
	  case ht of 
	      Term.Const aT    => apply (fromConst alistTVar aT)
	    | Term.Free  (a,_) => apply (Free a)
	    | Term.Bound i     => apply (Bound i)
	    | Term.Var (ix,_) => 
		  (case (assoc_string_int(!alistVar,ix)) of
		       None => (alistVar := (ix, (ref None, bounds ts))
					  :: !alistVar;
				Var (hdvar(!alistVar)))
		     | Some(v,is) => if is=bounds ts then Var v
			    else raise TRANS
				("Discrepancy among occurrences of "
				 ^ Syntax.string_of_vname ix))
	    | Term.Abs (a,_,body) => 
		  if null ts then Abs(a, from (lev+1) body)
		  else raise TRANS "argument not in normal form"
        end

      val npars = length (Logic.strip_params t)

      (*Skolemize a subgoal from a proof state*)
      fun skoSubgoal i t =
	  if i<npars then 
	      skoSubgoal (i+1)
		(subst_bound (Skolem (gensym "T_", getVars (!alistVar) i), 
			      t))
	  else t

  in  skoSubgoal 0 (from 0 (discard_foralls t))  end;


fun initialize() = 
    (fullTrace:=[];  trail := [];  ntrail := 0;
     nclosed := 0;  ntried := 1);


(*Tactic using tableau engine and proof reconstruction.  
 "start" is CPU time at start, for printing SEARCH time
	(also prints reconstruction time)
 "lim" is depth limit.*)
fun timing_depth_tac start cs lim i st0 = 
 (initialize();
  let val st = ObjectLogic.atomize_goal i st0;
      val {sign,...} = rep_thm st
      val skoprem = fromSubgoal (List.nth(prems_of st, i-1))
      val hyps  = strip_imp_prems skoprem
      and concl = strip_imp_concl skoprem
      fun cont (tacs,_,choices) = 
	  let val start = startTiming()
	  in
	  case Seq.pull(EVERY' (rev tacs) i st) of
	      None => (writeln ("PROOF FAILED for depth " ^
				Int.toString lim);
		       if !trace then writeln "************************\n"
		       else ();
		       backtrack choices)
	    | cell => (if (!trace orelse !stats)
		       then writeln (endTiming start ^ " for reconstruction")
		       else ();
		       Seq.make(fn()=> cell))
          end
  in prove (sign, start, cs, [initBranch (mkGoal concl :: hyps, lim)], cont) 
  end
  handle PROVE     => Seq.empty);

(*Public version with fixed depth*)
fun depth_tac cs lim i st = timing_depth_tac (startTiming()) cs lim i st;

fun blast_tac cs i st = 
    ((DEEPEN (1,20) (timing_depth_tac (startTiming()) cs) 0) i 
     THEN flexflex_tac) st
    handle TRANS s => (warning ("Blast_tac: " ^ s); Seq.empty);

fun Blast_tac i = blast_tac (Data.claset()) i;


(*** For debugging: these apply the prover to a subgoal and return 
     the resulting tactics, trace, etc.                            ***)

(*Translate subgoal i from a proof state*)
fun trygl cs lim i = 
    (initialize();
     let val st = topthm()
         val {sign,...} = rep_thm st
	 val skoprem = fromSubgoal (List.nth(prems_of st, i-1))
         val hyps  = strip_imp_prems skoprem
         and concl = strip_imp_concl skoprem
     in timeap prove (sign, startTiming(), cs, 
		      [initBranch (mkGoal concl :: hyps, lim)], I)
     end
     handle Subscript => error("There is no subgoal " ^ Int.toString i));

fun Trygl lim i = trygl (Data.claset()) lim i;

(*Read a string to make an initial, singleton branch*)
fun readGoal sign s = read_cterm sign (s,propT) |>
                      term_of |> fromTerm |> rand |> mkGoal;

fun tryInThy thy lim s = 
    (initialize();
     timeap prove (Theory.sign_of thy, 
		   startTiming(), 
		   Data.claset(), 
		   [initBranch ([readGoal (Theory.sign_of thy) s], lim)], 
		   I));


(** method setup **)

fun blast_args m =
  Method.bang_sectioned_args' 
      Data.cla_modifiers (Scan.lift (Scan.option Args.nat)) m;

fun blast_meth None = Data.cla_meth' blast_tac
  | blast_meth (Some lim) = Data.cla_meth' (fn cs => depth_tac cs lim);

val setup = [Method.add_methods [("blast", blast_args blast_meth, 
				  "tableau prover")]];


end;
