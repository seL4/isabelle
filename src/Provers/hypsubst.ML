(*  Title: 	Provers/hypsubst
    ID:         $Id$
    Author: 	Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Martin Coen's tactic for substitution in the hypotheses
*)

signature HYPSUBST_DATA =
  sig
  val dest_eq	: term -> term*term
  val imp_intr	: thm		(* (P ==> Q) ==> P-->Q *)
  val rev_mp	: thm		(* [| P;  P-->Q |] ==> Q *)
  val subst	: thm		(* [| a=b;  P(a) |] ==> P(b) *)
  val sym	: thm		(* a=b ==> b=a *)
  end;

signature HYPSUBST =
  sig
  val bound_hyp_subst_tac : int -> tactic
  val hyp_subst_tac       : int -> tactic
    (*exported purely for debugging purposes*)
  val eq_var              : bool -> term -> int * thm
  val inspect_pair        : bool -> term * term -> thm
  end;

functor HypsubstFun(Data: HYPSUBST_DATA): HYPSUBST = 
struct

local open Data in

fun REPEATN 0 tac = all_tac
  | REPEATN n tac = Tactic(fn state =>
                           tapply(tac THEN REPEATN (n-1) tac,  state));

exception EQ_VAR;

fun loose (i,t) = 0 mem add_loose_bnos(t,i,[]);

(*It's not safe to substitute for a constant; consider 0=1.
  It's not safe to substitute for x=t[x] since x is not eliminated.
  It's not safe to substitute for a Var; what if it appears in other goals?
  It's not safe to substitute for a variable free in the premises,
    but how could we check for this?*)
fun inspect_pair bnd (t,u) =
  case (Pattern.eta_contract t, Pattern.eta_contract u) of
       (Bound i, _) => if loose(i,u) then raise Match 
		       else sym		(*eliminates t*)
     | (_, Bound i) => if loose(i,t) then raise Match 
		       else asm_rl	(*eliminates u*)
     | (Free _, _) => if bnd orelse Logic.occs(t,u) then raise Match 
		      else sym		(*eliminates t*)
     | (_, Free _) => if bnd orelse Logic.occs(u,t) then raise Match 
		      else asm_rl	(*eliminates u*)
     | _ => raise Match;

(*Locates a substitutable variable on the left (resp. right) of an equality
   assumption.  Returns the number of intervening assumptions, paried with
   the rule asm_rl (resp. sym). *)
fun eq_var bnd =
  let fun eq_var_aux k (Const("all",_) $ Abs(_,_,t)) = eq_var_aux k t
	| eq_var_aux k (Const("==>",_) $ A $ B) = 
	      ((k, inspect_pair bnd (dest_eq A))
		      (*Exception Match comes from inspect_pair or dest_eq*)
	       handle Match => eq_var_aux (k+1) B)
	| eq_var_aux k _ = raise EQ_VAR
  in  eq_var_aux 0  end;

(*Select a suitable equality assumption and substitute throughout the subgoal
  Replaces only Bound variables if bnd is true*)
fun gen_hyp_subst_tac bnd i = DETERM (STATE(fn state =>
      let val (_,_,Bi,_) = dest_state(state,i)
	  val n = length(Logic.strip_assums_hyp Bi) - 1
	  val (k,symopt) = eq_var bnd Bi
      in 
	 EVERY [REPEATN k (etac rev_mp i),
		etac revcut_rl i,
		REPEATN (n-k) (etac rev_mp i),
		etac (symopt RS subst) i,
		REPEATN n (rtac imp_intr i)]
      end
      handle THM _ => no_tac | EQ_VAR => no_tac));

(*Substitutes for Free or Bound variables*)
val hyp_subst_tac = gen_hyp_subst_tac false;

(*Substitutes for Bound variables only -- this is always safe*)
val bound_hyp_subst_tac = gen_hyp_subst_tac true;

end
end;

