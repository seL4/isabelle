(*  Title: 	Provers/hypsubst
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Martin Coen's tactic for substitution in the hypotheses
*)

signature HYPSUBST_DATA =
  sig
  val dest_eq: term -> term*term
  val imp_intr: thm	(* (P ==> Q) ==> P-->Q *)
  val rev_cut_eq: thm	(* [| a=b;  a=b ==> R |] ==> R *)
  val rev_mp: thm	(* [| P;  P-->Q |] ==> Q *)
  val subst: thm	(* [| a=b;  P(a) |] ==> P(b) *)
  val sym: thm		(* a=b ==> b=a *)
  end;

signature HYPSUBST =
  sig
  val bound_hyp_subst_tac : int -> tactic
  val hyp_subst_tac       : int -> tactic
    (*exported purely for debugging purposes*)
  val eq_var              : bool -> term -> term * thm
  val inspect_pair        : bool -> term * term -> term * thm
  val liftvar             : int -> typ list -> term
  end;

functor HypsubstFun(Data: HYPSUBST_DATA): HYPSUBST = 
struct

local open Data in

fun REPEATN 0 tac = all_tac
  | REPEATN n tac = Tactic(fn state =>
                           tapply(tac THEN REPEATN (n-1) tac,  state));

local
  val T = case #1 (types_sorts rev_cut_eq) ("a",0) of
	      Some T => T
   	    | None   => error"No such variable in rev_cut_eq"
in
  fun liftvar inc paramTs = Var(("a",inc), paramTs ---> incr_tvar inc T);
end;

exception EQ_VAR;

fun loose (i,t) = 0 mem add_loose_bnos(t,i,[]);

(*It's not safe to substitute for a constant; consider 0=1.
  It's not safe to substitute for x=t[x] since x is not eliminated.
  It's not safe to substitute for a variable free in the premises,
    but how could we check for this?*)
fun inspect_pair bnd (t,u) =
  case (Pattern.eta_contract t, Pattern.eta_contract u) of
       (Bound i, _) => if loose(i,u) then raise Match 
		       else (t, asm_rl)
     | (_, Bound i) => if loose(i,t) then raise Match 
		       else (u, sym)
     | (Free _, _) => if bnd orelse Logic.occs(t,u) then raise Match 
		      else (t, asm_rl)
     | (_, Free _) => if bnd orelse Logic.occs(u,t) then raise Match 
		      else (u, sym) 
     | _ => raise Match;

 (* Extracts the name of the variable on the left (resp. right) of an equality
   assumption.  Returns the rule asm_rl (resp. sym). *)
fun eq_var bnd (Const("all",_) $ Abs(_,_,t)) = eq_var bnd t
  | eq_var bnd (Const("==>",_) $ A $ B) = 
	(inspect_pair bnd (dest_eq A) 
	        (*Match comes from inspect_pair or dest_eq*)
	 handle Match => eq_var bnd B)
  | eq_var bnd _ = raise EQ_VAR;

(*Lift and instantiate a rule wrt the given state and subgoal number *)
fun lift_instpair (state, i, t, rule) =
  let val {maxidx,sign,...} = rep_thm state
      val (_, _, Bi, _) = dest_state(state,i)
      val params = Logic.strip_params Bi
      val var = liftvar (maxidx+1) (map #2 params)
      and u   = Unify.rlist_abs(rev params, t)
      and cterm = Sign.cterm_of sign
  in cterm_instantiate [(cterm var, cterm u)] (lift_rule (state,i) rule)
  end;

fun eres_instpair_tac t rule i = STATE (fn state => 
	   compose_tac (true, lift_instpair (state, i, t, rule),
			length(prems_of rule)) i);

val ssubst = sym RS subst;

(*Select a suitable equality assumption and substitute throughout the subgoal
  Replaces only Bound variables if bnd is true*)
fun gen_hyp_subst_tac bnd i = DETERM (STATE(fn state =>
      let val (_,_,Bi,_) = dest_state(state,i)
	  val n = length(Logic.strip_assums_hyp Bi) - 1
	  val (t,symopt) = eq_var bnd Bi
      in eres_instpair_tac t (symopt RS rev_cut_eq) i  THEN
         REPEATN n (etac rev_mp i) THEN
	 etac ssubst i THEN REPEATN n (rtac imp_intr i)
      end
      handle THM _ => no_tac | EQ_VAR => no_tac));

(*Substitutes for Free or Bound variables*)
val hyp_subst_tac = gen_hyp_subst_tac false;

(*Substitutes for Bound variables only -- this is always safe*)
val bound_hyp_subst_tac = gen_hyp_subst_tac true;

end
end;

