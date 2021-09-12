(*  Title:      FOLP/hypsubst.ML
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Original version of Provers/hypsubst.  Cannot use new version because it
relies on the new simplifier!

Martin Coen's tactic for substitution in the hypotheses
*)

signature HYPSUBST_DATA =
  sig
  val dest_eq   : term -> term*term
  val imp_intr  : thm           (* (P ==> Q) ==> P-->Q *)
  val rev_mp    : thm           (* [| P;  P-->Q |] ==> Q *)
  val subst     : thm           (* [| a=b;  P(a) |] ==> P(b) *)
  val sym       : thm           (* a=b ==> b=a *)
  end;

signature HYPSUBST =
  sig
  val bound_hyp_subst_tac : Proof.context -> int -> tactic
  val hyp_subst_tac       : Proof.context -> int -> tactic
    (*exported purely for debugging purposes*)
  val eq_var              : bool -> term -> int * thm
  val inspect_pair        : bool -> term * term -> thm
  end;

functor Hypsubst(Data: HYPSUBST_DATA): HYPSUBST =
struct

local open Data in

exception EQ_VAR;

(*It's not safe to substitute for a constant; consider 0=1.
  It's not safe to substitute for x=t[x] since x is not eliminated.
  It's not safe to substitute for a Var; what if it appears in other goals?
  It's not safe to substitute for a variable free in the premises,
    but how could we check for this?*)
fun inspect_pair bnd (t, u) =
  (case (Envir.eta_contract t, Envir.eta_contract u) of
    (Bound i, _) =>
      if loose_bvar1 (u, i) then raise Match
      else sym         (*eliminates t*)
   | (_, Bound i) =>
      if loose_bvar (t, i) then raise Match
      else asm_rl      (*eliminates u*)
   | (Free _, _) =>
      if bnd orelse Logic.occs (t, u) then raise Match
      else sym          (*eliminates t*)
   | (_, Free _) =>
      if bnd orelse Logic.occs(u,t) then raise Match
      else asm_rl       (*eliminates u*)
   | _ => raise Match);

(*Locates a substitutable variable on the left (resp. right) of an equality
   assumption.  Returns the number of intervening assumptions, paried with
   the rule asm_rl (resp. sym). *)
fun eq_var bnd =
  let fun eq_var_aux k \<^Const_>\<open>Pure.all _ for \<open>Abs(_,_,t)\<close>\<close> = eq_var_aux k t
        | eq_var_aux k \<^Const_>\<open>Pure.imp for A B\<close> =
              ((k, inspect_pair bnd (dest_eq A))
                      (*Exception Match comes from inspect_pair or dest_eq*)
               handle Match => eq_var_aux (k+1) B)
        | eq_var_aux k _ = raise EQ_VAR
  in  eq_var_aux 0  end;

(*Select a suitable equality assumption and substitute throughout the subgoal
  Replaces only Bound variables if bnd is true*)
fun gen_hyp_subst_tac bnd ctxt = SUBGOAL(fn (Bi,i) =>
      let val n = length(Logic.strip_assums_hyp Bi) - 1
          val (k,symopt) = eq_var bnd Bi
      in
         DETERM
           (EVERY [REPEAT_DETERM_N k (eresolve_tac ctxt [rev_mp] i),
                   eresolve_tac ctxt [revcut_rl] i,
                   REPEAT_DETERM_N (n-k) (eresolve_tac ctxt [rev_mp] i),
                   eresolve_tac ctxt [symopt RS subst] i,
                   REPEAT_DETERM_N n (resolve_tac ctxt [imp_intr] i)])
      end
      handle THM _ => no_tac | EQ_VAR => no_tac);

(*Substitutes for Free or Bound variables*)
val hyp_subst_tac = gen_hyp_subst_tac false;

(*Substitutes for Bound variables only -- this is always safe*)
val bound_hyp_subst_tac = gen_hyp_subst_tac true;

end
end;

