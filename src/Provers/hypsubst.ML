(*  Title: 	Provers/hypsubst
    ID:         $Id$
    Authors: 	Martin D Coen, Tobias Nipkow and Lawrence C Paulson
    Copyright   1995  University of Cambridge

Tactic to substitute using the assumption x=t in the rest of the subgoal,
and to delete that assumption.  Original version due to Martin Coen.

This version uses the simplifier, and requires it to be already present.

Test data:

goal thy "!!x.[| Q(x,y,z); y=x; a=x; z=y; P(y) |] ==> P(z)";
goal thy "!!x.[| Q(x,y,z); z=f(x); x=z |] ==> P(z)";
goal thy "!!y. [| ?x=y; P(?x) |] ==> y = a";
goal thy "!!z. [| ?x=y; P(?x) |] ==> y = a";

by (hyp_subst_tac 1);
by (bound_hyp_subst_tac 1);

Here hyp_subst_tac goes wrong; harder still to prove P(f(f(a))) & P(f(a))
goal thy "P(a) --> (EX y. a=y --> P(f(a)))";
*)

signature HYPSUBST_DATA =
  sig
  structure Simplifier : SIMPLIFIER
  val dest_eq	       : term -> term*term*typ
  val eq_reflection    : thm		   (* a=b ==> a==b *)
  val imp_intr	       : thm		   (* (P ==> Q) ==> P-->Q *)
  val rev_mp	       : thm		   (* [| P;  P-->Q |] ==> Q *)
  val subst	       : thm		   (* [| a=b;  P(a) |] ==> P(b) *)
  val sym	       : thm		   (* a=b ==> b=a *)
  end;


signature HYPSUBST =
  sig
  val bound_hyp_subst_tac    : int -> tactic
  val hyp_subst_tac          : int -> tactic
    (*exported purely for debugging purposes*)
  val gen_hyp_subst_tac      : bool -> int -> tactic
  val vars_gen_hyp_subst_tac : bool -> int -> tactic
  val eq_var                 : bool -> bool -> term -> int * bool
  val inspect_pair           : bool -> bool -> term * term * typ -> bool
  val mk_eqs                 : thm -> thm list
  val thin_leading_eqs_tac   : bool -> int -> int -> tactic
  end;



functor HypsubstFun(Data: HYPSUBST_DATA): HYPSUBST = 
struct

local open Data in

exception EQ_VAR;

fun loose (i,t) = 0 mem_int add_loose_bnos(t,i,[]);

local val odot = ord"."
in
(*Simplifier turns Bound variables to dotted Free variables: 
  change it back (any Bound variable will do)
*)
fun contract t =
    case Pattern.eta_contract_atom t of
	Free(a,T) => if (ord a = odot) then Bound 0 else Free(a,T)
      | t'        => t'
end;

fun has_vars t = maxidx_of_term t <> ~1;

(*If novars then we forbid Vars in the equality.
  If bnd then we only look for Bound (or dotted Free) variables to eliminate. 
  When can we safely delete the equality?
    Not if it equates two constants; consider 0=1.
    Not if it resembles x=t[x], since substitution does not eliminate x.
    Not if it resembles ?x=0; another goal could instantiate ?x to Suc(i)
    Not if it involves a variable free in the premises, 
        but we can't check for this -- hence bnd and bound_hyp_subst_tac
  Prefer to eliminate Bound variables if possible.
  Result:  true = use as is,  false = reorient first *)
fun inspect_pair bnd novars (t,u,T) =
  if novars andalso maxidx_of_typ T <> ~1 
  then raise Match   (*variables in the type!*)
  else
  case (contract t, contract u) of
       (Bound i, _) => if loose(i,u) orelse novars andalso has_vars u 
		       then raise Match 
		       else true		(*eliminates t*)
     | (_, Bound i) => if loose(i,t) orelse novars andalso has_vars t  
		       then raise Match 
		       else false		(*eliminates u*)
     | (Free _, _) =>  if bnd orelse Logic.occs(t,u) orelse  
		          novars andalso has_vars u  
		       then raise Match 
		       else true		(*eliminates t*)
     | (_, Free _) =>  if bnd orelse Logic.occs(u,t) orelse  
		          novars andalso has_vars t 
		       then raise Match 
		       else false		(*eliminates u*)
     | _ => raise Match;

(*Locates a substitutable variable on the left (resp. right) of an equality
   assumption.  Returns the number of intervening assumptions. *)
fun eq_var bnd novars =
  let fun eq_var_aux k (Const("all",_) $ Abs(_,_,t)) = eq_var_aux k t
	| eq_var_aux k (Const("==>",_) $ A $ B) = 
	      ((k, inspect_pair bnd novars (dest_eq A))
		      (*Exception comes from inspect_pair or dest_eq*)
	       handle Match => eq_var_aux (k+1) B)
	| eq_var_aux k _ = raise EQ_VAR
  in  eq_var_aux 0  end;

(*We do not try to delete ALL equality assumptions at once.  But
  it is easy to handle several consecutive equality assumptions in a row.
  Note that we have to inspect the proof state after doing the rewriting,
  since e.g. z=f(x); x=z changes to z=f(x); x=f(x) and the second equality
  must NOT be deleted.  Tactic must rotate or delete m assumptions.
*)
fun thin_leading_eqs_tac bnd m = SUBGOAL (fn (Bi,i) =>
    let fun count []      = 0
	  | count (A::Bs) = ((inspect_pair bnd true (dest_eq A);  
			      1 + count Bs)
                             handle Match => 0)
        val j = Int.min(m, count (Logic.strip_assums_hyp Bi))
    in  REPEAT_DETERM_N j (etac thin_rl i)  THEN  rotate_tac (m-j) i
    end);

(*For the simpset.  Adds ALL suitable equalities, even if not first!
  No vars are allowed here, as simpsets are built from meta-assumptions*)
fun mk_eqs th = 
    [ if inspect_pair false false (Data.dest_eq (#prop (rep_thm th)))
      then th RS Data.eq_reflection
      else symmetric(th RS Data.eq_reflection) (*reorient*) ] 
    handle Match => [];  (*Exception comes from inspect_pair or dest_eq*)

local open Simplifier 
in

  val hyp_subst_ss = empty_ss setmksimps mk_eqs

  (*Select a suitable equality assumption and substitute throughout the subgoal
    Replaces only Bound variables if bnd is true*)
  fun gen_hyp_subst_tac bnd = SUBGOAL(fn (Bi,i) =>
	let val n = length(Logic.strip_assums_hyp Bi) - 1
	    val (k,_) = eq_var bnd true Bi
	in 
	   DETERM (EVERY [rotate_tac k i,
			  asm_full_simp_tac hyp_subst_ss i,
			  etac thin_rl i,
			  thin_leading_eqs_tac bnd (n-k) i])
	end
	handle THM _ => no_tac | EQ_VAR => no_tac);

end;

val ssubst = standard (sym RS subst);

(*Old version of the tactic above -- slower but the only way
  to handle equalities containing Vars.*)
fun vars_gen_hyp_subst_tac bnd = SUBGOAL(fn (Bi,i) =>
      let val n = length(Logic.strip_assums_hyp Bi) - 1
	  val (k,symopt) = eq_var bnd false Bi
      in 
	 DETERM
           (EVERY [REPEAT_DETERM_N k (etac rev_mp i),
		   etac revcut_rl i,
		   REPEAT_DETERM_N (n-k) (etac rev_mp i),
		   etac (if symopt then ssubst else subst) i,
		   REPEAT_DETERM_N n (rtac imp_intr i THEN rotate_tac ~1 i)])
      end
      handle THM _ => no_tac | EQ_VAR => no_tac);

(*Substitutes for Free or Bound variables*)
val hyp_subst_tac = 
    gen_hyp_subst_tac false ORELSE' vars_gen_hyp_subst_tac false;

(*Substitutes for Bound variables only -- this is always safe*)
val bound_hyp_subst_tac = 
    gen_hyp_subst_tac true ORELSE' vars_gen_hyp_subst_tac true;

end
end;

