(*  Title:      Provers/hypsubst.ML
    Authors:    Martin D Coen, Tobias Nipkow and Lawrence C Paulson
    Copyright   1995  University of Cambridge

Basic equational reasoning: hyp_subst_tac and methods "hypsubst", "subst".

Tactic to substitute using (at least) the assumption x=t in the rest
of the subgoal, and to delete (at least) that assumption.  Original
version due to Martin Coen.

This version uses the simplifier, and requires it to be already present.

Test data:

Goal "!!x.[| Q(x,y,z); y=x; a=x; z=y; P(y) |] ==> P(z)";
Goal "!!x.[| Q(x,y,z); z=f(x); x=z |] ==> P(z)";
Goal "!!y. [| ?x=y; P(?x) |] ==> y = a";
Goal "!!z. [| ?x=y; P(?x) |] ==> y = a";

Goal "!!x a. [| x = f(b); g(a) = b |] ==> P(x)";

by (bound_hyp_subst_tac 1);
by (hyp_subst_tac 1);

Here hyp_subst_tac goes wrong; harder still to prove P(f(f(a))) & P(f(a))
Goal "P(a) --> (EX y. a=y --> P(f(a)))";

Goal "!!x. [| Q(x,h1); P(a,h2); R(x,y,h3); R(y,z,h4); x=f(y); \
\                 P(x,h5); P(y,h6); K(x,h7) |] ==> Q(x,c)";
by (blast_hyp_subst_tac true 1);
*)

signature HYPSUBST_DATA =
sig
  val dest_Trueprop    : term -> term
  val dest_eq          : term -> term * term
  val dest_imp         : term -> term * term
  val eq_reflection    : thm               (* a=b ==> a==b *)
  val rev_eq_reflection: thm               (* a==b ==> a=b *)
  val imp_intr         : thm               (* (P ==> Q) ==> P-->Q *)
  val rev_mp           : thm               (* [| P;  P-->Q |] ==> Q *)
  val subst            : thm               (* [| a=b;  P(a) |] ==> P(b) *)
  val sym              : thm               (* a=b ==> b=a *)
  val thin_refl        : thm               (* [|x=x; PROP W|] ==> PROP W *)
end;

signature HYPSUBST =
sig
  val bound_hyp_subst_tac    : int -> tactic
  val hyp_subst_tac          : int -> tactic
  val blast_hyp_subst_tac    : bool -> int -> tactic
  val stac                   : thm -> int -> tactic
  val hypsubst_setup         : theory -> theory
end;

functor Hypsubst(Data: HYPSUBST_DATA): HYPSUBST =
struct

exception EQ_VAR;

(*Simplifier turns Bound variables to special Free variables:
  change it back (any Bound variable will do)*)
fun contract t =
  (case Envir.eta_contract t of
    Free (a, T) => if Name.is_bound a then Bound 0 else Free (a, T)
  | t' => t');

val has_vars = Term.exists_subterm Term.is_Var;
val has_tvars = Term.exists_type (Term.exists_subtype Term.is_TVar);

(*If novars then we forbid Vars in the equality.
  If bnd then we only look for Bound variables to eliminate.
  When can we safely delete the equality?
    Not if it equates two constants; consider 0=1.
    Not if it resembles x=t[x], since substitution does not eliminate x.
    Not if it resembles ?x=0; consider ?x=0 ==> ?x=1 or even ?x=0 ==> P
    Not if it involves a variable free in the premises,
        but we can't check for this -- hence bnd and bound_hyp_subst_tac
  Prefer to eliminate Bound variables if possible.
  Result:  true = use as is,  false = reorient first *)
fun inspect_pair bnd novars (t, u) =
  if novars andalso (has_tvars t orelse has_tvars u)
  then raise Match   (*variables in the type!*)
  else
    (case (contract t, contract u) of
      (Bound i, _) =>
        if loose_bvar1 (u, i) orelse novars andalso has_vars u
        then raise Match
        else true                (*eliminates t*)
    | (_, Bound i) =>
        if loose_bvar1 (t, i) orelse novars andalso has_vars t
        then raise Match
        else false               (*eliminates u*)
    | (t' as Free _, _) =>
        if bnd orelse Logic.occs (t', u) orelse novars andalso has_vars u
        then raise Match
        else true                (*eliminates t*)
    | (_, u' as Free _) =>
        if bnd orelse Logic.occs (u', t) orelse novars andalso has_vars t
        then raise Match
        else false               (*eliminates u*)
    | _ => raise Match);

(*Locates a substitutable variable on the left (resp. right) of an equality
   assumption.  Returns the number of intervening assumptions. *)
fun eq_var bnd novars =
  let fun eq_var_aux k (Const("all",_) $ Abs(_,_,t)) = eq_var_aux k t
        | eq_var_aux k (Const("==>",_) $ A $ B) =
              ((k, inspect_pair bnd novars
                    (Data.dest_eq (Data.dest_Trueprop A)))
               handle TERM _ => eq_var_aux (k+1) B
                 | Match => eq_var_aux (k+1) B)
        | eq_var_aux k _ = raise EQ_VAR
  in  eq_var_aux 0  end;

(*For the simpset.  Adds ALL suitable equalities, even if not first!
  No vars are allowed here, as simpsets are built from meta-assumptions*)
fun mk_eqs bnd th =
    [ if inspect_pair bnd false (Data.dest_eq (Data.dest_Trueprop (Thm.prop_of th)))
      then th RS Data.eq_reflection
      else Thm.symmetric(th RS Data.eq_reflection) (*reorient*) ]
    handle TERM _ => [] | Match => [];

local
in

  (*Select a suitable equality assumption; substitute throughout the subgoal
    If bnd is true, then it replaces Bound variables only. *)
  fun gen_hyp_subst_tac bnd =
    let fun tac i st = SUBGOAL (fn (Bi, _) =>
      let
        val (k, _) = eq_var bnd true Bi
        val hyp_subst_ss = Simplifier.global_context (Thm.theory_of_thm st) empty_ss
          |> Simplifier.set_mksimps (K (mk_eqs bnd))
      in EVERY [rotate_tac k i, asm_lr_simp_tac hyp_subst_ss i,
        etac thin_rl i, rotate_tac (~k) i]
      end handle THM _ => no_tac | EQ_VAR => no_tac) i st
    in REPEAT_DETERM1 o tac end;

end;

val ssubst = Drule.export_without_context (Data.sym RS Data.subst);

fun inst_subst_tac b rl = CSUBGOAL (fn (cBi, i) =>
  case try (Logic.strip_assums_hyp #> hd #>
      Data.dest_Trueprop #> Data.dest_eq #> pairself contract) (Thm.term_of cBi) of
    SOME (t, t') =>
      let
        val Bi = Thm.term_of cBi;
        val ps = Logic.strip_params Bi;
        val U = Term.fastype_of1 (rev (map snd ps), t);
        val Q = Data.dest_Trueprop (Logic.strip_assums_concl Bi);
        val rl' = Thm.lift_rule cBi rl;
        val Var (ixn, T) = Term.head_of (Data.dest_Trueprop
          (Logic.strip_assums_concl (Thm.prop_of rl')));
        val (v1, v2) = Data.dest_eq (Data.dest_Trueprop
          (Logic.strip_assums_concl (hd (Thm.prems_of rl'))));
        val (Ts, V) = split_last (Term.binder_types T);
        val u = list_abs (ps @ [("x", U)], case (if b then t else t') of
            Bound j => subst_bounds (map Bound
              ((1 upto j) @ 0 :: (j + 2 upto length ps)), Q)
          | t => Term.abstract_over (t, Term.incr_boundvars 1 Q));
        val thy = Thm.theory_of_thm rl';
        val (instT, _) = Thm.match (pairself (cterm_of thy o Logic.mk_type) (V, U));
      in compose_tac (true, Drule.instantiate_normalize (instT,
        map (pairself (cterm_of thy))
          [(Var (ixn, Ts ---> U --> body_type T), u),
           (Var (fst (dest_Var (head_of v1)), Ts ---> U), list_abs (ps, t)),
           (Var (fst (dest_Var (head_of v2)), Ts ---> U), list_abs (ps, t'))]) rl',
        nprems_of rl) i
      end
  | NONE => no_tac);

val imp_intr_tac = rtac Data.imp_intr;

(* FIXME: "etac Data.rev_mp i" will not behave as expected if goal has *)
(* premises containing meta-implications or quantifiers                *)

(*Old version of the tactic above -- slower but the only way
  to handle equalities containing Vars.*)
fun vars_gen_hyp_subst_tac bnd = SUBGOAL(fn (Bi,i) =>
      let val n = length(Logic.strip_assums_hyp Bi) - 1
          val (k,symopt) = eq_var bnd false Bi
      in
         DETERM
           (EVERY [REPEAT_DETERM_N k (etac Data.rev_mp i),
                   rotate_tac 1 i,
                   REPEAT_DETERM_N (n-k) (etac Data.rev_mp i),
                   inst_subst_tac symopt (if symopt then ssubst else Data.subst) i,
                   REPEAT_DETERM_N n (imp_intr_tac i THEN rotate_tac ~1 i)])
      end
      handle THM _ => no_tac | EQ_VAR => no_tac);

(*Substitutes for Free or Bound variables*)
val hyp_subst_tac = FIRST' [ematch_tac [Data.thin_refl],
        gen_hyp_subst_tac false, vars_gen_hyp_subst_tac false];

(*Substitutes for Bound variables only -- this is always safe*)
val bound_hyp_subst_tac =
    gen_hyp_subst_tac true ORELSE' vars_gen_hyp_subst_tac true;


(** Version for Blast_tac.  Hyps that are affected by the substitution are
    moved to the front.  Defect: even trivial changes are noticed, such as
    substitutions in the arguments of a function Var. **)

(*final re-reversal of the changed assumptions*)
fun reverse_n_tac 0 i = all_tac
  | reverse_n_tac 1 i = rotate_tac ~1 i
  | reverse_n_tac n i =
      REPEAT_DETERM_N n (rotate_tac ~1 i THEN etac Data.rev_mp i) THEN
      REPEAT_DETERM_N n (imp_intr_tac i THEN rotate_tac ~1 i);

(*Use imp_intr, comparing the old hyps with the new ones as they come out.*)
fun all_imp_intr_tac hyps i =
  let
    fun imptac (r, []) st = reverse_n_tac r i st
      | imptac (r, hyp::hyps) st =
          let
            val (hyp', _) =
              term_of (Thm.cprem_of st i)
              |> Logic.strip_assums_concl
              |> Data.dest_Trueprop |> Data.dest_imp;
            val (r', tac) =
              if Pattern.aeconv (hyp, hyp')
              then (r, imp_intr_tac i THEN rotate_tac ~1 i)
              else (*leave affected hyps at end*) (r + 1, imp_intr_tac i);
          in
            (case Seq.pull (tac st) of
              NONE => Seq.single st
            | SOME (st', _) => imptac (r', hyps) st')
          end
  in imptac (0, rev hyps) end;


fun blast_hyp_subst_tac trace = SUBGOAL(fn (Bi,i) =>
      let val (k,symopt) = eq_var false false Bi
          val hyps0 = map Data.dest_Trueprop (Logic.strip_assums_hyp Bi)
          (*omit selected equality, returning other hyps*)
          val hyps = List.take(hyps0, k) @ List.drop(hyps0, k+1)
          val n = length hyps
      in
         if trace then tracing "Substituting an equality" else ();
         DETERM
           (EVERY [REPEAT_DETERM_N k (etac Data.rev_mp i),
                   rotate_tac 1 i,
                   REPEAT_DETERM_N (n-k) (etac Data.rev_mp i),
                   inst_subst_tac symopt (if symopt then ssubst else Data.subst) i,
                   all_imp_intr_tac hyps i])
      end
      handle THM _ => no_tac | EQ_VAR => no_tac);


(*apply an equality or definition ONCE;
  fails unless the substitution has an effect*)
fun stac th =
  let val th' = th RS Data.rev_eq_reflection handle THM _ => th
  in CHANGED_GOAL (rtac (th' RS ssubst)) end;


(* theory setup *)

val hypsubst_setup =
  Method.setup @{binding hypsubst}
    (Scan.succeed (K (SIMPLE_METHOD' (CHANGED_PROP o hyp_subst_tac))))
    "substitution using an assumption (improper)" #>
  Method.setup @{binding simplesubst} (Attrib.thm >> (fn th => K (SIMPLE_METHOD' (stac th))))
    "simple substitution";

end;
