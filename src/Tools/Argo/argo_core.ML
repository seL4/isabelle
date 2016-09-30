(*  Title:      Tools/Argo/argo_core.ML
    Author:     Sascha Boehme

Core of the Argo theorem prover implementing the DPLL(T) loop.

The implementation is based on:

  Harald Ganzinger, George Hagen, Robert Nieuwenhuis, Albert Oliveras,
  Cesare Tinelli. DPLL(T): Fast decision procedures. In Lecture Notes in
  Computer Science, volume 3114, pages 175-188. Springer, 2004.

  Robert Nieuwenhuis, Albert Oliveras, Cesare Tinelli. Solving SAT and
  SAT modulo theories: From an abstract Davis-Putnam-Logemann-Loveland
  procedure to DPLL(T). In Journal of the ACM, volume 53(6), pages
  937-977.  ACM, 2006.
*)

signature ARGO_CORE =
sig
  (* context *)
  type context
  val context: context

  (* enriching the context *)
  val identify: Argo_Term.item -> context -> Argo_Term.identified * context
  val add_atom: Argo_Term.item -> context -> Argo_Term.identified * context
  val add_axiom: Argo_Cls.clause -> context -> context

  (* DPLL(T) loop *)
  val run: context -> context (* raises Argo_Proof.UNSAT *)

  (* model *)
  val model_of: context -> string * Argo_Expr.typ -> bool option
end

structure Argo_Core: ARGO_CORE =
struct

(* context *)

type context = {
  terms: Argo_Term.context, (* the term context to identify equal expressions *)
  iter: int, (* the current iteration of the search *)
  cdcl: Argo_Cdcl.context, (* the context of the propositional solver *)
  thy: Argo_Thy.context} (* the context of the theory solver *)

fun mk_context terms iter cdcl thy: context = {terms=terms, iter=iter, cdcl=cdcl, thy=thy}

val context = mk_context Argo_Term.context 1 Argo_Cdcl.context Argo_Thy.context

fun backjump levels = funpow levels Argo_Thy.backtrack


(* enriching the context *)

fun identify i ({terms, iter, cdcl, thy}: context) =
  let val (identified, terms) = Argo_Term.identify_item i terms
  in (identified, mk_context terms iter cdcl thy) end

fun add_atom i cx =
  (case identify i cx of
    known as (Argo_Term.Known _, _) => known
  | (atom as Argo_Term.New t, {terms, iter, cdcl, thy}: context) =>
      (case (Argo_Cdcl.add_atom t cdcl, Argo_Thy.add_atom t thy) of
        (cdcl, (NONE, thy)) => (atom, mk_context terms iter cdcl thy)
      | (cdcl, (SOME lit, thy)) =>
          (case Argo_Cdcl.assume Argo_Thy.explain lit cdcl thy of
            (NONE, cdcl, thy) => (atom, mk_context terms iter cdcl thy)
          | (SOME _, _, _) => raise Fail "bad conflict with new atom")))

fun add_axiom cls ({terms, iter, cdcl, thy}: context) =
  let val (levels, cdcl) = Argo_Cdcl.add_axiom cls cdcl
  in mk_context terms iter cdcl (backjump levels thy) end


(* DPLL(T) loop: CDCL with theories *)

datatype implications = None | Implications | Conflict of Argo_Cls.clause

fun cdcl_assume [] cdcl thy = (NONE, cdcl, thy)
  | cdcl_assume (lit :: lits) cdcl thy =
      (* assume an assignment deduced by the theory solver *)
      (case Argo_Cdcl.assume Argo_Thy.explain lit cdcl thy of
        (NONE, cdcl, thy) => cdcl_assume lits cdcl thy
      | (SOME cls, cdcl, thy) => (SOME cls, cdcl, thy))

fun theory_deduce _ (conflict as (Conflict _, _, _)) = conflict
  | theory_deduce f (result, cdcl, thy) =
      (case f thy of
        (Argo_Common.Implied [], thy) => (result, cdcl, thy)
      | (Argo_Common.Implied lits, thy) => 
          (* turn all implications of the theory solver into propositional assignments *)
          (case cdcl_assume lits cdcl thy of
            (NONE, cdcl, thy) => (Implications, cdcl, thy)
          | (SOME cls, cdcl, thy) => (Conflict cls, cdcl, thy))
      | (Argo_Common.Conflict cls, thy) => (Conflict cls, cdcl, thy))

fun theory_assume [] cdcl thy = (None, cdcl, thy)
  | theory_assume lps cdcl thy =
      (None, cdcl, thy)
      (* propagate all propositional implications to the theory solver *)
      |> fold (theory_deduce o Argo_Thy.assume) lps
      (* check the consistency of the theory model *)
      |> theory_deduce Argo_Thy.check

fun search limit cdcl thy =
  (* collect all propositional implications of the last assignments *)
  (case Argo_Cdcl.propagate cdcl of
    (Argo_Common.Implied lps, cdcl) =>
      (* propagate all propositional implications to the theory solver *)
      (case theory_assume lps cdcl thy of
        (None, cdcl, thy) =>
          (* stop searching if the conflict limit has been exceeded *)
          if limit <= 0 then (false, cdcl, thy)
          else
            (* no further propositional assignments, choose a value for the next unassigned atom *)
            (case Argo_Cdcl.decide cdcl of
              NONE => (true, cdcl, thy) (* the context is satisfiable *)
            | SOME cdcl => search limit cdcl (Argo_Thy.add_level thy))
      | (Implications, cdcl, thy) => search limit cdcl thy
      | (Conflict ([], p), _, _) => Argo_Proof.unsat p
      | (Conflict cls, cdcl, thy) => analyze cls limit cdcl thy)
  | (Argo_Common.Conflict cls, cdcl) => analyze cls limit cdcl thy)

and analyze cls limit cdcl thy =
  (* analyze the conflict, probably using lazy explanations from the theory solver *)
  let val (levels, cdcl, thy) = Argo_Cdcl.analyze Argo_Thy.explain cls cdcl thy
  in search (limit - 1) cdcl (backjump levels thy) end

fun luby_number i =
  let
    fun mult p = if p < i + 1 then mult (2 * p) else p
    val p = mult 2
  in if i = p - 1 then p div 2 else luby_number (i - (p div 2) + 1) end

fun next_restart_limit iter = 100 * luby_number iter

fun loop iter cdcl thy =
  (* perform a limited search that is stopped after a certain number of conflicts *)
  (case search (next_restart_limit iter) cdcl thy of
    (true, cdcl, thy) => (iter + 1, cdcl, thy)
  | (false, cdcl, thy) =>
      (* restart the solvers to avoid that they get stuck in a fruitless search *)
      let val (levels, cdcl) = Argo_Cdcl.restart cdcl
      in loop (iter + 1) cdcl (backjump levels thy) end)

fun run ({terms, iter, cdcl, thy}: context) =
  let val (iter, cdcl, thy) = loop iter cdcl (Argo_Thy.prepare thy)
  in mk_context terms iter cdcl thy end


(* model *)

fun model_of ({terms, cdcl, ...}: context) c =
  (case Argo_Term.identify_item (Argo_Term.Expr (Argo_Expr.E (Argo_Expr.Con c, []))) terms of
    (Argo_Term.Known t, _) => Argo_Cdcl.assignment_of cdcl (Argo_Lit.Pos t)
  | (Argo_Term.New _, _) => NONE)

end
