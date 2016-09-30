(*  Title:      Tools/Argo/argo_cls.ML
    Author:     Sascha Boehme

Representation of clauses. Clauses are disjunctions of literals with a proof that explains
why the disjunction holds.
*)

signature ARGO_CLS =
sig
  type clause = Argo_Lit.literal list * Argo_Proof.proof
  val eq_clause: clause * clause -> bool

  (* two-literal watches for clauses *)
  type table
  val table: table
  val put_watches: clause -> Argo_Lit.literal * Argo_Lit.literal -> table -> table
  val get_watches: table -> clause -> Argo_Lit.literal * Argo_Lit.literal
end

structure Argo_Cls: ARGO_CLS =
struct

type clause = Argo_Lit.literal list * Argo_Proof.proof

fun eq_clause ((_, p1), (_, p2)) = Argo_Proof.eq_proof_id (apply2 Argo_Proof.id_of (p1, p2))
fun clause_ord ((_, p1), (_, p2)) = Argo_Proof.proof_id_ord (apply2 Argo_Proof.id_of (p1, p2))


(* two-literal watches for clauses *)

(*
  The CDCL solver keeps a mapping of some literals to clauses. Exactly two literals
  of a clause are used to index the clause.
*)

structure Clstab = Table(type key = clause val ord = clause_ord)

type table = (Argo_Lit.literal * Argo_Lit.literal) Clstab.table

val table: table = Clstab.empty

fun put_watches cls lp table = Clstab.update (cls, lp) table
fun get_watches table cls = the (Clstab.lookup table cls)

end
