(*  Title:      Tools/Argo/argo_common.ML
    Author:     Sascha Boehme

Common infrastructure for the decision procedures of Argo.
*)

signature ARGO_COMMON =
sig
  type literal = Argo_Lit.literal * Argo_Proof.proof option
  datatype 'a implied = Implied of 'a list | Conflict of Argo_Cls.clause
end

structure Argo_Common: ARGO_COMMON =
struct

type literal = Argo_Lit.literal * Argo_Proof.proof option
  (* Implied new knowledge accompanied with an optional proof. If there is no proof,
     the literal is to be treated hypothetically. If there is a proof, the literal is
     to be treated as uni clause. *)

datatype 'a implied = Implied of 'a list | Conflict of Argo_Cls.clause
  (* A result of a step of a decision procedure, either an implication of new knowledge
     or clause whose literals are known to be false. *)

end
