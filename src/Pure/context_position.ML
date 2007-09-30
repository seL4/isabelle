(*  Title:      Pure/context_position.ML
    ID:         $Id$
    Author:     Makarius

Context positions.
*)

signature CONTEXT_POSITION =
sig
  val put: Position.T -> Proof.context -> Proof.context
  val get: Proof.context -> Position.T
  val str_of: Proof.context -> string
  val properties_of: Proof.context -> Markup.property list
end;

structure ContextPosition: CONTEXT_POSITION =
struct

structure Data = ProofDataFun
(
  type T = Position.T;
  fun init _ = Position.none;
);

val put = Data.put;
val get = Data.get;
val str_of = Position.str_of o get;
val properties_of = Position.properties_of o get;

end;
