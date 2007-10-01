(*  Title:      Pure/context_position.ML
    ID:         $Id$
    Author:     Makarius

Context positions.
*)

signature CONTEXT_POSITION =
sig
  val put: Position.T -> Context.generic -> Context.generic
  val put_ctxt: Position.T -> Proof.context -> Proof.context
  val get: Proof.context -> Position.T
  val str_of: Proof.context -> string
  val properties_of: Proof.context -> Markup.property list
end;

structure ContextPosition: CONTEXT_POSITION =
struct

structure Data = GenericDataFun
(
  type T = Position.T;
  val empty = Position.none;
  fun extend _ = empty;
  fun merge _ _ = empty;
);

val put = Data.put;
val put_ctxt = Context.proof_map o put;

val get = Data.get o Context.Proof;
val str_of = Position.str_of o get;
val properties_of = Position.properties_of o get;

end;
