(*  Title:      Pure/Isar/proof_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Type-safe interface for proof context data.
*)

signature PROOF_DATA_ARGS =
sig
  val name: string
  type T
  val init: theory -> T
  val print: Proof.context -> T -> unit
end;

signature PROOF_DATA =
sig
  type T
  val init: theory -> theory
  val print: Proof.context -> unit
  val get: Proof.context -> T
  val put: T -> Proof.context -> Proof.context
  val get_st: Proof.state -> T
  val put_st: T -> Proof.state -> Proof.state
end;

functor ProofDataFun(Args: PROOF_DATA_ARGS): PROOF_DATA =
struct

(*object kind kept private!*)
val kind = Object.kind Args.name;

type T = Args.T;
exception Data of T;

val init =
  ProofContext.init_data kind
    (Data o Args.init, fn ctxt => fn (Data x) => Args.print ctxt x);

val print = ProofContext.print_data kind;
val get = ProofContext.get_data kind (fn Data x => x);
val put = ProofContext.put_data kind Data;
val get_st = get o Proof.context_of;
val put_st = Proof.put_data kind Data;

end;


(*hide private data access functions*)
structure ProofContext: PROOF_CONTEXT = ProofContext;
structure Proof: PROOF = Proof;
