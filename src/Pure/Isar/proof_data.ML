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
  val print: ProofContext.context -> T -> unit
end;

signature PROOF_DATA =
sig
  type T
  val init: theory -> theory
  val print: ProofContext.context -> unit
  val get: ProofContext.context -> T
  val put: T -> ProofContext.context -> ProofContext.context
  val map: (T -> T) -> ProofContext.context -> ProofContext.context
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
fun map f ctxt = put (f (get ctxt)) ctxt;

end;


(*hide private data access functions*)
structure ProofContext: PROOF_CONTEXT = ProofContext;
