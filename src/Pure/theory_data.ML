(*  Title:      Pure/theory_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Type-safe interface for theory data.
*)

signature THEORY_DATA_ARGS =
sig
  val name: string
  type T
  val empty: T
  val copy: T -> T
  val prep_ext: T -> T
  val merge: T * T -> T
  val print: Sign.sg -> T -> unit
end;

signature THEORY_DATA =
sig
  type T
  val init: theory -> theory
  val print: theory -> unit
  val get_sg: Sign.sg -> T
  val get: theory -> T
  val put: T -> theory -> theory
end;

functor TheoryDataFun(Args: THEORY_DATA_ARGS): THEORY_DATA =
struct

(*object kind kept private!*)
val kind = Object.kind Args.name;

type T = Args.T;
exception Data of T;

val init =
  Theory.init_data kind
    (Data Args.empty,
      fn (Data x) => Data (Args.copy x),
      fn (Data x) => Data (Args.prep_ext x),
      fn (Data x1, Data x2) => Data (Args.merge (x1, x2)),
      fn sg => fn (Data x) => Args.print sg x);

val print = Theory.print_data kind;
val get_sg = Sign.get_data kind (fn Data x => x);
val get = get_sg o Theory.sign_of;
val put = Theory.put_data kind Data;

end;

(*hide private data access functions*)
structure Sign: SIGN = Sign;
structure Theory: THEORY = Theory;
