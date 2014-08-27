(*  Title:      HOL/Tools/SMT/z3_real.ML
    Author:     Sascha Boehme, TU Muenchen

Z3 setup for reals.
*)

structure Z3_Real: sig end =
struct

fun real_type_parser (SMTLIB.Sym "Real", []) = SOME @{typ Real.real}
  | real_type_parser _ = NONE

fun real_term_parser (SMTLIB.Dec (i, 0), []) = SOME (HOLogic.mk_number @{typ Real.real} i)
  | real_term_parser (SMTLIB.Sym "/", [t1, t2]) =
      SOME (@{term "inverse_class.divide :: real => _"} $ t1 $ t2)
  | real_term_parser (SMTLIB.Sym "to_real", [t]) = SOME (@{term "Real.real :: int => _"} $ t)
  | real_term_parser _ = NONE

fun abstract abs t =
  (case t of
    (c as @{term "inverse_class.divide :: real => _"}) $ t1 $ t2 =>
      abs t1 ##>> abs t2 #>> (fn (u1, u2) => SOME (c $ u1 $ u2))
  | (c as @{term "Real.real :: int => _"}) $ t =>
      abs t #>> (fn u => SOME (c $ u))
  | _ => pair NONE)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser real_type_parser #>
  SMTLIB_Proof.add_term_parser real_term_parser #>
  Z3_Replay_Methods.add_arith_abstracter abstract))

end;
