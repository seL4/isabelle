(*  Title:      HOL/Tools/SMT/z3_real.ML
    Author:     Sascha Boehme, TU Muenchen

Z3 setup for reals  based on a relaxed version of SMT-LIB (outside of LIRA).
*)

structure Z3_Real: sig end =
struct

val setup_builtins =
  SMT_Builtin.add_builtin_fun' Z3_Interface.smtlib_z3C
    (\<^Const>\<open>times \<^Type>\<open>real\<close>\<close>, "*") #>
  SMT_Builtin.add_builtin_fun' Z3_Interface.smtlib_z3C
    (\<^Const>\<open>divide \<^Type>\<open>real\<close>\<close>, "/")


val _ = Theory.setup (Context.theory_map
  setup_builtins)

end;
