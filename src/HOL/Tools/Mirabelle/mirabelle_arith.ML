(*  Title:      HOL/Mirabelle/Tools/mirabelle_arith.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
    Author:     Makarius

Mirabelle action: "arith".
*)

structure Mirabelle_Arith: sig end =
struct

val _ =
  Theory.setup (Mirabelle.command_action \<^binding>\<open>arith\<close>
    (fn {timeout, ...} => fn {pre, ...} =>
      if Mirabelle.can_apply timeout Arith_Data.arith_tac pre
      then "succeeded" else ""));

end
