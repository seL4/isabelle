(*  Title:      HOL/Mirabelle/Tools/mirabelle_try0.ML
    Author:     Jasmin Blanchette, TU Munich
    Author:     Makarius

Mirabelle action: "try0".
*)

structure Mirabelle_Try0 : sig end =
struct

val _ =
  Theory.setup (Mirabelle.command_action \<^binding>\<open>try0\<close>
    (fn {timeout, ...} => fn {pre, ...} =>
      if Timeout.apply (Time.scale 10.0 timeout) (Try0.try0 (SOME timeout) ([], [], [], [])) pre
      then "succeeded" else ""));

end
