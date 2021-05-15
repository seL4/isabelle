(*  Title:      HOL/Mirabelle/Tools/mirabelle_quickcheck.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich

Mirabelle action: "quickcheck".
*)

structure Mirabelle_Quickcheck: sig end =
struct

val _ =
  Theory.setup (Mirabelle.command_action \<^binding>\<open>quickcheck\<close>
    (fn {arguments, timeout, ...} => fn {pre, ...} =>
      let
        val has_valid_key = member (op =) ["iterations", "size", "generator"] o fst;
        val quickcheck =
          Quickcheck.quickcheck (map (apsnd single) (filter has_valid_key arguments)) 1;
      in
        (case Timeout.apply timeout quickcheck pre of
          NONE => "no counterexample"
        | SOME _ => "counterexample found")
      end));

end
