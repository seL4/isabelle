theory MutabelleExtra
imports Complex_Main "HOL-Library.Refute"
(*  "~/repos/afp/thys/AVL-Trees/AVL"
  "~/repos/afp/thys/BinarySearchTree/BinaryTree"
  "~/repos/afp/thys/Huffman/Huffman"
  "~/repos/afp/thys/List-Index/List_Index"
  "~/repos/afp/thys/Matrix/Matrix"
  "~/repos/afp/thys/NormByEval/NBE"
  "~/repos/afp/thys/Polynomials/Polynomial"
  "~/repos/afp/thys/Presburger-Automata/Presburger_Automata"
  "~/repos/afp/thys/Abstract-Rewriting/Abstract_Rewriting"*)
begin

ML_file \<open>mutabelle.ML\<close>
ML_file \<open>mutabelle_extra.ML\<close>


section \<open>configuration\<close>

ML \<open>val log_directory = ""\<close>


quickcheck_params [quiet, finite_types = false, report = false, size = 5, iterations = 1000]

(*
nitpick_params [timeout = 5, sat_solver = MiniSat_JNI, no_overlord, verbose, card = 1-5, iter = 1,2,4,8,12]
refute_params [maxtime = 10, minsize = 1, maxsize = 5, satsolver = jerusat]
*)

ML \<open>val mtds = [
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types false) "random",
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types true) "random",
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types false) "small",
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types true) "small"
]
\<close>

ML \<open>
fun mutation_testing_of (name, thy) =
  (MutabelleExtra.init_random 1.0;
  MutabelleExtra.thms_of false thy
  |> MutabelleExtra.take_random 200
  |> (fn thms => MutabelleExtra.mutate_theorems_and_write_report
         \<^theory> (1, 50) mtds thms (log_directory ^ "/" ^ name)))
\<close>
  

text \<open>Uncomment the following ML code to check the counterexample generation with all theorems of Complex_Main.\<close>

(*
ML {*

      MutabelleExtra.init_random 1.0;
      MutabelleExtra.thms_of true @{theory Complex_Main}
      |> MutabelleExtra.take_random 1000000
      |> (fn thms => List.drop (thms, 1000))
      |> (fn thms => MutabelleExtra.mutate_theorems_and_write_report
             @{theory} [
                        MutabelleExtra.quickcheck_mtd "code",
                        MutabelleExtra.smallcheck_mtd
                        (*MutabelleExtra.refute_mtd,
                        MutabelleExtra.nitpick_mtd*)] thms "/tmp/muta.out")

 *}
*)

section \<open>Mutation testing Isabelle theories\<close>

subsection \<open>List theory\<close>

(*
ML {*
mutation_testing_of ("List", @{theory List})
 *}
*)

section \<open>Mutation testing AFP theories\<close>

subsection \<open>AVL-Trees\<close>

(*
ML {*
mutation_testing_of ("AVL-Trees", @{theory AVL})
 *}
*)

subsection \<open>BinaryTree\<close>

(*
ML {*
mutation_testing_of ("BinaryTree", @{theory BinaryTree})
 *}
*)

subsection \<open>Huffman\<close>

(*
ML {*
mutation_testing_of ("Huffman", @{theory Huffman})
 *}
*)

subsection \<open>List_Index\<close>

(*
ML {*
mutation_testing_of ("List_Index", @{theory List_Index})
 *}
*)

subsection \<open>Matrix\<close>

(*
ML {*
mutation_testing_of ("Matrix", @{theory Matrix})
 *}
*)

subsection \<open>NBE\<close>

(*
ML {*
mutation_testing_of ("NBE", @{theory NBE})
 *}
*)

subsection \<open>Polynomial\<close>

(*
ML {*
mutation_testing_of ("Polynomial", @{theory Polynomial})
 *}
*)

subsection \<open>Presburger Automata\<close>

(*
ML {*
mutation_testing_of ("Presburger_Automata", @{theory Presburger_Automata})
 *}
*)

end
