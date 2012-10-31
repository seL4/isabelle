theory MutabelleExtra
imports Complex_Main "~~/src/HOL/Library/Refute"
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

ML_file "mutabelle.ML"
ML_file "mutabelle_extra.ML"


section {* configuration *}

ML {* val log_directory = "" *}


quickcheck_params [quiet, finite_types = false, report = false, size = 5, iterations = 1000]

(*
nitpick_params [timeout = 5, sat_solver = MiniSat, no_overlord, verbose, card = 1-5, iter = 1,2,4,8,12]
refute_params [maxtime = 10, minsize = 1, maxsize = 5, satsolver = jerusat]
*)
ML {* Try.auto_time_limit := 10.0 *}

ML {* val mtds = [
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types false) "random",
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types true) "random",
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types false) "small",
  MutabelleExtra.quickcheck_mtd (Config.put Quickcheck.finite_types true) "small"
]
*}

ML {*
fun mutation_testing_of (name, thy) =
  (MutabelleExtra.random_seed := 1.0;
  MutabelleExtra.thms_of false thy
  |> MutabelleExtra.take_random 200
  |> (fn thms => MutabelleExtra.mutate_theorems_and_write_report
         @{theory} (1, 50) mtds thms (log_directory ^ "/" ^ name)))
*}
  

text {* Uncomment the following ML code to check the counterexample generation with all theorems of Complex_Main. *}

(*
ML {*

      MutabelleExtra.random_seed := 1.0;
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

section {* Mutation testing Isabelle theories *}

subsection {* List theory *}

(*
ML {*
mutation_testing_of ("List", @{theory List})
 *}
*)

section {* Mutation testing AFP theories *}

subsection {* AVL-Trees *}

(*
ML {*
mutation_testing_of ("AVL-Trees", @{theory AVL})
 *}
*)

subsection {* BinaryTree *}

(*
ML {*
mutation_testing_of ("BinaryTree", @{theory BinaryTree})
 *}
*)

subsection {* Huffman *}

(*
ML {*
mutation_testing_of ("Huffman", @{theory Huffman})
 *}
*)

subsection {* List_Index *}

(*
ML {*
mutation_testing_of ("List_Index", @{theory List_Index})
 *}
*)

subsection {* Matrix *}

(*
ML {*
mutation_testing_of ("Matrix", @{theory Matrix})
 *}
*)

subsection {* NBE *}

(*
ML {*
mutation_testing_of ("NBE", @{theory NBE})
 *}
*)

subsection {* Polynomial *}

(*
ML {*
mutation_testing_of ("Polynomial", @{theory Polynomial})
 *}
*)

subsection {* Presburger Automata *}

(*
ML {*
mutation_testing_of ("Presburger_Automata", @{theory Presburger_Automata})
 *}
*)

end
