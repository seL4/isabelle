use_thys [
  "Examples",
  "Predicate_Compile_Tests",
(*  "Predicate_Compile_Quickcheck_Examples", -- should be added again soon *)
  "Specialisation_Examples",
(*  "Hotel_Example_Small_Generator",*)
  "IMP_1",
  "IMP_2"
(*  "IMP_3",
  "IMP_4"*)];

if getenv "ISABELLE_SWIPL" = "" andalso getenv "ISABELLE_YAP" = "" then
  (warning "No prolog system found - skipping some example theories"; ())
else
  if not (getenv "ISABELLE_SWIPL" = "") orelse
    #1 (Isabelle_System.bash_output "\"$ISABELLE_PREDICATE_COMPILE/lib/scripts/swipl_version\"") =
      "5.10.1"
  then
     (use_thys [
        "Code_Prolog_Examples",
        "Context_Free_Grammar_Example",
        "Hotel_Example_Prolog",
        "Lambda_Example",
        "List_Examples"];
      Unsynchronized.setmp quick_and_dirty true use_thys ["Reg_Exp_Example"])
  else (warning "Unsupported SWI-Prolog version - skipping some example theories"; ());
