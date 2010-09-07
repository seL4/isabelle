use_thys ["Predicate_Compile_Examples", "Predicate_Compile_Quickcheck_Examples", "Specialisation_Examples", "IMP_1", "IMP_2", "IMP_3", "IMP_4"];
if getenv "PROLOG_HOME" = "" then () else use_thys ["Code_Prolog_Examples", "Context_Free_Grammar_Example", "Hotel_Example", "Lambda_Example", "List_Examples"];
setmp_noncritical quick_and_dirty true use_thys ["Reg_Exp_Example"];
