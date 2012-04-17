(*  Title:      HOL/TPTP/TPTP_Interpret_Test.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Some tests for the TPTP interface. Some of the tests rely on the Isabelle
environment variable TPTP_PROBLEMS_PATH, which should point to the
TPTP-vX.Y.Z/Problems directory.
*)

theory TPTP_Interpret_Test
imports TPTP_Test TPTP_Interpret
begin

section "Interpreter tests"

text "Interpret a problem."
ML {*
  val (time, ((type_map, const_map, fmlas), thy)) =
    Timing.timing
      (TPTP_Interpret.interpret_file
       false
       (Path.dir tptp_probs_dir)
      (Path.append tptp_probs_dir (Path.explode "LCL/LCL825-1.p"))
       []
       [])
      @{theory}
*}

text "... and display nicely."
ML {*
  List.app (Pretty.writeln o (Syntax.pretty_term @{context}) o #4) fmlas
*}
ML {*
  (*Don't use TPTP_Syntax.string_of_tptp_formula, it's just for testing*)
  List.app (writeln o TPTP_Syntax.string_of_tptp_formula o #3) fmlas
*}


subsection "Multiple tests"

ML {*
  fun interpretation_test timeout ctxt =
    test_fn ctxt
     (fn file =>
       TimeLimit.timeLimit (Time.fromSeconds timeout)
        (TPTP_Interpret.interpret_file
          false
          (Path.dir tptp_probs_dir)
          file
          []
          [])
          @{theory})
     "interpreter"
     ()

  fun interpretation_tests timeout ctxt probs =
    List.app
     (interpretation_test timeout ctxt)
     (List.map situate probs)
*}

ML {*
  val some_probs =
    ["LCL/LCL825-1.p",
     "ALG/ALG001^5.p",
     "COM/COM003+2.p",
     "COM/COM003-1.p",
     "COM/COM024^5.p",
     "DAT/DAT017=1.p",
     "NUM/NUM021^1.p",
     "NUM/NUM858=1.p",
     "SYN/SYN000^2.p"]

  val take_too_long =
    ["NLP/NLP562+1.p",
     "SWV/SWV546-1.010.p",
     "SWV/SWV567-1.015.p",
     "LCL/LCL680+1.020.p"]

  val more_probs =
    ["GEG/GEG014^1.p",
     "GEG/GEG009^1.p",
     "GEG/GEG004^1.p",
     "GEG/GEG007^1.p",
     "GEG/GEG016^1.p",
     "GEG/GEG024=1.p",
     "GEG/GEG010^1.p",
     "GEG/GEG003^1.p",
     "GEG/GEG018^1.p",
     "SYN/SYN045^4.p",
     "SYN/SYN001^4.001.p",
     "SYN/SYN000^2.p",
     "SYN/SYN387^4.p",
     "SYN/SYN393^4.002.p",
     "SYN/SYN978^4.p",
     "SYN/SYN044^4.p",
     "SYN/SYN393^4.003.p",
     "SYN/SYN389^4.p"]
*}

ML {*
 interpretation_tests 5 @{context}
   (some_probs @ take_too_long @ more_probs)
*}


subsection "Test against whole TPTP"

text "Run interpretation over all problems. This works only for logics
 for which interpretation is defined (in TPTP_Parser/tptp_interpret.ML)."
ML {*
  report @{context} "Interpreting all problems.";
  fun interpretation_test timeout ctxt =
    test_fn ctxt
     (fn file =>
       TimeLimit.timeLimit (Time.fromSeconds timeout)
        (TPTP_Interpret.interpret_file
          false
          (Path.dir tptp_probs_dir)
          file
          []
          [])
          @{theory})
     "interpreter"
     ()
  (*val _ = S timed_test (interpretation_test 5) @{context}*)
*}

end