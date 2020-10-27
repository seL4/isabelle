(*  Title:      HOL/TPTP/TPTP_Interpret_Test.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Some tests for the TPTP interface. Some of the tests rely on the Isabelle
environment variable $TPTP, which should point to the TPTP-vX.Y.Z directory.
*)

theory TPTP_Interpret_Test
imports TPTP_Test TPTP_Interpret
begin

section "Interpreter tests"

text "Interpret a problem."
ML \<open>
  val (time, ((type_map, const_map, fmlas), thy)) =
    Timing.timing
      (TPTP_Interpret.interpret_file
       false
       [Path.explode "$TPTP"]
       (tptp_probs_dir + Path.explode "LCL/LCL825-1.p")
       []
       [])
      @{theory}
\<close>


text "... and display nicely."
ML \<open>
  List.app (Pretty.writeln o (Syntax.pretty_term @{context}) o #3) fmlas;
\<close>

subsection "Multiple tests"

ML \<open>
  (*default timeout is 1 min*)
  fun interpret timeout file thy =
    Timeout.apply (Time.fromSeconds (if timeout = 0 then 60 else timeout))
     (TPTP_Interpret.interpret_file
       false
       [Path.explode "$TPTP"]
       file
       []
       []) thy

  fun interpret_timed timeout file thy =
    Timing.timing (interpret timeout file) thy

  fun interpretation_test timeout ctxt =
    test_fn ctxt
     (fn file => interpret timeout file (Proof_Context.theory_of ctxt))
     "interpreter"
     ()

  fun interpretation_tests timeout ctxt probs =
    List.app
     (interpretation_test timeout ctxt)
     (map situate probs)
\<close>

ML \<open>
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

  val timeouts =
    ["NUM/NUM923^4.p",
    "NUM/NUM926^4.p",
    "NUM/NUM925^4.p",
    "NUM/NUM924^4.p",
    "CSR/CSR153^3.p",
    "CSR/CSR151^3.p",
    "CSR/CSR148^3.p",
    "CSR/CSR120^3.p",
    "CSR/CSR150^3.p",
    "CSR/CSR119^3.p",
    "CSR/CSR149^3.p"]

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
     "SYN/SYN387^4.p",
     "SYN/SYN393^4.002.p",
     "SYN/SYN978^4.p",
     "SYN/SYN044^4.p",
     "SYN/SYN393^4.003.p",
     "SYN/SYN389^4.p",
     "ARI/ARI625=1.p",
     "SYO/SYO561_2.p",
     "SYO/SYO562_1.p",
     "SYN/SYN000_2.p"]
\<close>

ML \<open>
 interpretation_tests (get_timeout @{context}) @{context}
   (some_probs @ take_too_long @ timeouts @ more_probs)
\<close>

ML \<open>
  parse_timed (situate "NUM/NUM923^4.p");
  interpret_timed 0 (situate "NUM/NUM923^4.p") @{theory}
\<close>

ML \<open>
  fun interp_gain timeout thy file =
    let
      val t1 = (parse_timed file |> fst)
      val t2 = (interpret_timed timeout file thy |> fst)
        handle exn => (*FIXME*)
          if Exn.is_interrupt exn then Exn.reraise exn
          else
            (warning (" test: file " ^ Path.print file ^
             " raised exception: " ^ Runtime.exn_message exn);
             {gc = Time.zeroTime, cpu = Time.zeroTime, elapsed = Time.zeroTime})
      val to_real = Time.toReal
      val diff_elapsed =
        #elapsed t2 - #elapsed t1
        |> to_real
      val elapsed = to_real (#elapsed t2)
    in
      (Path.base file, diff_elapsed,
       diff_elapsed / elapsed,
       elapsed)
    end
\<close>


subsection "Test against whole TPTP"

text "Run interpretation over all problems. This works only for logics
 for which interpretation is defined (in TPTP_Parser/tptp_interpret.ML)."
ML \<open>
  if test_all @{context} then
    (report @{context} "Interpreting all problems";
     S timed_test (interpretation_test (get_timeout @{context})) @{context} (TPTP_Syntax.get_file_list tptp_probs_dir))
  else ()
\<close>

end
