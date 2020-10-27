(*  Title:      HOL/TPTP/TPTP_Test.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Some test support for the TPTP interface. Some of the tests rely on the Isabelle
environment variable $TPTP, which should point to the TPTP-vX.Y.Z directory.
*)

theory TPTP_Test
imports TPTP_Parser
begin

ML \<open>
  val tptp_test_out = Attrib.setup_config_string @{binding "tptp_test_out"} (K "")
  val tptp_test_all = Attrib.setup_config_bool @{binding "tptp_test_all"} (K false)
  val tptp_test_timeout =
    Attrib.setup_config_int @{binding "tptp_test_timeout"} (K 5)
  fun test_all ctxt = Config.get ctxt tptp_test_all
  fun get_timeout ctxt = Config.get ctxt tptp_test_timeout
  fun S x y z = x z (y z)
\<close>

section "Parser tests"

ML \<open>
  fun payload_of (TPTP_Syntax.Annotated_Formula (_, _, _, _, fmla, _)) = fmla
  val payloads_of = map payload_of
\<close>


section "Source problems"
ML \<open>
  (*problem source*)
  val tptp_probs_dir =
    Path.explode "$TPTP/Problems"
    |> Path.expand;
\<close>


section "Supporting test functions"
ML \<open>
  fun report ctxt str =
    let
      val tptp_test_out = Config.get ctxt tptp_test_out
    in
      if tptp_test_out = "" then warning str
      else
        let
          val out_stream = TextIO.openAppend tptp_test_out
        in (TextIO.output (out_stream, str ^ "\n");
            TextIO.flushOut out_stream;
            TextIO.closeOut out_stream)
        end
    end

  fun test_fn ctxt f msg default_val file_name =
    let
      val _ = TPTP_Syntax.debug tracing (msg ^ " " ^ Path.print file_name)
    in
     (f file_name; ())
     (*otherwise report exceptions as warnings*)
     handle exn =>
       if Exn.is_interrupt exn then
         Exn.reraise exn
       else
         (report ctxt (msg ^ " test: file " ^ Path.print file_name ^
          " raised exception: " ^ Runtime.exn_message exn);
          default_val)
    end

  fun timed_test ctxt f test_files =
    let
      fun f' x = (f x; ())
      val time =
        Timing.timing (List.app f') test_files
        |> fst
      val duration =
        #elapsed time
        |> Time.toSeconds
        |> Real.fromLargeInt
      val average =
        (StringCvt.FIX (SOME 3),
         (duration / Real.fromInt (length test_files)))
        |-> Real.fmt
    in
      report ctxt ("Test timing: " ^ Timing.message time ^ "\n(about " ^ average ^
       "s per problem)")
    end
\<close>


ML \<open>
  fun situate file_name = tptp_probs_dir + Path.explode file_name;

  fun parser_test ctxt = (*FIXME argument order*)
    test_fn ctxt
     (fn file_name =>
        Path.implode file_name
        |> (fn file =>
             ((*report ctxt file; this is if you want the filename in the log*)
              TPTP_Parser.parse_file file)))
     "parser"
     ()

  fun parse_timed file =
    Timing.timing TPTP_Parser.parse_file (Path.implode file)
\<close>

end
