(*  Title:      HOL/TPTP/TPTP_Parser_Test.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Some tests for the TPTP interface. Some of the tests rely on the Isabelle
environment variable TPTP_PROBLEMS_PATH, which should point to the
TPTP-vX.Y.Z/Problems directory.
*)

theory TPTP_Parser_Test
imports TPTP_Parser
begin

ML {*
  val warning_out = Attrib.setup_config_string @{binding "warning_out"} (K "")
  fun S x y z = x z (y z)
*}

section "Parser tests"

ML {*
  fun payload_of (TPTP_Syntax.Annotated_Formula (_, _, _, _, fmla, _)) = fmla
  val payloads_of = map payload_of
*}
ML {*
  TPTP_Parser.parse_expression "" "fof(dt_k4_waybel34, axiom, ~ v3).";
  TPTP_Parser.parse_expression "" "thf(dt_k4_waybel34, axiom, ~ ($true | $false)).";
  TPTP_Parser.parse_expression ""
   "thf(dt_k4_waybel34, axiom, ~ (! [X : $o, Y : ($o > $o)] : ( (X | (Y = Y))))).";
  TPTP_Parser.parse_expression "" "tff(dt_k4_waybel34, axiom, ~ ($true)).";
  payloads_of it;
*}
ML {*
  TPTP_Parser.parse_expression "" "thf(bla, type, x : $o).";
  TPTP_Parser.parse_expression ""
   "fof(dt_k4_waybel34, axiom, ~ v3_struct_0(k4_waybel34(A))).";
  TPTP_Parser.parse_expression ""
   "fof(dt_k4_waybel34, axiom, (! [A] : (v1_xboole_0(A) => ( ~ v3_struct_0(k4_waybel34(A)))))).";
*}
ML {*
  TPTP_Parser.parse_expression ""
  ("fof(dt_k4_waybel34,axiom,(" ^
    "! [A] :" ^
      "( ~ v1_xboole_0(A)" ^
     "=> ( ~ v3_struct_0(k4_waybel34(A))" ^
        "& v2_altcat_1(k4_waybel34(A))" ^
        "& v6_altcat_1(k4_waybel34(A))" ^
        "& v11_altcat_1(k4_waybel34(A))" ^
        "& v12_altcat_1(k4_waybel34(A))" ^
        "& v2_yellow21(k4_waybel34(A))" ^
        "& l2_altcat_1(k4_waybel34(A)) ) ) )).")
*}

ML {*
open TPTP_Syntax;
@{assert}
  ((TPTP_Parser.parse_expression ""
   "thf(x,axiom,^ [X] : ^ [Y] : f @ g)."
   |> payloads_of |> hd)
  =
  Fmla (Interpreted_ExtraLogic Apply,
   [Quant (Lambda, [("X", NONE)],
      Quant (Lambda, [("Y", NONE)],
       Atom (THF_Atom_term (Term_Func (Uninterpreted "f", []))))),
    Atom (THF_Atom_term (Term_Func (Uninterpreted "g", [])))])
)
*}


section "Source problems"
ML {*
  (*problem source*)
  val thf_probs_dir =
    Path.explode "$TPTP_PROBLEMS_PATH"
    |> Path.expand;

  (*list of files to under test*)
  val files = TPTP_Syntax.get_file_list thf_probs_dir;

(*  (*test problem-name parsing and mangling*)
  val problem_names =
    map (Path.base #>
         Path.implode #>
         TPTP_Problem_Name.parse_problem_name #>
         TPTP_Problem_Name.mangle_problem_name)
        files*)
*}


section "Supporting test functions"
ML {*
  fun report ctxt str =
    let
      val warning_out = Config.get ctxt warning_out
    in
      if warning_out = "" then warning str
      else
        let
          val out_stream = TextIO.openAppend warning_out
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
         reraise exn
       else
         (report ctxt (msg ^ " test: file " ^ Path.print file_name ^
          " raised exception: " ^ ML_Compiler.exn_message exn);
          default_val)
    end

  fun timed_test ctxt f =
    let
      fun f' x = (f x; ())
      val time =
        Timing.timing (List.app f') files
        |> fst
      val duration =
        #elapsed time
        |> Time.toSeconds
        |> Real.fromLargeInt
      val average =
        (StringCvt.FIX (SOME 3),
         (duration / Real.fromInt (length files)))
        |-> Real.fmt
    in
      report ctxt ("Test timing: " ^ Timing.message time ^ "\n(about " ^ average ^
       "s per problem)")
    end
*}


subsection "More parser tests"
ML {*
  fun situate file_name = Path.append thf_probs_dir (Path.explode file_name);
  fun parser_test ctxt = (*FIXME argument order*)
    test_fn ctxt
     (fn file_name =>
        Path.implode file_name
        |> (fn file =>
             ((*report ctxt file; this is if you want the filename in the log*)
              TPTP_Parser.parse_file file)))
     "parser"
     ()
*}

declare [[warning_out = ""]]

text "Parse a specific problem."
ML {*
  map TPTP_Parser.parse_file
   ["$TPTP_PROBLEMS_PATH/FLD/FLD051-1.p",
    "$TPTP_PROBLEMS_PATH/FLD/FLD005-3.p",
    "$TPTP_PROBLEMS_PATH/SWV/SWV567-1.015.p",
    "$TPTP_PROBLEMS_PATH/SWV/SWV546-1.010.p"]
*}
ML {*
  parser_test @{context} (situate "DAT/DAT001=1.p");
  parser_test @{context} (situate "ALG/ALG001^5.p");
  parser_test @{context} (situate "NUM/NUM021^1.p");
  parser_test @{context} (situate "SYN/SYN000^1.p")
*}

text "Run the parser over all problems."
ML {*report @{context} "Testing parser"*}
ML {*
(*  val _ = S timed_test parser_test @{context}*)
*}


subsection "Interpretation"

text "Interpret a problem."
ML {*
  val (time, ((type_map, const_map, fmlas), thy)) =
    Timing.timing
    (TPTP_Interpret.interpret_file
     false
     (Path.dir thf_probs_dir)
    (Path.append thf_probs_dir (Path.explode "LCL/LCL825-1.p"))
     []
     [])
    @{theory}

  (*also tried
     "ALG/ALG001^5.p"
     "COM/COM003+2.p"
     "COM/COM003-1.p"
     "COM/COM024^5.p"
     "DAT/DAT017=1.p"
     "NUM/NUM021^1.p"
     "NUM/NUM858=1.p"
     "SYN/SYN000^2.p"*)

 (*These take too long
    "NLP/NLP562+1.p"
    "SWV/SWV546-1.010.p"
    "SWV/SWV567-1.015.p"
    "LCL/LCL680+1.020.p"*)
*}

text "... and display nicely."
ML {*
  List.app (Pretty.writeln o (Syntax.pretty_term @{context}) o #4) fmlas
*}
ML {*
  (*Don't use TPTP_Syntax.string_of_tptp_formula, it's just for testing*)
  List.app (writeln o TPTP_Syntax.string_of_tptp_formula o #3) fmlas
*}


text "Run interpretation over all problems. This works only for logics
 for which interpretation is defined (in TPTP_Parser/tptp_interpret.ML)."
ML {*
  report @{context} "Interpreting all problems.";
  fun interpretation_test timeout ctxt =
    test_fn ctxt
     (fn file =>
      (writeln (Path.implode file);
       TimeLimit.timeLimit (Time.fromSeconds timeout)
       (TPTP_Interpret.interpret_file
         false
         (Path.dir thf_probs_dir)
         file
         []
         [])
         @{theory}))
     "interpreter"
     ()
  val _ = S timed_test (interpretation_test 5) @{context}
*}

end