(*  Title:      HOL/TPTP/TPTP_Parser_Test.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Some tests for the TPTP interface. Some of the tests rely on the Isabelle
environment variable TPTP_PROBLEMS_PATH, which should point to the
TPTP-vX.Y.Z/Problems directory.
*)

theory TPTP_Parser_Test
imports TPTP_Test TPTP_Parser_Example
begin

section "Problem-name parsing tests"
ML {*
local
  open TPTP_Syntax;
  open TPTP_Problem_Name;

  val name_tests =
    [("HWV041_4.p",
        Standard {suffix = Problem ((4, NONE), "p"), prob_form = TFF, prob_domain = "HWV", prob_number = 41}),
     ("LCL617^1.p",
        Standard {suffix = Problem ((1, NONE), "p"), prob_form = THF, prob_domain = "LCL", prob_number = 617}),
     ("LCL831-1.p",
        Standard {suffix = Problem ((1, NONE), "p"), prob_form = CNF, prob_domain = "LCL", prob_number = 831}),
     ("HWV045=1.p",
        Standard {suffix = Problem ((1, NONE), "p"), prob_form = TFF_with_arithmetic, prob_domain = "HWV", prob_number = 45}),
     ("LCL655+1.010.p",
        Standard {suffix = Problem ((1, SOME 10), "p"), prob_form = FOF, prob_domain = "LCL", prob_number = 655}),
     ("OTH123.p",
        Nonstandard "OTH123.p"),
     ("other",
        Nonstandard "other"),
     ("AAA000£0.axiom",
        Nonstandard "AAA000£0.axiom"),
     ("AAA000£0.p",
        Nonstandard "AAA000£0.p"),
     ("AAA000.0.p",
        Nonstandard "AAA000.0.p"),
     ("AAA000£0.what",
        Nonstandard "AAA000£0.what"),
     ("",
        Nonstandard "")];
in
  val _ = map (fn (str, res) =>
    @{assert}(TPTP_Problem_Name.parse_problem_name str = res)) name_tests
end
*}


section "Parser tests"

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
ML {*
  if test_all @{context} then
    (report @{context} "Testing parser";
     S timed_test parser_test @{context})
  else ()
*}

end