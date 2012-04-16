(*  Title:      HOL/ex/SAT_Examples.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005-2009
*)

header {* Examples for the 'sat' and 'satx' tactic *}

theory SAT_Examples imports Main
begin

(* ML {* sat.solver := "zchaff_with_proofs"; *} *)
(* ML {* sat.solver := "minisat_with_proofs"; *} *)
ML {* sat.trace_sat := true; *}
ML {* quick_and_dirty := true; *}

lemma "True"
by sat

lemma "a | ~a"
by sat

lemma "(a | b) & ~a \<Longrightarrow> b"
by sat

lemma "(a & b) | (c & d) \<Longrightarrow> (a & b) | (c & d)"
(*
apply (tactic {* cnf.cnf_rewrite_tac 1 *})
*)
by sat

lemma "(a & b) | (c & d) \<Longrightarrow> (a & b) | (c & d)"
(*
apply (tactic {* cnf.cnfx_rewrite_tac 1 *})
apply (erule exE | erule conjE)+
*)
by satx

lemma "(a & b | c & d) & (e & f | g & h) | (i & j | k & l) & (m & n | p & q)
  \<Longrightarrow> (a & b | c & d) & (e & f | g & h) | (i & j | k & l) & (m & n | p & q)"
(*
apply (tactic {* cnf.cnf_rewrite_tac 1 *})
*)
by sat

lemma "(a & b | c & d) & (e & f | g & h) | (i & j | k & l) & (m & n | p & q)
  \<Longrightarrow> (a & b | c & d) & (e & f | g & h) | (i & j | k & l) & (m & n | p & q)"
(*
apply (tactic {* cnf.cnfx_rewrite_tac 1 *})
apply (erule exE | erule conjE)+
*)
by satx

lemma "P=P=P=P=P=P=P=P=P=P"
by sat

lemma "P=P=P=P=P=P=P=P=P=P"
by satx

lemma  "!! a b c. [| a | b | c | d ;
e | f | (a & d) ;
~(a | (c & ~c)) | b ;
~(b & (x | ~x)) | c ;
~(d | False) | c ;
~(c | (~p & (p | (q & ~q)))) |] ==> False"
by sat

lemma  "!! a b c. [| a | b | c | d ;
e | f | (a & d) ;
~(a | (c & ~c)) | b ;
~(b & (x | ~x)) | c ;
~(d | False) | c ;
~(c | (~p & (p | (q & ~q)))) |] ==> False"
by satx

text {* eta-Equivalence *}

lemma "(ALL x. P x) | ~ All P"
by sat

ML {* sat.trace_sat := false; *}
ML {* quick_and_dirty := false; *}

method_setup rawsat = {*
  Scan.succeed (SIMPLE_METHOD' o sat.rawsat_tac)
*} "SAT solver (no preprocessing)"

(* Translated from TPTP problem library: PUZ015-2.006.dimacs *)

lemma assumes 1: "~x0"
and 2: "~x30"
and 3: "~x29"
and 4: "~x59"
and 5: "x1 | x31 | x0"
and 6: "x2 | x32 | x1"
and 7: "x3 | x33 | x2"
and 8: "x4 | x34 | x3"
and 9: "x35 | x4"
and 10: "x5 | x36 | x30"
and 11: "x6 | x37 | x5 | x31"
and 12: "x7 | x38 | x6 | x32"
and 13: "x8 | x39 | x7 | x33"
and 14: "x9 | x40 | x8 | x34"
and 15: "x41 | x9 | x35"
and 16: "x10 | x42 | x36"
and 17: "x11 | x43 | x10 | x37"
and 18: "x12 | x44 | x11 | x38"
and 19: "x13 | x45 | x12 | x39"
and 20: "x14 | x46 | x13 | x40"
and 21: "x47 | x14 | x41"
and 22: "x15 | x48 | x42"
and 23: "x16 | x49 | x15 | x43"
and 24: "x17 | x50 | x16 | x44"
and 25: "x18 | x51 | x17 | x45"
and 26: "x19 | x52 | x18 | x46"
and 27: "x53 | x19 | x47"
and 28: "x20 | x54 | x48"
and 29: "x21 | x55 | x20 | x49"
and 30: "x22 | x56 | x21 | x50"
and 31: "x23 | x57 | x22 | x51"
and 32: "x24 | x58 | x23 | x52"
and 33: "x59 | x24 | x53"
and 34: "x25 | x54"
and 35: "x26 | x25 | x55"
and 36: "x27 | x26 | x56"
and 37: "x28 | x27 | x57"
and 38: "x29 | x28 | x58"
and 39: "~x1 | ~x31"
and 40: "~x1 | ~x0"
and 41: "~x31 | ~x0"
and 42: "~x2 | ~x32"
and 43: "~x2 | ~x1"
and 44: "~x32 | ~x1"
and 45: "~x3 | ~x33"
and 46: "~x3 | ~x2"
and 47: "~x33 | ~x2"
and 48: "~x4 | ~x34"
and 49: "~x4 | ~x3"
and 50: "~x34 | ~x3"
and 51: "~x35 | ~x4"
and 52: "~x5 | ~x36"
and 53: "~x5 | ~x30"
and 54: "~x36 | ~x30"
and 55: "~x6 | ~x37"
and 56: "~x6 | ~x5"
and 57: "~x6 | ~x31"
and 58: "~x37 | ~x5"
and 59: "~x37 | ~x31"
and 60: "~x5 | ~x31"
and 61: "~x7 | ~x38"
and 62: "~x7 | ~x6"
and 63: "~x7 | ~x32"
and 64: "~x38 | ~x6"
and 65: "~x38 | ~x32"
and 66: "~x6 | ~x32"
and 67: "~x8 | ~x39"
and 68: "~x8 | ~x7"
and 69: "~x8 | ~x33"
and 70: "~x39 | ~x7"
and 71: "~x39 | ~x33"
and 72: "~x7 | ~x33"
and 73: "~x9 | ~x40"
and 74: "~x9 | ~x8"
and 75: "~x9 | ~x34"
and 76: "~x40 | ~x8"
and 77: "~x40 | ~x34"
and 78: "~x8 | ~x34"
and 79: "~x41 | ~x9"
and 80: "~x41 | ~x35"
and 81: "~x9 | ~x35"
and 82: "~x10 | ~x42"
and 83: "~x10 | ~x36"
and 84: "~x42 | ~x36"
and 85: "~x11 | ~x43"
and 86: "~x11 | ~x10"
and 87: "~x11 | ~x37"
and 88: "~x43 | ~x10"
and 89: "~x43 | ~x37"
and 90: "~x10 | ~x37"
and 91: "~x12 | ~x44"
and 92: "~x12 | ~x11"
and 93: "~x12 | ~x38"
and 94: "~x44 | ~x11"
and 95: "~x44 | ~x38"
and 96: "~x11 | ~x38"
and 97: "~x13 | ~x45"
and 98: "~x13 | ~x12"
and 99: "~x13 | ~x39"
and 100: "~x45 | ~x12"
and 101: "~x45 | ~x39"
and 102: "~x12 | ~x39"
and 103: "~x14 | ~x46"
and 104: "~x14 | ~x13"
and 105: "~x14 | ~x40"
and 106: "~x46 | ~x13"
and 107: "~x46 | ~x40"
and 108: "~x13 | ~x40"
and 109: "~x47 | ~x14"
and 110: "~x47 | ~x41"
and 111: "~x14 | ~x41"
and 112: "~x15 | ~x48"
and 113: "~x15 | ~x42"
and 114: "~x48 | ~x42"
and 115: "~x16 | ~x49"
and 116: "~x16 | ~x15"
and 117: "~x16 | ~x43"
and 118: "~x49 | ~x15"
and 119: "~x49 | ~x43"
and 120: "~x15 | ~x43"
and 121: "~x17 | ~x50"
and 122: "~x17 | ~x16"
and 123: "~x17 | ~x44"
and 124: "~x50 | ~x16"
and 125: "~x50 | ~x44"
and 126: "~x16 | ~x44"
and 127: "~x18 | ~x51"
and 128: "~x18 | ~x17"
and 129: "~x18 | ~x45"
and 130: "~x51 | ~x17"
and 131: "~x51 | ~x45"
and 132: "~x17 | ~x45"
and 133: "~x19 | ~x52"
and 134: "~x19 | ~x18"
and 135: "~x19 | ~x46"
and 136: "~x52 | ~x18"
and 137: "~x52 | ~x46"
and 138: "~x18 | ~x46"
and 139: "~x53 | ~x19"
and 140: "~x53 | ~x47"
and 141: "~x19 | ~x47"
and 142: "~x20 | ~x54"
and 143: "~x20 | ~x48"
and 144: "~x54 | ~x48"
and 145: "~x21 | ~x55"
and 146: "~x21 | ~x20"
and 147: "~x21 | ~x49"
and 148: "~x55 | ~x20"
and 149: "~x55 | ~x49"
and 150: "~x20 | ~x49"
and 151: "~x22 | ~x56"
and 152: "~x22 | ~x21"
and 153: "~x22 | ~x50"
and 154: "~x56 | ~x21"
and 155: "~x56 | ~x50"
and 156: "~x21 | ~x50"
and 157: "~x23 | ~x57"
and 158: "~x23 | ~x22"
and 159: "~x23 | ~x51"
and 160: "~x57 | ~x22"
and 161: "~x57 | ~x51"
and 162: "~x22 | ~x51"
and 163: "~x24 | ~x58"
and 164: "~x24 | ~x23"
and 165: "~x24 | ~x52"
and 166: "~x58 | ~x23"
and 167: "~x58 | ~x52"
and 168: "~x23 | ~x52"
and 169: "~x59 | ~x24"
and 170: "~x59 | ~x53"
and 171: "~x24 | ~x53"
and 172: "~x25 | ~x54"
and 173: "~x26 | ~x25"
and 174: "~x26 | ~x55"
and 175: "~x25 | ~x55"
and 176: "~x27 | ~x26"
and 177: "~x27 | ~x56"
and 178: "~x26 | ~x56"
and 179: "~x28 | ~x27"
and 180: "~x28 | ~x57"
and 181: "~x27 | ~x57"
and 182: "~x29 | ~x28"
and 183: "~x29 | ~x58"
and 184: "~x28 | ~x58"
shows "False"
using assms
(*
by sat
*)
by rawsat  -- {* this is without CNF conversion *}

(* Translated from TPTP problem library: MSC007-1.008.dimacs *)

lemma assumes 1: "x0 | x1 | x2 | x3 | x4 | x5 | x6"
and 2: "x7 | x8 | x9 | x10 | x11 | x12 | x13"
and 3: "x14 | x15 | x16 | x17 | x18 | x19 | x20"
and 4: "x21 | x22 | x23 | x24 | x25 | x26 | x27"
and 5: "x28 | x29 | x30 | x31 | x32 | x33 | x34"
and 6: "x35 | x36 | x37 | x38 | x39 | x40 | x41"
and 7: "x42 | x43 | x44 | x45 | x46 | x47 | x48"
and 8: "x49 | x50 | x51 | x52 | x53 | x54 | x55"
and 9: "~x0 | ~x7"
and 10: "~x0 | ~x14"
and 11: "~x0 | ~x21"
and 12: "~x0 | ~x28"
and 13: "~x0 | ~x35"
and 14: "~x0 | ~x42"
and 15: "~x0 | ~x49"
and 16: "~x7 | ~x14"
and 17: "~x7 | ~x21"
and 18: "~x7 | ~x28"
and 19: "~x7 | ~x35"
and 20: "~x7 | ~x42"
and 21: "~x7 | ~x49"
and 22: "~x14 | ~x21"
and 23: "~x14 | ~x28"
and 24: "~x14 | ~x35"
and 25: "~x14 | ~x42"
and 26: "~x14 | ~x49"
and 27: "~x21 | ~x28"
and 28: "~x21 | ~x35"
and 29: "~x21 | ~x42"
and 30: "~x21 | ~x49"
and 31: "~x28 | ~x35"
and 32: "~x28 | ~x42"
and 33: "~x28 | ~x49"
and 34: "~x35 | ~x42"
and 35: "~x35 | ~x49"
and 36: "~x42 | ~x49"
and 37: "~x1 | ~x8"
and 38: "~x1 | ~x15"
and 39: "~x1 | ~x22"
and 40: "~x1 | ~x29"
and 41: "~x1 | ~x36"
and 42: "~x1 | ~x43"
and 43: "~x1 | ~x50"
and 44: "~x8 | ~x15"
and 45: "~x8 | ~x22"
and 46: "~x8 | ~x29"
and 47: "~x8 | ~x36"
and 48: "~x8 | ~x43"
and 49: "~x8 | ~x50"
and 50: "~x15 | ~x22"
and 51: "~x15 | ~x29"
and 52: "~x15 | ~x36"
and 53: "~x15 | ~x43"
and 54: "~x15 | ~x50"
and 55: "~x22 | ~x29"
and 56: "~x22 | ~x36"
and 57: "~x22 | ~x43"
and 58: "~x22 | ~x50"
and 59: "~x29 | ~x36"
and 60: "~x29 | ~x43"
and 61: "~x29 | ~x50"
and 62: "~x36 | ~x43"
and 63: "~x36 | ~x50"
and 64: "~x43 | ~x50"
and 65: "~x2 | ~x9"
and 66: "~x2 | ~x16"
and 67: "~x2 | ~x23"
and 68: "~x2 | ~x30"
and 69: "~x2 | ~x37"
and 70: "~x2 | ~x44"
and 71: "~x2 | ~x51"
and 72: "~x9 | ~x16"
and 73: "~x9 | ~x23"
and 74: "~x9 | ~x30"
and 75: "~x9 | ~x37"
and 76: "~x9 | ~x44"
and 77: "~x9 | ~x51"
and 78: "~x16 | ~x23"
and 79: "~x16 | ~x30"
and 80: "~x16 | ~x37"
and 81: "~x16 | ~x44"
and 82: "~x16 | ~x51"
and 83: "~x23 | ~x30"
and 84: "~x23 | ~x37"
and 85: "~x23 | ~x44"
and 86: "~x23 | ~x51"
and 87: "~x30 | ~x37"
and 88: "~x30 | ~x44"
and 89: "~x30 | ~x51"
and 90: "~x37 | ~x44"
and 91: "~x37 | ~x51"
and 92: "~x44 | ~x51"
and 93: "~x3 | ~x10"
and 94: "~x3 | ~x17"
and 95: "~x3 | ~x24"
and 96: "~x3 | ~x31"
and 97: "~x3 | ~x38"
and 98: "~x3 | ~x45"
and 99: "~x3 | ~x52"
and 100: "~x10 | ~x17"
and 101: "~x10 | ~x24"
and 102: "~x10 | ~x31"
and 103: "~x10 | ~x38"
and 104: "~x10 | ~x45"
and 105: "~x10 | ~x52"
and 106: "~x17 | ~x24"
and 107: "~x17 | ~x31"
and 108: "~x17 | ~x38"
and 109: "~x17 | ~x45"
and 110: "~x17 | ~x52"
and 111: "~x24 | ~x31"
and 112: "~x24 | ~x38"
and 113: "~x24 | ~x45"
and 114: "~x24 | ~x52"
and 115: "~x31 | ~x38"
and 116: "~x31 | ~x45"
and 117: "~x31 | ~x52"
and 118: "~x38 | ~x45"
and 119: "~x38 | ~x52"
and 120: "~x45 | ~x52"
and 121: "~x4 | ~x11"
and 122: "~x4 | ~x18"
and 123: "~x4 | ~x25"
and 124: "~x4 | ~x32"
and 125: "~x4 | ~x39"
and 126: "~x4 | ~x46"
and 127: "~x4 | ~x53"
and 128: "~x11 | ~x18"
and 129: "~x11 | ~x25"
and 130: "~x11 | ~x32"
and 131: "~x11 | ~x39"
and 132: "~x11 | ~x46"
and 133: "~x11 | ~x53"
and 134: "~x18 | ~x25"
and 135: "~x18 | ~x32"
and 136: "~x18 | ~x39"
and 137: "~x18 | ~x46"
and 138: "~x18 | ~x53"
and 139: "~x25 | ~x32"
and 140: "~x25 | ~x39"
and 141: "~x25 | ~x46"
and 142: "~x25 | ~x53"
and 143: "~x32 | ~x39"
and 144: "~x32 | ~x46"
and 145: "~x32 | ~x53"
and 146: "~x39 | ~x46"
and 147: "~x39 | ~x53"
and 148: "~x46 | ~x53"
and 149: "~x5 | ~x12"
and 150: "~x5 | ~x19"
and 151: "~x5 | ~x26"
and 152: "~x5 | ~x33"
and 153: "~x5 | ~x40"
and 154: "~x5 | ~x47"
and 155: "~x5 | ~x54"
and 156: "~x12 | ~x19"
and 157: "~x12 | ~x26"
and 158: "~x12 | ~x33"
and 159: "~x12 | ~x40"
and 160: "~x12 | ~x47"
and 161: "~x12 | ~x54"
and 162: "~x19 | ~x26"
and 163: "~x19 | ~x33"
and 164: "~x19 | ~x40"
and 165: "~x19 | ~x47"
and 166: "~x19 | ~x54"
and 167: "~x26 | ~x33"
and 168: "~x26 | ~x40"
and 169: "~x26 | ~x47"
and 170: "~x26 | ~x54"
and 171: "~x33 | ~x40"
and 172: "~x33 | ~x47"
and 173: "~x33 | ~x54"
and 174: "~x40 | ~x47"
and 175: "~x40 | ~x54"
and 176: "~x47 | ~x54"
and 177: "~x6 | ~x13"
and 178: "~x6 | ~x20"
and 179: "~x6 | ~x27"
and 180: "~x6 | ~x34"
and 181: "~x6 | ~x41"
and 182: "~x6 | ~x48"
and 183: "~x6 | ~x55"
and 184: "~x13 | ~x20"
and 185: "~x13 | ~x27"
and 186: "~x13 | ~x34"
and 187: "~x13 | ~x41"
and 188: "~x13 | ~x48"
and 189: "~x13 | ~x55"
and 190: "~x20 | ~x27"
and 191: "~x20 | ~x34"
and 192: "~x20 | ~x41"
and 193: "~x20 | ~x48"
and 194: "~x20 | ~x55"
and 195: "~x27 | ~x34"
and 196: "~x27 | ~x41"
and 197: "~x27 | ~x48"
and 198: "~x27 | ~x55"
and 199: "~x34 | ~x41"
and 200: "~x34 | ~x48"
and 201: "~x34 | ~x55"
and 202: "~x41 | ~x48"
and 203: "~x41 | ~x55"
and 204: "~x48 | ~x55"
shows "False"
using assms
(*
by sat
*)
by rawsat  -- {* this is without CNF conversion *}

(* Old sequent clause representation ("[c_i, p, ~q, \<dots>] \<turnstile> False"):
   sat, zchaff_with_proofs: 8705 resolution steps in
                            +++ User 1.154  All 1.189 secs
   sat, minisat_with_proofs: 40790 resolution steps in
                             +++ User 3.762  All 3.806 secs

   rawsat, zchaff_with_proofs: 8705 resolution steps in
                               +++ User 0.731  All 0.751 secs
   rawsat, minisat_with_proofs: 40790 resolution steps in
                                +++ User 3.514  All 3.550 secs

   CNF clause representation ("[c_1 && \<dots> && c_n, p, ~q, \<dots>] \<turnstile> False"):
   rawsat, zchaff_with_proofs: 8705 resolution steps in
                               +++ User 0.653  All 0.670 secs
   rawsat, minisat_with_proofs: 40790 resolution steps in
                                +++ User 1.860  All 1.886 secs

   (as of 2006-08-30, on a 2.5 GHz Pentium 4)
*)

text {*
Function {\tt benchmark} takes the name of an existing DIMACS CNF
file, parses this file, passes the problem to a SAT solver, and checks
the proof of unsatisfiability found by the solver.  The function
measures the time spent on proof reconstruction (at least real time
also includes time spent in the SAT solver), and additionally returns
the number of resolution steps in the proof.
*}

(* ML {*
sat.solver := "zchaff_with_proofs";
sat.trace_sat := false;
quick_and_dirty := false;
*} *)

ML {*
fun benchmark dimacsfile =
let
  val prop_fm = SatSolver.read_dimacs_cnf_file (Path.explode dimacsfile)
  fun and_to_list (Prop_Logic.And (fm1, fm2)) acc = and_to_list fm2 (fm1 :: acc)
    | and_to_list fm acc = rev (fm :: acc)
  val clauses = and_to_list prop_fm []
  val terms = map (HOLogic.mk_Trueprop o Prop_Logic.term_of_prop_formula) clauses
  val cterms = map (Thm.cterm_of @{theory}) terms
  val start = Timing.start ()
  val thm = sat.rawsat_thm @{context} cterms
in
  (Timing.result start, ! sat.counter)
end;
*}

end
