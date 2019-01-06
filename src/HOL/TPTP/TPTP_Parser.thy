(*  Title:      HOL/TPTP/TPTP_Parser.thy
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Parser for TPTP formulas
*)

theory TPTP_Parser
imports Pure
begin

ML_file \<open>TPTP_Parser/ml_yacc_lib.ML\<close> (*generated from ML-Yacc's lib*)

ML_file \<open>TPTP_Parser/tptp_syntax.ML\<close>
ML_file \<open>TPTP_Parser/tptp_lexyacc.ML\<close> (*generated from tptp.lex and tptp.yacc*)
ML_file \<open>TPTP_Parser/tptp_parser.ML\<close>
ML_file \<open>TPTP_Parser/tptp_problem_name.ML\<close>
ML_file \<open>TPTP_Parser/tptp_proof.ML\<close>

text \<open>The TPTP parser was generated using ML-Yacc, and needs the
ML-Yacc library to operate.  This library is included with the parser,
and we include the next section in accordance with ML-Yacc's terms of
use.\<close>

section "ML-YACC COPYRIGHT NOTICE, LICENSE AND DISCLAIMER."
text \<open>
Copyright 1989, 1990 by David R. Tarditi Jr. and Andrew W. Appel

Permission to use, copy, modify, and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies and that
both the copyright notice and this permission notice and warranty
disclaimer appear in supporting documentation, and that the names of
David R. Tarditi Jr. and Andrew W. Appel not be used in advertising or
publicity pertaining to distribution of the software without specific,
written prior permission.

David R. Tarditi Jr. and Andrew W. Appel disclaim all warranties with
regard to this software, including all implied warranties of
merchantability and fitness.  In no event shall David R. Tarditi
Jr. and Andrew W. Appel be liable for any special, indirect or
consequential damages or any damages whatsoever resulting from loss of
use, data or profits, whether in an action of contract, negligence or
other tortious action, arising out of or in connection with the use or
performance of this software.
\<close>

end
