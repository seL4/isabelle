(*  Title:      HOL/SMT_Examples/Boogie.thy
    Author:     Sascha Boehme, TU Muenchen
*)

section \<open>Proving Boogie-generated verification conditions\<close>

theory Boogie
imports Main
keywords "boogie_file" :: thy_load
begin

text \<open>
HOL-Boogie and its applications are described in:
\begin{itemize}

\item Sascha B"ohme, K. Rustan M. Leino, and Burkhart Wolff.
HOL-Boogie --- An Interactive Prover for the Boogie Program-Verifier.
Theorem Proving in Higher Order Logics, 2008.

\item Sascha B"ohme, Micha{\l} Moskal, Wolfram Schulte, and Burkhart Wolff.
HOL-Boogie --- An Interactive Prover-Backend for the Verifying C Compiler.
Journal of Automated Reasoning, 2009.

\end{itemize}
\<close>



section \<open>Built-in types and functions of Boogie\<close>

subsection \<open>Integer arithmetics\<close>

text \<open>
The operations \<open>div\<close> and \<open>mod\<close> are built-in in Boogie, but
without a particular semantics due to different interpretations in
programming languages. We assume that each application comes with a
proper axiomatization.
\<close>

axiomatization
  boogie_div :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "div'_b" 70) and
  boogie_mod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "mod'_b" 70)



section \<open>Setup\<close>

ML_file \<open>boogie.ML\<close>



section \<open>Verification condition proofs\<close>

declare [[smt_oracle = false]]
declare [[smt_read_only_certificates = true]]


external_file \<open>Boogie_Max.certs\<close>
declare [[smt_certificates = "Boogie_Max.certs"]]

boogie_file \<open>Boogie_Max.b2i\<close>


external_file \<open>Boogie_Dijkstra.certs\<close>
declare [[smt_certificates = "Boogie_Dijkstra.certs"]]

boogie_file \<open>Boogie_Dijkstra.b2i\<close>


declare [[z3_extensions = true]]
external_file \<open>VCC_Max.certs\<close>
declare [[smt_certificates = "VCC_Max.certs"]]

boogie_file \<open>VCC_Max.b2i\<close>

end
