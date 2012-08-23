(*  Title:      HOL/Boogie/Boogie.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Integration of the Boogie program verifier *}

theory Boogie
imports Word
keywords
  "boogie_open" :: thy_load and
  "boogie_end" :: thy_decl and
  "boogie_vc" :: thy_goal and
  "boogie_status" :: diag
begin

text {*
HOL-Boogie and its applications are described in:
\begin{itemize}

\item Sascha B"ohme, K. Rustan M. Leino, and Burkhart Wolff.
HOL-Boogie --- An Interactive Prover for the Boogie Program-Verifier.
Theorem Proving in Higher Order Logics, 2008.

\item Sascha B"ohme, Micha{\l} Moskal, Wolfram Schulte, and Burkhart Wolff.
HOL-Boogie --- An Interactive Prover-Backend for the Verifying C Compiler.
Journal of Automated Reasoning, 2009.

\end{itemize}
*}



section {* Built-in types and functions of Boogie *}

subsection {* Labels *}

text {*
See "Generating error traces from verification-condition counterexamples"
by Leino e.a. (2004) for a description of Boogie's labelling mechanism and
semantics.
*}

definition assert_at :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "assert_at l P = P"
definition block_at :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "block_at l P = P"

lemmas labels = assert_at_def block_at_def


subsection {* Integer arithmetics *}

text {*
The operations @{text div} and @{text mod} are built-in in Boogie, but
without a particular semantics due to different interpretations in
programming languages. We assume that each application comes with a
proper axiomatization.
*}

axiomatization
  boogie_div :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "div'_b" 70) and
  boogie_mod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "mod'_b" 70)



section {* Boogie environment *}

text {*
Proving Boogie-generated verification conditions happens inside
a Boogie environment:

  boogie_open "b2i file with extension"
  boogie_vc "verification condition 1" ...
  boogie_vc "verification condition 2" ...
  boogie_vc "verification condition 3" ...
  boogie_end

See the Boogie examples for more details.
 
At most one Boogie environment should occur per theory,
otherwise unexpected effects may arise.
*}



section {* Setup *}

ML {*
structure Boogie_Axioms = Named_Thms
(
  val name = @{binding boogie}
  val description =
    "Boogie background axioms loaded along with Boogie verification conditions"
)
*}
setup Boogie_Axioms.setup

ML_file "Tools/boogie_vcs.ML"
ML_file "Tools/boogie_loader.ML"
ML_file "Tools/boogie_tactics.ML"
setup Boogie_Tactics.setup

ML_file "Tools/boogie_commands.ML"
setup Boogie_Commands.setup

end
