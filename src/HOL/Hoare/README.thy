theory README imports Main
begin

section \<open>Hoare Logic for a Simple WHILE Language\<close>

subsection \<open>Language and logic\<close>

text \<open>
  This directory contains an implementation of Hoare logic for a simple WHILE
  language. The constructs are

    \<^item> \<^verbatim>\<open>SKIP\<close>
    \<^item> \<^verbatim>\<open>_ := _\<close>
    \<^item> \<^verbatim>\<open>_ ; _\<close>
    \<^item> \<^verbatim>\<open>IF _ THEN _ ELSE _ FI\<close>
    \<^item> \<^verbatim>\<open>WHILE _ INV {_} DO _ OD\<close>

  Note that each WHILE-loop must be annotated with an invariant.

  Within the context of theory \<^verbatim>\<open>Hoare\<close>, you can state goals of the form
    @{verbatim [display] \<open>VARS x y ... {P} prog {Q}\<close>}
  where \<^verbatim>\<open>prog\<close> is a program in the above language, \<^verbatim>\<open>P\<close> is the precondition,
  \<^verbatim>\<open>Q\<close> the postcondition, and \<^verbatim>\<open>x y ...\<close> is the list of all \<^emph>\<open>program
  variables\<close> in \<^verbatim>\<open>prog\<close>. The latter list must be nonempty and it must include
  all variables that occur on the left-hand side of an assignment in \<^verbatim>\<open>prog\<close>.
  Example:
    @{verbatim [display] \<open>VARS x {x = a} x := x+1 {x = a+1}\<close>}
  The (normal) variable \<^verbatim>\<open>a\<close> is merely used to record the initial value of
  \<^verbatim>\<open>x\<close> and is not a program variable. Pre/post conditions can be arbitrary HOL
  formulae mentioning both program variables and normal variables.

  The implementation hides reasoning in Hoare logic completely and provides a
  method \<^verbatim>\<open>vcg\<close> for transforming a goal in Hoare logic into an equivalent list
  of verification conditions in HOL: \<^theory_text>\<open>apply vcg\<close>

  If you want to simplify the resulting verification conditions at the same
  time: \<^theory_text>\<open>apply vcg_simp\<close> which, given the example goal above, solves it
  completely. For further examples see \<^file>\<open>Examples.thy\<close>.

  \<^bold>\<open>IMPORTANT:\<close>
  This is a logic of partial correctness. You can only prove that your program
  does the right thing \<^emph>\<open>if\<close> it terminates, but not \<^emph>\<open>that\<close> it terminates. A
  logic of total correctness is also provided and described below.
\<close>


subsection \<open>Total correctness\<close>

text \<open>
  To prove termination, each WHILE-loop must be annotated with a variant:

    \<^item> \<^verbatim>\<open>WHILE _ INV {_} VAR {_} DO _ OD\<close>

  A variant is an expression with type \<^verbatim>\<open>nat\<close>, which may use program variables
  and normal variables.

  A total-correctness goal has the form \<^verbatim>\<open>VARS x y ... [P] prog [Q]\<close> enclosing
  the pre- and postcondition in square brackets.

  Methods \<^verbatim>\<open>vcg_tc\<close> and \<^verbatim>\<open>vcg_tc_simp\<close> can be used to derive verification
  conditions.

  From a total-correctness proof, a function can be extracted which for every
  input satisfying the precondition returns an output satisfying the
  postcondition.
\<close>


subsection \<open>Notes on the implementation\<close>

text \<open>
  The implementation loosely follows

  Mike Gordon. \<^emph>\<open>Mechanizing Programming Logics in Higher Order Logic\<close>.
  University of Cambridge, Computer Laboratory, TR 145, 1988.

  published as

  Mike Gordon. \<^emph>\<open>Mechanizing Programming Logics in Higher Order Logic\<close>. In
  \<^emph>\<open>Current Trends in Hardware Verification and Automated Theorem Proving\<close>,
  edited by G. Birtwistle and P.A. Subrahmanyam, Springer-Verlag, 1989.

  The main differences: the state is modelled as a tuple as suggested in

  J. von Wright and J. Hekanaho and P. Luostarinen and T. Langbacka.
  \<^emph>\<open>Mechanizing Some Advanced Refinement Concepts\<close>. Formal Methods in System
  Design, 3, 1993, 49-81.

  and the embeding is deep, i.e. there is a concrete datatype of programs. The
  latter is not really necessary.
\<close>

end
