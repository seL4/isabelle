theory README imports Main
begin

section \<open>TLA: Lamport's Temporal Logic of Actions\<close>

text \<open>
  TLA \<^url>\<open>http://www.research.digital.com/SRC/personal/Leslie_Lamport/tla/tla.html\<close>
  is a linear-time temporal logic introduced by Leslie Lamport in \<^emph>\<open>The
  Temporal Logic of Actions\<close> (ACM TOPLAS 16(3), 1994, 872-923). Unlike other
  temporal logics, both systems and properties are represented as logical
  formulas, and logical connectives such as implication, conjunction, and
  existential quantification represent structural relations such as
  refinement, parallel composition, and hiding. TLA has been applied to
  numerous case studies.

  This directory formalizes TLA in Isabelle/HOL, as follows:

    \<^item> \<^file>\<open>Intensional.thy\<close> prepares the ground by introducing basic syntax for
      "lifted", possible-world based logics.

    \<^item> \<^file>\<open>Stfun.thy\<close> and \<^file>\<open>Action.thy\<close> represent the state and transition
      level formulas of TLA, evaluated over single states and pairs of states.

    \<^item> \<^file>\<open>Init.thy\<close> introduces temporal logic and defines conversion functions
      from nontemporal to temporal formulas.

    \<^item> \<^file>\<open>TLA.thy\<close> axiomatizes proper temporal logic.


  Please consult the \<^emph>\<open>design notes\<close>
  \<^url>\<open>http://www.pst.informatik.uni-muenchen.de/~merz/isabelle/IsaTLADesign.ps\<close>
  for further information regarding the setup and use of this encoding of TLA.

  The theories are accompanied by a small number of examples:

    \<^item> \<^dir>\<open>Inc\<close>: Lamport's \<^emph>\<open>increment\<close> example, a standard TLA benchmark,
      illustrates an elementary TLA proof.

    \<^item> \<^dir>\<open>Buffer\<close>: a proof that two buffers in a row implement a single buffer,
      uses a simple refinement mapping.

    \<^item> \<^dir>\<open>Memory\<close>: a verification of (the untimed part of) Broy and Lamport's
    \<^emph>\<open>RPC-Memory\<close> case study, more fully explained in LNCS 1169 (the \<^emph>\<open>TLA
    solution\<close> is available separately from
    \<^url>\<open>http://www.pst.informatik.uni-muenchen.de/~merz/papers/RPCMemory.html\<close>).
\<close>

end
