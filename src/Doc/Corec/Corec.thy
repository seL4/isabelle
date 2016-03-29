(*  Title:      Doc/Corec/Corec.thy
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Andrei Popescu, Middlesex University
    Author:     Dmitriy Traytel, ETH Zuerich

Tutorial for nonprimitively corecursive definitions.
*)

theory Corec
imports
  "../Datatypes/Setup"
  "~~/src/HOL/Library/BNF_Corec"
begin

section \<open>Introduction
  \label{sec:introduction}\<close>

text \<open>
...
\cite{isabelle-datatypes}
\<close>


section \<open>Introductory Examples
  \label{sec:introductory-examples}\<close>


subsection \<open>Simple Corecursion
  \label{ssec:simple-corecursion}\<close>


subsection \<open>Nested Corecursion
  \label{ssec:nested-corecursion}\<close>


subsection \<open>Polymorphism
  \label{ssec:polymorphism}\<close>


subsection \<open>Coinduction
  \label{ssec:coinduction}\<close>


subsection \<open>Uniqueness Reasoning
  \label{ssec:uniqueness-reasoning}\<close>


section \<open>Command Syntax
  \label{sec:command-syntax}\<close>


subsection \<open>corec and corecursive
  \label{ssec:corec-and-corecursive}\<close>


subsection \<open>friend_of_corec
  \label{ssec:friend-of-corec}\<close>


subsection \<open>coinduction_upto
  \label{ssec:coinduction-upto}\<close>


section \<open>Generated Theorems
  \label{sec:generated-theorems}\<close>


subsection \<open>corec and corecursive
  \label{ssec:corec-and-corecursive}\<close>


subsection \<open>friend_of_corec
  \label{ssec:friend-of-corec}\<close>


subsection \<open>coinduction_upto
  \label{ssec:coinduction-upto}\<close>


section \<open>Proof Method
  \label{sec:proof-method}\<close>


subsection \<open>corec_unique
  \label{ssec:corec-unique}\<close>


section \<open>Known Bugs and Limitations
  \label{sec:known-bugs-and-limitations}\<close>

text \<open>
This section lists the known bugs and limitations of the corecursion package at
the time of this writing.

\begin{enumerate}
\setlength{\itemsep}{0pt}

\item
\emph{TODO.} TODO.

  * no mutual types
  * limitation on type of friend
  * unfinished tactics
  * polymorphism of corecUU_transfer

\end{enumerate}
\<close>

end
