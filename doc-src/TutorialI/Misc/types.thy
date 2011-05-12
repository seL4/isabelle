(*<*)theory "types" imports Main begin(*>*)
type_synonym number = nat
type_synonym gate = "bool \<Rightarrow> bool \<Rightarrow> bool"
type_synonym ('a, 'b) alist = "('a \<times> 'b) list"

text{*\noindent
Internally all synonyms are fully expanded.  As a consequence Isabelle's
output never contains synonyms.  Their main purpose is to improve the
readability of theories.  Synonyms can be used just like any other
type.
*}

subsection{*Constant Definitions*}

text{*\label{sec:ConstDefinitions}\indexbold{definitions}%
Nonrecursive definitions can be made with the \commdx{definition}
command, for example @{text nand} and @{text xor} gates
(based on type @{typ gate} above):
*}

definition nand :: gate where "nand A B \<equiv> \<not>(A \<and> B)"
definition xor  :: gate where "xor  A B \<equiv> A \<and> \<not>B \<or> \<not>A \<and> B"

text{*\noindent%
The symbol \indexboldpos{\isasymequiv}{$IsaEq} is a special form of equality
that must be used in constant definitions.
Pattern-matching is not allowed: each definition must be of
the form $f\,x@1\,\dots\,x@n~\isasymequiv~t$.
Section~\ref{sec:Simp-with-Defs} explains how definitions are used
in proofs. The default name of each definition is $f$@{text"_def"}, where
$f$ is the name of the defined constant.*}
(*<*)end(*>*)
