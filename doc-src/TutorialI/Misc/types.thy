(*<*)theory "types" = Main:(*>*)
types number       = nat
      gate         = "bool \<Rightarrow> bool \<Rightarrow> bool"
      ('a,'b)alist = "('a \<times> 'b)list"

text{*\noindent
Internally all synonyms are fully expanded.  As a consequence Isabelle's
output never contains synonyms.  Their main purpose is to improve the
readability of theories.  Synonyms can be used just like any other
type.  Here, we declare two constants of type \isa{gate}:
*}

consts nand :: gate
       xor  :: gate

subsection{*Constant Definitions*}

text{*\label{sec:ConstDefinitions}\indexbold{definitions}%
The constants @{term"nand"} and @{term"xor"} above are non-recursive and can 
be defined directly:
*}

defs nand_def: "nand A B \<equiv> \<not>(A \<and> B)"
     xor_def:  "xor A B  \<equiv> A \<and> \<not>B \<or> \<not>A \<and> B"

text{*\noindent%
Here \commdx{defs} is a keyword and
@{thm[source]nand_def} and @{thm[source]xor_def} are user-supplied names.
The symbol \indexboldpos{\isasymequiv}{$IsaEq} is a special form of equality
that must be used in constant definitions.
Pattern-matching is not allowed: each definition must be of
the form $f\,x@1\,\dots\,x@n~\isasymequiv~t$.
Section~\ref{sec:Simp-with-Defs} explains how definitions are used
in proofs.

A \commdx{constdefs} command combines the effects of \isacommand{consts} and 
\isacommand{defs}.  For instance, we can introduce @{term"nand"} and @{term"xor"} by a 
single command: 
*}

constdefs nor :: gate
         "nor A B \<equiv> \<not>(A \<or> B)"
          xor2 :: gate
         "xor2 A B \<equiv> (A \<or> B) \<and> (\<not>A \<or> \<not>B)"

text{*\noindent
The default name of each definition is $f$@{text"_def"}, where
$f$ is the name of the defined constant.*}
(*<*)end(*>*)
