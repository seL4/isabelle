(*<*)theory "types" = Main:(*>*)
types number       = nat
      gate         = "bool \<Rightarrow> bool \<Rightarrow> bool"
      ('a,'b)alist = "('a \<times> 'b)list";

text{*\noindent\indexbold{*types}%
Internally all synonyms are fully expanded.  As a consequence Isabelle's
output never contains synonyms.  Their main purpose is to improve the
readability of theories.  Synonyms can be used just like any other
type:
*}

consts nand :: gate
       xor  :: gate;

subsection{*Constant definitions*}

text{*\label{sec:ConstDefinitions}\indexbold{definition}%
The above constants @{term"nand"} and @{term"xor"} are non-recursive and can
therefore be defined directly by
*}

defs nand_def: "nand A B \<equiv> \<not>(A \<and> B)"
     xor_def:  "xor A B  \<equiv> A \<and> \<not>B \<or> \<not>A \<and> B";

text{*\noindent%
where \isacommand{defs}\indexbold{*defs} is a keyword and
@{thm[source]nand_def} and @{thm[source]xor_def} are user-supplied names.
The symbol \indexboldpos{\isasymequiv}{$IsaEq} is a special form of equality
that must be used in constant definitions.
Declarations and definitions can also be merged
*}

constdefs nor :: gate
         "nor A B \<equiv> \<not>(A \<or> B)"
          xor2 :: gate
         "xor2 A B \<equiv> (A \<or> B) \<and> (\<not>A \<or> \<not>B)";

text{*\noindent\indexbold{*constdefs}%
in which case the default name of each definition is $f$@{text"_def"}, where
$f$ is the name of the defined constant.*}
(*<*)end(*>*)
