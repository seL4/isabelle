(*<*)
theory Translations = Main:
(*>*)
subsection{*Syntax Translations*}

text{*\label{sec:def-translations}
\index{syntax translations|(}%
\index{translations@\isacommand {translations} (command)|(}
Isabelle offers an additional definitional facility,
\textbf{syntax translations}.
They resemble macros: upon parsing, the defined concept is immediately
replaced by its definition.  This effect is reversed upon printing.  For example,
the symbol @{text"\<noteq>"} is defined via a syntax translation:
*}

translations "x \<noteq> y" \<rightleftharpoons> "\<not>(x = y)"

text{*\index{$IsaEqTrans@\isasymrightleftharpoons}
\noindent
Internally, @{text"\<noteq>"} never appears.

In addition to @{text"\<rightleftharpoons>"} there are
@{text"\<rightharpoonup>"}\index{$IsaEqTrans1@\isasymrightharpoonup}
and @{text"\<leftharpoondown>"}\index{$IsaEqTrans2@\isasymleftharpoondown}
for uni-directional translations, which only affect
parsing or printing.  This tutorial will not cover the details of
translations.  We have mentioned the concept merely because it
crops up occasionally; a number of HOL's built-in constructs are defined
via translations.  Translations are preferable to definitions when the new 
concept is a trivial variation on an existing one.  For example, we
don't need to derive new theorems about @{text"\<noteq>"}, since existing theorems
about @{text"="} still apply.%
\index{syntax translations|)}%
\index{translations@\isacommand {translations} (command)|)}
*}

(*<*)
end
(*>*)
