(*<*)
theory Translations = Main:
(*>*)
subsection{*Syntax Translations*}

text{*\label{sec:def-translations}
Isabelle offers an additional definition-like facility,
\textbf{syntax translations}\indexbold{syntax translation}.
They resemble makros: upon parsing, the defined concept is immediately
replaced by its definition, and this is reversed upon printing. For example,
the symbol @{text"\<noteq>"} is defined via a syntax translation:
*}

translations "x \<noteq> y" \<rightleftharpoons> "\<not>(x = y)"

text{*\indexbold{*translations}\indexbold{$IsaEqTrans@\isasymrightleftharpoons}
\noindent
Internally, @{text"\<noteq>"} never appears.

In addition to @{text"\<rightleftharpoons>"} there are
@{text"\<rightharpoonup>"}\indexbold{$IsaEqTrans1@\isasymrightharpoonup}
and @{text"\<leftharpoondown>"}\indexbold{$IsaEqTrans2@\isasymleftharpoondown}
for uni-directional translations (only upon
parsing respectively printing).  We do not want to cover the details of
translations at this point.  We haved mentioned the concept merely because it
crops up occasionally since a number of HOL's built-in constructs are defined
via translations.  *}

(*<*)
end
(*>*)
