(*<*)
theory def_rewr = Main:;

(*>*)text{*\noindent Constant definitions (\S\ref{sec:ConstDefinitions}) can
be used as simplification rules, but by default they are not.  Hence the
simplifier does not expand them automatically, just as it should be:
definitions are introduced for the purpose of abbreviating complex
concepts. Of course we need to expand the definitions initially to derive
enough lemmas that characterize the concept sufficiently for us to forget the
original definition. For example, given
*}

constdefs exor :: "bool \\<Rightarrow> bool \\<Rightarrow> bool"
         "exor A B \\<equiv> (A \\<and> \\<not>B) \\<or> (\\<not>A \\<and> B)";

text{*\noindent
we may want to prove
*}

lemma "exor A (\\<not>A)";

txt{*\noindent
Typically, the opening move consists in \emph{unfolding} the definition(s), which we need to
get started, but nothing else:\indexbold{*unfold}\indexbold{definition!unfolding}
*}

apply(simp only:exor_def);

txt{*\noindent
In this particular case, the resulting goal
\begin{isabellepar}%
~1.~A~{\isasymand}~{\isasymnot}~{\isasymnot}~A~{\isasymor}~{\isasymnot}~A~{\isasymand}~{\isasymnot}~A%
\end{isabellepar}%
can be proved by simplification. Thus we could have proved the lemma outright
*}(*<*)oops;lemma "exor A (\\<not>A)";(*>*)
by(simp add: exor_def)

text{*\noindent
Of course we can also unfold definitions in the middle of a proof.

You should normally not turn a definition permanently into a simplification
rule because this defeats the whole purpose of an abbreviation.
*}
(*<*)end(*>*)
