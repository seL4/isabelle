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
There is a special method for \emph{unfolding} definitions, which we need to
get started:\indexbold{*unfold}\indexbold{definition!unfolding}
*}

apply(unfold exor_def);

txt{*\noindent
It unfolds the given list of definitions (here merely one) in all subgoals:
\begin{isabellepar}%
~1.~A~{\isasymand}~{\isasymnot}~{\isasymnot}~A~{\isasymor}~{\isasymnot}~A~{\isasymand}~{\isasymnot}~A%
\end{isabellepar}%
The resulting goal can be proved by simplification.

In case we want to expand a definition in the middle of a proof, we can
simply include it locally:*}(*<*)oops;lemma "exor A (\\<not>A)";(*>*)
apply(simp add: exor_def);(*<*).(*>*)

text{*\noindent
In fact, this one command proves the above lemma directly.

You should normally not turn a definition permanently into a simplification
rule because this defeats the whole purpose of an abbreviation.
*}
(*<*)end(*>*)
