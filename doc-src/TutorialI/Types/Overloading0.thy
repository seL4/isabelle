(*<*)theory Overloading0 = Main:(*>*)

text{* We start with a concept that is required for type classes but already
useful on its own: \emph{overloading}. Isabelle allows overloading: a
constant may have multiple definitions at non-overlapping types. *}

subsubsection{*An Initial Example*}

text{*
If we want to introduce the notion of an \emph{inverse} for arbitrary types we
give it a polymorphic type *}

consts inverse :: "'a \<Rightarrow> 'a"

text{*\noindent
and provide different definitions at different instances:
*}

defs (overloaded)
inverse_bool: "inverse(b::bool) \<equiv> \<not> b"
inverse_set:  "inverse(A::'a set) \<equiv> -A"
inverse_pair: "inverse(p) \<equiv> (inverse(fst p), inverse(snd p))"

text{*\noindent
Isabelle will not complain because the three definitions do not overlap: no
two of the three types @{typ bool}, @{typ"'a set"} and @{typ"'a \<times> 'b"} have a
common instance. What is more, the recursion in @{thm[source]inverse_pair} is
benign because the type of @{term[source]inverse} becomes smaller: on the
left it is @{typ"'a \<times> 'b \<Rightarrow> 'a \<times> 'b"} but on the right @{typ"'a \<Rightarrow> 'a"} and
@{typ"'b \<Rightarrow> 'b"}. The annotation @{text"("}\isacommand{overloaded}@{text")"} tells Isabelle that
the definitions do intentionally define @{term[source]inverse} only at
instances of its declared type @{typ"'a \<Rightarrow> 'a"} --- this merely suppresses
warnings to that effect.

However, there is nothing to prevent the user from forming terms such as
@{text"inverse []"} and proving theorems such as @{text"inverse []
= inverse []"} when inverse is not defined on lists.  Proving theorems about
unspecified constants does not endanger soundness, but it is pointless.
To prevent such terms from even being formed requires the use of type classes.
*}
(*<*)end(*>*)
