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
@{typ"'b \<Rightarrow> 'b"}. The annotation @{text"(overloaded)"} tells Isabelle that
the definitions do intentionally define @{term[source]inverse} only at
instances of its declared type @{typ"'a \<Rightarrow> 'a"} --- this merely supresses
warnings to that effect.

However, there is nothing to prevent the user from forming terms such as
@{term[source]"inverse []"} and proving theorems as @{prop[source]"inverse []
= inverse []"}, although we never defined inverse on lists. We hasten to say
that there is nothing wrong with such terms and theorems. But it would be
nice if we could prevent their formation, simply because it is very likely
that the user did not mean to write what he did. Thus he had better not waste
his time pursuing it further. This requires the use of type classes.
*}
(*<*)end(*>*)
