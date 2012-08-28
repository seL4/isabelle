(*<*)
theory Option2 imports Main begin
hide_const None Some
hide_type option
(*>*)

text{*\indexbold{*option (type)}\indexbold{*None (constant)}%
\indexbold{*Some (constant)}
Our final datatype is very simple but still eminently useful:
*}

datatype 'a option = None | Some 'a;

text{*\noindent
Frequently one needs to add a distinguished element to some existing type.
For example, type @{text"t option"} can model the result of a computation that
may either terminate with an error (represented by @{const None}) or return
some value @{term v} (represented by @{term"Some v"}).
Similarly, @{typ nat} extended with $\infty$ can be modeled by type
@{typ"nat option"}. In both cases one could define a new datatype with
customized constructors like @{term Error} and @{term Infinity},
but it is often simpler to use @{text option}. For an application see
\S\ref{sec:Trie}.
*}
(*<*)
(*
definition infplus :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"infplus x y \<equiv> case x of None \<Rightarrow> None
               | Some m \<Rightarrow> (case y of None \<Rightarrow> None | Some n \<Rightarrow> Some(m+n))"

*)
end
(*>*)
