(*<*)
theory Option2 = Main:
hide const None Some
hide type option
(*>*)

text{*\indexbold{*option}\indexbold{*None}\indexbold{*Some}
Our final datatype is very simple but still eminently useful:
*}

datatype 'a option = None | Some 'a;

text{*\noindent
Frequently one needs to add a distinguished element to some existing type.
For example, type @{text"t option"} can model the result of a computation that
may either terminate with an error (represented by @{term None}) or return
some value @{term v} (represented by @{term"Some v"}).
Similarly, @{typ nat} extended with $\infty$ can be modeled by type
@{typ"nat option"}. In both cases one could define a new datatype with
customized constructors like @{term Error} and @{term Infinity},
but it is often simpler to use @{text option}. For an application see
\S\ref{sec:Trie}.
*}
(*<*)
(*
constdefs
 infplus :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option"
"infplus x y \<equiv> case x of None \<Rightarrow> None
               | Some m \<Rightarrow> (case y of None \<Rightarrow> None | Some n \<Rightarrow> Some(m+n))"

*)
end
(*>*)
