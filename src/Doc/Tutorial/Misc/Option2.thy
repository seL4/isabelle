(*<*)
theory Option2 imports Main begin
hide_const None Some
hide_type option
(*>*)

text\<open>\indexbold{*option (type)}\indexbold{*None (constant)}%
\indexbold{*Some (constant)}
Our final datatype is very simple but still eminently useful:
\<close>

datatype 'a option = None | Some 'a

text\<open>\noindent
Frequently one needs to add a distinguished element to some existing type.
For example, type \<open>t option\<close> can model the result of a computation that
may either terminate with an error (represented by \<^const>\<open>None\<close>) or return
some value \<^term>\<open>v\<close> (represented by \<^term>\<open>Some v\<close>).
Similarly, \<^typ>\<open>nat\<close> extended with $\infty$ can be modeled by type
\<^typ>\<open>nat option\<close>. In both cases one could define a new datatype with
customized constructors like \<^term>\<open>Error\<close> and \<^term>\<open>Infinity\<close>,
but it is often simpler to use \<open>option\<close>. For an application see
\S\ref{sec:Trie}.
\<close>
(*<*)
(*
definition infplus :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"infplus x y \<equiv> case x of None \<Rightarrow> None
               | Some m \<Rightarrow> (case y of None \<Rightarrow> None | Some n \<Rightarrow> Some(m+n))"

*)
end
(*>*)
