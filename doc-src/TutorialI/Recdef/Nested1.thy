(*<*)
theory Nested1 = Nested0:;
(*>*)

text{*\noindent
Although the definition of @{term trev} is quite natural, we will have
to overcome a minor difficulty in convincing Isabelle of its termination.
It is precisely this difficulty that is the \textit{raison d'\^etre} of
this subsection.

Defining @{term trev} by \isacommand{recdef} rather than \isacommand{primrec}
simplifies matters because we are now free to use the recursion equation
suggested at the end of \S\ref{sec:nested-datatype}:
*};

recdef trev "measure size"
 "trev (Var x)    = Var x"
 "trev (App f ts) = App f (rev(map trev ts))";

text{*\noindent
Remember that function @{term size} is defined for each \isacommand{datatype}.
However, the definition does not succeed. Isabelle complains about an
unproved termination condition
@{prop[display]"t : set ts --> size t < Suc (term_list_size ts)"}
where @{term set} returns the set of elements of a list
and @{text"term_list_size :: term list \<Rightarrow> nat"} is an auxiliary
function automatically defined by Isabelle
(while processing the declaration of @{text term}).  First we have to understand why the
recursive call of @{term trev} underneath @{term map} leads to the above
condition. The reason is that \isacommand{recdef} ``knows'' that @{term map}
will apply @{term trev} only to elements of @{term ts}. Thus the 
condition expresses that the size of the argument @{prop"t : set ts"} of any
recursive call of @{term trev} is strictly less than @{term"size(App f ts)"},
which equals @{term"Suc(term_list_size ts)"}.  We will now prove the termination condition and
continue with our definition.  Below we return to the question of how
\isacommand{recdef} ``knows'' about @{term map}.
*};

(*<*)
end;
(*>*)
