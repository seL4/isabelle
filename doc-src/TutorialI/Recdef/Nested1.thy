(*<*)
theory Nested1 = Nested0:
(*>*)
consts trev  :: "('a,'b)term => ('a,'b)term"

text{*\noindent
Although the definition of @{term"trev"} is quite natural, we will have
overcome a minor difficulty in convincing Isabelle of is termination.
It is precisely this difficulty that is the \textit{rasion d'\^etre} of
this subsection.

Defining @{term"trev"} by \isacommand{recdef} rather than \isacommand{primrec}
simplifies matters because we are now free to use the recursion equation
suggested at the end of \S\ref{sec:nested-datatype}:
*}
ML"Prim.Add_recdef_congs [map_cong]";
ML"Prim.print_recdef_congs(Context.the_context())";

recdef trev "measure size"
 "trev (Var x) = Var x"
 "trev (App f ts) = App f (rev(map trev ts))";
ML"Prim.congs []";
congs map_cong;
thm trev.simps;
(*<*)ML"Pretty.setmargin 60"(*>*)
text{*
FIXME: recdef should complain and generate unprovable termination condition!

The point is that the above termination condition is unprovable because it
ignores some crucial information: the recursive call of @{term"trev"} will
not involve arbitrary terms but only those in @{term"ts"}. This is expressed
by theorem \isa{map\_cong}:
\begin{quote}
@{thm[display]"map_cong"}
\end{quote}
*}

(*<*)
end
(*>*)


