(*<*)
theory Nested0 = Main:
(*>*)

text{*
In \S\ref{sec:nested-datatype} we defined the datatype of terms
*}

datatype ('a,'b)"term" = Var 'a | App 'b "('a,'b)term list"

text{*\noindent
and closed with the observation that the associated schema for the definition
of primitive recursive functions leads to overly verbose definitions. Moreover,
if you have worked exercise~\ref{ex:trev-trev} you will have noticed that
you needed to reprove many lemmas reminiscent of similar lemmas about
@{term"rev"}. We will now show you how \isacommand{recdef} can simplify
definitions and proofs about nested recursive datatypes. As an example we
choose exercise~\ref{ex:trev-trev}:
*}
(* consts trev  :: "('a,'b)term => ('a,'b)term" *)
(*<*)
end
(*>*)
