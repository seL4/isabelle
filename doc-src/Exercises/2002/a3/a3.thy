(*<*)
theory a3 = Main:
(*>*)

subsection{* Compilation *}

text {* This exercise deals with the compiler example in section~3.3
of \cite{isabelle-tutorial}. The simple side effect free expressions
are extended with side effects.
\begin{enumerate}

\item Read sections 3.3 and 8.2 of \cite{isabelle-tutorial}.  Study
the section about @{text fun_upd} in theory @{text Fun} of HOL:
@{text"fun_upd f x y"}, written @{text"f(x:=y)"}, is @{text f}
updated at @{text x} with new value @{text y}.

\item Extend data type @{text "('a, 'v) expr"} with a new alternative
@{text "Assign x e"} that shall represent an assignment @{text "x =
e"} of the value of the expression @{text e} to the variable @{text x}.
The value of an assignment shall be the value of @{text e}.

\item Modify the evaluation function @{text value} such that it can
deal with assignments. Note that since the evaluation of an expression
may now change the environment, it no longer suffices to return only
the value from the evaluation of an expression.

Define a function @{text "se_free :: expr \<Rightarrow> bool"} that
identifies side effect free expressions. Show that @{text "se_free e"}
implies that evaluation of @{text e} does not change the environment.

\item Extend data type @{text "('a, 'v) instr"} with a new instruction
@{text "Store x"} that stores the topmost element on the stack in
address/variable @{text x}, without removing it from the stack.
Update the machine semantics @{text exec} accordingly. You will face
the same problem as in the extension of @{text value}.

\item Modify the compiler @{text comp} and its correctness proof to
accommodate the above changes.
\end{enumerate}
*}
(*<*)
end
(*>*)