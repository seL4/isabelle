(*<*)
theory a6 = Main:
(*>*)
subsection {* The towers of Hanoi *}

text{*
In section \ref{psv2000hanoi} we introduced the towers of Hanoi and
defined a function @{term moves} to generate the moves to solve the
puzzle.  Now it is time to show that @{term moves} is correct. This
means that
\begin{itemize}
\item when executing the list of moves, the result is indeed the
intended one, i.e.\ all disks are moved from one peg to another, and
\item all of the moves are legal, i.e.\ never place a larger disk
on top of a smaller one.
\end{itemize}
Hint: this is a nontrivial undertaking. The complexity of your proofs
will depend crucially on your choice of model and you may have to
revise your model as you proceed with the proof.
*}

(*<*)
end
(*>*)