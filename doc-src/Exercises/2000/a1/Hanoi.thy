(*<*)
theory Hanoi = Main:
(*>*)
subsection {* The towers of Hanoi \label{psv2000hanoi} *}

text {*

We are given 3 pegs $A$, $B$ and $C$, and $n$ disks with a hole, such
that no two disks have the same diameter.  Initially all $n$ disks
rest on peg $A$, ordered according to their size, with the largest one
at the bottom. The aim is to transfer all $n$ disks from $A$ to $C$ by
a sequence of single-disk moves such that we never place a larger disk
on top of a smaller one. Peg $B$ may be used for intermediate storage.

\begin{center}
\includegraphics[width=0.8\textwidth]{Hanoi}
\end{center}

\medskip The pegs and moves can be modelled as follows:
*};  

datatype peg = A | B | C
types move = "peg * peg"

text {*
Define a primitive recursive function
*};

consts
  moves :: "nat => peg => peg => peg => move list";

text {* such that @{term moves}$~n~a~b~c$ returns a list of (legal)
moves that transfer $n$ disks from peg $a$ via $b$ to $c$.
Show that this requires $2^n - 1$ moves:
*}

theorem "length (moves n a b c) = 2^n - 1"
(*<*)oops(*>*)

text {* Hint: You need to strengthen the theorem for the
induction to go through. Beware: subtraction on natural numbers
behaves oddly: $n - m = 0$ if $n \le m$. *}

(*<*)
end
(*>*)
