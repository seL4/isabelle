(*<*)
theory VC_Principles
imports Proc1 Proc2
begin
(*>*)

chapter {* Principles of VC generation *}

text {*
\label{sec:vc-principles}
In this section, we will discuss some aspects of VC generation that are
useful for understanding and optimizing the VCs produced by the \SPARK{}
Examiner.

\begin{figure}
\lstinputlisting{loop_invariant.ads}
\lstinputlisting{loop_invariant.adb}
\caption{Assertions in for-loops}
\label{fig:loop-invariant-ex}
\end{figure}
\begin{figure}
\begin{tikzpicture}
\tikzstyle{box}=[draw, drop shadow, fill=white, rounded corners]
\node[box] (pre) at (0,0) {precondition};
\node[box] (assn) at (0,-3) {assertion};
\node[box] (post) at (0,-6) {postcondition};
\draw[-latex] (pre) -- node [right] {\small$(1 - 1) * b \mod 2^{32} = 0$} (assn);
\draw[-latex] (assn) .. controls (2.5,-4.5) and (2.5,-1.5) .. %
node [right] {\small$\begin{array}{l} %
(i - 1) * b \mod 2^{32} = c ~\longrightarrow \\ %
(i + 1 - 1) * b \mod 2^{32} ~= \\ %
(c + b) \mod 2^{32} %
\end{array}$} (assn);
\draw[-latex] (assn) -- node [right] {\small$\begin{array}{l} %
(a - 1) * b \mod 2^{32} = c ~\longrightarrow \\ %
a * b \mod 2^{32} = (c + b) \mod 2^{32} %
\end{array}$} (post);
\draw[-latex] (pre) .. controls (-2,-3) .. %
node [left] {\small$\begin{array}{l} %
\neg 1 \le a ~\longrightarrow \\ %
a * b \mod 2^{32} = 0 %
\end{array}$} (post);
\end{tikzpicture}
\caption{Control flow graph for procedure \texttt{Proc1}}
\label{fig:proc1-graph}
\end{figure}
\begin{figure}
\begin{tikzpicture}
\tikzstyle{box}=[draw, drop shadow, fill=white, rounded corners]
\node[box] (pre) at (0,0) {precondition};
\node[box] (assn1) at (2,-3) {assertion 1};
\node[box] (assn2) at (2,-6) {assertion 2};
\node[box] (post) at (0,-9) {postcondition};
\draw[-latex] (pre) -- node [right] {\small$(1 - 1) * b \mod 2^{32} = 0$} (assn1);
\draw[-latex] (assn1) -- node [left] {\small$\begin{array}{l} %
(i - 1) * b \mod 2^{32} = c \\ %
\longrightarrow \\ %
i * b \mod 2^{32} = \\ %
(c + b) \mod 2^{32} %
\end{array}$} (assn2);
\draw[-latex] (assn2) .. controls (4.5,-7.5) and (4.5,-1.5) .. %
node [right] {\small$\begin{array}{l} %
i * b \mod 2^{32} = c ~\longrightarrow \\ %
(i + 1 - 1) * b \mod 2^{32} = c %
\end{array}$} (assn1);
\draw[-latex] (assn2) -- node [right] {\small$\begin{array}{l} %
a * b \mod 2^{32} = c ~\longrightarrow \\ %
a * b \mod 2^{32} = c %
\end{array}$} (post);
\draw[-latex] (pre) .. controls (-3,-3) and (-3,-6) .. %
node [left,very near start] {\small$\begin{array}{l} %
\neg 1 \le a ~\longrightarrow \\ %
a * b \mod 2^{32} = 0 %
\end{array}$} (post);
\end{tikzpicture}
\caption{Control flow graph for procedure \texttt{Proc2}}
\label{fig:proc2-graph}
\end{figure}
As explained by Barnes \cite[\S 11.5]{Barnes}, the \SPARK{} Examiner unfolds the loop
\begin{lstlisting}
for I in T range L .. U loop
  --# assert P (I);
  S;
end loop;
\end{lstlisting}
to
\begin{lstlisting}
if L <= U then
  I := L;
  loop
    --# assert P (I);
    S;
    exit when I = U;
    I := I + 1;
  end loop;
end if;
\end{lstlisting}
Due to this treatment of for-loops, the user essentially has to prove twice that
\texttt{S} preserves the invariant \textit{\texttt{P}}, namely for
the path from the assertion to the assertion and from the assertion to the next cut
point following the loop. The preservation of the invariant has to be proved even
more often when the loop is followed by an if-statement. For trivial invariants,
this might not seem like a big problem, but in realistic applications, where invariants
are complex, this can be a major inconvenience. Often, the proofs of the invariant differ
only in a few variables, so it is tempting to just copy and modify existing proof scripts,
but this leads to proofs that are hard to maintain.
The problem of having to prove the invariant several times can be avoided by rephrasing
the above for-loop to
\begin{lstlisting}
for I in T range L .. U loop
  --# assert P (I);
  S;
  --# assert P (I + 1)
end loop;
\end{lstlisting}
The VC for the path from the second assertion to the first assertion is trivial and can
usually be proved automatically by the \SPARK{} Simplifier, whereas the VC for the path
from the first assertion to the second assertion actually expresses the fact that
\texttt{S} preserves the invariant.

We illustrate this technique using the example package shown in \figref{fig:loop-invariant-ex}.
It contains two procedures \texttt{Proc1} and \texttt{Proc2}, both of which implement
multiplication via addition. The procedures have the same specification, but in \texttt{Proc1},
only one \textbf{assert} statement is placed at the beginning of the loop, whereas \texttt{Proc2}
employs the trick explained above.
After applying the \SPARK{} Simplifier to the VCs generated for \texttt{Proc1}, two very
similar VCs
@{thm [display] (concl) procedure_proc1_5 [simplified pow_2_32_simp]}
and
@{thm [display,margin=60] (concl) procedure_proc1_8 [simplified pow_2_32_simp]}
remain, whereas for \texttt{Proc2}, only the first of the above VCs remains.
Why placing \textbf{assert} statements both at the beginning and at the end of the loop body
simplifies the proof of the invariant should become obvious when looking at \figref{fig:proc1-graph}
and \figref{fig:proc2-graph} showing the \emph{control flow graphs} for \texttt{Proc1} and
\texttt{Proc2}, respectively. The nodes in the graph correspond to cut points in the program,
and the paths between the cut points are annotated with the corresponding VCs. To reduce the
size of the graphs, we do not show nodes and edges corresponding to runtime checks.
The VCs for the path bypassing the loop and for the path from the precondition to the
(first) assertion are the same for both procedures. The graph for \texttt{Proc1} contains
two VCs expressing that the invariant is preserved by the execution of the loop body: one
for the path from the assertion to the assertion, and another one for the path from the
assertion to the conclusion, which corresponds to the last iteration of the loop. The latter
VC can be obtained from the former by simply replacing $i$ by $a$. In contrast, the graph
for \texttt{Proc2} contains only one such VC for the path from assertion 1 to assertion 2.
The VC for the path from assertion 2 to assertion 1 is trivial, and so is the VC for the
path from assertion 2 to the postcondition, expressing that the loop invariant implies
the postcondition when the loop has terminated.
*}

(*<*)
end
(*>*)
