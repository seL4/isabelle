(*<*)
theory pairs = Main:;
(*>*)
text{*
HOL also has pairs: \isa{($a@1$,$a@2$)} is of type \isa{$\tau@1$ *
  $\tau@2$} provided each $a@i$ is of type $\tau@i$. The components of a pair
are extracted by \isa{fst} and \isa{snd}: \isa{fst($x$,$y$) = $x$} and
\isa{snd($x$,$y$) = $y$}. Tuples are simulated by pairs nested to the right:
\isa{($a@1$,$a@2$,$a@3$)} stands for \isa{($a@1$,($a@2$,$a@3$))} and
\isa{$\tau@1$ * $\tau@2$ * $\tau@3$} for \isa{$\tau@1$ * ($\tau@2$ *
  $\tau@3$)}. Therefore we have \isa{fst(snd($a@1$,$a@2$,$a@3$)) = $a@2$}.

It is possible to use (nested) tuples as patterns in abstractions, for
example \isa{\isasymlambda(x,y,z).x+y+z} and
\isa{\isasymlambda((x,y),z).x+y+z}.
In addition to explicit $\lambda$-abstractions, tuple patterns can be used in
most variable binding constructs. Typical examples are
\begin{quote}
@{term"let (x,y) = f z in (y,x)"}\\
@{term"case xs of [] => 0 | (x,y)#zs => x+y"}
\end{quote}
Further important examples are quantifiers and sets (see~\S\ref{quant-pats}).
*}
(*<*)
end
(*>*)
