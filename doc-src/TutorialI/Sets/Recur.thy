theory Recur = Main:

ML "Pretty.setmargin 64"


text{*
@{thm[display] mono_def[no_vars]}
\rulename{mono_def}

@{thm[display] monoI[no_vars]}
\rulename{monoI}

@{thm[display] monoD[no_vars]}
\rulename{monoD}

@{thm[display] lfp_unfold[no_vars]}
\rulename{lfp_unfold}

@{thm[display] lfp_induct[no_vars]}
\rulename{lfp_induct}

@{thm[display] gfp_unfold[no_vars]}
\rulename{gfp_unfold}

@{thm[display] coinduct[no_vars]}
\rulename{coinduct}
*}

text{*\noindent
A relation $<$ is
\bfindex{wellfounded} if it has no infinite descending chain $\cdots <
a@2 < a@1 < a@0$. Clearly, a function definition is total iff the set
of all pairs $(r,l)$, where $l$ is the argument on the left-hand side
of an equation and $r$ the argument of some recursive call on the
corresponding right-hand side, induces a wellfounded relation. 

The HOL library formalizes
some of the theory of wellfounded relations. For example
@{prop"wf r"}\index{*wf|bold} means that relation @{term[show_types]"r::('a*'a)set"} is
wellfounded.
Finally we should mention that HOL already provides the mother of all
inductions, \textbf{wellfounded
induction}\indexbold{induction!wellfounded}\index{wellfounded
induction|see{induction, wellfounded}} (@{thm[source]wf_induct}):
@{thm[display]wf_induct[no_vars]}
where @{term"wf r"} means that the relation @{term r} is wellfounded

*}

text{*

@{thm[display] wf_induct[no_vars]}
\rulename{wf_induct}

@{thm[display] less_than_iff[no_vars]}
\rulename{less_than_iff}

@{thm[display] inv_image_def[no_vars]}
\rulename{inv_image_def}

@{thm[display] measure_def[no_vars]}
\rulename{measure_def}

@{thm[display] wf_less_than[no_vars]}
\rulename{wf_less_than}

@{thm[display] wf_inv_image[no_vars]}
\rulename{wf_inv_image}

@{thm[display] wf_measure[no_vars]}
\rulename{wf_measure}

@{thm[display] lex_prod_def[no_vars]}
\rulename{lex_prod_def}

@{thm[display] wf_lex_prod[no_vars]}
\rulename{wf_lex_prod}

*}

end

