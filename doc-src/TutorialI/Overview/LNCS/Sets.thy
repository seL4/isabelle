(*<*)theory Sets = Main:(*>*)

section{*Sets, Functions and Relations*}

subsection{*Set Notation*}

text{*
\begin{center}
\begin{tabular}{ccc}
@{term "A \<union> B"} & @{term "A \<inter> B"} & @{term "A - B"} \\
@{term "a \<in> A"} & @{term "b \<notin> A"} \\
@{term "{a,b}"} & @{text "{x. P x}"} \\
@{term "\<Union> M"} & @{text "\<Union>a \<in> A. F a"}
\end{tabular}
\end{center}*}
(*<*)term "A \<union> B" term "A \<inter> B" term "A - B"
term "a \<in> A" term "b \<notin> A"
term "{a,b}" term "{x. P x}"
term "\<Union> M"  term "\<Union>a \<in> A. F a"(*>*)


subsection{*Some Functions*}

text{*
\begin{tabular}{l}
@{thm id_def}\\
@{thm o_def[no_vars]}\\
@{thm image_def[no_vars]}\\
@{thm vimage_def[no_vars]}
\end{tabular}*}
(*<*)thm id_def o_def[no_vars] image_def[no_vars] vimage_def[no_vars](*>*)


subsection{*Some Relations*}

text{*
\begin{tabular}{l}
@{thm Id_def}\\
@{thm converse_def[no_vars]}\\
@{thm Image_def[no_vars]}\\
@{thm rtrancl_refl[no_vars]}\\
@{thm rtrancl_into_rtrancl[no_vars]}
\end{tabular}*}
(*<*)thm Id_def
thm converse_def[no_vars] Image_def[no_vars]
thm relpow.simps[no_vars]
thm rtrancl.intros[no_vars](*>*)


subsection{*Wellfoundedness*}

text{*
\begin{tabular}{l}
@{thm wf_def[no_vars]}\\
@{thm wf_iff_no_infinite_down_chain[no_vars]}
\end{tabular}*}
(*<*)thm wf_def[no_vars]
thm wf_iff_no_infinite_down_chain[no_vars](*>*)


subsection{*Fixed Point Operators*}

text{*
\begin{tabular}{l}
@{thm lfp_def[no_vars]}\\
@{thm lfp_unfold[no_vars]}\\
@{thm lfp_induct[no_vars]}
\end{tabular}*}
(*<*)thm lfp_def[no_vars] gfp_def[no_vars]
thm lfp_unfold[no_vars]
thm lfp_induct[no_vars](*>*)


subsection{*Case Study: Verified Model Checking*}

typedecl state

consts M :: "(state \<times> state)set"

typedecl atom

consts L :: "state \<Rightarrow> atom set"

datatype formula = Atom atom
                 | Neg formula
                 | And formula formula
                 | AX formula
                 | EF formula

consts valid :: "state \<Rightarrow> formula \<Rightarrow> bool"   ("(_ \<Turnstile> _)" [80,80] 80)

primrec
"s \<Turnstile> Atom a  = (a \<in> L s)"
"s \<Turnstile> Neg f   = (\<not>(s \<Turnstile> f))"
"s \<Turnstile> And f g = (s \<Turnstile> f \<and> s \<Turnstile> g)"
"s \<Turnstile> AX f    = (\<forall>t. (s,t) \<in> M \<longrightarrow> t \<Turnstile> f)"
"s \<Turnstile> EF f    = (\<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<Turnstile> f)"

consts mc :: "formula \<Rightarrow> state set"
primrec
"mc(Atom a)  = {s. a \<in> L s}"
"mc(Neg f)   = -mc f"
"mc(And f g) = mc f \<inter> mc g"
"mc(AX f)    = {s. \<forall>t. (s,t) \<in> M  \<longrightarrow> t \<in> mc f}"
"mc(EF f)    = lfp(\<lambda>T. mc f \<union> (M\<inverse> `` T))"

lemma mono_ef: "mono(\<lambda>T. A \<union> (M\<inverse> `` T))"
apply(rule monoI)
apply blast
done

lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> (M\<inverse> `` T)) = {s. \<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<in> A}"
apply(rule equalityI)
 thm lfp_lowerbound
 apply(rule lfp_lowerbound)
 apply(blast intro: rtrancl_trans)
apply(rule subsetI)
apply clarsimp
apply(erule converse_rtrancl_induct)
thm lfp_unfold[OF mono_ef]
 apply(subst lfp_unfold[OF mono_ef])
 apply(blast)
apply(subst lfp_unfold[OF mono_ef])
apply(blast)
done

theorem "mc f = {s. s \<Turnstile> f}"
apply(induct_tac f)
apply(auto simp add: EF_lemma)
done

text{*Preview of coming attractions: a structured proof of the
@{thm[source]EF_lemma}.*}
lemma EF_lemma:
  "lfp(\<lambda>T. A \<union> (M\<inverse> `` T)) = {s. \<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<in> A}"
  (is "lfp ?F = ?R") 
proof
  show "lfp ?F \<subseteq> ?R"
  proof (rule lfp_lowerbound)
    show "?F ?R \<subseteq> ?R" by(blast intro: rtrancl_trans)
  qed
next
  show "?R \<subseteq> lfp ?F"
  proof
    fix s assume "s \<in> ?R"
    then obtain t where st: "(s,t) \<in> M\<^sup>*" and tA: "t \<in> A" by blast
    from st show "s \<in> lfp ?F"
    proof (rule converse_rtrancl_induct)
      show "t \<in> lfp ?F"
      proof (subst lfp_unfold[OF mono_ef])
	show "t \<in> ?F(lfp ?F)" using tA by blast
      qed
    next
      fix s s'
      assume ss': "(s,s') \<in> M" and s't: "(s',t) \<in> M\<^sup>*"
         and IH: "s' \<in> lfp ?F"
      show "s \<in> lfp ?F"
      proof (subst lfp_unfold[OF mono_ef])
	show "s \<in> ?F(lfp ?F)" using prems by blast
      qed
    qed
  qed
qed

text{*
\begin{exercise}
@{term AX} has a dual operator @{term EN}\footnote{We cannot use the customary @{text EX}
as that is the \textsc{ascii}-equivalent of @{text"\<exists>"}}
(``there exists a next state such that'') with the intended semantics
@{prop[display]"(s \<Turnstile> EN f) = (EX t. (s,t) : M & t \<Turnstile> f)"}
Fortunately, @{term"EN f"} can already be expressed as a PDL formula. How?

Show that the semantics for @{term EF} satisfies the following recursion equation:
@{prop[display]"(s \<Turnstile> EF f) = (s \<Turnstile> f | s \<Turnstile> EN(EF f))"}
\end{exercise}*}
(*<*)end(*>*)
