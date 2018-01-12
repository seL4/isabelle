theory Functions imports Main begin


text\<open>
@{thm[display] id_def[no_vars]}
\rulename{id_def}

@{thm[display] o_def[no_vars]}
\rulename{o_def}

@{thm[display] o_assoc[no_vars]}
\rulename{o_assoc}
\<close>

text\<open>
@{thm[display] fun_upd_apply[no_vars]}
\rulename{fun_upd_apply}

@{thm[display] fun_upd_upd[no_vars]}
\rulename{fun_upd_upd}
\<close>


text\<open>
definitions of injective, surjective, bijective

@{thm[display] inj_on_def[no_vars]}
\rulename{inj_on_def}

@{thm[display] surj_def[no_vars]}
\rulename{surj_def}

@{thm[display] bij_def[no_vars]}
\rulename{bij_def}
\<close>



text\<open>
possibly interesting theorems about inv
\<close>

text\<open>
@{thm[display] inv_f_f[no_vars]}
\rulename{inv_f_f}

@{thm[display] inj_imp_surj_inv[no_vars]}
\rulename{inj_imp_surj_inv}

@{thm[display] surj_imp_inj_inv[no_vars]}
\rulename{surj_imp_inj_inv}

@{thm[display] surj_f_inv_f[no_vars]}
\rulename{surj_f_inv_f}

@{thm[display] bij_imp_bij_inv[no_vars]}
\rulename{bij_imp_bij_inv}

@{thm[display] inv_inv_eq[no_vars]}
\rulename{inv_inv_eq}

@{thm[display] o_inv_distrib[no_vars]}
\rulename{o_inv_distrib}
\<close>

text\<open>
small sample proof

@{thm[display] ext[no_vars]}
\rulename{ext}

@{thm[display] fun_eq_iff[no_vars]}
\rulename{fun_eq_iff}
\<close>

lemma "inj f \<Longrightarrow> (f o g = f o h) = (g = h)"
  apply (simp add: fun_eq_iff inj_on_def)
  apply (auto)
  done

text\<open>
\begin{isabelle}
inj\ f\ \isasymLongrightarrow \ (f\ \isasymcirc \ g\ =\ f\ \isasymcirc \ h)\ =\ (g\ =\ h)\isanewline
\ 1.\ \isasymforall x\ y.\ f\ x\ =\ f\ y\ \isasymlongrightarrow \ x\ =\ y\ \isasymLongrightarrow \isanewline
\ \ \ \ (\isasymforall x.\ f\ (g\ x)\ =\ f\ (h\ x))\ =\ (\isasymforall x.\ g\ x\ =\ h\ x)
\end{isabelle}
\<close>
 

text\<open>image, inverse image\<close>

text\<open>
@{thm[display] image_def[no_vars]}
\rulename{image_def}
\<close>

text\<open>
@{thm[display] image_Un[no_vars]}
\rulename{image_Un}
\<close>

text\<open>
@{thm[display] image_comp[no_vars]}
\rulename{image_comp}

@{thm[display] image_Int[no_vars]}
\rulename{image_Int}

@{thm[display] bij_image_Compl_eq[no_vars]}
\rulename{bij_image_Compl_eq}
\<close>


text\<open>
illustrates Union as well as image
\<close>

lemma "f`A \<union> g`A = (\<Union>x\<in>A. {f x, g x})"
by blast

lemma "f ` {(x,y). P x y} = {f(x,y) | x y. P x y}"
by blast

text\<open>actually a macro!\<close>

lemma "range f = f`UNIV"
by blast


text\<open>
inverse image
\<close>

text\<open>
@{thm[display] vimage_def[no_vars]}
\rulename{vimage_def}

@{thm[display] vimage_Compl[no_vars]}
\rulename{vimage_Compl}
\<close>


end
