(* ID:         $Id$ *)
theory Functions = Main:

ML "Pretty.setmargin 64"


text{*
@{thm[display] id_def[no_vars]}
\rulename{id_def}

@{thm[display] o_def[no_vars]}
\rulename{o_def}

@{thm[display] o_assoc[no_vars]}
\rulename{o_assoc}
*}

text{*
@{thm[display] fun_upd_apply[no_vars]}
\rulename{fun_upd_apply}

@{thm[display] fun_upd_upd[no_vars]}
\rulename{fun_upd_upd}
*}


text{*
definitions of injective, surjective, bijective

@{thm[display] inj_on_def[no_vars]}
\rulename{inj_on_def}

@{thm[display] surj_def[no_vars]}
\rulename{surj_def}

@{thm[display] bij_def[no_vars]}
\rulename{bij_def}
*}



text{*
possibly interesting theorems about inv
*}

text{*
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
*}



text{*
small sample proof

@{thm[display] ext[no_vars]}
\rulename{ext}

@{thm[display] expand_fun_eq[no_vars]}
\rulename{expand_fun_eq}
*}

lemma "inj f \<Longrightarrow> (f o g = f o h) = (g = h)";
  apply (simp add: expand_fun_eq inj_on_def)
  apply (auto)
  done

text{*
\begin{isabelle}
inj\ f\ \isasymLongrightarrow \ (f\ \isasymcirc \ g\ =\ f\ \isasymcirc \ h)\ =\ (g\ =\ h)\isanewline
\ 1.\ \isasymforall x\ y.\ f\ x\ =\ f\ y\ \isasymlongrightarrow \ x\ =\ y\ \isasymLongrightarrow \isanewline
\ \ \ \ (\isasymforall x.\ f\ (g\ x)\ =\ f\ (h\ x))\ =\ (\isasymforall x.\ g\ x\ =\ h\ x)
\end{isabelle}
*}
 

text{*image, inverse image*}

text{*
@{thm[display] image_def[no_vars]}
\rulename{image_def}
*}

text{*
@{thm[display] image_Un[no_vars]}
\rulename{image_Un}
*}

text{*
@{thm[display] image_compose[no_vars]}
\rulename{image_compose}

@{thm[display] image_Int[no_vars]}
\rulename{image_Int}

@{thm[display] bij_image_Compl_eq[no_vars]}
\rulename{bij_image_Compl_eq}
*}


text{*
illustrates Union as well as image
*}

lemma "f`A \<union> g`A = (\<Union>x\<in>A. {f x, g x})"
by blast

lemma "f ` {(x,y). P x y} = {f(x,y) | x y. P x y}"
by blast

text{*actually a macro!*}

lemma "range f = f`UNIV"
by blast


text{*
inverse image
*}

text{*
@{thm[display] vimage_def[no_vars]}
\rulename{vimage_def}

@{thm[display] vimage_Compl[no_vars]}
\rulename{vimage_Compl}
*}


end
