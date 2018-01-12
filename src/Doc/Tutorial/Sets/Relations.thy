theory Relations imports Main begin

(*Id is only used in UNITY*)
(*refl, antisym,trans,univalent,\<dots> ho hum*)

text\<open>
@{thm[display] Id_def[no_vars]}
\rulename{Id_def}
\<close>

text\<open>
@{thm[display] relcomp_unfold[no_vars]}
\rulename{relcomp_unfold}
\<close>

text\<open>
@{thm[display] R_O_Id[no_vars]}
\rulename{R_O_Id}
\<close>

text\<open>
@{thm[display] relcomp_mono[no_vars]}
\rulename{relcomp_mono}
\<close>

text\<open>
@{thm[display] converse_iff[no_vars]}
\rulename{converse_iff}
\<close>

text\<open>
@{thm[display] converse_relcomp[no_vars]}
\rulename{converse_relcomp}
\<close>

text\<open>
@{thm[display] Image_iff[no_vars]}
\rulename{Image_iff}
\<close>

text\<open>
@{thm[display] Image_UN[no_vars]}
\rulename{Image_UN}
\<close>

text\<open>
@{thm[display] Domain_iff[no_vars]}
\rulename{Domain_iff}
\<close>

text\<open>
@{thm[display] Range_iff[no_vars]}
\rulename{Range_iff}
\<close>

text\<open>
@{thm[display] relpow.simps[no_vars]}
\rulename{relpow.simps}

@{thm[display] rtrancl_refl[no_vars]}
\rulename{rtrancl_refl}

@{thm[display] r_into_rtrancl[no_vars]}
\rulename{r_into_rtrancl}

@{thm[display] rtrancl_trans[no_vars]}
\rulename{rtrancl_trans}

@{thm[display] rtrancl_induct[no_vars]}
\rulename{rtrancl_induct}

@{thm[display] rtrancl_idemp[no_vars]}
\rulename{rtrancl_idemp}

@{thm[display] r_into_trancl[no_vars]}
\rulename{r_into_trancl}

@{thm[display] trancl_trans[no_vars]}
\rulename{trancl_trans}

@{thm[display] trancl_into_rtrancl[no_vars]}
\rulename{trancl_into_rtrancl}

@{thm[display] trancl_converse[no_vars]}
\rulename{trancl_converse}
\<close>

text\<open>Relations.  transitive closure\<close>

lemma rtrancl_converseD: "(x,y) \<in> (r\<inverse>)\<^sup>* \<Longrightarrow> (y,x) \<in> r\<^sup>*"
apply (erule rtrancl_induct)
txt\<open>
@{subgoals[display,indent=0,margin=65]}
\<close>
 apply (rule rtrancl_refl)
apply (blast intro: rtrancl_trans)
done


lemma rtrancl_converseI: "(y,x) \<in> r\<^sup>* \<Longrightarrow> (x,y) \<in> (r\<inverse>)\<^sup>*"
apply (erule rtrancl_induct)
 apply (rule rtrancl_refl)
apply (blast intro: rtrancl_trans)
done

lemma rtrancl_converse: "(r\<inverse>)\<^sup>* = (r\<^sup>*)\<inverse>"
by (auto intro: rtrancl_converseI dest: rtrancl_converseD)

lemma rtrancl_converse: "(r\<inverse>)\<^sup>* = (r\<^sup>*)\<inverse>"
apply (intro equalityI subsetI)
txt\<open>
after intro rules

@{subgoals[display,indent=0,margin=65]}
\<close>
apply clarify
txt\<open>
after splitting
@{subgoals[display,indent=0,margin=65]}
\<close>
oops


lemma "(\<forall>u v. (u,v) \<in> A \<longrightarrow> u=v) \<Longrightarrow> A \<subseteq> Id"
apply (rule subsetI)
txt\<open>
@{subgoals[display,indent=0,margin=65]}

after subsetI
\<close>
apply clarify
txt\<open>
@{subgoals[display,indent=0,margin=65]}

subgoals after clarify
\<close>
by blast




text\<open>rejects\<close>

lemma "(a \<in> {z. P z} \<union> {y. Q y}) = P a \<or> Q a"
apply (blast)
done

text\<open>Pow, Inter too little used\<close>

lemma "(A \<subset> B) = (A \<subseteq> B \<and> A \<noteq> B)"
apply (simp add: psubset_eq)
done

end
