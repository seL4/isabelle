(* ID:         $Id$ *)
theory Relations = Main:

ML "Pretty.setmargin 64"

(*Id is only used in UNITY*)
(*refl, antisym,trans,univalent,\<dots> ho hum*)

text{*
@{thm[display]"Id_def"}
\rulename{Id_def}
*}

text{*
@{thm[display]"comp_def"}
\rulename{comp_def}
*}

text{*
@{thm[display]"R_O_Id"}
\rulename{R_O_Id}
*}

text{*
@{thm[display]"comp_mono"}
\rulename{comp_mono}
*}

text{*
@{thm[display]"converse_iff"}
\rulename{converse_iff}
*}

text{*
@{thm[display]"converse_comp"}
\rulename{converse_comp}
*}

text{*
@{thm[display]"Image_iff"}
\rulename{Image_iff}
*}

text{*
@{thm[display]"Image_UN"}
\rulename{Image_UN}
*}

text{*
@{thm[display]"Domain_iff"}
\rulename{Domain_iff}
*}

text{*
@{thm[display]"Range_iff"}
\rulename{Range_iff}
*}

text{*
@{thm[display]"relpow.simps"}
\rulename{relpow.simps}

@{thm[display]"rtrancl_unfold"}
\rulename{rtrancl_unfold}

@{thm[display]"rtrancl_refl"}
\rulename{rtrancl_refl}

@{thm[display]"r_into_rtrancl"}
\rulename{r_into_rtrancl}

@{thm[display]"rtrancl_trans"}
\rulename{rtrancl_trans}

@{thm[display]"rtrancl_induct"}
\rulename{rtrancl_induct}

@{thm[display]"rtrancl_idemp"}
\rulename{rtrancl_idemp}

@{thm[display]"r_into_trancl"}
\rulename{r_into_trancl}

@{thm[display]"trancl_trans"}
\rulename{trancl_trans}

@{thm[display]"trancl_into_rtrancl"}
\rulename{trancl_into_rtrancl}

@{thm[display]"trancl_converse"}
\rulename{trancl_converse}
*}

text{*Relations.  transitive closure*}

lemma rtrancl_converseD: "(x,y) \<in> (r^-1)^* \<Longrightarrow> (y,x) \<in> r^*"
  apply (erule rtrancl_induct)
   apply (rule rtrancl_refl)
  apply (blast intro: r_into_rtrancl rtrancl_trans)
  done

text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma\ rtrancl{\isacharunderscore}converseD{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}x{\isacharcomma}\ y{\isacharparenright}\ {\isasymin}\ {\isacharparenleft}r{\isacharcircum}{\isacharminus}\isadigit{1}{\isacharparenright}{\isacharcircum}{\isacharasterisk}\ {\isasymLongrightarrow}\ {\isacharparenleft}y{\isacharcomma}\ x{\isacharparenright}\ {\isasymin}\ r{\isacharcircum}{\isacharasterisk}\isanewline
\ \isadigit{1}{\isachardot}\ {\isacharparenleft}x{\isacharcomma}\ x{\isacharparenright}\ {\isasymin}\ r{\isacharcircum}{\isacharasterisk}\isanewline
\ \isadigit{2}{\isachardot}\ {\isasymAnd}y\ z{\isachardot}\ {\isasymlbrakk}{\isacharparenleft}x{\isacharcomma}\ y{\isacharparenright}\ {\isasymin}\ {\isacharparenleft}r{\isacharcircum}{\isacharminus}\isadigit{1}{\isacharparenright}{\isacharcircum}{\isacharasterisk}{\isacharsemicolon}\ {\isacharparenleft}y{\isacharcomma}\ z{\isacharparenright}\ {\isasymin}\ r{\isacharcircum}{\isacharminus}\isadigit{1}{\isacharsemicolon}\ {\isacharparenleft}y{\isacharcomma}\ x{\isacharparenright}\ {\isasymin}\ r{\isacharcircum}{\isacharasterisk}{\isasymrbrakk}\isanewline
\ \ \ \ \ \ \ \ \ \ {\isasymLongrightarrow}\ {\isacharparenleft}z{\isacharcomma}\ x{\isacharparenright}\ {\isasymin}\ r{\isacharcircum}{\isacharasterisk}
*}

lemma rtrancl_converseI: "(y,x) \<in> r^* \<Longrightarrow> (x,y) \<in> (r^-1)^*"
  apply (erule rtrancl_induct)
   apply (rule rtrancl_refl)
  apply (blast intro: r_into_rtrancl rtrancl_trans)
  done

lemma rtrancl_converse: "(r^-1)^* = (r^*)^-1"
  apply (auto intro: rtrancl_converseI dest: rtrancl_converseD)
  done


lemma "A \<subseteq> Id"
  apply (rule subsetI)
  apply (auto)
  oops

text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
A\ {\isasymsubseteq}\ Id\isanewline
\ \isadigit{1}{\isachardot}\ {\isasymAnd}x{\isachardot}\ x\ {\isasymin}\ A\ {\isasymLongrightarrow}\ x\ {\isasymin}\ Id

proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{2}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
A\ {\isasymsubseteq}\ Id\isanewline
\ \isadigit{1}{\isachardot}\ {\isasymAnd}a\ b{\isachardot}\ {\isacharparenleft}a{\isacharcomma}\ b{\isacharparenright}\ {\isasymin}\ A\ {\isasymLongrightarrow}\ a\ {\isacharequal}\ b
*}

text{*questions: do we cover force?  (Why not?)
Do we include tables of operators in ASCII and X-symbol notation like in the Logics manuals?*}


text{*rejects*}

lemma "(a \<in> {z. P z} \<union> {y. Q y}) = P a \<or> Q a"
  apply (blast)
  done

text{*Pow, Inter too little used*}

lemma "(A \<subset> B) = (A \<subseteq> B \<and> A \<noteq> B)"
  apply (simp add: psubset_def)
  done

(*
text{*
@{thm[display]"DD"}
\rulename{DD}
*}
*)

end
