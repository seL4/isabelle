(* ID:         $Id$ *)
theory Force = Main: 
  (*Use Divides rather than Main to experiment with the first proof.
    Otherwise, it is done by the nat_divide_cancel_factor simprocs.*)

declare div_mult_self_is_m [simp del];

lemma div_mult_self_is_m: 
      "0<n \<Longrightarrow> (m*n) div n = (m::nat)"
apply (insert mod_div_equality [of "m*n" n])
apply simp
done


lemma "(\<forall>x. P x) \<and> (\<exists>x. Q x) \<longrightarrow> (\<forall>x. P x \<and> Q x)"
apply clarify
oops

text {*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ {\isadigit{1}}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isacharparenleft}{\isasymforall}x{\isachardot}\ P\ x{\isacharparenright}\ {\isasymand}\ {\isacharparenleft}{\isasymexists}x{\isachardot}\ Q\ x{\isacharparenright}\ {\isasymlongrightarrow}\ {\isacharparenleft}{\isasymforall}x{\isachardot}\ P\ x\ {\isasymand}\ Q\ x{\isacharparenright}\isanewline
\ {\isadigit{1}}{\isachardot}\ {\isasymAnd}x\ xa{\isachardot}\ {\isasymlbrakk}{\isasymforall}x{\isachardot}\ P\ x{\isacharsemicolon}\ Q\ xa{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ x\ {\isasymand}\ Q\ x
*};

text {*
couldn't find a good example of clarsimp

@{thm[display]"someI"}
\rulename{someI}
*};

lemma "\<lbrakk>Q a; P a\<rbrakk> \<Longrightarrow> P (SOME x. P x \<and> Q x) \<and> Q (SOME x. P x \<and> Q x)"
apply (rule someI)
oops

lemma "\<lbrakk>Q a; P a\<rbrakk> \<Longrightarrow> P (SOME x. P x \<and> Q x) \<and> Q (SOME x. P x \<and> Q x)"
apply (fast intro!: someI)
done

text{*
proof\ {\isacharparenleft}prove{\isacharparenright}{\isacharcolon}\ step\ \isadigit{1}\isanewline
\isanewline
goal\ {\isacharparenleft}lemma{\isacharparenright}{\isacharcolon}\isanewline
{\isasymlbrakk}Q\ a{\isacharsemicolon}\ P\ a{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ {\isacharparenleft}SOME\ x{\isachardot}\ P\ x\ {\isasymand}\ Q\ x{\isacharparenright}\ {\isasymand}\ Q\ {\isacharparenleft}SOME\ x{\isachardot}\ P\ x\ {\isasymand}\ Q\ x{\isacharparenright}\isanewline
\ \isadigit{1}{\isachardot}\ {\isasymlbrakk}Q\ a{\isacharsemicolon}\ P\ a{\isasymrbrakk}\ {\isasymLongrightarrow}\ P\ {\isacharquery}x\ {\isasymand}\ Q\ {\isacharquery}x
*}

end

