theory Tacticals = Main:

text{*REPEAT*}
lemma "\<lbrakk>P\<longrightarrow>Q; Q\<longrightarrow>R; R\<longrightarrow>S; P\<rbrakk> \<Longrightarrow> S"
apply (drule mp, assumption)
apply (drule mp, assumption)
apply (drule mp, assumption)
apply (assumption)
done

lemma "\<lbrakk>P\<longrightarrow>Q; Q\<longrightarrow>R; R\<longrightarrow>S; P\<rbrakk> \<Longrightarrow> S"
by (drule mp, assumption)+

text{*ORELSE with REPEAT*}
lemma "\<lbrakk>Q\<longrightarrow>R; P\<longrightarrow>Q; x<#5\<longrightarrow>P;  Suc x < #5\<rbrakk> \<Longrightarrow> R" 
by (drule mp, (assumption|arith))+

text{*exercise: what's going on here?*}
lemma "\<lbrakk>P\<and>Q\<longrightarrow>R; P\<longrightarrow>Q; P\<rbrakk> \<Longrightarrow> R"
by (drule mp, intro?, assumption+)+

text{*defer and prefer*}

lemma "hard \<and> (P \<or> ~P) \<and> (Q\<longrightarrow>Q)"
apply intro   --{* @{subgoals[display,indent=0,margin=65]} *}
defer 1   --{* @{subgoals[display,indent=0,margin=65]} *}
apply blast+   --{* @{subgoals[display,indent=0,margin=65]} *}
oops

lemma "ok1 \<and> ok2 \<and> doubtful"
apply intro   --{* @{subgoals[display,indent=0,margin=65]} *}
prefer 3   --{* @{subgoals[display,indent=0,margin=65]} *}
oops

lemma "thing1 \<and> thing2 \<and> thing3 \<and> thing4 \<and> thing5 \<and> thing6"
apply intro   --{* @{subgoals[display,indent=0,margin=65]} *}
pr 2  
txt{* @{subgoals[display,indent=0,margin=65]} *}
oops



(*needed??*)

lemma "(P\<or>Q) \<and> (R\<or>S) \<Longrightarrow> PP"
apply elim
oops

lemma "((P\<or>Q) \<and> R) \<and> (Q \<and> (P\<or>S)) \<Longrightarrow> PP"
apply (elim conjE)
oops

lemma "((P\<or>Q) \<and> R) \<and> (Q \<and> (P\<or>S)) \<Longrightarrow> PP"
apply (erule conjE)+
oops

end
