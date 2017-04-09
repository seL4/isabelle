(*  Title:      ZF/Constructible/MetaExists.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section\<open>The meta-existential quantifier\<close>

theory MetaExists imports ZF begin

text\<open>Allows quantification over any term.  Used to quantify over classes.
Yields a proposition rather than a FOL formula.\<close>

definition
  ex :: "(('a::{}) \<Rightarrow> prop) \<Rightarrow> prop"  (binder "\<Or>" 0) where
  "ex(P) == (\<And>Q. (\<And>x. PROP P(x) \<Longrightarrow> PROP Q) \<Longrightarrow> PROP Q)"

lemma meta_exI: "PROP P(x) ==> (\<Or>x. PROP P(x))"
proof (unfold ex_def)
  assume P: "PROP P(x)"
  fix Q
  assume PQ: "\<And>x. PROP P(x) \<Longrightarrow> PROP Q"
  from P show "PROP Q" by (rule PQ)
qed 

lemma meta_exE: "[|\<Or>x. PROP P(x);  \<And>x. PROP P(x) ==> PROP R |] ==> PROP R"
proof (unfold ex_def)
  assume QPQ: "\<And>Q. (\<And>x. PROP P(x) \<Longrightarrow> PROP Q) \<Longrightarrow> PROP Q"
  assume PR: "\<And>x. PROP P(x) \<Longrightarrow> PROP R"
  from PR show "PROP R" by (rule QPQ)
qed

end
