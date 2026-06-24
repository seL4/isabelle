(*  Title:      HOL/Library/Function_Real_Vectors.thy
    Author:     Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    Author:     Fabian Immler, TUM
*)

section \<open>Functions as a real vector spaces\<close>

theory Function_Real_Vectors
  imports
    Complex_Main
    Function_Algebras
begin

instantiation "fun" :: (type, scaleR) scaleR
begin

definition scaleR_fun::"real \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "scaleR_fun = (\<lambda>c f. (\<lambda>x. c *\<^sub>R f x))"

lemma scaleR_apply [simp, code]: "(c *\<^sub>R f) x = c *\<^sub>R (f x)"
  by (simp add: scaleR_fun_def)

instance ..

end

instance "fun" :: (type, real_vector) real_vector
  by standard
    (auto simp: scaleR_fun_def algebra_simps)

end
