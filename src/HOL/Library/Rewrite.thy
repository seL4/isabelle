theory Rewrite
imports Main
begin

consts rewrite_HOLE :: "'a :: {}"
notation rewrite_HOLE ("HOLE")
notation rewrite_HOLE ("\<box>")

lemma eta_expand:
  fixes f :: "'a :: {} \<Rightarrow> 'b :: {}" shows "f \<equiv> (\<lambda>x. f x)"
  by (rule reflexive)

ML_file "cconv.ML"
ML_file "rewrite.ML"
setup Rewrite.setup

end
