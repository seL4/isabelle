(*  Title:      HOL/Alethe_Boolean_Rewrites_Lemmas.thy
    Author:     Hanna Lachnitt, Stanford University
*)
theory Alethe_Boolean_Rewrites_Lemmas
  imports Alethe_Rare_Nary_Ops
begin

lemma bool_or_taut_lemma:
  "w \<or> a \<or> foldr (\<or>) yss (\<not> w)"
  "a \<or> foldr (\<or>) xss (w \<or> aa \<or> foldr (\<or>) yss (\<not> w))"
  "foldr (\<or>) xss (w \<or> foldr (\<or>) yss (w \<longrightarrow> a \<or> foldr (\<or>) zss False))"
    apply force
   apply (metis (mono_tags, opaque_lifting) foldr_or_neutral)
  by (metis(full_types) foldr_or_neutral)

lemma bool_and_conf_lemma:
  "\<not> foldr (\<and>) xss (w \<and> aa \<and> foldr (\<and>) yss (\<not> w))"
  "\<not> foldr (\<and>) xss (w \<and> foldr (\<and>) yss (\<not> w \<and> a \<and> foldr (\<and>) zss True))"
  apply (metis (mono_tags, opaque_lifting) foldr_and_neutral)
  by (metis(full_types) foldr_and_neutral)

lemma bool_and_conf2_lemma:
  "\<not> foldr (\<and>) xss ((\<not> w) \<and> aa \<and> foldr (\<and>) yss w)"
  "\<not> foldr (\<and>) xss ((\<not> w) \<and> foldr (\<and>) yss (w \<and> a \<and> foldr (\<and>) zss True))"
  apply (metis (mono_tags, opaque_lifting) foldr_and_neutral)
  by (metis(full_types) foldr_and_neutral)

lemma bool_and_dup_lemma:
  "(b \<and> a \<and> foldr (\<and>) yss b) = (b \<and> a \<and> foldr (\<and>) yss True)"
  "(a \<and> foldr (\<and>) xss (b \<and> aa \<and> foldr (\<and>) yss b)) = (a \<and> foldr (\<and>) xss (b \<and> aa \<and> foldr (\<and>) yss True))"
  "foldr (\<and>) xss (b \<and> foldr (\<and>) yss (b \<and> a \<and> foldr (\<and>) zss True)) = foldr (\<and>) xss (b \<and> foldr (\<and>) yss (a \<and> foldr (\<and>) zss True))"
   apply auto[1]
   apply (metis(full_types))
  by (metis(full_types))

lemma bool_and_flatten_lemma:
  "(b \<and> a \<and> foldr (\<and>) yss True \<and> aa \<and> foldr (\<and>) zss True) = (b \<and> a \<and> foldr (\<and>) yss (aa \<and> foldr (\<and>) zss True))"
  by (metis(full_types) foldr_and_neutral)

lemma bool_or_dup_lemma:
  "(b \<or> a \<or> foldr (\<or>) yss b) = (b \<or> a \<or> foldr (\<or>) yss False)"
  "(a \<or> foldr (\<or>) xss (b \<or> aa \<or> foldr (\<or>) yss b)) = (a \<or> foldr (\<or>) xss (b \<or> aa \<or> foldr (\<or>) yss False))"
  "foldr (\<or>) xss (b \<or> foldr (\<or>) yss (b \<or> a \<or> foldr (\<or>) zss False)) = foldr (\<or>) xss (b \<or> foldr (\<or>) yss (a \<or> foldr (\<or>) zss False))"
    apply auto[1]
   apply (metis(full_types))
  by (metis(full_types))

lemma bool_or_flatten_lemma:
  "(b \<or> a \<or> foldr (\<or>) yss False \<or> aa \<or> foldr (\<or>) zss False) = (b \<or> a \<or> foldr (\<or>) yss (aa \<or> foldr (\<or>) zss False))"
  "(a \<or> foldr (\<or>) xss (b \<or> aa \<or> foldr (\<or>) yss False \<or> aaa \<or> foldr (\<or>) zss False)) =
  (a \<or> foldr (\<or>) xss (b \<or> aa \<or> foldr (\<or>) yss (aaa \<or> foldr (\<or>) zss False)))"
   apply (metis(full_types) foldr_or_neutral)
  by (metis(full_types) foldr_or_neutral)

lemma bool_or_and_distrib_lemma:
  shows "zs = ListVar zss \<Longrightarrow>
    ys = ListVar yss \<Longrightarrow>
    (y1 \<and> y2 \<and> foldr (\<and>) yss True \<or> z1 \<or> foldr (\<or>) zss False) =
    ((y1 \<or> z1 \<or> foldr (\<or>) zss False) \<and> (y2 \<and> foldr (\<and>) yss True \<or> z1 \<or> foldr (\<or>) zss False))"
  using disj_conj_distribR by simp

end
