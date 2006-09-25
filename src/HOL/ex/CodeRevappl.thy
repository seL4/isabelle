(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Combinators for structured results *}

theory CodeRevappl
imports Main
begin

section {* Combinators for structured results *}


subsection {* primitive definitions *}

definition
  revappl :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixl "\<triangleright>" 55)
  revappl_def: "x \<triangleright> f = f x"
  revappl_snd :: "'c \<times> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<times> 'b" (infixl "|\<triangleright>" 55)
  revappl_snd_split: "z |\<triangleright> f = (fst z , f (snd z))"
  revappl_swamp :: "'c \<times> 'a \<Rightarrow> ('a \<Rightarrow> 'd \<times> 'b) \<Rightarrow> ('c \<times> 'd) \<times> 'b" (infixl "|\<triangleright>\<triangleright>" 55)
  revappl_swamp_split: "z |\<triangleright>\<triangleright> f = ((fst z, fst (f (snd z))), snd (f (snd z)))"
  revappl_uncurry :: "'c \<times> 'a \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixl "\<turnstile>\<triangleright>" 55)
  revappl_uncurry_split: "z \<turnstile>\<triangleright> f = f (fst z) (snd z)"


subsection {* lemmas *}

lemma revappl_snd_def [code]:
  "(y, x) |\<triangleright> f = (y, f x)" unfolding revappl_snd_split by simp

lemma revappl_swamp_def [code]:
  "(y, x) |\<triangleright>\<triangleright> f = (let (z, w) = f x in ((y, z), w))" unfolding Let_def revappl_swamp_split split_def by simp

lemma revappl_uncurry_def [code]:
  "(y, x) \<turnstile>\<triangleright> f = f y x" unfolding revappl_uncurry_split by simp

lemmas revappl = revappl_def revappl_snd_def revappl_swamp_def revappl_uncurry_def

lemmas revappl_split = revappl_def revappl_snd_split revappl_swamp_split revappl_uncurry_split

end