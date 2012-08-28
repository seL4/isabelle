(*  Title:      Codatatype_Examples/TreeFsetI.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finitely branching possibly infinite trees, with sets of children.
*)

header {* Finitely Branching Possibly Infinite Trees, with Sets of Children *}

theory TreeFsetI
imports "../Codatatype"
begin

definition pair_fun (infixr "\<odot>" 50) where
  "f \<odot> g \<equiv> \<lambda>x. (f x, g x)"

bnf_codata treeFsetI: 't = "'a \<times> 't fset"

(* selectors for trees *)
definition "lab t \<equiv> fst (treeFsetI_unf t)"
definition "sub t \<equiv> snd (treeFsetI_unf t)"

lemma unf[simp]: "treeFsetI_unf t = (lab t, sub t)"
unfolding lab_def sub_def by simp

lemma coiter_pair_fun_lab: "lab (treeFsetI_coiter (f \<odot> g) t) = f t"
unfolding lab_def pair_fun_def treeFsetI.coiter treeFsetIBNF_map_def by simp

lemma coiter_pair_fun_sub: "sub (treeFsetI_coiter (f \<odot> g) t) = map_fset (treeFsetI_coiter (f \<odot> g)) (g t)"
unfolding sub_def pair_fun_def treeFsetI.coiter treeFsetIBNF_map_def by simp

(* tree map (contrived example): *)
definition "tmap f \<equiv> treeFsetI_coiter (f o lab \<odot> sub)"

lemma tmap_simps1[simp]: "lab (tmap f t) = f (lab t)"
unfolding tmap_def by (simp add: coiter_pair_fun_lab)

lemma trev_simps2[simp]: "sub (tmap f t) = map_fset (tmap f) (sub t)"
unfolding tmap_def by (simp add: coiter_pair_fun_sub)

lemma treeFsetIBNF_pred[simp]: "treeFsetIBNF_pred R1 R2 a b = (R1 (fst a) (fst b) \<and>
  (\<forall>t \<in> fset (snd a). (\<exists>u \<in> fset (snd b). R2 t u)) \<and>
  (\<forall>t \<in> fset (snd b). (\<exists>u \<in> fset (snd a). R2 u t)))"
apply (cases a)
apply (cases b)
apply (simp add: treeFsetIBNF.pred_unfold)
done

lemmas treeFsetI_coind = mp[OF treeFsetI.pred_coinduct]

lemma "tmap (f o g) x = tmap f (tmap g x)"
by (intro treeFsetI_coind[where phi="%x1 x2. \<exists>x. x1 = tmap (f o g) x \<and> x2 = tmap f (tmap g x)"])
   force+

end
