(*  Title:      HOL/BNF/Examples/TreeFI.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finitely branching possibly infinite trees.
*)

header {* Finitely Branching Possibly Infinite Trees *}

theory TreeFI
imports ListF
begin

codatatype 'a treeFI = Tree (lab: 'a) (sub: "'a treeFI listF")

definition pair_fun (infixr "\<odot>" 50) where
  "f \<odot> g \<equiv> \<lambda>x. (f x, g x)"

(* Tree reverse:*)
definition "trev \<equiv> treeFI_unfold lab (lrev o sub)"

lemma trev_simps1[simp]: "lab (trev t) = lab t"
  unfolding trev_def by simp

lemma trev_simps2[simp]: "sub (trev t) = mapF trev (lrev (sub t))"
  unfolding trev_def by simp

lemma treeFI_coinduct:
  assumes *: "phi x y"
  and step: "\<And>a b. phi a b \<Longrightarrow>
     lab a = lab b \<and>
     lengthh (sub a) = lengthh (sub b) \<and>
     (\<forall>i < lengthh (sub a). phi (nthh (sub a) i) (nthh (sub b) i))"
  shows "x = y"
using * proof (coinduct rule: treeFI.coinduct)
  fix t1 t2 assume "phi t1 t2" note * = step[OF this] and ** = conjunct2[OF *]
  from conjunct1[OF **] conjunct2[OF **] have "relF phi (sub t1) (sub t2)"
  proof (induction "sub t1" "sub t2" arbitrary: t1 t2 rule: listF_induct2)
    case (Conss x xs y ys)
    note sub = Conss(2,3)[symmetric] and phi = mp[OF spec[OF Conss(4)], unfolded sub]
      and IH = Conss(1)[of "Tree (lab t1) (tlF (sub t1))" "Tree (lab t2) (tlF (sub t2))",
        unfolded sub, simplified]
    from phi[of 0] show ?case unfolding sub by (auto intro!: IH dest: phi[simplified, OF Suc_mono])
  qed simp
  with conjunct1[OF *] show "lab t1 = lab t2 \<and> relF phi (sub t1) (sub t2)" ..
qed

lemma trev_trev: "trev (trev tr) = tr"
  by (rule treeFI_coinduct[of "%a b. trev (trev b) = a"]) auto

end
