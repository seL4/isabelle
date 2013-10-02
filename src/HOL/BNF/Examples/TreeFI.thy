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

(* Tree reverse:*)
primcorec trev where
  "lab (trev t) = lab t"
| "sub (trev t) = mapF trev (lrev (sub t))"

lemma treeFI_coinduct:
  assumes *: "phi x y"
  and step: "\<And>a b. phi a b \<Longrightarrow>
     lab a = lab b \<and>
     lengthh (sub a) = lengthh (sub b) \<and>
     (\<forall>i < lengthh (sub a). phi (nthh (sub a) i) (nthh (sub b) i))"
  shows "x = y"
using * proof (coinduction arbitrary: x y)
  case (Eq_treeFI t1 t2)
  from conjunct1[OF conjunct2[OF step[OF Eq_treeFI]]] conjunct2[OF conjunct2[OF step[OF Eq_treeFI]]]
  have "relF phi (sub t1) (sub t2)"
  proof (induction "sub t1" "sub t2" arbitrary: t1 t2 rule: listF_induct2)
    case (Conss x xs y ys)
    note sub = Conss(2,3)[symmetric] and phi = mp[OF spec[OF Conss(4)], unfolded sub]
      and IH = Conss(1)[of "Tree (lab t1) (tlF (sub t1))" "Tree (lab t2) (tlF (sub t2))",
        unfolded sub, simplified]
    from phi[of 0] show ?case unfolding sub by (auto intro!: IH dest: phi[simplified, OF Suc_mono])
  qed simp
  with conjunct1[OF step[OF Eq_treeFI]] show ?case by simp
qed

lemma trev_trev: "trev (trev tr) = tr"
  by (coinduction arbitrary: tr rule: treeFI_coinduct) auto

end
