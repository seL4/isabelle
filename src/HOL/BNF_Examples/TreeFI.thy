(*  Title:      HOL/BNF_Examples/TreeFI.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finitely branching possibly infinite trees.
*)

header {* Finitely Branching Possibly Infinite Trees *}

theory TreeFI
imports Main
begin

codatatype 'a treeFI = Tree (lab: 'a) (sub: "'a treeFI list")

(* Tree reverse:*)
primcorec trev where
  "lab (trev t) = lab t"
| "sub (trev t) = map trev (rev (sub t))"

lemma treeFI_coinduct:
  assumes *: "phi x y"
  and step: "\<And>a b. phi a b \<Longrightarrow>
     lab a = lab b \<and>
     length (sub a) = length (sub b) \<and>
     (\<forall>i < length (sub a). phi (nth (sub a) i) (nth (sub b) i))"
  shows "x = y"
using * proof (coinduction arbitrary: x y)
  case (Eq_treeFI t1 t2)
  from conjunct1[OF conjunct2[OF step[OF Eq_treeFI]]] conjunct2[OF conjunct2[OF step[OF Eq_treeFI]]]
  have "list_all2 phi (sub t1) (sub t2)"
  proof (induction "sub t1" "sub t2" arbitrary: t1 t2 rule: list_induct2)
    case (Cons x xs y ys)
    note sub = Cons(3,4)[symmetric] and phi = mp[OF spec[OF Cons(5)], unfolded sub]
      and IH = Cons(2)[of "Tree (lab t1) (tl (sub t1))" "Tree (lab t2) (tl (sub t2))",
        unfolded sub, simplified]
    from phi[of 0] show ?case unfolding sub by (auto intro!: IH dest: phi[simplified, OF Suc_mono])
  qed simp
  with conjunct1[OF step[OF Eq_treeFI]] show ?case by simp
qed

lemma trev_trev: "trev (trev tr) = tr"
  by (coinduction arbitrary: tr rule: treeFI_coinduct) (auto simp add: rev_map)

end
