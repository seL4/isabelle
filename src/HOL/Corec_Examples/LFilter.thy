(*  Title:      HOL/Corec_Examples/LFilter.thy
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Dmitriy Traytel, ETH Zuerich
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2014, 2016

The filter function on lazy lists.
*)

section \<open>The Filter Function on Lazy Lists\<close>

theory LFilter
imports "HOL-Library.BNF_Corec"
begin

codatatype (lset: 'a) llist =
  LNil
| LCons (lhd: 'a) (ltl: "'a llist")

corecursive lfilter where
  "lfilter P xs = (if \<forall>x \<in> lset xs. \<not> P x then
    LNil
    else if P (lhd xs) then
      LCons (lhd xs) (lfilter P (ltl xs))
    else
      lfilter P (ltl xs))"
proof (relation "measure (\<lambda>(P, xs). LEAST n. P (lhd ((ltl ^^ n) xs)))", rule wf_measure, clarsimp)
  fix P xs x
  assume "x \<in> lset xs" "P x" "\<not> P (lhd xs)"
  from this(1,2) obtain a where "P (lhd ((ltl ^^ a) xs))"
    by (atomize_elim, induct x xs rule: llist.set_induct)
       (auto simp: funpow_Suc_right simp del: funpow.simps(2) intro: exI[of _ 0] exI[of _ "Suc i" for i])
  with \<open>\<not> P (lhd xs)\<close>
    have "(LEAST n. P (lhd ((ltl ^^ n) xs))) = Suc (LEAST n. P (lhd ((ltl ^^ Suc n) xs)))"
    by (intro Least_Suc) auto
  then show "(LEAST n. P (lhd ((ltl ^^ n) (ltl xs)))) < (LEAST n. P (lhd ((ltl ^^ n) xs)))"
    by (simp add: funpow_swap1[of ltl])
qed

lemma lfilter_LNil [simp]: "lfilter P LNil = LNil"
  by(simp add: lfilter.code)

lemma lnull_lfilter [simp]: "lfilter P xs = LNil \<longleftrightarrow> (\<forall>x \<in> lset xs. \<not> P x)"
proof(rule iffI ballI)+
  show "\<not> P x" if "x \<in> lset xs" "lfilter P xs = LNil" for x using that
    by(induction rule: llist.set_induct)(subst (asm) lfilter.code; auto split: if_split_asm; fail)+
qed(simp add: lfilter.code)

lemma lfilter_LCons [simp]: "lfilter P (LCons x xs) = (if P x then LCons x (lfilter P xs) else lfilter P xs)"
  by(subst lfilter.code)(auto intro: sym)

lemma llist_in_lfilter [simp]: "lset (lfilter P xs) = lset xs \<inter> {x. P x}"
proof(intro set_eqI iffI)
  show "x \<in> lset xs \<inter> {x. P x}" if "x \<in> lset (lfilter P xs)" for x using that
  proof(induction ys\<equiv>"lfilter P xs" arbitrary: xs rule: llist.set_induct)
    case (LCons1 x xs ys)
    from this show ?case
      apply(induction arg\<equiv>"(P, ys)" arbitrary: ys rule: lfilter.inner_induct)
      subgoal by(subst (asm) (2) lfilter.code)(auto split: if_split_asm elim: llist.set_cases)
      done
  next
    case (LCons2 xs y x ys)
    from LCons2(3) LCons2(1) show ?case
      apply(induction arg\<equiv>"(P, ys)" arbitrary: ys rule: lfilter.inner_induct)
      subgoal using LCons2(2) by(subst (asm) (2) lfilter.code)(auto split: if_split_asm elim: llist.set_cases)
      done
  qed
  show "x \<in> lset (lfilter P xs)" if "x \<in> lset xs \<inter> {x. P x}" for x
    using that[THEN IntD1] that[THEN IntD2] by(induction) auto
qed

lemma lfilter_unique_weak:
  "(\<And>xs. f xs = (if \<forall>x \<in> lset xs. \<not> P x then LNil
    else if P (lhd xs) then LCons (lhd xs) (f (ltl xs))
    else lfilter P (ltl xs)))
   \<Longrightarrow> f = lfilter P"
  by(corec_unique)(rule ext lfilter.code)+

lemma lfilter_unique:
  assumes "\<And>xs. f xs = (if \<forall>x\<in>lset xs. \<not> P x then LNil
    else if P (lhd xs) then LCons (lhd xs) (f (ltl xs))
    else f (ltl xs))"
  shows "f = lfilter P"
\<comment> \<open>It seems as if we cannot use @{thm lfilter_unique_weak} for showing this as the induction and the coinduction must be nested\<close>
proof(rule ext)
  show "f xs = lfilter P xs" for xs
  proof(coinduction arbitrary: xs)
    case (Eq_llist xs)
    show ?case
      apply(induction arg\<equiv>"(P, xs)" arbitrary: xs rule: lfilter.inner_induct)
      apply(subst (1 2 3 4) assms)
      apply(subst (1 2 3 4) lfilter.code)
      apply auto
      done
  qed
qed

lemma lfilter_lfilter: "lfilter P \<circ> lfilter Q = lfilter (\<lambda>x. P x \<and> Q x)"
  by(rule lfilter_unique)(auto elim: llist.set_cases)

end
