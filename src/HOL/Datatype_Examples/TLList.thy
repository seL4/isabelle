section \<open>Terminated Lazy Lists as Quotients of Lazy Lists\<close>

text \<open>
This file demonstrates the lift_bnf utility for quotients on the example of lazy lists.

See the Coinductive AFP entry for a much more extensive library
of (terminated) lazy lists.
\<close>

theory TLList
imports Main
begin

codatatype (lset: 'a) llist = LNil | LCons 'a "'a llist"
  for map: lmap rel: lrel

inductive lfinite where
  LNil: "lfinite LNil"
| LCons: "\<And>x xs. lfinite xs \<Longrightarrow> lfinite (LCons x xs)"

lemma lfinite_lmapI: "lfinite xs \<Longrightarrow> lfinite (lmap f xs)"
  by (induct xs rule: lfinite.induct) (auto intro: lfinite.intros)

lemma lfinite_lmapD: "lfinite (lmap f xs) \<Longrightarrow> lfinite xs"
proof (induct "lmap f xs" arbitrary: xs rule: lfinite.induct)
  case LNil
  then show ?case
    by (cases xs) (auto intro: lfinite.intros)
next
  case (LCons y ys)
  then show ?case
    by (cases xs) (auto intro: lfinite.intros)
qed

lemma lfinite_lmap[simp]: "lfinite (lmap f xs) = lfinite xs"
  by (metis lfinite_lmapI lfinite_lmapD)

lemma lfinite_lrel: "lfinite xs \<Longrightarrow> lrel R xs ys \<Longrightarrow> lfinite ys"
proof (induct xs arbitrary: ys rule: lfinite.induct)
  case LNil
  then show ?case
    by (cases ys) (auto intro: lfinite.intros)
next
  case (LCons x xs)
  then show ?case
    by (cases ys) (auto intro: lfinite.intros)
      qed

lemma lfinite_lrel': "lfinite ys \<Longrightarrow> lrel R xs ys \<Longrightarrow> lfinite xs"
  using lfinite_lrel llist.rel_flip by blast

lemma lfinite_lrel_eq:
   "lrel R xs ys \<Longrightarrow> lfinite xs = lfinite ys"
  using lfinite_lrel lfinite_lrel' by blast+

definition eq_tllist where
  "eq_tllist p q = (fst p = fst q \<and> (if lfinite (fst p) then snd p = snd q else True))"

quotient_type ('a, 'b) tllist = "'a llist \<times> 'b" / eq_tllist
  apply (rule equivpI)
    apply (rule reflpI; auto simp: eq_tllist_def)
   apply (rule sympI; auto simp: eq_tllist_def)
  apply (rule transpI; auto simp: eq_tllist_def)
  done

primcorec lconst where
  "lconst a = LCons a (lconst a)"

lemma lfinite_lconst[simp]: "\<not> lfinite (lconst a)"
proof
  assume "lfinite (lconst a)"
  then show "False"
  apply (induct "lconst a" rule: lfinite.induct)
  subgoal by (subst (asm) lconst.code) auto
  subgoal by (subst (asm) (2) lconst.code) auto
  done
qed

lemma lset_lconst: "x \<in> lset (lconst b) \<Longrightarrow> x = b"
  apply (induct x "lconst b" arbitrary: b rule: llist.set_induct)
  subgoal by (subst (asm) lconst.code) auto
  subgoal by (subst (asm) (2) lconst.code) auto
  done

lift_bnf (tlset1: 'a, tlset2: 'b) tllist
  [wits: "\<lambda>a. (lconst a, undefined)" ]
  for map: tlmap rel: tlrel
  subgoal for P Q P' Q'
    by (force simp: eq_tllist_def relcompp_apply llist.rel_compp lfinite_lrel_eq split: if_splits)
  subgoal for Ss
    by (auto simp: eq_tllist_def)
  subgoal for Ss
    apply (auto 0 0 simp: eq_tllist_def)
    by metis
  subgoal for x b
    by (auto simp: eq_tllist_def llist.set_map dest: lset_lconst split: if_splits)
  subgoal for x b
    by (auto simp: eq_tllist_def sum_set_defs split: if_splits sum.splits)
  done

lift_definition TLNil :: "'b \<Rightarrow> ('a, 'b) tllist" is "\<lambda>b. (LNil, b)" .
lift_definition TLCons :: "'a \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist" is "\<lambda>x (xs, b). (LCons x xs, b)"
  by (auto simp: eq_tllist_def split: if_splits elim: lfinite.cases)

lemma lfinite_LCons: "lfinite (LCons x xs) = lfinite xs"
  using lfinite.simps by auto

lemmas lfinite_simps[simp] = lfinite.LNil lfinite_LCons

lemma tlset_TLNil: "tlset1 (TLNil b) = {}" "tlset2 (TLNil b) = {b}"
  by (transfer; auto simp: eq_tllist_def split: if_splits)+

lemma tlset_TLCons: "tlset1 (TLCons x xs) = {x} \<union> tlset1 xs" "tlset2 (TLCons x xs) = tlset2 xs"
  by (transfer; auto simp: eq_tllist_def split: if_splits)+

lift_definition tlfinite :: "('a, 'b) tllist \<Rightarrow> bool" is "\<lambda>(xs, _). lfinite xs"
  by (auto simp: eq_tllist_def)

lemma tlfinite_tlset2: "tlfinite xs \<Longrightarrow> tlset2 xs \<noteq> {}"
  apply (transfer, safe)
  subgoal for xs b
    by (induct xs rule: lfinite.induct) (auto simp: eq_tllist_def setr.simps)
  done

lemma tlfinite_tlset2': "b \<in> tlset2 xs \<Longrightarrow> tlfinite xs"
  by (transfer fixing: b, auto simp: eq_tllist_def setr.simps split: if_splits)

lemma "\<not> tlfinite xs \<Longrightarrow> tlset2 xs = {}"
  by (meson equals0I tlfinite_tlset2')

end