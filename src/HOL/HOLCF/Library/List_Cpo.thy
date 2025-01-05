(*  Title:      HOL/HOLCF/Library/List_Cpo.thy
    Author:     Brian Huffman
*)

section \<open>Lists as a complete partial order\<close>

theory List_Cpo
imports HOLCF
begin

subsection \<open>Lists are a partial order\<close>

instantiation list :: (po) po
begin

definition
  "xs \<sqsubseteq> ys \<longleftrightarrow> list_all2 (\<sqsubseteq>) xs ys"

instance
proof
  fix xs ys zs :: "'a list"
  show "xs \<sqsubseteq> xs"
    using below_refl 
    unfolding below_list_def
    by (rule list_all2_refl)
  show "xs \<sqsubseteq> ys \<Longrightarrow> ys \<sqsubseteq> zs \<Longrightarrow> xs \<sqsubseteq> zs"
    using below_trans 
    unfolding below_list_def
    by (rule list_all2_trans)
  show "xs \<sqsubseteq> ys \<Longrightarrow> ys \<sqsubseteq> xs \<Longrightarrow> xs = ys"
    using below_antisym
    unfolding below_list_def
    by (rule list_all2_antisym)
qed

end

lemma below_list_simps [simp]:
  "[] \<sqsubseteq> []"
  "x # xs \<sqsubseteq> y # ys \<longleftrightarrow> x \<sqsubseteq> y \<and> xs \<sqsubseteq> ys"
  "\<not> [] \<sqsubseteq> y # ys"
  "\<not> x # xs \<sqsubseteq> []"
by (simp_all add: below_list_def)

lemma Nil_below_iff [simp]: "[] \<sqsubseteq> xs \<longleftrightarrow> xs = []"
by (cases xs, simp_all)

lemma below_Nil_iff [simp]: "xs \<sqsubseteq> [] \<longleftrightarrow> xs = []"
by (cases xs, simp_all)

lemma list_below_induct [consumes 1, case_names Nil Cons]:
  assumes "xs \<sqsubseteq> ys"
  assumes 1: "P [] []"
  assumes 2: "\<And>x y xs ys. \<lbrakk>x \<sqsubseteq> y; xs \<sqsubseteq> ys; P xs ys\<rbrakk> \<Longrightarrow> P (x # xs) (y # ys)"
  shows "P xs ys"
using \<open>xs \<sqsubseteq> ys\<close>
proof (induct xs arbitrary: ys)
  case Nil thus ?case by (simp add: 1)
next
  case (Cons x xs) thus ?case by (cases ys, simp_all add: 2)
qed

lemma list_below_cases:
  assumes "xs \<sqsubseteq> ys"
  obtains "xs = []" and "ys = []" |
    x y xs' ys' where "xs = x # xs'" and "ys = y # ys'"
using assms by (cases xs, simp, cases ys, auto)

text "Thanks to Joachim Breitner"

lemma list_Cons_below:
  assumes "a # as \<sqsubseteq> xs"
  obtains b and bs where "a \<sqsubseteq> b" and "as \<sqsubseteq> bs" and "xs = b # bs"
  using assms by (cases xs, auto)

lemma list_below_Cons:
  assumes "xs \<sqsubseteq> b # bs"
  obtains a and as where "a \<sqsubseteq> b" and "as \<sqsubseteq> bs" and "xs = a # as"
  using assms by (cases xs, auto)

lemma hd_mono: "xs \<sqsubseteq> ys \<Longrightarrow> hd xs \<sqsubseteq> hd ys"
by (cases xs, simp, cases ys, simp, simp)

lemma tl_mono: "xs \<sqsubseteq> ys \<Longrightarrow> tl xs \<sqsubseteq> tl ys"
by (cases xs, simp, cases ys, simp, simp)

lemma ch2ch_hd [simp]: "chain (\<lambda>i. S i) \<Longrightarrow> chain (\<lambda>i. hd (S i))"
by (rule chainI, rule hd_mono, erule chainE)

lemma ch2ch_tl [simp]: "chain (\<lambda>i. S i) \<Longrightarrow> chain (\<lambda>i. tl (S i))"
by (rule chainI, rule tl_mono, erule chainE)

lemma below_same_length: "xs \<sqsubseteq> ys \<Longrightarrow> length xs = length ys"
unfolding below_list_def by (rule list_all2_lengthD)

lemma list_chain_induct [consumes 1, case_names Nil Cons]:
  assumes "chain S"
  assumes 1: "P (\<lambda>i. [])"
  assumes 2: "\<And>A B. chain A \<Longrightarrow> chain B \<Longrightarrow> P B \<Longrightarrow> P (\<lambda>i. A i # B i)"
  shows "P S"
using \<open>chain S\<close>
proof (induct "S 0" arbitrary: S)
  case Nil
  have "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono [OF \<open>chain S\<close>])
  with Nil have "\<forall>i. S i = []" by simp
  thus ?case by (simp add: 1)
next
  case (Cons x xs)
  have "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono [OF \<open>chain S\<close>])
  hence *: "\<forall>i. S i \<noteq> []" by (rule all_forward, insert Cons) auto
  have "chain (\<lambda>i. hd (S i))" and "chain (\<lambda>i. tl (S i))"
    using \<open>chain S\<close> by simp_all
  moreover have "P (\<lambda>i. tl (S i))"
    using \<open>chain S\<close> and \<open>x # xs = S 0\<close> [symmetric]
    by (simp add: Cons(1))
  ultimately have "P (\<lambda>i. hd (S i) # tl (S i))"
    by (rule 2)
  thus "P S" by (simp add: *)
qed

lemma list_chain_cases:
  assumes S: "chain S"
  obtains "S = (\<lambda>i. [])" |
    A B where "chain A" and "chain B" and "S = (\<lambda>i. A i # B i)"
using S by (induct rule: list_chain_induct) simp_all

subsection \<open>Lists are a complete partial order\<close>

lemma is_lub_Cons:
  assumes A: "range A <<| x"
  assumes B: "range B <<| xs"
  shows "range (\<lambda>i. A i # B i) <<| x # xs"
using assms
unfolding is_lub_def is_ub_def
by (clarsimp, case_tac u, simp_all)

instance list :: (cpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a list"
  assume "chain S"
  then show "\<exists>x. range S <<| x"
  proof (induct rule: list_chain_induct)
    case Nil
    have "{[]} <<| []"
      by simp
    then obtain x :: "'a list" where "{[]} <<| x" ..
    then show ?case
      by auto
  next
    case (Cons A B) then show ?case
      by (auto intro: is_lub_Cons cpo_lubI)
  qed
qed

subsection \<open>Continuity of list operations\<close>

lemma cont2cont_Cons [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x # g x)"
apply (rule contI)
apply (rule is_lub_Cons)
apply (erule contE [OF f])
apply (erule contE [OF g])
done

lemma lub_Cons:
  fixes A :: "nat \<Rightarrow> 'a::cpo"
  assumes A: "chain A" and B: "chain B"
  shows "(\<Squnion>i. A i # B i) = (\<Squnion>i. A i) # (\<Squnion>i. B i)"
by (intro lub_eqI is_lub_Cons cpo_lubI A B)

lemma cont2cont_case_list:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h1: "\<And>y ys. cont (\<lambda>x. h x y ys)"
  assumes h2: "\<And>x ys. cont (\<lambda>y. h x y ys)"
  assumes h3: "\<And>x y. cont (\<lambda>ys. h x y ys)"
  shows "cont (\<lambda>x. case f x of [] \<Rightarrow> g x | y # ys \<Rightarrow> h x y ys)"
apply (rule cont_apply [OF f])
apply (rule contI)
apply (erule list_chain_cases)
apply (simp add: is_lub_const)
apply (simp add: lub_Cons)
apply (simp add: cont2contlubE [OF h2])
apply (simp add: cont2contlubE [OF h3])
apply (simp add: diag_lub ch2ch_cont [OF h2] ch2ch_cont [OF h3])
apply (rule cpo_lubI, rule chainI, rule below_trans)
apply (erule cont2monofunE [OF h2 chainE])
apply (erule cont2monofunE [OF h3 chainE])
apply (case_tac y, simp_all add: g h1)
done

lemma cont2cont_case_list' [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h: "cont (\<lambda>p. h (fst p) (fst (snd p)) (snd (snd p)))"
  shows "cont (\<lambda>x. case f x of [] \<Rightarrow> g x | y # ys \<Rightarrow> h x y ys)"
using assms by (simp add: cont2cont_case_list prod_cont_iff)

text \<open>The simple version (due to Joachim Breitner) is needed if the
  element type of the list is not a cpo.\<close>

lemma cont2cont_case_list_simple [simp, cont2cont]:
  assumes "cont (\<lambda>x. f1 x)"
  assumes "\<And>y ys. cont (\<lambda>x. f2 x y ys)"
  shows "cont (\<lambda>x. case l of [] \<Rightarrow> f1 x | y # ys \<Rightarrow> f2 x y ys)"
using assms by (cases l) auto

text \<open>Lemma for proving continuity of recursive list functions:\<close>

lemma list_contI:
  fixes f :: "'a::cpo list \<Rightarrow> 'b::cpo"
  assumes f: "\<And>x xs. f (x # xs) = g x xs (f xs)"
  assumes g1: "\<And>xs y. cont (\<lambda>x. g x xs y)"
  assumes g2: "\<And>x y. cont (\<lambda>xs. g x xs y)"
  assumes g3: "\<And>x xs. cont (\<lambda>y. g x xs y)"
  shows "cont f"
proof (rule contI2)
  obtain h where h: "\<And>x xs y. g x xs y = h\<cdot>x\<cdot>xs\<cdot>y"
  proof
    fix x xs y show "g x xs y = (\<Lambda> x xs y. g x xs y)\<cdot>x\<cdot>xs\<cdot>y"
    by (simp add: cont2cont_LAM g1 g2 g3)
  qed
  show mono: "monofun f"
    apply (rule monofunI)
    apply (erule list_below_induct)
    apply simp
    apply (simp add: f h monofun_cfun)
    done
  fix Y :: "nat \<Rightarrow> 'a list"
  assume "chain Y" thus "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
    apply (induct rule: list_chain_induct)
    apply simp
    apply (simp add: lub_Cons f h)
    apply (simp add: lub_APP ch2ch_monofun [OF mono])
    apply (simp add: monofun_cfun)
    done
qed

text \<open>Continuity rule for map\<close>

lemma cont2cont_map [simp, cont2cont]:
  assumes f: "cont (\<lambda>(x, y). f x y)"
  assumes g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. map (\<lambda>y. f x y) (g x))"
using f
apply (simp add: prod_cont_iff)
apply (rule cont_apply [OF g])
apply (rule list_contI, rule list.map, simp, simp, simp)
apply (induct_tac y, simp, simp)
done

text \<open>There are probably lots of other list operations that also
deserve to have continuity lemmas.  I'll add more as they are
needed.\<close>

subsection \<open>Lists are a discrete cpo\<close>

instance list :: (discrete_cpo) discrete_cpo
proof
  fix xs ys :: "'a list"
  show "xs \<sqsubseteq> ys \<longleftrightarrow> xs = ys"
    by (induct xs arbitrary: ys, case_tac [!] ys, simp_all)
qed

subsection \<open>Compactness and chain-finiteness\<close>

lemma compact_Nil [simp]: "compact []"
apply (rule compactI2)
apply (erule list_chain_cases)
apply simp
apply (simp add: lub_Cons)
done

lemma compact_Cons: "\<lbrakk>compact x; compact xs\<rbrakk> \<Longrightarrow> compact (x # xs)"
apply (rule compactI2)
apply (erule list_chain_cases)
apply (auto simp add: lub_Cons dest!: compactD2)
apply (rename_tac i j, rule_tac x="max i j" in exI)
apply (drule (1) below_trans [OF _ chain_mono [OF _ max.cobounded1]])
apply (drule (1) below_trans [OF _ chain_mono [OF _ max.cobounded2]])
apply (erule (1) conjI)
done

lemma compact_Cons_iff [simp]:
  "compact (x # xs) \<longleftrightarrow> compact x \<and> compact xs"
apply (safe intro!: compact_Cons)
apply (simp only: compact_def)
apply (subgoal_tac "cont (\<lambda>x. x # xs)")
apply (drule (1) adm_subst, simp, simp)
apply (simp only: compact_def)
apply (subgoal_tac "cont (\<lambda>xs. x # xs)")
apply (drule (1) adm_subst, simp, simp)
done

instance list :: (chfin) chfin
proof
  fix Y :: "nat \<Rightarrow> 'a list" assume "chain Y"
  moreover have "\<And>(xs::'a list). compact xs"
    by (induct_tac xs, simp_all)
  ultimately show "\<exists>i. max_in_chain i Y"
    by (rule compact_imp_max_in_chain)
qed

subsection \<open>Using lists with fixrec\<close>

definition
  match_Nil :: "'a::cpo list \<rightarrow> 'b match \<rightarrow> 'b match"
where
  "match_Nil = (\<Lambda> xs k. case xs of [] \<Rightarrow> k | y # ys \<Rightarrow> Fixrec.fail)"

definition
  match_Cons :: "'a::cpo list \<rightarrow> ('a \<rightarrow> 'a list \<rightarrow> 'b match) \<rightarrow> 'b match"
where
  "match_Cons = (\<Lambda> xs k. case xs of [] \<Rightarrow> Fixrec.fail | y # ys \<Rightarrow> k\<cdot>y\<cdot>ys)"

lemma match_Nil_simps [simp]:
  "match_Nil\<cdot>[]\<cdot>k = k"
  "match_Nil\<cdot>(x # xs)\<cdot>k = Fixrec.fail"
unfolding match_Nil_def by simp_all

lemma match_Cons_simps [simp]:
  "match_Cons\<cdot>[]\<cdot>k = Fixrec.fail"
  "match_Cons\<cdot>(x # xs)\<cdot>k = k\<cdot>x\<cdot>xs"
unfolding match_Cons_def by simp_all

setup \<open>
  Fixrec.add_matchers
    [ (\<^const_name>\<open>Nil\<close>, \<^const_name>\<open>match_Nil\<close>),
      (\<^const_name>\<open>Cons\<close>, \<^const_name>\<open>match_Cons\<close>) ]
\<close>

end
