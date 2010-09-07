(*  Title:      HOLCF/Library/List_Cpo.thy
    Author:     Brian Huffman
*)

header {* Lists as a complete partial order *}

theory List_Cpo
imports HOLCF
begin

subsection {* Lists are a partial order *}

instantiation list :: (po) po
begin

definition
  "xs \<sqsubseteq> ys \<longleftrightarrow> list_all2 (op \<sqsubseteq>) xs ys"

instance proof
  fix xs :: "'a list"
  from below_refl show "xs \<sqsubseteq> xs"
    unfolding below_list_def
    by (rule list_all2_refl)
next
  fix xs ys zs :: "'a list"
  assume "xs \<sqsubseteq> ys" and "ys \<sqsubseteq> zs"
  with below_trans show "xs \<sqsubseteq> zs"
    unfolding below_list_def
    by (rule list_all2_trans)
next
  fix xs ys zs :: "'a list"
  assume "xs \<sqsubseteq> ys" and "ys \<sqsubseteq> xs"
  with below_antisym show "xs = ys"
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

lemma list_chain_cases:
  assumes S: "chain S"
  obtains "\<forall>i. S i = []" |
    A B where "chain A" and "chain B" and "\<forall>i. S i = A i # B i"
proof (cases "S 0")
  case Nil
  have "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono [OF S])
  with Nil have "\<forall>i. S i = []" by simp
  thus ?thesis ..
next
  case (Cons x xs)
  have "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono [OF S])
  hence *: "\<forall>i. S i \<noteq> []" by (rule all_forward) (auto simp add: Cons)
  let ?A = "\<lambda>i. hd (S i)"
  let ?B = "\<lambda>i. tl (S i)"
  from S have "chain ?A" and "chain ?B" by simp_all
  moreover have "\<forall>i. S i = ?A i # ?B i" by (simp add: *)
  ultimately show ?thesis ..
qed

subsection {* Lists are a complete partial order *}

lemma is_lub_Cons:
  assumes A: "range A <<| x"
  assumes B: "range B <<| xs"
  shows "range (\<lambda>i. A i # B i) <<| x # xs"
using assms
unfolding is_lub_def is_ub_def Ball_def [symmetric]
by (clarsimp, case_tac u, simp_all)

lemma list_cpo_lemma:
  fixes S :: "nat \<Rightarrow> 'a::cpo list"
  assumes "chain S" and "\<forall>i. length (S i) = n"
  shows "\<exists>x. range S <<| x"
using assms
 apply (induct n arbitrary: S)
  apply (subgoal_tac "S = (\<lambda>i. [])")
  apply (fast intro: lub_const)
  apply (simp add: ext_iff)
 apply (drule_tac x="\<lambda>i. tl (S i)" in meta_spec, clarsimp)
 apply (rule_tac x="(\<Squnion>i. hd (S i)) # x" in exI)
 apply (subgoal_tac "range (\<lambda>i. hd (S i) # tl (S i)) = range S")
  apply (erule subst)
  apply (rule is_lub_Cons)
   apply (rule thelubE [OF _ refl])
   apply (erule ch2ch_hd)
  apply assumption
 apply (rule_tac f="\<lambda>S. range S" in arg_cong)
 apply (rule ext)
 apply (rule hd_Cons_tl)
 apply (drule_tac x=i in spec, auto)
done

instance list :: (cpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a list"
  assume "chain S"
  hence "\<forall>i. S 0 \<sqsubseteq> S i" by (simp add: chain_mono)
  hence "\<forall>i. length (S i) = length (S 0)"
    by (fast intro: below_same_length [symmetric])
  with `chain S` show "\<exists>x. range S <<| x"
    by (rule list_cpo_lemma)
qed

subsection {* Continuity of list operations *}

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
by (intro thelubI is_lub_Cons cpo_lubI A B)

lemma cont2cont_list_case:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h1: "\<And>y ys. cont (\<lambda>x. h x y ys)"
  assumes h2: "\<And>x ys. cont (\<lambda>y. h x y ys)"
  assumes h3: "\<And>x y. cont (\<lambda>ys. h x y ys)"
  shows "cont (\<lambda>x. case f x of [] \<Rightarrow> g x | y # ys \<Rightarrow> h x y ys)"
apply (rule cont_apply [OF f])
apply (rule contI)
apply (erule list_chain_cases)
apply (simp add: lub_const)
apply (simp add: lub_Cons)
apply (simp add: cont2contlubE [OF h2])
apply (simp add: cont2contlubE [OF h3])
apply (simp add: diag_lub ch2ch_cont [OF h2] ch2ch_cont [OF h3])
apply (rule cpo_lubI, rule chainI, rule below_trans)
apply (erule cont2monofunE [OF h2 chainE])
apply (erule cont2monofunE [OF h3 chainE])
apply (case_tac y, simp_all add: g h1)
done

lemma cont2cont_list_case' [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h: "cont (\<lambda>p. h (fst p) (fst (snd p)) (snd (snd p)))"
  shows "cont (\<lambda>x. case f x of [] \<Rightarrow> g x | y # ys \<Rightarrow> h x y ys)"
proof -
  have "\<And>y ys. cont (\<lambda>x. h x (fst (y, ys)) (snd (y, ys)))"
    by (rule h [THEN cont_fst_snd_D1])
  hence h1: "\<And>y ys. cont (\<lambda>x. h x y ys)" by simp
  note h2 = h [THEN cont_fst_snd_D2, THEN cont_fst_snd_D1]
  note h3 = h [THEN cont_fst_snd_D2, THEN cont_fst_snd_D2]
  from f g h1 h2 h3 show ?thesis by (rule cont2cont_list_case)
qed

text {* The simple version (due to Joachim Breitner) is needed if the
  element type of the list is not a cpo. *}

lemma cont2cont_list_case_simple [simp, cont2cont]:
  assumes "cont (\<lambda>x. f1 x)"
  assumes "\<And>y ys. cont (\<lambda>x. f2 x y ys)"
  shows "cont (\<lambda>x. case l of [] \<Rightarrow> f1 x | y # ys \<Rightarrow> f2 x y ys)"
using assms by (cases l) auto

text {* There are probably lots of other list operations that also
deserve to have continuity lemmas.  I'll add more as they are
needed. *}

subsection {* Using lists with fixrec *}

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

setup {*
  Fixrec.add_matchers
    [ (@{const_name Nil}, @{const_name match_Nil}),
      (@{const_name Cons}, @{const_name match_Cons}) ]
*}

end
