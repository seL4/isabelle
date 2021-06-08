section \<open>Lexicographic orderings\<close>

theory Lexord
  imports Main
begin

subsection \<open>The preorder case\<close>

locale lex_preordering = preordering
begin

inductive lex_less :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>  (infix \<open>[\<^bold><]\<close> 50) 
where
  Nil: \<open>[] [\<^bold><] y # ys\<close>
| Cons: \<open>x \<^bold>< y \<Longrightarrow> x # xs [\<^bold><] y # ys\<close>
| Cons_eq: \<open>x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> x \<Longrightarrow> xs [\<^bold><] ys \<Longrightarrow> x # xs [\<^bold><] y # ys\<close>

inductive lex_less_eq :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close>  (infix \<open>[\<^bold>\<le>]\<close> 50)
where
  Nil: \<open>[] [\<^bold>\<le>] ys\<close>
| Cons: \<open>x \<^bold>< y \<Longrightarrow> x # xs [\<^bold>\<le>] y # ys\<close>
| Cons_eq: \<open>x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> x \<Longrightarrow> xs [\<^bold>\<le>] ys \<Longrightarrow> x # xs [\<^bold>\<le>] y # ys\<close>

lemma lex_less_simps [simp]:
  \<open>[] [\<^bold><] y # ys\<close>
  \<open>\<not> xs [\<^bold><] []\<close>
  \<open>x # xs [\<^bold><] y # ys \<longleftrightarrow> x \<^bold>< y \<or> x \<^bold>\<le> y \<and> y \<^bold>\<le> x \<and> xs [\<^bold><] ys\<close>
  by (auto intro: lex_less.intros elim: lex_less.cases)

lemma lex_less_eq_simps [simp]:
  \<open>[] [\<^bold>\<le>] ys\<close>
  \<open>\<not> x # xs [\<^bold>\<le>] []\<close>
  \<open>x # xs [\<^bold>\<le>] y # ys \<longleftrightarrow> x \<^bold>< y \<or> x \<^bold>\<le> y \<and> y \<^bold>\<le> x \<and> xs [\<^bold>\<le>] ys\<close>
  by (auto intro: lex_less_eq.intros elim: lex_less_eq.cases)

lemma lex_less_code [code]:
  \<open>[] [\<^bold><] y # ys \<longleftrightarrow> True\<close>
  \<open>xs [\<^bold><] [] \<longleftrightarrow> False\<close>
  \<open>x # xs [\<^bold><] y # ys \<longleftrightarrow> x \<^bold>< y \<or> x \<^bold>\<le> y \<and> y \<^bold>\<le> x \<and> xs [\<^bold><] ys\<close>
  by simp_all

lemma lex_less_eq_code [code]:
  \<open>[] [\<^bold>\<le>] ys \<longleftrightarrow> True\<close>
  \<open>x # xs [\<^bold>\<le>] [] \<longleftrightarrow> False\<close>
  \<open>x # xs [\<^bold>\<le>] y # ys \<longleftrightarrow> x \<^bold>< y \<or> x \<^bold>\<le> y \<and> y \<^bold>\<le> x \<and> xs [\<^bold>\<le>] ys\<close>
  by simp_all

lemma preordering:
  \<open>preordering ([\<^bold>\<le>]) ([\<^bold><])\<close>
proof
  fix xs ys zs
  show \<open>xs [\<^bold>\<le>] xs\<close>
    by (induction xs) (simp_all add: refl)
  show \<open>xs [\<^bold>\<le>] zs\<close> if \<open>xs [\<^bold>\<le>] ys\<close> \<open>ys [\<^bold>\<le>] zs\<close>
  using that proof (induction arbitrary: zs)
    case (Nil ys)
    then show ?case by simp
  next
    case (Cons x y xs ys)
    then show ?case
      by (cases zs) (auto dest: strict_trans strict_trans2)
  next
    case (Cons_eq x y xs ys)
    then show ?case
      by (cases zs) (auto dest: strict_trans1 intro: trans)
  qed
  show \<open>xs [\<^bold><] ys \<longleftrightarrow> xs [\<^bold>\<le>] ys \<and> \<not> ys [\<^bold>\<le>] xs\<close> (is \<open>?P \<longleftrightarrow> ?Q\<close>)
  proof
    assume ?P
    then have \<open>xs [\<^bold>\<le>] ys\<close>
      by induction simp_all
    moreover have \<open>\<not> ys [\<^bold>\<le>] xs\<close>
      using \<open>?P\<close>
      by induction (simp_all, simp_all add: strict_iff_not asym)
    ultimately show ?Q ..
  next
    assume ?Q
    then have \<open>xs [\<^bold>\<le>] ys\<close> \<open>\<not> ys [\<^bold>\<le>] xs\<close>
      by auto
    then show ?P
    proof induction
      case (Nil ys)
      then show ?case
        by (cases ys) simp_all
    next
      case (Cons x y xs ys)
      then show ?case
        by simp
    next
      case (Cons_eq x y xs ys)
      then show ?case
        by simp
    qed
  qed
qed

interpretation lex: preordering \<open>([\<^bold>\<le>])\<close> \<open>([\<^bold><])\<close>
  by (fact preordering)

end


subsection \<open>The order case\<close>

locale lex_ordering = lex_preordering + ordering
begin

interpretation lex: preordering \<open>([\<^bold>\<le>])\<close> \<open>([\<^bold><])\<close>
  by (fact preordering)

lemma less_lex_Cons_iff [simp]:
  \<open>x # xs [\<^bold><] y # ys \<longleftrightarrow> x \<^bold>< y \<or> x = y \<and> xs [\<^bold><] ys\<close>
  by (auto intro: refl antisym)

lemma less_eq_lex_Cons_iff [simp]:
  \<open>x # xs [\<^bold>\<le>] y # ys \<longleftrightarrow> x \<^bold>< y \<or> x = y \<and> xs [\<^bold>\<le>] ys\<close>
  by (auto intro: refl antisym)

lemma ordering:
  \<open>ordering ([\<^bold>\<le>]) ([\<^bold><])\<close>
proof
  fix xs ys
  show *: \<open>xs = ys\<close> if \<open>xs [\<^bold>\<le>] ys\<close> \<open>ys [\<^bold>\<le>] xs\<close>
  using that proof induction
  case (Nil ys)
    then show ?case by (cases ys) simp
  next
    case (Cons x y xs ys)
    then show ?case by (auto dest: asym intro: antisym)
      (simp add: strict_iff_not)
  next
    case (Cons_eq x y xs ys)
    then show ?case by (auto intro: antisym)
      (simp add: strict_iff_not)
  qed
  show \<open>xs [\<^bold><] ys \<longleftrightarrow> xs [\<^bold>\<le>] ys \<and> xs \<noteq> ys\<close>
    by (auto simp add: lex.strict_iff_not dest: *)
qed

interpretation lex: ordering \<open>([\<^bold>\<le>])\<close> \<open>([\<^bold><])\<close>
  by (fact ordering)

end


subsection \<open>Canonical instance\<close>

instantiation list :: (preorder) preorder
begin

global_interpretation lex: lex_preordering \<open>(\<le>) :: 'a::preorder \<Rightarrow> 'a \<Rightarrow> bool\<close> \<open>(<) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  defines less_eq_list = lex.lex_less_eq
    and less_list = lex.lex_less ..

instance
  by (rule class.preorder.of_class.intro, rule preordering_preorderI, fact lex.preordering)

end

global_interpretation lex: lex_ordering \<open>(\<le>) :: 'a::order \<Rightarrow> 'a \<Rightarrow> bool\<close> \<open>(<) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  rewrites \<open>lex_preordering.lex_less_eq (\<le>) (<) = ((\<le>) :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool)\<close>
    and \<open>lex_preordering.lex_less (\<le>) (<) = ((<) :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool)\<close>
proof -
  interpret lex_ordering \<open>(\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> \<open>(<) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> ..
  show \<open>lex_ordering ((\<le>)  :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (<)\<close>
    by (fact lex_ordering_axioms)
  show \<open>lex_preordering.lex_less_eq (\<le>) (<) = (\<le>)\<close>
    by (simp add: less_eq_list_def)
  show \<open>lex_preordering.lex_less (\<le>) (<) = (<)\<close>
    by (simp add: less_list_def)
qed

instance list :: (order) order
  by (rule class.order.of_class.intro, rule ordering_orderI, fact lex.ordering)

export_code \<open>(\<le>) :: _ list \<Rightarrow> _ list \<Rightarrow> bool\<close> \<open>(<) :: _ list \<Rightarrow> _ list \<Rightarrow> bool\<close> in Haskell


subsection \<open>Non-canonical instance\<close>

context comm_monoid_mult
begin

definition dvd_strict :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  where \<open>dvd_strict a b \<longleftrightarrow> a dvd b \<and> \<not> b dvd a\<close>

end

global_interpretation dvd: lex_preordering \<open>(dvd) :: 'a::comm_monoid_mult \<Rightarrow> 'a \<Rightarrow> bool\<close> dvd_strict
  defines lex_dvd = dvd.lex_less_eq
    and lex_dvd_strict = dvd.lex_less
  apply (rule lex_preordering.intro)
  apply standard
    apply (auto simp add: dvd_strict_def)
  done

print_theorems

global_interpretation lex_dvd: preordering lex_dvd lex_dvd_strict
  by (fact dvd.preordering)

definition \<open>example = lex_dvd [(4::int), - 7, 8] [- 8, 13, 5]\<close>

export_code example in Haskell

value example

end
