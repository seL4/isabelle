(*  Title:      HOL/Algebra/Indexed_Polynomials.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Indexed_Polynomials
  imports Weak_Morphisms "HOL-Library.Multiset" Polynomial_Divisibility
    
begin

section \<open>Indexed Polynomials\<close>

text \<open>In this theory, we build a basic framework to the study of polynomials on letters
      indexed by a set. The main interest is to then apply these concepts to the construction
      of the algebraic closure of a field. \<close>


subsection \<open>Definitions\<close>

text \<open>We formalize indexed monomials as multisets with its support a subset of the index set.
      On top of those, we build indexed polynomials which are simply functions mapping a monomial
      to its coefficient. \<close>

definition (in ring) indexed_const :: "'a \<Rightarrow> ('c multiset \<Rightarrow> 'a)" 
  where "indexed_const k = (\<lambda>m. if m = {#} then k else \<zero>)"

definition (in ring) indexed_pmult :: "('c multiset \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)" (infixl \<open>\<Otimes>\<close> 65)
  where "indexed_pmult P i = (\<lambda>m. if i \<in># m then P (m - {# i #}) else \<zero>)"

definition (in ring) indexed_padd :: "_ \<Rightarrow> _ \<Rightarrow> ('c multiset \<Rightarrow> 'a)" (infixl \<open>\<Oplus>\<close> 65)
  where "indexed_padd P Q = (\<lambda>m. (P m) \<oplus> (Q m))"

definition (in ring) indexed_var :: "'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)" (\<open>\<X>\<index>\<close>)
  where "indexed_var i = (indexed_const \<one>) \<Otimes> i"

definition (in ring) index_free :: "('c multiset \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> bool"
  where "index_free P i \<longleftrightarrow> (\<forall>m. i \<in># m \<longrightarrow> P m = \<zero>)"

definition (in ring) carrier_coeff :: "('c multiset \<Rightarrow> 'a) \<Rightarrow> bool"
  where "carrier_coeff P \<longleftrightarrow> (\<forall>m. P m \<in> carrier R)"

inductive_set (in ring) indexed_pset :: "'c set \<Rightarrow> 'a set \<Rightarrow> ('c multiset \<Rightarrow> 'a) set"
  (\<open>(\<open>open_block notation=\<open>postfix \<X>\<close>\<close>_ [\<X>\<index>])\<close> 80)
  for I and K where
    indexed_const:  "k \<in> K \<Longrightarrow> indexed_const k \<in> (K[\<X>\<^bsub>I\<^esub>])"
  | indexed_padd:  "\<lbrakk> P \<in> (K[\<X>\<^bsub>I\<^esub>]); Q \<in> (K[\<X>\<^bsub>I\<^esub>]) \<rbrakk> \<Longrightarrow> P \<Oplus> Q \<in> (K[\<X>\<^bsub>I\<^esub>])"
  | indexed_pmult: "\<lbrakk> P \<in> (K[\<X>\<^bsub>I\<^esub>]); i \<in> I \<rbrakk> \<Longrightarrow> P \<Otimes> i \<in> (K[\<X>\<^bsub>I\<^esub>])"

fun (in ring) indexed_eval_aux :: "('c multiset \<Rightarrow> 'a) list \<Rightarrow> 'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)"
  where "indexed_eval_aux Ps i = foldr (\<lambda>P Q. (Q \<Otimes> i) \<Oplus> P) Ps (indexed_const \<zero>)"

fun (in ring) indexed_eval :: "('c multiset \<Rightarrow> 'a) list \<Rightarrow> 'c \<Rightarrow> ('c multiset \<Rightarrow> 'a)"
  where "indexed_eval Ps i = indexed_eval_aux (rev Ps) i"


subsection \<open>Basic Properties\<close>

lemma (in ring) carrier_coeffE:
  assumes "carrier_coeff P" shows "P m \<in> carrier R"
  using assms unfolding carrier_coeff_def by simp

lemma (in ring) indexed_zero_def: "indexed_const \<zero> = (\<lambda>_. \<zero>)"
  unfolding indexed_const_def by simp

lemma (in ring) indexed_const_index_free: "index_free (indexed_const k) i"
  unfolding index_free_def indexed_const_def by auto

lemma (in domain) indexed_var_not_index_free: "\<not> index_free \<X>\<^bsub>i\<^esub> i"
proof -
  have "\<X>\<^bsub>i\<^esub> {# i #} = \<one>"
    unfolding indexed_var_def indexed_pmult_def indexed_const_def by simp
  thus ?thesis
    using one_not_zero unfolding index_free_def by fastforce 
qed

lemma (in ring) indexed_pmult_zero [simp]:
  shows "indexed_pmult (indexed_const \<zero>) i = indexed_const \<zero>"
  unfolding indexed_zero_def indexed_pmult_def by auto

lemma (in ring) indexed_padd_zero:
  assumes "carrier_coeff P" shows "P \<Oplus> (indexed_const \<zero>) = P" and "(indexed_const \<zero>) \<Oplus> P = P"
  using assms unfolding carrier_coeff_def indexed_zero_def indexed_padd_def by auto

lemma (in ring) indexed_padd_const:
  shows "(indexed_const k1) \<Oplus> (indexed_const k2) = indexed_const (k1 \<oplus> k2)"
  unfolding indexed_padd_def indexed_const_def by auto

lemma (in ring) indexed_const_in_carrier:
  assumes "K \<subseteq> carrier R" and "k \<in> K" shows "\<And>m. (indexed_const k) m \<in> carrier R"
  using assms unfolding indexed_const_def by auto

lemma (in ring) indexed_padd_in_carrier:
  assumes "carrier_coeff P" and "carrier_coeff Q" shows "carrier_coeff (indexed_padd P Q)"
  using assms unfolding carrier_coeff_def indexed_padd_def by simp

lemma (in ring) indexed_pmult_in_carrier:
  assumes "carrier_coeff P" shows "carrier_coeff (P \<Otimes> i)"
  using assms unfolding carrier_coeff_def indexed_pmult_def by simp

lemma (in ring) indexed_eval_aux_in_carrier:
  assumes "list_all carrier_coeff Ps" shows "carrier_coeff (indexed_eval_aux Ps i)"
  using assms unfolding carrier_coeff_def
  by (induct Ps) (auto simp add: indexed_zero_def indexed_padd_def indexed_pmult_def)

lemma (in ring) indexed_eval_in_carrier:
  assumes "list_all carrier_coeff Ps" shows "carrier_coeff (indexed_eval Ps i)"
  using assms indexed_eval_aux_in_carrier[of "rev Ps"] by auto

lemma (in ring) indexed_pset_in_carrier:
  assumes "K \<subseteq> carrier R" and "P \<in> (K[\<X>\<^bsub>I\<^esub>])" shows "carrier_coeff P"
  using assms(2,1) indexed_const_in_carrier unfolding carrier_coeff_def
  by (induction) (auto simp add: indexed_zero_def indexed_padd_def indexed_pmult_def)


subsection \<open>Indexed Eval\<close>

lemma (in ring) exists_indexed_eval_aux_monomial:
  assumes "carrier_coeff P" and "list_all carrier_coeff Qs"
    and "count n i = k" and "P n \<noteq> \<zero>" and "list_all (\<lambda>Q. index_free Q i) Qs"
  obtains m where "count m i = length Qs + k" and "(indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
proof -
  from assms(2,5) have "\<exists>m. count m i = length Qs + k \<and> (indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
  proof (induct Qs)
    case Nil thus ?case
      using indexed_padd_zero(2)[OF assms(1)] assms(3-4) by auto
  next
    case (Cons Q Qs)
    then obtain m where m: "count m i = length Qs + k" "(indexed_eval_aux (Qs @ [ P ]) i) m \<noteq> \<zero>"
      by auto
    define m' where "m' = m + {# i #}"
    hence "Q m' = \<zero>"
      using Cons(3) unfolding index_free_def by simp
    moreover have "(indexed_eval_aux (Qs @ [ P ]) i) m \<in> carrier R"
      using indexed_eval_aux_in_carrier[of "Qs @ [ P ]" i] Cons(2) assms(1) carrier_coeffE by auto
    hence "((indexed_eval_aux (Qs @ [ P ]) i) \<Otimes> i) m' \<in> carrier R - { \<zero> }"
      using m unfolding indexed_pmult_def m'_def by simp
    ultimately have "(indexed_eval_aux (Q # (Qs @ [ P ])) i) m' \<noteq> \<zero>"
      by (auto simp add: indexed_padd_def)
    moreover from \<open>count m i = length Qs + k\<close> have "count m' i = length (Q # Qs) + k"
      unfolding m'_def by simp
    ultimately show ?case
      by auto
  qed
  thus thesis
    using that by blast
qed

lemma (in ring) indexed_eval_aux_monomial_degree_le:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
    and "(indexed_eval_aux Ps i) m \<noteq> \<zero>" shows "count m i \<le> length Ps - 1"
  using assms(1-3)
proof (induct Ps arbitrary: m, simp add: indexed_zero_def)
  case (Cons P Ps) show ?case
  proof (cases "count m i = 0", simp)
    assume "count m i \<noteq> 0"
    hence "P m = \<zero>"
      using Cons(3) unfolding index_free_def by simp
    moreover have "(indexed_eval_aux Ps i) m \<in> carrier R"
      using carrier_coeffE[OF indexed_eval_aux_in_carrier[of Ps i]] Cons(2) by simp 
    ultimately have "((indexed_eval_aux Ps i) \<Otimes> i) m \<noteq> \<zero>"
      using Cons(4) by (auto simp add: indexed_padd_def)
    with \<open>count m i \<noteq> 0\<close> have "(indexed_eval_aux Ps i) (m - {# i #}) \<noteq> \<zero>"
      unfolding indexed_pmult_def by (auto simp del: indexed_eval_aux.simps)
    hence "count m i - 1 \<le> length Ps - 1"
      using Cons(1)[of "m - {# i #}"] Cons(2-3) by auto
    moreover from \<open>(indexed_eval_aux Ps i) (m - {# i #}) \<noteq> \<zero>\<close> have "length Ps > 0"
      by (auto simp add: indexed_zero_def)
    moreover from \<open>count m i \<noteq> 0\<close> have "count m i > 0"
      by simp
    ultimately show ?thesis
      by (simp add: Suc_leI le_diff_iff)
  qed
qed

lemma (in ring) indexed_eval_aux_is_inj:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
      and "list_all carrier_coeff Qs" and "list_all (\<lambda>Q. index_free Q i) Qs"
    and "indexed_eval_aux Ps i = indexed_eval_aux Qs i" and "length Ps = length Qs"
  shows "Ps = Qs"
  using assms
proof (induct Ps arbitrary: Qs, simp)
  case (Cons P Ps)
  from \<open>length (P # Ps) = length Qs\<close> obtain Q' Qs' where Qs: "Qs = Q' # Qs'" and "length Ps = length Qs'"
    by (metis Suc_length_conv)

  have in_carrier:
    "((indexed_eval_aux Ps  i) \<Otimes> i) m \<in> carrier R" "P  m \<in> carrier R"
    "((indexed_eval_aux Qs' i) \<Otimes> i) m \<in> carrier R" "Q' m \<in> carrier R" for m
    using indexed_eval_aux_in_carrier[of Ps  i]
          indexed_eval_aux_in_carrier[of Qs' i] Cons(2,4) carrier_coeffE
    unfolding Qs indexed_pmult_def by auto

  have "(indexed_eval_aux (P # Ps) i) m = (indexed_eval_aux (Q' # Qs') i) m" for m
    using Cons(6) unfolding Qs by simp
  hence eq: "((indexed_eval_aux Ps i) \<Otimes> i) m \<oplus> P m = ((indexed_eval_aux Qs' i) \<Otimes> i) m \<oplus> Q' m" for m
    by (simp add: indexed_padd_def)

  have "P m = Q' m" if "i \<in># m" for m
    using that Cons(3,5) unfolding index_free_def Qs by auto
  moreover have "P m = Q' m" if "i \<notin># m" for m
    using in_carrier(2,4) eq[of m] that by (auto simp add: indexed_pmult_def)
  ultimately have "P = Q'"
    by auto

  hence "(indexed_eval_aux Ps i) m = (indexed_eval_aux Qs' i) m" for m
    using eq[of "m + {# i #}"] in_carrier[of "m + {# i #}"] unfolding indexed_pmult_def by auto
  with \<open>length Ps = length Qs'\<close> have "Ps = Qs'"
    using Cons(1)[of Qs'] Cons(2-5) unfolding Qs by auto
  with \<open>P = Q'\<close> show ?case
    unfolding Qs by simp
qed

lemma (in ring) indexed_eval_aux_is_inj':
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
      and "list_all carrier_coeff Qs" and "list_all (\<lambda>Q. index_free Q i) Qs"
      and "carrier_coeff P" and "index_free P i" "P \<noteq> indexed_const \<zero>"
      and "carrier_coeff Q" and "index_free Q i" "Q \<noteq> indexed_const \<zero>"
    and "indexed_eval_aux (Ps @ [ P ]) i = indexed_eval_aux (Qs @ [ Q ]) i"
  shows "Ps = Qs" and "P = Q"
proof -
  obtain m n where "P m \<noteq> \<zero>" and "Q n \<noteq> \<zero>"
    using assms(7,10) unfolding indexed_zero_def by blast
  hence "count m i = 0" and "count n i = 0"
    using assms(6,9) unfolding index_free_def by (meson count_inI)+ 
  with \<open>P m \<noteq> \<zero>\<close> and \<open>Q n \<noteq> \<zero>\<close> obtain m' n'
    where m': "count m' i = length Ps" "(indexed_eval_aux (Ps @ [ P ]) i) m' \<noteq> \<zero>"
      and n': "count n' i = length Qs" "(indexed_eval_aux (Qs @ [ Q ]) i) n' \<noteq> \<zero>"
    using exists_indexed_eval_aux_monomial[of P Ps m i 0]
          exists_indexed_eval_aux_monomial[of Q Qs n i 0] assms(1-5,8)
    by (metis (no_types, lifting) add.right_neutral)
  have "(indexed_eval_aux (Qs @ [ Q ]) i) m' \<noteq> \<zero>"
    using m'(2) assms(11) by simp
  with \<open>count m' i = length Ps\<close> have "length Ps \<le> length Qs"
    using indexed_eval_aux_monomial_degree_le[of "Qs @ [ Q ]" i m'] assms(3-4,8-9) by auto
  moreover have "(indexed_eval_aux (Ps @ [ P ]) i) n' \<noteq> \<zero>"
    using n'(2) assms(11) by simp
  with \<open>count n' i = length Qs\<close> have "length Qs \<le> length Ps"
    using indexed_eval_aux_monomial_degree_le[of "Ps @ [ P ]" i n'] assms(1-2,5-6) by auto
  ultimately have same_len: "length (Ps @ [ P ]) = length (Qs @ [ Q ])"
    by simp
  thus "Ps = Qs" and "P = Q"
    using indexed_eval_aux_is_inj[of "Ps @ [ P ]" i "Qs @ [ Q ]"] assms(1-6,8-9,11) by auto
qed

lemma (in ring) exists_indexed_eval_monomial:
  assumes "carrier_coeff P" and "list_all carrier_coeff Qs"
    and "P n \<noteq> \<zero>" and "list_all (\<lambda>Q. index_free Q i) Qs"
  obtains m where "count m i = length Qs + (count n i)" and "(indexed_eval (P # Qs) i) m \<noteq> \<zero>"
  using exists_indexed_eval_aux_monomial[OF assms(1) _ _ assms(3), of "rev Qs"] assms(2,4) by auto

corollary (in ring) exists_indexed_eval_monomial':
  assumes "carrier_coeff P" and "list_all carrier_coeff Qs"
    and "P \<noteq> indexed_const \<zero>" and "list_all (\<lambda>Q. index_free Q i) Qs"
  obtains m where "count m i \<ge> length Qs" and "(indexed_eval (P # Qs) i) m \<noteq> \<zero>"
proof -
  from \<open>P \<noteq> indexed_const \<zero>\<close> obtain n where "P n \<noteq> \<zero>"
    unfolding indexed_const_def by auto
  then obtain m where "count m i = length Qs + (count n i)" and "(indexed_eval (P # Qs) i) m \<noteq> \<zero>"
    using exists_indexed_eval_monomial[OF assms(1-2) _ assms(4)] by auto
  thus thesis
    using that by force
qed

lemma (in ring) indexed_eval_monomial_degree_le:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
    and "(indexed_eval Ps i) m \<noteq> \<zero>" shows "count m i \<le> length Ps - 1"
  using indexed_eval_aux_monomial_degree_le[of "rev Ps"] assms by auto

lemma (in ring) indexed_eval_is_inj:
  assumes "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
      and "list_all carrier_coeff Qs" and "list_all (\<lambda>Q. index_free Q i) Qs"
      and "carrier_coeff P" and "index_free P i" "P \<noteq> indexed_const \<zero>"
      and "carrier_coeff Q" and "index_free Q i" "Q \<noteq> indexed_const \<zero>"
    and "indexed_eval (P # Ps) i = indexed_eval (Q # Qs) i"
  shows "Ps = Qs" and "P = Q"
proof -
  have rev_cond:
    "list_all carrier_coeff (rev Ps)" "list_all (\<lambda>P. index_free P i) (rev Ps)"
    "list_all carrier_coeff (rev Qs)" "list_all (\<lambda>Q. index_free Q i) (rev Qs)"
    using assms(1-4) by auto
  show "Ps = Qs" and "P = Q"
    using indexed_eval_aux_is_inj'[OF rev_cond assms(5-10)] assms(11) by auto
qed

lemma (in ring) indexed_eval_inj_on_carrier:
  assumes "\<And>P. P \<in> carrier L \<Longrightarrow> carrier_coeff P" and "\<And>P. P \<in> carrier L \<Longrightarrow> index_free P i" and "\<zero>\<^bsub>L\<^esub> = indexed_const \<zero>"
  shows "inj_on (\<lambda>Ps. indexed_eval Ps i) (carrier (poly_ring L))"
proof -
  { fix Ps
    assume "Ps \<in> carrier (poly_ring L)" and "indexed_eval Ps i = indexed_const \<zero>"
    have "Ps = []"
    proof (rule ccontr)
      assume "Ps \<noteq> []"
      then obtain P' Ps' where Ps: "Ps = P' # Ps'"
        using list.exhaust by blast
      with \<open>Ps \<in> carrier (poly_ring L)\<close>
      have "P' \<noteq> indexed_const \<zero>" and "list_all carrier_coeff Ps" and "list_all (\<lambda>P. index_free P i) Ps"
        using assms unfolding sym[OF univ_poly_carrier[of L "carrier L"]] polynomial_def
        by (simp add: list.pred_set subset_code(1))+
      then obtain m where "(indexed_eval Ps i) m \<noteq> \<zero>"
        using exists_indexed_eval_monomial'[of P' Ps'] unfolding Ps by auto
      hence "indexed_eval Ps i \<noteq> indexed_const \<zero>"
        unfolding indexed_const_def by auto
      with \<open>indexed_eval Ps i = indexed_const \<zero>\<close> show False by simp
    qed } note aux_lemma = this

  show ?thesis
  proof (rule inj_onI)
    fix Ps Qs
    assume "Ps \<in> carrier (poly_ring L)" and "Qs \<in> carrier (poly_ring L)"
    show "indexed_eval Ps i = indexed_eval Qs i \<Longrightarrow> Ps = Qs"
    proof (cases)
      assume "Qs = []" and "indexed_eval Ps i = indexed_eval Qs i"
      with \<open>Ps \<in> carrier (poly_ring L)\<close> show "Ps = Qs"
        using aux_lemma by simp
    next
      assume "Qs \<noteq> []" and eq: "indexed_eval Ps i = indexed_eval Qs i"
      with \<open>Qs \<in> carrier (poly_ring L)\<close> have "Ps \<noteq> []"
        using aux_lemma by auto
      from \<open>Ps \<noteq> []\<close> and \<open>Qs \<noteq> []\<close> obtain P' Ps' Q' Qs' where Ps: "Ps = P' # Ps'" and Qs: "Qs = Q' # Qs'"
        using list.exhaust by metis

      from \<open>Ps \<in> carrier (poly_ring L)\<close> and \<open>Ps = P' # Ps'\<close>
      have "carrier_coeff P'" and "index_free P' i" "P' \<noteq> indexed_const \<zero>"
       and "list_all carrier_coeff Ps'" and "list_all (\<lambda>P. index_free P i) Ps'"
        using assms unfolding sym[OF univ_poly_carrier[of L "carrier L"]] polynomial_def
        by (simp add: list.pred_set subset_code(1))+
      moreover 
      from \<open>Qs \<in> carrier (poly_ring L)\<close> and \<open>Qs = Q' # Qs'\<close>
      have "carrier_coeff Q'" and "index_free Q' i" "Q' \<noteq> indexed_const \<zero>"
       and "list_all carrier_coeff Qs'" and "list_all (\<lambda>P. index_free P i) Qs'"
        using assms unfolding sym[OF univ_poly_carrier[of L "carrier L"]] polynomial_def
        by (simp add: list.pred_set subset_code(1))+
      ultimately show ?thesis
        using indexed_eval_is_inj[of Ps' i Qs' P' Q'] eq unfolding Ps Qs by auto
    qed
  qed
qed


subsection \<open>Link with Weak Morphisms\<close>

text \<open>We study some elements of the contradiction needed in the algebraic closure existence proof. \<close>

context ring
begin

lemma (in ring) indexed_padd_index_free:
  assumes "index_free P i" and "index_free Q i" shows "index_free (P \<Oplus> Q) i"
  using assms unfolding indexed_padd_def index_free_def by auto

lemma (in ring) indexed_pmult_index_free:
  assumes "index_free P j" and "i \<noteq> j" shows "index_free (P \<Otimes> i) j"
  using assms unfolding index_free_def indexed_pmult_def
  by (metis insert_DiffM insert_noteq_member)

lemma (in ring) indexed_eval_index_free:
  assumes "list_all (\<lambda>P. index_free P j) Ps" and "i \<noteq> j" shows "index_free (indexed_eval Ps i) j"
proof -
  { fix Ps assume "list_all (\<lambda>P. index_free P j) Ps" hence "index_free (indexed_eval_aux Ps i) j"
      using indexed_padd_index_free[OF indexed_pmult_index_free[OF _ assms(2)]]
      by (induct Ps) (auto simp add: indexed_zero_def index_free_def) }
  thus ?thesis
    using assms(1) by auto
qed

context
  fixes L :: "(('c multiset) \<Rightarrow> 'a) ring" and i :: 'c
  assumes hyps:
    \<comment> \<open>i\<close>   "field L"
    \<comment> \<open>ii\<close>  "\<And>P. P \<in> carrier L \<Longrightarrow> carrier_coeff P"
    \<comment> \<open>iii\<close> "\<And>P. P \<in> carrier L \<Longrightarrow> index_free P i"
    \<comment> \<open>iv\<close>  "\<zero>\<^bsub>L\<^esub> = indexed_const \<zero>"
begin

interpretation L: field L
  using \<open>field L\<close> .

interpretation UP: principal_domain "poly_ring L"
  using L.univ_poly_is_principal[OF L.carrier_is_subfield] .


abbreviation eval_pmod
  where "eval_pmod q \<equiv> (\<lambda>p. indexed_eval (L.pmod p q) i)"

abbreviation image_poly
  where "image_poly q \<equiv> image_ring (eval_pmod q) (poly_ring L)"


lemma indexed_eval_is_weak_ring_morphism:
  assumes "q \<in> carrier (poly_ring L)" shows "weak_ring_morphism (eval_pmod q) (PIdl\<^bsub>poly_ring L\<^esub> q) (poly_ring L)"
proof (rule weak_ring_morphismI)
  show "ideal (PIdl\<^bsub>poly_ring L\<^esub> q) (poly_ring L)"
    using UP.cgenideal_ideal[OF assms] .
next
  fix a b assume in_carrier: "a \<in> carrier (poly_ring L)" "b \<in> carrier (poly_ring L)"
  note ldiv_closed = in_carrier[THEN L.long_division_closed(2)[OF L.carrier_is_subfield _ assms]]

  have "(eval_pmod q) a = (eval_pmod q) b \<longleftrightarrow> L.pmod a q = L.pmod b q"
    using inj_onD[OF indexed_eval_inj_on_carrier[OF hyps(2-4)] _ ldiv_closed] by fastforce
  also have " ... \<longleftrightarrow> q pdivides\<^bsub>L\<^esub> (a \<ominus>\<^bsub>poly_ring L\<^esub> b)"
    unfolding L.same_pmod_iff_pdivides[OF L.carrier_is_subfield in_carrier assms] ..
  also have " ... \<longleftrightarrow> PIdl\<^bsub>poly_ring L\<^esub> (a \<ominus>\<^bsub>poly_ring L\<^esub> b) \<subseteq> PIdl\<^bsub>poly_ring L\<^esub> q"
    unfolding UP.to_contain_is_to_divide[OF assms UP.minus_closed[OF in_carrier]] pdivides_def ..
  also have " ... \<longleftrightarrow> a \<ominus>\<^bsub>poly_ring L\<^esub> b \<in> PIdl\<^bsub>poly_ring L\<^esub> q"
    unfolding UP.cgenideal_eq_genideal[OF assms] UP.cgenideal_eq_genideal[OF UP.minus_closed[OF in_carrier]]
              UP.Idl_subset_ideal'[OF UP.minus_closed[OF in_carrier] assms] ..
  finally show "(eval_pmod q) a = (eval_pmod q) b \<longleftrightarrow> a \<ominus>\<^bsub>poly_ring L\<^esub> b \<in> PIdl\<^bsub>poly_ring L\<^esub> q" .
qed

lemma eval_norm_eq_id:
  assumes "q \<in> carrier (poly_ring L)" and "degree q > 0" and "a \<in> carrier L"
  shows "((eval_pmod q) \<circ> (ring.poly_of_const L)) a = a"
proof (cases)
  assume "a = \<zero>\<^bsub>L\<^esub>" thus ?thesis
    using L.long_division_zero(2)[OF L.carrier_is_subfield assms(1)] hyps(4)
    unfolding ring.poly_of_const_def[OF L.ring_axioms] by auto
next
  assume "a \<noteq> \<zero>\<^bsub>L\<^esub>" then have in_carrier: "[ a ] \<in> carrier (poly_ring L)"
    using assms(3) unfolding sym[OF univ_poly_carrier[of L "carrier L"]] polynomial_def by simp
  from \<open>a \<noteq> \<zero>\<^bsub>L\<^esub>\<close> show ?thesis
    using L.pmod_const(2)[OF L.carrier_is_subfield in_carrier assms(1)] assms(2)
          indexed_padd_zero(2)[OF hyps(2)[OF assms(3)]]
    unfolding ring.poly_of_const_def[OF L.ring_axioms] by auto
qed

lemma image_poly_iso_incl:
  assumes "q \<in> carrier (poly_ring L)" and "degree q > 0" shows "id \<in> ring_hom L (image_poly q)"
proof -
  have "((eval_pmod q) \<circ> L.poly_of_const) \<in> ring_hom L (image_poly q)"
    using ring_hom_trans[OF L.canonical_embedding_is_hom[OF L.carrier_is_subring]
          UP.weak_ring_morphism_is_hom[OF indexed_eval_is_weak_ring_morphism[OF assms(1)]]]
    by simp
  thus ?thesis
    using eval_norm_eq_id[OF assms(1-2)] L.ring_hom_restrict[of _ "image_poly q" id] by auto
qed

lemma image_poly_is_field:
  assumes "q \<in> carrier (poly_ring L)" and "pirreducible\<^bsub>L\<^esub> (carrier L) q" shows "field (image_poly q)"
  using UP.image_ring_is_field[OF indexed_eval_is_weak_ring_morphism[OF assms(1)]] assms(2)
  unfolding sym[OF L.rupture_is_field_iff_pirreducible[OF L.carrier_is_subfield assms(1)]] rupture_def
  by simp

lemma image_poly_index_free:
  assumes "q \<in> carrier (poly_ring L)" and "P \<in> carrier (image_poly q)" and "\<not> index_free P j" "i \<noteq> j"
  obtains Q where "Q \<in> carrier L" and "\<not> index_free Q j"
proof -
  from \<open>P \<in> carrier (image_poly q)\<close> obtain p where p: "p \<in> carrier (poly_ring L)" and P: "P = (eval_pmod q) p"
    unfolding image_ring_carrier by blast
  from \<open>\<not> index_free P j\<close> have "\<not> list_all (\<lambda>P. index_free P j) (L.pmod p q)"
    using indexed_eval_index_free[OF _ assms(4), of "L.pmod p q"] unfolding sym[OF P] by auto
  then obtain Q where "Q \<in> set (L.pmod p q)" and "\<not> index_free Q j"
    unfolding list_all_iff by auto
  thus ?thesis
    using L.long_division_closed(2)[OF L.carrier_is_subfield p assms(1)] that
    unfolding sym[OF univ_poly_carrier[of L "carrier L"]] polynomial_def
    by auto
qed

lemma eval_pmod_var:
  assumes "indexed_const \<in> ring_hom R L" and "q \<in> carrier (poly_ring L)" and "degree q > 1"
  shows "(eval_pmod q) X\<^bsub>L\<^esub> = \<X>\<^bsub>i\<^esub>" and "\<X>\<^bsub>i\<^esub> \<in> carrier (image_poly q)"
proof -
  have "X\<^bsub>L\<^esub> = [ indexed_const \<one>, indexed_const \<zero> ]" and "X\<^bsub>L\<^esub> \<in> carrier (poly_ring L)"
    using ring_hom_one[OF assms(1)] hyps(4) L.var_closed(1) L.carrier_is_subring unfolding var_def by auto
  thus "(eval_pmod q) X\<^bsub>L\<^esub> = \<X>\<^bsub>i\<^esub>"
    using L.pmod_const(2)[OF L.carrier_is_subfield _ assms(2), of "X\<^bsub>L\<^esub>"] assms(3)
    by (auto simp add: indexed_pmult_def indexed_padd_def indexed_const_def indexed_var_def)
  with \<open>X\<^bsub>L\<^esub> \<in> carrier (poly_ring L)\<close> show "\<X>\<^bsub>i\<^esub> \<in> carrier (image_poly q)"
    using image_iff unfolding image_ring_carrier by fastforce
qed

lemma image_poly_eval_indexed_var:
  assumes "indexed_const \<in> ring_hom R L"
    and "q \<in> carrier (poly_ring L)" and "degree q > 1" and "pirreducible\<^bsub>L\<^esub> (carrier L) q"
  shows "(ring.eval (image_poly q)) q \<X>\<^bsub>i\<^esub> = \<zero>\<^bsub>image_poly q\<^esub>"
proof -
  let ?surj = "L.rupture_surj (carrier L) q"
  let ?Rupt = "Rupt\<^bsub>L\<^esub> (carrier L) q"
  let ?f = "eval_pmod q"

  interpret UP: ring "poly_ring L"
    using L.univ_poly_is_ring[OF L.carrier_is_subring] .
  from \<open>pirreducible\<^bsub>L\<^esub> (carrier L) q\<close> interpret Rupt: field ?Rupt
    using L.rupture_is_field_iff_pirreducible[OF L.carrier_is_subfield assms(2)] by simp

  have weak_morphism: "weak_ring_morphism ?f (PIdl\<^bsub>poly_ring L\<^esub> q) (poly_ring L)"
    using indexed_eval_is_weak_ring_morphism[OF assms(2)] .
  then interpret I: ideal "PIdl\<^bsub>poly_ring L\<^esub> q" "poly_ring L"
    using weak_ring_morphism.axioms(1) by auto
  interpret Hom: ring_hom_ring ?Rupt "image_poly q" "\<lambda>x. the_elem (?f ` x)"
    using ring_hom_ring.intro[OF I.quotient_is_ring UP.image_ring_is_ring[OF weak_morphism]]
          UP.weak_ring_morphism_is_iso[OF weak_morphism]
    unfolding ring_iso_def symmetric[OF ring_hom_ring_axioms_def] rupture_def
    by auto

  have "set q \<subseteq> carrier L" and lc: "q \<noteq> [] \<Longrightarrow> lead_coeff q \<in> carrier L - { \<zero>\<^bsub>L\<^esub> }"
    using assms(2) unfolding sym[OF univ_poly_carrier] polynomial_def by auto

  have map_surj: "set (map (?surj \<circ> L.poly_of_const) q) \<subseteq> carrier ?Rupt"
  proof -
    have "L.poly_of_const a \<in> carrier (poly_ring L)" if "a \<in> carrier L" for a
      using that L.normalize_gives_polynomial[of "[ a ]"]
      unfolding univ_poly_carrier ring.poly_of_const_def[OF L.ring_axioms] by simp
    hence "(?surj \<circ> L.poly_of_const) a \<in> carrier ?Rupt" if "a \<in> carrier L" for a
      using ring_hom_memE(1)[OF L.rupture_surj_hom(1)[OF L.carrier_is_subring assms(2)]] that by simp
    with \<open>set q \<subseteq> carrier L\<close> show ?thesis
      by (induct q) (auto)
  qed

  have "?surj X\<^bsub>L\<^esub> \<in> carrier ?Rupt"
    using ring_hom_memE(1)[OF L.rupture_surj_hom(1)[OF _ assms(2)] L.var_closed(1)] L.carrier_is_subring by simp
  moreover have "map (\<lambda>x. the_elem (?f ` x)) (map (?surj \<circ> L.poly_of_const) q) = q"
  proof -
    define g where "g = (?surj \<circ> L.poly_of_const)"
    define f where "f = (\<lambda>x. the_elem (?f ` x))"

    have "the_elem (?f ` ((?surj \<circ> L.poly_of_const) a)) = ((eval_pmod q) \<circ> L.poly_of_const) a"
      if "a \<in> carrier L" for a
      using that L.normalize_gives_polynomial[of "[ a ]"] UP.weak_ring_morphism_range[OF weak_morphism]
      unfolding univ_poly_carrier ring.poly_of_const_def[OF L.ring_axioms] by auto
    hence "the_elem (?f ` ((?surj \<circ> L.poly_of_const) a)) = a" if "a \<in> carrier L" for a
      using eval_norm_eq_id[OF assms(2)] that assms(3) by simp
    hence "f (g a) = a" if "a \<in> carrier L" for a
      using that unfolding f_def g_def by simp
    with \<open>set q \<subseteq> carrier L\<close> have "map f (map g q) = q"
      by (induct q) (auto)
    thus ?thesis
      unfolding f_def g_def by simp
  qed
  moreover have "(\<lambda>x. the_elem (?f ` x)) (?surj X\<^bsub>L\<^esub>) = \<X>\<^bsub>i\<^esub>"
    using UP.weak_ring_morphism_range[OF weak_morphism L.var_closed(1)[OF L.carrier_is_subring]]
    unfolding eval_pmod_var(1)[OF assms(1-3)] by simp
  ultimately have "Hom.S.eval q \<X>\<^bsub>i\<^esub> = (\<lambda>x. the_elem (?f ` x)) (Rupt.eval (map (?surj \<circ> L.poly_of_const) q) (?surj X\<^bsub>L\<^esub>))"
    using Hom.eval_hom'[OF _ map_surj] by auto
  moreover have "\<zero>\<^bsub>?Rupt\<^esub> = ?surj \<zero>\<^bsub>poly_ring L\<^esub>"
    unfolding rupture_def FactRing_def by (simp add: I.a_rcos_const)
  hence "the_elem (?f ` \<zero>\<^bsub>?Rupt\<^esub>) = \<zero>\<^bsub>image_poly q\<^esub>"
    using UP.weak_ring_morphism_range[OF weak_morphism UP.zero_closed]
    unfolding image_ring_zero by simp 
  hence "(\<lambda>x. the_elem (?f ` x)) (Rupt.eval (map (?surj \<circ> L.poly_of_const) q) (?surj X\<^bsub>L\<^esub>)) = \<zero>\<^bsub>image_poly q\<^esub>"
    using L.polynomial_rupture[OF L.carrier_is_subring assms(2)] by simp
  ultimately show ?thesis
    by simp
qed

end (* of fixed L context. *)

end (* of ring context. *)

end