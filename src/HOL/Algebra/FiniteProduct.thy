(*  Title:      HOL/Algebra/FiniteProduct.thy
    Author:     Clemens Ballarin, started 19 November 2002

This file is largely based on HOL/Finite_Set.thy.
*)

theory FiniteProduct
imports Group
begin

subsection \<open>Product Operator for Commutative Monoids\<close>

subsubsection \<open>Inductive Definition of a Relation for Products over Sets\<close>

text \<open>Instantiation of locale \<open>LC\<close> of theory \<open>Finite_Set\<close> is not
  possible, because here we have explicit typing rules like
  \<open>x \<in> carrier G\<close>.  We introduce an explicit argument for the domain
  \<open>D\<close>.\<close>

inductive_set
  foldSetD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a] \<Rightarrow> ('b set * 'a) set"
  for D :: "'a set" and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" and e :: 'a
  where
    emptyI [intro]: "e \<in> D \<Longrightarrow> ({}, e) \<in> foldSetD D f e"
  | insertI [intro]: "\<lbrakk>x \<notin> A; f x y \<in> D; (A, y) \<in> foldSetD D f e\<rbrakk> \<Longrightarrow>
                      (insert x A, f x y) \<in> foldSetD D f e"

inductive_cases empty_foldSetDE [elim!]: "({}, x) \<in> foldSetD D f e"

definition
  foldD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a, 'b set] \<Rightarrow> 'a"
  where "foldD D f e A = (THE x. (A, x) \<in> foldSetD D f e)"

lemma foldSetD_closed: "(A, z) \<in> foldSetD D f e \<Longrightarrow> z \<in> D"
  by (erule foldSetD.cases) auto

lemma Diff1_foldSetD:
  "\<lbrakk>(A - {x}, y) \<in> foldSetD D f e; x \<in> A; f x y \<in> D\<rbrakk> \<Longrightarrow>
   (A, f x y) \<in> foldSetD D f e"
  by (metis Diff_insert_absorb foldSetD.insertI mk_disjoint_insert)

lemma foldSetD_imp_finite [simp]: "(A, x) \<in> foldSetD D f e \<Longrightarrow> finite A"
  by (induct set: foldSetD) auto

lemma finite_imp_foldSetD:
  "\<lbrakk>finite A; e \<in> D; \<And>x y. \<lbrakk>x \<in> A; y \<in> D\<rbrakk> \<Longrightarrow> f x y \<in> D\<rbrakk>
    \<Longrightarrow> \<exists>x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by (auto dest: foldSetD_closed)
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed

lemma foldSetD_backwards:
  assumes "A \<noteq> {}" "(A, z) \<in> foldSetD D f e"
  shows "\<exists>x y. x \<in> A \<and> (A - { x }, y) \<in> foldSetD D f e \<and> z = f x y"
  using assms(2) by (cases) (simp add: assms(1), metis Diff_insert_absorb insertI1)

subsubsection \<open>Left-Commutative Operations\<close>

locale LCD =
  fixes B :: "'b set"
  and D :: "'a set"
  and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl \<open>\<cdot>\<close> 70)
  assumes left_commute:
    "\<lbrakk>x \<in> B; y \<in> B; z \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  and f_closed [simp, intro!]: "!!x y. \<lbrakk>x \<in> B; y \<in> D\<rbrakk> \<Longrightarrow> f x y \<in> D"

lemma (in LCD) foldSetD_closed [dest]: "(A, z) \<in> foldSetD D f e \<Longrightarrow> z \<in> D"
  by (erule foldSetD.cases) auto

lemma (in LCD) Diff1_foldSetD:
  "\<lbrakk>(A - {x}, y) \<in> foldSetD D f e; x \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow>
  (A, f x y) \<in> foldSetD D f e"
  by (meson Diff1_foldSetD f_closed local.foldSetD_closed subsetCE)

lemma (in LCD) finite_imp_foldSetD:
  "\<lbrakk>finite A; A \<subseteq> B; e \<in> D\<rbrakk> \<Longrightarrow> \<exists>x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by auto
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed


lemma (in LCD) foldSetD_determ_aux:
  assumes "e \<in> D" and A: "card A < n" "A \<subseteq> B" "(A, x) \<in> foldSetD D f e" "(A, y) \<in> foldSetD D f e"
  shows "y = x"
  using A
proof (induction n arbitrary: A x y)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then consider "card A = n" | "card A < n"
    by linarith
  then show ?case
  proof cases
    case 1
    show ?thesis
      using foldSetD.cases [OF \<open>(A,x) \<in> foldSetD D (\<cdot>) e\<close>]
    proof cases
      case 1
      then show ?thesis
        using \<open>(A,y) \<in> foldSetD D (\<cdot>) e\<close> by auto
    next
      case (2 x' A' y')
      note A' = this
      show ?thesis
        using foldSetD.cases [OF \<open>(A,y) \<in> foldSetD D (\<cdot>) e\<close>]
      proof cases
        case 1
        then show ?thesis
          using \<open>(A,x) \<in> foldSetD D (\<cdot>) e\<close> by auto
      next
        case (2 x'' A'' y'')
        note A'' = this
        show ?thesis
        proof (cases "x' = x''")
          case True
          show ?thesis
          proof (cases "y' = y''")
            case True
            then show ?thesis
              using A' A'' \<open>x' = x''\<close> by (blast elim!: equalityE)
          next
            case False
            then show ?thesis
              using A' A'' \<open>x' = x''\<close> 
              by (metis \<open>card A = n\<close> Suc.IH Suc.prems(2) card_insert_disjoint foldSetD_imp_finite insert_eq_iff insert_subset lessI)
          qed
        next
          case False
          then have *: "A' - {x''} = A'' - {x'}" "x'' \<in> A'" "x' \<in> A''"
            using A' A'' by fastforce+
          then have "A' = insert x'' A'' - {x'}"
            using \<open>x' \<notin> A'\<close> by blast
          then have card: "card A' \<le> card A''"
            using A' A'' * by (metis card_Suc_Diff1 eq_refl foldSetD_imp_finite)
          obtain u where u: "(A' - {x''}, u) \<in> foldSetD D (\<cdot>) e"
            using finite_imp_foldSetD [of "A' - {x''}"] A' Diff_insert \<open>A \<subseteq> B\<close> \<open>e \<in> D\<close> by fastforce
          have "y' = f x'' u"
            using Diff1_foldSetD [OF u] \<open>x'' \<in> A'\<close> \<open>card A = n\<close> A' Suc.IH \<open>A \<subseteq> B\<close> by auto
          then have "(A'' - {x'}, u) \<in> foldSetD D f e"
            using "*"(1) u by auto
          then have "y'' = f x' u"
            using A'' by (metis * \<open>card A = n\<close> A'(1) Diff1_foldSetD Suc.IH \<open>A \<subseteq> B\<close>
                card card_Suc_Diff1 card_insert_disjoint foldSetD_imp_finite insert_subset le_imp_less_Suc)
          then show ?thesis
            using A' A''
            by (metis \<open>A \<subseteq> B\<close> \<open>y' = x'' \<cdot> u\<close> insert_subset left_commute local.foldSetD_closed u)
        qed   
      qed
    qed
  next
    case 2 with Suc show ?thesis by blast
  qed
qed

lemma (in LCD) foldSetD_determ:
  "\<lbrakk>(A, x) \<in> foldSetD D f e; (A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B\<rbrakk>
  \<Longrightarrow> y = x"
  by (blast intro: foldSetD_determ_aux [rule_format])

lemma (in LCD) foldD_equality:
  "\<lbrakk>(A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B\<rbrakk> \<Longrightarrow> foldD D f e A = y"
  by (unfold foldD_def) (blast intro: foldSetD_determ)

lemma foldD_empty [simp]:
  "e \<in> D \<Longrightarrow> foldD D f e {} = e"
  by (unfold foldD_def) blast

lemma (in LCD) foldD_insert_aux:
  "\<lbrakk>x \<notin> A; x \<in> B; e \<in> D; A \<subseteq> B\<rbrakk>
    \<Longrightarrow> ((insert x A, v) \<in> foldSetD D f e) \<longleftrightarrow> (\<exists>y. (A, y) \<in> foldSetD D f e \<and> v = f x y)"
  apply auto
  by (metis Diff_insert_absorb f_closed finite_Diff foldSetD.insertI foldSetD_determ foldSetD_imp_finite insert_subset local.finite_imp_foldSetD local.foldSetD_closed)

lemma (in LCD) foldD_insert:
  assumes "finite A" "x \<notin> A" "x \<in> B" "e \<in> D" "A \<subseteq> B"
  shows "foldD D f e (insert x A) = f x (foldD D f e A)"
proof -
  have "(THE v. \<exists>y. (A, y) \<in> foldSetD D (\<cdot>) e \<and> v = x \<cdot> y) = x \<cdot> (THE y. (A, y) \<in> foldSetD D (\<cdot>) e)"
    by (rule the_equality) (use assms foldD_def foldD_equality foldD_def finite_imp_foldSetD in \<open>metis+\<close>)
  then show ?thesis
    unfolding foldD_def using assms by (simp add: foldD_insert_aux)
qed

lemma (in LCD) foldD_closed [simp]:
  "\<lbrakk>finite A; e \<in> D; A \<subseteq> B\<rbrakk> \<Longrightarrow> foldD D f e A \<in> D"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: foldD_insert)
qed

lemma (in LCD) foldD_commute:
  "\<lbrakk>finite A; x \<in> B; e \<in> D; A \<subseteq> B\<rbrakk> \<Longrightarrow>
   f x (foldD D f e A) = foldD D f (f x e) A"
  by (induct set: finite) (auto simp add: left_commute foldD_insert)

lemma Int_mono2:
  "\<lbrakk>A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> A Int B \<subseteq> C"
  by blast

lemma (in LCD) foldD_nest_Un_Int:
  "\<lbrakk>finite A; finite C; e \<in> D; A \<subseteq> B; C \<subseteq> B\<rbrakk> \<Longrightarrow>
   foldD D f (foldD D f e C) A = foldD D f (foldD D f e (A Int C)) (A Un C)"
proof (induction set: finite)
  case (insert x F)
  then show ?case 
    by (simp add: foldD_insert foldD_commute Int_insert_left insert_absorb Int_mono2)
qed simp

lemma (in LCD) foldD_nest_Un_disjoint:
  "\<lbrakk>finite A; finite B; A Int B = {}; e \<in> D; A \<subseteq> B; C \<subseteq> B\<rbrakk>
    \<Longrightarrow> foldD D f e (A Un B) = foldD D f (foldD D f e B) A"
  by (simp add: foldD_nest_Un_Int)

\<comment> \<open>Delete rules to do with \<open>foldSetD\<close> relation.\<close>

declare foldSetD_imp_finite [simp del]
  empty_foldSetDE [rule del]
  foldSetD.intros [rule del]
declare (in LCD)
  foldSetD_closed [rule del]


text \<open>Commutative Monoids\<close>

text \<open>
  We enter a more restrictive context, with \<open>f :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  instead of \<open>'b \<Rightarrow> 'a \<Rightarrow> 'a\<close>.
\<close>

locale ACeD =
  fixes D :: "'a set"
    and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl \<open>\<cdot>\<close> 70)
    and e :: 'a
  assumes ident [simp]: "x \<in> D \<Longrightarrow> x \<cdot> e = x"
    and commute: "\<lbrakk>x \<in> D; y \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
    and assoc: "\<lbrakk>x \<in> D; y \<in> D; z \<in> D\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and e_closed [simp]: "e \<in> D"
    and f_closed [simp]: "\<lbrakk>x \<in> D; y \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> D"

lemma (in ACeD) left_commute:
  "\<lbrakk>x \<in> D; y \<in> D; z \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  assume D: "x \<in> D" "y \<in> D" "z \<in> D"
  then have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp add: commute)
  also from D have "... = y \<cdot> (z \<cdot> x)" by (simp add: assoc)
  also from D have "z \<cdot> x = x \<cdot> z" by (simp add: commute)
  finally show ?thesis .
qed

lemmas (in ACeD) AC = assoc commute left_commute

lemma (in ACeD) left_ident [simp]: "x \<in> D \<Longrightarrow> e \<cdot> x = x"
proof -
  assume "x \<in> D"
  then have "x \<cdot> e = x" by (rule ident)
  with \<open>x \<in> D\<close> show ?thesis by (simp add: commute)
qed

lemma (in ACeD) foldD_Un_Int:
  "\<lbrakk>finite A; finite B; A \<subseteq> D; B \<subseteq> D\<rbrakk> \<Longrightarrow>
    foldD D f e A \<cdot> foldD D f e B =
    foldD D f e (A Un B) \<cdot> foldD D f e (A Int B)"
proof (induction set: finite)
  case empty
  then show ?case 
    by(simp add: left_commute LCD.foldD_closed [OF LCD.intro [of D]])
next
  case (insert x F)
  then show ?case
    by(simp add: AC insert_absorb Int_insert_left Int_mono2
                 LCD.foldD_insert [OF LCD.intro [of D]]
                 LCD.foldD_closed [OF LCD.intro [of D]])
qed

lemma (in ACeD) foldD_Un_disjoint:
  "\<lbrakk>finite A; finite B; A Int B = {}; A \<subseteq> D; B \<subseteq> D\<rbrakk> \<Longrightarrow>
    foldD D f e (A Un B) = foldD D f e A \<cdot> foldD D f e B"
  by (simp add: foldD_Un_Int
    left_commute LCD.foldD_closed [OF LCD.intro [of D]])


subsubsection \<open>Products over Finite Sets\<close>

definition
  finprod :: "[('b, 'm) monoid_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b"
  where "finprod G f A =
   (if finite A
    then foldD (carrier G) (mult G \<circ> f) \<one>\<^bsub>G\<^esub> A
    else \<one>\<^bsub>G\<^esub>)"

syntax
  "_finprod" :: "index \<Rightarrow> idt \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"
    (\<open>(\<open>indent=3 notation=\<open>binder \<Otimes>\<close>\<close>\<Otimes>__\<in>_. _)\<close> [1000, 0, 51, 10] 10)
syntax_consts
  "_finprod" \<rightleftharpoons> finprod
translations
  "\<Otimes>\<^bsub>G\<^esub>i\<in>A. b" \<rightleftharpoons> "CONST finprod G (%i. b) A"
  \<comment> \<open>Beware of argument permutation!\<close>

lemma (in comm_monoid) finprod_empty [simp]:
  "finprod G f {} = \<one>"
  by (simp add: finprod_def)

lemma (in comm_monoid) finprod_infinite[simp]:
  "\<not> finite A \<Longrightarrow> finprod G f A = \<one>"
  by (simp add: finprod_def)

declare funcsetI [intro]
  funcset_mem [dest]

context comm_monoid begin

lemma finprod_insert [simp]:
  assumes "finite F" "a \<notin> F" "f \<in> F \<rightarrow> carrier G" "f a \<in> carrier G"
  shows "finprod G f (insert a F) = f a \<otimes> finprod G f F"
proof -
  have "finprod G f (insert a F) = foldD (carrier G) ((\<otimes>) \<circ> f) \<one> (insert a F)"
    by (simp add: finprod_def assms)
  also have "... = ((\<otimes>) \<circ> f) a (foldD (carrier G) ((\<otimes>) \<circ> f) \<one> F)"
    by (rule LCD.foldD_insert [OF LCD.intro [of "insert a F"]])
      (use assms in \<open>auto simp: m_lcomm Pi_iff\<close>)
  also have "... = f a \<otimes> finprod G f F"
    using \<open>finite F\<close> by (auto simp add: finprod_def)
  finally show ?thesis .
qed

lemma finprod_one_eqI: "(\<And>x. x \<in> A \<Longrightarrow> f x = \<one>) \<Longrightarrow> finprod G f A = \<one>"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A)
  have "(\<lambda>i. \<one>) \<in> A \<rightarrow> carrier G" by auto
  with insert show ?case by simp
qed simp

lemma finprod_one [simp]: "(\<Otimes>i\<in>A. \<one>) = \<one>"
  by (simp add: finprod_one_eqI)

lemma finprod_closed [simp]:
  fixes A
  assumes f: "f \<in> A \<rightarrow> carrier G"
  shows "finprod G f A \<in> carrier G"
using f
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A)
  then have a: "f a \<in> carrier G" by fast
  from insert have A: "f \<in> A \<rightarrow> carrier G" by fast
  from insert A a show ?case by simp
qed simp

lemma funcset_Int_left [simp, intro]:
  "\<lbrakk>f \<in> A \<rightarrow> C; f \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> f \<in> A Int B \<rightarrow> C"
  by fast

lemma funcset_Un_left [iff]:
  "(f \<in> A Un B \<rightarrow> C) = (f \<in> A \<rightarrow> C \<and> f \<in> B \<rightarrow> C)"
  by fast

lemma finprod_Un_Int:
  "\<lbrakk>finite A; finite B; g \<in> A \<rightarrow> carrier G; g \<in> B \<rightarrow> carrier G\<rbrakk> \<Longrightarrow>
     finprod G g (A Un B) \<otimes> finprod G g (A Int B) =
     finprod G g A \<otimes> finprod G g B"
\<comment> \<open>The reversed orientation looks more natural, but LOOPS as a simprule!\<close>
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert a A)
  then have a: "g a \<in> carrier G" by fast
  from insert have A: "g \<in> A \<rightarrow> carrier G" by fast
  from insert A a show ?case
    by (simp add: m_ac Int_insert_left insert_absorb Int_mono2)
qed

lemma finprod_Un_disjoint:
  "\<lbrakk>finite A; finite B; A Int B = {};
      g \<in> A \<rightarrow> carrier G; g \<in> B \<rightarrow> carrier G\<rbrakk>
   \<Longrightarrow> finprod G g (A Un B) = finprod G g A \<otimes> finprod G g B"
  by (metis Pi_split_domain finprod_Un_Int finprod_closed finprod_empty r_one)

lemma finprod_multf [simp]:
  "\<lbrakk>f \<in> A \<rightarrow> carrier G; g \<in> A \<rightarrow> carrier G\<rbrakk> \<Longrightarrow>
   finprod G (\<lambda>x. f x \<otimes> g x) A = (finprod G f A \<otimes> finprod G g A)"
proof (induct A rule: infinite_finite_induct)
  case empty show ?case by simp
next
  case (insert a A) then
  have fA: "f \<in> A \<rightarrow> carrier G" by fast
  from insert have fa: "f a \<in> carrier G" by fast
  from insert have gA: "g \<in> A \<rightarrow> carrier G" by fast
  from insert have ga: "g a \<in> carrier G" by fast
  from insert have fgA: "(%x. f x \<otimes> g x) \<in> A \<rightarrow> carrier G"
    by (simp add: Pi_def)
  show ?case
    by (simp add: insert fA fa gA ga fgA m_ac)
qed simp

lemma finprod_cong':
  "\<lbrakk>A = B; g \<in> B \<rightarrow> carrier G;
      !!i. i \<in> B \<Longrightarrow> f i = g i\<rbrakk> \<Longrightarrow> finprod G f A = finprod G g B"
proof -
  assume prems: "A = B" "g \<in> B \<rightarrow> carrier G"
    "!!i. i \<in> B \<Longrightarrow> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. \<lbrakk>A = B; g \<in> B \<rightarrow> carrier G;
      !!i. i \<in> B \<Longrightarrow> f i = g i\<rbrakk> \<Longrightarrow> finprod G f A = finprod G g B"
    proof induct
      case empty thus ?case by simp
    next
      case (insert x B)
      then have "finprod G f A = finprod G f (insert x B)" by simp
      also from insert have "... = f x \<otimes> finprod G f B"
      proof (intro finprod_insert)
        show "finite B" by fact
      next
        show "x \<notin> B" by fact
      next
        assume "x \<notin> B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
          "g \<in> insert x B \<rightarrow> carrier G"
        thus "f \<in> B \<rightarrow> carrier G" by fastforce
      next
        assume "x \<notin> B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
          "g \<in> insert x B \<rightarrow> carrier G"
        thus "f x \<in> carrier G" by fastforce
      qed
      also from insert have "... = g x \<otimes> finprod G g B" by fastforce
      also from insert have "... = finprod G g (insert x B)"
      by (intro finprod_insert [THEN sym]) auto
      finally show ?case .
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by simp
  qed
qed

lemma finprod_cong:
  "\<lbrakk>A = B; f \<in> B \<rightarrow> carrier G = True;
      \<And>i. i \<in> B =simp=> f i = g i\<rbrakk> \<Longrightarrow> finprod G f A = finprod G g B"
  (* This order of prems is slightly faster (3%) than the last two swapped. *)
  by (rule finprod_cong') (auto simp add: simp_implies_def)

text \<open>Usually, if this rule causes a failed congruence proof error,
  the reason is that the premise \<open>g \<in> B \<rightarrow> carrier G\<close> cannot be shown.
  Adding @{thm [source] Pi_def} to the simpset is often useful.
  For this reason, @{thm [source] finprod_cong}
  is not added to the simpset by default.
\<close>

end

declare funcsetI [rule del]
  funcset_mem [rule del]

context comm_monoid begin

lemma finprod_0 [simp]:
  "f \<in> {0::nat} \<rightarrow> carrier G \<Longrightarrow> finprod G f {..0} = f 0"
  by (simp add: Pi_def)

lemma finprod_0':
  "f \<in> {..n} \<rightarrow> carrier G \<Longrightarrow> (f 0) \<otimes> finprod G f {Suc 0..n} = finprod G f {..n}"
proof -
  assume A: "f \<in> {.. n} \<rightarrow> carrier G"
  hence "(f 0) \<otimes> finprod G f {Suc 0..n} = finprod G f {..0} \<otimes> finprod G f {Suc 0..n}"
    using finprod_0[of f] by (simp add: funcset_mem)
  also have " ... = finprod G f ({..0} \<union> {Suc 0..n})"
    using finprod_Un_disjoint[of "{..0}" "{Suc 0..n}" f] A by (simp add: funcset_mem)
  also have " ... = finprod G f {..n}"
    by (simp add: atLeastAtMost_insertL atMost_atLeast0)
  finally show ?thesis .
qed

lemma finprod_Suc [simp]:
  "f \<in> {..Suc n} \<rightarrow> carrier G \<Longrightarrow>
   finprod G f {..Suc n} = (f (Suc n) \<otimes> finprod G f {..n})"
by (simp add: Pi_def atMost_Suc)

lemma finprod_Suc2:
  "f \<in> {..Suc n} \<rightarrow> carrier G \<Longrightarrow>
   finprod G f {..Suc n} = (finprod G (%i. f (Suc i)) {..n} \<otimes> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case by (simp add: m_assoc Pi_def)
qed

lemma finprod_Suc3:
  assumes "f \<in> {..n :: nat} \<rightarrow> carrier G"
  shows "finprod G f {.. n} = (f n) \<otimes> finprod G f {..< n}"
proof (cases "n = 0")
  case True thus ?thesis
   using assms atMost_Suc by simp
next
  case False
  then obtain k where "n = Suc k"
    using not0_implies_Suc by blast
  thus ?thesis
    using finprod_Suc[of f k] assms atMost_Suc lessThan_Suc_atMost by simp
qed

lemma finprod_reindex: \<^marker>\<open>contributor \<open>Jeremy Avigad\<close>\<close>
  "f \<in> (h ` A) \<rightarrow> carrier G \<Longrightarrow>
        inj_on h A \<Longrightarrow> finprod G f (h ` A) = finprod G (\<lambda>x. f (h x)) A"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  hence "\<not> finite (h ` A)"
    using finite_imageD by blast
  with \<open>\<not> finite A\<close> show ?case by simp
qed (auto simp add: Pi_def)

lemma finprod_const: \<^marker>\<open>contributor \<open>Jeremy Avigad\<close>\<close>
  assumes a [simp]: "a \<in> carrier G"
    shows "finprod G (\<lambda>x. a) A = a [^] card A"
proof (induct A rule: infinite_finite_induct)
  case (insert b A)
  show ?case
  proof (subst finprod_insert[OF insert(1-2)])
    show "a \<otimes> (\<Otimes>x\<in>A. a) = a [^] card (insert b A)"
      by (insert insert, auto, subst m_comm, auto)
  qed auto
qed auto

lemma finprod_singleton: \<^marker>\<open>contributor \<open>Jesus Aransay\<close>\<close>
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and f_Pi: "f \<in> A \<rightarrow> carrier G"
  shows "(\<Otimes>j\<in>A. if i = j then f j else \<one>) = f i"
  using i_in_A finprod_insert [of "A - {i}" i "(\<lambda>j. if i = j then f j else \<one>)"]
    fin_A f_Pi finprod_one [of "A - {i}"]
    finprod_cong [of "A - {i}" "A - {i}" "(\<lambda>j. if i = j then f j else \<one>)" "(\<lambda>i. \<one>)"]
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)

lemma finprod_singleton_swap:
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and f_Pi: "f \<in> A \<rightarrow> carrier G"
  shows "(\<Otimes>j\<in>A. if j = i then f j else \<one>) = f i"
  using finprod_singleton [OF assms] by (simp add: eq_commute)

lemma finprod_mono_neutral_cong_left:
  assumes "finite B"
    and "A \<subseteq> B"
    and 1: "\<And>i. i \<in> B - A \<Longrightarrow> h i = \<one>"
    and gh: "\<And>x. x \<in> A \<Longrightarrow> g x = h x"
    and h: "h \<in> B \<rightarrow> carrier G"
  shows "finprod G g A = finprod G h B"
proof-
  have eq: "A \<union> (B - A) = B" using \<open>A \<subseteq> B\<close> by blast
  have d: "A \<inter> (B - A) = {}" using \<open>A \<subseteq> B\<close> by blast
  from \<open>finite B\<close> \<open>A \<subseteq> B\<close> have f: "finite A" "finite (B - A)"
    by (auto intro: finite_subset)
  have "h \<in> A \<rightarrow> carrier G" "h \<in> B - A \<rightarrow> carrier G"
    using assms by (auto simp: image_subset_iff_funcset)
  moreover have "finprod G g A = finprod G h A \<otimes> finprod G h (B - A)"
  proof -
    have "finprod G h (B - A) = \<one>"
      using "1" finprod_one_eqI by blast
    moreover have "finprod G g A = finprod G h A"
      using \<open>h \<in> A \<rightarrow> carrier G\<close> finprod_cong' gh by blast
    ultimately show ?thesis
      by (simp add: \<open>h \<in> A \<rightarrow> carrier G\<close>)
  qed
  ultimately show ?thesis
    by (simp add: finprod_Un_disjoint [OF f d, unfolded eq])
qed

lemma finprod_mono_neutral_cong_right:
  assumes "finite B"
    and "A \<subseteq> B" "\<And>i. i \<in> B - A \<Longrightarrow> g i = \<one>" "\<And>x. x \<in> A \<Longrightarrow> g x = h x" "g \<in> B \<rightarrow> carrier G"
  shows "finprod G g B = finprod G h A"
  using assms  by (auto intro!: finprod_mono_neutral_cong_left [symmetric])

lemma finprod_mono_neutral_cong:
  assumes [simp]: "finite B" "finite A"
    and *: "\<And>i. i \<in> B - A \<Longrightarrow> h i = \<one>" "\<And>i. i \<in> A - B \<Longrightarrow> g i = \<one>"
    and gh: "\<And>x. x \<in> A \<inter> B \<Longrightarrow> g x = h x"
    and g: "g \<in> A \<rightarrow> carrier G"
    and h: "h \<in> B \<rightarrow> carrier G"
 shows "finprod G g A = finprod G h B"
proof-
  have "finprod G g A = finprod G g (A \<inter> B)"
    by (rule finprod_mono_neutral_cong_right) (use assms in auto)
  also have "\<dots> = finprod G h (A \<inter> B)"
    by (rule finprod_cong) (use assms in auto)
  also have "\<dots> = finprod G h B"
    by (rule finprod_mono_neutral_cong_left) (use assms in auto)
  finally show ?thesis .
qed

end

(* Jeremy Avigad. This should be generalized to arbitrary groups, not just commutative
   ones, using Lagrange's theorem. *)

lemma (in comm_group) power_order_eq_one:
  assumes fin [simp]: "finite (carrier G)"
    and a [simp]: "a \<in> carrier G"
  shows "a [^] card(carrier G) = one G"
proof -
  have "(\<Otimes>x\<in>carrier G. x) = (\<Otimes>x\<in>carrier G. a \<otimes> x)"
    by (subst (2) finprod_reindex [symmetric],
      auto simp add: Pi_def inj_on_cmult surj_const_mult)
  also have "\<dots> = (\<Otimes>x\<in>carrier G. a) \<otimes> (\<Otimes>x\<in>carrier G. x)"
    by (auto simp add: finprod_multf Pi_def)
  also have "(\<Otimes>x\<in>carrier G. a) = a [^] card(carrier G)"
    by (auto simp add: finprod_const)
  finally show ?thesis
    by auto
qed

lemma (in comm_monoid) finprod_UN_disjoint:
  assumes
    "finite I" "\<And>i. i \<in> I \<Longrightarrow> finite (A i)" "pairwise (\<lambda>i j. disjnt (A i) (A j)) I"
    "\<And>i x. i \<in> I \<Longrightarrow> x \<in> A i \<Longrightarrow> g x \<in> carrier G"
shows "finprod G g (\<Union>(A ` I)) = finprod G (\<lambda>i. finprod G g (A i)) I"
  using assms
proof (induction set: finite)
  case empty
  then show ?case
    by force
next
  case (insert i I)
  then show ?case
    unfolding pairwise_def disjnt_def
    apply clarsimp
    apply (subst finprod_Un_disjoint)
         apply (fastforce intro!: funcsetI finprod_closed)+
    done
qed

lemma (in comm_monoid) finprod_Union_disjoint:
  "\<lbrakk>finite C; \<And>A. A \<in> C \<Longrightarrow> finite A \<and> (\<forall>x\<in>A. f x \<in> carrier G); pairwise disjnt C\<rbrakk> \<Longrightarrow>
    finprod G f (\<Union>C) = finprod G (finprod G f) C"
  by (frule finprod_UN_disjoint [of C id f]) auto

end
