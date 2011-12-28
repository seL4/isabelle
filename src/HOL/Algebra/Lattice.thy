(*  Title:      HOL/Algebra/Lattice.thy
    Author:     Clemens Ballarin, started 7 November 2003
    Copyright:  Clemens Ballarin

Most congruence rules by Stephan Hohe.
*)

theory Lattice
imports Congruence
begin

section {* Orders and Lattices *}

subsection {* Partial Orders *}

record 'a gorder = "'a eq_object" +
  le :: "['a, 'a] => bool" (infixl "\<sqsubseteq>\<index>" 50)

locale weak_partial_order = equivalence L for L (structure) +
  assumes le_refl [intro, simp]:
      "x \<in> carrier L ==> x \<sqsubseteq> x"
    and weak_le_antisym [intro]:
      "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L |] ==> x .= y"
    and le_trans [trans]:
      "[| x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L |] ==> x \<sqsubseteq> z"
    and le_cong:
      "\<lbrakk> x .= y; z .= w; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L; w \<in> carrier L \<rbrakk> \<Longrightarrow>
      x \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> w"

definition
  lless :: "[_, 'a, 'a] => bool" (infixl "\<sqsubset>\<index>" 50)
  where "x \<sqsubset>\<^bsub>L\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> y & x .\<noteq>\<^bsub>L\<^esub> y"


subsubsection {* The order relation *}

context weak_partial_order
begin

lemma le_cong_l [intro, trans]:
  "\<lbrakk> x .= y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD2])

lemma le_cong_r [intro, trans]:
  "\<lbrakk> x \<sqsubseteq> y; y .= z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD1])

lemma weak_refl [intro, simp]: "\<lbrakk> x .= y; x \<in> carrier L; y \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: le_cong_l)

end

lemma weak_llessI:
  fixes R (structure)
  assumes "x \<sqsubseteq> y" and "~(x .= y)"
  shows "x \<sqsubset> y"
  using assms unfolding lless_def by simp

lemma lless_imp_le:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "x \<sqsubseteq> y"
  using assms unfolding lless_def by simp

lemma weak_lless_imp_not_eq:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "\<not> (x .= y)"
  using assms unfolding lless_def by simp

lemma weak_llessE:
  fixes R (structure)
  assumes p: "x \<sqsubset> y" and e: "\<lbrakk>x \<sqsubseteq> y; \<not> (x .= y)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using p by (blast dest: lless_imp_le weak_lless_imp_not_eq e)

lemma (in weak_partial_order) lless_cong_l [trans]:
  assumes xx': "x .= x'"
    and xy: "x' \<sqsubset> y"
    and carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubset> y"
  using assms unfolding lless_def by (auto intro: trans sym)

lemma (in weak_partial_order) lless_cong_r [trans]:
  assumes xy: "x \<sqsubset> y"
    and  yy': "y .= y'"
    and carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
  shows "x \<sqsubset> y'"
  using assms unfolding lless_def by (auto intro: trans sym)  (*slow*)


lemma (in weak_partial_order) lless_antisym:
  assumes "a \<in> carrier L" "b \<in> carrier L"
    and "a \<sqsubset> b" "b \<sqsubset> a"
  shows "P"
  using assms
  by (elim weak_llessE) auto

lemma (in weak_partial_order) lless_trans [trans]:
  assumes "a \<sqsubset> b" "b \<sqsubset> c"
    and carr[simp]: "a \<in> carrier L" "b \<in> carrier L" "c \<in> carrier L"
  shows "a \<sqsubset> c"
  using assms unfolding lless_def by (blast dest: le_trans intro: sym)


subsubsection {* Upper and lower bounds of a set *}

definition
  Upper :: "[_, 'a set] => 'a set"
  where "Upper L A = {u. (ALL x. x \<in> A \<inter> carrier L --> x \<sqsubseteq>\<^bsub>L\<^esub> u)} \<inter> carrier L"

definition
  Lower :: "[_, 'a set] => 'a set"
  where "Lower L A = {l. (ALL x. x \<in> A \<inter> carrier L --> l \<sqsubseteq>\<^bsub>L\<^esub> x)} \<inter> carrier L"

lemma Upper_closed [intro!, simp]:
  "Upper L A \<subseteq> carrier L"
  by (unfold Upper_def) clarify

lemma Upper_memD [dest]:
  fixes L (structure)
  shows "[| u \<in> Upper L A; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u \<and> u \<in> carrier L"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_elemD [dest]:
  "[| u .\<in> Upper L A; u \<in> carrier L; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u"
  unfolding Upper_def elem_def
  by (blast dest: sym)

lemma Upper_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x \<in> Upper L A"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_elemI:
  "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x .\<in> Upper L A"
  unfolding Upper_def by blast

lemma Upper_antimono:
  "A \<subseteq> B ==> Upper L B \<subseteq> Upper L A"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_is_closed [simp]:
  "A \<subseteq> carrier L ==> is_closed (Upper L A)"
  by (rule is_closedI) (blast intro: Upper_memI)+

lemma (in weak_partial_order) Upper_mem_cong:
  assumes a'carr: "a' \<in> carrier L" and Acarr: "A \<subseteq> carrier L"
    and aa': "a .= a'"
    and aelem: "a \<in> Upper L A"
  shows "a' \<in> Upper L A"
proof (rule Upper_memI[OF _ a'carr])
  fix y
  assume yA: "y \<in> A"
  hence "y \<sqsubseteq> a" by (intro Upper_memD[OF aelem, THEN conjunct1] Acarr)
  also note aa'
  finally
      show "y \<sqsubseteq> a'"
      by (simp add: a'carr subsetD[OF Acarr yA] subsetD[OF Upper_closed aelem])
qed

lemma (in weak_partial_order) Upper_cong:
  assumes Acarr: "A \<subseteq> carrier L" and A'carr: "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "Upper L A = Upper L A'"
unfolding Upper_def
apply rule
 apply (rule, clarsimp) defer 1
 apply (rule, clarsimp) defer 1
proof -
  fix x a'
  assume carr: "x \<in> carrier L" "a' \<in> carrier L"
    and a'A': "a' \<in> A'"
  assume aLxCond[rule_format]: "\<forall>a. a \<in> A \<and> a \<in> carrier L \<longrightarrow> a \<sqsubseteq> x"

  from AA' and a'A' have "\<exists>a\<in>A. a' .= a" by (rule set_eqD2)
  from this obtain a
      where aA: "a \<in> A"
      and a'a: "a' .= a"
      by auto
  note [simp] = subsetD[OF Acarr aA] carr

  note a'a
  also have "a \<sqsubseteq> x" by (simp add: aLxCond aA)
  finally show "a' \<sqsubseteq> x" by simp
next
  fix x a
  assume carr: "x \<in> carrier L" "a \<in> carrier L"
    and aA: "a \<in> A"
  assume a'LxCond[rule_format]: "\<forall>a'. a' \<in> A' \<and> a' \<in> carrier L \<longrightarrow> a' \<sqsubseteq> x"

  from AA' and aA have "\<exists>a'\<in>A'. a .= a'" by (rule set_eqD1)
  from this obtain a'
      where a'A': "a' \<in> A'"
      and aa': "a .= a'"
      by auto
  note [simp] = subsetD[OF A'carr a'A'] carr

  note aa'
  also have "a' \<sqsubseteq> x" by (simp add: a'LxCond a'A')
  finally show "a \<sqsubseteq> x" by simp
qed

lemma Lower_closed [intro!, simp]:
  "Lower L A \<subseteq> carrier L"
  by (unfold Lower_def) clarify

lemma Lower_memD [dest]:
  fixes L (structure)
  shows "[| l \<in> Lower L A; x \<in> A; A \<subseteq> carrier L |] ==> l \<sqsubseteq> x \<and> l \<in> carrier L"
  by (unfold Lower_def) blast

lemma Lower_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> x \<sqsubseteq> y; x \<in> carrier L |] ==> x \<in> Lower L A"
  by (unfold Lower_def) blast

lemma Lower_antimono:
  "A \<subseteq> B ==> Lower L B \<subseteq> Lower L A"
  by (unfold Lower_def) blast

lemma (in weak_partial_order) Lower_is_closed [simp]:
  "A \<subseteq> carrier L \<Longrightarrow> is_closed (Lower L A)"
  by (rule is_closedI) (blast intro: Lower_memI dest: sym)+

lemma (in weak_partial_order) Lower_mem_cong:
  assumes a'carr: "a' \<in> carrier L" and Acarr: "A \<subseteq> carrier L"
    and aa': "a .= a'"
    and aelem: "a \<in> Lower L A"
  shows "a' \<in> Lower L A"
using assms Lower_closed[of L A]
by (intro Lower_memI) (blast intro: le_cong_l[OF aa'[symmetric]])

lemma (in weak_partial_order) Lower_cong:
  assumes Acarr: "A \<subseteq> carrier L" and A'carr: "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "Lower L A = Lower L A'"
unfolding Lower_def
apply rule
 apply clarsimp defer 1
 apply clarsimp defer 1
proof -
  fix x a'
  assume carr: "x \<in> carrier L" "a' \<in> carrier L"
    and a'A': "a' \<in> A'"
  assume "\<forall>a. a \<in> A \<and> a \<in> carrier L \<longrightarrow> x \<sqsubseteq> a"
  hence aLxCond: "\<And>a. \<lbrakk>a \<in> A; a \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> a" by fast

  from AA' and a'A' have "\<exists>a\<in>A. a' .= a" by (rule set_eqD2)
  from this obtain a
      where aA: "a \<in> A"
      and a'a: "a' .= a"
      by auto

  from aA and subsetD[OF Acarr aA]
      have "x \<sqsubseteq> a" by (rule aLxCond)
  also note a'a[symmetric]
  finally
      show "x \<sqsubseteq> a'" by (simp add: carr subsetD[OF Acarr aA])
next
  fix x a
  assume carr: "x \<in> carrier L" "a \<in> carrier L"
    and aA: "a \<in> A"
  assume "\<forall>a'. a' \<in> A' \<and> a' \<in> carrier L \<longrightarrow> x \<sqsubseteq> a'"
  hence a'LxCond: "\<And>a'. \<lbrakk>a' \<in> A'; a' \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> a'" by fast+

  from AA' and aA have "\<exists>a'\<in>A'. a .= a'" by (rule set_eqD1)
  from this obtain a'
      where a'A': "a' \<in> A'"
      and aa': "a .= a'"
      by auto
  from a'A' and subsetD[OF A'carr a'A']
      have "x \<sqsubseteq> a'" by (rule a'LxCond)
  also note aa'[symmetric]
  finally show "x \<sqsubseteq> a" by (simp add: carr subsetD[OF A'carr a'A'])
qed


subsubsection {* Least and greatest, as predicate *}

definition
  least :: "[_, 'a, 'a set] => bool"
  where "least L l A \<longleftrightarrow> A \<subseteq> carrier L & l \<in> A & (ALL x : A. l \<sqsubseteq>\<^bsub>L\<^esub> x)"

definition
  greatest :: "[_, 'a, 'a set] => bool"
  where "greatest L g A \<longleftrightarrow> A \<subseteq> carrier L & g \<in> A & (ALL x : A. x \<sqsubseteq>\<^bsub>L\<^esub> g)"

text (in weak_partial_order) {* Could weaken these to @{term "l \<in> carrier L \<and> l
  .\<in> A"} and @{term "g \<in> carrier L \<and> g .\<in> A"}. *}

lemma least_closed [intro, simp]:
  "least L l A ==> l \<in> carrier L"
  by (unfold least_def) fast

lemma least_mem:
  "least L l A ==> l \<in> A"
  by (unfold least_def) fast

lemma (in weak_partial_order) weak_least_unique:
  "[| least L x A; least L y A |] ==> x .= y"
  by (unfold least_def) blast

lemma least_le:
  fixes L (structure)
  shows "[| least L x A; a \<in> A |] ==> x \<sqsubseteq> a"
  by (unfold least_def) fast

lemma (in weak_partial_order) least_cong:
  "[| x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A |] ==> least L x A = least L x' A"
  by (unfold least_def) (auto dest: sym)

text (in weak_partial_order) {* @{const least} is not congruent in the second parameter for 
  @{term "A {.=} A'"} *}

lemma (in weak_partial_order) least_Upper_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L"
  shows "least L x (Upper L A) = least L x' (Upper L A)"
  apply (rule least_cong) using assms by auto

lemma (in weak_partial_order) least_Upper_cong_r:
  assumes Acarrs: "A \<subseteq> carrier L" "A' \<subseteq> carrier L" (* unneccessary with current Upper? *)
    and AA': "A {.=} A'"
  shows "least L x (Upper L A) = least L x (Upper L A')"
apply (subgoal_tac "Upper L A = Upper L A'", simp)
by (rule Upper_cong) fact+

lemma least_UpperI:
  fixes L (structure)
  assumes above: "!! x. x \<in> A ==> x \<sqsubseteq> s"
    and below: "!! y. y \<in> Upper L A ==> s \<sqsubseteq> y"
    and L: "A \<subseteq> carrier L"  "s \<in> carrier L"
  shows "least L s (Upper L A)"
proof -
  have "Upper L A \<subseteq> carrier L" by simp
  moreover from above L have "s \<in> Upper L A" by (simp add: Upper_def)
  moreover from below have "ALL x : Upper L A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: least_def)
qed

lemma least_Upper_above:
  fixes L (structure)
  shows "[| least L s (Upper L A); x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> s"
  by (unfold least_def) blast

lemma greatest_closed [intro, simp]:
  "greatest L l A ==> l \<in> carrier L"
  by (unfold greatest_def) fast

lemma greatest_mem:
  "greatest L l A ==> l \<in> A"
  by (unfold greatest_def) fast

lemma (in weak_partial_order) weak_greatest_unique:
  "[| greatest L x A; greatest L y A |] ==> x .= y"
  by (unfold greatest_def) blast

lemma greatest_le:
  fixes L (structure)
  shows "[| greatest L x A; a \<in> A |] ==> a \<sqsubseteq> x"
  by (unfold greatest_def) fast

lemma (in weak_partial_order) greatest_cong:
  "[| x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A |] ==>
  greatest L x A = greatest L x' A"
  by (unfold greatest_def) (auto dest: sym)

text (in weak_partial_order) {* @{const greatest} is not congruent in the second parameter for 
  @{term "A {.=} A'"} *}

lemma (in weak_partial_order) greatest_Lower_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L" (* unneccessary with current Lower *)
  shows "greatest L x (Lower L A) = greatest L x' (Lower L A)"
  apply (rule greatest_cong) using assms by auto

lemma (in weak_partial_order) greatest_Lower_cong_r:
  assumes Acarrs: "A \<subseteq> carrier L" "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "greatest L x (Lower L A) = greatest L x (Lower L A')"
apply (subgoal_tac "Lower L A = Lower L A'", simp)
by (rule Lower_cong) fact+

lemma greatest_LowerI:
  fixes L (structure)
  assumes below: "!! x. x \<in> A ==> i \<sqsubseteq> x"
    and above: "!! y. y \<in> Lower L A ==> y \<sqsubseteq> i"
    and L: "A \<subseteq> carrier L"  "i \<in> carrier L"
  shows "greatest L i (Lower L A)"
proof -
  have "Lower L A \<subseteq> carrier L" by simp
  moreover from below L have "i \<in> Lower L A" by (simp add: Lower_def)
  moreover from above have "ALL x : Lower L A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: greatest_def)
qed

lemma greatest_Lower_below:
  fixes L (structure)
  shows "[| greatest L i (Lower L A); x \<in> A; A \<subseteq> carrier L |] ==> i \<sqsubseteq> x"
  by (unfold greatest_def) blast

text {* Supremum and infimum *}

definition
  sup :: "[_, 'a set] => 'a" ("\<Squnion>\<index>_" [90] 90)
  where "\<Squnion>\<^bsub>L\<^esub>A = (SOME x. least L x (Upper L A))"

definition
  inf :: "[_, 'a set] => 'a" ("\<Sqinter>\<index>_" [90] 90)
  where "\<Sqinter>\<^bsub>L\<^esub>A = (SOME x. greatest L x (Lower L A))"

definition
  join :: "[_, 'a, 'a] => 'a" (infixl "\<squnion>\<index>" 65)
  where "x \<squnion>\<^bsub>L\<^esub> y = \<Squnion>\<^bsub>L\<^esub>{x, y}"

definition
  meet :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)
  where "x \<sqinter>\<^bsub>L\<^esub> y = \<Sqinter>\<^bsub>L\<^esub>{x, y}"


subsection {* Lattices *}

locale weak_upper_semilattice = weak_partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. least L s (Upper L {x, y})"

locale weak_lower_semilattice = weak_partial_order +
  assumes inf_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. greatest L s (Lower L {x, y})"

locale weak_lattice = weak_upper_semilattice + weak_lower_semilattice


subsubsection {* Supremum *}

lemma (in weak_upper_semilattice) joinI:
  "[| !!l. least L l (Upper L {x, y}) ==> P l; x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<squnion> y)"
proof (unfold join_def sup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!l. least L l (Upper L {x, y}) ==> P l"
  with sup_of_two_exists obtain s where "least L s (Upper L {x, y})" by fast
  with L show "P (SOME l. least L l (Upper L {x, y}))"
    by (fast intro: someI2 P)
qed

lemma (in weak_upper_semilattice) join_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<squnion> y \<in> carrier L"
  by (rule joinI) (rule least_closed)

lemma (in weak_upper_semilattice) join_cong_l:
  assumes carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
    and xx': "x .= x'"
  shows "x \<squnion> y .= x' \<squnion> y"
proof (rule joinI, rule joinI)
  fix a b
  from xx' carr
      have seq: "{x, y} {.=} {x', y}" by (rule set_eq_pairI)

  assume leasta: "least L a (Upper L {x, y})"
  assume "least L b (Upper L {x', y})"
  with carr
      have leastb: "least L b (Upper L {x, y})"
      by (simp add: least_Upper_cong_r[OF _ _ seq])

  from leasta leastb
      show "a .= b" by (rule weak_least_unique)
qed (rule carr)+

lemma (in weak_upper_semilattice) join_cong_r:
  assumes carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
    and yy': "y .= y'"
  shows "x \<squnion> y .= x \<squnion> y'"
proof (rule joinI, rule joinI)
  fix a b
  have "{x, y} = {y, x}" by fast
  also from carr yy'
      have "{y, x} {.=} {y', x}" by (intro set_eq_pairI)
  also have "{y', x} = {x, y'}" by fast
  finally
      have seq: "{x, y} {.=} {x, y'}" .

  assume leasta: "least L a (Upper L {x, y})"
  assume "least L b (Upper L {x, y'})"
  with carr
      have leastb: "least L b (Upper L {x, y})"
      by (simp add: least_Upper_cong_r[OF _ _ seq])

  from leasta leastb
      show "a .= b" by (rule weak_least_unique)
qed (rule carr)+

lemma (in weak_partial_order) sup_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> least L x (Upper L {x})"
  by (rule least_UpperI) auto

lemma (in weak_partial_order) weak_sup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} .= x"
  unfolding sup_def
  by (rule someI2) (auto intro: weak_least_unique sup_of_singletonI)

lemma (in weak_partial_order) sup_of_singleton_closed [simp]:
  "x \<in> carrier L \<Longrightarrow> \<Squnion>{x} \<in> carrier L"
  unfolding sup_def
  by (rule someI2) (auto intro: sup_of_singletonI)

text {* Condition on @{text A}: supremum exists. *}

lemma (in weak_upper_semilattice) sup_insertI:
  "[| !!s. least L s (Upper L (insert x A)) ==> P s;
  least L a (Upper L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Squnion>(insert x A))"
proof (unfold sup_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L (insert x A)) ==> P l"
    and least_a: "least L a (Upper L A)"
  from L least_a have La: "a \<in> carrier L" by simp
  from L sup_of_two_exists least_a
  obtain s where least_s: "least L s (Upper L {a, x})" by blast
  show "P (SOME l. least L l (Upper L (insert x A)))"
  proof (rule someI2)
    show "least L s (Upper L (insert x A))"
    proof (rule least_UpperI)
      fix z
      assume "z \<in> insert x A"
      then show "z \<sqsubseteq> s"
      proof
        assume "z = x" then show ?thesis
          by (simp add: least_Upper_above [OF least_s] L La)
      next
        assume "z \<in> A"
        with L least_s least_a show ?thesis
          by (rule_tac le_trans [where y = a]) (auto dest: least_Upper_above)
      qed
    next
      fix y
      assume y: "y \<in> Upper L (insert x A)"
      show "s \<sqsubseteq> y"
      proof (rule least_le [OF least_s], rule Upper_memI)
        fix z
        assume z: "z \<in> {a, x}"
        then show "z \<sqsubseteq> y"
        proof
          have y': "y \<in> Upper L A"
            apply (rule subsetD [where A = "Upper L (insert x A)"])
             apply (rule Upper_antimono)
             apply blast
            apply (rule y)
            done
          assume "z = a"
          with y' least_a show ?thesis by (fast dest: least_le)
        next
          assume "z \<in> {x}"  (* FIXME "z = x"; declare specific elim rule for "insert x {}" (!?) *)
          with y L show ?thesis by blast
        qed
      qed (rule Upper_closed [THEN subsetD, OF y])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from least_s show "s \<in> carrier L" by simp
    qed
  qed (rule P)
qed

lemma (in weak_upper_semilattice) finite_sup_least:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> least L (\<Squnion>A) (Upper L A)"
proof (induct set: finite)
  case empty
  then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis
      by simp (simp add: least_cong [OF weak_sup_of_singleton] sup_of_singletonI)
        (* The above step is hairy; least_cong can make simp loop.
        Would want special version of simp to apply least_cong. *)
  next
    case False
    with insert have "least L (\<Squnion>A) (Upper L A)" by simp
    with _ show ?thesis
      by (rule sup_insertI) (simp_all add: insert [simplified])
  qed
qed

lemma (in weak_upper_semilattice) finite_sup_insertI:
  assumes P: "!!l. least L l (Upper L (insert x A)) ==> P l"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Squnion> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: finite_sup_least)
next
  case False with P and xA show ?thesis
    by (simp add: sup_insertI finite_sup_least)
qed

lemma (in weak_upper_semilattice) finite_sup_closed [simp]:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> \<Squnion>A \<in> carrier L"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case
    by - (rule finite_sup_insertI, simp_all)
qed

lemma (in weak_upper_semilattice) join_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in weak_upper_semilattice) join_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> y \<sqsubseteq> x \<squnion> y"
  by (rule joinI [folded join_def]) (blast dest: least_mem)

lemma (in weak_upper_semilattice) sup_of_two_least:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> least L (\<Squnion>{x, y}) (Upper L {x, y})"
proof (unfold sup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with sup_of_two_exists obtain s where "least L s (Upper L {x, y})" by fast
  with L show "least L (SOME z. least L z (Upper L {x, y})) (Upper L {x, y})"
  by (fast intro: someI2 weak_least_unique)  (* blast fails *)
qed

lemma (in weak_upper_semilattice) join_le:
  assumes sub: "x \<sqsubseteq> z"  "y \<sqsubseteq> z"
    and x: "x \<in> carrier L" and y: "y \<in> carrier L" and z: "z \<in> carrier L"
  shows "x \<squnion> y \<sqsubseteq> z"
proof (rule joinI [OF _ x y])
  fix s
  assume "least L s (Upper L {x, y})"
  with sub z show "s \<sqsubseteq> z" by (fast elim: least_le intro: Upper_memI)
qed

lemma (in weak_upper_semilattice) weak_join_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) .= \<Squnion>{x, y, z}"
proof (rule finite_sup_insertI)
  -- {* The textbook argument in Jacobson I, p 457 *}
  fix s
  assume sup: "least L s (Upper L {x, y, z})"
  show "x \<squnion> (y \<squnion> z) .= s"
  proof (rule weak_le_antisym)
    from sup L show "x \<squnion> (y \<squnion> z) \<sqsubseteq> s"
      by (fastforce intro!: join_le elim: least_Upper_above)
  next
    from sup L show "s \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    by (erule_tac least_le)
      (blast intro!: Upper_memI intro: le_trans join_left join_right join_closed)
  qed (simp_all add: L least_closed [OF sup])
qed (simp_all add: L)

text {* Commutativity holds for @{text "="}. *}

lemma join_comm:
  fixes L (structure)
  shows "x \<squnion> y = y \<squnion> x"
  by (unfold join_def) (simp add: insert_commute)

lemma (in weak_upper_semilattice) weak_join_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z .= x \<squnion> (y \<squnion> z)"
proof -
  (* FIXME: could be simplified by improved simp: uniform use of .=,
     omit [symmetric] in last step. *)
  have "(x \<squnion> y) \<squnion> z = z \<squnion> (x \<squnion> y)" by (simp only: join_comm)
  also from L have "... .= \<Squnion>{z, x, y}" by (simp add: weak_join_assoc_lemma)
  also from L have "... = \<Squnion>{x, y, z}" by (simp add: insert_commute)
  also from L have "... .= x \<squnion> (y \<squnion> z)" by (simp add: weak_join_assoc_lemma [symmetric])
  finally show ?thesis by (simp add: L)
qed


subsubsection {* Infimum *}

lemma (in weak_lower_semilattice) meetI:
  "[| !!i. greatest L i (Lower L {x, y}) ==> P i;
  x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<sqinter> y)"
proof (unfold meet_def inf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!g. greatest L g (Lower L {x, y}) ==> P g"
  with inf_of_two_exists obtain i where "greatest L i (Lower L {x, y})" by fast
  with L show "P (SOME g. greatest L g (Lower L {x, y}))"
  by (fast intro: someI2 weak_greatest_unique P)
qed

lemma (in weak_lower_semilattice) meet_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<in> carrier L"
  by (rule meetI) (rule greatest_closed)

lemma (in weak_lower_semilattice) meet_cong_l:
  assumes carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
    and xx': "x .= x'"
  shows "x \<sqinter> y .= x' \<sqinter> y"
proof (rule meetI, rule meetI)
  fix a b
  from xx' carr
      have seq: "{x, y} {.=} {x', y}" by (rule set_eq_pairI)

  assume greatesta: "greatest L a (Lower L {x, y})"
  assume "greatest L b (Lower L {x', y})"
  with carr
      have greatestb: "greatest L b (Lower L {x, y})"
      by (simp add: greatest_Lower_cong_r[OF _ _ seq])

  from greatesta greatestb
      show "a .= b" by (rule weak_greatest_unique)
qed (rule carr)+

lemma (in weak_lower_semilattice) meet_cong_r:
  assumes carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
    and yy': "y .= y'"
  shows "x \<sqinter> y .= x \<sqinter> y'"
proof (rule meetI, rule meetI)
  fix a b
  have "{x, y} = {y, x}" by fast
  also from carr yy'
      have "{y, x} {.=} {y', x}" by (intro set_eq_pairI)
  also have "{y', x} = {x, y'}" by fast
  finally
      have seq: "{x, y} {.=} {x, y'}" .

  assume greatesta: "greatest L a (Lower L {x, y})"
  assume "greatest L b (Lower L {x, y'})"
  with carr
      have greatestb: "greatest L b (Lower L {x, y})"
      by (simp add: greatest_Lower_cong_r[OF _ _ seq])

  from greatesta greatestb
      show "a .= b" by (rule weak_greatest_unique)
qed (rule carr)+

lemma (in weak_partial_order) inf_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> greatest L x (Lower L {x})"
  by (rule greatest_LowerI) auto

lemma (in weak_partial_order) weak_inf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter>{x} .= x"
  unfolding inf_def
  by (rule someI2) (auto intro: weak_greatest_unique inf_of_singletonI)

lemma (in weak_partial_order) inf_of_singleton_closed:
  "x \<in> carrier L ==> \<Sqinter>{x} \<in> carrier L"
  unfolding inf_def
  by (rule someI2) (auto intro: inf_of_singletonI)

text {* Condition on @{text A}: infimum exists. *}

lemma (in weak_lower_semilattice) inf_insertI:
  "[| !!i. greatest L i (Lower L (insert x A)) ==> P i;
  greatest L a (Lower L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>(insert x A))"
proof (unfold inf_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!g. greatest L g (Lower L (insert x A)) ==> P g"
    and greatest_a: "greatest L a (Lower L A)"
  from L greatest_a have La: "a \<in> carrier L" by simp
  from L inf_of_two_exists greatest_a
  obtain i where greatest_i: "greatest L i (Lower L {a, x})" by blast
  show "P (SOME g. greatest L g (Lower L (insert x A)))"
  proof (rule someI2)
    show "greatest L i (Lower L (insert x A))"
    proof (rule greatest_LowerI)
      fix z
      assume "z \<in> insert x A"
      then show "i \<sqsubseteq> z"
      proof
        assume "z = x" then show ?thesis
          by (simp add: greatest_Lower_below [OF greatest_i] L La)
      next
        assume "z \<in> A"
        with L greatest_i greatest_a show ?thesis
          by (rule_tac le_trans [where y = a]) (auto dest: greatest_Lower_below)
      qed
    next
      fix y
      assume y: "y \<in> Lower L (insert x A)"
      show "y \<sqsubseteq> i"
      proof (rule greatest_le [OF greatest_i], rule Lower_memI)
        fix z
        assume z: "z \<in> {a, x}"
        then show "y \<sqsubseteq> z"
        proof
          have y': "y \<in> Lower L A"
            apply (rule subsetD [where A = "Lower L (insert x A)"])
            apply (rule Lower_antimono)
             apply blast
            apply (rule y)
            done
          assume "z = a"
          with y' greatest_a show ?thesis by (fast dest: greatest_le)
        next
          assume "z \<in> {x}"
          with y L show ?thesis by blast
        qed
      qed (rule Lower_closed [THEN subsetD, OF y])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from greatest_i show "i \<in> carrier L" by simp
    qed
  qed (rule P)
qed

lemma (in weak_lower_semilattice) finite_inf_greatest:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> greatest L (\<Sqinter>A) (Lower L A)"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis
      by simp (simp add: greatest_cong [OF weak_inf_of_singleton]
        inf_of_singleton_closed inf_of_singletonI)
  next
    case False
    from insert show ?thesis
    proof (rule_tac inf_insertI)
      from False insert show "greatest L (\<Sqinter>A) (Lower L A)" by simp
    qed simp_all
  qed
qed

lemma (in weak_lower_semilattice) finite_inf_insertI:
  assumes P: "!!i. greatest L i (Lower L (insert x A)) ==> P i"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Sqinter> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: finite_inf_greatest)
next
  case False with P and xA show ?thesis
    by (simp add: inf_insertI finite_inf_greatest)
qed

lemma (in weak_lower_semilattice) finite_inf_closed [simp]:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> \<Sqinter>A \<in> carrier L"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case
    by (rule_tac finite_inf_insertI) (simp_all)
qed

lemma (in weak_lower_semilattice) meet_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> x"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in weak_lower_semilattice) meet_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> y"
  by (rule meetI [folded meet_def]) (blast dest: greatest_mem)

lemma (in weak_lower_semilattice) inf_of_two_greatest:
  "[| x \<in> carrier L; y \<in> carrier L |] ==>
  greatest L (\<Sqinter> {x, y}) (Lower L {x, y})"
proof (unfold inf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with inf_of_two_exists obtain s where "greatest L s (Lower L {x, y})" by fast
  with L
  show "greatest L (SOME z. greatest L z (Lower L {x, y})) (Lower L {x, y})"
  by (fast intro: someI2 weak_greatest_unique)  (* blast fails *)
qed

lemma (in weak_lower_semilattice) meet_le:
  assumes sub: "z \<sqsubseteq> x"  "z \<sqsubseteq> y"
    and x: "x \<in> carrier L" and y: "y \<in> carrier L" and z: "z \<in> carrier L"
  shows "z \<sqsubseteq> x \<sqinter> y"
proof (rule meetI [OF _ x y])
  fix i
  assume "greatest L i (Lower L {x, y})"
  with sub z show "z \<sqsubseteq> i" by (fast elim: greatest_le intro: Lower_memI)
qed

lemma (in weak_lower_semilattice) weak_meet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) .= \<Sqinter>{x, y, z}"
proof (rule finite_inf_insertI)
  txt {* The textbook argument in Jacobson I, p 457 *}
  fix i
  assume inf: "greatest L i (Lower L {x, y, z})"
  show "x \<sqinter> (y \<sqinter> z) .= i"
  proof (rule weak_le_antisym)
    from inf L show "i \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (fastforce intro!: meet_le elim: greatest_Lower_below)
  next
    from inf L show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> i"
    by (erule_tac greatest_le)
      (blast intro!: Lower_memI intro: le_trans meet_left meet_right meet_closed)
  qed (simp_all add: L greatest_closed [OF inf])
qed (simp_all add: L)

lemma meet_comm:
  fixes L (structure)
  shows "x \<sqinter> y = y \<sqinter> x"
  by (unfold meet_def) (simp add: insert_commute)

lemma (in weak_lower_semilattice) weak_meet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z .= x \<sqinter> (y \<sqinter> z)"
proof -
  (* FIXME: improved simp, see weak_join_assoc above *)
  have "(x \<sqinter> y) \<sqinter> z = z \<sqinter> (x \<sqinter> y)" by (simp only: meet_comm)
  also from L have "... .= \<Sqinter> {z, x, y}" by (simp add: weak_meet_assoc_lemma)
  also from L have "... = \<Sqinter> {x, y, z}" by (simp add: insert_commute)
  also from L have "... .= x \<sqinter> (y \<sqinter> z)" by (simp add: weak_meet_assoc_lemma [symmetric])
  finally show ?thesis by (simp add: L)
qed


subsection {* Total Orders *}

locale weak_total_order = weak_partial_order +
  assumes total: "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

text {* Introduction rule: the usual definition of total order *}

lemma (in weak_partial_order) weak_total_orderI:
  assumes total: "!!x y. [| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "weak_total_order L"
  by default (rule total)

text {* Total orders are lattices. *}

sublocale weak_total_order < weak: weak_lattice
proof
  fix x y
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  show "EX s. least L s (Upper L {x, y})"
  proof -
    note total L
    moreover
    {
      assume "x \<sqsubseteq> y"
      with L have "least L y (Upper L {x, y})"
        by (rule_tac least_UpperI) auto
    }
    moreover
    {
      assume "y \<sqsubseteq> x"
      with L have "least L x (Upper L {x, y})"
        by (rule_tac least_UpperI) auto
    }
    ultimately show ?thesis by blast
  qed
next
  fix x y
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  show "EX i. greatest L i (Lower L {x, y})"
  proof -
    note total L
    moreover
    {
      assume "y \<sqsubseteq> x"
      with L have "greatest L y (Lower L {x, y})"
        by (rule_tac greatest_LowerI) auto
    }
    moreover
    {
      assume "x \<sqsubseteq> y"
      with L have "greatest L x (Lower L {x, y})"
        by (rule_tac greatest_LowerI) auto
    }
    ultimately show ?thesis by blast
  qed
qed


subsection {* Complete Lattices *}

locale weak_complete_lattice = weak_lattice +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in weak_partial_order) weak_complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "weak_complete_lattice L"
  by default (auto intro: sup_exists inf_exists)

definition
  top :: "_ => 'a" ("\<top>\<index>")
  where "\<top>\<^bsub>L\<^esub> = sup L (carrier L)"

definition
  bottom :: "_ => 'a" ("\<bottom>\<index>")
  where "\<bottom>\<^bsub>L\<^esub> = inf L (carrier L)"


lemma (in weak_complete_lattice) supI:
  "[| !!l. least L l (Upper L A) ==> P l; A \<subseteq> carrier L |]
  ==> P (\<Squnion>A)"
proof (unfold sup_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L A) ==> P l"
  with sup_exists obtain s where "least L s (Upper L A)" by blast
  with L show "P (SOME l. least L l (Upper L A))"
  by (fast intro: someI2 weak_least_unique P)
qed

lemma (in weak_complete_lattice) sup_closed [simp]:
  "A \<subseteq> carrier L ==> \<Squnion>A \<in> carrier L"
  by (rule supI) simp_all

lemma (in weak_complete_lattice) top_closed [simp, intro]:
  "\<top> \<in> carrier L"
  by (unfold top_def) simp

lemma (in weak_complete_lattice) infI:
  "[| !!i. greatest L i (Lower L A) ==> P i; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>A)"
proof (unfold inf_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. greatest L l (Lower L A) ==> P l"
  with inf_exists obtain s where "greatest L s (Lower L A)" by blast
  with L show "P (SOME l. greatest L l (Lower L A))"
  by (fast intro: someI2 weak_greatest_unique P)
qed

lemma (in weak_complete_lattice) inf_closed [simp]:
  "A \<subseteq> carrier L ==> \<Sqinter>A \<in> carrier L"
  by (rule infI) simp_all

lemma (in weak_complete_lattice) bottom_closed [simp, intro]:
  "\<bottom> \<in> carrier L"
  by (unfold bottom_def) simp

text {* Jacobson: Theorem 8.1 *}

lemma Lower_empty [simp]:
  "Lower L {} = carrier L"
  by (unfold Lower_def) simp

lemma Upper_empty [simp]:
  "Upper L {} = carrier L"
  by (unfold Upper_def) simp

theorem (in weak_partial_order) weak_complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "weak_complete_lattice L"
proof (rule weak_complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_below [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B])
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)


subsection {* Orders and Lattices where @{text eq} is the Equality *}

locale partial_order = weak_partial_order +
  assumes eq_is_equal: "op .= = op ="
begin

declare weak_le_antisym [rule del]

lemma le_antisym [intro]:
  "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L |] ==> x = y"
  using weak_le_antisym unfolding eq_is_equal .

lemma lless_eq:
  "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y & x \<noteq> y"
  unfolding lless_def by (simp add: eq_is_equal)

lemma lless_asym:
  assumes "a \<in> carrier L" "b \<in> carrier L"
    and "a \<sqsubset> b" "b \<sqsubset> a"
  shows "P"
  using assms unfolding lless_eq by auto

end


text {* Least and greatest, as predicate *}

lemma (in partial_order) least_unique:
  "[| least L x A; least L y A |] ==> x = y"
  using weak_least_unique unfolding eq_is_equal .

lemma (in partial_order) greatest_unique:
  "[| greatest L x A; greatest L y A |] ==> x = y"
  using weak_greatest_unique unfolding eq_is_equal .


text {* Lattices *}

locale upper_semilattice = partial_order +
  assumes sup_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. least L s (Upper L {x, y})"

sublocale upper_semilattice < weak: weak_upper_semilattice
  by default (rule sup_of_two_exists)

locale lower_semilattice = partial_order +
  assumes inf_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. greatest L s (Lower L {x, y})"

sublocale lower_semilattice < weak: weak_lower_semilattice
  by default (rule inf_of_two_exists)

locale lattice = upper_semilattice + lower_semilattice


text {* Supremum *}

declare (in partial_order) weak_sup_of_singleton [simp del]

lemma (in partial_order) sup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} = x"
  using weak_sup_of_singleton unfolding eq_is_equal .

lemma (in upper_semilattice) join_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) = \<Squnion>{x, y, z}"
  using weak_join_assoc_lemma L unfolding eq_is_equal .

lemma (in upper_semilattice) join_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  using weak_join_assoc L unfolding eq_is_equal .


text {* Infimum *}

declare (in partial_order) weak_inf_of_singleton [simp del]

lemma (in partial_order) inf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter>{x} = x"
  using weak_inf_of_singleton unfolding eq_is_equal .

text {* Condition on @{text A}: infimum exists. *}

lemma (in lower_semilattice) meet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) = \<Sqinter>{x, y, z}"
  using weak_meet_assoc_lemma L unfolding eq_is_equal .

lemma (in lower_semilattice) meet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  using weak_meet_assoc L unfolding eq_is_equal .


text {* Total Orders *}

locale total_order = partial_order +
  assumes total_order_total: "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

sublocale total_order < weak: weak_total_order
  by default (rule total_order_total)

text {* Introduction rule: the usual definition of total order *}

lemma (in partial_order) total_orderI:
  assumes total: "!!x y. [| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "total_order L"
  by default (rule total)

text {* Total orders are lattices. *}

sublocale total_order < weak: lattice
  by default (auto intro: sup_of_two_exists inf_of_two_exists)


text {* Complete lattices *}

locale complete_lattice = lattice +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

sublocale complete_lattice < weak: weak_complete_lattice
  by default (auto intro: sup_exists inf_exists)

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in partial_order) complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
  by default (auto intro: sup_exists inf_exists)

theorem (in partial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_below [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B])
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)


subsection {* Examples *}

subsubsection {* The Powerset of a Set is a Complete Lattice *}

theorem powerset_is_complete_lattice:
  "complete_lattice (| carrier = Pow A, eq = op =, le = op \<subseteq> |)"
  (is "complete_lattice ?L")
proof (rule partial_order.complete_latticeI)
  show "partial_order ?L"
    by default auto
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "least ?L (\<Union> B) (Upper ?L B)"
    by (fastforce intro!: least_UpperI simp: Upper_def)
  then show "EX s. least ?L s (Upper ?L B)" ..
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "greatest ?L (\<Inter> B \<inter> A) (Lower ?L B)"
    txt {* @{term "\<Inter> B"} is not the infimum of @{term B}:
      @{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! *}
    by (fastforce intro!: greatest_LowerI simp: Lower_def)
  then show "EX i. greatest ?L i (Lower ?L B)" ..
qed

text {* An other example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}). *}

end
