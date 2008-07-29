(*
  Title:     HOL/Algebra/Lattice.thy
  Id:        $Id$
  Author:    Clemens Ballarin, started 7 November 2003
  Copyright: Clemens Ballarin
*)

theory GLattice imports Congruence begin

(* FIXME: unify with Lattice.thy *)


section {* Orders and Lattices *}

subsection {* Partial Orders *}

record 'a gorder = "'a eq_object" +
  le :: "['a, 'a] => bool" (infixl "\<sqsubseteq>\<index>" 50)

locale gpartial_order = equivalence L +
  assumes le_refl [intro, simp]:
      "x \<in> carrier L ==> x \<sqsubseteq> x"
    and le_anti_sym [intro]:
      "[| x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L |] ==> x .= y"
    and le_trans [trans]:
      "[| x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L |] ==> x \<sqsubseteq> z"
    and le_cong:
      "\<lbrakk> x .= y; z .= w; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L; w \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> w"

constdefs (structure L)
  glless :: "[_, 'a, 'a] => bool" (infixl "\<sqsubset>\<index>" 50)
  "x \<sqsubset> y == x \<sqsubseteq> y & x .\<noteq> y"


subsubsection {* The order relation *}

context gpartial_order begin

lemma le_cong_l [intro, trans]:
  "\<lbrakk> x .= y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD2])

lemma le_cong_r [intro, trans]:
  "\<lbrakk> x \<sqsubseteq> y; y .= z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD1])

lemma gen_refl [intro, simp]: "\<lbrakk> x .= y; x \<in> carrier L; y \<in> carrier L \<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: le_cong_l)

end

lemma gllessI:
  fixes R (structure)
  assumes "x \<sqsubseteq> y" and "~(x .= y)"
  shows "x \<sqsubset> y"
  using assms
  unfolding glless_def
  by simp

lemma gllessD1:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "x \<sqsubseteq> y"
  using assms
  unfolding glless_def
  by simp

lemma gllessD2:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "\<not> (x .= y)"
  using assms
  unfolding glless_def
  by simp

lemma gllessE:
  fixes R (structure)
  assumes p: "x \<sqsubset> y"
    and e: "\<lbrakk>x \<sqsubseteq> y; \<not> (x .= y)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using p
  by (blast dest: gllessD1 gllessD2 e)

(*
lemma (in gpartial_order) lless_cong_l [trans]:
  assumes xx': "x \<doteq> x'"
    and xy: "x' \<sqsubset> y"
    and carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubseteq> y"
using xy
unfolding lless_def
proof clarify
  note xx'
  also assume "x' \<sqsubseteq> y"
  finally show "x \<sqsubseteq> y" by (simp add: carr)
qed
*)

lemma (in gpartial_order) glless_cong_l [trans]:
  assumes xx': "x .= x'"
    and xy: "x' \<sqsubset> y"
    and carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubset> y"
  using assms
  apply (elim gllessE, intro gllessI)
  apply (iprover intro: le_cong_l)
  apply (iprover intro: trans sym)
  done

(*
lemma (in gpartial_order) lless_cong_r:
  assumes xy: "x \<sqsubset> y"
    and  yy': "y \<doteq> y'"
    and carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
  shows "x \<sqsubseteq> y'"
using xy
unfolding lless_def
proof clarify
  assume "x \<sqsubseteq> y"
  also note yy'
  finally show "x \<sqsubseteq> y'" by (simp add: carr)
qed
*)

lemma (in gpartial_order) glless_cong_r [trans]:
  assumes xy: "x \<sqsubset> y"
    and  yy': "y .= y'"
    and carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
  shows "x \<sqsubset> y'"
  using assms
  apply (elim gllessE, intro gllessI)
  apply (iprover intro: le_cong_r)
  apply (iprover intro: trans sym)
  done

(*
lemma (in gpartial_order) glless_antisym:
  assumes "a \<in> carrier L" "b \<in> carrier L"
    and "a \<sqsubset> b" "b \<sqsubset> a"
  shows "a \<doteq> b"
  using assms
  by (elim gllessE) (rule gle_anti_sym)

lemma (in gpartial_order) glless_trans [trans]:
  assumes "a .\<sqsubset> b" "b .\<sqsubset> c"
    and carr[simp]: "a \<in> carrier L" "b \<in> carrier L" "c \<in> carrier L"
  shows "a .\<sqsubset> c"
using assms
apply (elim gllessE, intro gllessI)
 apply (iprover dest: le_trans)
proof (rule ccontr, simp)
  assume ab: "a \<sqsubseteq> b" and bc: "b \<sqsubseteq> c"
    and ac: "a \<doteq> c"
    and nbc: "\<not> b \<doteq> c"
  note ac[symmetric]
  also note ab
  finally have "c \<sqsubseteq> b" by simp
  with bc have "b \<doteq> c" by (iprover intro: gle_anti_sym carr)
  with nbc
      show "False" by simp
qed
*)

subsubsection {* Upper and lower bounds of a set *}

constdefs (structure L)
  Upper :: "[_, 'a set] => 'a set"
  "Upper L A == {u. (ALL x. x \<in> A \<inter> carrier L --> x \<sqsubseteq> u)} \<inter> carrier L"

  Lower :: "[_, 'a set] => 'a set"
  "Lower L A == {l. (ALL x. x \<in> A \<inter> carrier L --> l \<sqsubseteq> x)} \<inter> carrier L"

lemma Upper_closed [intro!, simp]:
  "Upper L A \<subseteq> carrier L"
  by (unfold Upper_def) clarify

lemma Upper_memD [dest]:
  fixes L (structure)
  shows "[| u \<in> Upper L A; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u \<and> u \<in> carrier L"
  by (unfold Upper_def) blast

lemma (in gpartial_order) Upper_elemD [dest]:
  "[| u .\<in> Upper L A; u \<in> carrier L; x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> u"
  unfolding Upper_def elem_def
  by (blast dest: sym)

lemma Upper_memI:
  fixes L (structure)
  shows "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x \<in> Upper L A"
  by (unfold Upper_def) blast

lemma (in gpartial_order) Upper_elemI:
  "[| !! y. y \<in> A ==> y \<sqsubseteq> x; x \<in> carrier L |] ==> x .\<in> Upper L A"
  unfolding Upper_def by blast

lemma Upper_antimono:
  "A \<subseteq> B ==> Upper L B \<subseteq> Upper L A"
  by (unfold Upper_def) blast

lemma (in gpartial_order) Upper_is_closed [simp]:
  "A \<subseteq> carrier L ==> is_closed (Upper L A)"
  by (rule is_closedI) (blast intro: Upper_memI)+

lemma (in gpartial_order) Upper_mem_cong:
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

lemma (in gpartial_order) Upper_cong:
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

lemma (in gpartial_order) Lower_is_closed [simp]:
  "A \<subseteq> carrier L \<Longrightarrow> is_closed (Lower L A)"
  by (rule is_closedI) (blast intro: Lower_memI dest: sym)+

lemma (in gpartial_order) Lower_mem_cong:
  assumes a'carr: "a' \<in> carrier L" and Acarr: "A \<subseteq> carrier L"
    and aa': "a .= a'"
    and aelem: "a \<in> Lower L A"
  shows "a' \<in> Lower L A"
using assms Lower_closed[of L A]
by (intro Lower_memI) (blast intro: le_cong_l[OF aa'[symmetric]])

lemma (in gpartial_order) Lower_cong:
  assumes Acarr: "A \<subseteq> carrier L" and A'carr: "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "Lower L A = Lower L A'"
using Lower_memD[of y]
unfolding Lower_def
apply safe
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

constdefs (structure L)
  gleast :: "[_, 'a, 'a set] => bool"
  "gleast L l A == A \<subseteq> carrier L & l \<in> A & (ALL x : A. l \<sqsubseteq> x)"

  ggreatest :: "[_, 'a, 'a set] => bool"
  "ggreatest L g A == A \<subseteq> carrier L & g \<in> A & (ALL x : A. x \<sqsubseteq> g)"

lemma gleast_closed [intro, simp]:
  "gleast L l A ==> l \<in> carrier L"
  by (unfold gleast_def) fast

lemma gleast_mem:
  "gleast L l A ==> l \<in> A"
  by (unfold gleast_def) fast

lemma (in gpartial_order) gleast_unique:
  "[| gleast L x A; gleast L y A |] ==> x .= y"
  by (unfold gleast_def) blast

lemma gleast_le:
  fixes L (structure)
  shows "[| gleast L x A; a \<in> A |] ==> x \<sqsubseteq> a"
  by (unfold gleast_def) fast

lemma (in gpartial_order) gleast_cong:
  "[| x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A |] ==> gleast L x A = gleast L x' A"
  by (unfold gleast_def) (auto dest: sym)

text {* @{const gleast} is not congruent in the second parameter for 
  @{term [locale=gpartial_order] "A {.=} A'"} *}

lemma (in gpartial_order) gleast_Upper_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L"
  shows "gleast L x (Upper L A) = gleast L x' (Upper L A)"
  apply (rule gleast_cong) using assms by auto

lemma (in gpartial_order) gleast_Upper_cong_r:
  assumes Acarrs: "A \<subseteq> carrier L" "A' \<subseteq> carrier L" (* unneccessary with current Upper? *)
    and AA': "A {.=} A'"
  shows "gleast L x (Upper L A) = gleast L x (Upper L A')"
apply (subgoal_tac "Upper L A = Upper L A'", simp)
by (rule Upper_cong) fact+

lemma gleast_UpperI:
  fixes L (structure)
  assumes above: "!! x. x \<in> A ==> x \<sqsubseteq> s"
    and below: "!! y. y \<in> Upper L A ==> s \<sqsubseteq> y"
    and L: "A \<subseteq> carrier L"  "s \<in> carrier L"
  shows "gleast L s (Upper L A)"
proof -
  have "Upper L A \<subseteq> carrier L" by simp
  moreover from above L have "s \<in> Upper L A" by (simp add: Upper_def)
  moreover from below have "ALL x : Upper L A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: gleast_def)
qed

lemma gleast_Upper_above:
  fixes L (structure)
  shows "[| gleast L s (Upper L A); x \<in> A; A \<subseteq> carrier L |] ==> x \<sqsubseteq> s"
  by (unfold gleast_def) blast

lemma ggreatest_closed [intro, simp]:
  "ggreatest L l A ==> l \<in> carrier L"
  by (unfold ggreatest_def) fast

lemma ggreatest_mem:
  "ggreatest L l A ==> l \<in> A"
  by (unfold ggreatest_def) fast

lemma (in gpartial_order) ggreatest_unique:
  "[| ggreatest L x A; ggreatest L y A |] ==> x .= y"
  by (unfold ggreatest_def) blast

lemma ggreatest_le:
  fixes L (structure)
  shows "[| ggreatest L x A; a \<in> A |] ==> a \<sqsubseteq> x"
  by (unfold ggreatest_def) fast

lemma (in gpartial_order) ggreatest_cong:
  "[| x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A |] ==>
  ggreatest L x A = ggreatest L x' A"
  by (unfold ggreatest_def) (auto dest: sym)

text {* @{const ggreatest} is not congruent in the second parameter for 
  @{term [locale=gpartial_order] "A {.=} A'"} *}

lemma (in gpartial_order) ggreatest_Lower_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L" (* unneccessary with current Lower *)
  shows "ggreatest L x (Lower L A) = ggreatest L x' (Lower L A)"
  apply (rule ggreatest_cong) using assms by auto

lemma (in gpartial_order) ggreatest_Lower_cong_r:
  assumes Acarrs: "A \<subseteq> carrier L" "A' \<subseteq> carrier L"
    and AA': "A {.=} A'"
  shows "ggreatest L x (Lower L A) = ggreatest L x (Lower L A')"
apply (subgoal_tac "Lower L A = Lower L A'", simp)
by (rule Lower_cong) fact+

lemma ggreatest_LowerI:
  fixes L (structure)
  assumes below: "!! x. x \<in> A ==> i \<sqsubseteq> x"
    and above: "!! y. y \<in> Lower L A ==> y \<sqsubseteq> i"
    and L: "A \<subseteq> carrier L"  "i \<in> carrier L"
  shows "ggreatest L i (Lower L A)"
proof -
  have "Lower L A \<subseteq> carrier L" by simp
  moreover from below L have "i \<in> Lower L A" by (simp add: Lower_def)
  moreover from above have "ALL x : Lower L A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: ggreatest_def)
qed

lemma ggreatest_Lower_below:
  fixes L (structure)
  shows "[| ggreatest L i (Lower L A); x \<in> A; A \<subseteq> carrier L |] ==> i \<sqsubseteq> x"
  by (unfold ggreatest_def) blast

text {* Supremum and infimum *}

constdefs (structure L)
  gsup :: "[_, 'a set] => 'a" ("\<Squnion>\<index>_" [90] 90)
  "\<Squnion>A == SOME x. gleast L x (Upper L A)"

  ginf :: "[_, 'a set] => 'a" ("\<Sqinter>\<index>_" [90] 90)
  "\<Sqinter>A == SOME x. ggreatest L x (Lower L A)"

  gjoin :: "[_, 'a, 'a] => 'a" (infixl "\<squnion>\<index>" 65)
  "x \<squnion> y == \<Squnion> {x, y}"

  gmeet :: "[_, 'a, 'a] => 'a" (infixl "\<sqinter>\<index>" 70)
  "x \<sqinter> y == \<Sqinter> {x, y}"


subsection {* Lattices *}

locale gupper_semilattice = gpartial_order +
  assumes gsup_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. gleast L s (Upper L {x, y})"

locale glower_semilattice = gpartial_order +
  assumes ginf_of_two_exists:
    "[| x \<in> carrier L; y \<in> carrier L |] ==> EX s. ggreatest L s (Lower L {x, y})"

locale glattice = gupper_semilattice + glower_semilattice


subsubsection {* Supremum *}

lemma (in gupper_semilattice) gjoinI:
  "[| !!l. gleast L l (Upper L {x, y}) ==> P l; x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<squnion> y)"
proof (unfold gjoin_def gsup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!l. gleast L l (Upper L {x, y}) ==> P l"
  with gsup_of_two_exists obtain s where "gleast L s (Upper L {x, y})" by fast
  with L show "P (SOME l. gleast L l (Upper L {x, y}))"
    by (fast intro: someI2 P)
qed

lemma (in gupper_semilattice) gjoin_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<squnion> y \<in> carrier L"
  by (rule gjoinI) (rule gleast_closed)

lemma (in gupper_semilattice) gjoin_cong_l:
  assumes carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
    and xx': "x .= x'"
  shows "x \<squnion> y .= x' \<squnion> y"
proof (rule gjoinI, rule gjoinI)
  fix a b
  from xx' carr
      have seq: "{x, y} {.=} {x', y}" by (rule set_eq_pairI)

  assume gleasta: "gleast L a (Upper L {x, y})"
  assume "gleast L b (Upper L {x', y})"
  with carr
      have gleastb: "gleast L b (Upper L {x, y})"
      by (simp add: gleast_Upper_cong_r[OF _ _ seq])

  from gleasta gleastb
      show "a .= b" by (rule gleast_unique)
qed (rule carr)+

lemma (in gupper_semilattice) gjoin_cong_r:
  assumes carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
    and yy': "y .= y'"
  shows "x \<squnion> y .= x \<squnion> y'"
proof (rule gjoinI, rule gjoinI)
  fix a b
  have "{x, y} = {y, x}" by fast
  also from carr yy'
      have "{y, x} {.=} {y', x}" by (intro set_eq_pairI)
  also have "{y', x} = {x, y'}" by fast
  finally
      have seq: "{x, y} {.=} {x, y'}" .

  assume gleasta: "gleast L a (Upper L {x, y})"
  assume "gleast L b (Upper L {x, y'})"
  with carr
      have gleastb: "gleast L b (Upper L {x, y})"
      by (simp add: gleast_Upper_cong_r[OF _ _ seq])

  from gleasta gleastb
      show "a .= b" by (rule gleast_unique)
qed (rule carr)+

lemma (in gpartial_order) gsup_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> gleast L x (Upper L {x})"
  by (rule gleast_UpperI) auto

lemma (in gpartial_order) gsup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} .= x"
  unfolding gsup_def
  by (rule someI2) (auto intro: gleast_unique gsup_of_singletonI)

lemma (in gpartial_order) gsup_of_singleton_closed [simp]:
  "x \<in> carrier L \<Longrightarrow> \<Squnion>{x} \<in> carrier L"
  unfolding gsup_def
  by (rule someI2) (auto intro: gsup_of_singletonI)

text {* Condition on @{text A}: supremum exists. *}

lemma (in gupper_semilattice) gsup_insertI:
  "[| !!s. gleast L s (Upper L (insert x A)) ==> P s;
  gleast L a (Upper L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Squnion>(insert x A))"
proof (unfold gsup_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!l. gleast L l (Upper L (insert x A)) ==> P l"
    and gleast_a: "gleast L a (Upper L A)"
  from L gleast_a have La: "a \<in> carrier L" by simp
  from L gsup_of_two_exists gleast_a
  obtain s where gleast_s: "gleast L s (Upper L {a, x})" by blast
  show "P (SOME l. gleast L l (Upper L (insert x A)))"
  proof (rule someI2)
    show "gleast L s (Upper L (insert x A))"
    proof (rule gleast_UpperI)
      fix z
      assume "z \<in> insert x A"
      then show "z \<sqsubseteq> s"
      proof
        assume "z = x" then show ?thesis
          by (simp add: gleast_Upper_above [OF gleast_s] L La)
      next
        assume "z \<in> A"
        with L gleast_s gleast_a show ?thesis
          by (rule_tac le_trans [where y = a]) (auto dest: gleast_Upper_above)
      qed
    next
      fix y
      assume y: "y \<in> Upper L (insert x A)"
      show "s \<sqsubseteq> y"
      proof (rule gleast_le [OF gleast_s], rule Upper_memI)
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
          with y' gleast_a show ?thesis by (fast dest: gleast_le)
	next
	  assume "z \<in> {x}"  (* FIXME "z = x"; declare specific elim rule for "insert x {}" (!?) *)
          with y L show ?thesis by blast
	qed
      qed (rule Upper_closed [THEN subsetD, OF y])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from gleast_s show "s \<in> carrier L" by simp
    qed
  qed (rule P)
qed

lemma (in gupper_semilattice) finite_gsup_gleast:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> gleast L (\<Squnion>A) (Upper L A)"
proof (induct set: finite)
  case empty
  then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis
      by simp (simp add: gleast_cong [OF gsup_of_singleton]
	gsup_of_singleton_closed gsup_of_singletonI)
	(* The above step is hairy; gleast_cong can make simp loop.
	Would want special version of simp to apply gleast_cong. *)
  next
    case False
    with insert have "gleast L (\<Squnion>A) (Upper L A)" by simp
    with _ show ?thesis
      by (rule gsup_insertI) (simp_all add: insert [simplified])
  qed
qed

lemma (in gupper_semilattice) finite_gsup_insertI:
  assumes P: "!!l. gleast L l (Upper L (insert x A)) ==> P l"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Squnion> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: finite_gsup_gleast)
next
  case False with P and xA show ?thesis
    by (simp add: gsup_insertI finite_gsup_gleast)
qed

lemma (in gupper_semilattice) finite_gsup_closed [simp]:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> \<Squnion>A \<in> carrier L"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case
    by - (rule finite_gsup_insertI, simp_all)
qed

lemma (in gupper_semilattice) gjoin_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> x \<squnion> y"
  by (rule gjoinI [folded gjoin_def]) (blast dest: gleast_mem)

lemma (in gupper_semilattice) gjoin_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> y \<sqsubseteq> x \<squnion> y"
  by (rule gjoinI [folded gjoin_def]) (blast dest: gleast_mem)

lemma (in gupper_semilattice) gsup_of_two_gleast:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> gleast L (\<Squnion>{x, y}) (Upper L {x, y})"
proof (unfold gsup_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with gsup_of_two_exists obtain s where "gleast L s (Upper L {x, y})" by fast
  with L show "gleast L (SOME z. gleast L z (Upper L {x, y})) (Upper L {x, y})"
  by (fast intro: someI2 gleast_unique)  (* blast fails *)
qed

lemma (in gupper_semilattice) gjoin_le:
  assumes sub: "x \<sqsubseteq> z"  "y \<sqsubseteq> z"
    and x: "x \<in> carrier L" and y: "y \<in> carrier L" and z: "z \<in> carrier L"
  shows "x \<squnion> y \<sqsubseteq> z"
proof (rule gjoinI [OF _ x y])
  fix s
  assume "gleast L s (Upper L {x, y})"
  with sub z show "s \<sqsubseteq> z" by (fast elim: gleast_le intro: Upper_memI)
qed

lemma (in gupper_semilattice) gjoin_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) .= \<Squnion>{x, y, z}"
proof (rule finite_gsup_insertI)
  -- {* The textbook argument in Jacobson I, p 457 *}
  fix s
  assume gsup: "gleast L s (Upper L {x, y, z})"
  show "x \<squnion> (y \<squnion> z) .= s"
  proof (rule le_anti_sym)
    from gsup L show "x \<squnion> (y \<squnion> z) \<sqsubseteq> s"
      by (fastsimp intro!: gjoin_le elim: gleast_Upper_above)
  next
    from gsup L show "s \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    by (erule_tac gleast_le)
      (blast intro!: Upper_memI intro: le_trans gjoin_left gjoin_right gjoin_closed)
  qed (simp_all add: L gleast_closed [OF gsup])
qed (simp_all add: L)

text {* Commutativity holds for @{text "="}. *}

lemma gjoin_comm:
  fixes L (structure)
  shows "x \<squnion> y = y \<squnion> x"
  by (unfold gjoin_def) (simp add: insert_commute)

lemma (in gupper_semilattice) gjoin_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z .= x \<squnion> (y \<squnion> z)"
proof -
  (* FIXME: could be simplified by improved simp: uniform use of .=,
     omit [symmetric] in last step. *)
  have "(x \<squnion> y) \<squnion> z = z \<squnion> (x \<squnion> y)" by (simp only: gjoin_comm)
  also from L have "... .= \<Squnion>{z, x, y}" by (simp add: gjoin_assoc_lemma)
  also from L have "... = \<Squnion>{x, y, z}" by (simp add: insert_commute)
  also from L have "... .= x \<squnion> (y \<squnion> z)" by (simp add: gjoin_assoc_lemma [symmetric])
  finally show ?thesis by (simp add: L)
qed


subsubsection {* Infimum *}

lemma (in glower_semilattice) gmeetI:
  "[| !!i. ggreatest L i (Lower L {x, y}) ==> P i;
  x \<in> carrier L; y \<in> carrier L |]
  ==> P (x \<sqinter> y)"
proof (unfold gmeet_def ginf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
    and P: "!!g. ggreatest L g (Lower L {x, y}) ==> P g"
  with ginf_of_two_exists obtain i where "ggreatest L i (Lower L {x, y})" by fast
  with L show "P (SOME g. ggreatest L g (Lower L {x, y}))"
  by (fast intro: someI2 ggreatest_unique P)
qed

lemma (in glower_semilattice) gmeet_closed [simp]:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<in> carrier L"
  by (rule gmeetI) (rule ggreatest_closed)

lemma (in glower_semilattice) gmeet_cong_l:
  assumes carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
    and xx': "x .= x'"
  shows "x \<sqinter> y .= x' \<sqinter> y"
proof (rule gmeetI, rule gmeetI)
  fix a b
  from xx' carr
      have seq: "{x, y} {.=} {x', y}" by (rule set_eq_pairI)

  assume ggreatesta: "ggreatest L a (Lower L {x, y})"
  assume "ggreatest L b (Lower L {x', y})"
  with carr
      have ggreatestb: "ggreatest L b (Lower L {x, y})"
      by (simp add: ggreatest_Lower_cong_r[OF _ _ seq])

  from ggreatesta ggreatestb
      show "a .= b" by (rule ggreatest_unique)
qed (rule carr)+

lemma (in glower_semilattice) gmeet_cong_r:
  assumes carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
    and yy': "y .= y'"
  shows "x \<sqinter> y .= x \<sqinter> y'"
proof (rule gmeetI, rule gmeetI)
  fix a b
  have "{x, y} = {y, x}" by fast
  also from carr yy'
      have "{y, x} {.=} {y', x}" by (intro set_eq_pairI)
  also have "{y', x} = {x, y'}" by fast
  finally
      have seq: "{x, y} {.=} {x, y'}" .

  assume ggreatesta: "ggreatest L a (Lower L {x, y})"
  assume "ggreatest L b (Lower L {x, y'})"
  with carr
      have ggreatestb: "ggreatest L b (Lower L {x, y})"
      by (simp add: ggreatest_Lower_cong_r[OF _ _ seq])

  from ggreatesta ggreatestb
      show "a .= b" by (rule ggreatest_unique)
qed (rule carr)+

lemma (in gpartial_order) ginf_of_singletonI:      (* only reflexivity needed ? *)
  "x \<in> carrier L ==> ggreatest L x (Lower L {x})"
  by (rule ggreatest_LowerI) auto

lemma (in gpartial_order) ginf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter>{x} .= x"
  unfolding ginf_def
  by (rule someI2) (auto intro: ggreatest_unique ginf_of_singletonI)

lemma (in gpartial_order) ginf_of_singleton_closed:
  "x \<in> carrier L ==> \<Sqinter>{x} \<in> carrier L"
  unfolding ginf_def
  by (rule someI2) (auto intro: ginf_of_singletonI)

text {* Condition on @{text A}: infimum exists. *}

lemma (in glower_semilattice) ginf_insertI:
  "[| !!i. ggreatest L i (Lower L (insert x A)) ==> P i;
  ggreatest L a (Lower L A); x \<in> carrier L; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>(insert x A))"
proof (unfold ginf_def)
  assume L: "x \<in> carrier L"  "A \<subseteq> carrier L"
    and P: "!!g. ggreatest L g (Lower L (insert x A)) ==> P g"
    and ggreatest_a: "ggreatest L a (Lower L A)"
  from L ggreatest_a have La: "a \<in> carrier L" by simp
  from L ginf_of_two_exists ggreatest_a
  obtain i where ggreatest_i: "ggreatest L i (Lower L {a, x})" by blast
  show "P (SOME g. ggreatest L g (Lower L (insert x A)))"
  proof (rule someI2)
    show "ggreatest L i (Lower L (insert x A))"
    proof (rule ggreatest_LowerI)
      fix z
      assume "z \<in> insert x A"
      then show "i \<sqsubseteq> z"
      proof
        assume "z = x" then show ?thesis
          by (simp add: ggreatest_Lower_below [OF ggreatest_i] L La)
      next
        assume "z \<in> A"
        with L ggreatest_i ggreatest_a show ?thesis
          by (rule_tac le_trans [where y = a]) (auto dest: ggreatest_Lower_below)
      qed
    next
      fix y
      assume y: "y \<in> Lower L (insert x A)"
      show "y \<sqsubseteq> i"
      proof (rule ggreatest_le [OF ggreatest_i], rule Lower_memI)
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
          with y' ggreatest_a show ?thesis by (fast dest: ggreatest_le)
	next
          assume "z \<in> {x}"
          with y L show ?thesis by blast
	qed
      qed (rule Lower_closed [THEN subsetD, OF y])
    next
      from L show "insert x A \<subseteq> carrier L" by simp
      from ggreatest_i show "i \<in> carrier L" by simp
    qed
  qed (rule P)
qed

lemma (in glower_semilattice) finite_ginf_ggreatest:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> ggreatest L (\<Sqinter>A) (Lower L A)"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x A)
  show ?case
  proof (cases "A = {}")
    case True
    with insert show ?thesis
      by simp (simp add: ggreatest_cong [OF ginf_of_singleton]
	ginf_of_singleton_closed ginf_of_singletonI)
  next
    case False
    from insert show ?thesis
    proof (rule_tac ginf_insertI)
      from False insert show "ggreatest L (\<Sqinter>A) (Lower L A)" by simp
    qed simp_all
  qed
qed

lemma (in glower_semilattice) finite_ginf_insertI:
  assumes P: "!!i. ggreatest L i (Lower L (insert x A)) ==> P i"
    and xA: "finite A"  "x \<in> carrier L"  "A \<subseteq> carrier L"
  shows "P (\<Sqinter> (insert x A))"
proof (cases "A = {}")
  case True with P and xA show ?thesis
    by (simp add: finite_ginf_ggreatest)
next
  case False with P and xA show ?thesis
    by (simp add: ginf_insertI finite_ginf_ggreatest)
qed

lemma (in glower_semilattice) finite_ginf_closed [simp]:
  "[| finite A; A \<subseteq> carrier L; A ~= {} |] ==> \<Sqinter>A \<in> carrier L"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case
    by (rule_tac finite_ginf_insertI) (simp_all)
qed

lemma (in glower_semilattice) gmeet_left:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> x"
  by (rule gmeetI [folded gmeet_def]) (blast dest: ggreatest_mem)

lemma (in glower_semilattice) gmeet_right:
  "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqinter> y \<sqsubseteq> y"
  by (rule gmeetI [folded gmeet_def]) (blast dest: ggreatest_mem)

lemma (in glower_semilattice) ginf_of_two_ggreatest:
  "[| x \<in> carrier L; y \<in> carrier L |] ==>
  ggreatest L (\<Sqinter> {x, y}) (Lower L {x, y})"
proof (unfold ginf_def)
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  with ginf_of_two_exists obtain s where "ggreatest L s (Lower L {x, y})" by fast
  with L
  show "ggreatest L (SOME z. ggreatest L z (Lower L {x, y})) (Lower L {x, y})"
  by (fast intro: someI2 ggreatest_unique)  (* blast fails *)
qed

lemma (in glower_semilattice) gmeet_le:
  assumes sub: "z \<sqsubseteq> x"  "z \<sqsubseteq> y"
    and x: "x \<in> carrier L" and y: "y \<in> carrier L" and z: "z \<in> carrier L"
  shows "z \<sqsubseteq> x \<sqinter> y"
proof (rule gmeetI [OF _ x y])
  fix i
  assume "ggreatest L i (Lower L {x, y})"
  with sub z show "z \<sqsubseteq> i" by (fast elim: ggreatest_le intro: Lower_memI)
qed

lemma (in glower_semilattice) gmeet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) .= \<Sqinter>{x, y, z}"
proof (rule finite_ginf_insertI)
  txt {* The textbook argument in Jacobson I, p 457 *}
  fix i
  assume ginf: "ggreatest L i (Lower L {x, y, z})"
  show "x \<sqinter> (y \<sqinter> z) .= i"
  proof (rule le_anti_sym)
    from ginf L show "i \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
      by (fastsimp intro!: gmeet_le elim: ggreatest_Lower_below)
  next
    from ginf L show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> i"
    by (erule_tac ggreatest_le)
      (blast intro!: Lower_memI intro: le_trans gmeet_left gmeet_right gmeet_closed)
  qed (simp_all add: L ggreatest_closed [OF ginf])
qed (simp_all add: L)

lemma gmeet_comm:
  fixes L (structure)
  shows "x \<sqinter> y = y \<sqinter> x"
  by (unfold gmeet_def) (simp add: insert_commute)

lemma (in glower_semilattice) gmeet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z .= x \<sqinter> (y \<sqinter> z)"
proof -
  (* FIXME: improved simp, see gjoin_assoc above *)
  have "(x \<sqinter> y) \<sqinter> z = z \<sqinter> (x \<sqinter> y)" by (simp only: gmeet_comm)
  also from L have "... .= \<Sqinter> {z, x, y}" by (simp add: gmeet_assoc_lemma)
  also from L have "... = \<Sqinter> {x, y, z}" by (simp add: insert_commute)
  also from L have "... .= x \<sqinter> (y \<sqinter> z)" by (simp add: gmeet_assoc_lemma [symmetric])
  finally show ?thesis by (simp add: L)
qed


subsection {* Total Orders *}

locale gtotal_order = gpartial_order +
  assumes total: "[| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"

text {* Introduction rule: the usual definition of total order *}

lemma (in gpartial_order) gtotal_orderI:
  assumes total: "!!x y. [| x \<in> carrier L; y \<in> carrier L |] ==> x \<sqsubseteq> y | y \<sqsubseteq> x"
  shows "gtotal_order L"
  by unfold_locales (rule total)

text {* Total orders are lattices. *}

interpretation gtotal_order < glattice
proof unfold_locales
  fix x y
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  show "EX s. gleast L s (Upper L {x, y})"
  proof -
    note total L
    moreover
    {
      assume "x \<sqsubseteq> y"
      with L have "gleast L y (Upper L {x, y})"
        by (rule_tac gleast_UpperI) auto
    }
    moreover
    {
      assume "y \<sqsubseteq> x"
      with L have "gleast L x (Upper L {x, y})"
        by (rule_tac gleast_UpperI) auto
    }
    ultimately show ?thesis by blast
  qed
next
  fix x y
  assume L: "x \<in> carrier L"  "y \<in> carrier L"
  show "EX i. ggreatest L i (Lower L {x, y})"
  proof -
    note total L
    moreover
    {
      assume "y \<sqsubseteq> x"
      with L have "ggreatest L y (Lower L {x, y})"
        by (rule_tac ggreatest_LowerI) auto
    }
    moreover
    {
      assume "x \<sqsubseteq> y"
      with L have "ggreatest L x (Lower L {x, y})"
        by (rule_tac ggreatest_LowerI) auto
    }
    ultimately show ?thesis by blast
  qed
qed


subsection {* Complete lattices *}

locale complete_lattice = glattice +
  assumes gsup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. gleast L s (Upper L A)"
    and ginf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. ggreatest L i (Lower L A)"

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in gpartial_order) complete_latticeI:
  assumes gsup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. gleast L s (Upper L A)"
    and ginf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. ggreatest L i (Lower L A)"
  shows "complete_lattice L"
  by unfold_locales (auto intro: gsup_exists ginf_exists)

constdefs (structure L)
  top :: "_ => 'a" ("\<top>\<index>")
  "\<top> == gsup L (carrier L)"

  bottom :: "_ => 'a" ("\<bottom>\<index>")
  "\<bottom> == ginf L (carrier L)"


lemma (in complete_lattice) gsupI:
  "[| !!l. gleast L l (Upper L A) ==> P l; A \<subseteq> carrier L |]
  ==> P (\<Squnion>A)"
proof (unfold gsup_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. gleast L l (Upper L A) ==> P l"
  with gsup_exists obtain s where "gleast L s (Upper L A)" by blast
  with L show "P (SOME l. gleast L l (Upper L A))"
  by (fast intro: someI2 gleast_unique P)
qed

lemma (in complete_lattice) gsup_closed [simp]:
  "A \<subseteq> carrier L ==> \<Squnion>A \<in> carrier L"
  by (rule gsupI) simp_all

lemma (in complete_lattice) top_closed [simp, intro]:
  "\<top> \<in> carrier L"
  by (unfold top_def) simp

lemma (in complete_lattice) ginfI:
  "[| !!i. ggreatest L i (Lower L A) ==> P i; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>A)"
proof (unfold ginf_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. ggreatest L l (Lower L A) ==> P l"
  with ginf_exists obtain s where "ggreatest L s (Lower L A)" by blast
  with L show "P (SOME l. ggreatest L l (Lower L A))"
  by (fast intro: someI2 ggreatest_unique P)
qed

lemma (in complete_lattice) ginf_closed [simp]:
  "A \<subseteq> carrier L ==> \<Sqinter>A \<in> carrier L"
  by (rule ginfI) simp_all

lemma (in complete_lattice) bottom_closed [simp, intro]:
  "\<bottom> \<in> carrier L"
  by (unfold bottom_def) simp

text {* Jacobson: Theorem 8.1 *}

lemma Lower_empty [simp]:
  "Lower L {} = carrier L"
  by (unfold Lower_def) simp

lemma Upper_empty [simp]:
  "Upper L {} = carrier L"
  by (unfold Upper_def) simp

theorem (in gpartial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. ggreatest L g (carrier L)"
    and ginf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. ggreatest L i (Lower L A)"
  shows "complete_lattice L"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "ggreatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: ggreatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from ginf_exists [OF B_L B_non_empty]
  obtain b where b_ginf_B: "ggreatest L b (Lower L ?B)" ..
  have "gleast L b (Upper L A)"
apply (rule gleast_UpperI)
   apply (rule ggreatest_le [where A = "Lower L ?B"])
    apply (rule b_ginf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule ggreatest_Lower_below [OF b_ginf_B])
  apply simp
 apply (rule L)
apply (rule ggreatest_closed [OF b_ginf_B])
done
  then show "EX s. gleast L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. ggreatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule ginf_exists)
  qed
qed

(* TODO: prove dual version *)


subsection {* Examples *}

(* Not so useful for the generalised version.

subsubsection {* Powerset of a Set is a Complete Lattice *}

theorem powerset_is_complete_lattice:
  "complete_lattice (| carrier = Pow A, le = op \<subseteq> |)"
  (is "complete_lattice ?L")
proof (rule gpartial_order.complete_latticeI)
  show "gpartial_order ?L"
    by (rule gpartial_order.intro) auto
next
  fix B
  assume B: "B \<subseteq> carrier ?L"
  show "EX s. gleast ?L s (Upper ?L B)"
  proof
    from B show "gleast ?L (\<Union> B) (Upper ?L B)"
      by (fastsimp intro!: gleast_UpperI simp: Upper_def)
  qed
next
  fix B
  assume B: "B \<subseteq> carrier ?L"
  show "EX i. ggreatest ?L i (Lower ?L B)"
  proof
    from B show "ggreatest ?L (\<Inter> B \<inter> A) (Lower ?L B)"
      txt {* @{term "\<Inter> B"} is not the infimum of @{term B}:
	@{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! *}
      by (fastsimp intro!: ggreatest_LowerI simp: Lower_def)
  qed
qed

text {* An other example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}). *}

*)

end
