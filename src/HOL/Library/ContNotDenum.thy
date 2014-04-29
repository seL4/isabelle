(*  Title:      HOL/Library/ContNonDenum.thy
    Author:     Benjamin Porter, Monash University, NICTA, 2005
*)

header {* Non-denumerability of the Continuum. *}

theory ContNotDenum
imports Complex_Main
begin

subsection {* Abstract *}

text {* The following document presents a proof that the Continuum is
uncountable. It is formalised in the Isabelle/Isar theorem proving
system.

{\em Theorem:} The Continuum @{text "\<real>"} is not denumerable. In other
words, there does not exist a function @{text "f: \<nat> \<Rightarrow> \<real>"} such that f is
surjective.

{\em Outline:} An elegant informal proof of this result uses Cantor's
Diagonalisation argument. The proof presented here is not this
one. First we formalise some properties of closed intervals, then we
prove the Nested Interval Property. This property relies on the
completeness of the Real numbers and is the foundation for our
argument. Informally it states that an intersection of countable
closed intervals (where each successive interval is a subset of the
last) is non-empty. We then assume a surjective function @{text
"f: \<nat> \<Rightarrow> \<real>"} exists and find a real x such that x is not in the range of f
by generating a sequence of closed intervals then using the NIP. *}


subsection {* Closed Intervals *}

subsection {* Nested Interval Property *}

theorem NIP:
  fixes f :: "nat \<Rightarrow> real set"
  assumes subset: "\<forall>n. f (Suc n) \<subseteq> f n"
    and closed: "\<forall>n. \<exists>a b. f n = {a..b} \<and> a \<le> b"
  shows "(\<Inter>n. f n) \<noteq> {}"
proof -
  let ?I = "\<lambda>n. {Inf (f n) .. Sup (f n)}"
  {
    fix n
    from closed[rule_format, of n] obtain a b where "f n = {a .. b}" "a \<le> b"
      by auto
    then have "f n = {Inf (f n) .. Sup (f n)}" and "Inf (f n) \<le> Sup (f n)"
      by auto
  }
  note f_eq = this
  {
    fix n m :: nat
    assume "n \<le> m"
    then have "f m \<subseteq> f n"
      by (induct rule: dec_induct) (metis order_refl, metis order_trans subset)
  }
  note subset' = this

  have "compact (f 0)"
    by (subst f_eq) (rule compact_Icc)
  then have "f 0 \<inter> (\<Inter>i. f i) \<noteq> {}"
  proof (rule compact_imp_fip_image)
    fix I :: "nat set"
    assume I: "finite I"
    have "{} \<subset> f (Max (insert 0 I))"
      using f_eq[of "Max (insert 0 I)"] by auto
    also have "\<dots> \<subseteq> (\<Inter>i\<in>insert 0 I. f i)"
    proof (rule INF_greatest)
      fix i
      assume "i \<in> insert 0 I"
      with I show "f (Max (insert 0 I)) \<subseteq> f i"
        by (intro subset') auto
    qed
    finally show "f 0 \<inter> (\<Inter>i\<in>I. f i) \<noteq> {}"
      by auto
  qed (subst f_eq, auto)
  then show "(\<Inter>n. f n) \<noteq> {}"
    by auto
qed


subsection {* Generating the intervals *}

subsubsection {* Existence of non-singleton closed intervals *}

text {* This lemma asserts that given any non-singleton closed
interval (a,b) and any element c, there exists a closed interval that
is a subset of (a,b) and that does not contain c and is a
non-singleton itself. *}

lemma closed_subset_ex:
  fixes c :: real
  assumes "a < b"
  shows "\<exists>ka kb. ka < kb \<and> {ka..kb} \<subseteq> {a..b} \<and> c \<notin> {ka..kb}"
proof (cases "c < b")
  case True
  show ?thesis
  proof (cases "c < a")
    case True
    with `a < b` `c < b` have "c \<notin> {a..b}"
      by auto
    with `a < b` show ?thesis
      by auto
  next
    case False
    then have "a \<le> c" by simp
    def ka \<equiv> "(c + b)/2"
    from ka_def `c < b` have "ka < b"
      by auto
    moreover from ka_def `c < b` have "ka > c"
      by simp
    ultimately have "c \<notin> {ka..b}"
      by auto
    moreover from `a \<le> c` `ka > c` have "ka \<ge> a"
      by simp
    then have "{ka..b} \<subseteq> {a..b}"
      by auto
    ultimately have "ka < b  \<and> {ka..b} \<subseteq> {a..b} \<and> c \<notin> {ka..b}"
      using `ka < b` by auto
    then show ?thesis
      by auto
  qed
next
  case False
  then have "c \<ge> b" by simp
  def kb \<equiv> "(a + b)/2"
  with `a < b` have "kb < b" by auto
  with kb_def `c \<ge> b` have "a < kb" "kb < c"
    by auto
  from `kb < c` have c: "c \<notin> {a..kb}"
    by auto
  with `kb < b` have "{a..kb} \<subseteq> {a..b}"
    by auto
  with `a < kb` c have "a < kb \<and> {a..kb} \<subseteq> {a..b} \<and> c \<notin> {a..kb}"
    by simp
  then show ?thesis
    by auto
qed


subsection {* newInt: Interval generation *}

text {* Given a function f:@{text "\<nat>\<Rightarrow>\<real>"}, newInt (Suc n) f returns a
closed interval such that @{text "newInt (Suc n) f \<subseteq> newInt n f"} and
does not contain @{text "f (Suc n)"}. With the base case defined such
that @{text "(f 0)\<notin>newInt 0 f"}. *}


subsubsection {* Definition *}

primrec newInt :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (real set)"
where
  "newInt 0 f = {f 0 + 1..f 0 + 2}"
| "newInt (Suc n) f =
    (SOME e.
      (\<exists>e1 e2.
         e1 < e2 \<and>
         e = {e1..e2} \<and>
         e \<subseteq> newInt n f \<and>
         f (Suc n) \<notin> e))"


subsubsection {* Properties *}

text {* We now show that every application of newInt returns an
appropriate interval. *}

lemma newInt_ex:
  "\<exists>a b. a < b \<and>
    newInt (Suc n) f = {a..b} \<and>
    newInt (Suc n) f \<subseteq> newInt n f \<and>
    f (Suc n) \<notin> newInt (Suc n) f"
proof (induct n)
  case 0
  let ?e = "SOME e. \<exists>e1 e2.
    e1 < e2 \<and>
    e = {e1..e2} \<and>
    e \<subseteq> {f 0 + 1..f 0 + 2} \<and>
    f (Suc 0) \<notin> e"

  have "newInt (Suc 0) f = ?e" by auto
  moreover
  have "f 0 + 1 < f 0 + 2" by simp
  with closed_subset_ex
  have "\<exists>ka kb. ka < kb \<and> {ka..kb} \<subseteq> {f 0 + 1..f 0 + 2} \<and> f (Suc 0) \<notin> {ka..kb}" .
  then have "\<exists>e. \<exists>ka kb. ka < kb \<and> e = {ka..kb} \<and> e \<subseteq> {f 0 + 1..f 0 + 2} \<and> f (Suc 0) \<notin> e"
    by simp
  then have "\<exists>ka kb. ka < kb \<and> ?e = {ka..kb} \<and> ?e \<subseteq> {f 0 + 1..f 0 + 2} \<and> f (Suc 0) \<notin> ?e"
    by (rule someI_ex)
  ultimately have "\<exists>e1 e2. e1 < e2 \<and>
      newInt (Suc 0) f = {e1..e2} \<and>
      newInt (Suc 0) f \<subseteq> {f 0 + 1..f 0 + 2} \<and>
      f (Suc 0) \<notin> newInt (Suc 0) f"
    by simp
  then show "\<exists>a b. a < b \<and> newInt (Suc 0) f = {a..b} \<and>
      newInt (Suc 0) f \<subseteq> newInt 0 f \<and> f (Suc 0) \<notin> newInt (Suc 0) f"
    by simp
next
  case (Suc n)
  then have "\<exists>a b.
      a < b \<and>
      newInt (Suc n) f = {a..b} \<and>
      newInt (Suc n) f \<subseteq> newInt n f \<and>
      f (Suc n) \<notin> newInt (Suc n) f"
    by simp
  then obtain a and b where ab: "a < b \<and>
      newInt (Suc n) f = {a..b} \<and>
      newInt (Suc n) f \<subseteq> newInt n f \<and>
      f (Suc n) \<notin> newInt (Suc n) f"
    by auto
  then have cab: "{a..b} = newInt (Suc n) f"
    by simp

  let ?e = "SOME e. \<exists>e1 e2.
      e1 < e2 \<and>
      e = {e1..e2} \<and>
      e \<subseteq> {a..b} \<and>
      f (Suc (Suc n)) \<notin> e"
  from cab have ni: "newInt (Suc (Suc n)) f = ?e"
    by auto

  from ab have "a < b" by simp
  with closed_subset_ex have "\<exists>ka kb. ka < kb \<and> {ka..kb} \<subseteq> {a..b} \<and>
    f (Suc (Suc n)) \<notin> {ka..kb}" .
  then have "\<exists>e. \<exists>ka kb. ka < kb \<and> e = {ka..kb} \<and>
      {ka..kb} \<subseteq> {a..b} \<and> f (Suc (Suc n)) \<notin> {ka..kb}"
    by simp
  then have "\<exists>e.  \<exists>ka kb. ka < kb \<and> e = {ka..kb} \<and> e \<subseteq> {a..b} \<and> f (Suc (Suc n)) \<notin> e"
    by simp
  then have "\<exists>ka kb. ka < kb \<and> ?e = {ka..kb} \<and> ?e \<subseteq> {a..b} \<and> f (Suc (Suc n)) \<notin> ?e"
    by (rule someI_ex)
  with ab ni show "\<exists>ka kb. ka < kb \<and>
      newInt (Suc (Suc n)) f = {ka..kb} \<and>
      newInt (Suc (Suc n)) f \<subseteq> newInt (Suc n) f \<and>
      f (Suc (Suc n)) \<notin> newInt (Suc (Suc n)) f"
    by auto
qed

lemma newInt_subset: "newInt (Suc n) f \<subseteq> newInt n f"
  using newInt_ex by auto


text {* Another fundamental property is that no element in the range
of f is in the intersection of all closed intervals generated by
newInt. *}

lemma newInt_inter: "\<forall>n. f n \<notin> (\<Inter>n. newInt n f)"
proof
  fix n :: nat
  have "f n \<notin> newInt n f"
  proof (cases n)
    case 0
    moreover have "newInt 0 f = {f 0 + 1..f 0 + 2}"
      by simp
    ultimately show ?thesis by simp
  next
    case (Suc m)
    from newInt_ex have "\<exists>a b. a < b \<and> (newInt (Suc m) f) = {a..b} \<and>
      newInt (Suc m) f \<subseteq> newInt m f \<and> f (Suc m) \<notin> newInt (Suc m) f" .
    then have "f (Suc m) \<notin> newInt (Suc m) f"
      by auto
    with Suc show ?thesis by simp
  qed
  then show "f n \<notin> (\<Inter>n. newInt n f)" by auto
qed

lemma newInt_notempty: "(\<Inter>n. newInt n f) \<noteq> {}"
proof -
  let ?g = "\<lambda>n. newInt n f"
  have "\<forall>n. ?g (Suc n) \<subseteq> ?g n"
  proof
    fix n
    show "?g (Suc n) \<subseteq> ?g n" by (rule newInt_subset)
  qed
  moreover have "\<forall>n. \<exists>a b. ?g n = {a..b} \<and> a \<le> b"
  proof
    fix n :: nat
    show "\<exists>a b. ?g n = {a..b} \<and> a \<le> b"
    proof (cases n)
      case 0
      then have "?g n = {f 0 + 1..f 0 + 2} \<and> (f 0 + 1 \<le> f 0 + 2)"
        by simp
      then show ?thesis
        by blast
    next
      case (Suc m)
      have "\<exists>a b. a < b \<and> (newInt (Suc m) f) = {a..b} \<and>
        (newInt (Suc m) f) \<subseteq> (newInt m f) \<and> (f (Suc m)) \<notin> (newInt (Suc m) f)"
        by (rule newInt_ex)
      then obtain a and b where "a < b \<and> (newInt (Suc m) f) = {a..b}"
        by auto
      with Suc have "?g n = {a..b} \<and> a \<le> b"
        by auto
      then show ?thesis
        by blast
    qed
  qed
  ultimately show ?thesis by (rule NIP)
qed


subsection {* Final Theorem *}

theorem real_non_denum: "\<not> (\<exists>f :: nat \<Rightarrow> real. surj f)"
proof
  assume "\<exists>f :: nat \<Rightarrow> real. surj f"
  then obtain f :: "nat \<Rightarrow> real" where "surj f"
    by auto
  txt "We now produce a real number x that is not in the range of f, using the properties of newInt."
  have "\<exists>x. x \<in> (\<Inter>n. newInt n f)"
    using newInt_notempty by blast
  moreover have "\<forall>n. f n \<notin> (\<Inter>n. newInt n f)"
    by (rule newInt_inter)
  ultimately obtain x where "x \<in> (\<Inter>n. newInt n f)" and "\<forall>n. f n \<noteq> x"
    by blast
  moreover from `surj f` have "x \<in> range f"
    by simp
  ultimately show False
    by blast
qed

end

