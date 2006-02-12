(*  Title       : HOL/Real/ContNonDenum
    ID          : $Id$
    Author      : Benjamin Porter, Monash University, NICTA, 2005
*)

header {* Non-denumerability of the Continuum. *}

theory ContNotDenum
imports RComplete
begin

section {* Abstract *}

text {* The following document presents a proof that the Continuum is
uncountable. It is formalised in the Isabelle/Isar theorem proving
system.

{\em Theorem:} The Continuum @{text "\<real>"} is not denumerable. In other
words, there does not exist a function f:@{text "\<nat>\<Rightarrow>\<real>"} such that f is
surjective.

{\em Outline:} An elegant informal proof of this result uses Cantor's
Diagonalisation argument. The proof presented here is not this
one. First we formalise some properties of closed intervals, then we
prove the Nested Interval Property. This property relies on the
completeness of the Real numbers and is the foundation for our
argument. Informally it states that an intersection of countable
closed intervals (where each successive interval is a subset of the
last) is non-empty. We then assume a surjective function f:@{text
"\<nat>\<Rightarrow>\<real>"} exists and find a real x such that x is not in the range of f
by generating a sequence of closed intervals then using the NIP. *}

section {* Closed Intervals *}

text {* This section formalises some properties of closed intervals. *}

subsection {* Definition *}

constdefs closed_int :: "real \<Rightarrow> real \<Rightarrow> real set"
  "closed_int x y \<equiv> {z. x \<le> z \<and> z \<le> y}"

subsection {* Properties *}

lemma closed_int_subset:
  assumes xy: "x1 \<ge> x0" "y1 \<le> y0"
  shows "closed_int x1 y1 \<subseteq> closed_int x0 y0"
proof -
  {
    fix x::real
    assume "x \<in> closed_int x1 y1"
    hence "x \<ge> x1 \<and> x \<le> y1" by (unfold closed_int_def, simp)
    with xy have "x \<ge> x0 \<and> x \<le> y0" by auto
    hence "x \<in> closed_int x0 y0" by (unfold closed_int_def, simp)
  }
  thus ?thesis by auto
qed

lemma closed_int_least:
  assumes a: "a \<le> b"
  shows "a \<in> closed_int a b \<and> (\<forall>x \<in> closed_int a b. a \<le> x)"
proof
  from a have "a\<in>{x. a\<le>x \<and> x\<le>b}" by simp
  thus "a \<in> closed_int a b" by (unfold closed_int_def)
next
  have "\<forall>x\<in>{x. a\<le>x \<and> x\<le>b}. a\<le>x" by simp
  thus "\<forall>x \<in> closed_int a b. a \<le> x" by (unfold closed_int_def)
qed

lemma closed_int_most:
  assumes a: "a \<le> b"
  shows "b \<in> closed_int a b \<and> (\<forall>x \<in> closed_int a b. x \<le> b)"
proof
  from a have "b\<in>{x. a\<le>x \<and> x\<le>b}" by simp
  thus "b \<in> closed_int a b" by (unfold closed_int_def)
next
  have "\<forall>x\<in>{x. a\<le>x \<and> x\<le>b}. x\<le>b" by simp
  thus "\<forall>x \<in> closed_int a b. x\<le>b" by (unfold closed_int_def)
qed

lemma closed_not_empty:
  shows "a \<le> b \<Longrightarrow> \<exists>x. x \<in> closed_int a b" 
  by (auto dest: closed_int_least)

lemma closed_mem:
  assumes "a \<le> c" and "c \<le> b"
  shows "c \<in> closed_int a b"
  by (unfold closed_int_def) auto

lemma closed_subset:
  assumes ac: "a \<le> b"  "c \<le> d" 
  assumes closed: "closed_int a b \<subseteq> closed_int c d"
  shows "b \<ge> c"
proof -
  from closed have "\<forall>x\<in>closed_int a b. x\<in>closed_int c d" by auto
  hence "\<forall>x. a\<le>x \<and> x\<le>b \<longrightarrow> c\<le>x \<and> x\<le>d" by (unfold closed_int_def, auto)
  with ac have "c\<le>b \<and> b\<le>d" by simp
  thus ?thesis by auto
qed


section {* Nested Interval Property *}

theorem NIP:
  fixes f::"nat \<Rightarrow> real set"
  assumes subset: "\<forall>n. f (Suc n) \<subseteq> f n"
  and closed: "\<forall>n. \<exists>a b. f n = closed_int a b \<and> a \<le> b"
  shows "(\<Inter>n. f n) \<noteq> {}"
proof -
  let ?g = "\<lambda>n. (SOME c. c\<in>(f n) \<and> (\<forall>x\<in>(f n). c \<le> x))"
  have ne: "\<forall>n. \<exists>x. x\<in>(f n)"
  proof
    fix n
    from closed have "\<exists>a b. f n = closed_int a b \<and> a \<le> b" by simp
    then obtain a and b where fn: "f n = closed_int a b \<and> a \<le> b" by auto
    hence "a \<le> b" ..
    with closed_not_empty have "\<exists>x. x\<in>closed_int a b" by simp
    with fn show "\<exists>x. x\<in>(f n)" by simp
  qed

  have gdef: "\<forall>n. (?g n)\<in>(f n) \<and> (\<forall>x\<in>(f n). (?g n)\<le>x)"
  proof
    fix n
    from closed have "\<exists>a b. f n = closed_int a b \<and> a \<le> b" ..
    then obtain a and b where ff: "f n = closed_int a b" and "a \<le> b" by auto
    hence "a \<le> b" by simp
    hence "a\<in>closed_int a b \<and> (\<forall>x\<in>closed_int a b. a \<le> x)" by (rule closed_int_least)
    with ff have "a\<in>(f n) \<and> (\<forall>x\<in>(f n). a \<le> x)" by simp
    hence "\<exists>c. c\<in>(f n) \<and> (\<forall>x\<in>(f n). c \<le> x)" ..
    thus "(?g n)\<in>(f n) \<and> (\<forall>x\<in>(f n). (?g n)\<le>x)" by (rule someI_ex)
  qed

  -- "A denotes the set of all left-most points of all the intervals ..."
  moreover obtain A where Adef: "A = ?g ` \<nat>" by simp
  ultimately have "\<exists>x. x\<in>A"
  proof -
    have "(0::nat) \<in> \<nat>" by simp
    moreover have "?g 0 = ?g 0" by simp
    ultimately have "?g 0 \<in> ?g ` \<nat>" by (rule  rev_image_eqI)
    with Adef have "?g 0 \<in> A" by simp
    thus ?thesis ..
  qed

  -- "Now show that A is bounded above ..."
  moreover have "\<exists>y. isUb (UNIV::real set) A y"
  proof -
    {
      fix n
      from ne have ex: "\<exists>x. x\<in>(f n)" ..
      from gdef have "(?g n)\<in>(f n) \<and> (\<forall>x\<in>(f n). (?g n)\<le>x)" by simp
      moreover
      from closed have "\<exists>a b. f n = closed_int a b \<and> a \<le> b" ..
      then obtain a and b where "f n = closed_int a b \<and> a \<le> b" by auto
      hence "b\<in>(f n) \<and> (\<forall>x\<in>(f n). x \<le> b)" using closed_int_most by blast
      ultimately have "\<forall>x\<in>(f n). (?g n) \<le> b" by simp
      with ex have "(?g n) \<le> b" by auto
      hence "\<exists>b. (?g n) \<le> b" by auto
    }
    hence aux: "\<forall>n. \<exists>b. (?g n) \<le> b" ..

    have fs: "\<forall>n::nat. f n \<subseteq> f 0"
    proof (rule allI, induct_tac n)
      show "f 0 \<subseteq> f 0" by simp
    next
      fix n
      assume "f n \<subseteq> f 0"
      moreover from subset have "f (Suc n) \<subseteq> f n" ..
      ultimately show "f (Suc n) \<subseteq> f 0" by simp
    qed
    have "\<forall>n. (?g n)\<in>(f 0)"
    proof
      fix n
      from gdef have "(?g n)\<in>(f n) \<and> (\<forall>x\<in>(f n). (?g n)\<le>x)" by simp
      hence "?g n \<in> f n" ..
      with fs show "?g n \<in> f 0" by auto
    qed
    moreover from closed
      obtain a and b where "f 0 = closed_int a b" and alb: "a \<le> b" by blast
    ultimately have "\<forall>n. ?g n \<in> closed_int a b" by auto
    with alb have "\<forall>n. ?g n \<le> b" using closed_int_most by blast
    with Adef have "\<forall>y\<in>A. y\<le>b" by auto
    hence "A *<= b" by (unfold setle_def)
    moreover have "b \<in> (UNIV::real set)" by simp
    ultimately have "A *<= b \<and> b \<in> (UNIV::real set)" by simp
    hence "isUb (UNIV::real set) A b" by (unfold isUb_def)
    thus ?thesis by auto
  qed
  -- "by the Axiom Of Completeness, A has a least upper bound ..."
  ultimately have "\<exists>t. isLub UNIV A t" by (rule reals_complete)

  -- "denote this least upper bound as t ..."
  then obtain t where tdef: "isLub UNIV A t" ..

  -- "and finally show that this least upper bound is in all the intervals..."
  have "\<forall>n. t \<in> f n"
  proof
    fix n::nat
    from closed obtain a and b where
      int: "f n = closed_int a b" and alb: "a \<le> b" by blast

    have "t \<ge> a"
    proof -
      have "a \<in> A"
      proof -
          (* by construction *)
        from alb int have ain: "a\<in>f n \<and> (\<forall>x\<in>f n. a \<le> x)"
          using closed_int_least by blast
        moreover have "\<forall>e. e\<in>f n \<and> (\<forall>x\<in>f n. e \<le> x) \<longrightarrow> e = a"
        proof clarsimp
          fix e
          assume ein: "e \<in> f n" and lt: "\<forall>x\<in>f n. e \<le> x"
          from lt ain have aux: "\<forall>x\<in>f n. a \<le> x \<and> e \<le> x" by auto
  
          from ein aux have "a \<le> e \<and> e \<le> e" by auto
          moreover from ain aux have "a \<le> a \<and> e \<le> a" by auto
          ultimately show "e = a" by simp
        qed
        hence "\<And>e.  e\<in>f n \<and> (\<forall>x\<in>f n. e \<le> x) \<Longrightarrow> e = a" by simp
        ultimately have "(?g n) = a" by (rule some_equality)
        moreover
        {
          have "n = of_nat n" by simp
          moreover have "of_nat n \<in> \<nat>" by simp
          ultimately have "n \<in> \<nat>"
            apply -
            apply (subst(asm) eq_sym_conv)
            apply (erule subst)
            .
        }
        with Adef have "(?g n) \<in> A" by auto
        ultimately show ?thesis by simp
      qed 
      with tdef show "a \<le> t" by (rule isLubD2)
    qed
    moreover have "t \<le> b"
    proof -
      have "isUb UNIV A b"
      proof -
        {
          from alb int have
            ain: "b\<in>f n \<and> (\<forall>x\<in>f n. x \<le> b)" using closed_int_most by blast
          
          have subsetd: "\<forall>m. \<forall>n. f (n + m) \<subseteq> f n"
          proof (rule allI, induct_tac m)
            show "\<forall>n. f (n + 0) \<subseteq> f n" by simp
          next
            fix m n
            assume pp: "\<forall>p. f (p + n) \<subseteq> f p"
            {
              fix p
              from pp have "f (p + n) \<subseteq> f p" by simp
              moreover from subset have "f (Suc (p + n)) \<subseteq> f (p + n)" by auto
              hence "f (p + (Suc n)) \<subseteq> f (p + n)" by simp
              ultimately have "f (p + (Suc n)) \<subseteq> f p" by simp
            }
            thus "\<forall>p. f (p + Suc n) \<subseteq> f p" ..
          qed 
          have subsetm: "\<forall>\<alpha> \<beta>. \<alpha> \<ge> \<beta> \<longrightarrow> (f \<alpha>) \<subseteq> (f \<beta>)"
          proof ((rule allI)+, rule impI)
            fix \<alpha>::nat and \<beta>::nat
            assume "\<beta> \<le> \<alpha>"
            hence "\<exists>k. \<alpha> = \<beta> + k" by (simp only: le_iff_add)
            then obtain k where "\<alpha> = \<beta> + k" ..
            moreover
            from subsetd have "f (\<beta> + k) \<subseteq> f \<beta>" by simp
            ultimately show "f \<alpha> \<subseteq> f \<beta>" by auto
          qed 
          
          fix m   
          {
            assume "m \<ge> n"
            with subsetm have "f m \<subseteq> f n" by simp
            with ain have "\<forall>x\<in>f m. x \<le> b" by auto
            moreover
            from gdef have "?g m \<in> f m \<and> (\<forall>x\<in>f m. ?g m \<le> x)" by simp
            ultimately have "?g m \<le> b" by auto
          }
          moreover
          {
            assume "\<not>(m \<ge> n)"
            hence "m < n" by simp
            with subsetm have sub: "(f n) \<subseteq> (f m)" by simp
            from closed obtain ma and mb where
              "f m = closed_int ma mb \<and> ma \<le> mb" by blast
            hence one: "ma \<le> mb" and fm: "f m = closed_int ma mb" by auto 
            from one alb sub fm int have "ma \<le> b" using closed_subset by blast
            moreover have "(?g m) = ma"
            proof -
              from gdef have "?g m \<in> f m \<and> (\<forall>x\<in>f m. ?g m \<le> x)" ..
              moreover from one have
                "ma \<in> closed_int ma mb \<and> (\<forall>x\<in>closed_int ma mb. ma \<le> x)"
                by (rule closed_int_least)
              with fm have "ma\<in>f m \<and> (\<forall>x\<in>f m. ma \<le> x)" by simp
              ultimately have "ma \<le> ?g m \<and> ?g m \<le> ma" by auto
              thus "?g m = ma" by auto
            qed
            ultimately have "?g m \<le> b" by simp
          } 
          ultimately have "?g m \<le> b" by (rule case_split)
        }
        with Adef have "\<forall>y\<in>A. y\<le>b" by auto
        hence "A *<= b" by (unfold setle_def)
        moreover have "b \<in> (UNIV::real set)" by simp
        ultimately have "A *<= b \<and> b \<in> (UNIV::real set)" by simp
        thus "isUb (UNIV::real set) A b" by (unfold isUb_def)
      qed
      with tdef show "t \<le> b" by (rule isLub_le_isUb)
    qed
    ultimately have "t \<in> closed_int a b" by (rule closed_mem)
    with int show "t \<in> f n" by simp
  qed
  hence "t \<in> (\<Inter>n. f n)" by auto
  thus ?thesis by auto
qed

section {* Generating the intervals *}

subsubsection {* Existence of non-singleton closed intervals *}

text {* This lemma asserts that given any non-singleton closed
interval (a,b) and any element c, there exists a closed interval that
is a subset of (a,b) and that does not contain c and is a
non-singleton itself. *}

lemma closed_subset_ex:
  fixes c::real
  assumes alb: "a < b"
  shows
    "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int a b \<and> c \<notin> (closed_int ka kb)"
proof -
  {
    assume clb: "c < b"
    {
      assume cla: "c < a"
      from alb cla clb have "c \<notin> closed_int a b" by (unfold closed_int_def, auto)
      with alb have
        "a < b \<and> closed_int a b \<subseteq> closed_int a b \<and> c \<notin> closed_int a b"
        by auto
      hence
        "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int a b \<and> c \<notin> (closed_int ka kb)"
        by auto
    }
    moreover
    {
      assume ncla: "\<not>(c < a)"
      with clb have cdef: "a \<le> c \<and> c < b" by simp
      obtain ka where kadef: "ka = (c + b)/2" by blast

      from kadef clb have kalb: "ka < b" by auto
      moreover from kadef cdef have kagc: "ka > c" by simp
      ultimately have "c\<notin>(closed_int ka b)" by (unfold closed_int_def, auto)
      moreover from cdef kagc have "ka \<ge> a" by simp
      hence "closed_int ka b \<subseteq> closed_int a b" by (unfold closed_int_def, auto)
      ultimately have
        "ka < b  \<and> closed_int ka b \<subseteq> closed_int a b \<and> c \<notin> closed_int ka b"
        using kalb by auto
      hence
        "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int a b \<and> c \<notin> (closed_int ka kb)"
        by auto

    }
    ultimately have
      "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int a b \<and> c \<notin> (closed_int ka kb)"
      by (rule case_split)
  }
  moreover
  {
    assume "\<not> (c < b)"
    hence cgeb: "c \<ge> b" by simp

    obtain kb where kbdef: "kb = (a + b)/2" by blast
    with alb have kblb: "kb < b" by auto
    with kbdef cgeb have "a < kb \<and> kb < c" by auto
    moreover hence "c \<notin> (closed_int a kb)" by (unfold closed_int_def, auto)
    moreover from kblb have
      "closed_int a kb \<subseteq> closed_int a b" by (unfold closed_int_def, auto)
    ultimately have
      "a < kb \<and>  closed_int a kb \<subseteq> closed_int a b \<and> c\<notin>closed_int a kb"
      by simp
    hence
      "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int a b \<and> c \<notin> (closed_int ka kb)"
      by auto
  }
  ultimately show ?thesis by (rule case_split)
qed

subsection {* newInt: Interval generation *}

text {* Given a function f:@{text "\<nat>\<Rightarrow>\<real>"}, newInt (Suc n) f returns a
closed interval such that @{text "newInt (Suc n) f \<subseteq> newInt n f"} and
does not contain @{text "f (Suc n)"}. With the base case defined such
that @{text "(f 0)\<notin>newInt 0 f"}. *}

subsubsection {* Definition *}

consts newInt :: "nat \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> (real set)"
primrec
"newInt 0 f = closed_int (f 0 + 1) (f 0 + 2)"
"newInt (Suc n) f =
  (SOME e. (\<exists>e1 e2.
   e1 < e2 \<and>
   e = closed_int e1 e2 \<and>
   e \<subseteq> (newInt n f) \<and>
   (f (Suc n)) \<notin> e)
  )"

subsubsection {* Properties *}

text {* We now show that every application of newInt returns an
appropriate interval. *}

lemma newInt_ex:
  "\<exists>a b. a < b \<and>
   newInt (Suc n) f = closed_int a b \<and>
   newInt (Suc n) f \<subseteq> newInt n f \<and>
   f (Suc n) \<notin> newInt (Suc n) f"
proof (induct n)
  case 0

  let ?e = "SOME e. \<exists>e1 e2.
   e1 < e2 \<and>
   e = closed_int e1 e2 \<and>
   e \<subseteq> closed_int (f 0 + 1) (f 0 + 2) \<and>
   f (Suc 0) \<notin> e"

  have "newInt (Suc 0) f = ?e" by auto
  moreover
  have "f 0 + 1 < f 0 + 2" by simp
  with closed_subset_ex have
    "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int (f 0 + 1) (f 0 + 2) \<and>
     f (Suc 0) \<notin> (closed_int ka kb)" .
  hence
    "\<exists>e. \<exists>ka kb. ka < kb \<and> e = closed_int ka kb \<and>
     e \<subseteq> closed_int (f 0 + 1) (f 0 + 2) \<and> f (Suc 0) \<notin> e" by simp
  hence
    "\<exists>ka kb. ka < kb \<and> ?e = closed_int ka kb \<and>
     ?e \<subseteq> closed_int (f 0 + 1) (f 0 + 2) \<and> f (Suc 0) \<notin> ?e"
    by (rule someI_ex)
  ultimately have "\<exists>e1 e2. e1 < e2 \<and>
   newInt (Suc 0) f = closed_int e1 e2 \<and>
   newInt (Suc 0) f \<subseteq> closed_int (f 0 + 1) (f 0 + 2) \<and>
   f (Suc 0) \<notin> newInt (Suc 0) f" by simp
  thus
    "\<exists>a b. a < b \<and> newInt (Suc 0) f = closed_int a b \<and>
     newInt (Suc 0) f \<subseteq> newInt 0 f \<and> f (Suc 0) \<notin> newInt (Suc 0) f"
    by simp
next
  case (Suc n)
  hence "\<exists>a b.
   a < b \<and>
   newInt (Suc n) f = closed_int a b \<and>
   newInt (Suc n) f \<subseteq> newInt n f \<and>
   f (Suc n) \<notin> newInt (Suc n) f" by simp
  then obtain a and b where ab: "a < b \<and>
   newInt (Suc n) f = closed_int a b \<and>
   newInt (Suc n) f \<subseteq> newInt n f \<and>
   f (Suc n) \<notin> newInt (Suc n) f" by auto
  hence cab: "closed_int a b = newInt (Suc n) f" by simp

  let ?e = "SOME e. \<exists>e1 e2.
    e1 < e2 \<and>
    e = closed_int e1 e2 \<and>
    e \<subseteq> closed_int a b \<and>
    f (Suc (Suc n)) \<notin> e"
  from cab have ni: "newInt (Suc (Suc n)) f = ?e" by auto

  from ab have "a < b" by simp
  with closed_subset_ex have
    "\<exists>ka kb. ka < kb \<and> closed_int ka kb \<subseteq> closed_int a b \<and>
     f (Suc (Suc n)) \<notin> closed_int ka kb" .
  hence
    "\<exists>e. \<exists>ka kb. ka < kb \<and> e = closed_int ka kb \<and>
     closed_int ka kb \<subseteq> closed_int a b \<and> f (Suc (Suc n)) \<notin> closed_int ka kb"
    by simp
  hence
    "\<exists>e.  \<exists>ka kb. ka < kb \<and> e = closed_int ka kb \<and>
     e \<subseteq> closed_int a b \<and> f (Suc (Suc n)) \<notin> e" by simp
  hence
    "\<exists>ka kb. ka < kb \<and> ?e = closed_int ka kb \<and>
     ?e \<subseteq> closed_int a b \<and> f (Suc (Suc n)) \<notin> ?e" by (rule someI_ex)
  with ab ni show
    "\<exists>ka kb. ka < kb \<and>
     newInt (Suc (Suc n)) f = closed_int ka kb \<and>
     newInt (Suc (Suc n)) f \<subseteq> newInt (Suc n) f \<and>
     f (Suc (Suc n)) \<notin> newInt (Suc (Suc n)) f" by auto
qed

lemma newInt_subset:
  "newInt (Suc n) f \<subseteq> newInt n f"
  using newInt_ex by auto


text {* Another fundamental property is that no element in the range
of f is in the intersection of all closed intervals generated by
newInt. *}

lemma newInt_inter:
  "\<forall>n. f n \<notin> (\<Inter>n. newInt n f)"
proof
  fix n::nat
  {
    assume n0: "n = 0"
    moreover have "newInt 0 f = closed_int (f 0 + 1) (f 0 + 2)" by simp
    ultimately have "f n \<notin> newInt n f" by (unfold closed_int_def, simp)
  }
  moreover
  {
    assume "\<not> n = 0"
    hence "n > 0" by simp
    then obtain m where ndef: "n = Suc m" by (auto simp add: gr0_conv_Suc)

    from newInt_ex have
      "\<exists>a b. a < b \<and> (newInt (Suc m) f) = closed_int a b \<and>
       newInt (Suc m) f \<subseteq> newInt m f \<and> f (Suc m) \<notin> newInt (Suc m) f" .
    then have "f (Suc m) \<notin> newInt (Suc m) f" by auto
    with ndef have "f n \<notin> newInt n f" by simp
  }
  ultimately have "f n \<notin> newInt n f" by (rule case_split)
  thus "f n \<notin> (\<Inter>n. newInt n f)" by auto
qed


lemma newInt_notempty:
  "(\<Inter>n. newInt n f) \<noteq> {}"
proof -
  let ?g = "\<lambda>n. newInt n f"
  have "\<forall>n. ?g (Suc n) \<subseteq> ?g n"
  proof
    fix n
    show "?g (Suc n) \<subseteq> ?g n" by (rule newInt_subset)
  qed
  moreover have "\<forall>n. \<exists>a b. ?g n = closed_int a b \<and> a \<le> b"
  proof
    fix n::nat
    {
      assume "n = 0"
      then have
        "?g n = closed_int (f 0 + 1) (f 0 + 2) \<and> (f 0 + 1 \<le> f 0 + 2)"
        by simp
      hence "\<exists>a b. ?g n = closed_int a b \<and> a \<le> b" by blast
    }
    moreover
    {
      assume "\<not> n = 0"
      then have "n > 0" by simp
      then obtain m where nd: "n = Suc m" by (auto simp add: gr0_conv_Suc)

      have
        "\<exists>a b. a < b \<and> (newInt (Suc m) f) = closed_int a b \<and>
        (newInt (Suc m) f) \<subseteq> (newInt m f) \<and> (f (Suc m)) \<notin> (newInt (Suc m) f)"
        by (rule newInt_ex)
      then obtain a and b where
        "a < b \<and> (newInt (Suc m) f) = closed_int a b" by auto
      with nd have "?g n = closed_int a b \<and> a \<le> b" by auto
      hence "\<exists>a b. ?g n = closed_int a b \<and> a \<le> b" by blast
    }
    ultimately show "\<exists>a b. ?g n = closed_int a b \<and> a \<le> b" by (rule case_split)
  qed
  ultimately show ?thesis by (rule NIP)
qed


section {* Final Theorem *}

theorem real_non_denum:
  shows "\<not> (\<exists>f::nat\<Rightarrow>real. surj f)"
proof -- "by contradiction"
  assume "\<exists>f::nat\<Rightarrow>real. surj f"
  then obtain f::"nat\<Rightarrow>real" where "surj f" by auto
  hence rangeF: "range f = UNIV" by (rule surj_range)
  -- "We now produce a real number x that is not in the range of f, using the properties of newInt. "
  have "\<exists>x. x \<in> (\<Inter>n. newInt n f)" using newInt_notempty by blast
  moreover have "\<forall>n. f n \<notin> (\<Inter>n. newInt n f)" by (rule newInt_inter)
  ultimately obtain x where "x \<in> (\<Inter>n. newInt n f)" and "\<forall>n. f n \<noteq> x" by blast
  moreover from rangeF have "x \<in> range f" by simp
  ultimately show False by blast
qed

end