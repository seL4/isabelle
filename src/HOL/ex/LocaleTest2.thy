(*  Title:      HOL/ex/LocaleTest2.thy
    Author:     Clemens Ballarin
    Copyright (c) 2007 by Clemens Ballarin

More regression tests for locales.
Definitions are less natural in FOL, since there is no selection operator.
Hence we do them here in HOL, not in the main test suite for locales,
which is FOL/ex/LocaleTest.thy
*)

section \<open>Test of Locale Interpretation\<close>

theory LocaleTest2
imports Main 
begin

section \<open>Interpretation of Defined Concepts\<close>

text \<open>Naming convention for global objects: prefixes D and d\<close>


subsection \<open>Lattices\<close>

text \<open>Much of the lattice proofs are from HOL/Lattice.\<close>


subsubsection \<open>Definitions\<close>

locale dpo =
  fixes le :: "['a, 'a] => bool" (infixl \<open>\<sqsubseteq>\<close> 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and antisym [intro]: "[| x \<sqsubseteq> y; y \<sqsubseteq> x |] ==> x = y"
    and trans [trans]: "[| x \<sqsubseteq> y; y \<sqsubseteq> z |] ==> x \<sqsubseteq> z"

begin

theorem circular:
  "[| x \<sqsubseteq> y; y \<sqsubseteq> z; z \<sqsubseteq> x |] ==> x = y & y = z"
  by (blast intro: trans)

definition
  less :: "['a, 'a] => bool" (infixl \<open>\<sqsubset>\<close> 50)
  where "(x \<sqsubset> y) = (x \<sqsubseteq> y & x ~= y)"

theorem abs_test:
  "(\<sqsubset>) = (\<lambda>x y. x \<sqsubset> y)"
  by simp

definition
  is_inf :: "['a, 'a, 'a] => bool"
  where "is_inf x y i = (i \<sqsubseteq> x \<and> i \<sqsubseteq> y \<and> (\<forall>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<longrightarrow> z \<sqsubseteq> i))"

definition
  is_sup :: "['a, 'a, 'a] => bool"
  where "is_sup x y s = (x \<sqsubseteq> s \<and> y \<sqsubseteq> s \<and> (\<forall>z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> s \<sqsubseteq> z))"

end

locale dlat = dpo +
  assumes ex_inf: "\<exists>inf. dpo.is_inf le x y inf"
    and ex_sup: "\<exists>sup. dpo.is_sup le x y sup"

begin

definition
  meet :: "['a, 'a] => 'a" (infixl \<open>\<sqinter>\<close> 70)
  where "x \<sqinter> y = (THE inf. is_inf x y inf)"

definition
  join :: "['a, 'a] => 'a" (infixl \<open>\<squnion>\<close> 65)
  where "x \<squnion> y = (THE sup. is_sup x y sup)"

lemma is_infI [intro?]: "i \<sqsubseteq> x \<Longrightarrow> i \<sqsubseteq> y \<Longrightarrow>
    (\<And>z. z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> i) \<Longrightarrow> is_inf x y i"
  by (unfold is_inf_def) blast

lemma is_inf_lower [elim?]:
  "is_inf x y i \<Longrightarrow> (i \<sqsubseteq> x \<Longrightarrow> i \<sqsubseteq> y \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold is_inf_def) blast

lemma is_inf_greatest [elim?]:
    "is_inf x y i \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> i"
  by (unfold is_inf_def) blast

theorem is_inf_uniq: "is_inf x y i \<Longrightarrow> is_inf x y i' \<Longrightarrow> i = i'"
proof -
  assume inf: "is_inf x y i"
  assume inf': "is_inf x y i'"
  show ?thesis
  proof (rule antisym)
    from inf' show "i \<sqsubseteq> i'"
    proof (rule is_inf_greatest)
      from inf show "i \<sqsubseteq> x" ..
      from inf show "i \<sqsubseteq> y" ..
    qed
    from inf show "i' \<sqsubseteq> i"
    proof (rule is_inf_greatest)
      from inf' show "i' \<sqsubseteq> x" ..
      from inf' show "i' \<sqsubseteq> y" ..
    qed
  qed
qed

theorem is_inf_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> is_inf x y x"
proof -
  assume "x \<sqsubseteq> y"
  show ?thesis
  proof
    show "x \<sqsubseteq> x" ..
    show "x \<sqsubseteq> y" by fact
    fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y" show "z \<sqsubseteq> x" by fact
  qed
qed

lemma meet_equality [elim?]: "is_inf x y i \<Longrightarrow> x \<sqinter> y = i"
proof (unfold meet_def)
  assume "is_inf x y i"
  then show "(THE i. is_inf x y i) = i"
    by (rule the_equality) (rule is_inf_uniq [OF _ \<open>is_inf x y i\<close>])
qed

lemma meetI [intro?]:
    "i \<sqsubseteq> x \<Longrightarrow> i \<sqsubseteq> y \<Longrightarrow> (\<And>z. z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> i) \<Longrightarrow> x \<sqinter> y = i"
  by (rule meet_equality, rule is_infI) blast+

lemma is_inf_meet [intro?]: "is_inf x y (x \<sqinter> y)"
proof (unfold meet_def)
  from ex_inf obtain i where "is_inf x y i" ..
  then show "is_inf x y (THE i. is_inf x y i)"
    by (rule theI) (rule is_inf_uniq [OF _ \<open>is_inf x y i\<close>])
qed

lemma meet_left [intro?]:
  "x \<sqinter> y \<sqsubseteq> x"
  by (rule is_inf_lower) (rule is_inf_meet)

lemma meet_right [intro?]:
  "x \<sqinter> y \<sqsubseteq> y"
  by (rule is_inf_lower) (rule is_inf_meet)

lemma meet_le [intro?]:
  "[| z \<sqsubseteq> x; z \<sqsubseteq> y |] ==> z \<sqsubseteq> x \<sqinter> y"
  by (rule is_inf_greatest) (rule is_inf_meet)

lemma is_supI [intro?]: "x \<sqsubseteq> s \<Longrightarrow> y \<sqsubseteq> s \<Longrightarrow>
    (\<And>z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> s \<sqsubseteq> z) \<Longrightarrow> is_sup x y s"
  by (unfold is_sup_def) blast

lemma is_sup_least [elim?]:
    "is_sup x y s \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> s \<sqsubseteq> z"
  by (unfold is_sup_def) blast

lemma is_sup_upper [elim?]:
    "is_sup x y s \<Longrightarrow> (x \<sqsubseteq> s \<Longrightarrow> y \<sqsubseteq> s \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold is_sup_def) blast

theorem is_sup_uniq: "is_sup x y s \<Longrightarrow> is_sup x y s' \<Longrightarrow> s = s'"
proof -
  assume sup: "is_sup x y s"
  assume sup': "is_sup x y s'"
  show ?thesis
  proof (rule antisym)
    from sup show "s \<sqsubseteq> s'"
    proof (rule is_sup_least)
      from sup' show "x \<sqsubseteq> s'" ..
      from sup' show "y \<sqsubseteq> s'" ..
    qed
    from sup' show "s' \<sqsubseteq> s"
    proof (rule is_sup_least)
      from sup show "x \<sqsubseteq> s" ..
      from sup show "y \<sqsubseteq> s" ..
    qed
  qed
qed

theorem is_sup_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> is_sup x y y"
proof -
  assume "x \<sqsubseteq> y"
  show ?thesis
  proof
    show "x \<sqsubseteq> y" by fact
    show "y \<sqsubseteq> y" ..
    fix z assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
    show "y \<sqsubseteq> z" by fact
  qed
qed

lemma join_equality [elim?]: "is_sup x y s \<Longrightarrow> x \<squnion> y = s"
proof (unfold join_def)
  assume "is_sup x y s"
  then show "(THE s. is_sup x y s) = s"
    by (rule the_equality) (rule is_sup_uniq [OF _ \<open>is_sup x y s\<close>])
qed

lemma joinI [intro?]: "x \<sqsubseteq> s \<Longrightarrow> y \<sqsubseteq> s \<Longrightarrow>
    (\<And>z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> s \<sqsubseteq> z) \<Longrightarrow> x \<squnion> y = s"
  by (rule join_equality, rule is_supI) blast+

lemma is_sup_join [intro?]: "is_sup x y (x \<squnion> y)"
proof (unfold join_def)
  from ex_sup obtain s where "is_sup x y s" ..
  then show "is_sup x y (THE s. is_sup x y s)"
    by (rule theI) (rule is_sup_uniq [OF _ \<open>is_sup x y s\<close>])
qed

lemma join_left [intro?]:
  "x \<sqsubseteq> x \<squnion> y"
  by (rule is_sup_upper) (rule is_sup_join)

lemma join_right [intro?]:
  "y \<sqsubseteq> x \<squnion> y"
  by (rule is_sup_upper) (rule is_sup_join)

lemma join_le [intro?]:
  "[| x \<sqsubseteq> z; y \<sqsubseteq> z |] ==> x \<squnion> y \<sqsubseteq> z"
  by (rule is_sup_least) (rule is_sup_join)

theorem meet_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
proof (rule meetI)
  show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> x \<sqinter> y"
  proof
    show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> x" ..
    show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y"
    proof -
      have "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y \<sqinter> z" ..
      also have "\<dots> \<sqsubseteq> y" ..
      finally show ?thesis .
    qed
  qed
  show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> z"
  proof -
    have "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y \<sqinter> z" ..
    also have "\<dots> \<sqsubseteq> z" ..
    finally show ?thesis .
  qed
  fix w assume "w \<sqsubseteq> x \<sqinter> y" and "w \<sqsubseteq> z"
  show "w \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
  proof
    show "w \<sqsubseteq> x"
    proof -
      have "w \<sqsubseteq> x \<sqinter> y" by fact
      also have "\<dots> \<sqsubseteq> x" ..
      finally show ?thesis .
    qed
    show "w \<sqsubseteq> y \<sqinter> z"
    proof
      show "w \<sqsubseteq> y"
      proof -
        have "w \<sqsubseteq> x \<sqinter> y" by fact
        also have "\<dots> \<sqsubseteq> y" ..
        finally show ?thesis .
      qed
      show "w \<sqsubseteq> z" by fact
    qed
  qed
qed

theorem meet_commute: "x \<sqinter> y = y \<sqinter> x"
proof (rule meetI)
  show "y \<sqinter> x \<sqsubseteq> x" ..
  show "y \<sqinter> x \<sqsubseteq> y" ..
  fix z assume "z \<sqsubseteq> y" and "z \<sqsubseteq> x"
  then show "z \<sqsubseteq> y \<sqinter> x" ..
qed

theorem meet_join_absorb: "x \<sqinter> (x \<squnion> y) = x"
proof (rule meetI)
  show "x \<sqsubseteq> x" ..
  show "x \<sqsubseteq> x \<squnion> y" ..
  fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> x \<squnion> y"
  show "z \<sqsubseteq> x" by fact
qed

theorem join_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
proof (rule joinI)
  show "x \<squnion> y \<sqsubseteq> x \<squnion> (y \<squnion> z)"
  proof
    show "x \<sqsubseteq> x \<squnion> (y \<squnion> z)" ..
    show "y \<sqsubseteq> x \<squnion> (y \<squnion> z)"
    proof -
      have "y \<sqsubseteq> y \<squnion> z" ..
      also have "... \<sqsubseteq> x \<squnion> (y \<squnion> z)" ..
      finally show ?thesis .
    qed
  qed
  show "z \<sqsubseteq> x \<squnion> (y \<squnion> z)"
  proof -
    have "z \<sqsubseteq> y \<squnion> z"  ..
    also have "... \<sqsubseteq> x \<squnion> (y \<squnion> z)" ..
    finally show ?thesis .
  qed
  fix w assume "x \<squnion> y \<sqsubseteq> w" and "z \<sqsubseteq> w"
  show "x \<squnion> (y \<squnion> z) \<sqsubseteq> w"
  proof
    show "x \<sqsubseteq> w"
    proof -
      have "x \<sqsubseteq> x \<squnion> y" ..
      also have "\<dots> \<sqsubseteq> w" by fact
      finally show ?thesis .
    qed
    show "y \<squnion> z \<sqsubseteq> w"
    proof
      show "y \<sqsubseteq> w"
      proof -
        have "y \<sqsubseteq> x \<squnion> y" ..
        also have "... \<sqsubseteq> w" by fact
        finally show ?thesis .
      qed
      show "z \<sqsubseteq> w" by fact
    qed
  qed
qed

theorem join_commute: "x \<squnion> y = y \<squnion> x"
proof (rule joinI)
  show "x \<sqsubseteq> y \<squnion> x" ..
  show "y \<sqsubseteq> y \<squnion> x" ..
  fix z assume "y \<sqsubseteq> z" and "x \<sqsubseteq> z"
  then show "y \<squnion> x \<sqsubseteq> z" ..
qed

theorem join_meet_absorb: "x \<squnion> (x \<sqinter> y) = x"
proof (rule joinI)
  show "x \<sqsubseteq> x" ..
  show "x \<sqinter> y \<sqsubseteq> x" ..
  fix z assume "x \<sqsubseteq> z" and "x \<sqinter> y \<sqsubseteq> z"
  show "x \<sqsubseteq> z" by fact
qed

theorem meet_idem: "x \<sqinter> x = x"
proof -
  have "x \<sqinter> (x \<squnion> (x \<sqinter> x)) = x" by (rule meet_join_absorb)
  also have "x \<squnion> (x \<sqinter> x) = x" by (rule join_meet_absorb)
  finally show ?thesis .
qed

theorem meet_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
proof (rule meetI)
  assume "x \<sqsubseteq> y"
  show "x \<sqsubseteq> x" ..
  show "x \<sqsubseteq> y" by fact
  fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
  show "z \<sqsubseteq> x" by fact
qed

theorem meet_related2 [elim?]: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
  by (drule meet_related) (simp add: meet_commute)

theorem join_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
proof (rule joinI)
  assume "x \<sqsubseteq> y"
  show "y \<sqsubseteq> y" ..
  show "x \<sqsubseteq> y" by fact
  fix z assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
  show "y \<sqsubseteq> z" by fact
qed

theorem join_related2 [elim?]: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  by (drule join_related) (simp add: join_commute)


text \<open>Additional theorems\<close>

theorem meet_connection: "(x \<sqsubseteq> y) = (x \<sqinter> y = x)"
proof
  assume "x \<sqsubseteq> y"
  then have "is_inf x y x" ..
  then show "x \<sqinter> y = x" ..
next
  have "x \<sqinter> y \<sqsubseteq> y" ..
  also assume "x \<sqinter> y = x"
  finally show "x \<sqsubseteq> y" .
qed

theorem meet_connection2: "(x \<sqsubseteq> y) = (y \<sqinter> x = x)"
  using meet_commute meet_connection by simp

theorem join_connection: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
proof
  assume "x \<sqsubseteq> y"
  then have "is_sup x y y" ..
  then show "x \<squnion> y = y" ..
next
  have "x \<sqsubseteq> x \<squnion> y" ..
  also assume "x \<squnion> y = y"
  finally show "x \<sqsubseteq> y" .
qed

theorem join_connection2: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
  using join_commute join_connection by simp


text \<open>Naming according to Jacobson I, p.\ 459.\<close>

lemmas L1 = join_commute meet_commute
lemmas L2 = join_assoc meet_assoc
(*lemmas L3 = join_idem meet_idem*)
lemmas L4 = join_meet_absorb meet_join_absorb

end

locale ddlat = dlat +
  assumes meet_distr:
    "dlat.meet le x (dlat.join le y z) =
    dlat.join le (dlat.meet le x y) (dlat.meet le x z)"

begin

lemma join_distr:
  "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  txt \<open>Jacobson I, p.\ 462\<close>
proof -
  have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)" by (simp add: L4)
  also have "... = x \<squnion> ((x \<sqinter> z) \<squnion> (y \<sqinter> z))" by (simp add: L2)
  also have "... = x \<squnion> ((x \<squnion> y) \<sqinter> z)" by (simp add: L1 meet_distr)
  also have "... = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)" by (simp add: L1 L4)
  also have "... = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by (simp add: meet_distr)
  finally show ?thesis .
qed

end

locale dlo = dpo +
  assumes total: "x \<sqsubseteq> y | y \<sqsubseteq> x"

begin

lemma less_total: "x \<sqsubset> y | x = y | y \<sqsubset> x"
  using total
  by (unfold less_def) blast

end


sublocale dlo < dlat
proof
  fix x y
  from total have "is_inf x y (if x \<sqsubseteq> y then x else y)" by (auto simp: is_inf_def)
  then show "\<exists>inf. is_inf x y inf" by blast
next
  fix x y
  from total have "is_sup x y (if x \<sqsubseteq> y then y else x)" by (auto simp: is_sup_def)
  then show "\<exists>sup. is_sup x y sup" by blast
qed

sublocale dlo < ddlat
proof
  fix x y z
  show "x \<sqinter> (y \<squnion> z) = x \<sqinter> y \<squnion> x \<sqinter> z" (is "?l = ?r")
    txt \<open>Jacobson I, p.\ 462\<close>
  proof -
    { assume c: "y \<sqsubseteq> x" "z \<sqsubseteq> x"
      from c have "?l = y \<squnion> z"
        by (metis c (*join_commute*) join_connection2 join_related2 (*meet_commute*) meet_connection meet_related2 total)
      also from c have "... = ?r" by (metis (*c*) (*join_commute*) meet_related2)
      finally have "?l = ?r" . }
    moreover
    { assume c: "x \<sqsubseteq> y | x \<sqsubseteq> z"
      from c have "?l = x"
        by (metis (*antisym*) (*c*) (*circular*) (*join_assoc*)(* join_commute *) join_connection2 (*join_left*) join_related2 meet_connection(* meet_related2*) total trans)
      also from c have "... = ?r"
        by (metis join_commute join_related2 meet_connection meet_related2 total)
      finally have "?l = ?r" . }
    moreover note total
    ultimately show ?thesis by blast
  qed
qed

subsubsection \<open>Total order \<open><=\<close> on \<^typ>\<open>int\<close>\<close>

interpretation int: dpo "(<=) :: [int, int] => bool"
  rewrites "(dpo.less (<=) (x::int) y) = (x < y)"
  txt \<open>We give interpretation for less, but not \<open>is_inf\<close> and \<open>is_sub\<close>.\<close>
proof -
  show "dpo ((<=) :: [int, int] => bool)"
    proof qed auto
  then interpret int: dpo "(<=) :: [int, int] => bool" .
    txt \<open>Gives interpreted version of \<open>less_def\<close> (without condition).\<close>
  show "(dpo.less (<=) (x::int) y) = (x < y)"
    by (unfold int.less_def) auto
qed

thm int.circular
lemma "\<lbrakk> (x::int) \<le> y; y \<le> z; z \<le> x\<rbrakk> \<Longrightarrow> x = y \<and> y = z"
  by simp

thm int.abs_test
lemma "((<) :: [int, int] => bool) = (<)"
  by (rule int.abs_test)

interpretation int: dlat "(<=) :: [int, int] => bool"
  rewrites meet_eq: "dlat.meet (<=) (x::int) y = min x y"
    and join_eq: "dlat.join (<=) (x::int) y = max x y"
proof -
  show "dlat ((<=) :: [int, int] => bool)"
  proof unfold_locales
    fix x y :: int
    show "\<exists>inf. int.is_inf x y inf"
      using int.is_inf_def by fastforce
    show "\<exists>sup. int.is_sup x y sup"
      using int.is_sup_def by fastforce
  qed
  then interpret int: dlat "(<=) :: [int, int] => bool" .
  txt \<open>Interpretation to ease use of definitions, which are
    conditional in general but unconditional after interpretation.\<close>
  show "dlat.meet (<=) (x::int) y = min x y"
    by (smt (verit, best) int.meet_related int.meet_related2)
  show "dlat.join (<=) (x::int) y = max x y"
    by (smt (verit, best) int.join_related int.join_related2)
qed

interpretation int: dlo "(<=) :: [int, int] => bool"
  proof qed arith

text \<open>Interpreted theorems from the locales, involving defined terms.\<close>

thm int.less_def text \<open>from dpo\<close>
thm int.meet_left text \<open>from dlat\<close>
thm int.meet_distr text \<open>from ddlat\<close>
thm int.less_total text \<open>from dlo\<close>


subsubsection \<open>Total order \<open><=\<close> on \<^typ>\<open>nat\<close>\<close>

interpretation nat: dpo "(<=) :: [nat, nat] => bool"
  rewrites "dpo.less (<=) (x::nat) y = (x < y)"
  txt \<open>We give interpretation for less, but not \<open>is_inf\<close> and \<open>is_sub\<close>.\<close>
proof -
  show "dpo ((<=) :: [nat, nat] => bool)"
    proof qed auto
  then interpret nat: dpo "(<=) :: [nat, nat] => bool" .
    txt \<open>Gives interpreted version of \<open>less_def\<close> (without condition).\<close>
  show "dpo.less (<=) (x::nat) y = (x < y)"
    by (simp add: nat.less_def nat_less_le)
qed

interpretation nat: dlat "(<=) :: [nat, nat] => bool"
  rewrites "dlat.meet (<=) (x::nat) y = min x y"
    and "dlat.join (<=) (x::nat) y = max x y"
proof -
  show "dlat ((<=) :: [nat, nat] => bool)"
  proof
    fix x y :: nat
    show "\<exists>inf. nat.is_inf x y inf"
      by (metis nat.is_inf_def nle_le)
    show "\<exists>sup. nat.is_sup x y sup"
      by (metis nat.is_sup_def nle_le)
  qed
  then interpret nat: dlat "(<=) :: [nat, nat] => bool" .
  txt \<open>Interpretation to ease use of definitions, which are
    conditional in general but unconditional after interpretation.\<close>
  show "dlat.meet (<=) (x::nat) y = min x y"
    by (metis min_def nat.meet_connection nat.meet_connection2 nle_le)
  show "dlat.join (<=) (x::nat) y = max x y"
    by (metis max_def nat.join_connection2 nat.join_related2 nle_le)
qed

interpretation nat: dlo "(<=) :: [nat, nat] => bool"
  proof qed arith

text \<open>Interpreted theorems from the locales, involving defined terms.\<close>

thm nat.less_def text \<open>from dpo\<close>
thm nat.meet_left text \<open>from dlat\<close>
thm nat.meet_distr text \<open>from ddlat\<close>
thm nat.less_total text \<open>from ldo\<close>


subsubsection \<open>Lattice \<open>dvd\<close> on \<^typ>\<open>nat\<close>\<close>

interpretation nat_dvd: dpo "(dvd) :: [nat, nat] => bool"
  rewrites "dpo.less (dvd) (x::nat) y = (x dvd y & x ~= y)"
  txt \<open>We give interpretation for less, but not \<open>is_inf\<close> and \<open>is_sub\<close>.\<close>
proof -
  show "dpo ((dvd) :: [nat, nat] => bool)"
    proof qed (auto simp: dvd_def)
  then interpret nat_dvd: dpo "(dvd) :: [nat, nat] => bool" .
    txt \<open>Gives interpreted version of \<open>less_def\<close> (without condition).\<close>
  show "dpo.less (dvd) (x::nat) y = (x dvd y & x ~= y)"
    unfolding nat_dvd.less_def
    by auto
qed

interpretation nat_dvd: dlat "(dvd) :: [nat, nat] => bool"
  rewrites "dlat.meet (dvd) (x::nat) y = gcd x y"
    and "dlat.join (dvd) (x::nat) y = lcm x y"
proof -
  show "dlat ((dvd) :: [nat, nat] => bool)"
  proof
    fix x y :: nat
    show "\<exists>inf. nat_dvd.is_inf x y inf"
      unfolding nat_dvd.is_inf_def
      by (force simp: intro: exI [where x = "gcd x y"])
    show "\<exists>sup. nat_dvd.is_sup x y sup"
      unfolding nat_dvd.is_sup_def
      by (force simp: intro: exI [where x = "lcm x y"])
  qed
  then interpret nat_dvd: dlat "(dvd) :: [nat, nat] => bool" .
  txt \<open>Interpretation to ease use of definitions, which are
    conditional in general but unconditional after interpretation.\<close>
  show "dlat.meet (dvd) (x::nat) y = gcd x y"
    by (meson gcd_unique_nat nat_dvd.meetI)
  show "dlat.join (dvd) (x::nat) y = lcm x y"
    by (simp add: nat_dvd.joinI)
qed

text \<open>Interpreted theorems from the locales, involving defined terms.\<close>

thm nat_dvd.less_def text \<open>from dpo\<close>
lemma "((x::nat) dvd y \<and> x \<noteq> y) = (x dvd y \<and> x \<noteq> y)"
  by simp

thm nat_dvd.meet_left text \<open>from dlat\<close>
lemma "gcd x y dvd (x::nat)"
  by blast


subsection \<open>Group example with defined operations \<open>inv\<close> and \<open>unit\<close>\<close>

subsubsection \<open>Locale declarations and lemmas\<close>

locale Dsemi =
  fixes prod (infixl \<open>**\<close> 65)
  assumes assoc: "(x ** y) ** z = x ** (y ** z)"

locale Dmonoid = Dsemi +
  fixes one
  assumes l_one [simp]: "one ** x = x"
    and r_one [simp]: "x ** one = x"

begin

definition
  inv where "inv x = (THE y. x ** y = one & y ** x = one)"
definition
  unit where "unit x = (\<exists>y. x ** y = one  & y ** x = one)"

lemma inv_unique:
  assumes eq: "y ** x = one" "x ** y' = one"
  shows "y = y'"
proof -
  from eq have "y = y ** (x ** y')" by (simp add: r_one)
  also have "... = (y ** x) ** y'" by (simp add: assoc)
  also from eq have "... = y'" by (simp add: l_one)
  finally show ?thesis .
qed

lemma unit_one [intro, simp]:
  "unit one"
  by (unfold unit_def) auto

lemma unit_l_inv_ex:
  "unit x ==> \<exists>y. y ** x = one"
  by (unfold unit_def) auto

lemma unit_r_inv_ex:
  "unit x ==> \<exists>y. x ** y = one"
  by (unfold unit_def) auto

lemma unit_l_inv:
  "unit x ==> inv x ** x = one"
  by (smt (verit, ccfv_threshold) inv_unique local.inv_def theI' unit_def)

lemma unit_r_inv:
  "unit x ==> x ** inv x = one"
  by (metis inv_unique unit_l_inv unit_r_inv_ex)

lemma unit_inv_unit [intro, simp]:
  "unit x ==> unit (inv x)"
proof -
  assume x: "unit x"
  show "unit (inv x)"
    by (auto simp add: unit_def
      intro: unit_l_inv unit_r_inv x)
qed

lemma unit_l_cancel [simp]:
  "unit x ==> (x ** y = x ** z) = (y = z)"
proof
  assume eq: "x ** y = x ** z"
    and G: "unit x"
  then have "(inv x ** x) ** y = (inv x ** x) ** z"
    by (simp add: assoc)
  with G show "y = z" by (simp add: unit_l_inv)
next
  assume eq: "y = z"
    and G: "unit x"
  then show "x ** y = x ** z" by simp
qed

lemma unit_inv_inv [simp]:
  "unit x ==> inv (inv x) = x"
proof -
  assume x: "unit x"
  then have "inv x ** inv (inv x) = inv x ** x"
    by (simp add: unit_l_inv unit_r_inv)
  with x show ?thesis by simp
qed

lemma inv_inj_on_unit:
  "inj_on inv {x. unit x}"
proof (rule inj_onI, simp)
  fix x y
  assume G: "unit x"  "unit y" and eq: "inv x = inv y"
  then have "inv (inv x) = inv (inv y)" by simp
  with G show "x = y" by simp
qed

lemma unit_inv_comm:
  assumes inv: "x ** y = one"
    and G: "unit x"  "unit y"
  shows "y ** x = one"
proof -
  from G have "x ** y ** x = x ** one" by (auto simp add: inv)
  with G show ?thesis by (simp del: r_one add: assoc)
qed

end


locale Dgrp = Dmonoid +
  assumes unit [intro, simp]: "Dmonoid.unit ((**)) one x"

begin

lemma l_inv_ex [simp]:
  "\<exists>y. y ** x = one"
  using unit_l_inv_ex by simp

lemma r_inv_ex [simp]:
  "\<exists>y. x ** y = one"
  using unit_r_inv_ex by simp

lemma l_inv [simp]:
  "inv x ** x = one"
  using unit_l_inv by simp

lemma l_cancel [simp]:
  "(x ** y = x ** z) = (y = z)"
  using unit_l_inv by simp

lemma r_inv [simp]:
  "x ** inv x = one"
proof -
  have "inv x ** (x ** inv x) = inv x ** one"
    by (simp add: assoc [symmetric] l_inv)
  then show ?thesis by (simp del: r_one)
qed

lemma r_cancel [simp]:
  "(y ** x = z ** x) = (y = z)"
proof
  assume eq: "y ** x = z ** x"
  then have "y ** (x ** inv x) = z ** (x ** inv x)"
    by (simp add: assoc [symmetric] del: r_inv)
  then show "y = z" by simp
qed simp

lemma inv_one [simp]:
  "inv one = one"
proof -
  have "inv one = one ** (inv one)" by (simp del: r_inv)
  moreover have "... = one" by simp
  finally show ?thesis .
qed

lemma inv_inv [simp]:
  "inv (inv x) = x"
  using unit_inv_inv by simp

lemma inv_inj:
  "inj_on inv UNIV"
  using inv_inj_on_unit by simp

lemma inv_mult_group:
  "inv (x ** y) = inv y ** inv x"
proof -
  have "inv (x ** y) ** (x ** y) = (inv y ** inv x) ** (x ** y)"
    by (simp add: assoc l_inv) (simp add: assoc [symmetric])
  then show ?thesis by (simp del: l_inv)
qed

lemma inv_comm:
  "x ** y = one ==> y ** x = one"
  using unit unit_inv_comm by blast

lemma inv_equality: "y ** x = one \<Longrightarrow> inv x = y"
  by (metis assoc r_inv r_one)

end


locale Dhom = prod: Dgrp prod one + sum: Dgrp sum zero
    for prod (infixl \<open>**\<close> 65) and one and sum (infixl \<open>+++\<close> 60) and zero +
  fixes hom
  assumes hom_mult [simp]: "hom (x ** y) = hom x +++ hom y"

begin

lemma hom_one [simp]:
  "hom one = zero"
proof -
  have "hom one +++ zero = hom one +++ hom one"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis by (simp del: sum.r_one)
qed

end


subsubsection \<open>Interpretation of Functions\<close>

interpretation Dfun: Dmonoid "(o)" "id :: 'a => 'a"
  rewrites "Dmonoid.unit (o) id f = bij (f::'a => 'a)"
(*    and "Dmonoid.inv (o) id" = "inv :: ('a => 'a) => ('a => 'a)" *)
proof -
  show "Dmonoid (o) (id :: 'a => 'a)" proof qed (simp_all add: o_assoc)
  note Dmonoid = this
(*
  from this interpret Dmonoid "(o)" "id :: 'a => 'a" .
*)
  have "\<And>y. \<lbrakk>f \<circ> y = id; y \<circ> f = id\<rbrakk> \<Longrightarrow> bij f"
    using o_bij by auto
  moreover have "bij f \<Longrightarrow> \<exists>y. f \<circ> y = id \<and> y \<circ> f = id"
    by (meson bij_betw_def inv_o_cancel surj_iff)
    ultimately
  show "Dmonoid.unit (o) (id :: 'a => 'a) f = bij f"
    by (metis Dmonoid Dmonoid.unit_def)
qed

thm Dmonoid.unit_def Dfun.unit_def

thm Dmonoid.inv_inj_on_unit Dfun.inv_inj_on_unit

lemma unit_id: "(f :: unit => unit) = id"
  by rule simp

interpretation Dfun: Dgrp "(o)" "id :: unit => unit"
  rewrites "Dmonoid.inv (o) id f = inv (f :: unit => unit)"
proof -
  have "Dmonoid (o) (id :: 'a => 'a)" ..
  note Dmonoid = this

  show "Dgrp (o) (id :: unit => unit)"
  proof
    fix x :: "unit \<Rightarrow> unit"
    show "Dmonoid.unit (\<circ>) id x"
      by (simp add: Dmonoid Dmonoid.unit_def unit_id)
  qed
  show "Dmonoid.inv (o) id f = inv (f :: unit \<Rightarrow> unit)"
    unfolding Dmonoid.inv_def [OF Dmonoid]
    by force
qed

thm Dfun.unit_l_inv Dfun.l_inv

thm Dfun.inv_equality
thm Dfun.inv_equality

end
