(*  Title:      HOL/Library/While_Combinator.thy
    Author:     Tobias Nipkow
    Author:     Alexander Krauss
*)

section {* A general ``while'' combinator *}

theory While_Combinator
imports Main
begin

subsection {* Partial version *}

definition while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a option" where
"while_option b c s = (if (\<exists>k. ~ b ((c ^^ k) s))
   then Some ((c ^^ (LEAST k. ~ b ((c ^^ k) s))) s)
   else None)"

theorem while_option_unfold[code]:
"while_option b c s = (if b s then while_option b c (c s) else Some s)"
proof cases
  assume "b s"
  show ?thesis
  proof (cases "\<exists>k. ~ b ((c ^^ k) s)")
    case True
    then obtain k where 1: "~ b ((c ^^ k) s)" ..
    with `b s` obtain l where "k = Suc l" by (cases k) auto
    with 1 have "~ b ((c ^^ l) (c s))" by (auto simp: funpow_swap1)
    then have 2: "\<exists>l. ~ b ((c ^^ l) (c s))" ..
    from 1
    have "(LEAST k. ~ b ((c ^^ k) s)) = Suc (LEAST l. ~ b ((c ^^ Suc l) s))"
      by (rule Least_Suc) (simp add: `b s`)
    also have "... = Suc (LEAST l. ~ b ((c ^^ l) (c s)))"
      by (simp add: funpow_swap1)
    finally
    show ?thesis 
      using True 2 `b s` by (simp add: funpow_swap1 while_option_def)
  next
    case False
    then have "~ (\<exists>l. ~ b ((c ^^ Suc l) s))" by blast
    then have "~ (\<exists>l. ~ b ((c ^^ l) (c s)))"
      by (simp add: funpow_swap1)
    with False  `b s` show ?thesis by (simp add: while_option_def)
  qed
next
  assume [simp]: "~ b s"
  have least: "(LEAST k. ~ b ((c ^^ k) s)) = 0"
    by (rule Least_equality) auto
  moreover 
  have "\<exists>k. ~ b ((c ^^ k) s)" by (rule exI[of _ "0::nat"]) auto
  ultimately show ?thesis unfolding while_option_def by auto 
qed

lemma while_option_stop2:
 "while_option b c s = Some t \<Longrightarrow> EX k. t = (c^^k) s \<and> \<not> b t"
apply(simp add: while_option_def split: if_splits)
by (metis (lifting) LeastI_ex)

lemma while_option_stop: "while_option b c s = Some t \<Longrightarrow> ~ b t"
by(metis while_option_stop2)

theorem while_option_rule:
assumes step: "!!s. P s ==> b s ==> P (c s)"
and result: "while_option b c s = Some t"
and init: "P s"
shows "P t"
proof -
  def k == "LEAST k. ~ b ((c ^^ k) s)"
  from assms have t: "t = (c ^^ k) s"
    by (simp add: while_option_def k_def split: if_splits)    
  have 1: "ALL i<k. b ((c ^^ i) s)"
    by (auto simp: k_def dest: not_less_Least)

  { fix i assume "i <= k" then have "P ((c ^^ i) s)"
      by (induct i) (auto simp: init step 1) }
  thus "P t" by (auto simp: t)
qed

lemma funpow_commute: 
  "\<lbrakk>\<forall>k' < k. f (c ((c^^k') s)) = c' (f ((c^^k') s))\<rbrakk> \<Longrightarrow> f ((c^^k) s) = (c'^^k) (f s)"
by (induct k arbitrary: s) auto

lemma while_option_commute_invariant:
assumes Invariant: "\<And>s. P s \<Longrightarrow> b s \<Longrightarrow> P (c s)"
assumes TestCommute: "\<And>s. P s \<Longrightarrow> b s = b' (f s)"
assumes BodyCommute: "\<And>s. P s \<Longrightarrow> b s \<Longrightarrow> f (c s) = c' (f s)"
assumes Initial: "P s"
shows "map_option f (while_option b c s) = while_option b' c' (f s)"
unfolding while_option_def
proof (rule trans[OF if_distrib if_cong], safe, unfold option.inject)
  fix k
  assume "\<not> b ((c ^^ k) s)"
  with Initial show "\<exists>k. \<not> b' ((c' ^^ k) (f s))"
  proof (induction k arbitrary: s)
    case 0 thus ?case by (auto simp: TestCommute intro: exI[of _ 0])
  next
    case (Suc k) thus ?case
    proof (cases "b s")
      assume "b s"
      with Suc.IH[of "c s"] Suc.prems show ?thesis
        by (metis BodyCommute Invariant comp_apply funpow.simps(2) funpow_swap1)
    next
      assume "\<not> b s"
      with Suc show ?thesis by (auto simp: TestCommute intro: exI [of _ 0])
    qed
  qed
next
  fix k
  assume "\<not> b' ((c' ^^ k) (f s))"
  with Initial show "\<exists>k. \<not> b ((c ^^ k) s)"
  proof (induction k arbitrary: s)
    case 0 thus ?case by (auto simp: TestCommute intro: exI[of _ 0])
  next
    case (Suc k) thus ?case
    proof (cases "b s")
       assume "b s"
      with Suc.IH[of "c s"] Suc.prems show ?thesis
        by (metis BodyCommute Invariant comp_apply funpow.simps(2) funpow_swap1)
    next
      assume "\<not> b s"
      with Suc show ?thesis by (auto simp: TestCommute intro: exI [of _ 0])
    qed
  qed
next
  fix k
  assume k: "\<not> b' ((c' ^^ k) (f s))"
  have *: "(LEAST k. \<not> b' ((c' ^^ k) (f s))) = (LEAST k. \<not> b ((c ^^ k) s))"
          (is "?k' = ?k")
  proof (cases ?k')
    case 0
    have "\<not> b' ((c' ^^ 0) (f s))"
      unfolding 0[symmetric] by (rule LeastI[of _ k]) (rule k)
    hence "\<not> b s" by (auto simp: TestCommute Initial)
    hence "?k = 0" by (intro Least_equality) auto
    with 0 show ?thesis by auto
  next
    case (Suc k')
    have "\<not> b' ((c' ^^ Suc k') (f s))"
      unfolding Suc[symmetric] by (rule LeastI) (rule k)
    moreover
    { fix k assume "k \<le> k'"
      hence "k < ?k'" unfolding Suc by simp
      hence "b' ((c' ^^ k) (f s))" by (rule iffD1[OF not_not, OF not_less_Least])
    }
    note b' = this
    { fix k assume "k \<le> k'"
      hence "f ((c ^^ k) s) = (c' ^^ k) (f s)"
      and "b ((c ^^ k) s) = b' ((c' ^^ k) (f s))"
      and "P ((c ^^ k) s)"
        by (induct k) (auto simp: b' assms)
      with `k \<le> k'`
      have "b ((c ^^ k) s)"
      and "f ((c ^^ k) s) = (c' ^^ k) (f s)"
      and "P ((c ^^ k) s)"
        by (auto simp: b')
    }
    note b = this(1) and body = this(2) and inv = this(3)
    hence k': "f ((c ^^ k') s) = (c' ^^ k') (f s)" by auto
    ultimately show ?thesis unfolding Suc using b
    proof (intro Least_equality[symmetric])
      case goal1
      hence Test: "\<not> b' (f ((c ^^ Suc k') s))"
        by (auto simp: BodyCommute inv b)
      have "P ((c ^^ Suc k') s)" by (auto simp: Invariant inv b)
      with Test show ?case by (auto simp: TestCommute)
    next
      case goal2 thus ?case by (metis not_less_eq_eq)
    qed
  qed
  have "f ((c ^^ ?k) s) = (c' ^^ ?k') (f s)" unfolding *
  proof (rule funpow_commute, clarify)
    fix k assume "k < ?k"
    hence TestTrue: "b ((c ^^ k) s)" by (auto dest: not_less_Least)
    from `k < ?k` have "P ((c ^^ k) s)"
    proof (induct k)
      case 0 thus ?case by (auto simp: assms)
    next
      case (Suc h)
      hence "P ((c ^^ h) s)" by auto
      with Suc show ?case
        by (auto, metis (lifting, no_types) Invariant Suc_lessD not_less_Least)
    qed
    with TestTrue show "f (c ((c ^^ k) s)) = c' (f ((c ^^ k) s))"
      by (metis BodyCommute)
  qed
  thus "\<exists>z. (c ^^ ?k) s = z \<and> f z = (c' ^^ ?k') (f s)" by blast
qed

lemma while_option_commute:
  assumes "\<And>s. b s = b' (f s)" "\<And>s. \<lbrakk>b s\<rbrakk> \<Longrightarrow> f (c s) = c' (f s)" 
  shows "map_option f (while_option b c s) = while_option b' c' (f s)"
by(rule while_option_commute_invariant[where P = "\<lambda>_. True"])
  (auto simp add: assms)

subsection {* Total version *}

definition while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where "while b c s = the (while_option b c s)"

lemma while_unfold [code]:
  "while b c s = (if b s then while b c (c s) else s)"
unfolding while_def by (subst while_option_unfold) simp

lemma def_while_unfold:
  assumes fdef: "f == while test do"
  shows "f x = (if test x then f(do x) else x)"
unfolding fdef by (fact while_unfold)


text {*
 The proof rule for @{term while}, where @{term P} is the invariant.
*}

theorem while_rule_lemma:
  assumes invariant: "!!s. P s ==> b s ==> P (c s)"
    and terminate: "!!s. P s ==> \<not> b s ==> Q s"
    and wf: "wf {(t, s). P s \<and> b s \<and> t = c s}"
  shows "P s \<Longrightarrow> Q (while b c s)"
  using wf
  apply (induct s)
  apply simp
  apply (subst while_unfold)
  apply (simp add: invariant terminate)
  done

theorem while_rule:
  "[| P s;
      !!s. [| P s; b s  |] ==> P (c s);
      !!s. [| P s; \<not> b s  |] ==> Q s;
      wf r;
      !!s. [| P s; b s  |] ==> (c s, s) \<in> r |] ==>
   Q (while b c s)"
  apply (rule while_rule_lemma)
     prefer 4 apply assumption
    apply blast
   apply blast
  apply (erule wf_subset)
  apply blast
  done

text{* Proving termination: *}

theorem wf_while_option_Some:
  assumes "wf {(t, s). (P s \<and> b s) \<and> t = c s}"
  and "!!s. P s \<Longrightarrow> b s \<Longrightarrow> P(c s)" and "P s"
  shows "EX t. while_option b c s = Some t"
using assms(1,3)
proof (induction s)
  case less thus ?case using assms(2)
    by (subst while_option_unfold) simp
qed

lemma wf_rel_while_option_Some:
assumes wf: "wf R"
assumes smaller: "\<And>s. P s \<and> b s \<Longrightarrow> (c s, s) \<in> R"
assumes inv: "\<And>s. P s \<and> b s \<Longrightarrow> P(c s)"
assumes init: "P s"
shows "\<exists>t. while_option b c s = Some t"
proof -
 from smaller have "{(t,s). P s \<and> b s \<and> t = c s} \<subseteq> R" by auto
 with wf have "wf {(t,s). P s \<and> b s \<and> t = c s}" by (auto simp: wf_subset)
 with inv init show ?thesis by (auto simp: wf_while_option_Some)
qed

theorem measure_while_option_Some: fixes f :: "'s \<Rightarrow> nat"
shows "(!!s. P s \<Longrightarrow> b s \<Longrightarrow> P(c s) \<and> f(c s) < f s)
  \<Longrightarrow> P s \<Longrightarrow> EX t. while_option b c s = Some t"
by(blast intro: wf_while_option_Some[OF wf_if_measure, of P b f])

text{* Kleene iteration starting from the empty set and assuming some finite
bounding set: *}

lemma while_option_finite_subset_Some: fixes C :: "'a set"
  assumes "mono f" and "!!X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C"
  shows "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f {} = Some P"
proof(rule measure_while_option_Some[where
    f= "%A::'a set. card C - card A" and P= "%A. A \<subseteq> C \<and> A \<subseteq> f A" and s= "{}"])
  fix A assume A: "A \<subseteq> C \<and> A \<subseteq> f A" "f A \<noteq> A"
  show "(f A \<subseteq> C \<and> f A \<subseteq> f (f A)) \<and> card C - card (f A) < card C - card A"
    (is "?L \<and> ?R")
  proof
    show ?L by(metis A(1) assms(2) monoD[OF `mono f`])
    show ?R by (metis A assms(2,3) card_seteq diff_less_mono2 equalityI linorder_le_less_linear rev_finite_subset)
  qed
qed simp

lemma lfp_the_while_option:
  assumes "mono f" and "!!X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C"
  shows "lfp f = the(while_option (\<lambda>A. f A \<noteq> A) f {})"
proof-
  obtain P where "while_option (\<lambda>A. f A \<noteq> A) f {} = Some P"
    using while_option_finite_subset_Some[OF assms] by blast
  with while_option_stop2[OF this] lfp_Kleene_iter[OF assms(1)]
  show ?thesis by auto
qed

lemma lfp_while:
  assumes "mono f" and "!!X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C"
  shows "lfp f = while (\<lambda>A. f A \<noteq> A) f {}"
unfolding while_def using assms by (rule lfp_the_while_option) blast


text{* Computing the reflexive, transitive closure by iterating a successor
function. Stops when an element is found that dos not satisfy the test.

More refined (and hence more efficient) versions can be found in ITP 2011 paper
by Nipkow (the theories are in the AFP entry Flyspeck by Nipkow)
and the AFP article Executable Transitive Closures by René Thiemann. *}

context
fixes p :: "'a \<Rightarrow> bool"
and f :: "'a \<Rightarrow> 'a list"
and x :: 'a
begin

fun rtrancl_while_test :: "'a list \<times> 'a set \<Rightarrow> bool"
where "rtrancl_while_test (ws,_) = (ws \<noteq> [] \<and> p(hd ws))"

fun rtrancl_while_step :: "'a list \<times> 'a set \<Rightarrow> 'a list \<times> 'a set"
where "rtrancl_while_step (ws, Z) =
  (let x = hd ws; new = remdups (filter (\<lambda>y. y \<notin> Z) (f x))
  in (new @ tl ws, set new \<union> Z))"

definition rtrancl_while :: "('a list * 'a set) option"
where "rtrancl_while = while_option rtrancl_while_test rtrancl_while_step ([x],{x})"

fun rtrancl_while_invariant :: "'a list \<times> 'a set \<Rightarrow> bool"
where "rtrancl_while_invariant (ws, Z) =
   (x \<in> Z \<and> set ws \<subseteq> Z \<and> distinct ws \<and> {(x,y). y \<in> set(f x)} `` (Z - set ws) \<subseteq> Z \<and>
    Z \<subseteq> {(x,y). y \<in> set(f x)}^* `` {x} \<and> (\<forall>z\<in>Z - set ws. p z))"

lemma rtrancl_while_invariant: 
  assumes inv: "rtrancl_while_invariant st" and test: "rtrancl_while_test st"
  shows   "rtrancl_while_invariant (rtrancl_while_step st)"
proof (cases st)
  fix ws Z assume st: "st = (ws, Z)"
  with test obtain h t where "ws = h # t" "p h" by (cases ws) auto
  with inv st show ?thesis by (auto intro: rtrancl.rtrancl_into_rtrancl)
qed

lemma rtrancl_while_Some: assumes "rtrancl_while = Some(ws,Z)"
shows "if ws = []
       then Z = {(x,y). y \<in> set(f x)}^* `` {x} \<and> (\<forall>z\<in>Z. p z)
       else \<not>p(hd ws) \<and> hd ws \<in> {(x,y). y \<in> set(f x)}^* `` {x}"
proof -
  have "rtrancl_while_invariant ([x],{x})" by simp
  with rtrancl_while_invariant have I: "rtrancl_while_invariant (ws,Z)"
    by (rule while_option_rule[OF _ assms[unfolded rtrancl_while_def]])
  { assume "ws = []"
    hence ?thesis using I
      by (auto simp del:Image_Collect_split dest: Image_closed_trancl)
  } moreover
  { assume "ws \<noteq> []"
    hence ?thesis using I while_option_stop[OF assms[unfolded rtrancl_while_def]]
      by (simp add: subset_iff)
  }
  ultimately show ?thesis by simp
qed

lemma rtrancl_while_finite_Some:
  assumes "finite ({(x, y). y \<in> set (f x)}\<^sup>* `` {x})" (is "finite ?Cl")
  shows "\<exists>y. rtrancl_while = Some y"
proof -
  let ?R = "(\<lambda>(_, Z). card (?Cl - Z)) <*mlex*> (\<lambda>(ws, _). length ws) <*mlex*> {}"
  have "wf ?R" by (blast intro: wf_mlex)
  then show ?thesis unfolding rtrancl_while_def
  proof (rule wf_rel_while_option_Some[of ?R rtrancl_while_invariant])
    fix st assume *: "rtrancl_while_invariant st \<and> rtrancl_while_test st"
    hence I: "rtrancl_while_invariant (rtrancl_while_step st)"
      by (blast intro: rtrancl_while_invariant)
    show "(rtrancl_while_step st, st) \<in> ?R"
    proof (cases st)
      fix ws Z let ?ws = "fst (rtrancl_while_step st)" and ?Z = "snd (rtrancl_while_step st)"
      assume st: "st = (ws, Z)"
      with * obtain h t where ws: "ws = h # t" "p h" by (cases ws) auto
      { assume "remdups (filter (\<lambda>y. y \<notin> Z) (f h)) \<noteq> []"
        then obtain z where "z \<in> set (remdups (filter (\<lambda>y. y \<notin> Z) (f h)))" by fastforce
        with st ws I have "Z \<subset> ?Z" "Z \<subseteq> ?Cl" "?Z \<subseteq> ?Cl" by auto
        with assms have "card (?Cl - ?Z) < card (?Cl - Z)" by (blast intro: psubset_card_mono)
        with st ws have ?thesis unfolding mlex_prod_def by simp
      }
      moreover
      { assume "remdups (filter (\<lambda>y. y \<notin> Z) (f h)) = []"
        with st ws have "?Z = Z" "?ws = t"  by (auto simp: filter_empty_conv)
        with st ws have ?thesis unfolding mlex_prod_def by simp
      }
      ultimately show ?thesis by blast
    qed
  qed (simp_all add: rtrancl_while_invariant)
qed

end

hide_const (open) rtrancl_while_test rtrancl_while_step rtrancl_while_invariant
hide_fact (open) rtrancl_while_invariant

end
