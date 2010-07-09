(*  Title:      HOL/Library/While_Combinator.thy
    Author:     Tobias Nipkow
    Author:     Alexander Krauss
    Copyright   2000 TU Muenchen
*)

header {* A general ``while'' combinator *}

theory While_Combinator
imports Main
begin

subsection {* Option result *}

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

lemma while_option_stop:
assumes "while_option b c s = Some t"
shows "~ b t"
proof -
  from assms have ex: "\<exists>k. ~ b ((c ^^ k) s)"
  and t: "t = (c ^^ (LEAST k. ~ b ((c ^^ k) s))) s"
    by (auto simp: while_option_def split: if_splits)
  from LeastI_ex[OF ex]
  show "~ b t" unfolding t .
qed

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


subsection {* Totalized version *}

definition while :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where "while b c s = the (while_option b c s)"

lemma while_unfold:
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

text {*
 \medskip An application: computation of the @{term lfp} on finite
 sets via iteration.
*}

theorem lfp_conv_while:
  "[| mono f; finite U; f U = U |] ==>
    lfp f = fst (while (\<lambda>(A, fA). A \<noteq> fA) (\<lambda>(A, fA). (fA, f fA)) ({}, f {}))"
apply (rule_tac P = "\<lambda>(A, B). (A \<subseteq> U \<and> B = f A \<and> A \<subseteq> B \<and> B \<subseteq> lfp f)" and
                r = "((Pow U \<times> UNIV) \<times> (Pow U \<times> UNIV)) \<inter>
                     inv_image finite_psubset (op - U o fst)" in while_rule)
   apply (subst lfp_unfold)
    apply assumption
   apply (simp add: monoD)
  apply (subst lfp_unfold)
   apply assumption
  apply clarsimp
  apply (blast dest: monoD)
 apply (fastsimp intro!: lfp_lowerbound)
 apply (blast intro: wf_finite_psubset Int_lower2 [THEN [2] wf_subset])
apply (clarsimp simp add: finite_psubset_def order_less_le)
apply (blast intro!: finite_Diff dest: monoD)
done


subsection {* Example *}

text{* Cannot use @{thm[source]set_eq_subset} because it leads to
looping because the antisymmetry simproc turns the subset relationship
back into equality. *}

theorem "P (lfp (\<lambda>N::int set. {0} \<union> {(n + 2) mod 6 | n. n \<in> N})) =
  P {0, 4, 2}"
proof -
  have seteq: "!!A B. (A = B) = ((!a : A. a:B) & (!b:B. b:A))"
    by blast
  have aux: "!!f A B. {f n | n. A n \<or> B n} = {f n | n. A n} \<union> {f n | n. B n}"
    apply blast
    done
  show ?thesis
    apply (subst lfp_conv_while [where ?U = "{0, 1, 2, 3, 4, 5}"])
       apply (rule monoI)
      apply blast
     apply simp
    apply (simp add: aux set_eq_subset)
    txt {* The fixpoint computation is performed purely by rewriting: *}
    apply (simp add: while_unfold aux seteq del: subset_empty)
    done
qed

end
