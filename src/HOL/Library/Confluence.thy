theory Confluence imports
  Main
begin

section \<open>Confluence\<close>

definition semiconfluentp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "semiconfluentp r \<longleftrightarrow> r\<inverse>\<inverse> OO r\<^sup>*\<^sup>* \<le> r\<^sup>*\<^sup>* OO r\<inverse>\<inverse>\<^sup>*\<^sup>*"

definition confluentp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "confluentp r \<longleftrightarrow> r\<inverse>\<inverse>\<^sup>*\<^sup>* OO r\<^sup>*\<^sup>* \<le> r\<^sup>*\<^sup>* OO r\<inverse>\<inverse>\<^sup>*\<^sup>*"

definition strong_confluentp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "strong_confluentp r \<longleftrightarrow> r\<inverse>\<inverse> OO r \<le> r\<^sup>*\<^sup>* OO (r\<inverse>\<inverse>)\<^sup>=\<^sup>="

lemma semiconfluentpI [intro?]:
  "semiconfluentp r" if "\<And>x y z. \<lbrakk> r x y; r\<^sup>*\<^sup>* x z \<rbrakk> \<Longrightarrow> \<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u"
  using that unfolding semiconfluentp_def rtranclp_conversep by blast

lemma semiconfluentpD: "\<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u" if "semiconfluentp r" "r x y" "r\<^sup>*\<^sup>* x z"
  using that unfolding semiconfluentp_def rtranclp_conversep by blast

lemma confluentpI:
  "confluentp r" if "\<And>x y z. \<lbrakk> r\<^sup>*\<^sup>* x y; r\<^sup>*\<^sup>* x z \<rbrakk> \<Longrightarrow> \<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u"
  using that unfolding confluentp_def rtranclp_conversep by blast

lemma confluentpD: "\<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u" if "confluentp r" "r\<^sup>*\<^sup>* x y" "r\<^sup>*\<^sup>* x z"
  using that unfolding confluentp_def rtranclp_conversep by blast

lemma strong_confluentpI [intro?]:
  "strong_confluentp r" if "\<And>x y z. \<lbrakk> r x y; r x z \<rbrakk> \<Longrightarrow> \<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>=\<^sup>= z u"
  using that unfolding strong_confluentp_def by blast

lemma strong_confluentpD: "\<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>=\<^sup>= z u" if "strong_confluentp r" "r x y" "r x z"
  using that unfolding strong_confluentp_def by blast

lemma semiconfluentp_imp_confluentp: "confluentp r" if r: "semiconfluentp r"
proof(rule confluentpI)
  show "\<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u" if "r\<^sup>*\<^sup>* x y" "r\<^sup>*\<^sup>* x z" for x y z
    using that(2,1)
    by(induction arbitrary: y rule: converse_rtranclp_induct)
      (blast intro: rtranclp_trans dest:  r[THEN semiconfluentpD])+
qed

lemma confluentp_imp_semiconfluentp: "semiconfluentp r" if "confluentp r"
  using that by(auto intro!: semiconfluentpI dest: confluentpD[OF that])

lemma confluentp_eq_semiconfluentp: "confluentp r \<longleftrightarrow> semiconfluentp r"
  by(blast intro: semiconfluentp_imp_confluentp confluentp_imp_semiconfluentp)

lemma confluentp_conv_strong_confluentp_rtranclp:
  "confluentp r \<longleftrightarrow> strong_confluentp (r\<^sup>*\<^sup>*)"
  by(auto simp add: confluentp_def strong_confluentp_def rtranclp_conversep)

lemma strong_confluentp_into_semiconfluentp:
  "semiconfluentp r" if r: "strong_confluentp r"
proof
  show "\<exists>u. r\<^sup>*\<^sup>* y u \<and> r\<^sup>*\<^sup>* z u" if "r x y" "r\<^sup>*\<^sup>* x z" for x y z
    using that(2,1)
    apply(induction arbitrary: y rule: converse_rtranclp_induct)
    subgoal by blast
    subgoal for a b c
      by (drule (1) strong_confluentpD[OF r, of a c])(auto 10 0 intro: rtranclp_trans)
    done
qed

lemma strong_confluentp_imp_confluentp: "confluentp r" if "strong_confluentp r"
  unfolding confluentp_eq_semiconfluentp using that by(rule strong_confluentp_into_semiconfluentp)

lemma semiconfluentp_equivclp: "equivclp r = r\<^sup>*\<^sup>* OO r\<inverse>\<inverse>\<^sup>*\<^sup>*" if r: "semiconfluentp r"
proof(rule antisym[rotated] r_OO_conversep_into_equivclp predicate2I)+
  show "(r\<^sup>*\<^sup>* OO r\<inverse>\<inverse>\<^sup>*\<^sup>*) x y" if "equivclp r x y" for x y using that unfolding equivclp_def rtranclp_conversep
    by(induction rule: converse_rtranclp_induct)
      (blast elim!: symclpE intro: converse_rtranclp_into_rtranclp rtranclp_trans dest: semiconfluentpD[OF r])+
qed

end