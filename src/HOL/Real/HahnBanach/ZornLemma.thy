(*  Title:      HOL/Real/HahnBanach/ZornLemma.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Zorn's Lemma *}

theory ZornLemma = Aux + Zorn:

text {*
  Zorn's Lemmas states: if every linear ordered subset of an ordered
  set @{text S} has an upper bound in @{text S}, then there exists a
  maximal element in @{text S}.  In our application, @{text S} is a
  set of sets ordered by set inclusion. Since the union of a chain of
  sets is an upper bound for all elements of the chain, the conditions
  of Zorn's lemma can be modified: if @{text S} is non-empty, it
  suffices to show that for every non-empty chain @{text c} in @{text
  S} the union of @{text c} also lies in @{text S}.
*}

theorem Zorn's_Lemma:
  assumes r: "\<And>c. c \<in> chain S \<Longrightarrow> \<exists>x. x \<in> c \<Longrightarrow> \<Union>c \<in> S"
    and aS: "a \<in> S"
  shows "\<exists>y \<in> S. \<forall>z \<in> S. y \<subseteq> z \<longrightarrow> y = z"
proof (rule Zorn_Lemma2)
  txt_raw {* \footnote{See
  \url{http://isabelle.in.tum.de/library/HOL/HOL-Real/Zorn.html}} \isanewline *}
  show "\<forall>c \<in> chain S. \<exists>y \<in> S. \<forall>z \<in> c. z \<subseteq> y"
  proof
    fix c assume "c \<in> chain S"
    show "\<exists>y \<in> S. \<forall>z \<in> c. z \<subseteq> y"
    proof cases

      txt {* If @{text c} is an empty chain, then every element in
      @{text S} is an upper bound of @{text c}. *}

      assume "c = {}"
      with aS show ?thesis by fast

      txt {* If @{text c} is non-empty, then @{text "\<Union>c"} is an upper
      bound of @{text c}, lying in @{text S}. *}

    next
      assume c: "c \<noteq> {}"
      show ?thesis
      proof
        show "\<forall>z \<in> c. z \<subseteq> \<Union>c" by fast
        show "\<Union>c \<in> S"
        proof (rule r)
          from c show "\<exists>x. x \<in> c" by fast
        qed
      qed
    qed
  qed
qed

end
