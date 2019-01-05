(*  Title:      HOL/Isar_Examples/Structured_Statements.thy
    Author:     Makarius
*)

section \<open>Structured statements within Isar proofs\<close>

theory Structured_Statements
  imports Main
begin

subsection \<open>Introduction steps\<close>

notepad
begin
  fix A B :: bool
  fix P :: "'a \<Rightarrow> bool"

  have "A \<longrightarrow> B"
  proof
    show B if A using that \<proof>
  qed

  have "\<not> A"
  proof
    show False if A using that \<proof>
  qed

  have "\<forall>x. P x"
  proof
    show "P x" for x \<proof>
  qed
end


subsection \<open>If-and-only-if\<close>

notepad
begin
  fix A B :: bool

  have "A \<longleftrightarrow> B"
  proof
    show B if A \<proof>
    show A if B \<proof>
  qed
next
  fix A B :: bool

  have iff_comm: "(A \<and> B) \<longleftrightarrow> (B \<and> A)"
  proof
    show "B \<and> A" if "A \<and> B"
    proof
      show B using that ..
      show A using that ..
    qed
    show "A \<and> B" if "B \<and> A"
    proof
      show A using that ..
      show B using that ..
    qed
  qed

  text \<open>Alternative proof, avoiding redundant copy of symmetric argument.\<close>
  have iff_comm: "(A \<and> B) \<longleftrightarrow> (B \<and> A)"
  proof
    show "B \<and> A" if "A \<and> B" for A B
    proof
      show B using that ..
      show A using that ..
    qed
    then show "A \<and> B" if "B \<and> A"
      by this (rule that)
  qed
end


subsection \<open>Elimination and cases\<close>

notepad
begin
  fix A B C D :: bool
  assume *: "A \<or> B \<or> C \<or> D"

  consider (a) A | (b) B | (c) C | (d) D
    using * by blast
  then have something
  proof cases
    case a  thm \<open>A\<close>
    then show ?thesis \<proof>
  next
    case b  thm \<open>B\<close>
    then show ?thesis \<proof>
  next
    case c  thm \<open>C\<close>
    then show ?thesis \<proof>
  next
    case d  thm \<open>D\<close>
    then show ?thesis \<proof>
  qed
next
  fix A :: "'a \<Rightarrow> bool"
  fix B :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  assume *: "(\<exists>x. A x) \<or> (\<exists>y z. B y z)"

  consider (a) x where "A x" | (b) y z where "B y z"
    using * by blast
  then have something
  proof cases
    case a  thm \<open>A x\<close>
    then show ?thesis \<proof>
  next
    case b  thm \<open>B y z\<close>
    then show ?thesis \<proof>
  qed
end


subsection \<open>Induction\<close>

notepad
begin
  fix P :: "nat \<Rightarrow> bool"
  fix n :: nat

  have "P n"
  proof (induct n)
    show "P 0" \<proof>
    show "P (Suc n)" if "P n" for n  thm \<open>P n\<close>
      using that \<proof>
  qed
end


subsection \<open>Suffices-to-show\<close>

notepad
begin
  fix A B C
  assume r: "A \<Longrightarrow> B \<Longrightarrow> C"

  have C
  proof -
    show ?thesis when A (is ?A) and B (is ?B)
      using that by (rule r)
    show ?A \<proof>
    show ?B \<proof>
  qed
next
  fix a :: 'a
  fix A :: "'a \<Rightarrow> bool"
  fix C

  have C
  proof -
    show ?thesis when "A x" (is ?A) for x :: 'a  \<comment> \<open>abstract \<^term>\<open>x\<close>\<close>
      using that \<proof>
    show "?A a"  \<comment> \<open>concrete \<^term>\<open>a\<close>\<close>
      \<proof>
  qed
end

end
