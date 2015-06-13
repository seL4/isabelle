(*  Title:      HOL/Isar_Examples/Structured_Statements.thy
    Author:     Makarius
*)

section \<open>Structured statements within Isar proofs\<close>

theory Structured_Statements
imports Main
begin

notepad
begin

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

end