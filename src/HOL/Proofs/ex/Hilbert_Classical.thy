(*  Title:      HOL/Proofs/ex/Hilbert_Classical.thy
    Author:     Stefan Berghofer
    Author:     Makarius Wenzel
*)

section \<open>Hilbert's choice and classical logic\<close>

theory Hilbert_Classical
  imports Main
begin

text \<open>
  Derivation of the classical law of tertium-non-datur by means of
  Hilbert's choice operator (due to M. J. Beeson and J. Harrison).
\<close>


subsection \<open>Proof text\<close>

theorem tertium_non_datur: "A \<or> \<not> A"
proof -
  let ?P = "\<lambda>x. (x \<longleftrightarrow> False) \<or> (x \<longleftrightarrow> True) \<and> A"
  let ?Q = "\<lambda>x. (x \<longleftrightarrow> False) \<and> A \<or> (x \<longleftrightarrow> True)"

  have a: "?P (Eps ?P)"
  proof (rule someI)
    show "?P False" using refl ..
  qed
  have b: "?Q (Eps ?Q)"
  proof (rule someI)
    show "?Q True" using refl ..
  qed

  from a show ?thesis
  proof
    assume "(Eps ?P \<longleftrightarrow> True) \<and> A"
    then have A ..
    then show ?thesis ..
  next
    assume P: "Eps ?P \<longleftrightarrow> False"
    from b show ?thesis
    proof
      assume "(Eps ?Q \<longleftrightarrow> False) \<and> A"
      then have A ..
      then show ?thesis ..
    next
      assume Q: "Eps ?Q \<longleftrightarrow> True"
      have neq: "?P \<noteq> ?Q"
      proof
        assume "?P = ?Q"
        then have "Eps ?P \<longleftrightarrow> Eps ?Q" by (rule arg_cong)
        also note P
        also note Q
        finally show False by (rule False_neq_True)
      qed
      have "\<not> A"
      proof
        assume A
        have "?P = ?Q"
        proof (rule ext)
          show "?P x \<longleftrightarrow> ?Q x" for x
          proof
            assume "?P x"
            then show "?Q x"
            proof
              assume "x \<longleftrightarrow> False"
              from this and \<open>A\<close> have "(x \<longleftrightarrow> False) \<and> A" ..
              then show ?thesis ..
            next
              assume "(x \<longleftrightarrow> True) \<and> A"
              then have "x \<longleftrightarrow> True" ..
              then show ?thesis ..
            qed
          next
            assume "?Q x"
            then show "?P x"
            proof
              assume "(x \<longleftrightarrow> False) \<and> A"
              then have "x \<longleftrightarrow> False" ..
              then show ?thesis ..
            next
              assume "x \<longleftrightarrow> True"
              from this and \<open>A\<close> have "(x \<longleftrightarrow> True) \<and> A" ..
              then show ?thesis ..
            qed
          qed
        qed
        with neq show False by contradiction
      qed
      then show ?thesis ..
    qed
  qed
qed


subsection \<open>Proof term of text\<close>

prf tertium_non_datur


subsection \<open>Proof script\<close>

theorem tertium_non_datur': "A \<or> \<not> A"
  apply (subgoal_tac
      "(((SOME x. x = False \<or> x = True \<and> A) = False) \<or>
      ((SOME x. x = False \<or> x = True \<and> A) = True) \<and> A) \<and>
      (((SOME x. x = False \<and> A \<or> x = True) = False) \<and> A \<or>
      ((SOME x. x = False \<and> A \<or> x = True) = True))")
   prefer 2
   apply (rule conjI)
    apply (rule someI)
    apply (rule disjI1)
    apply (rule refl)
   apply (rule someI)
   apply (rule disjI2)
   apply (rule refl)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule disjE)
    apply (erule conjE)
    apply (erule disjI1)
   prefer 2
   apply (erule conjE)
   apply (erule disjI1)
  apply (subgoal_tac
      "(\<lambda>x. (x = False) \<or> (x = True) \<and> A) \<noteq>
      (\<lambda>x. (x = False) \<and> A \<or> (x = True))")
   prefer 2
   apply (rule notI)
   apply (drule_tac f = "\<lambda>y. SOME x. y x" in arg_cong)
   apply (drule trans, assumption)
   apply (drule sym)
   apply (drule trans, assumption)
   apply (erule False_neq_True)
  apply (rule disjI2)
  apply (rule notI)
  apply (erule notE)
  apply (rule ext)
  apply (rule iffI)
   apply (erule disjE)
    apply (rule disjI1)
    apply (erule conjI)
    apply assumption
   apply (erule conjE)
   apply (erule disjI2)
  apply (erule disjE)
   apply (erule conjE)
   apply (erule disjI1)
  apply (rule disjI2)
  apply (erule conjI)
  apply assumption
  done


subsection \<open>Proof term of script\<close>

prf tertium_non_datur'

end
