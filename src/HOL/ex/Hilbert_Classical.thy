(*  Title:      HOL/ex/Hilbert_Classical.thy
    ID:         $Id$
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Hilbert's choice and classical logic *}

theory Hilbert_Classical = Main:

text {*
  Derivation of the classical law of tertium-non-datur by means of
  Hilbert's choice operator (due to M. J. Beeson and J. Harrison).
*}


subsection {* Proof text *}

theorem tnd: "A \<or> \<not> A"
proof -
  let ?P = "\<lambda>X. X = False \<or> X = True \<and> A"
  let ?Q = "\<lambda>X. X = False \<and> A \<or> X = True"

  have a: "?P (Eps ?P)"
  proof (rule someI)
    have "False = False" ..
    thus "?P False" ..
  qed
  have b: "?Q (Eps ?Q)"
  proof (rule someI)
    have "True = True" ..
    thus "?Q True" ..
  qed

  from a show ?thesis
  proof
    assume "Eps ?P = True \<and> A"
    hence A ..
    thus ?thesis ..
  next
    assume P: "Eps ?P = False"
    from b show ?thesis
    proof
      assume "Eps ?Q = False \<and> A"
      hence A ..
      thus ?thesis ..
    next
      assume Q: "Eps ?Q = True"
      have neq: "?P \<noteq> ?Q"
      proof
	assume "?P = ?Q"
	hence "Eps ?P = Eps ?Q" by (rule arg_cong)
	also note P
	also note Q
	finally show False by (rule False_neq_True)
      qed
      have "\<not> A"
      proof
	assume a: A
	have "?P = ?Q"
	proof
	  fix x show "?P x = ?Q x"
	  proof
	    assume "?P x"
	    thus "?Q x"
	    proof
	      assume "x = False"
	      from this and a have "x = False \<and> A" ..
	      thus "?Q x" ..
	    next
	      assume "x = True \<and> A"
	      hence "x = True" ..
	      thus "?Q x" ..
	    qed
	  next
	    assume "?Q x"
	    thus "?P x"
	    proof
	      assume "x = False \<and> A"
	      hence "x = False" ..
	      thus "?P x" ..
	    next
	      assume "x = True"
	      from this and a have "x = True \<and> A" ..
	      thus "?P x" ..
	    qed
	  qed
	qed
	with neq show False by contradiction
      qed
      thus ?thesis ..
    qed
  qed
qed


subsection {* Proof term of text *}

text {*
  {\small @{prf [display, margin = 80] tnd}}
*}


subsection {* Proof script *}

theorem tnd': "A \<or> \<not> A"
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


subsection {* Proof term of script *}

text {*
  {\small @{prf [display, margin = 80] tnd'}}
*}

end
