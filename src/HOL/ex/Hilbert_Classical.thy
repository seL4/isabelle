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

theorem tnd: "P \<or> \<not> P"
proof -
  let ?A = "\<lambda>x. x = False \<or> x = True \<and> P"
  let ?B = "\<lambda>x. x = False \<and> P \<or> x = True"
  let ?f = "\<lambda>R. SOME y. R y"

  have a: "?A (?f ?A)"
  proof (rule someI)
    have "False = False" ..
    thus "?A False" ..
  qed
  have b: "?B (?f ?B)"
  proof (rule someI)
    have "True = True" ..
    thus "?B True" ..
  qed

  from a show ?thesis
  proof
    assume fa: "?f ?A = False"
    from b show ?thesis
    proof
      assume "?f ?B = False \<and> P"
      hence P ..
      thus ?thesis ..
    next
      assume fb: "?f ?B = True"
      have neq: "?A \<noteq> ?B"
      proof
	assume "?A = ?B" hence eq: "?f ?A = ?f ?B" by (rule arg_cong)
	from fa have "False = ?f ?A" ..
	also note eq
	also note fb
	finally have "False = True" .
	thus False by (rule False_neq_True)
      qed
      have "\<not> P"
      proof
	assume p: P
	have "?A = ?B"
	proof
	  fix x
	  show "?A x = ?B x"
	  proof
	    assume "?A x"
	    thus "?B x"
	    proof
	      assume "x = False"
	      from this and p
	      have "x = False \<and> P" ..
	      thus "?B x" ..
	    next
	      assume "x = True \<and> P"
	      hence "x = True" ..
	      thus "?B x" ..
	    qed
	  next
	    assume "?B x"
	    thus "?A x"
	    proof
	      assume "x = False \<and> P"
	      hence "x = False" ..
	      thus "?A x" ..
	    next
	      assume "x = True"
	      from this and p
	      have "x = True \<and> P" ..
	      thus "?A x" ..
	    qed
	  qed
	qed
	with neq show False by contradiction
      qed
      thus ?thesis ..
    qed
  next
    assume "?f ?A = True \<and> P" hence P ..
    thus ?thesis ..
  qed
qed


subsection {* Proof script *}

theorem tnd': "P \<or> \<not> P"
  apply (subgoal_tac
    "(((SOME x. x = False \<or> x = True \<and> P) = False) \<or>
      ((SOME x. x = False \<or> x = True \<and> P) = True) \<and> P) \<and>
     (((SOME x. x = False \<and> P \<or> x = True) = False) \<and> P \<or>
      ((SOME x. x = False \<and> P \<or> x = True) = True))")
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
    "(\<lambda>x. (x = False) \<or> (x = True) \<and> P) \<noteq>
     (\<lambda>x. (x = False) \<and> P \<or> (x = True))")
  prefer 2
  apply (rule notI)
  apply (drule_tac f="\<lambda>y. SOME x. y x" in arg_cong)
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


subsection {* Proof term of text *}

text {*
  @{prf [display] tnd}
*}


subsection {* Proof term of script *}

text {*
  @{prf [display] tnd'}
*}

end
