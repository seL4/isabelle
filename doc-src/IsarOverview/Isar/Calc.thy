theory Calc = Main:

subsection{* Chains of equalities *}

axclass
  group < zero, plus, minus
  assoc:       "(x + y) + z = x + (y + z)"
  left_0:      "0 + x = x"
  left_minus:  "-x + x = 0"

theorem right_minus: "x + -x = (0::'a::group)"
proof -
  have   "x + -x = (-(-x) + -x) + (x + -x)"
    by (simp only: left_0 left_minus)
  also have "... = -(-x) + ((-x + x) + -x)"
    by (simp only: group.assoc)
  also have "... = 0"
    by (simp only: left_0 left_minus)
  finally show ?thesis .
qed

subsection{* Inequalities and substitution *}

lemmas distrib = zadd_zmult_distrib zadd_zmult_distrib2
                 zdiff_zmult_distrib zdiff_zmult_distrib2
declare numeral_2_eq_2[simp]


lemma fixes a :: int shows "(a+b)\<twosuperior> \<le> 2*(a\<twosuperior> + b\<twosuperior>)"
proof -
       have "(a+b)\<twosuperior> \<le> (a+b)\<twosuperior> + (a-b)\<twosuperior>"  by simp
  also have "(a+b)\<twosuperior> \<le> a\<twosuperior> + b\<twosuperior> + 2*a*b"  by(simp add:distrib)
  also have "(a-b)\<twosuperior> = a\<twosuperior> + b\<twosuperior> - 2*a*b"  by(simp add:distrib)
  finally show ?thesis by simp
qed


subsection{* More transitivity *}

lemma assumes R: "(a,b) \<in> R" "(b,c) \<in> R" "(c,d) \<in> R"
      shows "(a,d) \<in> R\<^sup>*"
proof -
       have "(a,b) \<in> R\<^sup>*" ..
  also have "(b,c) \<in> R\<^sup>*" ..
  also have "(c,d) \<in> R\<^sup>*" ..
  finally show ?thesis .
qed

end