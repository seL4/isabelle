theory Calc = Main:

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


lemma assumes R: "(a,b) \<in> R" "(b,c) \<in> R" "(c,d) \<in> R"
      shows "(a,d) \<in> R\<^sup>*"
proof -
       have "(a,b) \<in> R\<^sup>*" ..
  also have "(b,c) \<in> R\<^sup>*" ..
  also have "(c,d) \<in> R\<^sup>*" ..
  finally show ?thesis .
qed

end