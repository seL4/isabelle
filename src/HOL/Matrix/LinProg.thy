(*  Title:      HOL/Matrix/LinProg.thy
    ID:         $Id$
    Author:     Steven Obua
*)

theory LinProg = Matrix:

lemma linprog_by_duality_approx_general:
  assumes
  fmuladdprops:
  "! a b c d. a <= b & c <= d \<longrightarrow> fadd a c <= fadd b d"
  "! c a b. 0 <= c & a <= b \<longrightarrow> fmul c a <= fmul c b"
  "! a. fmul 0 a = 0"
  "! a. fmul a 0 = 0"
  "fadd 0 0 = 0"
  "associative fadd"
  "commutative fadd"
  "associative fmul"
  "distributive fmul fadd"
  and specificprops:
  "mult_matrix fmul fadd (combine_matrix fadd A dA) x <= (b::('a::{order, zero}) matrix)"
  "mult_matrix fmul fadd y A = c"
  "0 <= y"
  shows
  "combine_matrix fadd (mult_matrix fmul fadd c x) (mult_matrix fmul fadd (mult_matrix fmul fadd y dA) x)
  <= mult_matrix fmul fadd y b"
proof -
  let ?mul = "mult_matrix fmul fadd"
  let ?add = "combine_matrix fadd"
  let ?t1 = "?mul y (?mul (?add A dA) x)"
  have a: "?t1 <= ?mul y b" by (rule le_left_mult, simp_all!)
  have b: "?t1 = ?mul (?mul y (?add A dA)) x" by (simp! add: mult_matrix_assoc_simple[THEN sym])
  have assoc: "associative ?add" by (simp! add: combine_matrix_assoc)
  have r_distr: "r_distributive ?mul ?add"
    apply (rule r_distributive_matrix)
    by (simp! add: distributive_def)+
  have l_distr: "l_distributive ?mul ?add"
    apply (rule l_distributive_matrix)
    by (simp! add: distributive_def)+
  have c:"?mul y (?add A dA) = ?add (?mul y A) (?mul y dA)"
    by (insert r_distr, simp add: r_distributive_def)
  have d:"?mul (?add (?mul y A) (?mul y dA)) x = ?add (?mul (?mul y A) x) (?mul (?mul y dA) x)"
    by (insert l_distr, simp add: l_distributive_def)
  have e:"\<dots> = ?add (?mul c x) (?mul (?mul y dA) x)" by (simp!)
  from a b c d e show "?add (?mul c x) (?mul (?mul y dA) x) <= ?mul y b" by simp
qed

lemma linprog_by_duality_approx:
  assumes
  "(A + dA) * x <= (b::('a::lordered_ring) matrix)"
  "y * A = c"
  "0 <= y"
  shows
  "c * x  + (y * dA) * x <= y * b"
apply (simp add: times_matrix_def plus_matrix_def)
apply (rule linprog_by_duality_approx_general)
apply (simp_all)
apply (simp_all add: associative_def add_assoc mult_assoc)
apply (simp_all add: commutative_def add_commute)
apply (simp_all add: distributive_def l_distributive_def r_distributive_def left_distrib right_distrib)
apply (simp_all! add: plus_matrix_def times_matrix_def)
apply (simp add: add_mono)
apply (simp add: mult_left_mono)
done

lemma linprog_by_duality:
  assumes
  "A * x <= (b::('a::lordered_ring) matrix)"
  "y * A = c"
  "0 <= y"
  shows
  "c * x  <= y * b"
proof -
  have a:"(A + 0) * x <= b" by (simp!)
  have b:"c * x + (y*0)*x <= y * b" by (rule linprog_by_duality_approx, simp_all!)
  show "c * x <= y*b" by (insert b, simp)
qed

end
