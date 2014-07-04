(*  Title:      HOL/Quotient_Examples/Int_Pow.thy
    Author:     Ondrej Kuncar
    Author:     Lars Noschinski
*)

theory Int_Pow
imports Main "~~/src/HOL/Algebra/Group"
begin                          

(*
  This file demonstrates how to restore Lifting/Transfer enviromenent.

  We want to define int_pow (a power with an integer exponent) by directly accessing 
  the representation type "nat * nat" that was used to define integers.
*)

context monoid
begin

(* first some additional lemmas that are missing in monoid *)

lemma Units_nat_pow_Units [intro, simp]: 
  "a \<in> Units G \<Longrightarrow> a (^) (c :: nat) \<in> Units G" by (induct c) auto

lemma Units_r_cancel [simp]:
  "[| z \<in> Units G; x \<in> carrier G; y \<in> carrier G |] ==>
   (x \<otimes> z = y \<otimes> z) = (x = y)"
proof
  assume eq: "x \<otimes> z = y \<otimes> z"
    and G: "z \<in> Units G"  "x \<in> carrier G"  "y \<in> carrier G"
  then have "x \<otimes> (z \<otimes> inv z) = y \<otimes> (z \<otimes> inv z)"
    by (simp add: m_assoc[symmetric] Units_closed del: Units_r_inv)
  with G show "x = y" by simp
next
  assume eq: "x = y"
    and G: "z \<in> Units G"  "x \<in> carrier G"  "y \<in> carrier G"
  then show "x \<otimes> z = y \<otimes> z" by simp
qed

lemma inv_mult_units:
  "[| x \<in> Units G; y \<in> Units G |] ==> inv (x \<otimes> y) = inv y \<otimes> inv x"
proof -
  assume G: "x \<in> Units G"  "y \<in> Units G"
  moreover then have "x \<in> carrier G"  "y \<in> carrier G" by auto
  ultimately have "inv (x \<otimes> y) \<otimes> (x \<otimes> y) = (inv y \<otimes> inv x) \<otimes> (x \<otimes> y)"
    by (simp add: m_assoc) (simp add: m_assoc [symmetric])
  with G show ?thesis by (simp del: Units_l_inv)
qed

lemma mult_same_comm: 
  assumes [simp, intro]: "a \<in> Units G" 
  shows "a (^) (m::nat) \<otimes> inv (a (^) (n::nat)) = inv (a (^) n) \<otimes> a (^) m"
proof (cases "m\<ge>n")
  have [simp]: "a \<in> carrier G" using `a \<in> _` by (rule Units_closed)
  case True
    then obtain k where *:"m = k + n" and **:"m = n + k" by (metis Nat.le_iff_add add.commute)
    have "a (^) (m::nat) \<otimes> inv (a (^) (n::nat)) = a (^) k"
      using * by (auto simp add: nat_pow_mult[symmetric] m_assoc)
    also have "\<dots> = inv (a (^) n) \<otimes> a (^) m"
      using ** by (auto simp add: nat_pow_mult[symmetric] m_assoc[symmetric])
    finally show ?thesis .
next
  have [simp]: "a \<in> carrier G" using `a \<in> _` by (rule Units_closed)
  case False
    then obtain k where *:"n = k + m" and **:"n = m + k" 
      by (metis Nat.le_iff_add add.commute nat_le_linear)
    have "a (^) (m::nat) \<otimes> inv (a (^) (n::nat)) = inv(a (^) k)"
      using * by (auto simp add: nat_pow_mult[symmetric] m_assoc[symmetric] inv_mult_units)
    also have "\<dots> = inv (a (^) n) \<otimes> a (^) m"
      using ** by (auto simp add: nat_pow_mult[symmetric] m_assoc inv_mult_units)
    finally show ?thesis .
qed

lemma mult_inv_same_comm: 
  "a \<in> Units G \<Longrightarrow> inv (a (^) (m::nat)) \<otimes> inv (a (^) (n::nat)) = inv (a (^) n) \<otimes> inv (a (^) m)"
by (simp add: inv_mult_units[symmetric] nat_pow_mult ac_simps Units_closed)

context
includes int.lifting (* restores Lifting/Transfer for integers *)
begin

lemma int_pow_rsp:
  assumes eq: "(b::nat) + e = d + c"
  assumes a_in_G [simp, intro]: "a \<in> Units G"
  shows "a (^) b \<otimes> inv (a (^) c) = a (^) d \<otimes> inv (a (^) e)"
proof(cases "b\<ge>c")
  have [simp]: "a \<in> carrier G" using `a \<in> _` by (rule Units_closed)
  case True
    then obtain n where "b = n + c" by (metis Nat.le_iff_add add.commute)
    then have "d = n + e" using eq by arith
    from `b = _` have "a (^) b \<otimes> inv (a (^) c) = a (^) n" 
      by (auto simp add: nat_pow_mult[symmetric] m_assoc)
    also from `d = _`  have "\<dots> = a (^) d \<otimes> inv (a (^) e)"   
      by (auto simp add: nat_pow_mult[symmetric] m_assoc)
    finally show ?thesis .
next
  have [simp]: "a \<in> carrier G" using `a \<in> _` by (rule Units_closed)
  case False
    then obtain n where "c = n + b" by (metis Nat.le_iff_add add.commute nat_le_linear)
    then have "e = n + d" using eq by arith
    from `c = _` have "a (^) b \<otimes> inv (a (^) c) = inv (a (^) n)" 
      by (auto simp add: nat_pow_mult[symmetric] m_assoc[symmetric] inv_mult_units)
    also from `e = _` have "\<dots> = a (^) d \<otimes> inv (a (^) e)"   
      by (auto simp add: nat_pow_mult[symmetric] m_assoc[symmetric] inv_mult_units)
    finally show ?thesis .
qed

(*
  This definition is more convinient than the definition in HOL/Algebra/Group because
  it doesn't contain a test z < 0 when a (^) z is being defined.
*)

lift_definition int_pow :: "('a, 'm) monoid_scheme \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> 'a" is 
  "\<lambda>G a (n1, n2). if a \<in> Units G \<and> monoid G then (a (^)\<^bsub>G\<^esub> n1) \<otimes>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> (a (^)\<^bsub>G\<^esub> n2)) else \<one>\<^bsub>G\<^esub>" 
unfolding intrel_def by (auto intro: monoid.int_pow_rsp)

(*
  Thus, for example, the proof of distributivity of int_pow and addition 
  doesn't require a substantial number of case distinctions.
*)

lemma int_pow_dist:
  assumes [simp]: "a \<in> Units G"
  shows "int_pow G a ((n::int) + m) = int_pow G a n \<otimes>\<^bsub>G\<^esub> int_pow G a m"
proof -
  {
    fix k l m :: nat
    have "a (^) l \<otimes> (inv (a (^) m) \<otimes> inv (a (^) k)) = (a (^) l \<otimes> inv (a (^) k)) \<otimes> inv (a (^) m)" 
      (is "?lhs = _")
      by (simp add: mult_inv_same_comm m_assoc Units_closed)
    also have "\<dots> = (inv (a (^) k) \<otimes> a (^) l) \<otimes> inv (a (^) m)"
      by (simp add: mult_same_comm)
    also have "\<dots> = inv (a (^) k) \<otimes> (a (^) l \<otimes> inv (a (^) m))" (is "_ = ?rhs")
      by (simp add: m_assoc Units_closed)
    finally have "?lhs = ?rhs" .
  }
  then show ?thesis
    by (transfer fixing: G) (auto simp add: nat_pow_mult[symmetric] inv_mult_units m_assoc Units_closed)
qed

end

lifting_update int.lifting
lifting_forget int.lifting

end

end
