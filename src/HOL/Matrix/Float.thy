theory Float = Hyperreal:

constdefs  
  pow2 :: "int \<Rightarrow> real"
  "pow2 a == if (0 <= a) then (2^(nat a)) else (inverse (2^(nat (-a))))" 
  float :: "int * int \<Rightarrow> real"
  "float x == (real (fst x)) * (pow2 (snd x))"

lemma pow2_0[simp]: "pow2 0 = 1"
by (simp add: pow2_def)

lemma pow2_1[simp]: "pow2 1 = 2"
by (simp add: pow2_def)

lemma pow2_neg: "pow2 x = inverse (pow2 (-x))"
by (simp add: pow2_def)

lemma pow2_add1: "pow2 (1 + a) = 2 * (pow2 a)" 
proof -
  have h: "! n. nat (2 + int n) - Suc 0 = nat (1 + int n)" by arith
  have g: "! a b. a - -1 = a + (1::int)" by arith
  have pos: "! n. pow2 (int n + 1) = 2 * pow2 (int n)"
    apply (auto, induct_tac n)
    apply (simp_all add: pow2_def)
    apply (rule_tac m1="2" and n1="nat (2 + int na)" in ssubst[OF realpow_num_eq_if])
    apply (auto simp add: h)
    apply arith
    done
  show ?thesis
  proof (induct a)
    case (1 n)
    from pos show ?case by (simp add: ring_eq_simps)
  next
    case (2 n)
    show ?case
      apply (auto)
      apply (subst pow2_neg[of "- int n"])
      apply (subst pow2_neg[of "-1 - int n"])
      apply (auto simp add: g pos)
      done
  qed
qed
  
lemma pow2_add: "pow2 (a+b) = (pow2 a) * (pow2 b)"
proof (induct b)
  case (1 n) 
  show ?case
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc m)
    show ?case by (auto simp add: ring_eq_simps pow2_add1 prems)
  qed
next
  case (2 n)
  show ?case
  proof (induct n)
    case 0
    show ?case
      apply (auto)
      apply (subst pow2_neg[of "a + -1"])
      apply (subst pow2_neg[of "-1"])
      apply (simp)
      apply (insert pow2_add1[of "-a"])
      apply (simp add: ring_eq_simps)
      apply (subst pow2_neg[of "-a"])
      apply (simp)
      done
    case (Suc m)
    have a: "int m - (a + -2) =  1 + (int m - a + 1)" by arith
    have b: "int m - -2 = 1 + (int m + 1)" by arith
    show ?case
      apply (auto)
      apply (subst pow2_neg[of "a + (-2 - int m)"])
      apply (subst pow2_neg[of "-2 - int m"])
      apply (auto simp add: ring_eq_simps)
      apply (subst a)
      apply (subst b)
      apply (simp only: pow2_add1)
      apply (subst pow2_neg[of "int m - a + 1"])
      apply (subst pow2_neg[of "int m + 1"])
      apply auto
      apply (insert prems)
      apply (auto simp add: ring_eq_simps)
      done
  qed
qed

lemma "float (a, e) + float (b, e) = float (a + b, e)"  
by (simp add: float_def ring_eq_simps)

constdefs 
  int_of_real :: "real \<Rightarrow> int"
  "int_of_real x == SOME y. real y = x"  
  real_is_int :: "real \<Rightarrow> bool"
  "real_is_int x == ? (u::int). x = real u" 

lemma real_is_int_def2: "real_is_int x = (x = real (int_of_real x))"
by (auto simp add: real_is_int_def int_of_real_def)

lemma float_transfer: "real_is_int ((real a)*(pow2 c)) \<Longrightarrow> float (a, b) = float (int_of_real ((real a)*(pow2 c)), b - c)"
by (simp add: float_def real_is_int_def2 pow2_add[symmetric])

lemma pow2_int: "pow2 (int c) = (2::real)^c"
by (simp add: pow2_def)

lemma float_transfer_nat: "float (a, b) = float (a * 2^c, b - int c)" 
by (simp add: float_def pow2_int[symmetric] pow2_add[symmetric])

lemma real_is_int_real[simp]: "real_is_int (real (x::int))"
by (auto simp add: real_is_int_def int_of_real_def)

lemma int_of_real_real[simp]: "int_of_real (real x) = x"
by (simp add: int_of_real_def)

lemma real_int_of_real[simp]: "real_is_int x \<Longrightarrow> real (int_of_real x) = x"
by (auto simp add: int_of_real_def real_is_int_def)

lemma real_is_int_add_int_of_real: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> (int_of_real (a+b)) = (int_of_real a) + (int_of_real b)"
by (auto simp add: int_of_real_def real_is_int_def)

lemma real_is_int_add[simp]: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> real_is_int (a+b)"
apply (subst real_is_int_def2)
apply (simp add: real_is_int_add_int_of_real real_int_of_real)
done

lemma int_of_real_sub: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> (int_of_real (a-b)) = (int_of_real a) - (int_of_real b)"
by (auto simp add: int_of_real_def real_is_int_def)

lemma real_is_int_sub[simp]: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> real_is_int (a-b)"
apply (subst real_is_int_def2)
apply (simp add: int_of_real_sub real_int_of_real)
done

lemma real_is_int_rep: "real_is_int x \<Longrightarrow> ?! (a::int). real a = x"
by (auto simp add: real_is_int_def)

lemma int_of_real_mult: 
  assumes "real_is_int a" "real_is_int b"
  shows "(int_of_real (a*b)) = (int_of_real a) * (int_of_real b)"
proof -
  from prems have a: "?! (a'::int). real a' = a" by (rule_tac real_is_int_rep, auto)
  from prems have b: "?! (b'::int). real b' = b" by (rule_tac real_is_int_rep, auto)
  from a obtain a'::int where a':"a = real a'" by auto
  from b obtain b'::int where b':"b = real b'" by auto
  have r: "real a' * real b' = real (a' * b')" by auto
  show ?thesis
    apply (simp add: a' b')
    apply (subst r)
    apply (simp only: int_of_real_real)
    done
qed

lemma real_is_int_mult[simp]: "real_is_int a \<Longrightarrow> real_is_int b \<Longrightarrow> real_is_int (a*b)"
apply (subst real_is_int_def2)
apply (simp add: int_of_real_mult)
done

lemma real_is_int_0[simp]: "real_is_int (0::real)"
by (simp add: real_is_int_def int_of_real_def)

lemma real_is_int_1[simp]: "real_is_int (1::real)"
proof -
  have "real_is_int (1::real) = real_is_int(real (1::int))" by auto
  also have "\<dots> = True" by (simp only: real_is_int_real)
  ultimately show ?thesis by auto
qed

lemma real_is_int_n1: "real_is_int (-1::real)"
proof -
  have "real_is_int (-1::real) = real_is_int(real (-1::int))" by auto
  also have "\<dots> = True" by (simp only: real_is_int_real)
  ultimately show ?thesis by auto
qed

lemma real_is_int_number_of[simp]: "real_is_int ((number_of::bin\<Rightarrow>real) x)"
proof -
  have neg1: "real_is_int (-1::real)"
  proof -
    have "real_is_int (-1::real) = real_is_int(real (-1::int))" by auto
    also have "\<dots> = True" by (simp only: real_is_int_real)
    ultimately show ?thesis by auto
  qed
  
  { 
    fix x::int
    have "!! y. real_is_int ((number_of::bin\<Rightarrow>real) (Abs_Bin x))"
      apply (simp add: number_of_eq)
      apply (subst Abs_Bin_inverse)
      apply (simp add: Bin_def)
      apply (induct x)
      apply (induct_tac n)
      apply (simp)
      apply (simp)
      apply (induct_tac n)
      apply (simp add: neg1)
    proof -
      fix n :: nat
      assume rn: "(real_is_int (of_int (- (int (Suc n)))))"
      have s: "-(int (Suc (Suc n))) = -1 + - (int (Suc n))" by simp
      show "real_is_int (of_int (- (int (Suc (Suc n)))))"
	apply (simp only: s of_int_add)
	apply (rule real_is_int_add)
	apply (simp add: neg1)
	apply (simp only: rn)
	done
    qed
  }
  note Abs_Bin = this
  {
    fix x :: bin
    have "? u. x = Abs_Bin u"
      apply (rule exI[where x = "Rep_Bin x"])
      apply (simp add: Rep_Bin_inverse)
      done
  }
  then obtain u::int where "x = Abs_Bin u" by auto
  with Abs_Bin show ?thesis by auto
qed

lemma int_of_real_0[simp]: "int_of_real (0::real) = (0::int)"
by (simp add: int_of_real_def)

lemma int_of_real_1[simp]: "int_of_real (1::real) = (1::int)"
proof - 
  have 1: "(1::real) = real (1::int)" by auto
  show ?thesis by (simp only: 1 int_of_real_real)
qed

lemma int_of_real_number_of[simp]: "int_of_real (number_of b) = number_of b"
proof -
  have "real_is_int (number_of b)" by simp
  then have uu: "?! u::int. number_of b = real u" by (auto simp add: real_is_int_rep)
  then obtain u::int where u:"number_of b = real u" by auto
  have "number_of b = real ((number_of b)::int)" 
    by (simp add: number_of_eq real_of_int_def)
  have ub: "number_of b = real ((number_of b)::int)" 
    by (simp add: number_of_eq real_of_int_def)
  from uu u ub have unb: "u = number_of b"
    by blast
  have "int_of_real (number_of b) = u" by (simp add: u)
  with unb show ?thesis by simp
qed

lemma float_transfer_even: "even a \<Longrightarrow> float (a, b) = float (a div 2, b+1)"
  apply (subst float_transfer[where a="a" and b="b" and c="-1", simplified])
  apply (simp_all add: pow2_def even_def real_is_int_def ring_eq_simps)
  apply (auto)
proof -
  fix q::int
  have a:"b - (-1\<Colon>int) = (1\<Colon>int) + b" by arith
  show "(float (q, (b - (-1\<Colon>int)))) = (float (q, ((1\<Colon>int) + b)))" 
    by (simp add: a)
qed
    
consts
  norm_float :: "int*int \<Rightarrow> int*int"

lemma int_div_zdiv: "int (a div b) = (int a) div (int b)"
apply (subst split_div, auto)
apply (subst split_zdiv, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and r="int j" and r'=ja in IntDiv.unique_quotient)
apply (auto simp add: IntDiv.quorem_def int_eq_of_nat)
done

lemma int_mod_zmod: "int (a mod b) = (int a) mod (int b)"
apply (subst split_mod, auto)
apply (subst split_zmod, auto)
apply (rule_tac a="int (b * i) + int j" and b="int b" and q="int i" and q'=ia in IntDiv.unique_remainder)
apply (auto simp add: IntDiv.quorem_def int_eq_of_nat)
done

lemma abs_div_2_less: "a \<noteq> 0 \<Longrightarrow> a \<noteq> -1 \<Longrightarrow> abs((a::int) div 2) < abs a"
by arith

lemma terminating_norm_float: "\<forall>a. (a::int) \<noteq> 0 \<and> even a \<longrightarrow> a \<noteq> 0 \<and> \<bar>a div 2\<bar> < \<bar>a\<bar>"
apply (auto)
apply (rule abs_div_2_less)
apply (auto)
done

ML {* simp_depth_limit := 2 *} 
recdef norm_float "measure (% (a,b). nat (abs a))"
  "norm_float (a,b) = (if (a \<noteq> 0) & (even a) then norm_float (a div 2, b+1) else (if a=0 then (0,0) else (a,b)))"
(hints simp: terminating_norm_float)
ML {* simp_depth_limit := 1000 *}


lemma norm_float: "float x = float (norm_float x)"
proof -
  {
    fix a b :: int 
    have norm_float_pair: "float (a,b) = float (norm_float (a,b))" 
    proof (induct a b rule: norm_float.induct)
      case (1 u v)
      show ?case 
      proof cases
	assume u: "u \<noteq> 0 \<and> even u"
	with prems have ind: "float (u div 2, v + 1) = float (norm_float (u div 2, v + 1))" by auto
	with u have "float (u,v) = float (u div 2, v+1)" by (simp add: float_transfer_even) 
	then show ?thesis
	  apply (subst norm_float.simps)
	  apply (simp add: ind)
	  done
      next
	assume "~(u \<noteq> 0 \<and> even u)"
	then show ?thesis
	  by (simp add: prems float_def)
      qed
    qed
  }
  note helper = this
  have "? a b. x = (a,b)" by auto
  then obtain a b where "x = (a, b)" by blast
  then show ?thesis by (simp only: helper)
qed

lemma pow2_int: "pow2 (int n) = 2^n"
  by (simp add: pow2_def)

lemma float_add: 
  "float (a1, e1) + float (a2, e2) = 
  (if e1<=e2 then float (a1+a2*2^(nat(e2-e1)), e1) 
  else float (a1*2^(nat (e1-e2))+a2, e2))"
  apply (simp add: float_def ring_eq_simps)
  apply (auto simp add: pow2_int[symmetric] pow2_add[symmetric])
  done

lemma float_mult:
  "float (a1, e1) * float (a2, e2) = 
  (float (a1 * a2, e1 + e2))"
  by (simp add: float_def pow2_add)

lemma float_minus:
  "- (float (a,b)) = float (-a, b)"
  by (simp add: float_def)

lemma zero_less_pow2:
  "0 < pow2 x"
proof -
  {
    fix y
    have "0 <= y \<Longrightarrow> 0 < pow2 y"    
      by (induct y, induct_tac n, simp_all add: pow2_add)
  }
  note helper=this
  show ?thesis
    apply (case_tac "0 <= x")
    apply (simp add: helper)
    apply (subst pow2_neg)
    apply (simp add: helper)
    done
qed

lemma zero_le_float:
  "(0 <= float (a,b)) = (0 <= a)"
  apply (auto simp add: float_def)
  apply (auto simp add: zero_le_mult_iff zero_less_pow2) 
  apply (insert zero_less_pow2[of b])
  apply (simp_all)
  done

lemma float_abs:
  "abs (float (a,b)) = (if 0 <= a then (float (a,b)) else (float (-a,b)))"
  apply (auto simp add: abs_if)
  apply (simp_all add: zero_le_float[symmetric, of a b] float_minus)
  done

lemma norm_0_1: "(0::_::number_ring) = Numeral0 & (1::_::number_ring) = Numeral1"
  by auto
  
lemma add_left_zero: "0 + a = (a::'a::comm_monoid_add)"
  by simp

lemma add_right_zero: "a + 0 = (a::'a::comm_monoid_add)"
  by simp

lemma mult_left_one: "1 * a = (a::'a::semiring_1)"
  by simp

lemma mult_right_one: "a * 1 = (a::'a::semiring_1)"
  by simp

lemma int_pow_0: "(a::int)^(Numeral0) = 1"
  by simp

lemma int_pow_1: "(a::int)^(Numeral1) = a"
  by simp

lemma zero_eq_Numeral0_nring: "(0::'a::number_ring) = Numeral0"
  by simp

lemma one_eq_Numeral1_nring: "(1::'a::number_ring) = Numeral1"
  by simp

lemma zero_eq_Numeral0_nat: "(0::nat) = Numeral0"
  by simp

lemma one_eq_Numeral1_nat: "(1::nat) = Numeral1"
  by simp

lemma zpower_Pls: "(z::int)^Numeral0 = Numeral1"
  by simp

lemma zpower_Min: "(z::int)^((-1)::nat) = Numeral1"
proof -
  have 1:"((-1)::nat) = 0"
    by simp
  show ?thesis by (simp add: 1)
qed

lemma fst_cong: "a=a' \<Longrightarrow> fst (a,b) = fst (a',b)"
  by simp

lemma snd_cong: "b=b' \<Longrightarrow> snd (a,b) = snd (a,b')"
  by simp

lemma lift_bool: "x \<Longrightarrow> x=True"
  by simp

lemma nlift_bool: "~x \<Longrightarrow> x=False"
  by simp

lemma not_false_eq_true: "(~ False) = True" by simp

lemma not_true_eq_false: "(~ True) = False" by simp


lemmas binarith = 
  Pls_0_eq Min_1_eq
  bin_pred_Pls bin_pred_Min bin_pred_1 bin_pred_0     
  bin_succ_Pls bin_succ_Min bin_succ_1 bin_succ_0
  bin_add_Pls bin_add_Min bin_add_BIT_0 bin_add_BIT_10
  bin_add_BIT_11 bin_minus_Pls bin_minus_Min bin_minus_1 
  bin_minus_0 bin_mult_Pls bin_mult_Min bin_mult_1 bin_mult_0 
  bin_add_Pls_right bin_add_Min_right

thm eq_number_of_eq

lemma int_eq_number_of_eq: "(((number_of v)::int)=(number_of w)) = iszero ((number_of (bin_add v (bin_minus w)))::int)"
  by simp

lemma int_iszero_number_of_Pls: "iszero (Numeral0::int)" 
  by (simp only: iszero_number_of_Pls)

lemma int_nonzero_number_of_Min: "~(iszero ((-1)::int))"
  by simp
thm iszero_number_of_1

lemma int_iszero_number_of_0: "iszero ((number_of (w BIT False))::int) = iszero ((number_of w)::int)"
  by simp

lemma int_iszero_number_of_1: "\<not> iszero ((number_of (w BIT True))::int)" 
  by simp

lemma int_less_number_of_eq_neg: "(((number_of x)::int) < number_of y) = neg ((number_of (bin_add x (bin_minus y)))::int)"
  by simp

lemma int_not_neg_number_of_Pls: "\<not> (neg (Numeral0::int))" 
  by simp

lemma int_neg_number_of_Min: "neg (-1::int)"
  by simp

lemma int_neg_number_of_BIT: "neg ((number_of (w BIT x))::int) = neg ((number_of w)::int)"
  by simp

lemma int_le_number_of_eq: "(((number_of x)::int) \<le> number_of y) = (\<not> neg ((number_of (bin_add y (bin_minus x)))::int))"
  by simp

lemmas intarithrel = 
  (*abs_zero abs_one*)
  int_eq_number_of_eq 
  lift_bool[OF int_iszero_number_of_Pls] nlift_bool[OF int_nonzero_number_of_Min] int_iszero_number_of_0 
  lift_bool[OF int_iszero_number_of_1] int_less_number_of_eq_neg nlift_bool[OF int_not_neg_number_of_Pls] lift_bool[OF int_neg_number_of_Min]
  int_neg_number_of_BIT int_le_number_of_eq

lemma int_number_of_add_sym: "((number_of v)::int) + number_of w = number_of (bin_add v w)"
  by simp

lemma int_number_of_diff_sym: "((number_of v)::int) - number_of w = number_of (bin_add v (bin_minus w))"
  by simp

lemma int_number_of_mult_sym: "((number_of v)::int) * number_of w = number_of (bin_mult v w)"
  by simp

lemma int_number_of_minus_sym: "- ((number_of v)::int) = number_of (bin_minus v)"
  by simp

lemmas intarith = int_number_of_add_sym int_number_of_minus_sym int_number_of_diff_sym int_number_of_mult_sym

lemmas natarith = (*zero_eq_Numeral0_nat one_eq_Numeral1_nat*) add_nat_number_of 
  diff_nat_number_of mult_nat_number_of eq_nat_number_of less_nat_number_of

lemmas powerarith = nat_number_of zpower_number_of_even 
  zpower_number_of_odd[simplified zero_eq_Numeral0_nring one_eq_Numeral1_nring]   
  zpower_Pls zpower_Min

lemmas floatarith[simplified norm_0_1] = float_add float_mult float_minus float_abs zero_le_float

lemmas arith = binarith intarith intarithrel natarith powerarith floatarith not_false_eq_true not_true_eq_false

(* needed for the verifying code generator *)
lemmas arith_no_let = arith[simplified Let_def]

end
 
