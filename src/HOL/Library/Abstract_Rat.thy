(*  Title:      HOL/Library/Abstract_Rat.thy
    Author:     Amine Chaieb
*)

header {* Abstract rational numbers *}

theory Abstract_Rat
imports Complex_Main
begin

type_synonym Num = "int \<times> int"

abbreviation Num0_syn :: Num  ("0\<^sub>N")
  where "0\<^sub>N \<equiv> (0, 0)"

abbreviation Numi_syn :: "int \<Rightarrow> Num"  ("_\<^sub>N")
  where "i\<^sub>N \<equiv> (i, 1)"

definition isnormNum :: "Num \<Rightarrow> bool" where
  "isnormNum = (\<lambda>(a,b). (if a = 0 then b = 0 else b > 0 \<and> gcd a b = 1))"

definition normNum :: "Num \<Rightarrow> Num" where
  "normNum = (\<lambda>(a,b).
    (if a=0 \<or> b = 0 then (0,0) else
      (let g = gcd a b
       in if b > 0 then (a div g, b div g) else (- (a div g), - (b div g)))))"

declare gcd_dvd1_int[presburger] gcd_dvd2_int[presburger]

lemma normNum_isnormNum [simp]: "isnormNum (normNum x)"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  { assume "a=0 \<or> b = 0" hence ?thesis by (simp add: x normNum_def isnormNum_def) }
  moreover
  { assume anz: "a \<noteq> 0" and bnz: "b \<noteq> 0"
    let ?g = "gcd a b"
    let ?a' = "a div ?g"
    let ?b' = "b div ?g"
    let ?g' = "gcd ?a' ?b'"
    from anz bnz have "?g \<noteq> 0" by simp  with gcd_ge_0_int[of a b]
    have gpos: "?g > 0" by arith
    have gdvd: "?g dvd a" "?g dvd b" by arith+
    from dvd_mult_div_cancel[OF gdvd(1)] dvd_mult_div_cancel[OF gdvd(2)] anz bnz
    have nz': "?a' \<noteq> 0" "?b' \<noteq> 0" by - (rule notI, simp)+
    from anz bnz have stupid: "a \<noteq> 0 \<or> b \<noteq> 0" by arith
    from div_gcd_coprime_int[OF stupid] have gp1: "?g' = 1" .
    from bnz have "b < 0 \<or> b > 0" by arith
    moreover
    { assume b: "b > 0"
      from b have "?b' \<ge> 0"
        by (presburger add: pos_imp_zdiv_nonneg_iff[OF gpos])
      with nz' have b': "?b' > 0" by arith
      from b b' anz bnz nz' gp1 have ?thesis
        by (simp add: x isnormNum_def normNum_def Let_def split_def) }
    moreover {
      assume b: "b < 0"
      { assume b': "?b' \<ge> 0"
        from gpos have th: "?g \<ge> 0" by arith
        from mult_nonneg_nonneg[OF th b'] dvd_mult_div_cancel[OF gdvd(2)]
        have False using b by arith }
      hence b': "?b' < 0" by (presburger add: linorder_not_le[symmetric])
      from anz bnz nz' b b' gp1 have ?thesis
        by (simp add: x isnormNum_def normNum_def Let_def split_def) }
    ultimately have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed

text {* Arithmetic over Num *}

definition Nadd :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl "+\<^sub>N" 60) where
  "Nadd = (\<lambda>(a,b) (a',b'). if a = 0 \<or> b = 0 then normNum(a',b')
    else if a'=0 \<or> b' = 0 then normNum(a,b)
    else normNum(a*b' + b*a', b*b'))"

definition Nmul :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl "*\<^sub>N" 60) where
  "Nmul = (\<lambda>(a,b) (a',b'). let g = gcd (a*a') (b*b')
    in (a*a' div g, b*b' div g))"

definition Nneg :: "Num \<Rightarrow> Num" ("~\<^sub>N")
  where "Nneg \<equiv> (\<lambda>(a,b). (-a,b))"

definition Nsub :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl "-\<^sub>N" 60)
  where "Nsub = (\<lambda>a b. a +\<^sub>N ~\<^sub>N b)"

definition Ninv :: "Num \<Rightarrow> Num"
  where "Ninv = (\<lambda>(a,b). if a < 0 then (-b, \<bar>a\<bar>) else (b,a))"

definition Ndiv :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl "\<div>\<^sub>N" 60)
  where "Ndiv = (\<lambda>a b. a *\<^sub>N Ninv b)"

lemma Nneg_normN[simp]: "isnormNum x \<Longrightarrow> isnormNum (~\<^sub>N x)"
  by (simp add: isnormNum_def Nneg_def split_def)

lemma Nadd_normN[simp]: "isnormNum (x +\<^sub>N y)"
  by (simp add: Nadd_def split_def)

lemma Nsub_normN[simp]: "\<lbrakk> isnormNum y\<rbrakk> \<Longrightarrow> isnormNum (x -\<^sub>N y)"
  by (simp add: Nsub_def split_def)

lemma Nmul_normN[simp]:
  assumes xn: "isnormNum x" and yn: "isnormNum y"
  shows "isnormNum (x *\<^sub>N y)"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  { assume "a = 0"
    hence ?thesis using xn x y
      by (simp add: isnormNum_def Let_def Nmul_def split_def) }
  moreover
  { assume "a' = 0"
    hence ?thesis using yn x y
      by (simp add: isnormNum_def Let_def Nmul_def split_def) }
  moreover
  { assume a: "a \<noteq>0" and a': "a'\<noteq>0"
    hence bp: "b > 0" "b' > 0" using xn yn x y by (simp_all add: isnormNum_def)
    from mult_pos_pos[OF bp] have "x *\<^sub>N y = normNum (a * a', b * b')"
      using x y a a' bp by (simp add: Nmul_def Let_def split_def normNum_def)
    hence ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma Ninv_normN[simp]: "isnormNum x \<Longrightarrow> isnormNum (Ninv x)"
  by (simp add: Ninv_def isnormNum_def split_def)
    (cases "fst x = 0", auto simp add: gcd_commute_int)

lemma isnormNum_int[simp]:
  "isnormNum 0\<^sub>N" "isnormNum ((1::int)\<^sub>N)" "i \<noteq> 0 \<Longrightarrow> isnormNum (i\<^sub>N)"
  by (simp_all add: isnormNum_def)


text {* Relations over Num *}

definition Nlt0:: "Num \<Rightarrow> bool"  ("0>\<^sub>N")
  where "Nlt0 = (\<lambda>(a,b). a < 0)"

definition Nle0:: "Num \<Rightarrow> bool"  ("0\<ge>\<^sub>N")
  where "Nle0 = (\<lambda>(a,b). a \<le> 0)"

definition Ngt0:: "Num \<Rightarrow> bool"  ("0<\<^sub>N")
  where "Ngt0 = (\<lambda>(a,b). a > 0)"

definition Nge0:: "Num \<Rightarrow> bool"  ("0\<le>\<^sub>N")
  where "Nge0 = (\<lambda>(a,b). a \<ge> 0)"

definition Nlt :: "Num \<Rightarrow> Num \<Rightarrow> bool"  (infix "<\<^sub>N" 55)
  where "Nlt = (\<lambda>a b. 0>\<^sub>N (a -\<^sub>N b))"

definition Nle :: "Num \<Rightarrow> Num \<Rightarrow> bool"  (infix "\<le>\<^sub>N" 55)
  where "Nle = (\<lambda>a b. 0\<ge>\<^sub>N (a -\<^sub>N b))"

definition "INum = (\<lambda>(a,b). of_int a / of_int b)"

lemma INum_int [simp]: "INum (i\<^sub>N) = ((of_int i) ::'a::field)" "INum 0\<^sub>N = (0::'a::field)"
  by (simp_all add: INum_def)

lemma isnormNum_unique[simp]:
  assumes na: "isnormNum x" and nb: "isnormNum y"
  shows "((INum x ::'a::{field_char_0, field_inverse_zero}) = INum y) = (x = y)" (is "?lhs = ?rhs")
proof
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  assume H: ?lhs
  { assume "a = 0 \<or> b = 0 \<or> a' = 0 \<or> b' = 0"
    hence ?rhs using na nb H
      by (simp add: x y INum_def split_def isnormNum_def split: split_if_asm) }
  moreover
  { assume az: "a \<noteq> 0" and bz: "b \<noteq> 0" and a'z: "a'\<noteq>0" and b'z: "b'\<noteq>0"
    from az bz a'z b'z na nb have pos: "b > 0" "b' > 0" by (simp_all add: x y isnormNum_def)
    from H bz b'z have eq: "a * b' = a'*b"
      by (simp add: x y INum_def eq_divide_eq divide_eq_eq of_int_mult[symmetric] del: of_int_mult)
    from az a'z na nb have gcd1: "gcd a b = 1" "gcd b a = 1" "gcd a' b' = 1" "gcd b' a' = 1"
      by (simp_all add: x y isnormNum_def add: gcd_commute_int)
    from eq have raw_dvd: "a dvd a' * b" "b dvd b' * a" "a' dvd a * b'" "b' dvd b * a'"
      apply -
      apply algebra
      apply algebra
      apply simp
      apply algebra
      done
    from zdvd_antisym_abs[OF coprime_dvd_mult_int[OF gcd1(2) raw_dvd(2)]
        coprime_dvd_mult_int[OF gcd1(4) raw_dvd(4)]]
      have eq1: "b = b'" using pos by arith
      with eq have "a = a'" using pos by simp
      with eq1 have ?rhs by (simp add: x y) }
  ultimately show ?rhs by blast
next
  assume ?rhs thus ?lhs by simp
qed


lemma isnormNum0[simp]:
    "isnormNum x \<Longrightarrow> (INum x = (0::'a::{field_char_0, field_inverse_zero})) = (x = 0\<^sub>N)"
  unfolding INum_int(2)[symmetric]
  by (rule isnormNum_unique) simp_all

lemma of_int_div_aux: "d ~= 0 ==> ((of_int x)::'a::field_char_0) / (of_int d) =
    of_int (x div d) + (of_int (x mod d)) / ((of_int d)::'a)"
proof -
  assume "d ~= 0"
  let ?t = "of_int (x div d) * ((of_int d)::'a) + of_int(x mod d)"
  let ?f = "\<lambda>x. x / of_int d"
  have "x = (x div d) * d + x mod d"
    by auto
  then have eq: "of_int x = ?t"
    by (simp only: of_int_mult[symmetric] of_int_add [symmetric])
  then have "of_int x / of_int d = ?t / of_int d"
    using cong[OF refl[of ?f] eq] by simp
  then show ?thesis by (simp add: add_divide_distrib algebra_simps `d ~= 0`)
qed

lemma of_int_div: "(d::int) ~= 0 ==> d dvd n ==>
    (of_int(n div d)::'a::field_char_0) = of_int n / of_int d"
  apply (frule of_int_div_aux [of d n, where ?'a = 'a])
  apply simp
  apply (simp add: dvd_eq_mod_eq_0)
  done


lemma normNum[simp]: "INum (normNum x) = (INum x :: 'a::{field_char_0, field_inverse_zero})"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  { assume "a = 0 \<or> b = 0"
    hence ?thesis by (simp add: x INum_def normNum_def split_def Let_def) }
  moreover
  { assume a: "a \<noteq> 0" and b: "b \<noteq> 0"
    let ?g = "gcd a b"
    from a b have g: "?g \<noteq> 0"by simp
    from of_int_div[OF g, where ?'a = 'a]
    have ?thesis by (auto simp add: x INum_def normNum_def split_def Let_def) }
  ultimately show ?thesis by blast
qed

lemma INum_normNum_iff:
  "(INum x ::'a::{field_char_0, field_inverse_zero}) = INum y \<longleftrightarrow> normNum x = normNum y"
  (is "?lhs = ?rhs")
proof -
  have "normNum x = normNum y \<longleftrightarrow> (INum (normNum x) :: 'a) = INum (normNum y)"
    by (simp del: normNum)
  also have "\<dots> = ?lhs" by simp
  finally show ?thesis by simp
qed

lemma Nadd[simp]: "INum (x +\<^sub>N y) = INum x + (INum y :: 'a :: {field_char_0, field_inverse_zero})"
proof -
  let ?z = "0:: 'a"
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  { assume "a=0 \<or> a'= 0 \<or> b =0 \<or> b' = 0"
    hence ?thesis
      apply (cases "a=0", simp_all add: x y Nadd_def)
      apply (cases "b= 0", simp_all add: INum_def)
       apply (cases "a'= 0", simp_all)
       apply (cases "b'= 0", simp_all)
       done }
  moreover
  { assume aa': "a \<noteq> 0" "a'\<noteq> 0" and bb': "b \<noteq> 0" "b' \<noteq> 0"
    { assume z: "a * b' + b * a' = 0"
      hence "of_int (a*b' + b*a') / (of_int b* of_int b') = ?z" by simp
      hence "of_int b' * of_int a / (of_int b * of_int b') +
          of_int b * of_int a' / (of_int b * of_int b') = ?z"
        by (simp add:add_divide_distrib)
      hence th: "of_int a / of_int b + of_int a' / of_int b' = ?z" using bb' aa'
        by simp
      from z aa' bb' have ?thesis
        by (simp add: x y th Nadd_def normNum_def INum_def split_def) }
    moreover {
      assume z: "a * b' + b * a' \<noteq> 0"
      let ?g = "gcd (a * b' + b * a') (b*b')"
      have gz: "?g \<noteq> 0" using z by simp
      have ?thesis using aa' bb' z gz
        of_int_div[where ?'a = 'a, OF gz gcd_dvd1_int[where x="a * b' + b * a'" and y="b*b'"]]
        of_int_div[where ?'a = 'a, OF gz gcd_dvd2_int[where x="a * b' + b * a'" and y="b*b'"]]
        by (simp add: x y Nadd_def INum_def normNum_def Let_def add_divide_distrib) }
    ultimately have ?thesis using aa' bb'
      by (simp add: x y Nadd_def INum_def normNum_def Let_def) }
  ultimately show ?thesis by blast
qed

lemma Nmul[simp]: "INum (x *\<^sub>N y) = INum x * (INum y:: 'a :: {field_char_0, field_inverse_zero})"
proof -
  let ?z = "0::'a"
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  { assume "a=0 \<or> a'= 0 \<or> b = 0 \<or> b' = 0"
    hence ?thesis
      apply (cases "a=0", simp_all add: x y Nmul_def INum_def Let_def)
      apply (cases "b=0", simp_all)
      apply (cases "a'=0", simp_all)
      done }
  moreover
  { assume z: "a \<noteq> 0" "a' \<noteq> 0" "b \<noteq> 0" "b' \<noteq> 0"
    let ?g="gcd (a*a') (b*b')"
    have gz: "?g \<noteq> 0" using z by simp
    from z of_int_div[where ?'a = 'a, OF gz gcd_dvd1_int[where x="a*a'" and y="b*b'"]]
      of_int_div[where ?'a = 'a , OF gz gcd_dvd2_int[where x="a*a'" and y="b*b'"]]
    have ?thesis by (simp add: Nmul_def x y Let_def INum_def) }
  ultimately show ?thesis by blast
qed

lemma Nneg[simp]: "INum (~\<^sub>N x) = - (INum x ::'a:: field)"
  by (simp add: Nneg_def split_def INum_def)

lemma Nsub[simp]: "INum (x -\<^sub>N y) = INum x - (INum y:: 'a :: {field_char_0, field_inverse_zero})"
  by (simp add: Nsub_def split_def)

lemma Ninv[simp]: "INum (Ninv x) = (1::'a :: field_inverse_zero) / (INum x)"
  by (simp add: Ninv_def INum_def split_def)

lemma Ndiv[simp]: "INum (x \<div>\<^sub>N y) = INum x / (INum y ::'a :: {field_char_0, field_inverse_zero})"
  by (simp add: Ndiv_def)

lemma Nlt0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a :: {field_char_0, linordered_field_inverse_zero})< 0) = 0>\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  { assume "a = 0" hence ?thesis by (simp add: x Nlt0_def INum_def) }
  moreover
  { assume a: "a \<noteq> 0" hence b: "(of_int b::'a) > 0"
      using nx by (simp add: x isnormNum_def)
    from pos_divide_less_eq[OF b, where b="of_int a" and a="0::'a"]
    have ?thesis by (simp add: x Nlt0_def INum_def) }
  ultimately show ?thesis by blast
qed

lemma Nle0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a :: {field_char_0, linordered_field_inverse_zero}) \<le> 0) = 0\<ge>\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  { assume "a = 0" hence ?thesis by (simp add: x Nle0_def INum_def) }
  moreover
  { assume a: "a \<noteq> 0" hence b: "(of_int b :: 'a) > 0"
      using nx by (simp add: x isnormNum_def)
    from pos_divide_le_eq[OF b, where b="of_int a" and a="0::'a"]
    have ?thesis by (simp add: x Nle0_def INum_def) }
  ultimately show ?thesis by blast
qed

lemma Ngt0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a :: {field_char_0, linordered_field_inverse_zero})> 0) = 0<\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  { assume "a = 0" hence ?thesis by (simp add: x Ngt0_def INum_def) }
  moreover
  { assume a: "a \<noteq> 0" hence b: "(of_int b::'a) > 0" using nx
      by (simp add: x isnormNum_def)
    from pos_less_divide_eq[OF b, where b="of_int a" and a="0::'a"]
    have ?thesis by (simp add: x Ngt0_def INum_def) }
  ultimately show ?thesis by blast
qed

lemma Nge0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a :: {field_char_0, linordered_field_inverse_zero}) \<ge> 0) = 0\<le>\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  { assume "a = 0" hence ?thesis by (simp add: x Nge0_def INum_def) }
  moreover
  { assume "a \<noteq> 0" hence b: "(of_int b::'a) > 0" using nx
      by (simp add: x isnormNum_def)
    from pos_le_divide_eq[OF b, where b="of_int a" and a="0::'a"]
    have ?thesis by (simp add: x Nge0_def INum_def) }
  ultimately show ?thesis by blast
qed

lemma Nlt_iff[simp]:
  assumes nx: "isnormNum x" and ny: "isnormNum y"
  shows "((INum x :: 'a :: {field_char_0, linordered_field_inverse_zero}) < INum y) = (x <\<^sub>N y)"
proof -
  let ?z = "0::'a"
  have "((INum x ::'a) < INum y) = (INum (x -\<^sub>N y) < ?z)"
    using nx ny by simp
  also have "\<dots> = (0>\<^sub>N (x -\<^sub>N y))"
    using Nlt0_iff[OF Nsub_normN[OF ny]] by simp
  finally show ?thesis by (simp add: Nlt_def)
qed

lemma Nle_iff[simp]:
  assumes nx: "isnormNum x" and ny: "isnormNum y"
  shows "((INum x :: 'a :: {field_char_0, linordered_field_inverse_zero})\<le> INum y) = (x \<le>\<^sub>N y)"
proof -
  have "((INum x ::'a) \<le> INum y) = (INum (x -\<^sub>N y) \<le> (0::'a))"
    using nx ny by simp
  also have "\<dots> = (0\<ge>\<^sub>N (x -\<^sub>N y))"
    using Nle0_iff[OF Nsub_normN[OF ny]] by simp
  finally show ?thesis by (simp add: Nle_def)
qed

lemma Nadd_commute:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "x +\<^sub>N y = y +\<^sub>N x"
proof -
  have n: "isnormNum (x +\<^sub>N y)" "isnormNum (y +\<^sub>N x)" by simp_all
  have "(INum (x +\<^sub>N y)::'a) = INum (y +\<^sub>N x)" by simp
  with isnormNum_unique[OF n] show ?thesis by simp
qed

lemma [simp]:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "(0, b) +\<^sub>N y = normNum y"
    and "(a, 0) +\<^sub>N y = normNum y"
    and "x +\<^sub>N (0, b) = normNum x"
    and "x +\<^sub>N (a, 0) = normNum x"
  apply (simp add: Nadd_def split_def)
  apply (simp add: Nadd_def split_def)
  apply (subst Nadd_commute, simp add: Nadd_def split_def)
  apply (subst Nadd_commute, simp add: Nadd_def split_def)
  done

lemma normNum_nilpotent_aux[simp]:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  assumes nx: "isnormNum x"
  shows "normNum x = x"
proof -
  let ?a = "normNum x"
  have n: "isnormNum ?a" by simp
  have th: "INum ?a = (INum x ::'a)" by simp
  with isnormNum_unique[OF n nx] show ?thesis by simp
qed

lemma normNum_nilpotent[simp]:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "normNum (normNum x) = normNum x"
  by simp

lemma normNum0[simp]: "normNum (0,b) = 0\<^sub>N" "normNum (a,0) = 0\<^sub>N"
  by (simp_all add: normNum_def)

lemma normNum_Nadd:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "normNum (x +\<^sub>N y) = x +\<^sub>N y" by simp

lemma Nadd_normNum1[simp]:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "normNum x +\<^sub>N y = x +\<^sub>N y"
proof -
  have n: "isnormNum (normNum x +\<^sub>N y)" "isnormNum (x +\<^sub>N y)" by simp_all
  have "INum (normNum x +\<^sub>N y) = INum x + (INum y :: 'a)" by simp
  also have "\<dots> = INum (x +\<^sub>N y)" by simp
  finally show ?thesis using isnormNum_unique[OF n] by simp
qed

lemma Nadd_normNum2[simp]:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "x +\<^sub>N normNum y = x +\<^sub>N y"
proof -
  have n: "isnormNum (x +\<^sub>N normNum y)" "isnormNum (x +\<^sub>N y)" by simp_all
  have "INum (x +\<^sub>N normNum y) = INum x + (INum y :: 'a)" by simp
  also have "\<dots> = INum (x +\<^sub>N y)" by simp
  finally show ?thesis using isnormNum_unique[OF n] by simp
qed

lemma Nadd_assoc:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  shows "x +\<^sub>N y +\<^sub>N z = x +\<^sub>N (y +\<^sub>N z)"
proof -
  have n: "isnormNum (x +\<^sub>N y +\<^sub>N z)" "isnormNum (x +\<^sub>N (y +\<^sub>N z))" by simp_all
  have "INum (x +\<^sub>N y +\<^sub>N z) = (INum (x +\<^sub>N (y +\<^sub>N z)) :: 'a)" by simp
  with isnormNum_unique[OF n] show ?thesis by simp
qed

lemma Nmul_commute: "isnormNum x \<Longrightarrow> isnormNum y \<Longrightarrow> x *\<^sub>N y = y *\<^sub>N x"
  by (simp add: Nmul_def split_def Let_def gcd_commute_int mult_commute)

lemma Nmul_assoc:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  assumes nx: "isnormNum x" and ny: "isnormNum y" and nz: "isnormNum z"
  shows "x *\<^sub>N y *\<^sub>N z = x *\<^sub>N (y *\<^sub>N z)"
proof -
  from nx ny nz have n: "isnormNum (x *\<^sub>N y *\<^sub>N z)" "isnormNum (x *\<^sub>N (y *\<^sub>N z))"
    by simp_all
  have "INum (x +\<^sub>N y +\<^sub>N z) = (INum (x +\<^sub>N (y +\<^sub>N z)) :: 'a)" by simp
  with isnormNum_unique[OF n] show ?thesis by simp
qed

lemma Nsub0:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  assumes x: "isnormNum x" and y: "isnormNum y"
  shows "x -\<^sub>N y = 0\<^sub>N \<longleftrightarrow> x = y"
proof -
  fix h :: 'a
  from isnormNum_unique[where 'a = 'a, OF Nsub_normN[OF y], where y="0\<^sub>N"]
  have "(x -\<^sub>N y = 0\<^sub>N) = (INum (x -\<^sub>N y) = (INum 0\<^sub>N :: 'a)) " by simp
  also have "\<dots> = (INum x = (INum y :: 'a))" by simp
  also have "\<dots> = (x = y)" using x y by simp
  finally show ?thesis .
qed

lemma Nmul0[simp]: "c *\<^sub>N 0\<^sub>N = 0\<^sub>N" " 0\<^sub>N *\<^sub>N c = 0\<^sub>N"
  by (simp_all add: Nmul_def Let_def split_def)

lemma Nmul_eq0[simp]:
  assumes "SORT_CONSTRAINT('a::{field_char_0, field_inverse_zero})"
  assumes nx: "isnormNum x" and ny: "isnormNum y"
  shows "x*\<^sub>N y = 0\<^sub>N \<longleftrightarrow> x = 0\<^sub>N \<or> y = 0\<^sub>N"
proof -
  fix h :: 'a
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  have n0: "isnormNum 0\<^sub>N" by simp
  show ?thesis using nx ny
    apply (simp only: isnormNum_unique[where ?'a = 'a, OF  Nmul_normN[OF nx ny] n0, symmetric]
      Nmul[where ?'a = 'a])
    apply (simp add: x y INum_def split_def isnormNum_def split: split_if_asm)
    done
qed

lemma Nneg_Nneg[simp]: "~\<^sub>N (~\<^sub>N c) = c"
  by (simp add: Nneg_def split_def)

lemma Nmul1[simp]:
    "isnormNum c \<Longrightarrow> 1\<^sub>N *\<^sub>N c = c"
    "isnormNum c \<Longrightarrow> c *\<^sub>N (1\<^sub>N) = c"
  apply (simp_all add: Nmul_def Let_def split_def isnormNum_def)
  apply (cases "fst c = 0", simp_all, cases c, simp_all)+
  done

end
