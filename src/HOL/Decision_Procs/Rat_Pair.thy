(*  Title:      HOL/Decision_Procs/Rat_Pair.thy
    Author:     Amine Chaieb
*)

section \<open>Rational numbers as pairs\<close>

theory Rat_Pair
  imports Complex_Main
begin

type_synonym Num = "int \<times> int"

abbreviation Num0_syn :: Num  (\<open>0\<^sub>N\<close>)
  where "0\<^sub>N \<equiv> (0, 0)"

abbreviation Numi_syn :: "int \<Rightarrow> Num"  (\<open>'((_)')\<^sub>N\<close>)
  where "(i)\<^sub>N \<equiv> (i, 1)"

definition isnormNum :: "Num \<Rightarrow> bool"
  where "isnormNum = (\<lambda>(a, b). if a = 0 then b = 0 else b > 0 \<and> gcd a b = 1)"

definition normNum :: "Num \<Rightarrow> Num"
  where "normNum = (\<lambda>(a,b).
    (if a = 0 \<or> b = 0 then (0, 0)
     else
      (let g = gcd a b
       in if b > 0 then (a div g, b div g) else (- (a div g), - (b div g)))))"

declare gcd_dvd1[presburger] gcd_dvd2[presburger]

lemma normNum_isnormNum [simp]: "isnormNum (normNum x)"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  consider "a = 0 \<or> b = 0" | "a \<noteq> 0" "b \<noteq> 0"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp add: x normNum_def isnormNum_def)
  next
    case ab: 2
    let ?g = "gcd a b"
    let ?a' = "a div ?g"
    let ?b' = "b div ?g"
    let ?g' = "gcd ?a' ?b'"
    from ab have "?g \<noteq> 0" by simp
    with gcd_ge_0_int[of a b] have gpos: "?g > 0" by arith
    have gdvd: "?g dvd a" "?g dvd b" by arith+
    from dvd_mult_div_cancel[OF gdvd(1)] dvd_mult_div_cancel[OF gdvd(2)] ab
    have nz': "?a' \<noteq> 0" "?b' \<noteq> 0" by - (rule notI, simp)+
    from ab have stupid: "a \<noteq> 0 \<or> b \<noteq> 0" by arith
    from div_gcd_coprime[OF stupid] have gp1: "?g' = 1"
      by simp
    from ab consider "b < 0" | "b > 0" by arith
    then show ?thesis
    proof cases
      case b: 1
      have False if b': "?b' \<ge> 0"
      proof -
        from gpos have th: "?g \<ge> 0" by arith
        from mult_nonneg_nonneg[OF th b'] dvd_mult_div_cancel[OF gdvd(2)]
        show ?thesis using b by arith
      qed
      then have b': "?b' < 0" by (presburger add: linorder_not_le[symmetric])
      from ab(1) nz' b b' gp1 show ?thesis
        by (simp add: x isnormNum_def normNum_def Let_def split_def)
    next
      case b: 2
      then have "?b' \<ge> 0"
        by (presburger add: pos_imp_zdiv_nonneg_iff[OF gpos])
      with nz' have b': "?b' > 0" by arith
      from b b' ab(1) nz' gp1 show ?thesis
        by (simp add: x isnormNum_def normNum_def Let_def split_def)
    qed
  qed
qed

text \<open>Arithmetic over Num\<close>

definition Nadd :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl \<open>+\<^sub>N\<close> 60)
where
  "Nadd = (\<lambda>(a, b) (a', b').
    if a = 0 \<or> b = 0 then normNum (a', b')
    else if a' = 0 \<or> b' = 0 then normNum (a, b)
    else normNum (a * b' + b * a', b * b'))"

definition Nmul :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl \<open>*\<^sub>N\<close> 60)
where
  "Nmul = (\<lambda>(a, b) (a', b').
    let g = gcd (a * a') (b * b')
    in (a * a' div g, b * b' div g))"

definition Nneg :: "Num \<Rightarrow> Num" (\<open>~\<^sub>N\<close>)
  where "Nneg = (\<lambda>(a, b). (- a, b))"

definition Nsub :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl \<open>-\<^sub>N\<close> 60)
  where "Nsub = (\<lambda>a b. a +\<^sub>N ~\<^sub>N b)"

definition Ninv :: "Num \<Rightarrow> Num"
  where "Ninv = (\<lambda>(a, b). if a < 0 then (- b, \<bar>a\<bar>) else (b, a))"

definition Ndiv :: "Num \<Rightarrow> Num \<Rightarrow> Num"  (infixl \<open>\<div>\<^sub>N\<close> 60)
  where "Ndiv = (\<lambda>a b. a *\<^sub>N Ninv b)"

lemma Nneg_normN[simp]: "isnormNum x \<Longrightarrow> isnormNum (~\<^sub>N x)"
  by (simp add: isnormNum_def Nneg_def split_def)

lemma Nadd_normN[simp]: "isnormNum (x +\<^sub>N y)"
  by (simp add: Nadd_def split_def)

lemma Nsub_normN[simp]: "isnormNum y \<Longrightarrow> isnormNum (x -\<^sub>N y)"
  by (simp add: Nsub_def split_def)

lemma Nmul_normN[simp]:
  assumes xn: "isnormNum x"
    and yn: "isnormNum y"
  shows "isnormNum (x *\<^sub>N y)"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  consider "a = 0" | "a' = 0" | "a \<noteq> 0" "a' \<noteq> 0" by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using xn x y by (simp add: isnormNum_def Let_def Nmul_def split_def)
  next
    case 2
    then show ?thesis
      using yn x y by (simp add: isnormNum_def Let_def Nmul_def split_def)
  next
    case aa': 3
    then have bp: "b > 0" "b' > 0"
      using xn yn x y by (simp_all add: isnormNum_def)
    from bp have "x *\<^sub>N y = normNum (a * a', b * b')"
      using x y aa' bp by (simp add: Nmul_def Let_def split_def normNum_def)
    then show ?thesis by simp
  qed
qed

lemma Ninv_normN[simp]: "isnormNum x \<Longrightarrow> isnormNum (Ninv x)"
  by (simp add: Ninv_def isnormNum_def split_def gcd.commute split: if_split_asm)

lemma isnormNum_int[simp]: "isnormNum 0\<^sub>N" "isnormNum ((1::int)\<^sub>N)" "i \<noteq> 0 \<Longrightarrow> isnormNum (i)\<^sub>N"
  by (simp_all add: isnormNum_def)


text \<open>Relations over Num\<close>

definition Nlt0:: "Num \<Rightarrow> bool"  (\<open>0>\<^sub>N\<close>)
  where "Nlt0 = (\<lambda>(a, b). a < 0)"

definition Nle0:: "Num \<Rightarrow> bool"  (\<open>0\<ge>\<^sub>N\<close>)
  where "Nle0 = (\<lambda>(a, b). a \<le> 0)"

definition Ngt0:: "Num \<Rightarrow> bool"  (\<open>0<\<^sub>N\<close>)
  where "Ngt0 = (\<lambda>(a, b). a > 0)"

definition Nge0:: "Num \<Rightarrow> bool"  (\<open>0\<le>\<^sub>N\<close>)
  where "Nge0 = (\<lambda>(a, b). a \<ge> 0)"

definition Nlt :: "Num \<Rightarrow> Num \<Rightarrow> bool"  (infix \<open><\<^sub>N\<close> 55)
  where "Nlt = (\<lambda>a b. 0>\<^sub>N (a -\<^sub>N b))"

definition Nle :: "Num \<Rightarrow> Num \<Rightarrow> bool"  (infix \<open>\<le>\<^sub>N\<close> 55)
  where "Nle = (\<lambda>a b. 0\<ge>\<^sub>N (a -\<^sub>N b))"

definition "INum = (\<lambda>(a, b). of_int a / of_int b)"

lemma INum_int [simp]: "INum (i)\<^sub>N = (of_int i ::'a::field)" "INum 0\<^sub>N = (0::'a::field)"
  by (simp_all add: INum_def)

lemma isnormNum_unique[simp]:
  assumes na: "isnormNum x"
    and nb: "isnormNum y"
  shows "(INum x ::'a::field_char_0) = INum y \<longleftrightarrow> x = y"
  (is "?lhs = ?rhs")
proof
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  consider "a = 0 \<or> b = 0 \<or> a' = 0 \<or> b' = 0" | "a \<noteq> 0" "b \<noteq> 0" "a' \<noteq> 0" "b' \<noteq> 0"
    by blast
  then show ?rhs if H: ?lhs
  proof cases
    case 1
    then show ?thesis
      using na nb H by (simp add: x y INum_def split_def isnormNum_def split: if_split_asm)
  next
    case 2
    with na nb have pos: "b > 0" "b' > 0"
      by (simp_all add: x y isnormNum_def)
    from H \<open>b \<noteq> 0\<close> \<open>b' \<noteq> 0\<close> have eq: "a * b' = a' * b"
      by (simp add: x y INum_def eq_divide_eq divide_eq_eq of_int_mult[symmetric] del: of_int_mult)
    from \<open>a \<noteq> 0\<close> \<open>a' \<noteq> 0\<close> na nb
    have gcd1: "gcd a b = 1" "gcd b a = 1" "gcd a' b' = 1" "gcd b' a' = 1"
      by (simp_all add: x y isnormNum_def add: gcd.commute)
    then have "coprime a b" "coprime b a" "coprime a' b'" "coprime b' a'"
      by (simp_all add: coprime_iff_gcd_eq_1)
    from eq have raw_dvd: "a dvd a' * b" "b dvd b' * a" "a' dvd a * b'" "b' dvd b * a'"
      by (algebra|simp)+
    then have eq1: "b = b'"
      using pos \<open>coprime b a\<close> \<open>coprime b' a'\<close>
      by (auto simp add: coprime_dvd_mult_left_iff intro: associated_eqI)
    with eq have "a = a'" using pos by simp
    with \<open>b = b'\<close> show ?thesis by (simp add: x y)
  qed
  show ?lhs if ?rhs
    using that by simp
qed

lemma isnormNum0[simp]: "isnormNum x \<Longrightarrow> INum x = (0::'a::field_char_0) \<longleftrightarrow> x = 0\<^sub>N"
  unfolding INum_int(2)[symmetric]
  by (rule isnormNum_unique) simp_all

lemma of_int_div_aux:
  assumes "d \<noteq> 0"
  shows "(of_int x ::'a::field_char_0) / of_int d =
    of_int (x div d) + (of_int (x mod d)) / of_int d"
proof -
  let ?t = "of_int (x div d) * (of_int d ::'a) + of_int (x mod d)"
  let ?f = "\<lambda>x. x / of_int d"
  have "x = (x div d) * d + x mod d"
    by auto
  then have eq: "of_int x = ?t"
    by (simp only: of_int_mult[symmetric] of_int_add [symmetric])
  then have "of_int x / of_int d = ?t / of_int d"
    using cong[OF refl[of ?f] eq] by simp
  then show ?thesis
    by (simp add: add_divide_distrib algebra_simps \<open>d \<noteq> 0\<close>)
qed

lemma of_int_div:
  fixes d :: int
  assumes "d \<noteq> 0" "d dvd n"
  shows "(of_int (n div d) ::'a::field_char_0) = of_int n / of_int d"
  using assms of_int_div_aux [of d n, where ?'a = 'a] by simp

lemma normNum[simp]: "INum (normNum x) = (INum x :: 'a::field_char_0)"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  consider "a = 0 \<or> b = 0" | "a \<noteq> 0" "b \<noteq> 0" by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp add: x INum_def normNum_def split_def Let_def)
  next
    case ab: 2
    let ?g = "gcd a b"
    from ab have g: "?g \<noteq> 0"by simp
    from of_int_div[OF g, where ?'a = 'a] show ?thesis
      by (auto simp add: x INum_def normNum_def split_def Let_def)
  qed
qed

lemma INum_normNum_iff: "(INum x ::'a::field_char_0) = INum y \<longleftrightarrow> normNum x = normNum y"
  (is "?lhs \<longleftrightarrow> _")
proof -
  have "normNum x = normNum y \<longleftrightarrow> (INum (normNum x) :: 'a) = INum (normNum y)"
    by (simp del: normNum)
  also have "\<dots> = ?lhs" by simp
  finally show ?thesis by simp
qed

lemma Nadd[simp]: "INum (x +\<^sub>N y) = INum x + (INum y :: 'a :: field_char_0)"
proof -
  let ?z = "0::'a"
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  consider "a = 0 \<or> a'= 0 \<or> b =0 \<or> b' = 0" | "a \<noteq> 0" "a'\<noteq> 0" "b \<noteq> 0" "b' \<noteq> 0"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (auto simp: x y INum_def Nadd_def normNum_def Let_def of_int_div)
  next
    case neq: 2
    show ?thesis
    proof (cases "a * b' + b * a' = 0")
      case True
      then have "of_int (a * b' + b * a') / (of_int b * of_int b') = ?z"
        by simp
      then have "of_int b' * of_int a / (of_int b * of_int b') +
          of_int b * of_int a' / (of_int b * of_int b') = ?z"
        by (simp add: add_divide_distrib)
      then have th: "of_int a / of_int b + of_int a' / of_int b' = ?z"
        using neq by simp
      from True neq show ?thesis
        by (simp add: x y th Nadd_def normNum_def INum_def split_def)
    next
      case False
      let ?g = "gcd (a * b' + b * a') (b * b')"
      have gz: "?g \<noteq> 0"
        using False by simp
      show ?thesis
        using neq False gz
          of_int_div [where ?'a = 'a, OF gz gcd_dvd1 [of "a * b' + b * a'" "b * b'"]]
          of_int_div [where ?'a = 'a, OF gz gcd_dvd2 [of "a * b' + b * a'" "b * b'"]]
        by (simp add: x y Nadd_def INum_def normNum_def Let_def) (simp add: field_simps)
    qed
  qed
qed

lemma Nmul[simp]: "INum (x *\<^sub>N y) = INum x * (INum y:: 'a::field_char_0)"
proof -
  let ?z = "0::'a"
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  consider "a = 0 \<or> a' = 0 \<or> b = 0 \<or> b' = 0" | "a \<noteq> 0" "a' \<noteq> 0" "b \<noteq> 0" "b' \<noteq> 0"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (auto simp add: x y Nmul_def INum_def)
  next
    case neq: 2
    let ?g = "gcd (a * a') (b * b')"
    have gz: "?g \<noteq> 0"
      using neq by simp
    from neq of_int_div [where ?'a = 'a, OF gz gcd_dvd1 [of "a * a'" "b * b'"]]
      of_int_div [where ?'a = 'a , OF gz gcd_dvd2 [of "a * a'" "b * b'"]]
    show ?thesis
      by (simp add: Nmul_def x y Let_def INum_def)
  qed
qed

lemma Nneg[simp]: "INum (~\<^sub>N x) = - (INum x :: 'a::field)"
  by (simp add: Nneg_def split_def INum_def)

lemma Nsub[simp]: "INum (x -\<^sub>N y) = INum x - (INum y:: 'a::field_char_0)"
  by (simp add: Nsub_def split_def)

lemma Ninv[simp]: "INum (Ninv x) = (1 :: 'a::field) / INum x"
  by (simp add: Ninv_def INum_def split_def)

lemma Ndiv[simp]: "INum (x \<div>\<^sub>N y) = INum x / (INum y :: 'a::field_char_0)"
  by (simp add: Ndiv_def)

lemma Nlt0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a::{field_char_0,linordered_field}) < 0) = 0>\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  show ?thesis
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: x Nlt0_def INum_def)
  next
    case False
    then have b: "(of_int b::'a) > 0"
      using nx by (simp add: x isnormNum_def)
    from pos_divide_less_eq[OF b, where b="of_int a" and a="0::'a"]
    show ?thesis
      by (simp add: x Nlt0_def INum_def)
  qed
qed

lemma Nle0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a::{field_char_0,linordered_field}) \<le> 0) = 0\<ge>\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  show ?thesis
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: x Nle0_def INum_def)
  next
    case False
    then have b: "(of_int b :: 'a) > 0"
      using nx by (simp add: x isnormNum_def)
    from pos_divide_le_eq[OF b, where b="of_int a" and a="0::'a"]
    show ?thesis
      by (simp add: x Nle0_def INum_def)
  qed
qed

lemma Ngt0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "((INum x :: 'a::{field_char_0,linordered_field}) > 0) = 0<\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  show ?thesis
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: x Ngt0_def INum_def)
  next
    case False
    then have b: "(of_int b::'a) > 0"
      using nx by (simp add: x isnormNum_def)
    from pos_less_divide_eq[OF b, where b="of_int a" and a="0::'a"]
    show ?thesis
      by (simp add: x Ngt0_def INum_def)
  qed
qed

lemma Nge0_iff[simp]:
  assumes nx: "isnormNum x"
  shows "(INum x :: 'a::{field_char_0,linordered_field}) \<ge> 0 \<longleftrightarrow> 0\<le>\<^sub>N x"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  show ?thesis
  proof (cases "a = 0")
    case True
    then show ?thesis
      by (simp add: x Nge0_def INum_def)
  next
    case False
    then have b: "(of_int b::'a) > 0"
      using nx by (simp add: x isnormNum_def)
    from pos_le_divide_eq[OF b, where b="of_int a" and a="0::'a"]
    show ?thesis
      by (simp add: x Nge0_def INum_def)
  qed
qed

lemma Nlt_iff[simp]:
  assumes nx: "isnormNum x"
    and ny: "isnormNum y"
  shows "((INum x :: 'a::{field_char_0,linordered_field}) < INum y) \<longleftrightarrow> x <\<^sub>N y"
proof -
  let ?z = "0::'a"
  have "((INum x ::'a) < INum y) \<longleftrightarrow> INum (x -\<^sub>N y) < ?z"
    using nx ny by simp
  also have "\<dots> \<longleftrightarrow> 0>\<^sub>N (x -\<^sub>N y)"
    using Nlt0_iff[OF Nsub_normN[OF ny]] by simp
  finally show ?thesis
    by (simp add: Nlt_def)
qed

lemma Nle_iff[simp]:
  assumes nx: "isnormNum x"
    and ny: "isnormNum y"
  shows "((INum x :: 'a::{field_char_0,linordered_field}) \<le> INum y) \<longleftrightarrow> x \<le>\<^sub>N y"
proof -
  have "((INum x ::'a) \<le> INum y) \<longleftrightarrow> INum (x -\<^sub>N y) \<le> (0::'a)"
    using nx ny by simp
  also have "\<dots> \<longleftrightarrow> 0\<ge>\<^sub>N (x -\<^sub>N y)"
    using Nle0_iff[OF Nsub_normN[OF ny]] by simp
  finally show ?thesis
    by (simp add: Nle_def)
qed

lemma Nadd_commute:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "x +\<^sub>N y = y +\<^sub>N x"
proof -
  have n: "isnormNum (x +\<^sub>N y)" "isnormNum (y +\<^sub>N x)"
    by simp_all
  have "(INum (x +\<^sub>N y)::'a) = INum (y +\<^sub>N x)"
    by simp
  with isnormNum_unique[OF n] show ?thesis
    by simp
qed

lemma [simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "(0, b) +\<^sub>N y = normNum y"
    and "(a, 0) +\<^sub>N y = normNum y"
    and "x +\<^sub>N (0, b) = normNum x"
    and "x +\<^sub>N (a, 0) = normNum x"
  by (simp_all add: Nadd_def normNum_def split_def)

lemma normNum_nilpotent_aux[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  assumes nx: "isnormNum x"
  shows "normNum x = x"
proof -
  let ?a = "normNum x"
  have n: "isnormNum ?a" by simp
  have th: "INum ?a = (INum x ::'a)" by simp
  with isnormNum_unique[OF n nx] show ?thesis by simp
qed

lemma normNum_nilpotent[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "normNum (normNum x) = normNum x"
  by simp

lemma normNum0[simp]: "normNum (0, b) = 0\<^sub>N" "normNum (a, 0) = 0\<^sub>N"
  by (simp_all add: normNum_def)

lemma normNum_Nadd:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "normNum (x +\<^sub>N y) = x +\<^sub>N y"
  by simp

lemma Nadd_normNum1[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "normNum x +\<^sub>N y = x +\<^sub>N y"
proof -
  have n: "isnormNum (normNum x +\<^sub>N y)" "isnormNum (x +\<^sub>N y)"
    by simp_all
  have "INum (normNum x +\<^sub>N y) = INum x + (INum y :: 'a)"
    by simp
  also have "\<dots> = INum (x +\<^sub>N y)"
    by simp
  finally show ?thesis
    using isnormNum_unique[OF n] by simp
qed

lemma Nadd_normNum2[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "x +\<^sub>N normNum y = x +\<^sub>N y"
proof -
  have n: "isnormNum (x +\<^sub>N normNum y)" "isnormNum (x +\<^sub>N y)"
    by simp_all
  have "INum (x +\<^sub>N normNum y) = INum x + (INum y :: 'a)"
    by simp
  also have "\<dots> = INum (x +\<^sub>N y)"
    by simp
  finally show ?thesis
    using isnormNum_unique[OF n] by simp
qed

lemma Nadd_assoc:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "x +\<^sub>N y +\<^sub>N z = x +\<^sub>N (y +\<^sub>N z)"
proof -
  have n: "isnormNum (x +\<^sub>N y +\<^sub>N z)" "isnormNum (x +\<^sub>N (y +\<^sub>N z))"
    by simp_all
  have "INum (x +\<^sub>N y +\<^sub>N z) = (INum (x +\<^sub>N (y +\<^sub>N z)) :: 'a)"
    by simp
  with isnormNum_unique[OF n] show ?thesis
    by simp
qed

lemma Nmul_commute: "isnormNum x \<Longrightarrow> isnormNum y \<Longrightarrow> x *\<^sub>N y = y *\<^sub>N x"
  by (simp add: Nmul_def split_def Let_def gcd.commute mult.commute)

lemma Nmul_assoc:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  assumes nx: "isnormNum x"
    and ny: "isnormNum y"
    and nz: "isnormNum z"
  shows "x *\<^sub>N y *\<^sub>N z = x *\<^sub>N (y *\<^sub>N z)"
proof -
  from nx ny nz have n: "isnormNum (x *\<^sub>N y *\<^sub>N z)" "isnormNum (x *\<^sub>N (y *\<^sub>N z))"
    by simp_all
  have "INum (x +\<^sub>N y +\<^sub>N z) = (INum (x +\<^sub>N (y +\<^sub>N z)) :: 'a)"
    by simp
  with isnormNum_unique[OF n] show ?thesis
    by simp
qed

lemma Nsub0:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  assumes x: "isnormNum x"
    and y: "isnormNum y"
  shows "x -\<^sub>N y = 0\<^sub>N \<longleftrightarrow> x = y"
proof -
  from isnormNum_unique[where 'a = 'a, OF Nsub_normN[OF y], where y="0\<^sub>N"]
  have "x -\<^sub>N y = 0\<^sub>N \<longleftrightarrow> INum (x -\<^sub>N y) = (INum 0\<^sub>N :: 'a)"
    by simp
  also have "\<dots> \<longleftrightarrow> INum x = (INum y :: 'a)"
    by simp
  also have "\<dots> \<longleftrightarrow> x = y"
    using x y by simp
  finally show ?thesis .
qed

lemma Nmul0[simp]: "c *\<^sub>N 0\<^sub>N = 0\<^sub>N" " 0\<^sub>N *\<^sub>N c = 0\<^sub>N"
  by (simp_all add: Nmul_def Let_def split_def)

lemma Nmul_eq0[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  assumes nx: "isnormNum x"
    and ny: "isnormNum y"
  shows "x*\<^sub>N y = 0\<^sub>N \<longleftrightarrow> x = 0\<^sub>N \<or> y = 0\<^sub>N"
proof -
  obtain a b where x: "x = (a, b)" by (cases x)
  obtain a' b' where y: "y = (a', b')" by (cases y)
  have n0: "isnormNum 0\<^sub>N" by simp
  show ?thesis using nx ny
    by (metis (no_types, opaque_lifting) INum_int(2) Nmul Nmul0(1) Nmul0(2) isnormNum0 mult_eq_0_iff)
qed

lemma Nneg_Nneg[simp]: "~\<^sub>N (~\<^sub>N c) = c"
  by (simp add: Nneg_def split_def)

lemma Nmul1[simp]: "isnormNum c \<Longrightarrow> (1)\<^sub>N *\<^sub>N c = c" "isnormNum c \<Longrightarrow> c *\<^sub>N (1)\<^sub>N = c"
  by (simp add: Nmul_def Let_def split_def isnormNum_def, metis div_0 div_by_1 surjective_pairing)+

end
