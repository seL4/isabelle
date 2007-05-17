(*  Title:      HOL/Library/Executable_Real.thy
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Implementation of rational real numbers as pairs of integers *}

theory Executable_Real
imports GCD "~~/src/HOL/Real/Real"
begin

subsection {* Implementation of operations on pair of integers *}

types Num = "int * int"
syntax "_Num0" :: "Num" ("0\<^sub>N")
translations "0\<^sub>N" \<rightleftharpoons> "(0,0)"
syntax "_Numi" :: "int \<Rightarrow> Num" ("_\<^sub>N")
translations "i\<^sub>N" \<rightleftharpoons> "(i,1)::Num"

constdefs isnormNum :: "Num \<Rightarrow> bool"
  "isnormNum \<equiv> \<lambda>(a,b). (if a = 0 then b = 0 else b > 0 \<and> igcd a b = 1)"

constdefs normNum :: "Num \<Rightarrow> Num"
  "normNum \<equiv> \<lambda>(a,b). (if a=0 \<or> b = 0 then (0,0) else 
  (let g = igcd a b 
   in if b > 0 then (a div g, b div g) else (- (a div g), - (b div g))))"
lemma normNum_isnormNum[simp]: "isnormNum (normNum x)"
proof-
  have " \<exists> a b. x = (a,b)" by auto
  then obtain a b where x[simp]: "x = (a,b)" by blast
  {assume "a=0 \<or> b = 0" hence ?thesis by (simp add: normNum_def isnormNum_def)}  
  moreover
  {assume anz: "a \<noteq> 0" and bnz: "b \<noteq> 0" 
    let ?g = "igcd a b"
    let ?a' = "a div ?g"
    let ?b' = "b div ?g"
    let ?g' = "igcd ?a' ?b'"
    from anz bnz have "?g \<noteq> 0" by simp  with igcd_pos[of a b] 
    have gpos: "?g > 0"  by arith
    have gdvd: "?g dvd a" "?g dvd b" by (simp_all add: igcd_dvd1 igcd_dvd2)
    from zdvd_mult_div_cancel[OF gdvd(1)] zdvd_mult_div_cancel[OF gdvd(2)]
    anz bnz
    have nz':"?a' \<noteq> 0" "?b' \<noteq> 0" 
      by - (rule notI,simp add:igcd_def)+
    from anz bnz have stupid: "a \<noteq> 0 \<or> b \<noteq> 0" by blast
    from div_igcd_relprime[OF stupid] have gp1: "?g' = 1" .
    from bnz have "b < 0 \<or> b > 0" by arith
    moreover
    {assume b: "b > 0"
      from pos_imp_zdiv_nonneg_iff[OF gpos] b
      have "?b' \<ge> 0" by simp
      with nz' have b': "?b' > 0" by simp
      from b b' anz bnz nz' gp1 have ?thesis 
	by (simp add: isnormNum_def normNum_def Let_def split_def fst_conv snd_conv)}
    moreover {assume b: "b < 0"
      {assume b': "?b' \<ge> 0" 
	from gpos have th: "?g \<ge> 0" by arith
	from mult_nonneg_nonneg[OF th b'] zdvd_mult_div_cancel[OF gdvd(2)]
	have False using b by simp }
      hence b': "?b' < 0" by arith
      from anz bnz nz' b b' gp1 have ?thesis 
	by (simp add: isnormNum_def normNum_def Let_def split_def fst_conv snd_conv)}
    ultimately have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed
    (* Arithmetic over Num *)
constdefs Nadd :: "Num \<Rightarrow> Num \<Rightarrow> Num" (infixl "+\<^sub>N" 60)
  "Nadd \<equiv> \<lambda>(a,b) (a',b'). if a = 0 \<or> b = 0 then normNum(a',b') 
  else if a'=0 \<or> b' = 0 then normNum(a,b) 
  else normNum(a*b' + b*a', b*b')"
constdefs Nmul :: "Num \<Rightarrow> Num \<Rightarrow> Num" (infixl "*\<^sub>N" 60)
  "Nmul \<equiv> \<lambda>(a,b) (a',b'). let g = igcd (a*a') (b*b') 
  in (a*a' div g, b*b' div g)"
constdefs Nneg :: "Num \<Rightarrow> Num" ("~\<^sub>N")
  "Nneg \<equiv> \<lambda>(a,b). (-a,b)"
constdefs  Nsub :: "Num \<Rightarrow> Num \<Rightarrow> Num" (infixl "-\<^sub>N" 60)
  "Nsub \<equiv> \<lambda>a b. a +\<^sub>N ~\<^sub>N b"
constdefs Ninv :: "Num \<Rightarrow> Num" 
"Ninv \<equiv> \<lambda>(a,b). if a < 0 then (-b, \<bar>a\<bar>) else (b,a)"
constdefs Ndiv :: "Num \<Rightarrow> Num \<Rightarrow> Num" (infixl "\<div>\<^sub>N" 60)
  "Ndiv \<equiv> \<lambda>a b. a *\<^sub>N Ninv b"

lemma Nneg_normN[simp]: "isnormNum x \<Longrightarrow> isnormNum (~\<^sub>N x)"
  by(simp add: isnormNum_def Nneg_def split_def)
lemma Nadd_normN[simp]: "isnormNum (x +\<^sub>N y)"
  by (simp add: Nadd_def split_def)
lemma Nsub_normN[simp]: "\<lbrakk> isnormNum y\<rbrakk> \<Longrightarrow> isnormNum (x -\<^sub>N y)"
  by (simp add: Nsub_def split_def)
lemma Nmul_normN[simp]: assumes xn:"isnormNum x" and yn: "isnormNum y"
  shows "isnormNum (x *\<^sub>N y)"
proof-
  have "\<exists>a b. x = (a,b)" and "\<exists> a' b'. y = (a',b')" by auto
  then obtain a b a' b' where ab: "x = (a,b)"  and ab': "y = (a',b')" by blast 
  {assume "a = 0"
    hence ?thesis using xn ab ab'
      by (simp add: igcd_def isnormNum_def Let_def Nmul_def split_def)}
  moreover
  {assume "a' = 0"
    hence ?thesis using yn ab ab' 
      by (simp add: igcd_def isnormNum_def Let_def Nmul_def split_def)}
  moreover
  {assume a: "a \<noteq>0" and a': "a'\<noteq>0"
    hence bp: "b > 0" "b' > 0" using xn yn ab ab' by (simp_all add: isnormNum_def)
    from mult_pos_pos[OF bp] have "x *\<^sub>N y = normNum (a*a', b*b')" 
      using ab ab' a a' bp by (simp add: Nmul_def Let_def split_def normNum_def)
    hence ?thesis by simp}
  ultimately show ?thesis by blast
qed

lemma Ninv_normN[simp]: "isnormNum x \<Longrightarrow> isnormNum (Ninv x)"
by (simp add: Ninv_def isnormNum_def split_def)
(cases "fst x = 0",auto simp add: igcd_commute)

lemma isnormNum_int[simp]: 
  "isnormNum 0\<^sub>N" "isnormNum (1::int)\<^sub>N" "i \<noteq> 0 \<Longrightarrow> isnormNum i\<^sub>N"
 by (simp_all add: isnormNum_def igcd_def)

    (* Relations over Num *)
constdefs Nlt0:: "Num \<Rightarrow> bool" ("0>\<^sub>N")
  "Nlt0 \<equiv> \<lambda>(a,b). a < 0"
constdefs Nle0:: "Num \<Rightarrow> bool" ("0\<ge>\<^sub>N")
  "Nle0 \<equiv> \<lambda>(a,b). a \<le> 0"
constdefs Ngt0:: "Num \<Rightarrow> bool" ("0<\<^sub>N")
  "Ngt0 \<equiv> \<lambda>(a,b). a > 0"
constdefs Nge0:: "Num \<Rightarrow> bool" ("0\<le>\<^sub>N")
  "Nge0 \<equiv> \<lambda>(a,b). a \<ge> 0"
constdefs Nlt :: "Num \<Rightarrow> Num \<Rightarrow> bool" (infix "<\<^sub>N" 55)
  "Nlt \<equiv> \<lambda>a b. 0>\<^sub>N (a -\<^sub>N b)"
constdefs Nle :: "Num \<Rightarrow> Num \<Rightarrow> bool" (infix "\<le>\<^sub>N" 55)
  "Nle \<equiv> \<lambda>a b. 0\<ge>\<^sub>N (a -\<^sub>N b)"


subsection {* Interpretation of the normalized rats in reals *}

definition
  INum:: "Num \<Rightarrow> real"
where
  INum_def: "INum \<equiv> \<lambda>(a,b). real a / real b"

code_datatype INum
instance real :: eq ..

definition
  real_int :: "int \<Rightarrow> real"
where
  "real_int = real"
lemmas [code unfold] = real_int_def [symmetric]

lemma [code unfold]:
  "real = real_int o int"
  by (auto simp add: real_int_def expand_fun_eq)

lemma INum_int [simp]: "INum i\<^sub>N = real i" "INum 0\<^sub>N = 0"
  by (simp_all add: INum_def)
lemmas [code, code unfold] = INum_int [unfolded real_int_def [symmetric], symmetric]

lemma [code, code unfold]: "1 = INum 1\<^sub>N" by simp

lemma isnormNum_unique[simp]: 
  assumes na: "isnormNum x" and nb: "isnormNum y" 
  shows "(INum x = INum y) = (x = y)" (is "?lhs = ?rhs")
proof
  have "\<exists> a b a' b'. x = (a,b) \<and> y = (a',b')" by auto
  then obtain a b a' b' where xy[simp]: "x = (a,b)" "y=(a',b')" by blast
  assume H: ?lhs 
  {assume "a = 0 \<or> b = 0 \<or> a' = 0 \<or> b' = 0" hence ?rhs
      using na nb H
      by (simp add: INum_def split_def isnormNum_def)
       (cases "a = 0", simp_all,cases "b = 0", simp_all,
      cases "a' = 0", simp_all,cases "a' = 0", simp_all)}
  moreover
  { assume az: "a \<noteq> 0" and bz: "b \<noteq> 0" and a'z: "a'\<noteq>0" and b'z: "b'\<noteq>0"
    from az bz a'z b'z na nb have pos: "b > 0" "b' > 0" by (simp_all add: isnormNum_def)
    from prems have eq:"a * b' = a'*b" 
      by (simp add: INum_def  eq_divide_eq divide_eq_eq real_of_int_mult[symmetric] del: real_of_int_mult)
    from prems have gcd1: "igcd a b = 1" "igcd b a = 1" "igcd a' b' = 1" "igcd b' a' = 1"       
      by (simp_all add: isnormNum_def add: igcd_commute)
    from eq have raw_dvd: "a dvd a'*b" "b dvd b'*a" "a' dvd a*b'" "b' dvd b*a'" 
      apply(unfold dvd_def)
      apply (rule_tac x="b'" in exI, simp add: mult_ac)
      apply (rule_tac x="a'" in exI, simp add: mult_ac)
      apply (rule_tac x="b" in exI, simp add: mult_ac)
      apply (rule_tac x="a" in exI, simp add: mult_ac)
      done
    from zdvd_dvd_eq[OF bz zrelprime_dvd_mult[OF gcd1(2) raw_dvd(2)]
      zrelprime_dvd_mult[OF gcd1(4) raw_dvd(4)]]
      have eq1: "b = b'" using pos by simp_all
      with eq have "a = a'" using pos by simp
      with eq1 have ?rhs by simp}
  ultimately show ?rhs by blast
next
  assume ?rhs thus ?lhs by simp
qed


lemma isnormNum0[simp]: "isnormNum x \<Longrightarrow> (INum x = 0) = (x = 0\<^sub>N)"
  unfolding INum_int(2)[symmetric]
  by (rule isnormNum_unique, simp_all)

lemma normNum[simp]: "INum (normNum x) = INum x"
proof-
  have "\<exists> a b. x = (a,b)" by auto
  then obtain a b where x[simp]: "x = (a,b)" by blast
  {assume "a=0 \<or> b = 0" hence ?thesis
      by (simp add: INum_def normNum_def split_def Let_def)}
  moreover 
  {assume a: "a\<noteq>0" and b: "b\<noteq>0"
    let ?g = "igcd a b"
    from a b have g: "?g \<noteq> 0"by simp
    from real_of_int_div[OF g]
    have ?thesis by (simp add: INum_def normNum_def split_def Let_def)}
  ultimately show ?thesis by blast
qed

lemma INum_normNum_iff [code]: "INum x = INum y \<longleftrightarrow> normNum x = normNum y" (is "?lhs = ?rhs")
proof -
  have "normNum x = normNum y \<longleftrightarrow> INum (normNum x) = INum (normNum y)"
    by (simp del: normNum)
  also have "\<dots> = ?lhs" by simp
  finally show ?thesis by simp
qed

lemma Nadd[simp]: "INum (x +\<^sub>N y) = INum x + INum y"
proof-
  have " \<exists> a b. x = (a,b)" " \<exists> a' b'. y = (a',b')" by auto
  then obtain a b a' b' where x[simp]: "x = (a,b)" 
    and y[simp]: "y = (a',b')" by blast
  {assume "a=0 \<or> a'= 0 \<or> b =0 \<or> b' = 0" hence ?thesis 
      apply (cases "a=0",simp_all add: Nadd_def)
      apply (cases "b= 0",simp_all add: INum_def)
       apply (cases "a'= 0",simp_all)
       apply (cases "b'= 0",simp_all)
       done }
  moreover 
  {assume aa':"a \<noteq> 0" "a'\<noteq> 0" and bb': "b \<noteq> 0" "b' \<noteq> 0" 
    {assume z: "a * b' + b * a' = 0"
      hence "real (a*b' + b*a') / (real b* real b') = 0" by simp
      hence "real b' * real a / (real b * real b') + real b * real a' / (real b * real b') = 0"  by (simp add:add_divide_distrib) 
      hence th: "real a / real b + real a' / real b' = 0" using bb' aa' by simp 
      from z aa' bb' have ?thesis 
	by (simp add: th Nadd_def normNum_def INum_def split_def)}
    moreover {assume z: "a * b' + b * a' \<noteq> 0"
      let ?g = "igcd (a * b' + b * a') (b*b')"
      have gz: "?g \<noteq> 0" using z by simp
      have ?thesis using aa' bb' z gz
	real_of_int_div[OF gz igcd_dvd1[where i="a * b' + b * a'" and j="b*b'"]]
	real_of_int_div[OF gz igcd_dvd2[where i="a * b' + b * a'" and j="b*b'"]]
	by (simp add: x y Nadd_def INum_def normNum_def Let_def add_divide_distrib)}
    ultimately have ?thesis using aa' bb' 
      by (simp add: Nadd_def INum_def normNum_def x y Let_def) }
  ultimately show ?thesis by blast
qed
lemmas [code] = Nadd [symmetric]

lemma Nmul[simp]: "INum (x *\<^sub>N y) = INum x * INum y"
proof-
  have " \<exists> a b. x = (a,b)" " \<exists> a' b'. y = (a',b')" by auto
  then obtain a b a' b' where x: "x = (a,b)" and y: "y = (a',b')" by blast
  {assume "a=0 \<or> a'= 0 \<or> b = 0 \<or> b' = 0" hence ?thesis 
      apply (cases "a=0",simp_all add: x y Nmul_def INum_def Let_def)
      apply (cases "b=0",simp_all)
      apply (cases "a'=0",simp_all) 
      done }
  moreover
  {assume z: "a \<noteq> 0" "a' \<noteq> 0" "b \<noteq> 0" "b' \<noteq> 0"
    let ?g="igcd (a*a') (b*b')"
    have gz: "?g \<noteq> 0" using z by simp
    from z real_of_int_div[OF gz igcd_dvd1[where i="a*a'" and j="b*b'"]] 
      real_of_int_div[OF gz igcd_dvd2[where i="a*a'" and j="b*b'"]] 
    have ?thesis by (simp add: Nmul_def x y Let_def INum_def)}
  ultimately show ?thesis by blast
qed
lemmas [code] = Nmul [symmetric]

lemma Nneg[simp]: "INum (~\<^sub>N x) = - INum x"
  by (simp add: Nneg_def split_def INum_def)
lemmas [code] = Nneg [symmetric]

lemma Nsub[simp]: shows "INum (x -\<^sub>N y) = INum x - INum y"
  by (simp add: Nsub_def split_def)
lemmas [code] = Nsub [symmetric]

lemma Ninv[simp]: "INum (Ninv x) = 1 / (INum x)"
  by (simp add: Ninv_def INum_def split_def)
lemmas [code] = Ninv [symmetric]

lemma Ndiv[simp]: "INum (x \<div>\<^sub>N y) = INum x / INum y" by (simp add: Ndiv_def)
lemmas [code] = Ndiv [symmetric]

lemma Nlt0_iff[simp]: assumes nx: "isnormNum x" shows "(INum x < 0) = 0>\<^sub>N x "
proof-
  have " \<exists> a b. x = (a,b)" by simp
  then obtain a b where x[simp]:"x = (a,b)" by blast
  {assume "a = 0" hence ?thesis by (simp add: Nlt0_def INum_def) }
  moreover
  {assume a: "a\<noteq>0" hence b: "real b > 0" using nx by (simp add: isnormNum_def)
    from pos_divide_less_eq[OF b, where b="real a" and a="0"]
    have ?thesis by (simp add: Nlt0_def INum_def)}
  ultimately show ?thesis by blast
qed

lemma   Nle0_iff[simp]:assumes nx: "isnormNum x" shows "(INum x \<le> 0) = 0\<ge>\<^sub>N x"
proof-
  have " \<exists> a b. x = (a,b)" by simp
  then obtain a b where x[simp]:"x = (a,b)" by blast
  {assume "a = 0" hence ?thesis by (simp add: Nle0_def INum_def) }
  moreover
  {assume a: "a\<noteq>0" hence b: "real b > 0" using nx by (simp add: isnormNum_def)
    from pos_divide_le_eq[OF b, where b="real a" and a="0"]
    have ?thesis by (simp add: Nle0_def INum_def)}
  ultimately show ?thesis by blast
qed

lemma Ngt0_iff[simp]:assumes nx: "isnormNum x" shows "(INum x > 0) = 0<\<^sub>N x"
proof-
  have " \<exists> a b. x = (a,b)" by simp
  then obtain a b where x[simp]:"x = (a,b)" by blast
  {assume "a = 0" hence ?thesis by (simp add: Ngt0_def INum_def) }
  moreover
  {assume a: "a\<noteq>0" hence b: "real b > 0" using nx by (simp add: isnormNum_def)
    from pos_less_divide_eq[OF b, where b="real a" and a="0"]
    have ?thesis by (simp add: Ngt0_def INum_def)}
  ultimately show ?thesis by blast
qed
lemma Nge0_iff[simp]:assumes nx: "isnormNum x" shows "(INum x \<ge> 0) = 0\<le>\<^sub>N x"
proof-
  have " \<exists> a b. x = (a,b)" by simp
  then obtain a b where x[simp]:"x = (a,b)" by blast
  {assume "a = 0" hence ?thesis by (simp add: Nge0_def INum_def) }
  moreover
  {assume a: "a\<noteq>0" hence b: "real b > 0" using nx by (simp add: isnormNum_def)
    from pos_le_divide_eq[OF b, where b="real a" and a="0"]
    have ?thesis by (simp add: Nge0_def INum_def)}
  ultimately show ?thesis by blast
qed

lemma Nlt_iff[simp]: assumes nx: "isnormNum x" and ny: "isnormNum y"
  shows "(INum x < INum y) = (x <\<^sub>N y)"
proof-
  have "(INum x < INum y) = (INum (x -\<^sub>N y) < 0)" using nx ny by simp
  also have "\<dots> = (0>\<^sub>N (x -\<^sub>N y))" using Nlt0_iff[OF Nsub_normN[OF ny]] by simp
  finally show ?thesis by (simp add: Nlt_def)
qed

lemma [code]: "INum x < INum y \<longleftrightarrow> normNum x <\<^sub>N normNum y"
proof -
  have "normNum x <\<^sub>N normNum y \<longleftrightarrow> INum (normNum x) < INum (normNum y)" 
    by (simp del: normNum)
  also have "\<dots> = (INum x < INum y)" by simp 
  finally show ?thesis by simp
qed

lemma Nle_iff[simp]: assumes nx: "isnormNum x" and ny: "isnormNum y"
  shows "(INum x \<le> INum y) = (x \<le>\<^sub>N y)"
proof-
  have "(INum x \<le> INum y) = (INum (x -\<^sub>N y) \<le> 0)" using nx ny by simp
  also have "\<dots> = (0\<ge>\<^sub>N (x -\<^sub>N y))" using Nle0_iff[OF Nsub_normN[OF ny]] by simp
  finally show ?thesis by (simp add: Nle_def)
qed

lemma [code]: "INum x \<le> INum y \<longleftrightarrow> normNum x \<le>\<^sub>N normNum y"
proof -
  have "normNum x \<le>\<^sub>N normNum y \<longleftrightarrow> INum (normNum x) \<le> INum (normNum y)" 
    by (simp del: normNum)
  also have "\<dots> = (INum x \<le> INum y)" by simp 
  finally show ?thesis by simp
qed

lemma Nadd_commute: "x +\<^sub>N y = y +\<^sub>N x"
proof-
  have n: "isnormNum (x +\<^sub>N y)" "isnormNum (y +\<^sub>N x)" by simp_all
  have "INum (x +\<^sub>N y) = INum (y +\<^sub>N x)" by simp
  with isnormNum_unique[OF n] show ?thesis by simp
qed

lemma[simp]: "(0, b) +\<^sub>N y = normNum y" "(a, 0) +\<^sub>N y = normNum y" 
  "x +\<^sub>N (0, b) = normNum x" "x +\<^sub>N (a, 0) = normNum x"
  apply (simp add: Nadd_def split_def, simp add: Nadd_def split_def)
  apply (subst Nadd_commute,simp add: Nadd_def split_def)
  apply (subst Nadd_commute,simp add: Nadd_def split_def)
  done

lemma normNum_nilpotent_aux[simp]: assumes nx: "isnormNum x" 
  shows "normNum x = x"
proof-
  let ?a = "normNum x"
  have n: "isnormNum ?a" by simp
  have th:"INum ?a = INum x" by simp
  with isnormNum_unique[OF n nx]  
  show ?thesis by simp
qed

lemma normNum_nilpotent[simp]: "normNum (normNum x) = normNum x"
  by simp
lemma normNum0[simp]: "normNum (0,b) = 0\<^sub>N" "normNum (a,0) = 0\<^sub>N"
  by (simp_all add: normNum_def)
lemma normNum_Nadd: "normNum (x +\<^sub>N y) = x +\<^sub>N y" by simp
lemma Nadd_normNum1[simp]: "normNum x +\<^sub>N y = x +\<^sub>N y"
proof-
  have n: "isnormNum (normNum x +\<^sub>N y)" "isnormNum (x +\<^sub>N y)" by simp_all
  have "INum (normNum x +\<^sub>N y) = INum x + INum y" by simp
  also have "\<dots> = INum (x +\<^sub>N y)" by simp
  finally show ?thesis using isnormNum_unique[OF n] by simp
qed
lemma Nadd_normNum2[simp]: "x +\<^sub>N normNum y = x +\<^sub>N y"
proof-
  have n: "isnormNum (x +\<^sub>N normNum y)" "isnormNum (x +\<^sub>N y)" by simp_all
  have "INum (x +\<^sub>N normNum y) = INum x + INum y" by simp
  also have "\<dots> = INum (x +\<^sub>N y)" by simp
  finally show ?thesis using isnormNum_unique[OF n] by simp
qed

lemma Nadd_assoc: "x +\<^sub>N y +\<^sub>N z = x +\<^sub>N (y +\<^sub>N z)"
proof-
  have n: "isnormNum (x +\<^sub>N y +\<^sub>N z)" "isnormNum (x +\<^sub>N (y +\<^sub>N z))" by simp_all
  have "INum (x +\<^sub>N y +\<^sub>N z) = INum (x +\<^sub>N (y +\<^sub>N z))" by simp
  with isnormNum_unique[OF n] show ?thesis by simp
qed

lemma Nmul_commute: "isnormNum x \<Longrightarrow> isnormNum y \<Longrightarrow> x *\<^sub>N y = y *\<^sub>N x"
  by (simp add: Nmul_def split_def Let_def igcd_commute mult_commute)

lemma Nmul_assoc: assumes nx: "isnormNum x" and ny:"isnormNum y" and nz:"isnormNum z"
  shows "x *\<^sub>N y *\<^sub>N z = x *\<^sub>N (y *\<^sub>N z)"
proof-
  from nx ny nz have n: "isnormNum (x *\<^sub>N y *\<^sub>N z)" "isnormNum (x *\<^sub>N (y *\<^sub>N z))" 
    by simp_all
  have "INum (x +\<^sub>N y +\<^sub>N z) = INum (x +\<^sub>N (y +\<^sub>N z))" by simp
  with isnormNum_unique[OF n] show ?thesis by simp
qed

lemma Nsub0: assumes x: "isnormNum x" and y:"isnormNum y" shows "(x -\<^sub>N y = 0\<^sub>N) = (x = y)"
proof-
  from isnormNum_unique[OF Nsub_normN[OF y], where y="0\<^sub>N"] 
  have "(x -\<^sub>N y = 0\<^sub>N) = (INum (x -\<^sub>N y) = INum 0\<^sub>N)" by simp
  also have "\<dots> = (INum x = INum y)" by simp
  also have "\<dots> = (x = y)" using x y by simp
  finally show ?thesis .
qed
lemma Nmul0[simp]: "c *\<^sub>N 0\<^sub>N = 0\<^sub>N" " 0\<^sub>N *\<^sub>N c = 0\<^sub>N"
  by (simp_all add: Nmul_def Let_def split_def)

lemma Nmul_eq0[simp]: assumes nx:"isnormNum x" and ny: "isnormNum y"
  shows "(x*\<^sub>N y = 0\<^sub>N) = (x = 0\<^sub>N \<or> y = 0\<^sub>N)"
proof-
  have " \<exists> a b a' b'. x = (a,b) \<and> y= (a',b')" by auto
  then obtain a b a' b' where xy[simp]: "x = (a,b)" "y = (a',b')" by blast
  have n0: "isnormNum 0\<^sub>N" by simp
  show ?thesis using nx ny 
    apply (simp only: isnormNum_unique[OF  Nmul_normN[OF nx ny] n0, symmetric] Nmul)
    apply (simp add: INum_def split_def isnormNum_def fst_conv snd_conv)
    apply (cases "a=0",simp_all)
    apply (cases "a'=0",simp_all)
    done 
qed
lemma Nneg_Nneg[simp]: "~\<^sub>N (~\<^sub>N c) = c"
  by (simp add: Nneg_def split_def)

lemma Nmul1[simp]: 
  "isnormNum c \<Longrightarrow> 1\<^sub>N *\<^sub>N c = c" 
  "isnormNum c \<Longrightarrow> c *\<^sub>N 1\<^sub>N  = c" 
  apply (simp_all add: Nmul_def Let_def split_def isnormNum_def)
  by (cases "fst c = 0", simp_all,cases c, simp_all)+

lemma [code, code unfold]:
  "number_of k = real_int (number_of k)"
  by (simp add: real_int_def)

types_code real ("{* int * int *}")
attach (term_of) {*
fun term_of_real (p, q) =
  let 
    val rT = HOLogic.realT;
in if q = 1
  then HOLogic.mk_number rT p
  else @{term "op / \<Colon> real \<Rightarrow> real \<Rightarrow> real"} $
    HOLogic.mk_number rT p $ HOLogic.mk_number rT q
end;
*}

consts_code INum ("")

end