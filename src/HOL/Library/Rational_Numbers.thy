(*  Title:      HOL/Library/Rational_Numbers.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*
  \title{Rational numbers}
  \author{Markus Wenzel}
*}

theory Rational_Numbers = Quotient + Ring_and_Field:

subsection {* Fractions *}

subsubsection {* The type of fractions *}

typedef fraction = "{(a, b) :: int \<times> int | a b. b \<noteq> 0}"
proof
  show "(0, 1) \<in> ?fraction" by simp
qed

constdefs
  fract :: "int => int => fraction"
  "fract a b == Abs_fraction (a, b)"
  num :: "fraction => int"
  "num Q == fst (Rep_fraction Q)"
  den :: "fraction => int"
  "den Q == snd (Rep_fraction Q)"

lemma fract_num [simp]: "b \<noteq> 0 ==> num (fract a b) = a"
  by (simp add: fract_def num_def fraction_def Abs_fraction_inverse)

lemma fract_den [simp]: "b \<noteq> 0 ==> den (fract a b) = b"
  by (simp add: fract_def den_def fraction_def Abs_fraction_inverse)

lemma fraction_cases [case_names fract, cases type: fraction]:
  "(!!a b. Q = fract a b ==> b \<noteq> 0 ==> C) ==> C"
proof -
  assume r: "!!a b. Q = fract a b ==> b \<noteq> 0 ==> C"
  obtain a b where "Q = fract a b" and "b \<noteq> 0"
    by (cases Q) (auto simp add: fract_def fraction_def)
  thus C by (rule r)
qed

lemma fraction_induct [case_names fract, induct type: fraction]:
    "(!!a b. b \<noteq> 0 ==> P (fract a b)) ==> P Q"
  by (cases Q) simp


subsubsection {* Equivalence of fractions *}

instance fraction :: eqv ..

defs (overloaded)
  equiv_fraction_def: "Q \<sim> R == num Q * den R = num R * den Q"

lemma equiv_fraction_iff [iff]:
    "b \<noteq> 0 ==> b' \<noteq> 0 ==> (fract a b \<sim> fract a' b') = (a * b' = a' * b)"
  by (simp add: equiv_fraction_def)

instance fraction :: equiv
proof
  fix Q R S :: fraction
  {
    show "Q \<sim> Q"
    proof (induct Q)
      fix a b :: int
      assume "b \<noteq> 0" and "b \<noteq> 0"
      with refl show "fract a b \<sim> fract a b" ..
    qed
  next
    assume "Q \<sim> R" and "R \<sim> S"
    show "Q \<sim> S"
    proof (insert prems, induct Q, induct R, induct S)
      fix a b a' b' a'' b'' :: int
      assume b: "b \<noteq> 0" and b': "b' \<noteq> 0" and b'': "b'' \<noteq> 0"
      assume "fract a b \<sim> fract a' b'" hence eq1: "a * b' = a' * b" ..
      assume "fract a' b' \<sim> fract a'' b''" hence eq2: "a' * b'' = a'' * b'" ..
      have "a * b'' = a'' * b"
      proof cases
        assume "a' = 0"
        with b' eq1 eq2 have "a = 0 \<and> a'' = 0" by auto
        thus ?thesis by simp
      next
        assume a': "a' \<noteq> 0"
        from eq1 eq2 have "(a * b') * (a' * b'') = (a' * b) * (a'' * b')" by simp
        hence "(a * b'') * (a' * b') = (a'' * b) * (a' * b')" by (simp only: zmult_ac)
        with a' b' show ?thesis by simp
      qed
      thus "fract a b \<sim> fract a'' b''" ..
    qed
  next
    show "Q \<sim> R ==> R \<sim> Q"
    proof (induct Q, induct R)
      fix a b a' b' :: int
      assume b: "b \<noteq> 0" and b': "b' \<noteq> 0"
      assume "fract a b \<sim> fract a' b'"
      hence "a * b' = a' * b" ..
      hence "a' * b = a * b'" ..
      thus "fract a' b' \<sim> fract a b" ..
    qed
  }
qed

lemma eq_fraction_iff [iff]:
    "b \<noteq> 0 ==> b' \<noteq> 0 ==> (\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor>) = (a * b' = a' * b)"
  by (simp add: equiv_fraction_iff quot_equality)


subsubsection {* Operations on fractions *}

text {*
 We define the basic arithmetic operations on fractions and
 demonstrate their ``well-definedness'', i.e.\ congruence with respect
 to equivalence of fractions.
*}

instance fraction :: zero ..
instance fraction :: one ..
instance fraction :: plus ..
instance fraction :: minus ..
instance fraction :: times ..
instance fraction :: inverse ..
instance fraction :: ord ..

defs (overloaded)
  zero_fraction_def: "0 == fract 0 1"
  one_fraction_def: "1 == fract 1 1"
  add_fraction_def: "Q + R ==
    fract (num Q * den R + num R * den Q) (den Q * den R)"
  minus_fraction_def: "-Q == fract (-(num Q)) (den Q)"
  mult_fraction_def: "Q * R == fract (num Q * num R) (den Q * den R)"
  inverse_fraction_def: "inverse Q == fract (den Q) (num Q)"
  le_fraction_def: "Q \<le> R ==
    (num Q * den R) * (den Q * den R) \<le> (num R * den Q) * (den Q * den R)"

lemma is_zero_fraction_iff: "b \<noteq> 0 ==> (\<lfloor>fract a b\<rfloor> = \<lfloor>0\<rfloor>) = (a = 0)"
  by (simp add: zero_fraction_def eq_fraction_iff)

theorem add_fraction_cong:
  "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> \<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor>
    ==> b \<noteq> 0 ==> b' \<noteq> 0 ==> d \<noteq> 0 ==> d' \<noteq> 0
    ==> \<lfloor>fract a b + fract c d\<rfloor> = \<lfloor>fract a' b' + fract c' d'\<rfloor>"
proof -
  assume neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
  assume "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor>" hence eq1: "a * b' = a' * b" ..
  assume "\<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor>" hence eq2: "c * d' = c' * d" ..
  have "\<lfloor>fract (a * d + c * b) (b * d)\<rfloor> = \<lfloor>fract (a' * d' + c' * b') (b' * d')\<rfloor>"
  proof
    show "(a * d + c * b) * (b' * d') = (a' * d' + c' * b') * (b * d)"
      (is "?lhs = ?rhs")
    proof -
      have "?lhs = (a * b') * (d * d') + (c * d') * (b * b')"
        by (simp add: int_distrib zmult_ac)
      also have "... = (a' * b) * (d * d') + (c' * d) * (b * b')"
        by (simp only: eq1 eq2)
      also have "... = ?rhs"
        by (simp add: int_distrib zmult_ac)
      finally show "?lhs = ?rhs" .
    qed
    from neq show "b * d \<noteq> 0" by simp
    from neq show "b' * d' \<noteq> 0" by simp
  qed
  with neq show ?thesis by (simp add: add_fraction_def)
qed

theorem minus_fraction_cong:
  "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> b \<noteq> 0 ==> b' \<noteq> 0
    ==> \<lfloor>-(fract a b)\<rfloor> = \<lfloor>-(fract a' b')\<rfloor>"
proof -
  assume neq: "b \<noteq> 0"  "b' \<noteq> 0"
  assume "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor>"
  hence "a * b' = a' * b" ..
  hence "-a * b' = -a' * b" by simp
  hence "\<lfloor>fract (-a) b\<rfloor> = \<lfloor>fract (-a') b'\<rfloor>" ..
  with neq show ?thesis by (simp add: minus_fraction_def)
qed

theorem mult_fraction_cong:
  "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> \<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor>
    ==> b \<noteq> 0 ==> b' \<noteq> 0 ==> d \<noteq> 0 ==> d' \<noteq> 0
    ==> \<lfloor>fract a b * fract c d\<rfloor> = \<lfloor>fract a' b' * fract c' d'\<rfloor>"
proof -
  assume neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
  assume "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor>" hence eq1: "a * b' = a' * b" ..
  assume "\<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor>" hence eq2: "c * d' = c' * d" ..
  have "\<lfloor>fract (a * c) (b * d)\<rfloor> = \<lfloor>fract (a' * c') (b' * d')\<rfloor>"
  proof
    from eq1 eq2 have "(a * b') * (c * d') = (a' * b) * (c' * d)" by simp
    thus "(a * c) * (b' * d') = (a' * c') * (b * d)" by (simp add: zmult_ac)
    from neq show "b * d \<noteq> 0" by simp
    from neq show "b' * d' \<noteq> 0" by simp
  qed
  with neq show "\<lfloor>fract a b * fract c d\<rfloor> = \<lfloor>fract a' b' * fract c' d'\<rfloor>"
    by (simp add: mult_fraction_def)
qed

theorem inverse_fraction_cong:
  "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> \<lfloor>fract a b\<rfloor> \<noteq> \<lfloor>0\<rfloor> ==> \<lfloor>fract a' b'\<rfloor> \<noteq> \<lfloor>0\<rfloor>
    ==> b \<noteq> 0 ==> b' \<noteq> 0
    ==> \<lfloor>inverse (fract a b)\<rfloor> = \<lfloor>inverse (fract a' b')\<rfloor>"
proof -
  assume neq: "b \<noteq> 0"  "b' \<noteq> 0"
  assume "\<lfloor>fract a b\<rfloor> \<noteq> \<lfloor>0\<rfloor>" and "\<lfloor>fract a' b'\<rfloor> \<noteq> \<lfloor>0\<rfloor>"
  with neq obtain "a \<noteq> 0" and "a' \<noteq> 0" by (simp add: is_zero_fraction_iff)
  assume "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor>"
  hence "a * b' = a' * b" ..
  hence "b * a' = b' * a" by (simp only: zmult_ac)
  hence "\<lfloor>fract b a\<rfloor> = \<lfloor>fract b' a'\<rfloor>" ..
  with neq show ?thesis by (simp add: inverse_fraction_def)
qed

theorem le_fraction_cong:
  "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> \<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor>
    ==> b \<noteq> 0 ==> b' \<noteq> 0 ==> d \<noteq> 0 ==> d' \<noteq> 0
    ==> (fract a b \<le> fract c d) = (fract a' b' \<le> fract c' d')"
proof -
  assume neq: "b \<noteq> 0"  "b' \<noteq> 0"  "d \<noteq> 0"  "d' \<noteq> 0"
  assume "\<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor>" hence eq1: "a * b' = a' * b" ..
  assume "\<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor>" hence eq2: "c * d' = c' * d" ..

  let ?le = "\<lambda>a b c d. ((a * d) * (b * d) \<le> (c * b) * (b * d))"
  {
    fix a b c d x :: int assume x: "x \<noteq> 0"
    have "?le a b c d = ?le (a * x) (b * x) c d"
    proof -
      from x have "0 < x * x" by (auto simp add: int_less_le)
      hence "?le a b c d =
          ((a * d) * (b * d) * (x * x) \<le> (c * b) * (b * d) * (x * x))"
        by (simp add: zmult_zle_cancel2)
      also have "... = ?le (a * x) (b * x) c d"
        by (simp add: zmult_ac)
      finally show ?thesis .
    qed
  } note le_factor = this

  let ?D = "b * d" and ?D' = "b' * d'"
  from neq have D: "?D \<noteq> 0" by simp
  from neq have "?D' \<noteq> 0" by simp
  hence "?le a b c d = ?le (a * ?D') (b * ?D') c d"
    by (rule le_factor)
  also have "... = ((a * b') * ?D * ?D' * d * d' \<le> (c * d') * ?D * ?D' * b * b')"
    by (simp add: zmult_ac)
  also have "... = ((a' * b) * ?D * ?D' * d * d' \<le> (c' * d) * ?D * ?D' * b * b')"
    by (simp only: eq1 eq2)
  also have "... = ?le (a' * ?D) (b' * ?D) c' d'"
    by (simp add: zmult_ac)
  also from D have "... = ?le a' b' c' d'"
    by (rule le_factor [symmetric])
  finally have "?le a b c d = ?le a' b' c' d'" .
  with neq show ?thesis by (simp add: le_fraction_def)
qed


subsection {* Rational numbers *}

subsubsection {* The type of rational numbers *}

typedef (Rat)
  rat = "UNIV :: fraction quot set" ..

lemma RatI [intro, simp]: "Q \<in> Rat"
  by (simp add: Rat_def)

constdefs
  fraction_of :: "rat => fraction"
  "fraction_of q == pick (Rep_Rat q)"
  rat_of :: "fraction => rat"
  "rat_of Q == Abs_Rat \<lfloor>Q\<rfloor>"

theorem rat_of_equality [iff?]: "(rat_of Q = rat_of Q') = (\<lfloor>Q\<rfloor> = \<lfloor>Q'\<rfloor>)"
  by (simp add: rat_of_def Abs_Rat_inject)

lemma rat_of: "\<lfloor>Q\<rfloor> = \<lfloor>Q'\<rfloor> ==> rat_of Q = rat_of Q'" ..

constdefs
  Fract :: "int => int => rat"
  "Fract a b == rat_of (fract a b)"

theorem Fract_inverse: "\<lfloor>fraction_of (Fract a b)\<rfloor> = \<lfloor>fract a b\<rfloor>"
  by (simp add: fraction_of_def rat_of_def Fract_def Abs_Rat_inverse pick_inverse)

theorem Fract_equality [iff?]:
    "(Fract a b = Fract c d) = (\<lfloor>fract a b\<rfloor> = \<lfloor>fract c d\<rfloor>)"
  by (simp add: Fract_def rat_of_equality)

theorem eq_rat:
    "b \<noteq> 0 ==> d \<noteq> 0 ==> (Fract a b = Fract c d) = (a * d = c * b)"
  by (simp add: Fract_equality eq_fraction_iff)

theorem Rat_cases [case_names Fract, cases type: rat]:
  "(!!a b. q = Fract a b ==> b \<noteq> 0 ==> C) ==> C"
proof -
  assume r: "!!a b. q = Fract a b ==> b \<noteq> 0 ==> C"
  obtain x where "q = Abs_Rat x" by (cases q)
  moreover obtain Q where "x = \<lfloor>Q\<rfloor>" by (cases x)
  moreover obtain a b where "Q = fract a b" and "b \<noteq> 0" by (cases Q)
  ultimately have "q = Fract a b" by (simp only: Fract_def rat_of_def)
  thus ?thesis by (rule r)
qed

theorem Rat_induct [case_names Fract, induct type: rat]:
    "(!!a b. b \<noteq> 0 ==> P (Fract a b)) ==> P q"
  by (cases q) simp


subsubsection {* Canonical function definitions *}

text {*
  Note that the unconditional version below is much easier to read.
*}

theorem rat_cond_function:
  "(!!q r. P \<lfloor>fraction_of q\<rfloor> \<lfloor>fraction_of r\<rfloor> ==>
      f q r == g (fraction_of q) (fraction_of r)) ==>
    (!!a b a' b' c d c' d'.
      \<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> \<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor> ==>
      P \<lfloor>fract a b\<rfloor> \<lfloor>fract c d\<rfloor> ==> P \<lfloor>fract a' b'\<rfloor> \<lfloor>fract c' d'\<rfloor> ==>
      b \<noteq> 0 ==> b' \<noteq> 0 ==> d \<noteq> 0 ==> d' \<noteq> 0 ==>
      g (fract a b) (fract c d) = g (fract a' b') (fract c' d')) ==>
    P \<lfloor>fract a b\<rfloor> \<lfloor>fract c d\<rfloor> ==>
      f (Fract a b) (Fract c d) = g (fract a b) (fract c d)"
  (is "PROP ?eq ==> PROP ?cong ==> ?P ==> _")
proof -
  assume eq: "PROP ?eq" and cong: "PROP ?cong" and P: ?P
  have "f (Abs_Rat \<lfloor>fract a b\<rfloor>) (Abs_Rat \<lfloor>fract c d\<rfloor>) = g (fract a b) (fract c d)"
  proof (rule quot_cond_function)
    fix X Y assume "P X Y"
    with eq show "f (Abs_Rat X) (Abs_Rat Y) == g (pick X) (pick Y)"
      by (simp add: fraction_of_def pick_inverse Abs_Rat_inverse)
  next
    fix Q Q' R R' :: fraction
    show "\<lfloor>Q\<rfloor> = \<lfloor>Q'\<rfloor> ==> \<lfloor>R\<rfloor> = \<lfloor>R'\<rfloor> ==>
        P \<lfloor>Q\<rfloor> \<lfloor>R\<rfloor> ==> P \<lfloor>Q'\<rfloor> \<lfloor>R'\<rfloor> ==> g Q R = g Q' R'"
      by (induct Q, induct Q', induct R, induct R') (rule cong)
  qed
  thus ?thesis by (unfold Fract_def rat_of_def)
qed

theorem rat_function:
  "(!!q r. f q r == g (fraction_of q) (fraction_of r)) ==>
    (!!a b a' b' c d c' d'.
      \<lfloor>fract a b\<rfloor> = \<lfloor>fract a' b'\<rfloor> ==> \<lfloor>fract c d\<rfloor> = \<lfloor>fract c' d'\<rfloor> ==>
      b \<noteq> 0 ==> b' \<noteq> 0 ==> d \<noteq> 0 ==> d' \<noteq> 0 ==>
      g (fract a b) (fract c d) = g (fract a' b') (fract c' d')) ==>
    f (Fract a b) (Fract c d) = g (fract a b) (fract c d)"
proof -
  case rule_context from this TrueI
  show ?thesis by (rule rat_cond_function)
qed


subsubsection {* Standard operations on rational numbers *}

instance rat :: zero ..
instance rat :: one ..
instance rat :: plus ..
instance rat :: minus ..
instance rat :: times ..
instance rat :: inverse ..
instance rat :: ord ..
instance rat :: number ..

defs (overloaded)
  zero_rat_def: "0 == rat_of 0"
  one_rat_def: "1 == rat_of 1"
  add_rat_def: "q + r == rat_of (fraction_of q + fraction_of r)"
  minus_rat_def: "-q == rat_of (-(fraction_of q))"
  diff_rat_def: "q - r == q + (-(r::rat))"
  mult_rat_def: "q * r == rat_of (fraction_of q * fraction_of r)"
  inverse_rat_def: "q \<noteq> 0 ==> inverse q == rat_of (inverse (fraction_of q))"
  divide_rat_def: "r \<noteq> 0 ==> q / r == q * inverse (r::rat)"
  le_rat_def: "q \<le> r == fraction_of q \<le> fraction_of r"
  less_rat_def: "q < r == q \<le> r \<and> q \<noteq> (r::rat)"
  abs_rat_def: "\<bar>q\<bar> == if q < 0 then -q else (q::rat)"
  number_of_rat_def: "number_of b == Fract (number_of b) 1"

theorem zero_rat: "0 = Fract 0 1"
  by (simp add: zero_rat_def zero_fraction_def rat_of_def Fract_def)        

theorem one_rat: "1 = Fract 1 1"
  by (simp add: one_rat_def one_fraction_def rat_of_def Fract_def)

theorem add_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  Fract a b + Fract c d = Fract (a * d + c * b) (b * d)"
proof -
  have "Fract a b + Fract c d = rat_of (fract a b + fract c d)"
    by (rule rat_function, rule add_rat_def, rule rat_of, rule add_fraction_cong)
  also
  assume "b \<noteq> 0"  "d \<noteq> 0"
  hence "fract a b + fract c d = fract (a * d + c * b) (b * d)"
    by (simp add: add_fraction_def)
  finally show ?thesis by (unfold Fract_def)
qed

theorem minus_rat: "b \<noteq> 0 ==> -(Fract a b) = Fract (-a) b"
proof -
  have "-(Fract a b) = rat_of (-(fract a b))"
    by (rule rat_function, rule minus_rat_def, rule rat_of, rule minus_fraction_cong)
  also assume "b \<noteq> 0" hence "-(fract a b) = fract (-a) b"
    by (simp add: minus_fraction_def)
  finally show ?thesis by (unfold Fract_def)
qed

theorem diff_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
    Fract a b - Fract c d = Fract (a * d - c * b) (b * d)"
  by (simp add: diff_rat_def add_rat minus_rat)

theorem mult_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  Fract a b * Fract c d = Fract (a * c) (b * d)"
proof -
  have "Fract a b * Fract c d = rat_of (fract a b * fract c d)"
    by (rule rat_function, rule mult_rat_def, rule rat_of, rule mult_fraction_cong)
  also
  assume "b \<noteq> 0"  "d \<noteq> 0"
  hence "fract a b * fract c d = fract (a * c) (b * d)"
    by (simp add: mult_fraction_def)
  finally show ?thesis by (unfold Fract_def)
qed

theorem inverse_rat: "Fract a b \<noteq> 0 ==> b \<noteq> 0 ==>
  inverse (Fract a b) = Fract b a"
proof -
  assume neq: "b \<noteq> 0" and nonzero: "Fract a b \<noteq> 0"
  hence "\<lfloor>fract a b\<rfloor> \<noteq> \<lfloor>0\<rfloor>"
    by (simp add: zero_rat eq_rat is_zero_fraction_iff)
  with _ inverse_fraction_cong [THEN rat_of]
  have "inverse (Fract a b) = rat_of (inverse (fract a b))"
  proof (rule rat_cond_function)
    fix q assume cond: "\<lfloor>fraction_of q\<rfloor> \<noteq> \<lfloor>0\<rfloor>"
    have "q \<noteq> 0"
    proof (cases q)
      fix a b assume "b \<noteq> 0" and "q = Fract a b"
      from this cond show ?thesis
        by (simp add: Fract_inverse is_zero_fraction_iff zero_rat eq_rat)
    qed
    thus "inverse q == rat_of (inverse (fraction_of q))"
      by (rule inverse_rat_def)
  qed
  also from neq nonzero have "inverse (fract a b) = fract b a"
    by (simp add: inverse_fraction_def)
  finally show ?thesis by (unfold Fract_def)
qed

theorem divide_rat: "Fract c d \<noteq> 0 ==> b \<noteq> 0 ==> d \<noteq> 0 ==>
  Fract a b / Fract c d = Fract (a * d) (b * c)"
proof -
  assume neq: "b \<noteq> 0"  "d \<noteq> 0" and nonzero: "Fract c d \<noteq> 0"
  hence "c \<noteq> 0" by (simp add: zero_rat eq_rat)
  with neq nonzero show ?thesis
    by (simp add: divide_rat_def inverse_rat mult_rat)
qed

theorem le_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
  (Fract a b \<le> Fract c d) = ((a * d) * (b * d) \<le> (c * b) * (b * d))"
proof -
  have "(Fract a b \<le> Fract c d) = (fract a b \<le> fract c d)"
    by (rule rat_function, rule le_rat_def, rule le_fraction_cong)
  also
  assume "b \<noteq> 0"  "d \<noteq> 0"
  hence "(fract a b \<le> fract c d) = ((a * d) * (b * d) \<le> (c * b) * (b * d))"
    by (simp add: le_fraction_def)
  finally show ?thesis .
qed

theorem less_rat: "b \<noteq> 0 ==> d \<noteq> 0 ==>
    (Fract a b < Fract c d) = ((a * d) * (b * d) < (c * b) * (b * d))"
  by (simp add: less_rat_def le_rat eq_rat int_less_le)

theorem abs_rat: "b \<noteq> 0 ==> \<bar>Fract a b\<bar> = Fract \<bar>a\<bar> \<bar>b\<bar>"
  by (simp add: abs_rat_def minus_rat zero_rat less_rat eq_rat)
    (auto simp add: zmult_less_0_iff int_0_less_mult_iff int_le_less split: zabs_split)


subsubsection {* The ordered field of rational numbers *}

lemma rat_add_assoc: "(q + r) + s = q + (r + (s::rat))"
  by (induct q, induct r, induct s) 
     (simp add: add_rat zadd_ac zmult_ac int_distrib)

lemma rat_add_0: "0 + q = (q::rat)"
  by (induct q) (simp add: zero_rat add_rat)

lemma rat_left_minus: "(-q) + q = (0::rat)"
  by (induct q) (simp add: zero_rat minus_rat add_rat eq_rat)


instance rat :: field
proof
  fix q r s :: rat
  show "(q + r) + s = q + (r + s)"
    by (rule rat_add_assoc)
  show "q + r = r + q"
    by (induct q, induct r) (simp add: add_rat zadd_ac zmult_ac)
  show "0 + q = q"
    by (induct q) (simp add: zero_rat add_rat)
  show "(-q) + q = 0"
    by (rule rat_left_minus)
  show "q - r = q + (-r)"
    by (induct q, induct r) (simp add: add_rat minus_rat diff_rat)
  show "(q * r) * s = q * (r * s)"
    by (induct q, induct r, induct s) (simp add: mult_rat zmult_ac)
  show "q * r = r * q"
    by (induct q, induct r) (simp add: mult_rat zmult_ac)
  show "1 * q = q"
    by (induct q) (simp add: one_rat mult_rat)
  show "(q + r) * s = q * s + r * s"
    by (induct q, induct r, induct s) 
       (simp add: add_rat mult_rat eq_rat int_distrib)
  show "q \<noteq> 0 ==> inverse q * q = 1"
    by (induct q) (simp add: inverse_rat mult_rat one_rat zero_rat eq_rat)
  show "r \<noteq> 0 ==> q / r = q * inverse r"
    by (induct q, induct r)
       (simp add: mult_rat divide_rat inverse_rat zero_rat eq_rat)
  show "0 \<noteq> (1::rat)"
    by (simp add: zero_rat one_rat eq_rat) 
  assume eq: "s+q = s+r" 
    hence "(-s + s) + q = (-s + s) + r" by (simp only: eq rat_add_assoc)
    thus "q = r" by (simp add: rat_left_minus rat_add_0)
qed

instance rat :: linorder
proof
  fix q r s :: rat
  {
    assume "q \<le> r" and "r \<le> s"
    show "q \<le> s"
    proof (insert prems, induct q, induct r, induct s)
      fix a b c d e f :: int
      assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
      assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract e f"
      show "Fract a b \<le> Fract e f"
      proof -
        from neq obtain bb: "0 < b * b" and dd: "0 < d * d" and ff: "0 < f * f"
          by (auto simp add: int_less_le)
        have "(a * d) * (b * d) * (f * f) \<le> (c * b) * (b * d) * (f * f)"
        proof -
          from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
            by (simp add: le_rat)
          with ff show ?thesis by (simp add: zmult_zle_cancel2)
        qed
        also have "... = (c * f) * (d * f) * (b * b)"
          by (simp only: zmult_ac)
        also have "... \<le> (e * d) * (d * f) * (b * b)"
        proof -
          from neq 2 have "(c * f) * (d * f) \<le> (e * d) * (d * f)"
            by (simp add: le_rat)
          with bb show ?thesis by (simp add: zmult_zle_cancel2)
        qed
        finally have "(a * f) * (b * f) * (d * d) \<le> e * b * (b * f) * (d * d)"
          by (simp only: zmult_ac)
        with dd have "(a * f) * (b * f) \<le> (e * b) * (b * f)"
          by (simp add: zmult_zle_cancel2)
        with neq show ?thesis by (simp add: le_rat)
      qed
    qed
  next
    assume "q \<le> r" and "r \<le> q"
    show "q = r"
    proof (insert prems, induct q, induct r)
      fix a b c d :: int
      assume neq: "b \<noteq> 0"  "d \<noteq> 0"
      assume 1: "Fract a b \<le> Fract c d" and 2: "Fract c d \<le> Fract a b"
      show "Fract a b = Fract c d"
      proof -
        from neq 1 have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
          by (simp add: le_rat)
        also have "... \<le> (a * d) * (b * d)"
        proof -
          from neq 2 have "(c * b) * (d * b) \<le> (a * d) * (d * b)"
            by (simp add: le_rat)
          thus ?thesis by (simp only: zmult_ac)
        qed
        finally have "(a * d) * (b * d) = (c * b) * (b * d)" .
        moreover from neq have "b * d \<noteq> 0" by simp
        ultimately have "a * d = c * b" by simp
        with neq show ?thesis by (simp add: eq_rat)
      qed
    qed
  next
    show "q \<le> q"
      by (induct q) (simp add: le_rat)
    show "(q < r) = (q \<le> r \<and> q \<noteq> r)"
      by (simp only: less_rat_def)
    show "q \<le> r \<or> r \<le> q"
      by (induct q, induct r) (simp add: le_rat zmult_ac, arith)
  }
qed

instance rat :: ordered_field
proof
  fix q r s :: rat
  show "0 < (1::rat)" 
    by (simp add: zero_rat one_rat less_rat) 
  show "q \<le> r ==> s + q \<le> s + r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: int
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume le: "Fract a b \<le> Fract c d"
    show "Fract e f + Fract a b \<le> Fract e f + Fract c d"
    proof -
      let ?F = "f * f" from neq have F: "0 < ?F"
        by (auto simp add: int_less_le)
      from neq le have "(a * d) * (b * d) \<le> (c * b) * (b * d)"
        by (simp add: le_rat)
      with F have "(a * d) * (b * d) * ?F * ?F \<le> (c * b) * (b * d) * ?F * ?F"
        by (simp add: zmult_zle_cancel2)
      with neq show ?thesis by (simp add: add_rat le_rat zmult_ac int_distrib)
    qed
  qed
  show "q < r ==> 0 < s ==> s * q < s * r"
  proof (induct q, induct r, induct s)
    fix a b c d e f :: int
    assume neq: "b \<noteq> 0"  "d \<noteq> 0"  "f \<noteq> 0"
    assume le: "Fract a b < Fract c d"
    assume gt: "0 < Fract e f"
    show "Fract e f * Fract a b < Fract e f * Fract c d"
    proof -
      let ?E = "e * f" and ?F = "f * f"
      from neq gt have "0 < ?E"
        by (auto simp add: zero_rat less_rat le_rat int_less_le eq_rat)
      moreover from neq have "0 < ?F"
        by (auto simp add: int_less_le)
      moreover from neq le have "(a * d) * (b * d) < (c * b) * (b * d)"
        by (simp add: less_rat)
      ultimately have "(a * d) * (b * d) * ?E * ?F < (c * b) * (b * d) * ?E * ?F"
        by (simp add: zmult_zless_cancel2)
      with neq show ?thesis
        by (simp add: less_rat mult_rat zmult_ac)
    qed
  qed
  show "\<bar>q\<bar> = (if q < 0 then -q else q)"
    by (simp only: abs_rat_def)
qed


subsection {* Embedding integers *}

constdefs
  rat :: "int => rat"    (* FIXME generalize int to any numeric subtype (?) *)
  "rat z == Fract z 1"
  int_set :: "rat set"    ("\<int>")    (* FIXME generalize rat to any numeric supertype (?) *)
  "\<int> == range rat"

lemma rat_inject: "(rat z = rat w) = (z = w)"
proof
  assume "rat z = rat w"
  hence "Fract z 1 = Fract w 1" by (unfold rat_def)
  hence "\<lfloor>fract z 1\<rfloor> = \<lfloor>fract w 1\<rfloor>" ..
  thus "z = w" by auto
next
  assume "z = w"
  thus "rat z = rat w" by simp
qed

lemma int_set_cases [case_names rat, cases set: int_set]:
  "q \<in> \<int> ==> (!!z. q = rat z ==> C) ==> C"
proof (unfold int_set_def)
  assume "!!z. q = rat z ==> C"
  assume "q \<in> range rat" thus C ..
qed

lemma int_set_induct [case_names rat, induct set: int_set]:
  "q \<in> \<int> ==> (!!z. P (rat z)) ==> P q"
  by (rule int_set_cases) auto

theorem number_of_rat: "number_of b = rat (number_of b)"
  by (simp add: number_of_rat_def rat_def)

end
