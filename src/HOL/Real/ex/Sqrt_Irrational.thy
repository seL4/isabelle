(*  Title:      HOL/Real/ex/Sqrt_Irrational.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*  Square roots of primes are irrational *}

theory Sqrt_Irrational = Real + Primes:

syntax (xsymbols)                        (* FIXME move to main HOL (!?) *)
  "_square" :: "'a => 'a"  ("(_\<twosuperior>)" [1000] 999)
syntax (HTML output)
  "_square" :: "'a => 'a"  ("(_\<twosuperior>)" [1000] 999)
syntax (output)
  "_square" :: "'a => 'a"  ("(_^2)" [1000] 999)
translations
  "x\<twosuperior>" == "x^Suc (Suc 0)"


subsection {* The set of rational numbers *}

constdefs
  rationals :: "real set"    ("\<rat>")
  "\<rat> == {x. \<exists>m n. n \<noteq> 0 \<and> \<bar>x\<bar> = real (m::nat) / real (n::nat)}"

theorem rationals_rep: "x \<in> \<rat> ==>
  \<exists>m n. n \<noteq> 0 \<and> \<bar>x\<bar> = real m / real n \<and> gcd (m, n) = 1"
proof -
  assume "x \<in> \<rat>"
  then obtain m n :: nat where n: "n \<noteq> 0" and x_rat: "\<bar>x\<bar> = real m / real n"
    by (unfold rationals_def) blast
  let ?gcd = "gcd (m, n)"
  from n have gcd: "?gcd \<noteq> 0" by (simp add: gcd_zero)
  let ?k = "m div ?gcd"
  let ?l = "n div ?gcd"
  let ?gcd' = "gcd (?k, ?l)"
  have "?gcd dvd m" .. hence gcd_k: "?gcd * ?k = m"
    by (rule dvd_mult_div_cancel)
  have "?gcd dvd n" .. hence gcd_l: "?gcd * ?l = n"
    by (rule dvd_mult_div_cancel)

  from n gcd_l have "?l \<noteq> 0"
    by (auto iff del: neq0_conv)
  moreover
  have "\<bar>x\<bar> = real ?k / real ?l"
  proof -
    from gcd have "real ?k / real ?l = real (?gcd * ?k) / real (?gcd * ?l)"
      by (simp add: real_mult_div_cancel1)
    also from gcd_k gcd_l have "... = real m / real n" by simp
    also from x_rat have "... = \<bar>x\<bar>" ..
    finally show ?thesis ..
  qed
  moreover
  have "?gcd' = 1"
  proof -
    have "?gcd * ?gcd' = gcd (?gcd * ?k, ?gcd * ?l)"
      by (rule gcd_mult_distrib2)
    with gcd_k gcd_l have "?gcd * ?gcd' = ?gcd" by simp
    with gcd show ?thesis by simp
  qed
  ultimately show ?thesis by blast
qed

lemma [elim?]: "r \<in> \<rat> ==>
    (!!m n. n \<noteq> 0 ==> \<bar>r\<bar> = real m / real n ==> gcd (m, n) = 1 ==> C) ==> C"
  by (insert rationals_rep) blast


subsection {* Main theorem *}

text {*
  The square root of any prime number (including @{text 2}) is
  irrational.
*}

theorem sqrt_prime_irrational: "x\<twosuperior> = real p ==> p \<in> prime ==> x \<notin> \<rat>"
proof
  assume x_sqrt: "x\<twosuperior> = real p"
  assume p_prime: "p \<in> prime"
  hence p: "1 < p" by (simp add: prime_def)
  assume "x \<in> \<rat>"
  then obtain m n where
    n: "n \<noteq> 0" and x_rat: "\<bar>x\<bar> = real m / real n" and gcd: "gcd (m, n) = 1" ..
  have eq: "m\<twosuperior> = p * n\<twosuperior>"
  proof -
    from n x_rat have "real m = \<bar>x\<bar> * real n" by simp
    hence "real (m\<twosuperior>) = x\<twosuperior> * real (n\<twosuperior>)" by (simp split: abs_split)
    also from x_sqrt have "... = real (p * n\<twosuperior>)" by simp
    finally show ?thesis ..
  qed
  have "p dvd m \<and> p dvd n"
  proof
    from eq have "p dvd m\<twosuperior>" ..
    with p_prime show "p dvd m" by (rule prime_dvd_square)
    then obtain k where "m = p * k" ..
    with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: mult_ac)
    with p have "n\<twosuperior> = p * k\<twosuperior>" by simp
    hence "p dvd n\<twosuperior>" ..
    with p_prime show "p dvd n" by (rule prime_dvd_square)
  qed
  hence "p dvd gcd (m, n)" ..
  with gcd have "p dvd 1" by simp
  hence "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed


subsection {* Variations *}

text {*
  Just for the record: we instantiate the main theorem for the
  specific prime number @{text 2} (real mathematicians would never do
  this formally :-).
*}

theorem "x\<twosuperior> = real (# 2::nat) ==> x \<notin> \<rat>"
proof (rule sqrt_prime_irrational)
  {
    fix m :: nat assume dvd: "m dvd # 2"
    hence "m \<le> # 2" by (simp add: dvd_imp_le)
    moreover from dvd have "m \<noteq> 0" by (auto dest: dvd_0_left iff del: neq0_conv)
    ultimately have "m = 1 \<or> m = # 2" by arith
  }
  thus "# 2 \<in> prime" by (simp add: prime_def)
qed

text {*
  \medskip An alternative version of the main proof, using mostly
  linear forward-reasoning.  While this results in less top-down
  structure, it is probably closer to proofs seen in mathematics.
*}

theorem "x\<twosuperior> = real p ==> p \<in> prime ==> x \<notin> \<rat>"
proof
  assume x_sqrt: "x\<twosuperior> = real p"
  assume p_prime: "p \<in> prime"
  hence p: "1 < p" by (simp add: prime_def)
  assume "x \<in> \<rat>"
  then obtain m n where
    n: "n \<noteq> 0" and x_rat: "\<bar>x\<bar> = real m / real n" and gcd: "gcd (m, n) = 1" ..
  from n x_rat have "real m = \<bar>x\<bar> * real n" by simp
  hence "real (m\<twosuperior>) = x\<twosuperior> * real (n\<twosuperior>)" by (simp split: abs_split)
  also from x_sqrt have "... = real (p * n\<twosuperior>)" by simp
  finally have eq: "m\<twosuperior> = p * n\<twosuperior>" ..
  hence "p dvd m\<twosuperior>" ..
  with p_prime have dvd_m: "p dvd m" by (rule prime_dvd_square)
  then obtain k where "m = p * k" ..
  with eq have "p * n\<twosuperior> = p\<twosuperior> * k\<twosuperior>" by (auto simp add: mult_ac)
  with p have "n\<twosuperior> = p * k\<twosuperior>" by simp
  hence "p dvd n\<twosuperior>" ..
  with p_prime have "p dvd n" by (rule prime_dvd_square)
  with dvd_m have "p dvd gcd (m, n)" by (rule gcd_greatest)
  with gcd have "p dvd 1" by simp
  hence "p \<le> 1" by (simp add: dvd_imp_le)
  with p show False by simp
qed

end
