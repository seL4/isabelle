(*  Title:      HOL/ex/Puzzle.thy
    ID:         $Id$
    Author:     Tobias Nipkow
*)

header {* Fun with Functions *}

theory Puzzle imports Complex begin

text{* From \emph{Solving Mathematical Problems} by Terence Tao. He quotes
Greitzer's \emph{Interational Mathematical Olympiads 1959--1977} as the
original source. Was first brought to our attention by Herbert Ehler who
provided a similar proof. *}


theorem identity1: fixes f :: "nat \<Rightarrow> nat"
assumes fff: "!!n. f(f(n)) < f(Suc(n))"
shows "f(n) = n"
proof -
  { fix m n have key: "n \<le> m \<Longrightarrow> n \<le> f(m)"
    proof(induct n arbitrary: m)
      case 0 show ?case by simp
    next
      case (Suc n)
      hence "m \<noteq> 0" by simp
      then obtain k where [simp]: "m = Suc k" by (metis not0_implies_Suc)
      have "n \<le> f(k)" using Suc by simp
      hence "n \<le> f(f(k))" using Suc by simp
      also have "\<dots> < f(m)" using fff by simp
      finally show ?case by simp
    qed }
  hence "!!n. n \<le> f(n)" by simp
  hence "!!n. f(n) < f(Suc n)" by(metis fff order_le_less_trans)
  hence "f(n) < n+1" by (metis fff lift_Suc_mono_less_iff[of f] Suc_plus1)
  with `n \<le> f(n)` show "f n = n" by arith
qed


text{* From \emph{Solving Mathematical Problems} by Terence Tao. He quotes
the \emph{Australian Mathematics Competition} 1984 as the original source.
Possible extension:
Should also hold if the range of @{text f} is the reals!
*}

lemma identity2: fixes f :: "nat \<Rightarrow> nat"
assumes "f(k) = k" and "k \<ge> 2"
and f_times: "\<And>m n. f(m*n) = f(m)*f(n)"
and f_mono: "\<And>m n. m<n \<Longrightarrow> f m < f n"
shows "f(n) = n"
proof -
  have 0: "f(0) = 0"
    by (metis f_mono f_times mult_1_right mult_is_0 nat_less_le nat_mult_eq_cancel_disj not_less_eq)
  have 1: "f(1) = 1"
    by (metis f_mono f_times gr_implies_not0 mult_eq_self_implies_10 nat_mult_1_right zero_less_one)
  have 2: "f 2 = 2"
  proof -
    have "2 + (k - 2) = k" using `k \<ge> 2` by arith
    hence "f(2) \<le> 2"
      using mono_nat_linear_lb[of f 2 "k - 2",OF f_mono] `f k = k`
      by simp arith
    thus "f 2 = 2" using 1 f_mono[of 1 2] by arith
  qed
  show ?thesis
  proof(induct rule:less_induct)
    case (less i)
    show ?case
    proof cases
      assume "i\<le>1" thus ?case using 0 1 by (auto simp add:le_Suc_eq)
    next
      assume "~i\<le>1"
      show ?case
      proof cases
	assume "i mod 2 = 0"
	hence "EX k. i=2*k" by arith
	then obtain k where "i = 2*k" ..
	hence "0 < k" and "k<i" using `~i\<le>1` by arith+
	hence "f(k) = k" using less(1) by blast
	thus "f(i) = i" using `i = 2*k` by(simp add:f_times 2)
      next
	assume "i mod 2 \<noteq> 0"
	hence "EX k. i=2*k+1" by arith
	then obtain k where "i = 2*k+1" ..
	hence "0<k" and "k+1<i" using `~i\<le>1` by arith+
	have "2*k < f(2*k+1)"
	proof -
	  have "2*k = 2*f(k)" using less(1) `i=2*k+1` by simp
	  also have "\<dots> = f(2*k)" by(simp add:f_times 2)
	  also have "\<dots> < f(2*k+1)" using f_mono[of "2*k" "2*k+1"] by simp
	  finally show ?thesis .
	qed
	moreover
	have "f(2*k+1) < 2*(k+1)"
	proof -
	  have "f(2*k+1) < f(2*k+2)" using f_mono[of "2*k+1" "2*k+2"] by simp
	  also have "\<dots> = f(2*(k+1))" by simp
	  also have "\<dots> = 2*f(k+1)" by(simp only:f_times 2)
	  also have "f(k+1) = k+1" using less(1) `i=2*k+1` `~i\<le>1` by simp
	  finally show ?thesis .
	qed
	ultimately show "f(i) = i" using `i = 2*k+1` by arith
      qed
    qed
  qed
qed


text{* One more from Tao's booklet. If @{text f} is also assumed to be
continuous, @{term"f(x::real) = x+1"} holds for all reals, not only
rationals. Extend the proof!

The definition of @{text Rats} should go somewhere else. *}

definition "Rats = { real(i::int)/real(n::nat) |i n. n \<noteq> 0}"

theorem plus1:
fixes f :: "real \<Rightarrow> real"
assumes 0: "f 0 = 1" and f_add: "!!x y. f(x+y+1) = f x + f y"

assumes "r : Rats"
shows "f(r) = r + 1"
proof -
  { fix i :: int have "f(real i) = real i + 1"
    proof (induct i rule: Presburger.int_induct[where k=0])
      case base show ?case using 0 by simp
    next
      case (step1 i)
      have "f(real(i+1)) = f(real i + 0 + 1)" by simp
      also have "\<dots> = f(real i) + f 0" by(rule f_add)
      also have "\<dots> = real(i+1) + 1" using step1 0 by simp
      finally show ?case .
    next
      case (step2 i)
      have "f(real i) = f(real(i - 1) + 0 + 1)" by simp
      also have "\<dots> = f(real(i - 1)) + f 0" by(rule f_add)
      also have "\<dots> = f(real(i - 1)) + 1 " using 0 by simp
      finally show ?case using step2 by simp
    qed }
  note f_int = this
  { fix n r have "f(real(Suc n)*r + real n) = real(Suc n) * f r"
    proof(induct n)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "real(Suc(Suc n))*r + real(Suc n) =
            r + (real(Suc n)*r + real n) + 1" (is "?a = ?b")
	by(simp add:real_of_nat_Suc ring_simps)
      hence "f ?a = f ?b" by simp
      also have "\<dots> = f r + f(real(Suc n)*r + real n)" by(rule f_add)
      also have "\<dots> = f r + real(Suc n) * f r" by(simp only:Suc)
      finally show ?case by(simp add:real_of_nat_Suc ring_simps)
    qed }
  note 1 = this
  { fix n::nat and r assume "n>0"
    have "f(real(n)*r + real(n - 1)) = real(n) * f r"
    proof(cases n)
      case 0 thus ?thesis using `n>0` by simp
    next
      case Suc thus ?thesis using `n>0` by (simp add:1)
    qed }
  note f_mult = this
  from `r:Rats` obtain i::int and n::nat where r: "r = real i/real n" and "n>0"
    by(fastsimp simp:Rats_def)
  have "real(n)*f(real i/real n) = f(real i + real(n - 1))"
    using `n>0` by(simp add:f_mult[symmetric])
  also have "\<dots> = f(real(i + int n - 1))" using `n>0`
    by (metis One_nat_def Suc_leI int_1 real_of_int_add real_of_int_of_nat_eq ring_class.ring_simps(4) zdiff_int)
  also have "\<dots> = real(i + int n - 1) + 1" by(rule f_int)
  also have "\<dots> = real i + real n" by arith
  finally show ?thesis using `n>0` unfolding r by (simp add:field_simps)
qed


text{* The only total model of a naive recursion equation of factorial on
integers is 0 for all negative arguments: *}

theorem ifac_neg0: fixes ifac :: "int \<Rightarrow> int"
assumes ifac_rec: "!!i. ifac i = (if i=0 then 1 else i*ifac(i - 1))"
shows "i<0 \<Longrightarrow> ifac i = 0"
proof(rule ccontr)
  assume 0: "i<0" "ifac i \<noteq> 0"
  { fix j assume "j \<le> i"
    have "ifac j \<noteq> 0"
      apply(rule int_le_induct[OF `j\<le>i`])
       apply(rule `ifac i \<noteq> 0`)
      apply (metis `i<0` ifac_rec linorder_not_le mult_eq_0_iff)
      done
  } note below0 = this
  { fix j assume "j<i"
    have "1 < -j" using `j<i` `i<0` by arith
    have "ifac(j - 1) \<noteq> 0" using `j<i` by(simp add: below0)
    then have "\<bar>ifac (j - 1)\<bar> < (-j) * \<bar>ifac (j - 1)\<bar>" using `j<i`
      mult_le_less_imp_less[OF order_refl[of "abs(ifac(j - 1))"] `1 < -j`]
      by(simp add:mult_commute)
    hence "abs(ifac(j - 1)) < abs(ifac j)"
      using `1 < -j` by(simp add: ifac_rec[of "j"] abs_mult)
  } note not_wf = this
  let ?f = "%j. nat(abs(ifac(i - int(j+1))))"
  obtain k where "\<not> ?f (Suc k) < ?f k"
    using wf_no_infinite_down_chainE[OF wf_less, of "?f"] by blast
  moreover have "i - int (k + 1) - 1 = i - int (Suc k + 1)" by arith
  ultimately show False using not_wf[of "i - int(k+1)"]
    by (simp only:) arith
qed

end
