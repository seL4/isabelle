(*  Title:      HOL/Old_Number_Theory/Legacy_GCD.thy
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

header {* The Greatest Common Divisor *}

theory Legacy_GCD
imports Main
begin

text {*
  See \cite{davenport92}. \bigskip
*}

subsection {* Specification of GCD on nats *}

definition
  is_gcd :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where -- {* @{term gcd} as a relation *}
  "is_gcd m n p \<longleftrightarrow> p dvd m \<and> p dvd n \<and>
    (\<forall>d. d dvd m \<longrightarrow> d dvd n \<longrightarrow> d dvd p)"

text {* Uniqueness *}

lemma is_gcd_unique: "is_gcd a b m \<Longrightarrow> is_gcd a b n \<Longrightarrow> m = n"
  by (simp add: is_gcd_def) (blast intro: dvd_antisym)

text {* Connection to divides relation *}

lemma is_gcd_dvd: "is_gcd a b m \<Longrightarrow> k dvd a \<Longrightarrow> k dvd b \<Longrightarrow> k dvd m"
  by (auto simp add: is_gcd_def)

text {* Commutativity *}

lemma is_gcd_commute: "is_gcd m n k = is_gcd n m k"
  by (auto simp add: is_gcd_def)


subsection {* GCD on nat by Euclid's algorithm *}

fun gcd :: "nat => nat => nat"
  where "gcd m n = (if n = 0 then m else gcd n (m mod n))"

lemma gcd_induct [case_names "0" rec]:
  fixes m n :: nat
  assumes "\<And>m. P m 0"
    and "\<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n"
  shows "P m n"
proof (induct m n rule: gcd.induct)
  case (1 m n)
  with assms show ?case by (cases "n = 0") simp_all
qed

lemma gcd_0 [simp, algebra]: "gcd m 0 = m"
  by simp

lemma gcd_0_left [simp,algebra]: "gcd 0 m = m"
  by simp

lemma gcd_non_0: "n > 0 \<Longrightarrow> gcd m n = gcd n (m mod n)"
  by simp

lemma gcd_1 [simp, algebra]: "gcd m (Suc 0) = Suc 0"
  by simp

lemma nat_gcd_1_right [simp, algebra]: "gcd m 1 = 1"
  unfolding One_nat_def by (rule gcd_1)

declare gcd.simps [simp del]

text {*
  \medskip @{term "gcd m n"} divides @{text m} and @{text n}.  The
  conjunctions don't seem provable separately.
*}

lemma gcd_dvd1 [iff, algebra]: "gcd m n dvd m"
  and gcd_dvd2 [iff, algebra]: "gcd m n dvd n"
  apply (induct m n rule: gcd_induct)
     apply (simp_all add: gcd_non_0)
  apply (blast dest: dvd_mod_imp_dvd)
  done

text {*
  \medskip Maximality: for all @{term m}, @{term n}, @{term k}
  naturals, if @{term k} divides @{term m} and @{term k} divides
  @{term n} then @{term k} divides @{term "gcd m n"}.
*}

lemma gcd_greatest: "k dvd m \<Longrightarrow> k dvd n \<Longrightarrow> k dvd gcd m n"
  by (induct m n rule: gcd_induct) (simp_all add: gcd_non_0 dvd_mod)

text {*
  \medskip Function gcd yields the Greatest Common Divisor.
*}

lemma is_gcd: "is_gcd m n (gcd m n) "
  by (simp add: is_gcd_def gcd_greatest)


subsection {* Derived laws for GCD *}

lemma gcd_greatest_iff [iff, algebra]: "k dvd gcd m n \<longleftrightarrow> k dvd m \<and> k dvd n"
  by (blast intro!: gcd_greatest intro: dvd_trans)

lemma gcd_zero[algebra]: "gcd m n = 0 \<longleftrightarrow> m = 0 \<and> n = 0"
  by (simp only: dvd_0_left_iff [symmetric] gcd_greatest_iff)

lemma gcd_commute: "gcd m n = gcd n m"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (subst is_gcd_commute)
  apply (simp add: is_gcd)
  done

lemma gcd_assoc: "gcd (gcd k m) n = gcd k (gcd m n)"
  apply (rule is_gcd_unique)
   apply (rule is_gcd)
  apply (simp add: is_gcd_def)
  apply (blast intro: dvd_trans)
  done

lemma gcd_1_left [simp, algebra]: "gcd (Suc 0) m = Suc 0"
  by (simp add: gcd_commute)

lemma nat_gcd_1_left [simp, algebra]: "gcd 1 m = 1"
  unfolding One_nat_def by (rule gcd_1_left)

text {*
  \medskip Multiplication laws
*}

lemma gcd_mult_distrib2: "k * gcd m n = gcd (k * m) (k * n)"
    -- {* \cite[page 27]{davenport92} *}
  apply (induct m n rule: gcd_induct)
   apply simp
  apply (case_tac "k = 0")
   apply (simp_all add: gcd_non_0)
  done

lemma gcd_mult [simp, algebra]: "gcd k (k * n) = k"
  apply (rule gcd_mult_distrib2 [of k 1 n, simplified, symmetric])
  done

lemma gcd_self [simp, algebra]: "gcd k k = k"
  apply (rule gcd_mult [of k 1, simplified])
  done

lemma relprime_dvd_mult: "gcd k n = 1 ==> k dvd m * n ==> k dvd m"
  apply (insert gcd_mult_distrib2 [of m k n])
  apply simp
  apply (erule_tac t = m in ssubst)
  apply simp
  done

lemma relprime_dvd_mult_iff: "gcd k n = 1 ==> (k dvd m * n) = (k dvd m)"
  by (auto intro: relprime_dvd_mult dvd_mult2)

lemma gcd_mult_cancel: "gcd k n = 1 ==> gcd (k * m) n = gcd m n"
  apply (rule dvd_antisym)
   apply (rule gcd_greatest)
    apply (rule_tac n = k in relprime_dvd_mult)
     apply (simp add: gcd_assoc)
     apply (simp add: gcd_commute)
    apply (simp_all add: mult_commute)
  done


text {* \medskip Addition laws *}

lemma gcd_add1 [simp, algebra]: "gcd (m + n) n = gcd m n"
  by (cases "n = 0") (auto simp add: gcd_non_0)

lemma gcd_add2 [simp, algebra]: "gcd m (m + n) = gcd m n"
proof -
  have "gcd m (m + n) = gcd (m + n) m" by (rule gcd_commute)
  also have "... = gcd (n + m) m" by (simp add: add_commute)
  also have "... = gcd n m" by simp
  also have  "... = gcd m n" by (rule gcd_commute)
  finally show ?thesis .
qed

lemma gcd_add2' [simp, algebra]: "gcd m (n + m) = gcd m n"
  apply (subst add_commute)
  apply (rule gcd_add2)
  done

lemma gcd_add_mult[algebra]: "gcd m (k * m + n) = gcd m n"
  by (induct k) (simp_all add: add_assoc)

lemma gcd_dvd_prod: "gcd m n dvd m * n" 
  using mult_dvd_mono [of 1] by auto

text {*
  \medskip Division by gcd yields rrelatively primes.
*}

lemma div_gcd_relprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "gcd (a div gcd a b) (b div gcd a b) = 1"
proof -
  let ?g = "gcd a b"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "gcd ?a' ?b'"
  have dvdg: "?g dvd a" "?g dvd b" by simp_all
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'" by simp_all
  from dvdg dvdg' obtain ka kb ka' kb' where
      kab: "a = ?g * ka" "b = ?g * kb" "?a' = ?g' * ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  then have "?g * ?a' = (?g * ?g') * ka'" "?g * ?b' = (?g * ?g') * kb'" by simp_all
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp add: dvd_mult_div_cancel [OF dvdg(1)]
      dvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0" using nz by (simp add: gcd_zero)
  then have gp: "?g > 0" by simp
  from gcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  with dvd_mult_cancel1 [OF gp] show "?g' = 1" by simp
qed


lemma gcd_unique: "d dvd a\<and>d dvd b \<and> (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
proof(auto)
  assume H: "d dvd a" "d dvd b" "\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d"
  from H(3)[rule_format] gcd_dvd1[of a b] gcd_dvd2[of a b] 
  have th: "gcd a b dvd d" by blast
  from dvd_antisym[OF th gcd_greatest[OF H(1,2)]]  show "d = gcd a b" by blast 
qed

lemma gcd_eq: assumes H: "\<forall>d. d dvd x \<and> d dvd y \<longleftrightarrow> d dvd u \<and> d dvd v"
  shows "gcd x y = gcd u v"
proof-
  from H have "\<forall>d. d dvd x \<and> d dvd y \<longleftrightarrow> d dvd gcd u v" by simp
  with gcd_unique[of "gcd u v" x y]  show ?thesis by auto
qed

lemma ind_euclid:
  assumes c: " \<forall>a b. P (a::nat) b \<longleftrightarrow> P b a" and z: "\<forall>a. P a 0"
  and add: "\<forall>a b. P a b \<longrightarrow> P a (a + b)"
  shows "P a b"
proof(induct "a + b" arbitrary: a b rule: less_induct)
  case less
  have "a = b \<or> a < b \<or> b < a" by arith
  moreover {assume eq: "a= b"
    from add[rule_format, OF z[rule_format, of a]] have "P a b" using eq
    by simp}
  moreover
  {assume lt: "a < b"
    hence "a + b - a < a + b \<or> a = 0" by arith
    moreover
    {assume "a =0" with z c have "P a b" by blast }
    moreover
    {assume "a + b - a < a + b"
      also have th0: "a + b - a = a + (b - a)" using lt by arith
      finally have "a + (b - a) < a + b" .
      then have "P a (a + (b - a))" by (rule add[rule_format, OF less])
      then have "P a b" by (simp add: th0[symmetric])}
    ultimately have "P a b" by blast}
  moreover
  {assume lt: "a > b"
    hence "b + a - b < a + b \<or> b = 0" by arith
    moreover
    {assume "b =0" with z c have "P a b" by blast }
    moreover
    {assume "b + a - b < a + b"
      also have th0: "b + a - b = b + (a - b)" using lt by arith
      finally have "b + (a - b) < a + b" .
      then have "P b (b + (a - b))" by (rule add[rule_format, OF less])
      then have "P b a" by (simp add: th0[symmetric])
      hence "P a b" using c by blast }
    ultimately have "P a b" by blast}
ultimately  show "P a b" by blast
qed

lemma bezout_lemma: 
  assumes ex: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x = b * y + d \<or> b * x = a * y + d)"
  shows "\<exists>d x y. d dvd a \<and> d dvd a + b \<and> (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
using ex
apply clarsimp
apply (rule_tac x="d" in exI, simp)
apply (case_tac "a * x = b * y + d" , simp_all)
apply (rule_tac x="x + y" in exI)
apply (rule_tac x="y" in exI)
apply algebra
apply (rule_tac x="x" in exI)
apply (rule_tac x="x + y" in exI)
apply algebra
done

lemma bezout_add: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x = b * y + d \<or> b * x = a * y + d)"
apply(induct a b rule: ind_euclid)
apply blast
apply clarify
apply (rule_tac x="a" in exI, simp)
apply clarsimp
apply (rule_tac x="d" in exI)
apply (case_tac "a * x = b * y + d", simp_all)
apply (rule_tac x="x+y" in exI)
apply (rule_tac x="y" in exI)
apply algebra
apply (rule_tac x="x" in exI)
apply (rule_tac x="x+y" in exI)
apply algebra
done

lemma bezout: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and> (a * x - b * y = d \<or> b * x - a * y = d)"
using bezout_add[of a b]
apply clarsimp
apply (rule_tac x="d" in exI, simp)
apply (rule_tac x="x" in exI)
apply (rule_tac x="y" in exI)
apply auto
done


text {* We can get a stronger version with a nonzeroness assumption. *}
lemma divides_le: "m dvd n ==> m <= n \<or> n = (0::nat)" by (auto simp add: dvd_def)

lemma bezout_add_strong: assumes nz: "a \<noteq> (0::nat)"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
proof-
  from nz have ap: "a > 0" by simp
 from bezout_add[of a b] 
 have "(\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d) \<or> (\<exists>d x y. d dvd a \<and> d dvd b \<and> b * x = a * y + d)" by blast
 moreover
 {fix d x y assume H: "d dvd a" "d dvd b" "a * x = b * y + d"
   from H have ?thesis by blast }
 moreover
 {fix d x y assume H: "d dvd a" "d dvd b" "b * x = a * y + d"
   {assume b0: "b = 0" with H  have ?thesis by simp}
   moreover 
   {assume b: "b \<noteq> 0" hence bp: "b > 0" by simp
     from divides_le[OF H(2)] b have "d < b \<or> d = b" using le_less by blast
     moreover
     {assume db: "d=b"
       from nz H db have ?thesis apply simp
         apply (rule exI[where x = b], simp)
         apply (rule exI[where x = b])
        by (rule exI[where x = "a - 1"], simp add: diff_mult_distrib2)}
    moreover
    {assume db: "d < b" 
        {assume "x=0" hence ?thesis using nz H by simp }
        moreover
        {assume x0: "x \<noteq> 0" hence xp: "x > 0" by simp
          
          from db have "d \<le> b - 1" by simp
          hence "d*b \<le> b*(b - 1)" by simp
          with xp mult_mono[of "1" "x" "d*b" "b*(b - 1)"]
          have dble: "d*b \<le> x*b*(b - 1)" using bp by simp
          from H (3) have "a * ((b - 1) * y) + d * (b - 1 + 1) = d + x*b*(b - 1)" by algebra
          hence "a * ((b - 1) * y) = d + x*b*(b - 1) - d*b" using bp by simp
          hence "a * ((b - 1) * y) = d + (x*b*(b - 1) - d*b)" 
            by (simp only: diff_add_assoc[OF dble, of d, symmetric])
          hence "a * ((b - 1) * y) = b*(x*(b - 1) - d) + d"
            by (simp only: diff_mult_distrib2 add_commute mult_ac)
          hence ?thesis using H(1,2)
            apply -
            apply (rule exI[where x=d], simp)
            apply (rule exI[where x="(b - 1) * y"])
            by (rule exI[where x="x*(b - 1) - d"], simp)}
        ultimately have ?thesis by blast}
    ultimately have ?thesis by blast}
  ultimately have ?thesis by blast}
 ultimately show ?thesis by blast
qed


lemma bezout_gcd: "\<exists>x y. a * x - b * y = gcd a b \<or> b * x - a * y = gcd a b"
proof-
  let ?g = "gcd a b"
  from bezout[of a b] obtain d x y where d: "d dvd a" "d dvd b" "a * x - b * y = d \<or> b * x - a * y = d" by blast
  from d(1,2) have "d dvd ?g" by simp
  then obtain k where k: "?g = d*k" unfolding dvd_def by blast
  from d(3) have "(a * x - b * y)*k = d*k \<or> (b * x - a * y)*k = d*k" by blast 
  hence "a * x * k - b * y*k = d*k \<or> b * x * k - a * y*k = d*k" 
    by (algebra add: diff_mult_distrib)
  hence "a * (x * k) - b * (y*k) = ?g \<or> b * (x * k) - a * (y*k) = ?g" 
    by (simp add: k mult_assoc)
  thus ?thesis by blast
qed

lemma bezout_gcd_strong: assumes a: "a \<noteq> 0" 
  shows "\<exists>x y. a * x = b * y + gcd a b"
proof-
  let ?g = "gcd a b"
  from bezout_add_strong[OF a, of b]
  obtain d x y where d: "d dvd a" "d dvd b" "a * x = b * y + d" by blast
  from d(1,2) have "d dvd ?g" by simp
  then obtain k where k: "?g = d*k" unfolding dvd_def by blast
  from d(3) have "a * x * k = (b * y + d) *k " by algebra
  hence "a * (x * k) = b * (y*k) + ?g" by (algebra add: k)
  thus ?thesis by blast
qed

lemma gcd_mult_distrib: "gcd(a * c) (b * c) = c * gcd a b"
by(simp add: gcd_mult_distrib2 mult_commute)

lemma gcd_bezout: "(\<exists>x y. a * x - b * y = d \<or> b * x - a * y = d) \<longleftrightarrow> gcd a b dvd d"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?g = "gcd a b"
  {assume H: ?rhs then obtain k where k: "d = ?g*k" unfolding dvd_def by blast
    from bezout_gcd[of a b] obtain x y where xy: "a * x - b * y = ?g \<or> b * x - a * y = ?g"
      by blast
    hence "(a * x - b * y)*k = ?g*k \<or> (b * x - a * y)*k = ?g*k" by auto
    hence "a * x*k - b * y*k = ?g*k \<or> b * x * k - a * y*k = ?g*k" 
      by (simp only: diff_mult_distrib)
    hence "a * (x*k) - b * (y*k) = d \<or> b * (x * k) - a * (y*k) = d"
      by (simp add: k[symmetric] mult_assoc)
    hence ?lhs by blast}
  moreover
  {fix x y assume H: "a * x - b * y = d \<or> b * x - a * y = d"
    have dv: "?g dvd a*x" "?g dvd b * y" "?g dvd b*x" "?g dvd a * y"
      using dvd_mult2[OF gcd_dvd1[of a b]] dvd_mult2[OF gcd_dvd2[of a b]] by simp_all
    from dvd_diff_nat[OF dv(1,2)] dvd_diff_nat[OF dv(3,4)] H
    have ?rhs by auto}
  ultimately show ?thesis by blast
qed

lemma gcd_bezout_sum: assumes H:"a * x + b * y = d" shows "gcd a b dvd d"
proof-
  let ?g = "gcd a b"
    have dv: "?g dvd a*x" "?g dvd b * y" 
      using dvd_mult2[OF gcd_dvd1[of a b]] dvd_mult2[OF gcd_dvd2[of a b]] by simp_all
    from dvd_add[OF dv] H
    show ?thesis by auto
qed

lemma gcd_mult': "gcd b (a * b) = b"
by (simp add: mult_commute[of a b]) 

lemma gcd_add: "gcd(a + b) b = gcd a b" 
  "gcd(b + a) b = gcd a b" "gcd a (a + b) = gcd a b" "gcd a (b + a) = gcd a b"
by (simp_all add: gcd_commute)

lemma gcd_sub: "b <= a ==> gcd(a - b) b = gcd a b" "a <= b ==> gcd a (b - a) = gcd a b"
proof-
  {fix a b assume H: "b \<le> (a::nat)"
    hence th: "a - b + b = a" by arith
    from gcd_add(1)[of "a - b" b] th  have "gcd(a - b) b = gcd a b" by simp}
  note th = this
{
  assume ab: "b \<le> a"
  from th[OF ab] show "gcd (a - b)  b = gcd a b" by blast
next
  assume ab: "a \<le> b"
  from th[OF ab] show "gcd a (b - a) = gcd a b" 
    by (simp add: gcd_commute)}
qed


subsection {* LCM defined by GCD *}


definition
  lcm :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  lcm_def: "lcm m n = m * n div gcd m n"

lemma prod_gcd_lcm:
  "m * n = gcd m n * lcm m n"
  unfolding lcm_def by (simp add: dvd_mult_div_cancel [OF gcd_dvd_prod])

lemma lcm_0 [simp]: "lcm m 0 = 0"
  unfolding lcm_def by simp

lemma lcm_1 [simp]: "lcm m 1 = m"
  unfolding lcm_def by simp

lemma lcm_0_left [simp]: "lcm 0 n = 0"
  unfolding lcm_def by simp

lemma lcm_1_left [simp]: "lcm 1 m = m"
  unfolding lcm_def by simp

lemma dvd_pos:
  fixes n m :: nat
  assumes "n > 0" and "m dvd n"
  shows "m > 0"
using assms by (cases m) auto

lemma lcm_least:
  assumes "m dvd k" and "n dvd k"
  shows "lcm m n dvd k"
proof (cases k)
  case 0 then show ?thesis by auto
next
  case (Suc _) then have pos_k: "k > 0" by auto
  from assms dvd_pos [OF this] have pos_mn: "m > 0" "n > 0" by auto
  with gcd_zero [of m n] have pos_gcd: "gcd m n > 0" by simp
  from assms obtain p where k_m: "k = m * p" using dvd_def by blast
  from assms obtain q where k_n: "k = n * q" using dvd_def by blast
  from pos_k k_m have pos_p: "p > 0" by auto
  from pos_k k_n have pos_q: "q > 0" by auto
  have "k * k * gcd q p = k * gcd (k * q) (k * p)"
    by (simp add: mult_ac gcd_mult_distrib2)
  also have "\<dots> = k * gcd (m * p * q) (n * q * p)"
    by (simp add: k_m [symmetric] k_n [symmetric])
  also have "\<dots> = k * p * q * gcd m n"
    by (simp add: mult_ac gcd_mult_distrib2)
  finally have "(m * p) * (n * q) * gcd q p = k * p * q * gcd m n"
    by (simp only: k_m [symmetric] k_n [symmetric])
  then have "p * q * m * n * gcd q p = p * q * k * gcd m n"
    by (simp add: mult_ac)
  with pos_p pos_q have "m * n * gcd q p = k * gcd m n"
    by simp
  with prod_gcd_lcm [of m n]
  have "lcm m n * gcd q p * gcd m n = k * gcd m n"
    by (simp add: mult_ac)
  with pos_gcd have "lcm m n * gcd q p = k" by simp
  then show ?thesis using dvd_def by auto
qed

lemma lcm_dvd1 [iff]:
  "m dvd lcm m n"
proof (cases m)
  case 0 then show ?thesis by simp
next
  case (Suc _)
  then have mpos: "m > 0" by simp
  show ?thesis
  proof (cases n)
    case 0 then show ?thesis by simp
  next
    case (Suc _)
    then have npos: "n > 0" by simp
    have "gcd m n dvd n" by simp
    then obtain k where "n = gcd m n * k" using dvd_def by auto
    then have "m * n div gcd m n = m * (gcd m n * k) div gcd m n" by (simp add: mult_ac)
    also have "\<dots> = m * k" using mpos npos gcd_zero by simp
    finally show ?thesis by (simp add: lcm_def)
  qed
qed

lemma lcm_dvd2 [iff]: 
  "n dvd lcm m n"
proof (cases n)
  case 0 then show ?thesis by simp
next
  case (Suc _)
  then have npos: "n > 0" by simp
  show ?thesis
  proof (cases m)
    case 0 then show ?thesis by simp
  next
    case (Suc _)
    then have mpos: "m > 0" by simp
    have "gcd m n dvd m" by simp
    then obtain k where "m = gcd m n * k" using dvd_def by auto
    then have "m * n div gcd m n = (gcd m n * k) * n div gcd m n" by (simp add: mult_ac)
    also have "\<dots> = n * k" using mpos npos gcd_zero by simp
    finally show ?thesis by (simp add: lcm_def)
  qed
qed

lemma gcd_add1_eq: "gcd (m + k) k = gcd (m + k) m"
  by (simp add: gcd_commute)

lemma gcd_diff2: "m \<le> n ==> gcd n (n - m) = gcd n m"
  apply (subgoal_tac "n = m + (n - m)")
  apply (erule ssubst, rule gcd_add1_eq, simp)  
  done


subsection {* GCD and LCM on integers *}

definition
  zgcd :: "int \<Rightarrow> int \<Rightarrow> int" where
  "zgcd i j = int (gcd (nat (abs i)) (nat (abs j)))"

lemma zgcd_zdvd1 [iff, algebra]: "zgcd i j dvd i"
by (simp add: zgcd_def int_dvd_iff)

lemma zgcd_zdvd2 [iff, algebra]: "zgcd i j dvd j"
by (simp add: zgcd_def int_dvd_iff)

lemma zgcd_pos: "zgcd i j \<ge> 0"
by (simp add: zgcd_def)

lemma zgcd0 [simp,algebra]: "(zgcd i j = 0) = (i = 0 \<and> j = 0)"
by (simp add: zgcd_def gcd_zero)

lemma zgcd_commute: "zgcd i j = zgcd j i"
unfolding zgcd_def by (simp add: gcd_commute)

lemma zgcd_zminus [simp, algebra]: "zgcd (- i) j = zgcd i j"
unfolding zgcd_def by simp

lemma zgcd_zminus2 [simp, algebra]: "zgcd i (- j) = zgcd i j"
unfolding zgcd_def by simp

  (* should be solved by algebra*)
lemma zrelprime_dvd_mult: "zgcd i j = 1 \<Longrightarrow> i dvd k * j \<Longrightarrow> i dvd k"
  unfolding zgcd_def
proof -
  assume "int (gcd (nat \<bar>i\<bar>) (nat \<bar>j\<bar>)) = 1" "i dvd k * j"
  then have g: "gcd (nat \<bar>i\<bar>) (nat \<bar>j\<bar>) = 1" by simp
  from `i dvd k * j` obtain h where h: "k*j = i*h" unfolding dvd_def by blast
  have th: "nat \<bar>i\<bar> dvd nat \<bar>k\<bar> * nat \<bar>j\<bar>"
    unfolding dvd_def
    by (rule_tac x= "nat \<bar>h\<bar>" in exI, simp add: h nat_abs_mult_distrib [symmetric])
  from relprime_dvd_mult [OF g th] obtain h' where h': "nat \<bar>k\<bar> = nat \<bar>i\<bar> * h'"
    unfolding dvd_def by blast
  from h' have "int (nat \<bar>k\<bar>) = int (nat \<bar>i\<bar> * h')" by simp
  then have "\<bar>k\<bar> = \<bar>i\<bar> * int h'" by (simp add: int_mult)
  then show ?thesis
    apply (subst abs_dvd_iff [symmetric])
    apply (subst dvd_abs_iff [symmetric])
    apply (unfold dvd_def)
    apply (rule_tac x = "int h'" in exI, simp)
    done
qed

lemma int_nat_abs: "int (nat (abs x)) = abs x" by arith

lemma zgcd_greatest:
  assumes "k dvd m" and "k dvd n"
  shows "k dvd zgcd m n"
proof -
  let ?k' = "nat \<bar>k\<bar>"
  let ?m' = "nat \<bar>m\<bar>"
  let ?n' = "nat \<bar>n\<bar>"
  from `k dvd m` and `k dvd n` have dvd': "?k' dvd ?m'" "?k' dvd ?n'"
    unfolding zdvd_int by (simp_all only: int_nat_abs abs_dvd_iff dvd_abs_iff)
  from gcd_greatest [OF dvd'] have "int (nat \<bar>k\<bar>) dvd zgcd m n"
    unfolding zgcd_def by (simp only: zdvd_int)
  then have "\<bar>k\<bar> dvd zgcd m n" by (simp only: int_nat_abs)
  then show "k dvd zgcd m n" by simp
qed

lemma div_zgcd_relprime:
  assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
  shows "zgcd (a div (zgcd a b)) (b div (zgcd a b)) = 1"
proof -
  from nz have nz': "nat \<bar>a\<bar> \<noteq> 0 \<or> nat \<bar>b\<bar> \<noteq> 0" by arith 
  let ?g = "zgcd a b"
  let ?a' = "a div ?g"
  let ?b' = "b div ?g"
  let ?g' = "zgcd ?a' ?b'"
  have dvdg: "?g dvd a" "?g dvd b" by simp_all
  have dvdg': "?g' dvd ?a'" "?g' dvd ?b'" by simp_all
  from dvdg dvdg' obtain ka kb ka' kb' where
   kab: "a = ?g*ka" "b = ?g*kb" "?a' = ?g'*ka'" "?b' = ?g' * kb'"
    unfolding dvd_def by blast
  then have "?g* ?a' = (?g * ?g') * ka'" "?g* ?b' = (?g * ?g') * kb'" by simp_all
  then have dvdgg':"?g * ?g' dvd a" "?g* ?g' dvd b"
    by (auto simp add: zdvd_mult_div_cancel [OF dvdg(1)]
      zdvd_mult_div_cancel [OF dvdg(2)] dvd_def)
  have "?g \<noteq> 0" using nz by simp
  then have gp: "?g \<noteq> 0" using zgcd_pos[where i="a" and j="b"] by arith
  from zgcd_greatest [OF dvdgg'] have "?g * ?g' dvd ?g" .
  with zdvd_mult_cancel1 [OF gp] have "\<bar>?g'\<bar> = 1" by simp
  with zgcd_pos show "?g' = 1" by simp
qed

lemma zgcd_0 [simp, algebra]: "zgcd m 0 = abs m"
  by (simp add: zgcd_def abs_if)

lemma zgcd_0_left [simp, algebra]: "zgcd 0 m = abs m"
  by (simp add: zgcd_def abs_if)

lemma zgcd_non_0: "0 < n ==> zgcd m n = zgcd n (m mod n)"
  apply (frule_tac b = n and a = m in pos_mod_sign)
  apply (simp del: pos_mod_sign add: zgcd_def abs_if nat_mod_distrib)
  apply (auto simp add: gcd_non_0 nat_mod_distrib [symmetric] zmod_zminus1_eq_if)
  apply (frule_tac a = m in pos_mod_bound)
  apply (simp del: pos_mod_bound add: nat_diff_distrib gcd_diff2 nat_le_eq_zle)
  done

lemma zgcd_eq: "zgcd m n = zgcd n (m mod n)"
  apply (cases "n = 0", simp)
  apply (auto simp add: linorder_neq_iff zgcd_non_0)
  apply (cut_tac m = "-m" and n = "-n" in zgcd_non_0, auto)
  done

lemma zgcd_1 [simp, algebra]: "zgcd m 1 = 1"
  by (simp add: zgcd_def abs_if)

lemma zgcd_0_1_iff [simp, algebra]: "zgcd 0 m = 1 \<longleftrightarrow> \<bar>m\<bar> = 1"
  by (simp add: zgcd_def abs_if)

lemma zgcd_greatest_iff[algebra]: "k dvd zgcd m n = (k dvd m \<and> k dvd n)"
  by (simp add: zgcd_def abs_if int_dvd_iff dvd_int_iff nat_dvd_iff)

lemma zgcd_1_left [simp, algebra]: "zgcd 1 m = 1"
  by (simp add: zgcd_def)

lemma zgcd_assoc: "zgcd (zgcd k m) n = zgcd k (zgcd m n)"
  by (simp add: zgcd_def gcd_assoc)

lemma zgcd_left_commute: "zgcd k (zgcd m n) = zgcd m (zgcd k n)"
  apply (rule zgcd_commute [THEN trans])
  apply (rule zgcd_assoc [THEN trans])
  apply (rule zgcd_commute [THEN arg_cong])
  done

lemmas zgcd_ac = zgcd_assoc zgcd_commute zgcd_left_commute
  -- {* addition is an AC-operator *}

lemma zgcd_zmult_distrib2: "0 \<le> k ==> k * zgcd m n = zgcd (k * m) (k * n)"
  by (simp del: minus_mult_right [symmetric]
      add: minus_mult_right nat_mult_distrib zgcd_def abs_if
          mult_less_0_iff gcd_mult_distrib2 [symmetric] of_nat_mult)

lemma zgcd_zmult_distrib2_abs: "zgcd (k * m) (k * n) = abs k * zgcd m n"
  by (simp add: abs_if zgcd_zmult_distrib2)

lemma zgcd_self [simp]: "0 \<le> m ==> zgcd m m = m"
  by (cut_tac k = m and m = 1 and n = 1 in zgcd_zmult_distrib2, simp_all)

lemma zgcd_zmult_eq_self [simp]: "0 \<le> k ==> zgcd k (k * n) = k"
  by (cut_tac k = k and m = 1 and n = n in zgcd_zmult_distrib2, simp_all)

lemma zgcd_zmult_eq_self2 [simp]: "0 \<le> k ==> zgcd (k * n) k = k"
  by (cut_tac k = k and m = n and n = 1 in zgcd_zmult_distrib2, simp_all)


definition "zlcm i j = int (lcm(nat(abs i)) (nat(abs j)))"

lemma dvd_zlcm_self1[simp, algebra]: "i dvd zlcm i j"
by(simp add:zlcm_def dvd_int_iff)

lemma dvd_zlcm_self2[simp, algebra]: "j dvd zlcm i j"
by(simp add:zlcm_def dvd_int_iff)


lemma dvd_imp_dvd_zlcm1:
  assumes "k dvd i" shows "k dvd (zlcm i j)"
proof -
  have "nat(abs k) dvd nat(abs i)" using `k dvd i`
    by(simp add:int_dvd_iff[symmetric] dvd_int_iff[symmetric])
  thus ?thesis by(simp add:zlcm_def dvd_int_iff)(blast intro: dvd_trans)
qed

lemma dvd_imp_dvd_zlcm2:
  assumes "k dvd j" shows "k dvd (zlcm i j)"
proof -
  have "nat(abs k) dvd nat(abs j)" using `k dvd j`
    by(simp add:int_dvd_iff[symmetric] dvd_int_iff[symmetric])
  thus ?thesis by(simp add:zlcm_def dvd_int_iff)(blast intro: dvd_trans)
qed


lemma zdvd_self_abs1: "(d::int) dvd (abs d)"
by (case_tac "d <0", simp_all)

lemma zdvd_self_abs2: "(abs (d::int)) dvd d"
by (case_tac "d<0", simp_all)

(* lcm a b is positive for positive a and b *)

lemma lcm_pos: 
  assumes mpos: "m > 0"
    and npos: "n>0"
  shows "lcm m n > 0"
proof (rule ccontr, simp add: lcm_def gcd_zero)
  assume h:"m*n div gcd m n = 0"
  from mpos npos have "gcd m n \<noteq> 0" using gcd_zero by simp
  hence gcdp: "gcd m n > 0" by simp
  with h
  have "m*n < gcd m n"
    by (cases "m * n < gcd m n") (auto simp add: div_if[OF gcdp, where m="m*n"])
  moreover 
  have "gcd m n dvd m" by simp
  with mpos dvd_imp_le have t1:"gcd m n \<le> m" by simp
  with npos have t1:"gcd m n *n \<le> m*n" by simp
  have "gcd m n \<le> gcd m n*n" using npos by simp
  with t1 have "gcd m n \<le> m*n" by arith
  ultimately show "False" by simp
qed

lemma zlcm_pos: 
  assumes anz: "a \<noteq> 0"
  and bnz: "b \<noteq> 0" 
  shows "0 < zlcm a b"
proof-
  let ?na = "nat (abs a)"
  let ?nb = "nat (abs b)"
  have nap: "?na >0" using anz by simp
  have nbp: "?nb >0" using bnz by simp
  have "0 < lcm ?na ?nb" by (rule lcm_pos[OF nap nbp])
  thus ?thesis by (simp add: zlcm_def)
qed

lemma zgcd_code [code]:
  "zgcd k l = \<bar>if l = 0 then k else zgcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by (simp add: zgcd_def gcd.simps [of "nat \<bar>k\<bar>"] nat_mod_distrib)

end
