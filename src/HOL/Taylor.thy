(*  Title:      HOL/Taylor.thy
    Author:     Lukas Bulwahn, Bernhard Haeupler, Technische Universitaet Muenchen
*)

section {* Taylor series *}

theory Taylor
imports MacLaurin
begin

text {*
We use MacLaurin and the translation of the expansion point @{text c} to @{text 0}
to prove Taylor's theorem.
*}

lemma taylor_up: 
  assumes INIT: "n>0" "diff 0 = f"
  and DERIV: "(\<forall> m t. m < n & a \<le> t & t \<le> b \<longrightarrow> DERIV (diff m) t :> (diff (Suc m) t))"
  and INTERV: "a \<le> c" "c < b" 
  shows "\<exists>t::real. c < t & t < b & 
    f b = (\<Sum>m<n. (diff m c / (fact m)) * (b - c)^m) + (diff n t / (fact n)) * (b - c)^n"
proof -
  from INTERV have "0 < b-c" by arith
  moreover 
  from INIT have "n>0" "((\<lambda>m x. diff m (x + c)) 0) = (\<lambda>x. f (x + c))" by auto
  moreover
  have "ALL m t. m < n & 0 <= t & t <= b - c --> DERIV (%x. diff m (x + c)) t :> diff (Suc m) (t + c)"
  proof (intro strip)
    fix m t
    assume "m < n & 0 <= t & t <= b - c"
    with DERIV and INTERV have "DERIV (diff m) (t + c) :> diff (Suc m) (t + c)" by auto
    moreover
    from DERIV_ident and DERIV_const have "DERIV (%x. x + c) t :> 1+0" by (rule DERIV_add)
    ultimately have "DERIV (%x. diff m (x + c)) t :> diff (Suc m) (t + c) * (1+0)"
      by (rule DERIV_chain2)
    thus "DERIV (%x. diff m (x + c)) t :> diff (Suc m) (t + c)" by simp
  qed
  ultimately obtain x where 
        "0 < x & x < b - c & 
        f (b - c + c) = (\<Sum>m<n. diff m (0 + c) / (fact m) * (b - c) ^ m) +
          diff n (x + c) / (fact n) * (b - c) ^ n"
     by (rule Maclaurin [THEN exE])
  then have "c<x+c & x+c<b \<and> f b = (\<Sum>m<n. diff m c / (fact m) * (b - c) ^ m) +
    diff n (x+c) / (fact n) * (b - c) ^ n"
    by fastforce
  thus ?thesis by fastforce
qed

lemma taylor_down:
  fixes a::real
  assumes INIT: "n>0" "diff 0 = f"
  and DERIV: "(\<forall> m t. m < n & a \<le> t & t \<le> b \<longrightarrow> DERIV (diff m) t :> (diff (Suc m) t))"
  and INTERV: "a < c" "c \<le> b"
  shows "\<exists> t. a < t & t < c & 
    f a = (\<Sum>m<n. (diff m c / (fact m)) * (a - c)^m) + (diff n t / (fact n)) * (a - c)^n" 
proof -
  from INTERV have "a-c < 0" by arith
  moreover 
  from INIT have "n>0" "((\<lambda>m x. diff m (x + c)) 0) = (\<lambda>x. f (x + c))" by auto
  moreover
  have "ALL m t. m < n & a-c <= t & t <= 0 --> DERIV (%x. diff m (x + c)) t :> diff (Suc m) (t + c)"
  proof (rule allI impI)+
    fix m t
    assume "m < n & a-c <= t & t <= 0"
    with DERIV and INTERV have "DERIV (diff m) (t + c) :> diff (Suc m) (t + c)" by auto 
    moreover
    from DERIV_ident and DERIV_const have "DERIV (%x. x + c) t :> 1+0" by (rule DERIV_add)
    ultimately have "DERIV (%x. diff m (x + c)) t :> diff (Suc m) (t + c) * (1+0)" by (rule DERIV_chain2)
    thus "DERIV (%x. diff m (x + c)) t :> diff (Suc m) (t + c)" by simp
  qed
  ultimately obtain x where 
         "a - c < x & x < 0 &
      f (a - c + c) = (SUM m<n. diff m (0 + c) / (fact m) * (a - c) ^ m) +
        diff n (x + c) / (fact n) * (a - c) ^ n"
     by (rule Maclaurin_minus [THEN exE])
  then have "a<x+c & x+c<c \<and> f a = (\<Sum>m<n. diff m c / (fact m) * (a - c) ^ m) +
      diff n (x+c) / (fact n) * (a - c) ^ n"
    by fastforce
  thus ?thesis by fastforce
qed

lemma taylor:
  fixes a::real
  assumes INIT: "n>0" "diff 0 = f"
  and DERIV: "(\<forall> m t. m < n & a \<le> t & t \<le> b \<longrightarrow> DERIV (diff m) t :> (diff (Suc m) t))"
  and INTERV: "a \<le> c " "c \<le> b" "a \<le> x" "x \<le> b" "x \<noteq> c" 
  shows "\<exists> t. (if x<c then (x < t & t < c) else (c < t & t < x)) &
    f x = (\<Sum>m<n. (diff m c / (fact m)) * (x - c)^m) + (diff n t / (fact n)) * (x - c)^n" 
proof (cases "x<c")
  case True
  note INIT
  moreover from DERIV and INTERV
  have "\<forall>m t. m < n \<and> x \<le> t \<and> t \<le> b \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    by fastforce
  moreover note True
  moreover from INTERV have "c \<le> b" by simp
  ultimately have "\<exists>t>x. t < c \<and> f x =
    (\<Sum>m<n. diff m c / (fact m) * (x - c) ^ m) + diff n t / (fact n) * (x - c) ^ n"
    by (rule taylor_down)
  with True show ?thesis by simp
next
  case False
  note INIT
  moreover from DERIV and INTERV
  have "\<forall>m t. m < n \<and> a \<le> t \<and> t \<le> x \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t"
    by fastforce
  moreover from INTERV have "a \<le> c" by arith
  moreover from False and INTERV have "c < x" by arith
  ultimately have "\<exists>t>c. t < x \<and> f x =
    (\<Sum>m<n. diff m c / (fact m) * (x - c) ^ m) + diff n t / (fact n) * (x - c) ^ n" 
    by (rule taylor_up)
  with False show ?thesis by simp
qed

end
