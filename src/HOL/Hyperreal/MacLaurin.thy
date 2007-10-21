(*  ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*MacLaurin Series*}

theory MacLaurin
imports Transcendental
begin

subsection{*Maclaurin's Theorem with Lagrange Form of Remainder*}

text{*This is a very long, messy proof even now that it's been broken down
into lemmas.*}

lemma Maclaurin_lemma:
    "0 < h ==>
     \<exists>B. f h = (\<Sum>m=0..<n. (j m / real (fact m)) * (h^m)) +
               (B * ((h^n) / real(fact n)))"
apply (rule_tac x = "(f h - (\<Sum>m=0..<n. (j m / real (fact m)) * h^m)) *
                 real(fact n) / (h^n)"
       in exI)
apply (simp) 
done

lemma eq_diff_eq': "(x = y - z) = (y = x + (z::real))"
by arith

text{*A crude tactic to differentiate by proof.*}

lemmas deriv_rulesI =
  DERIV_ident DERIV_const DERIV_cos DERIV_cmult
  DERIV_sin DERIV_exp DERIV_inverse DERIV_pow
  DERIV_add DERIV_diff DERIV_mult DERIV_minus
  DERIV_inverse_fun DERIV_quotient DERIV_fun_pow
  DERIV_fun_exp DERIV_fun_sin DERIV_fun_cos
  DERIV_ident DERIV_const DERIV_cos

ML
{*
local
exception DERIV_name;
fun get_fun_name (_ $ (Const ("Lim.deriv",_) $ Abs(_,_, Const (f,_) $ _) $ _ $ _)) = f
|   get_fun_name (_ $ (_ $ (Const ("Lim.deriv",_) $ Abs(_,_, Const (f,_) $ _) $ _ $ _))) = f
|   get_fun_name _ = raise DERIV_name;

in

val deriv_tac =
  SUBGOAL (fn (prem,i) =>
   (resolve_tac @{thms deriv_rulesI} i) ORELSE
    ((rtac (read_instantiate [("f",get_fun_name prem)]
                     @{thm DERIV_chain2}) i) handle DERIV_name => no_tac));;

val DERIV_tac = ALLGOALS(fn i => REPEAT(deriv_tac i));

end
*}

lemma Maclaurin_lemma2:
      "[| \<forall>m t. m < n \<and> 0\<le>t \<and> t\<le>h \<longrightarrow> DERIV (diff m) t :> diff (Suc m) t;
          n = Suc k;
        difg =
        (\<lambda>m t. diff m t -
               ((\<Sum>p = 0..<n - m. diff (m + p) 0 / real (fact p) * t ^ p) +
                B * (t ^ (n - m) / real (fact (n - m)))))|] ==>
        \<forall>m t. m < n & 0 \<le> t & t \<le> h -->
                    DERIV (difg m) t :> difg (Suc m) t"
apply clarify
apply (rule DERIV_diff)
apply (simp (no_asm_simp))
apply (tactic DERIV_tac)
apply (tactic DERIV_tac)
apply (rule_tac [2] lemma_DERIV_subst)
apply (rule_tac [2] DERIV_quotient)
apply (rule_tac [3] DERIV_const)
apply (rule_tac [2] DERIV_pow)
  prefer 3 apply (simp add: fact_diff_Suc)
 prefer 2 apply simp
apply (frule_tac m = m in less_add_one, clarify)
apply (simp del: setsum_op_ivl_Suc)
apply (insert sumr_offset4 [of 1])
apply (simp del: setsum_op_ivl_Suc fact_Suc realpow_Suc)
apply (rule lemma_DERIV_subst)
apply (rule DERIV_add)
apply (rule_tac [2] DERIV_const)
apply (rule DERIV_sumr, clarify)
 prefer 2 apply simp
apply (simp (no_asm) add: divide_inverse mult_assoc del: fact_Suc realpow_Suc)
apply (rule DERIV_cmult)
apply (rule lemma_DERIV_subst)
apply (best intro: DERIV_chain2 intro!: DERIV_intros)
apply (subst fact_Suc)
apply (subst real_of_nat_mult)
apply (simp add: mult_ac)
done


lemma Maclaurin_lemma3:
  fixes difg :: "nat => real => real" shows
     "[|\<forall>k t. k < Suc m \<and> 0\<le>t & t\<le>h \<longrightarrow> DERIV (difg k) t :> difg (Suc k) t;
        \<forall>k<Suc m. difg k 0 = 0; DERIV (difg n) t :> 0;  n < m; 0 < t;
        t < h|]
     ==> \<exists>ta. 0 < ta & ta < t & DERIV (difg (Suc n)) ta :> 0"
apply (rule Rolle, assumption, simp)
apply (drule_tac x = n and P="%k. k<Suc m --> difg k 0 = 0" in spec)
apply (rule DERIV_unique)
prefer 2 apply assumption
apply force
apply (metis DERIV_isCont dlo_simps(4) dlo_simps(9) less_trans_Suc nat_less_le not_less_eq real_le_trans)
apply (metis Suc_less_eq differentiableI dlo_simps(7) dlo_simps(8) dlo_simps(9)   real_le_trans xt1(8))
done

lemma Maclaurin:
   "[| 0 < h; n \<noteq> 0; diff 0 = f;
       \<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. 0 < t &
              t < h &
              f h =
              setsum (%m. (diff m 0 / real (fact m)) * h ^ m) {0..<n} +
              (diff n t / real (fact n)) * h ^ n"
apply (case_tac "n = 0", force)
apply (drule not0_implies_Suc)
apply (erule exE)
apply (frule_tac f=f and n=n and j="%m. diff m 0" in Maclaurin_lemma)
apply (erule exE)
apply (subgoal_tac "\<exists>g.
     g = (%t. f t - (setsum (%m. (diff m 0 / real(fact m)) * t^m) {0..<n} + (B * (t^n / real(fact n)))))")
 prefer 2 apply blast
apply (erule exE)
apply (subgoal_tac "g 0 = 0 & g h =0")
 prefer 2
 apply (simp del: setsum_op_ivl_Suc)
 apply (cut_tac n = m and k = 1 in sumr_offset2)
 apply (simp add: eq_diff_eq' del: setsum_op_ivl_Suc)
apply (subgoal_tac "\<exists>difg. difg = (%m t. diff m t - (setsum (%p. (diff (m + p) 0 / real (fact p)) * (t ^ p)) {0..<n-m} + (B * ((t ^ (n - m)) / real (fact (n - m))))))")
 prefer 2 apply blast
apply (erule exE)
apply (subgoal_tac "difg 0 = g")
 prefer 2 apply simp
apply (frule Maclaurin_lemma2, assumption+)
apply (subgoal_tac "\<forall>ma. ma < n --> (\<exists>t. 0 < t & t < h & difg (Suc ma) t = 0) ")
 apply (drule_tac x = m and P="%m. m<n --> (\<exists>t. ?QQ m t)" in spec)
 apply (erule impE)
  apply (simp (no_asm_simp))
 apply (erule exE)
 apply (rule_tac x = t in exI)
 apply (simp del: realpow_Suc fact_Suc)
apply (subgoal_tac "\<forall>m. m < n --> difg m 0 = 0")
 prefer 2
 apply clarify
 apply simp
 apply (frule_tac m = ma in less_add_one, clarify)
 apply (simp del: setsum_op_ivl_Suc)
apply (insert sumr_offset4 [of 1])
apply (simp del: setsum_op_ivl_Suc fact_Suc realpow_Suc)
apply (subgoal_tac "\<forall>m. m < n --> (\<exists>t. 0 < t & t < h & DERIV (difg m) t :> 0) ")
apply (rule allI, rule impI)
apply (drule_tac x = ma and P="%m. m<n --> (\<exists>t. ?QQ m t)" in spec)
apply (erule impE, assumption)
apply (erule exE)
apply (rule_tac x = t in exI)
(* do some tidying up *)
apply (erule_tac [!] V= "difg = (%m t. diff m t - (setsum (%p. diff (m + p) 0 / real (fact p) * t ^ p) {0..<n-m} + B * (t ^ (n - m) / real (fact (n - m)))))"
       in thin_rl)
apply (erule_tac [!] V="g = (%t. f t - (setsum (%m. diff m 0 / real (fact m) * t ^ m) {0..<n} + B * (t ^ n / real (fact n))))"
       in thin_rl)
apply (erule_tac [!] V="f h = setsum (%m. diff m 0 / real (fact m) * h ^ m) {0..<n} + B * (h ^ n / real (fact n))"
       in thin_rl)
(* back to business *)
apply (simp (no_asm_simp))
apply (rule DERIV_unique)
prefer 2 apply blast
apply force
apply (rule allI, induct_tac "ma")
apply (rule impI, rule Rolle, assumption, simp, simp)
apply (metis DERIV_isCont zero_less_Suc)
apply (metis One_nat_def differentiableI dlo_simps(7))
apply safe
apply force
apply (frule Maclaurin_lemma3, assumption+, safe)
apply (rule_tac x = ta in exI, force)
done

lemma Maclaurin_objl:
  "0 < h & n\<noteq>0 & diff 0 = f &
  (\<forall>m t. m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t)
   --> (\<exists>t. 0 < t & t < h &
            f h = (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
                  diff n t / real (fact n) * h ^ n)"
by (blast intro: Maclaurin)


lemma Maclaurin2:
   "[| 0 < h; diff 0 = f;
       \<forall>m t.
          m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. 0 < t &
              t \<le> h &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n"
apply (case_tac "n", auto)
apply (drule Maclaurin, auto)
done

lemma Maclaurin2_objl:
     "0 < h & diff 0 = f &
       (\<forall>m t.
          m < n & 0 \<le> t & t \<le> h --> DERIV (diff m) t :> diff (Suc m) t)
    --> (\<exists>t. 0 < t &
              t \<le> h &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n)"
by (blast intro: Maclaurin2)

lemma Maclaurin_minus:
   "[| h < 0; n \<noteq> 0; diff 0 = f;
       \<forall>m t. m < n & h \<le> t & t \<le> 0 --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. h < t &
              t < 0 &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n"
apply (cut_tac f = "%x. f (-x)"
        and diff = "%n x. (-1 ^ n) * diff n (-x)"
        and h = "-h" and n = n in Maclaurin_objl)
apply (simp)
apply safe
apply (subst minus_mult_right)
apply (rule DERIV_cmult)
apply (rule lemma_DERIV_subst)
apply (rule DERIV_chain2 [where g=uminus])
apply (rule_tac [2] DERIV_minus, rule_tac [2] DERIV_ident)
prefer 2 apply force
apply force
apply (rule_tac x = "-t" in exI, auto)
apply (subgoal_tac "(\<Sum>m = 0..<n. -1 ^ m * diff m 0 * (-h)^m / real(fact m)) =
                    (\<Sum>m = 0..<n. diff m 0 * h ^ m / real(fact m))")
apply (rule_tac [2] setsum_cong[OF refl])
apply (auto simp add: divide_inverse power_mult_distrib [symmetric])
done

lemma Maclaurin_minus_objl:
     "(h < 0 & n \<noteq> 0 & diff 0 = f &
       (\<forall>m t.
          m < n & h \<le> t & t \<le> 0 --> DERIV (diff m) t :> diff (Suc m) t))
    --> (\<exists>t. h < t &
              t < 0 &
              f h =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * h ^ m) +
              diff n t / real (fact n) * h ^ n)"
by (blast intro: Maclaurin_minus)


subsection{*More Convenient "Bidirectional" Version.*}

(* not good for PVS sin_approx, cos_approx *)

lemma Maclaurin_bi_le_lemma [rule_format]:
  "n\<noteq>0 \<longrightarrow>
   diff 0 0 =
   (\<Sum>m = 0..<n. diff m 0 * 0 ^ m / real (fact m)) +
   diff n 0 * 0 ^ n / real (fact n)"
by (induct "n", auto)

lemma Maclaurin_bi_le:
   "[| diff 0 = f;
       \<forall>m t. m < n & abs t \<le> abs x --> DERIV (diff m) t :> diff (Suc m) t |]
    ==> \<exists>t. abs t \<le> abs x &
              f x =
              (\<Sum>m=0..<n. diff m 0 / real (fact m) * x ^ m) +
              diff n t / real (fact n) * x ^ n"
apply (case_tac "n = 0", force)
apply (case_tac "x = 0")
 apply (rule_tac x = 0 in exI)
 apply (force simp add: Maclaurin_bi_le_lemma)
apply (cut_tac x = x and y = 0 in linorder_less_linear, auto)
 txt{*Case 1, where @{term "x < 0"}*}
 apply (cut_tac f = "diff 0" and diff = diff and h = x and n = n in Maclaurin_minus_objl, safe)
  apply (simp add: abs_if)
 apply (rule_tac x = t in exI)
 apply (simp add: abs_if)
txt{*Case 2, where @{term "0 < x"}*}
apply (cut_tac f = "diff 0" and diff = diff and h = x and n = n in Maclaurin_objl, safe)
 apply (simp add: abs_if)
apply (rule_tac x = t in exI)
apply (simp add: abs_if)
done

lemma Maclaurin_all_lt:
     "[| diff 0 = f;
         \<forall>m x. DERIV (diff m) x :> diff(Suc m) x;
        x ~= 0; n \<noteq> 0
      |] ==> \<exists>t. 0 < abs t & abs t < abs x &
               f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                     (diff n t / real (fact n)) * x ^ n"
apply (rule_tac x = x and y = 0 in linorder_cases)
prefer 2 apply blast
apply (drule_tac [2] diff=diff in Maclaurin)
apply (drule_tac diff=diff in Maclaurin_minus, simp_all, safe)
apply (rule_tac [!] x = t in exI, auto)
done

lemma Maclaurin_all_lt_objl:
     "diff 0 = f &
      (\<forall>m x. DERIV (diff m) x :> diff(Suc m) x) &
      x ~= 0 & n \<noteq> 0
      --> (\<exists>t. 0 < abs t & abs t < abs x &
               f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                     (diff n t / real (fact n)) * x ^ n)"
by (blast intro: Maclaurin_all_lt)

lemma Maclaurin_zero [rule_format]:
     "x = (0::real)
      ==> n \<noteq> 0 -->
          (\<Sum>m=0..<n. (diff m (0::real) / real (fact m)) * x ^ m) =
          diff 0 0"
by (induct n, auto)

lemma Maclaurin_all_le: "[| diff 0 = f;
        \<forall>m x. DERIV (diff m) x :> diff (Suc m) x
      |] ==> \<exists>t. abs t \<le> abs x &
              f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                    (diff n t / real (fact n)) * x ^ n"
apply(cases "n=0")
apply (force)
apply (case_tac "x = 0")
apply (frule_tac diff = diff and n = n in Maclaurin_zero, assumption)
apply (drule not0_implies_Suc)
apply (rule_tac x = 0 in exI, force)
apply (frule_tac diff = diff and n = n in Maclaurin_all_lt, auto)
apply (rule_tac x = t in exI, auto)
done

lemma Maclaurin_all_le_objl: "diff 0 = f &
      (\<forall>m x. DERIV (diff m) x :> diff (Suc m) x)
      --> (\<exists>t. abs t \<le> abs x &
              f x = (\<Sum>m=0..<n. (diff m 0 / real (fact m)) * x ^ m) +
                    (diff n t / real (fact n)) * x ^ n)"
by (blast intro: Maclaurin_all_le)


subsection{*Version for Exponential Function*}

lemma Maclaurin_exp_lt: "[| x ~= 0; n \<noteq> 0 |]
      ==> (\<exists>t. 0 < abs t &
                abs t < abs x &
                exp x = (\<Sum>m=0..<n. (x ^ m) / real (fact m)) +
                        (exp t / real (fact n)) * x ^ n)"
by (cut_tac diff = "%n. exp" and f = exp and x = x and n = n in Maclaurin_all_lt_objl, auto)


lemma Maclaurin_exp_le:
     "\<exists>t. abs t \<le> abs x &
            exp x = (\<Sum>m=0..<n. (x ^ m) / real (fact m)) +
                       (exp t / real (fact n)) * x ^ n"
by (cut_tac diff = "%n. exp" and f = exp and x = x and n = n in Maclaurin_all_le_objl, auto)


subsection{*Version for Sine Function*}

lemma MVT2:
     "[| a < b; \<forall>x. a \<le> x & x \<le> b --> DERIV f x :> f'(x) |]
      ==> \<exists>z::real. a < z & z < b & (f b - f a = (b - a) * f'(z))"
apply (drule MVT)
apply (blast intro: DERIV_isCont)
apply (force dest: order_less_imp_le simp add: differentiable_def)
apply (blast dest: DERIV_unique order_less_imp_le)
done

lemma mod_exhaust_less_4:
  "m mod 4 = 0 | m mod 4 = 1 | m mod 4 = 2 | m mod 4 = (3::nat)"
by auto

lemma Suc_Suc_mult_two_diff_two [rule_format, simp]:
  "n\<noteq>0 --> Suc (Suc (2 * n - 2)) = 2*n"
by (induct "n", auto)

lemma lemma_Suc_Suc_4n_diff_2 [rule_format, simp]:
  "n\<noteq>0 --> Suc (Suc (4*n - 2)) = 4*n"
by (induct "n", auto)

lemma Suc_mult_two_diff_one [rule_format, simp]:
  "n\<noteq>0 --> Suc (2 * n - 1) = 2*n"
by (induct "n", auto)


text{*It is unclear why so many variant results are needed.*}

lemma Maclaurin_sin_expansion2:
     "\<exists>t. abs t \<le> abs x &
       sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and x = x
        and diff = "%n x. sin (x + 1/2*real n * pi)" in Maclaurin_all_lt_objl)
apply safe
apply (simp (no_asm))
apply (simp (no_asm))
apply (case_tac "n", clarify, simp, simp add: lemma_STAR_sin)
apply (rule ccontr, simp)
apply (drule_tac x = x in spec, simp)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_zero_iff odd_Suc_mult_two_ex)
done

lemma Maclaurin_sin_expansion:
     "\<exists>t. sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (insert Maclaurin_sin_expansion2 [of x n]) 
apply (blast intro: elim:); 
done



lemma Maclaurin_sin_expansion3:
     "[| n \<noteq> 0; 0 < x |] ==>
       \<exists>t. 0 < t & t < x &
       sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real(n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and h = x and diff = "%n x. sin (x + 1/2*real (n) *pi)" in Maclaurin_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_zero_iff odd_Suc_mult_two_ex)
done

lemma Maclaurin_sin_expansion4:
     "0 < x ==>
       \<exists>t. 0 < t & t \<le> x &
       sin x =
       (\<Sum>m=0..<n. (if even m then 0
                       else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
                       x ^ m)
      + ((sin(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = sin and n = n and h = x and diff = "%n x. sin (x + 1/2*real (n) *pi)" in Maclaurin2_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: sin_zero_iff odd_Suc_mult_two_ex)
done


subsection{*Maclaurin Expansion for Cosine Function*}

lemma sumr_cos_zero_one [simp]:
 "(\<Sum>m=0..<(Suc n).
     (if even m then -1 ^ (m div 2)/(real  (fact m)) else 0) * 0 ^ m) = 1"
by (induct "n", auto)

lemma Maclaurin_cos_expansion:
     "\<exists>t. abs t \<le> abs x &
       cos x =
       (\<Sum>m=0..<n. (if even m
                       then -1 ^ (m div 2)/(real (fact m))
                       else 0) *
                       x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and x = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_all_lt_objl)
apply safe
apply (simp (no_asm))
apply (simp (no_asm))
apply (case_tac "n", simp)
apply (simp del: setsum_op_ivl_Suc)
apply (rule ccontr, simp)
apply (drule_tac x = x in spec, simp)
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_zero_iff even_mult_two_ex)
done

lemma Maclaurin_cos_expansion2:
     "[| 0 < x; n \<noteq> 0 |] ==>
       \<exists>t. 0 < t & t < x &
       cos x =
       (\<Sum>m=0..<n. (if even m
                       then -1 ^ (m div 2)/(real (fact m))
                       else 0) *
                       x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and h = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_zero_iff even_mult_two_ex)
done

lemma Maclaurin_minus_cos_expansion:
     "[| x < 0; n \<noteq> 0 |] ==>
       \<exists>t. x < t & t < 0 &
       cos x =
       (\<Sum>m=0..<n. (if even m
                       then -1 ^ (m div 2)/(real (fact m))
                       else 0) *
                       x ^ m)
      + ((cos(t + 1/2 * real (n) *pi) / real (fact n)) * x ^ n)"
apply (cut_tac f = cos and n = n and h = x and diff = "%n x. cos (x + 1/2*real (n) *pi)" in Maclaurin_minus_objl)
apply safe
apply simp
apply (simp (no_asm))
apply (erule ssubst)
apply (rule_tac x = t in exI, simp)
apply (rule setsum_cong[OF refl])
apply (auto simp add: cos_zero_iff even_mult_two_ex)
done

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 +/- x). Where is it??                                    *)
(* ------------------------------------------------------------------------- *)

lemma sin_bound_lemma:
    "[|x = y; abs u \<le> (v::real) |] ==> \<bar>(x + u) - y\<bar> \<le> v"
by auto

lemma Maclaurin_sin_bound:
  "abs(sin x - (\<Sum>m=0..<n. (if even m then 0 else (-1 ^ ((m - Suc 0) div 2)) / real (fact m)) *
  x ^ m))  \<le> inverse(real (fact n)) * \<bar>x\<bar> ^ n"
proof -
  have "!! x (y::real). x \<le> 1 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x * y \<le> 1 * y"
    by (rule_tac mult_right_mono,simp_all)
  note est = this[simplified]
  let ?diff = "\<lambda>(n::nat) x. if n mod 4 = 0 then sin(x) else if n mod 4 = 1 then cos(x) else if n mod 4 = 2 then -sin(x) else -cos(x)"
  have diff_0: "?diff 0 = sin" by simp
  have DERIV_diff: "\<forall>m x. DERIV (?diff m) x :> ?diff (Suc m) x"
    apply (clarify)
    apply (subst (1 2 3) mod_Suc_eq_Suc_mod)
    apply (cut_tac m=m in mod_exhaust_less_4)
    apply (safe, simp_all)
    apply (rule DERIV_minus, simp)
    apply (rule lemma_DERIV_subst, rule DERIV_minus, rule DERIV_cos, simp)
    done
  from Maclaurin_all_le [OF diff_0 DERIV_diff]
  obtain t where t1: "\<bar>t\<bar> \<le> \<bar>x\<bar>" and
    t2: "sin x = (\<Sum>m = 0..<n. ?diff m 0 / real (fact m) * x ^ m) +
      ?diff n t / real (fact n) * x ^ n" by fast
  have diff_m_0:
    "\<And>m. ?diff m 0 = (if even m then 0
         else -1 ^ ((m - Suc 0) div 2))"
    apply (subst even_even_mod_4_iff)
    apply (cut_tac m=m in mod_exhaust_less_4)
    apply (elim disjE, simp_all)
    apply (safe dest!: mod_eqD, simp_all)
    done
  show ?thesis
    apply (subst t2)
    apply (rule sin_bound_lemma)
    apply (rule setsum_cong[OF refl])
    apply (subst diff_m_0, simp)
    apply (auto intro: mult_right_mono [where b=1, simplified] mult_right_mono
                   simp add: est mult_nonneg_nonneg mult_ac divide_inverse
                          power_abs [symmetric] abs_mult)
    done
qed

end
