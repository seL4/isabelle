(*  Title       : FrechetDeriv.thy
    Author      : Brian Huffman
*)

header {* Frechet Derivative *}

theory FrechetDeriv
imports Complex_Main
begin

definition
  fderiv ::
  "['a::real_normed_vector \<Rightarrow> 'b::real_normed_vector, 'a, 'a \<Rightarrow> 'b] \<Rightarrow> bool"
    -- {* Frechet derivative: D is derivative of function f at x *}
          ("(FDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "FDERIV f x :> D = (bounded_linear D \<and>
    (\<lambda>h. norm (f (x + h) - f x - D h) / norm h) -- 0 --> 0)"

lemma FDERIV_I:
  "\<lbrakk>bounded_linear D; (\<lambda>h. norm (f (x + h) - f x - D h) / norm h) -- 0 --> 0\<rbrakk>
   \<Longrightarrow> FDERIV f x :> D"
by (simp add: fderiv_def)

lemma FDERIV_D:
  "FDERIV f x :> D \<Longrightarrow> (\<lambda>h. norm (f (x + h) - f x - D h) / norm h) -- 0 --> 0"
by (simp add: fderiv_def)

lemma FDERIV_bounded_linear: "FDERIV f x :> D \<Longrightarrow> bounded_linear D"
by (simp add: fderiv_def)

lemma bounded_linear_zero: "bounded_linear (\<lambda>x. 0)"
  by (rule bounded_linear_intro [where K=0], simp_all)

lemma FDERIV_const: "FDERIV (\<lambda>x. k) x :> (\<lambda>h. 0)"
  by (simp add: fderiv_def bounded_linear_zero tendsto_const)

lemma bounded_linear_ident: "bounded_linear (\<lambda>x. x)"
  by (rule bounded_linear_intro [where K=1], simp_all)

lemma FDERIV_ident: "FDERIV (\<lambda>x. x) x :> (\<lambda>h. h)"
  by (simp add: fderiv_def bounded_linear_ident tendsto_const)

subsection {* Addition *}

lemma bounded_linear_add:
  assumes "bounded_linear f"
  assumes "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis apply (unfold_locales)
    apply (simp only: f.add g.add add_ac)
    apply (simp only: f.scaleR g.scaleR scaleR_right_distrib)
    apply (rule f.pos_bounded [THEN exE], rename_tac Kf)
    apply (rule g.pos_bounded [THEN exE], rename_tac Kg)
    apply (rule_tac x="Kf + Kg" in exI, safe)
    apply (subst distrib_left)
    apply (rule order_trans [OF norm_triangle_ineq])
    apply (rule add_mono, erule spec, erule spec)
    done
qed

lemma norm_ratio_ineq:
  fixes x y :: "'a::real_normed_vector"
  fixes h :: "'b::real_normed_vector"
  shows "norm (x + y) / norm h \<le> norm x / norm h + norm y / norm h"
apply (rule ord_le_eq_trans)
apply (rule divide_right_mono)
apply (rule norm_triangle_ineq)
apply (rule norm_ge_zero)
apply (rule add_divide_distrib)
done

lemma FDERIV_add:
  assumes f: "FDERIV f x :> F"
  assumes g: "FDERIV g x :> G"
  shows "FDERIV (\<lambda>x. f x + g x) x :> (\<lambda>h. F h + G h)"
proof (rule FDERIV_I)
  show "bounded_linear (\<lambda>h. F h + G h)"
    apply (rule bounded_linear_add)
    apply (rule FDERIV_bounded_linear [OF f])
    apply (rule FDERIV_bounded_linear [OF g])
    done
next
  have f': "(\<lambda>h. norm (f (x + h) - f x - F h) / norm h) -- 0 --> 0"
    using f by (rule FDERIV_D)
  have g': "(\<lambda>h. norm (g (x + h) - g x - G h) / norm h) -- 0 --> 0"
    using g by (rule FDERIV_D)
  from f' g'
  have "(\<lambda>h. norm (f (x + h) - f x - F h) / norm h
           + norm (g (x + h) - g x - G h) / norm h) -- 0 --> 0"
    by (rule tendsto_add_zero)
  thus "(\<lambda>h. norm (f (x + h) + g (x + h) - (f x + g x) - (F h + G h))
           / norm h) -- 0 --> 0"
    apply (rule real_LIM_sandwich_zero)
     apply (simp add: divide_nonneg_pos)
    apply (simp only: add_diff_add)
    apply (rule norm_ratio_ineq)
    done
qed

subsection {* Subtraction *}

lemma bounded_linear_minus:
  assumes "bounded_linear f"
  shows "bounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis apply (unfold_locales)
    apply (simp add: f.add)
    apply (simp add: f.scaleR)
    apply (simp add: f.bounded)
    done
qed

lemma FDERIV_minus:
  "FDERIV f x :> F \<Longrightarrow> FDERIV (\<lambda>x. - f x) x :> (\<lambda>h. - F h)"
apply (rule FDERIV_I)
apply (rule bounded_linear_minus)
apply (erule FDERIV_bounded_linear)
apply (simp only: fderiv_def minus_diff_minus norm_minus_cancel)
done

lemma FDERIV_diff:
  "\<lbrakk>FDERIV f x :> F; FDERIV g x :> G\<rbrakk>
   \<Longrightarrow> FDERIV (\<lambda>x. f x - g x) x :> (\<lambda>h. F h - G h)"
by (simp only: diff_minus FDERIV_add FDERIV_minus)

subsection {* Uniqueness *}

lemma FDERIV_zero_unique:
  assumes "FDERIV (\<lambda>x. 0) x :> F" shows "F = (\<lambda>h. 0)"
proof -
  interpret F: bounded_linear F
    using assms by (rule FDERIV_bounded_linear)
  let ?r = "\<lambda>h. norm (F h) / norm h"
  have *: "?r -- 0 --> 0"
    using assms unfolding fderiv_def by simp
  show "F = (\<lambda>h. 0)"
  proof
    fix h show "F h = 0"
    proof (rule ccontr)
      assume "F h \<noteq> 0"
      moreover from this have h: "h \<noteq> 0"
        by (clarsimp simp add: F.zero)
      ultimately have "0 < ?r h"
        by (simp add: divide_pos_pos)
      from LIM_D [OF * this] obtain s where s: "0 < s"
        and r: "\<And>x. x \<noteq> 0 \<Longrightarrow> norm x < s \<Longrightarrow> ?r x < ?r h" by auto
      from dense [OF s] obtain t where t: "0 < t \<and> t < s" ..
      let ?x = "scaleR (t / norm h) h"
      have "?x \<noteq> 0" and "norm ?x < s" using t h by simp_all
      hence "?r ?x < ?r h" by (rule r)
      thus "False" using t h by (simp add: F.scaleR)
    qed
  qed
qed

lemma FDERIV_unique:
  assumes "FDERIV f x :> F" and "FDERIV f x :> F'" shows "F = F'"
proof -
  have "FDERIV (\<lambda>x. 0) x :> (\<lambda>h. F h - F' h)"
    using FDERIV_diff [OF assms] by simp
  hence "(\<lambda>h. F h - F' h) = (\<lambda>h. 0)"
    by (rule FDERIV_zero_unique)
  thus "F = F'"
    unfolding fun_eq_iff right_minus_eq .
qed

subsection {* Continuity *}

lemma FDERIV_isCont:
  assumes f: "FDERIV f x :> F"
  shows "isCont f x"
proof -
  from f interpret F: bounded_linear "F" by (rule FDERIV_bounded_linear)
  have "(\<lambda>h. norm (f (x + h) - f x - F h) / norm h) -- 0 --> 0"
    by (rule FDERIV_D [OF f])
  hence "(\<lambda>h. norm (f (x + h) - f x - F h) / norm h * norm h) -- 0 --> 0"
    by (intro tendsto_mult_zero tendsto_norm_zero tendsto_ident_at)
  hence "(\<lambda>h. norm (f (x + h) - f x - F h)) -- 0 --> 0"
    by (simp cong: LIM_cong)
  hence "(\<lambda>h. f (x + h) - f x - F h) -- 0 --> 0"
    by (rule tendsto_norm_zero_cancel)
  hence "(\<lambda>h. f (x + h) - f x - F h + F h) -- 0 --> 0"
    by (intro tendsto_add_zero F.tendsto_zero tendsto_ident_at)
  hence "(\<lambda>h. f (x + h) - f x) -- 0 --> 0"
    by simp
  thus "isCont f x"
    unfolding isCont_iff by (rule LIM_zero_cancel)
qed

subsection {* Composition *}

lemma real_divide_cancel_lemma:
  fixes a b c :: real
  shows "(b = 0 \<Longrightarrow> a = 0) \<Longrightarrow> (a / b) * (b / c) = a / c"
by simp

lemma bounded_linear_compose:
  assumes "bounded_linear f"
  assumes "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis proof (unfold_locales)
    fix x y show "f (g (x + y)) = f (g x) + f (g y)"
      by (simp only: f.add g.add)
  next
    fix r x show "f (g (scaleR r x)) = scaleR r (f (g x))"
      by (simp only: f.scaleR g.scaleR)
  next
    from f.pos_bounded
    obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf" by fast
    from g.pos_bounded
    obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg" by fast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult_assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma FDERIV_compose:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  fixes g :: "'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes f: "FDERIV f x :> F"
  assumes g: "FDERIV g (f x) :> G"
  shows "FDERIV (\<lambda>x. g (f x)) x :> (\<lambda>h. G (F h))"
proof (rule FDERIV_I)
  from FDERIV_bounded_linear [OF g] FDERIV_bounded_linear [OF f]
  show "bounded_linear (\<lambda>h. G (F h))"
    by (rule bounded_linear_compose)
next
  let ?Rf = "\<lambda>h. f (x + h) - f x - F h"
  let ?Rg = "\<lambda>k. g (f x + k) - g (f x) - G k"
  let ?k = "\<lambda>h. f (x + h) - f x"
  let ?Nf = "\<lambda>h. norm (?Rf h) / norm h"
  let ?Ng = "\<lambda>h. norm (?Rg (?k h)) / norm (?k h)"
  from f interpret F: bounded_linear "F" by (rule FDERIV_bounded_linear)
  from g interpret G: bounded_linear "G" by (rule FDERIV_bounded_linear)
  from F.bounded obtain kF where kF: "\<And>x. norm (F x) \<le> norm x * kF" by fast
  from G.bounded obtain kG where kG: "\<And>x. norm (G x) \<le> norm x * kG" by fast

  let ?fun2 = "\<lambda>h. ?Nf h * kG + ?Ng h * (?Nf h + kF)"

  show "(\<lambda>h. norm (g (f (x + h)) - g (f x) - G (F h)) / norm h) -- 0 --> 0"
  proof (rule real_LIM_sandwich_zero)
    have Nf: "?Nf -- 0 --> 0"
      using FDERIV_D [OF f] .

    have Ng1: "isCont (\<lambda>k. norm (?Rg k) / norm k) 0"
      by (simp add: isCont_def FDERIV_D [OF g])
    have Ng2: "?k -- 0 --> 0"
      apply (rule LIM_zero)
      apply (fold isCont_iff)
      apply (rule FDERIV_isCont [OF f])
      done
    have Ng: "?Ng -- 0 --> 0"
      using isCont_tendsto_compose [OF Ng1 Ng2] by simp

    have "(\<lambda>h. ?Nf h * kG + ?Ng h * (?Nf h + kF))
           -- 0 --> 0 * kG + 0 * (0 + kF)"
      by (intro tendsto_intros Nf Ng)
    thus "(\<lambda>h. ?Nf h * kG + ?Ng h * (?Nf h + kF)) -- 0 --> 0"
      by simp
  next
    fix h::'a assume h: "h \<noteq> 0"
    thus "0 \<le> norm (g (f (x + h)) - g (f x) - G (F h)) / norm h"
      by (simp add: divide_nonneg_pos)
  next
    fix h::'a assume h: "h \<noteq> 0"
    have "g (f (x + h)) - g (f x) - G (F h) = G (?Rf h) + ?Rg (?k h)"
      by (simp add: G.diff)
    hence "norm (g (f (x + h)) - g (f x) - G (F h)) / norm h
           = norm (G (?Rf h) + ?Rg (?k h)) / norm h"
      by (rule arg_cong)
    also have "\<dots> \<le> norm (G (?Rf h)) / norm h + norm (?Rg (?k h)) / norm h"
      by (rule norm_ratio_ineq)
    also have "\<dots> \<le> ?Nf h * kG + ?Ng h * (?Nf h + kF)"
    proof (rule add_mono)
      show "norm (G (?Rf h)) / norm h \<le> ?Nf h * kG"
        apply (rule ord_le_eq_trans)
        apply (rule divide_right_mono [OF kG norm_ge_zero])
        apply simp
        done
    next
      have "norm (?Rg (?k h)) / norm h = ?Ng h * (norm (?k h) / norm h)"
        apply (rule real_divide_cancel_lemma [symmetric])
        apply (simp add: G.zero)
        done
      also have "\<dots> \<le> ?Ng h * (?Nf h + kF)"
      proof (rule mult_left_mono)
        have "norm (?k h) / norm h = norm (?Rf h + F h) / norm h"
          by simp
        also have "\<dots> \<le> ?Nf h + norm (F h) / norm h"
          by (rule norm_ratio_ineq)
        also have "\<dots> \<le> ?Nf h + kF"
          apply (rule add_left_mono)
          apply (subst pos_divide_le_eq, simp add: h)
          apply (subst mult_commute)
          apply (rule kF)
          done
        finally show "norm (?k h) / norm h \<le> ?Nf h + kF" .
      next
        show "0 \<le> ?Ng h"
        apply (case_tac "f (x + h) - f x = 0", simp)
        apply (rule divide_nonneg_pos [OF norm_ge_zero])
        apply simp
        done
      qed
      finally show "norm (?Rg (?k h)) / norm h \<le> ?Ng h * (?Nf h + kF)" .
    qed
    finally show "norm (g (f (x + h)) - g (f x) - G (F h)) / norm h
        \<le> ?Nf h * kG + ?Ng h * (?Nf h + kF)" .
  qed
qed

subsection {* Product Rule *}

lemma (in bounded_bilinear) FDERIV_lemma:
  "a' ** b' - a ** b - (a ** B + A ** b)
   = a ** (b' - b - B) + (a' - a - A) ** b' + A ** (b' - b)"
by (simp add: diff_left diff_right)

lemma (in bounded_bilinear) FDERIV:
  fixes x :: "'d::real_normed_vector"
  assumes f: "FDERIV f x :> F"
  assumes g: "FDERIV g x :> G"
  shows "FDERIV (\<lambda>x. f x ** g x) x :> (\<lambda>h. f x ** G h + F h ** g x)"
proof (rule FDERIV_I)
  show "bounded_linear (\<lambda>h. f x ** G h + F h ** g x)"
    apply (rule bounded_linear_add)
    apply (rule bounded_linear_compose [OF bounded_linear_right])
    apply (rule FDERIV_bounded_linear [OF g])
    apply (rule bounded_linear_compose [OF bounded_linear_left])
    apply (rule FDERIV_bounded_linear [OF f])
    done
next
  from bounded_linear.bounded [OF FDERIV_bounded_linear [OF f]]
  obtain KF where norm_F: "\<And>x. norm (F x) \<le> norm x * KF" by fast

  from pos_bounded obtain K where K: "0 < K" and norm_prod:
    "\<And>a b. norm (a ** b) \<le> norm a * norm b * K" by fast

  let ?Rf = "\<lambda>h. f (x + h) - f x - F h"
  let ?Rg = "\<lambda>h. g (x + h) - g x - G h"

  let ?fun1 = "\<lambda>h.
        norm (f x ** ?Rg h + ?Rf h ** g (x + h) + F h ** (g (x + h) - g x)) /
        norm h"

  let ?fun2 = "\<lambda>h.
        norm (f x) * (norm (?Rg h) / norm h) * K +
        norm (?Rf h) / norm h * norm (g (x + h)) * K +
        KF * norm (g (x + h) - g x) * K"

  have "?fun1 -- 0 --> 0"
  proof (rule real_LIM_sandwich_zero)
    from f g isCont_iff [THEN iffD1, OF FDERIV_isCont [OF g]]
    have "?fun2 -- 0 -->
          norm (f x) * 0 * K + 0 * norm (g x) * K + KF * norm (0::'b) * K"
      by (intro tendsto_intros LIM_zero FDERIV_D)
    thus "?fun2 -- 0 --> 0"
      by simp
  next
    fix h::'d assume "h \<noteq> 0"
    thus "0 \<le> ?fun1 h"
      by (simp add: divide_nonneg_pos)
  next
    fix h::'d assume "h \<noteq> 0"
    have "?fun1 h \<le> (norm (f x) * norm (?Rg h) * K +
         norm (?Rf h) * norm (g (x + h)) * K +
         norm h * KF * norm (g (x + h) - g x) * K) / norm h"
      by (intro
        divide_right_mono mult_mono'
        order_trans [OF norm_triangle_ineq add_mono]
        order_trans [OF norm_prod mult_right_mono]
        mult_nonneg_nonneg order_refl norm_ge_zero norm_F
        K [THEN order_less_imp_le]
      )
    also have "\<dots> = ?fun2 h"
      by (simp add: add_divide_distrib)
    finally show "?fun1 h \<le> ?fun2 h" .
  qed
  thus "(\<lambda>h.
    norm (f (x + h) ** g (x + h) - f x ** g x - (f x ** G h + F h ** g x))
    / norm h) -- 0 --> 0"
    by (simp only: FDERIV_lemma)
qed

lemmas FDERIV_mult =
  bounded_bilinear.FDERIV [OF bounded_bilinear_mult]

lemmas FDERIV_scaleR =
  bounded_bilinear.FDERIV [OF bounded_bilinear_scaleR]


subsection {* Powers *}

lemma FDERIV_power_Suc:
  fixes x :: "'a::{real_normed_algebra,comm_ring_1}"
  shows "FDERIV (\<lambda>x. x ^ Suc n) x :> (\<lambda>h. (1 + of_nat n) * x ^ n * h)"
 apply (induct n)
  apply (simp add: FDERIV_ident)
 apply (drule FDERIV_mult [OF FDERIV_ident])
 apply (simp only: of_nat_Suc distrib_right mult_1_left)
 apply (simp only: power_Suc distrib_left add_ac mult_ac)
done

lemma FDERIV_power:
  fixes x :: "'a::{real_normed_algebra,comm_ring_1}"
  shows "FDERIV (\<lambda>x. x ^ n) x :> (\<lambda>h. of_nat n * x ^ (n - 1) * h)"
  apply (cases n)
   apply (simp add: FDERIV_const)
  apply (simp add: FDERIV_power_Suc del: power_Suc)
  done


subsection {* Inverse *}

lemmas bounded_linear_mult_const =
  bounded_linear_mult_left [THEN bounded_linear_compose]

lemmas bounded_linear_const_mult =
  bounded_linear_mult_right [THEN bounded_linear_compose]

lemma FDERIV_inverse:
  fixes x :: "'a::real_normed_div_algebra"
  assumes x: "x \<noteq> 0"
  shows "FDERIV inverse x :> (\<lambda>h. - (inverse x * h * inverse x))"
        (is "FDERIV ?inv _ :> _")
proof (rule FDERIV_I)
  show "bounded_linear (\<lambda>h. - (?inv x * h * ?inv x))"
    apply (rule bounded_linear_minus)
    apply (rule bounded_linear_mult_const)
    apply (rule bounded_linear_const_mult)
    apply (rule bounded_linear_ident)
    done
next
  show "(\<lambda>h. norm (?inv (x + h) - ?inv x - - (?inv x * h * ?inv x)) / norm h)
        -- 0 --> 0"
  proof (rule LIM_equal2)
    show "0 < norm x" using x by simp
  next
    fix h::'a
    assume 1: "h \<noteq> 0"
    assume "norm (h - 0) < norm x"
    hence "h \<noteq> -x" by clarsimp
    hence 2: "x + h \<noteq> 0"
      apply (rule contrapos_nn)
      apply (rule sym)
      apply (erule minus_unique)
      done
    show "norm (?inv (x + h) - ?inv x - - (?inv x * h * ?inv x)) / norm h
          = norm ((?inv (x + h) - ?inv x) * h * ?inv x) / norm h"
      apply (subst inverse_diff_inverse [OF 2 x])
      apply (subst minus_diff_minus)
      apply (subst norm_minus_cancel)
      apply (simp add: left_diff_distrib)
      done
  next
    show "(\<lambda>h. norm ((?inv (x + h) - ?inv x) * h * ?inv x) / norm h)
          -- 0 --> 0"
    proof (rule real_LIM_sandwich_zero)
      show "(\<lambda>h. norm (?inv (x + h) - ?inv x) * norm (?inv x))
            -- 0 --> 0"
        apply (rule tendsto_mult_left_zero)
        apply (rule tendsto_norm_zero)
        apply (rule LIM_zero)
        apply (rule LIM_offset_zero)
        apply (rule tendsto_inverse)
        apply (rule tendsto_ident_at)
        apply (rule x)
        done
    next
      fix h::'a assume h: "h \<noteq> 0"
      show "0 \<le> norm ((?inv (x + h) - ?inv x) * h * ?inv x) / norm h"
        apply (rule divide_nonneg_pos)
        apply (rule norm_ge_zero)
        apply (simp add: h)
        done
    next
      fix h::'a assume h: "h \<noteq> 0"
      have "norm ((?inv (x + h) - ?inv x) * h * ?inv x) / norm h
            \<le> norm (?inv (x + h) - ?inv x) * norm h * norm (?inv x) / norm h"
        apply (rule divide_right_mono [OF _ norm_ge_zero])
        apply (rule order_trans [OF norm_mult_ineq])
        apply (rule mult_right_mono [OF _ norm_ge_zero])
        apply (rule norm_mult_ineq)
        done
      also have "\<dots> = norm (?inv (x + h) - ?inv x) * norm (?inv x)"
        by simp
      finally show "norm ((?inv (x + h) - ?inv x) * h * ?inv x) / norm h
            \<le> norm (?inv (x + h) - ?inv x) * norm (?inv x)" .
    qed
  qed
qed

subsection {* Alternate definition *}

lemma field_fderiv_def:
  fixes x :: "'a::real_normed_field" shows
  "FDERIV f x :> (\<lambda>h. h * D) = (\<lambda>h. (f (x + h) - f x) / h) -- 0 --> D"
 apply (unfold fderiv_def)
 apply (simp add: bounded_linear_mult_left)
 apply (simp cong: LIM_cong add: nonzero_norm_divide [symmetric])
 apply (subst diff_divide_distrib)
 apply (subst times_divide_eq_left [symmetric])
 apply (simp cong: LIM_cong)
 apply (simp add: tendsto_norm_zero_iff LIM_zero_iff)
done

end
