(*  Title       : HLim.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{* Limits and Continuity (Nonstandard) *}

theory HLim
imports Star Lim
begin

text{*Nonstandard Definitions*}

definition
  NSLIM :: "['a::real_normed_vector => 'b::real_normed_vector, 'a, 'b] => bool"
            ("((_)/ -- (_)/ --NS> (_))" [60, 0, 60] 60) where
  [code del]: "f -- a --NS> L =
    (\<forall>x. (x \<noteq> star_of a & x @= star_of a --> ( *f* f) x @= star_of L))"

definition
  isNSCont :: "['a::real_normed_vector => 'b::real_normed_vector, 'a] => bool" where
    --{*NS definition dispenses with limit notions*}
  [code del]: "isNSCont f a = (\<forall>y. y @= star_of a -->
         ( *f* f) y @= star_of (f a))"

definition
  isNSUCont :: "['a::real_normed_vector => 'b::real_normed_vector] => bool" where
  [code del]: "isNSUCont f = (\<forall>x y. x @= y --> ( *f* f) x @= ( *f* f) y)"


subsection {* Limits of Functions *}

lemma NSLIM_I:
  "(\<And>x. \<lbrakk>x \<noteq> star_of a; x \<approx> star_of a\<rbrakk> \<Longrightarrow> starfun f x \<approx> star_of L)
   \<Longrightarrow> f -- a --NS> L"
by (simp add: NSLIM_def)

lemma NSLIM_D:
  "\<lbrakk>f -- a --NS> L; x \<noteq> star_of a; x \<approx> star_of a\<rbrakk>
   \<Longrightarrow> starfun f x \<approx> star_of L"
by (simp add: NSLIM_def)

text{*Proving properties of limits using nonstandard definition.
      The properties hold for standard limits as well!*}

lemma NSLIM_mult:
  fixes l m :: "'a::real_normed_algebra"
  shows "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) * g(x)) -- x --NS> (l * m)"
by (auto simp add: NSLIM_def intro!: approx_mult_HFinite)

lemma starfun_scaleR [simp]:
  "starfun (\<lambda>x. f x *\<^sub>R g x) = (\<lambda>x. scaleHR (starfun f x) (starfun g x))"
by transfer (rule refl)

lemma NSLIM_scaleR:
  "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) *\<^sub>R g(x)) -- x --NS> (l *\<^sub>R m)"
by (auto simp add: NSLIM_def intro!: approx_scaleR_HFinite)

lemma NSLIM_add:
     "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) + g(x)) -- x --NS> (l + m)"
by (auto simp add: NSLIM_def intro!: approx_add)

lemma NSLIM_const [simp]: "(%x. k) -- x --NS> k"
by (simp add: NSLIM_def)

lemma NSLIM_minus: "f -- a --NS> L ==> (%x. -f(x)) -- a --NS> -L"
by (simp add: NSLIM_def)

lemma NSLIM_diff:
  "\<lbrakk>f -- x --NS> l; g -- x --NS> m\<rbrakk> \<Longrightarrow> (\<lambda>x. f x - g x) -- x --NS> (l - m)"
by (simp only: diff_def NSLIM_add NSLIM_minus)

lemma NSLIM_add_minus: "[| f -- x --NS> l; g -- x --NS> m |] ==> (%x. f(x) + -g(x)) -- x --NS> (l + -m)"
by (simp only: NSLIM_add NSLIM_minus)

lemma NSLIM_inverse:
  fixes L :: "'a::real_normed_div_algebra"
  shows "[| f -- a --NS> L;  L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --NS> (inverse L)"
apply (simp add: NSLIM_def, clarify)
apply (drule spec)
apply (auto simp add: star_of_approx_inverse)
done

lemma NSLIM_zero:
  assumes f: "f -- a --NS> l" shows "(%x. f(x) - l) -- a --NS> 0"
proof -
  have "(\<lambda>x. f x - l) -- a --NS> l - l"
    by (rule NSLIM_diff [OF f NSLIM_const])
  thus ?thesis by simp
qed

lemma NSLIM_zero_cancel: "(%x. f(x) - l) -- x --NS> 0 ==> f -- x --NS> l"
apply (drule_tac g = "%x. l" and m = l in NSLIM_add)
apply (auto simp add: diff_minus add_assoc)
done

lemma NSLIM_const_not_eq:
  fixes a :: "'a::real_normed_algebra_1"
  shows "k \<noteq> L \<Longrightarrow> \<not> (\<lambda>x. k) -- a --NS> L"
apply (simp add: NSLIM_def)
apply (rule_tac x="star_of a + of_hypreal epsilon" in exI)
apply (simp add: hypreal_epsilon_not_zero approx_def)
done

lemma NSLIM_not_zero:
  fixes a :: "'a::real_normed_algebra_1"
  shows "k \<noteq> 0 \<Longrightarrow> \<not> (\<lambda>x. k) -- a --NS> 0"
by (rule NSLIM_const_not_eq)

lemma NSLIM_const_eq:
  fixes a :: "'a::real_normed_algebra_1"
  shows "(\<lambda>x. k) -- a --NS> L \<Longrightarrow> k = L"
apply (rule ccontr)
apply (blast dest: NSLIM_const_not_eq)
done

lemma NSLIM_unique:
  fixes a :: "'a::real_normed_algebra_1"
  shows "\<lbrakk>f -- a --NS> L; f -- a --NS> M\<rbrakk> \<Longrightarrow> L = M"
apply (drule (1) NSLIM_diff)
apply (auto dest!: NSLIM_const_eq)
done

lemma NSLIM_mult_zero:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "[| f -- x --NS> 0; g -- x --NS> 0 |] ==> (%x. f(x)*g(x)) -- x --NS> 0"
by (drule NSLIM_mult, auto)

lemma NSLIM_self: "(%x. x) -- a --NS> a"
by (simp add: NSLIM_def)

subsubsection {* Equivalence of @{term LIM} and @{term NSLIM} *}

lemma LIM_NSLIM:
  assumes f: "f -- a --> L" shows "f -- a --NS> L"
proof (rule NSLIM_I)
  fix x
  assume neq: "x \<noteq> star_of a"
  assume approx: "x \<approx> star_of a"
  have "starfun f x - star_of L \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r::real assume r: "0 < r"
    from LIM_D [OF f r]
    obtain s where s: "0 < s" and
      less_r: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < s\<rbrakk> \<Longrightarrow> norm (f x - L) < r"
      by fast
    from less_r have less_r':
       "\<And>x. \<lbrakk>x \<noteq> star_of a; hnorm (x - star_of a) < star_of s\<rbrakk>
        \<Longrightarrow> hnorm (starfun f x - star_of L) < star_of r"
      by transfer
    from approx have "x - star_of a \<in> Infinitesimal"
      by (unfold approx_def)
    hence "hnorm (x - star_of a) < star_of s"
      using s by (rule InfinitesimalD2)
    with neq show "hnorm (starfun f x - star_of L) < star_of r"
      by (rule less_r')
  qed
  thus "starfun f x \<approx> star_of L"
    by (unfold approx_def)
qed

lemma NSLIM_LIM:
  assumes f: "f -- a --NS> L" shows "f -- a --> L"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  have "\<exists>s>0. \<forall>x. x \<noteq> star_of a \<and> hnorm (x - star_of a) < s
        \<longrightarrow> hnorm (starfun f x - star_of L) < star_of r"
  proof (rule exI, safe)
    show "0 < epsilon" by (rule hypreal_epsilon_gt_zero)
  next
    fix x assume neq: "x \<noteq> star_of a"
    assume "hnorm (x - star_of a) < epsilon"
    with Infinitesimal_epsilon
    have "x - star_of a \<in> Infinitesimal"
      by (rule hnorm_less_Infinitesimal)
    hence "x \<approx> star_of a"
      by (unfold approx_def)
    with f neq have "starfun f x \<approx> star_of L"
      by (rule NSLIM_D)
    hence "starfun f x - star_of L \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun f x - star_of L) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r"
    by transfer
qed

theorem LIM_NSLIM_iff: "(f -- x --> L) = (f -- x --NS> L)"
by (blast intro: LIM_NSLIM NSLIM_LIM)


subsection {* Continuity *}

lemma isNSContD:
  "\<lbrakk>isNSCont f a; y \<approx> star_of a\<rbrakk> \<Longrightarrow> ( *f* f) y \<approx> star_of (f a)"
by (simp add: isNSCont_def)

lemma isNSCont_NSLIM: "isNSCont f a ==> f -- a --NS> (f a) "
by (simp add: isNSCont_def NSLIM_def)

lemma NSLIM_isNSCont: "f -- a --NS> (f a) ==> isNSCont f a"
apply (simp add: isNSCont_def NSLIM_def, auto)
apply (case_tac "y = star_of a", auto)
done

text{*NS continuity can be defined using NS Limit in
    similar fashion to standard def of continuity*}
lemma isNSCont_NSLIM_iff: "(isNSCont f a) = (f -- a --NS> (f a))"
by (blast intro: isNSCont_NSLIM NSLIM_isNSCont)

text{*Hence, NS continuity can be given
  in terms of standard limit*}
lemma isNSCont_LIM_iff: "(isNSCont f a) = (f -- a --> (f a))"
by (simp add: LIM_NSLIM_iff isNSCont_NSLIM_iff)

text{*Moreover, it's trivial now that NS continuity
  is equivalent to standard continuity*}
lemma isNSCont_isCont_iff: "(isNSCont f a) = (isCont f a)"
apply (simp add: isCont_def)
apply (rule isNSCont_LIM_iff)
done

text{*Standard continuity ==> NS continuity*}
lemma isCont_isNSCont: "isCont f a ==> isNSCont f a"
by (erule isNSCont_isCont_iff [THEN iffD2])

text{*NS continuity ==> Standard continuity*}
lemma isNSCont_isCont: "isNSCont f a ==> isCont f a"
by (erule isNSCont_isCont_iff [THEN iffD1])

text{*Alternative definition of continuity*}

(* Prove equivalence between NS limits - *)
(* seems easier than using standard def  *)
lemma NSLIM_h_iff: "(f -- a --NS> L) = ((%h. f(a + h)) -- 0 --NS> L)"
apply (simp add: NSLIM_def, auto)
apply (drule_tac x = "star_of a + x" in spec)
apply (drule_tac [2] x = "- star_of a + x" in spec, safe, simp)
apply (erule mem_infmal_iff [THEN iffD2, THEN Infinitesimal_add_approx_self [THEN approx_sym]])
apply (erule_tac [3] approx_minus_iff2 [THEN iffD1])
 prefer 2 apply (simp add: add_commute diff_def [symmetric])
apply (rule_tac x = x in star_cases)
apply (rule_tac [2] x = x in star_cases)
apply (auto simp add: starfun star_of_def star_n_minus star_n_add add_assoc approx_refl star_n_zero_num)
done

lemma NSLIM_isCont_iff: "(f -- a --NS> f a) = ((%h. f(a + h)) -- 0 --NS> f a)"
by (rule NSLIM_h_iff)

lemma isNSCont_minus: "isNSCont f a ==> isNSCont (%x. - f x) a"
by (simp add: isNSCont_def)

lemma isNSCont_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  shows "[| isNSCont f x; f x \<noteq> 0 |] ==> isNSCont (%x. inverse (f x)) x"
by (auto intro: isCont_inverse simp add: isNSCont_isCont_iff)

lemma isNSCont_const [simp]: "isNSCont (%x. k) a"
by (simp add: isNSCont_def)

lemma isNSCont_abs [simp]: "isNSCont abs (a::real)"
apply (simp add: isNSCont_def)
apply (auto intro: approx_hrabs simp add: starfun_rabs_hrabs)
done


subsection {* Uniform Continuity *}

lemma isNSUContD: "[| isNSUCont f; x \<approx> y|] ==> ( *f* f) x \<approx> ( *f* f) y"
by (simp add: isNSUCont_def)

lemma isUCont_isNSUCont:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "isUCont f" shows "isNSUCont f"
proof (unfold isNSUCont_def, safe)
  fix x y :: "'a star"
  assume approx: "x \<approx> y"
  have "starfun f x - starfun f y \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r::real assume r: "0 < r"
    with f obtain s where s: "0 < s" and
      less_r: "\<And>x y. norm (x - y) < s \<Longrightarrow> norm (f x - f y) < r"
      by (auto simp add: isUCont_def dist_norm)
    from less_r have less_r':
       "\<And>x y. hnorm (x - y) < star_of s
        \<Longrightarrow> hnorm (starfun f x - starfun f y) < star_of r"
      by transfer
    from approx have "x - y \<in> Infinitesimal"
      by (unfold approx_def)
    hence "hnorm (x - y) < star_of s"
      using s by (rule InfinitesimalD2)
    thus "hnorm (starfun f x - starfun f y) < star_of r"
      by (rule less_r')
  qed
  thus "starfun f x \<approx> starfun f y"
    by (unfold approx_def)
qed

lemma isNSUCont_isUCont:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "isNSUCont f" shows "isUCont f"
proof (unfold isUCont_def dist_norm, safe)
  fix r::real assume r: "0 < r"
  have "\<exists>s>0. \<forall>x y. hnorm (x - y) < s
        \<longrightarrow> hnorm (starfun f x - starfun f y) < star_of r"
  proof (rule exI, safe)
    show "0 < epsilon" by (rule hypreal_epsilon_gt_zero)
  next
    fix x y :: "'a star"
    assume "hnorm (x - y) < epsilon"
    with Infinitesimal_epsilon
    have "x - y \<in> Infinitesimal"
      by (rule hnorm_less_Infinitesimal)
    hence "x \<approx> y"
      by (unfold approx_def)
    with f have "starfun f x \<approx> starfun f y"
      by (simp add: isNSUCont_def)
    hence "starfun f x - starfun f y \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun f x - starfun f y) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r"
    by transfer
qed

end
