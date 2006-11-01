(*  Title       : Lim.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    GMVT by Benjamin Porter, 2005
*)

header{*Limits, Continuity and Differentiation*}

theory Lim
imports SEQ
begin

text{*Standard and Nonstandard Definitions*}

definition
  LIM :: "['a::real_normed_vector => 'b::real_normed_vector, 'a, 'b] => bool"
        ("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60)
  "f -- a --> L =
     (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s
        --> norm (f x - L) < r)"

  NSLIM :: "['a::real_normed_vector => 'b::real_normed_vector, 'a, 'b] => bool"
            ("((_)/ -- (_)/ --NS> (_))" [60, 0, 60] 60)
  "f -- a --NS> L =
    (\<forall>x. (x \<noteq> star_of a & x @= star_of a --> ( *f* f) x @= star_of L))"

  isCont :: "['a::real_normed_vector => 'b::real_normed_vector, 'a] => bool"
  "isCont f a = (f -- a --> (f a))"

  isNSCont :: "['a::real_normed_vector => 'b::real_normed_vector, 'a] => bool"
    --{*NS definition dispenses with limit notions*}
  "isNSCont f a = (\<forall>y. y @= star_of a -->
         ( *f* f) y @= star_of (f a))"

  deriv :: "[real \<Rightarrow> 'a::real_normed_vector, real, 'a] \<Rightarrow> bool"
    --{*Differentiation: D is derivative of function f at x*}
          ("(DERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  "DERIV f x :> D = ((%h. (f(x + h) - f x) /# h) -- 0 --> D)"

  nsderiv :: "[real=>real,real,real] => bool"
          ("(NSDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  "NSDERIV f x :> D = (\<forall>h \<in> Infinitesimal - {0}.
      (( *f* f)(hypreal_of_real x + h)
       - hypreal_of_real (f x))/h @= hypreal_of_real D)"

  differentiable :: "[real=>real,real] => bool"   (infixl "differentiable" 60)
  "f differentiable x = (\<exists>D. DERIV f x :> D)"

  NSdifferentiable :: "[real=>real,real] => bool"
                       (infixl "NSdifferentiable" 60)
  "f NSdifferentiable x = (\<exists>D. NSDERIV f x :> D)"

  increment :: "[real=>real,real,hypreal] => hypreal"
  "increment f x h = (@inc. f NSdifferentiable x &
           inc = ( *f* f)(hypreal_of_real x + h) - hypreal_of_real (f x))"

  isUCont :: "['a::real_normed_vector => 'b::real_normed_vector] => bool"
  "isUCont f = (\<forall>r>0. \<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r)"

  isNSUCont :: "['a::real_normed_vector => 'b::real_normed_vector] => bool"
  "isNSUCont f = (\<forall>x y. x @= y --> ( *f* f) x @= ( *f* f) y)"


consts
  Bolzano_bisect :: "[real*real=>bool, real, real, nat] => (real*real)"
primrec
  "Bolzano_bisect P a b 0 = (a,b)"
  "Bolzano_bisect P a b (Suc n) =
      (let (x,y) = Bolzano_bisect P a b n
       in if P(x, (x+y)/2) then ((x+y)/2, y)
                            else (x, (x+y)/2))"


subsection {* Limits of Functions *}

subsubsection {* Purely standard proofs *}

lemma LIM_eq:
     "f -- a --> L =
     (\<forall>r>0.\<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)"
by (simp add: LIM_def diff_minus)

lemma LIM_I:
     "(!!r. 0<r ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)
      ==> f -- a --> L"
by (simp add: LIM_eq)

lemma LIM_D:
     "[| f -- a --> L; 0<r |]
      ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r"
by (simp add: LIM_eq)

lemma LIM_shift: "f -- a --> L \<Longrightarrow> (\<lambda>x. f (x + k)) -- a - k --> L"
apply (rule LIM_I)
apply (drule_tac r="r" in LIM_D, safe)
apply (rule_tac x="s" in exI, safe)
apply (drule_tac x="x + k" in spec)
apply (simp add: compare_rls)
done

lemma LIM_const [simp]: "(%x. k) -- x --> k"
by (simp add: LIM_def)

lemma LIM_add:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "f -- a --> L" and g: "g -- a --> M"
  shows "(%x. f x + g(x)) -- a --> (L + M)"
proof (rule LIM_I)
  fix r :: real
  assume r: "0 < r"
  from LIM_D [OF f half_gt_zero [OF r]]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < fs --> norm (f x - L) < r/2"
  by blast
  from LIM_D [OF g half_gt_zero [OF r]]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < gs --> norm (g x - M) < r/2"
  by blast
  show "\<exists>s>0.\<forall>x. x \<noteq> a \<and> norm (x-a) < s \<longrightarrow> norm (f x + g x - (L + M)) < r"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: 'a
    assume "x \<noteq> a \<and> norm (x-a) < min fs gs"
    hence "x \<noteq> a \<and> norm (x-a) < fs \<and> norm (x-a) < gs" by simp
    with fs_lt gs_lt
    have "norm (f x - L) < r/2" and "norm (g x - M) < r/2" by blast+
    hence "norm (f x - L) + norm (g x - M) < r" by arith
    thus "norm (f x + g x - (L + M)) < r"
      by (blast intro: norm_diff_triangle_ineq order_le_less_trans)
  qed
qed

lemma minus_diff_minus:
  fixes a b :: "'a::ab_group_add"
  shows "(- a) - (- b) = - (a - b)"
by simp

lemma LIM_minus: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
by (simp only: LIM_eq minus_diff_minus norm_minus_cancel)

lemma LIM_add_minus:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (intro LIM_add LIM_minus)

lemma LIM_diff:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) - g(x)) -- x --> l-m"
by (simp only: diff_minus LIM_add LIM_minus)

lemma LIM_const_not_eq:
  fixes a :: "'a::real_normed_div_algebra"
  shows "k \<noteq> L ==> ~ ((%x. k) -- a --> L)"
apply (simp add: LIM_eq)
apply (rule_tac x="norm (k - L)" in exI, simp, safe)
apply (rule_tac x="a + of_real (s/2)" in exI, simp add: norm_of_real)
done

lemma LIM_const_eq:
  fixes a :: "'a::real_normed_div_algebra"
  shows "(%x. k) -- a --> L ==> k = L"
apply (rule ccontr)
apply (blast dest: LIM_const_not_eq)
done

lemma LIM_unique:
  fixes a :: "'a::real_normed_div_algebra"
  shows "[| f -- a --> L; f -- a --> M |] ==> L = M"
apply (drule LIM_diff, assumption)
apply (auto dest!: LIM_const_eq)
done

lemma LIM_mult_zero:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes f: "f -- a --> 0" and g: "g -- a --> 0"
  shows "(%x. f(x) * g(x)) -- a --> 0"
proof (rule LIM_I, simp)
  fix r :: real
  assume r: "0<r"
  from LIM_D [OF f zero_less_one]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < fs --> norm (f x) < 1"
  by auto
  from LIM_D [OF g r]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & norm (x-a) < gs --> norm (g x) < r"
  by auto
  show "\<exists>s. 0 < s \<and> (\<forall>x. x \<noteq> a \<and> norm (x-a) < s \<longrightarrow> norm (f x * g x) < r)"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: 'a
    assume "x \<noteq> a \<and> norm (x-a) < min fs gs"
    hence  "x \<noteq> a \<and> norm (x-a) < fs \<and> norm (x-a) < gs" by simp
    with fs_lt gs_lt
    have "norm (f x) < 1" and "norm (g x) < r" by blast+
    hence "norm (f x) * norm (g x) < 1*r"
      by (rule mult_strict_mono' [OF _ _ norm_ge_zero norm_ge_zero])
    thus "norm (f x * g x) < r"
      by (simp add: order_le_less_trans [OF norm_mult_ineq])
  qed
qed

lemma LIM_self: "(%x. x) -- a --> a"
by (auto simp add: LIM_def)

text{*Limits are equal for functions equal except at limit point*}
lemma LIM_equal:
     "[| \<forall>x. x \<noteq> a --> (f x = g x) |] ==> (f -- a --> l) = (g -- a --> l)"
by (simp add: LIM_def)

lemma LIM_cong:
  "\<lbrakk>a = b; \<And>x. x \<noteq> b \<Longrightarrow> f x = g x; l = m\<rbrakk>
   \<Longrightarrow> (f -- a --> l) = (g -- b --> m)"
by (simp add: LIM_def)

text{*Two uses in Hyperreal/Transcendental.ML*}
lemma LIM_trans:
     "[| (%x. f(x) + -g(x)) -- a --> 0;  g -- a --> l |] ==> f -- a --> l"
apply (drule LIM_add, assumption)
apply (auto simp add: add_assoc)
done

subsubsection {* Purely nonstandard proofs *}

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
  "starfun (\<lambda>x. f x *# g x) = (\<lambda>x. scaleHR (starfun f x) (starfun g x))"
by transfer (rule refl)

lemma NSLIM_scaleR:
  "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) *# g(x)) -- x --NS> (l *# m)"
by (auto simp add: NSLIM_def intro!: approx_scaleR_HFinite)

lemma NSLIM_add:
     "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) + g(x)) -- x --NS> (l + m)"
by (auto simp add: NSLIM_def intro!: approx_add)

lemma NSLIM_const [simp]: "(%x. k) -- x --NS> k"
by (simp add: NSLIM_def)

lemma NSLIM_minus: "f -- a --NS> L ==> (%x. -f(x)) -- a --NS> -L"
by (simp add: NSLIM_def)

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
  assumes f: "f -- a --NS> l" shows "(%x. f(x) + -l) -- a --NS> 0"
proof -
  have "(\<lambda>x. f x + - l) -- a --NS> l + -l"
    by (rule NSLIM_add_minus [OF f NSLIM_const])
  thus ?thesis by simp
qed

lemma NSLIM_zero_cancel: "(%x. f(x) - l) -- x --NS> 0 ==> f -- x --NS> l"
apply (drule_tac g = "%x. l" and m = l in NSLIM_add)
apply (auto simp add: diff_minus add_assoc)
done

lemma NSLIM_const_not_eq:
  fixes a :: real (* TODO: generalize to real_normed_div_algebra *)
  shows "k \<noteq> L ==> ~ ((%x. k) -- a --NS> L)"
apply (simp add: NSLIM_def)
apply (rule_tac x="star_of a + epsilon" in exI)
apply (auto intro: Infinitesimal_add_approx_self [THEN approx_sym]
            simp add: hypreal_epsilon_not_zero)
done

lemma NSLIM_not_zero:
  fixes a :: real
  shows "k \<noteq> 0 ==> ~ ((%x. k) -- a --NS> 0)"
by (rule NSLIM_const_not_eq)

lemma NSLIM_const_eq:
  fixes a :: real
  shows "(%x. k) -- a --NS> L ==> k = L"
apply (rule ccontr)
apply (blast dest: NSLIM_const_not_eq)
done

text{* can actually be proved more easily by unfolding the definition!*}
lemma NSLIM_unique:
  fixes a :: real
  shows "[| f -- a --NS> L; f -- a --NS> M |] ==> L = M"
apply (drule NSLIM_minus)
apply (drule NSLIM_add, assumption)
apply (auto dest!: NSLIM_const_eq [symmetric])
apply (simp add: diff_def [symmetric])
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

subsubsection {* Derived theorems about @{term LIM} *}

lemma LIM_mult2:
  fixes l m :: "'a::real_normed_algebra"
  shows "[| f -- x --> l; g -- x --> m |]
      ==> (%x. f(x) * g(x)) -- x --> (l * m)"
by (simp add: LIM_NSLIM_iff NSLIM_mult)

lemma LIM_scaleR:
  "[| f -- x --> l; g -- x --> m |]
      ==> (%x. f(x) *# g(x)) -- x --> (l *# m)"
by (simp add: LIM_NSLIM_iff NSLIM_scaleR)

lemma LIM_add2:
     "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + g(x)) -- x --> (l + m)"
by (simp add: LIM_NSLIM_iff NSLIM_add)

lemma LIM_const2: "(%x. k) -- x --> k"
by (simp add: LIM_NSLIM_iff)

lemma LIM_minus2: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
by (simp add: LIM_NSLIM_iff NSLIM_minus)

lemma LIM_add_minus2: "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (simp add: LIM_NSLIM_iff NSLIM_add_minus)

lemma LIM_inverse:
  fixes L :: "'a::real_normed_div_algebra"
  shows "[| f -- a --> L; L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --> (inverse L)"
by (simp add: LIM_NSLIM_iff NSLIM_inverse)

lemma LIM_zero2: "f -- a --> l ==> (%x. f(x) + -l) -- a --> 0"
by (simp add: LIM_NSLIM_iff NSLIM_zero)

lemma LIM_zero_cancel: "(%x. f(x) - l) -- x --> 0 ==> f -- x --> l"
apply (drule_tac g = "%x. l" and M = l in LIM_add)
apply (auto simp add: diff_minus add_assoc)
done

lemma LIM_unique2:
  fixes a :: real
  shows "[| f -- a --> L; f -- a --> M |] ==> L = M"
by (simp add: LIM_NSLIM_iff NSLIM_unique)

(* we can use the corresponding thm LIM_mult2 *)
(* for standard definition of limit           *)

lemma LIM_mult_zero2:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "[| f -- x --> 0; g -- x --> 0 |] ==> (%x. f(x)*g(x)) -- x --> 0"
by (drule LIM_mult2, auto)


subsection {* Continuity *}

lemma isNSContD: "[| isNSCont f a; y \<approx> hypreal_of_real a |] ==> ( *f* f) y \<approx> hypreal_of_real (f a)"
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

lemma LIM_isCont_iff: "(f -- a --> f a) = ((%h. f(a + h)) -- 0 --> f(a))"
by (simp add: LIM_NSLIM_iff NSLIM_isCont_iff)

lemma isCont_iff: "(isCont f x) = ((%h. f(x + h)) -- 0 --> f(x))"
by (simp add: isCont_def LIM_isCont_iff)

text{*Immediate application of nonstandard criterion for continuity can offer
   very simple proofs of some standard property of continuous functions*}
text{*sum continuous*}
lemma isCont_add: "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) + g(x)) a"
by (auto intro: approx_add simp add: isNSCont_isCont_iff [symmetric] isNSCont_def)

text{*mult continuous*}
lemma isCont_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  shows "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) * g(x)) a"
by (auto intro!: starfun_mult_HFinite_approx
            simp del: starfun_mult [symmetric]
            simp add: isNSCont_isCont_iff [symmetric] isNSCont_def)

text{*composition of continuous functions
     Note very short straightforard proof!*}
lemma isCont_o: "[| isCont f a; isCont g (f a) |] ==> isCont (g o f) a"
by (auto simp add: isNSCont_isCont_iff [symmetric] isNSCont_def starfun_o [symmetric])

lemma isCont_o2: "[| isCont f a; isCont g (f a) |] ==> isCont (%x. g (f x)) a"
by (auto dest: isCont_o simp add: o_def)

lemma isNSCont_minus: "isNSCont f a ==> isNSCont (%x. - f x) a"
by (simp add: isNSCont_def)

lemma isCont_minus: "isCont f a ==> isCont (%x. - f x) a"
by (auto simp add: isNSCont_isCont_iff [symmetric] isNSCont_minus)

lemma isCont_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  shows "[| isCont f x; f x \<noteq> 0 |] ==> isCont (%x. inverse (f x)) x"
apply (simp add: isCont_def)
apply (blast intro: LIM_inverse)
done

lemma isNSCont_inverse:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  shows "[| isNSCont f x; f x \<noteq> 0 |] ==> isNSCont (%x. inverse (f x)) x"
by (auto intro: isCont_inverse simp add: isNSCont_isCont_iff)

lemma isCont_diff:
      "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) - g(x)) a"
apply (simp add: diff_minus)
apply (auto intro: isCont_add isCont_minus)
done

lemma isCont_Id: "isCont (\<lambda>x. x) a"
by (simp only: isCont_def LIM_self)

lemma isCont_const [simp]: "isCont (%x. k) a"
by (simp add: isCont_def)

lemma isNSCont_const [simp]: "isNSCont (%x. k) a"
by (simp add: isNSCont_def)

lemma isNSCont_abs [simp]: "isNSCont abs (a::real)"
apply (simp add: isNSCont_def)
apply (auto intro: approx_hrabs simp add: hypreal_of_real_hrabs [symmetric] starfun_rabs_hrabs)
done

lemma isCont_abs [simp]: "isCont abs (a::real)"
by (auto simp add: isNSCont_isCont_iff [symmetric])


(****************************************************************
(%* Leave as commented until I add topology theory or remove? *%)
(%*------------------------------------------------------------
  Elementary topology proof for a characterisation of
  continuity now: a function f is continuous if and only
  if the inverse image, {x. f(x) \<in> A}, of any open set A
  is always an open set
 ------------------------------------------------------------*%)
Goal "[| isNSopen A; \<forall>x. isNSCont f x |]
               ==> isNSopen {x. f x \<in> A}"
by (auto_tac (claset(),simpset() addsimps [isNSopen_iff1]));
by (dtac (mem_monad_approx RS approx_sym);
by (dres_inst_tac [("x","a")] spec 1);
by (dtac isNSContD 1 THEN assume_tac 1)
by (dtac bspec 1 THEN assume_tac 1)
by (dres_inst_tac [("x","( *f* f) x")] approx_mem_monad2 1);
by (blast_tac (claset() addIs [starfun_mem_starset]);
qed "isNSCont_isNSopen";

Goalw [isNSCont_def]
          "\<forall>A. isNSopen A --> isNSopen {x. f x \<in> A} \
\              ==> isNSCont f x";
by (auto_tac (claset() addSIs [(mem_infmal_iff RS iffD1) RS
     (approx_minus_iff RS iffD2)],simpset() addsimps
      [Infinitesimal_def,SReal_iff]));
by (dres_inst_tac [("x","{z. abs(z + -f(x)) < ya}")] spec 1);
by (etac (isNSopen_open_interval RSN (2,impE));
by (auto_tac (claset(),simpset() addsimps [isNSopen_def,isNSnbhd_def]));
by (dres_inst_tac [("x","x")] spec 1);
by (auto_tac (claset() addDs [approx_sym RS approx_mem_monad],
    simpset() addsimps [hypreal_of_real_zero RS sym,STAR_starfun_rabs_add_minus]));
qed "isNSopen_isNSCont";

Goal "(\<forall>x. isNSCont f x) = \
\     (\<forall>A. isNSopen A --> isNSopen {x. f(x) \<in> A})";
by (blast_tac (claset() addIs [isNSCont_isNSopen,
    isNSopen_isNSCont]);
qed "isNSCont_isNSopen_iff";

(%*------- Standard version of same theorem --------*%)
Goal "(\<forall>x. isCont f x) = \
\         (\<forall>A. isopen A --> isopen {x. f(x) \<in> A})";
by (auto_tac (claset() addSIs [isNSCont_isNSopen_iff],
              simpset() addsimps [isNSopen_isopen_iff RS sym,
              isNSCont_isCont_iff RS sym]));
qed "isCont_isopen_iff";
*******************************************************************)

subsection {* Uniform Continuity *}

lemma isNSUContD: "[| isNSUCont f; x \<approx> y|] ==> ( *f* f) x \<approx> ( *f* f) y"
by (simp add: isNSUCont_def)

lemma isUCont_isCont: "isUCont f ==> isCont f x"
by (simp add: isUCont_def isCont_def LIM_def, meson)

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
      by (auto simp add: isUCont_def)
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
proof (unfold isUCont_def, safe)
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

subsection {* Derivatives *}

subsubsection {* Purely standard proofs *}

lemma DERIV_iff: "(DERIV f x :> D) = ((%h. (f(x + h) - f(x))/#h) -- 0 --> D)"
by (simp add: deriv_def)

lemma DERIV_D: "DERIV f x :> D ==> (%h. (f(x + h) - f(x))/#h) -- 0 --> D"
by (simp add: deriv_def)

lemma DERIV_const [simp]: "DERIV (\<lambda>x. k) x :> 0"
by (simp add: deriv_def)

lemma DERIV_Id [simp]: "DERIV (\<lambda>x. x) x :> 1"
by (simp add: deriv_def real_scaleR_def cong: LIM_cong)

lemma add_diff_add:
  fixes a b c d :: "'a::ab_group_add"
  shows "(a + c) - (b + d) = (a - b) + (c - d)"
by simp

lemma DERIV_add:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E\<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. f x + g x) x :> D + E"
by (simp only: deriv_def add_diff_add scaleR_right_distrib LIM_add)

lemma DERIV_minus:
  "DERIV f x :> D \<Longrightarrow> DERIV (\<lambda>x. - f x) x :> - D"
by (simp only: deriv_def minus_diff_minus scaleR_minus_right LIM_minus)

lemma DERIV_diff:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E\<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. f x - g x) x :> D - E"
by (simp only: diff_def DERIV_add DERIV_minus)

lemma DERIV_add_minus:
  "\<lbrakk>DERIV f x :> D; DERIV g x :> E\<rbrakk> \<Longrightarrow> DERIV (\<lambda>x. f x + - g x) x :> D + - E"
by (simp only: DERIV_add DERIV_minus)

lemma DERIV_isCont: "DERIV f x :> D \<Longrightarrow> isCont f x"
proof (unfold isCont_iff)
  assume "DERIV f x :> D"
  hence "(\<lambda>h. (f(x+h) - f(x)) /# h) -- 0 --> D"
    by (rule DERIV_D)
  hence "(\<lambda>h. h *# ((f(x+h) - f(x)) /# h)) -- 0 --> 0 *# D"
    by (intro LIM_scaleR LIM_self)
  hence "(\<lambda>h. (f(x+h) - f(x))) -- 0 --> 0"
    by (simp cong: LIM_cong)
  thus "(\<lambda>h. f(x+h)) -- 0 --> f(x)"
    by (simp add: LIM_def)
qed

lemma DERIV_mult_lemma:
  fixes a b c d :: "'a::real_algebra"
  shows "(a * b - c * d) /# h = a * ((b - d) /# h) + ((a - c) /# h) * d"
by (simp add: diff_minus scaleR_right_distrib [symmetric] ring_distrib)

lemma DERIV_mult':
  fixes f g :: "real \<Rightarrow> 'a::real_normed_algebra"
  assumes f: "DERIV f x :> D"
  assumes g: "DERIV g x :> E"
  shows "DERIV (\<lambda>x. f x * g x) x :> f x * E + D * g x"
proof (unfold deriv_def)
  from f have "isCont f x"
    by (rule DERIV_isCont)
  hence "(\<lambda>h. f(x+h)) -- 0 --> f x"
    by (simp only: isCont_iff)
  hence "(\<lambda>h. f(x+h) * ((g(x+h) - g x) /# h) +
              ((f(x+h) - f x) /# h) * g x)
          -- 0 --> f x * E + D * g x"
    by (intro LIM_add LIM_mult2 LIM_const DERIV_D f g)
  thus "(\<lambda>h. (f(x+h) * g(x+h) - f x * g x) /# h)
         -- 0 --> f x * E + D * g x"
    by (simp only: DERIV_mult_lemma)
qed

lemma DERIV_mult:
  fixes f g :: "real \<Rightarrow> 'a::{real_normed_algebra,comm_ring}" shows
     "[| DERIV f x :> Da; DERIV g x :> Db |]
      ==> DERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
by (drule (1) DERIV_mult', simp only: mult_commute add_commute)

lemma DERIV_unique:
      "[| DERIV f x :> D; DERIV f x :> E |] ==> D = E"
apply (simp add: deriv_def)
apply (blast intro: LIM_unique)
done

text{*Differentiation of finite sum*}

lemma DERIV_sumr [rule_format (no_asm)]:
     "(\<forall>r. m \<le> r & r < (m + n) --> DERIV (%x. f r x) x :> (f' r x))
      --> DERIV (%x. \<Sum>n=m..<n::nat. f n x :: real) x :> (\<Sum>r=m..<n. f' r x)"
apply (induct "n")
apply (auto intro: DERIV_add)
done

text{*Alternative definition for differentiability*}

lemma DERIV_LIM_iff:
     "((%h::real. (f(a + h) - f(a)) / h) -- 0 --> D) =
      ((%x. (f(x)-f(a)) / (x-a)) -- a --> D)"
apply (rule iffI)
apply (drule_tac k="- a" in LIM_shift)
apply (simp add: diff_minus)
apply (drule_tac k="a" in LIM_shift)
apply (simp add: add_commute)
done

lemma DERIV_LIM_iff':
     "((%h::real. (f(a + h) - f(a)) /# h) -- 0 --> D) =
      ((%x. (f(x)-f(a)) /# (x-a)) -- a --> D)"
apply (rule iffI)
apply (drule_tac k="- a" in LIM_shift)
apply (simp add: diff_minus)
apply (drule_tac k="a" in LIM_shift)
apply (simp add: add_commute)
done

lemma DERIV_iff2: "(DERIV f x :> D) = ((%z. (f(z) - f(x)) /# (z-x)) -- x --> D)"
by (simp add: deriv_def diff_minus [symmetric] DERIV_LIM_iff')

lemma inverse_diff_inverse:
  "\<lbrakk>(a::'a::division_ring) \<noteq> 0; b \<noteq> 0\<rbrakk>
   \<Longrightarrow> inverse a - inverse b = - (inverse a * (a - b) * inverse b)"
by (simp add: right_diff_distrib left_diff_distrib mult_assoc)

lemma DERIV_inverse_lemma:
  "\<lbrakk>a \<noteq> 0; b \<noteq> (0::'a::real_normed_div_algebra)\<rbrakk>
   \<Longrightarrow> (inverse a - inverse b) /# h
     = - (inverse a * ((a - b) /# h) * inverse b)"
by (simp add: inverse_diff_inverse)

lemma LIM_equal2:
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- a --> l"
apply (unfold LIM_def, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="min s R" in exI, safe)
apply (simp add: 1)
apply (simp add: 2)
done

lemma DERIV_inverse':
  fixes f :: "real \<Rightarrow> 'a::real_normed_div_algebra"
  assumes der: "DERIV f x :> D"
  assumes neq: "f x \<noteq> 0"
  shows "DERIV (\<lambda>x. inverse (f x)) x :> - (inverse (f x) * D * inverse (f x))"
    (is "DERIV _ _ :> ?E")
proof (unfold DERIV_iff2)
  from der have lim_f: "f -- x --> f x"
    by (rule DERIV_isCont [unfolded isCont_def])

  from neq have "0 < norm (f x)" by simp
  with LIM_D [OF lim_f] obtain s
    where s: "0 < s"
    and less_fx: "\<And>z. \<lbrakk>z \<noteq> x; norm (z - x) < s\<rbrakk>
                  \<Longrightarrow> norm (f z - f x) < norm (f x)"
    by fast

  show "(\<lambda>z. (inverse (f z) - inverse (f x)) /# (z - x)) -- x --> ?E"
  proof (rule LIM_equal2 [OF s])
    fix z :: real
    assume "z \<noteq> x" "norm (z - x) < s"
    hence "norm (f z - f x) < norm (f x)" by (rule less_fx)
    hence "f z \<noteq> 0" by auto
    thus "(inverse (f z) - inverse (f x)) /# (z - x) =
          - (inverse (f z) * ((f z - f x) /# (z - x)) * inverse (f x))"
      using neq by (rule DERIV_inverse_lemma)
  next
    from der have "(\<lambda>z. (f z - f x) /# (z - x)) -- x --> D"
      by (unfold DERIV_iff2)
    thus "(\<lambda>z. - (inverse (f z) * ((f z - f x) /# (z - x)) * inverse (f x)))
          -- x --> ?E"
      by (intro LIM_mult2 LIM_inverse LIM_minus LIM_const lim_f neq)
  qed
qed

lemma DERIV_divide:
  fixes D E :: "'a::{real_normed_div_algebra,field}"
  shows "\<lbrakk>DERIV f x :> D; DERIV g x :> E; g x \<noteq> 0\<rbrakk>
         \<Longrightarrow> DERIV (\<lambda>x. f x / g x) x :> (D * g x - f x * E) / (g x * g x)"
apply (subgoal_tac "f x * - (inverse (g x) * E * inverse (g x)) +
          D * inverse (g x) = (D * g x - f x * E) / (g x * g x)")
apply (erule subst)
apply (unfold divide_inverse)
apply (erule DERIV_mult')
apply (erule (1) DERIV_inverse')
apply (simp add: left_diff_distrib nonzero_inverse_mult_distrib)
apply (simp add: mult_ac)
done

lemma DERIV_power_Suc:
  fixes f :: "real \<Rightarrow> 'a::{real_normed_algebra,recpower}"
  assumes f: "DERIV f x :> D"
  shows "DERIV (\<lambda>x. f x ^ Suc n) x :> (of_nat n + 1) *# (D * f x ^ n)"
proof (induct n)
case 0
  show ?case by (simp add: power_Suc f)
case (Suc k)
  from DERIV_mult' [OF f Suc] show ?case
    apply (simp only: of_nat_Suc scaleR_left_distrib scaleR_one)
    apply (simp only: power_Suc right_distrib mult_scaleR_right mult_ac)
    done
qed

lemma DERIV_power:
  fixes f :: "real \<Rightarrow> 'a::{real_normed_algebra,recpower}"
  assumes f: "DERIV f x :> D"
  shows "DERIV (\<lambda>x. f x ^ n) x :> of_nat n *# (D * f x ^ (n - Suc 0))"
by (cases "n", simp, simp add: DERIV_power_Suc f)


(* ------------------------------------------------------------------------ *)
(* Caratheodory formulation of derivative at a point: standard proof        *)
(* ------------------------------------------------------------------------ *)

lemma CARAT_DERIV:
     "(DERIV f x :> l) =
      (\<exists>g. (\<forall>z. f z - f x = (z-x) *# g z) & isCont g x & g x = l)"
      (is "?lhs = ?rhs")
proof
  assume der: "DERIV f x :> l"
  show "\<exists>g. (\<forall>z. f z - f x = (z-x) *# g z) \<and> isCont g x \<and> g x = l"
  proof (intro exI conjI)
    let ?g = "(%z. if z = x then l else (f z - f x) /# (z-x))"
    show "\<forall>z. f z - f x = (z-x) *# ?g z" by (simp)
    show "isCont ?g x" using der
      by (simp add: isCont_iff DERIV_iff diff_minus
               cong: LIM_equal [rule_format])
    show "?g x = l" by simp
  qed
next
  assume "?rhs"
  then obtain g where
    "(\<forall>z. f z - f x = (z-x) *# g z)" and "isCont g x" and "g x = l" by blast
  thus "(DERIV f x :> l)"
     by (auto simp add: isCont_iff DERIV_iff diff_minus
               cong: LIM_equal [rule_format])
qed

lemma LIM_compose:
  assumes f: "f -- a --> l"
  assumes g: "isCont g l"
  shows "(\<lambda>x. g (f x)) -- a --> g l"
proof (rule LIM_I)
  fix r::real assume r: "0 < r"
  obtain s where s: "0 < s"
    and less_r: "\<And>y. \<lbrakk>y \<noteq> l; norm (y - l) < s\<rbrakk> \<Longrightarrow> norm (g y - g l) < r"
    using LIM_D [OF g [unfolded isCont_def] r] by fast
  obtain t where t: "0 < t"
    and less_s: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < t\<rbrakk> \<Longrightarrow> norm (f x - l) < s"
    using LIM_D [OF f s] by fast

  show "\<exists>t>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < t \<longrightarrow> norm (g (f x) - g l) < r"
  proof (rule exI, safe)
    show "0 < t" using t .
  next
    fix x assume "x \<noteq> a" and "norm (x - a) < t"
    hence "norm (f x - l) < s" by (rule less_s)
    thus "norm (g (f x) - g l) < r"
      using r less_r by (case_tac "f x = l", simp_all)
  qed
qed

lemma DERIV_chain':
  assumes f: "DERIV f x :> D"
  assumes g: "DERIV g (f x) :> E"
  shows "DERIV (\<lambda>x. g (f x)) x :> D *# E"
proof (unfold DERIV_iff2)
  obtain d where d: "\<forall>y. g y - g (f x) = (y - f x) *# d y"
    and cont_d: "isCont d (f x)" and dfx: "d (f x) = E"
    using CARAT_DERIV [THEN iffD1, OF g] by fast
  from f have "f -- x --> f x"
    by (rule DERIV_isCont [unfolded isCont_def])
  hence "(\<lambda>z. d (f z)) -- x --> d (f x)"
    using cont_d by (rule LIM_compose)
  hence "(\<lambda>z. ((f z - f x) /# (z - x)) *# d (f z))
          -- x --> D *# d (f x)"
    by (rule LIM_scaleR [OF f [unfolded DERIV_iff2]])
  thus "(\<lambda>z. (g (f z) - g (f x)) /# (z - x)) -- x --> D *# E"
    by (simp add: d dfx real_scaleR_def)
qed


subsubsection {* Nonstandard proofs *}

lemma DERIV_NS_iff:
      "(DERIV f x :> D) = ((%h. (f(x + h) - f(x))/#h) -- 0 --NS> D)"
by (simp add: deriv_def LIM_NSLIM_iff)

lemma NS_DERIV_D: "DERIV f x :> D ==> (%h. (f(x + h) - f(x))/#h) -- 0 --NS> D"
by (simp add: deriv_def LIM_NSLIM_iff)

lemma NSDeriv_unique:
     "[| NSDERIV f x :> D; NSDERIV f x :> E |] ==> D = E"
apply (simp add: nsderiv_def)
apply (cut_tac Infinitesimal_epsilon hypreal_epsilon_not_zero)
apply (auto dest!: bspec [where x=epsilon]
            intro!: inj_hypreal_of_real [THEN injD]
            dest: approx_trans3)
done

text {*First NSDERIV in terms of NSLIM*}

text{*first equivalence *}
lemma NSDERIV_NSLIM_iff:
      "(NSDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NS> D)"
apply (simp add: nsderiv_def NSLIM_def, auto)
apply (drule_tac x = xa in bspec)
apply (rule_tac [3] ccontr)
apply (drule_tac [3] x = h in spec)
apply (auto simp add: mem_infmal_iff starfun_lambda_cancel)
done

text{*second equivalence *}
lemma NSDERIV_NSLIM_iff2:
     "(NSDERIV f x :> D) = ((%z. (f(z) - f(x)) / (z-x)) -- x --NS> D)"
by (simp add: NSDERIV_NSLIM_iff DERIV_LIM_iff  diff_minus [symmetric]
              LIM_NSLIM_iff [symmetric])

(* while we're at it! *)
lemma NSDERIV_iff2:
     "(NSDERIV f x :> D) =
      (\<forall>w.
        w \<noteq> hypreal_of_real x & w \<approx> hypreal_of_real x -->
        ( *f* (%z. (f z - f x) / (z-x))) w \<approx> hypreal_of_real D)"
by (simp add: NSDERIV_NSLIM_iff2 NSLIM_def)

(*FIXME DELETE*)
lemma hypreal_not_eq_minus_iff: "(x \<noteq> a) = (x - a \<noteq> (0::hypreal))"
by (auto dest: hypreal_eq_minus_iff [THEN iffD2])

lemma NSDERIVD5:
  "(NSDERIV f x :> D) ==>
   (\<forall>u. u \<approx> hypreal_of_real x -->
     ( *f* (%z. f z - f x)) u \<approx> hypreal_of_real D * (u - hypreal_of_real x))"
apply (auto simp add: NSDERIV_iff2)
apply (case_tac "u = hypreal_of_real x", auto)
apply (drule_tac x = u in spec, auto)
apply (drule_tac c = "u - hypreal_of_real x" and b = "hypreal_of_real D" in approx_mult1)
apply (drule_tac [!] hypreal_not_eq_minus_iff [THEN iffD1])
apply (subgoal_tac [2] "( *f* (%z. z-x)) u \<noteq> (0::hypreal) ")
apply (auto simp add:
         approx_minus_iff [THEN iffD1, THEN mem_infmal_iff [THEN iffD2]]
         Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma NSDERIVD4:
     "(NSDERIV f x :> D) ==>
      (\<forall>h \<in> Infinitesimal.
               (( *f* f)(hypreal_of_real x + h) -
                 hypreal_of_real (f x))\<approx> (hypreal_of_real D) * h)"
apply (auto simp add: nsderiv_def)
apply (case_tac "h = (0::hypreal) ")
apply (auto simp add: diff_minus)
apply (drule_tac x = h in bspec)
apply (drule_tac [2] c = h in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: diff_minus)
done

lemma NSDERIVD3:
     "(NSDERIV f x :> D) ==>
      (\<forall>h \<in> Infinitesimal - {0}.
               (( *f* f)(hypreal_of_real x + h) -
                 hypreal_of_real (f x))\<approx> (hypreal_of_real D) * h)"
apply (auto simp add: nsderiv_def)
apply (rule ccontr, drule_tac x = h in bspec)
apply (drule_tac [2] c = h in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc diff_minus)
done

text{*Differentiability implies continuity
         nice and simple "algebraic" proof*}
lemma NSDERIV_isNSCont: "NSDERIV f x :> D ==> isNSCont f x"
apply (auto simp add: nsderiv_def isNSCont_NSLIM_iff NSLIM_def)
apply (drule approx_minus_iff [THEN iffD1])
apply (drule hypreal_not_eq_minus_iff [THEN iffD1])
apply (drule_tac x = "xa - hypreal_of_real x" in bspec)
 prefer 2 apply (simp add: add_assoc [symmetric])
apply (auto simp add: mem_infmal_iff [symmetric] add_commute)
apply (drule_tac c = "xa - hypreal_of_real x" in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc)
apply (drule_tac x3=D in
           HFinite_hypreal_of_real [THEN [2] Infinitesimal_HFinite_mult,
             THEN mem_infmal_iff [THEN iffD1]])
apply (auto simp add: mult_commute
            intro: approx_trans approx_minus_iff [THEN iffD2])
done

text{*Differentiation rules for combinations of functions
      follow from clear, straightforard, algebraic
      manipulations*}
text{*Constant function*}

(* use simple constant nslimit theorem *)
lemma NSDERIV_const [simp]: "(NSDERIV (%x. k) x :> 0)"
by (simp add: NSDERIV_NSLIM_iff)

text{*Sum of functions- proved easily*}

lemma NSDERIV_add: "[| NSDERIV f x :> Da;  NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x + g x) x :> Da + Db"
apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
apply (auto simp add: add_divide_distrib diff_divide_distrib dest!: spec)
apply (drule_tac b = "hypreal_of_real Da" and d = "hypreal_of_real Db" in approx_add)
apply (auto simp add: diff_def add_ac)
done

text{*Product of functions - Proof is trivial but tedious
  and long due to rearrangement of terms*}

lemma lemma_nsderiv1: "((a::hypreal)*b) - (c*d) = (b*(a - c)) + (c*(b - d))"
by (simp add: right_diff_distrib)

lemma lemma_nsderiv2: "[| (x - y) / z = hypreal_of_real D + yb; z \<noteq> 0;
         z \<in> Infinitesimal; yb \<in> Infinitesimal |]
      ==> x - y \<approx> 0"
apply (frule_tac c1 = z in hypreal_mult_right_cancel [THEN iffD2], assumption)
apply (erule_tac V = "(x - y) / z = hypreal_of_real D + yb" in thin_rl)
apply (auto intro!: Infinitesimal_HFinite_mult2 HFinite_add
            simp add: mult_assoc mem_infmal_iff [symmetric])
apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma NSDERIV_mult: "[| NSDERIV f x :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
apply (auto dest!: spec
      simp add: starfun_lambda_cancel lemma_nsderiv1)
apply (simp (no_asm) add: add_divide_distrib diff_divide_distrib)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply (auto simp add: times_divide_eq_right [symmetric]
            simp del: times_divide_eq)
apply (drule_tac D = Db in lemma_nsderiv2, assumption+)
apply (drule_tac
     approx_minus_iff [THEN iffD2, THEN bex_Infinitesimal_iff2 [THEN iffD2]])
apply (auto intro!: approx_add_mono1
            simp add: left_distrib right_distrib mult_commute add_assoc)
apply (rule_tac b1 = "hypreal_of_real Db * hypreal_of_real (f x)"
         in add_commute [THEN subst])
apply (auto intro!: Infinitesimal_add_approx_self2 [THEN approx_sym]
                    Infinitesimal_add Infinitesimal_mult
                    Infinitesimal_hypreal_of_real_mult
                    Infinitesimal_hypreal_of_real_mult2
          simp add: add_assoc [symmetric])
done

text{*Multiplying by a constant*}
lemma NSDERIV_cmult: "NSDERIV f x :> D
      ==> NSDERIV (%x. c * f x) x :> c*D"
apply (simp only: times_divide_eq_right [symmetric] NSDERIV_NSLIM_iff
                  minus_mult_right right_diff_distrib [symmetric])
apply (erule NSLIM_const [THEN NSLIM_mult])
done

text{*Negation of function*}
lemma NSDERIV_minus: "NSDERIV f x :> D ==> NSDERIV (%x. -(f x)) x :> -D"
proof (simp add: NSDERIV_NSLIM_iff)
  assume "(\<lambda>h. (f (x + h) - f x) / h) -- 0 --NS> D"
  hence deriv: "(\<lambda>h. - ((f(x+h) - f x) / h)) -- 0 --NS> - D"
    by (rule NSLIM_minus)
  have "\<forall>h. - ((f (x + h) - f x) / h) = (- f (x + h) + f x) / h"
    by (simp add: minus_divide_left)
  with deriv
  show "(\<lambda>h. (- f (x + h) + f x) / h) -- 0 --NS> - D" by simp
qed

text{*Subtraction*}
lemma NSDERIV_add_minus: "[| NSDERIV f x :> Da; NSDERIV g x :> Db |] ==> NSDERIV (%x. f x + -g x) x :> Da + -Db"
by (blast dest: NSDERIV_add NSDERIV_minus)

lemma NSDERIV_diff:
     "[| NSDERIV f x :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x - g x) x :> Da-Db"
apply (simp add: diff_minus)
apply (blast intro: NSDERIV_add_minus)
done

text{*  Similarly to the above, the chain rule admits an entirely
   straightforward derivation. Compare this with Harrison's
   HOL proof of the chain rule, which proved to be trickier and
   required an alternative characterisation of differentiability-
   the so-called Carathedory derivative. Our main problem is
   manipulation of terms.*}


(* lemmas *)
lemma NSDERIV_zero:
      "[| NSDERIV g x :> D;
               ( *f* g) (hypreal_of_real(x) + xa) = hypreal_of_real(g x);
               xa \<in> Infinitesimal;
               xa \<noteq> 0
            |] ==> D = 0"
apply (simp add: nsderiv_def)
apply (drule bspec, auto)
done

(* can be proved differently using NSLIM_isCont_iff *)
lemma NSDERIV_approx:
     "[| NSDERIV f x :> D;  h \<in> Infinitesimal;  h \<noteq> 0 |]
      ==> ( *f* f) (hypreal_of_real(x) + h) - hypreal_of_real(f x) \<approx> 0"
apply (simp add: nsderiv_def)
apply (simp add: mem_infmal_iff [symmetric])
apply (rule Infinitesimal_ratio)
apply (rule_tac [3] approx_hypreal_of_real_HFinite, auto)
done

(*---------------------------------------------------------------
   from one version of differentiability

                f(x) - f(a)
              --------------- \<approx> Db
                  x - a
 ---------------------------------------------------------------*)
lemma NSDERIVD1: "[| NSDERIV f (g x) :> Da;
         ( *f* g) (hypreal_of_real(x) + xa) \<noteq> hypreal_of_real (g x);
         ( *f* g) (hypreal_of_real(x) + xa) \<approx> hypreal_of_real (g x)
      |] ==> (( *f* f) (( *f* g) (hypreal_of_real(x) + xa))
                   - hypreal_of_real (f (g x)))
              / (( *f* g) (hypreal_of_real(x) + xa) - hypreal_of_real (g x))
             \<approx> hypreal_of_real(Da)"
by (auto simp add: NSDERIV_NSLIM_iff2 NSLIM_def diff_minus [symmetric])

(*--------------------------------------------------------------
   from other version of differentiability

                f(x + h) - f(x)
               ----------------- \<approx> Db
                       h
 --------------------------------------------------------------*)
lemma NSDERIVD2: "[| NSDERIV g x :> Db; xa \<in> Infinitesimal; xa \<noteq> 0 |]
      ==> (( *f* g) (hypreal_of_real(x) + xa) - hypreal_of_real(g x)) / xa
          \<approx> hypreal_of_real(Db)"
by (auto simp add: NSDERIV_NSLIM_iff NSLIM_def mem_infmal_iff starfun_lambda_cancel)

lemma lemma_chain: "(z::hypreal) \<noteq> 0 ==> x*y = (x*inverse(z))*(z*y)"
by auto

text{*This proof uses both definitions of differentiability.*}
lemma NSDERIV_chain: "[| NSDERIV f (g x) :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (f o g) x :> Da * Db"
apply (simp (no_asm_simp) add: NSDERIV_NSLIM_iff NSLIM_def
                mem_infmal_iff [symmetric])
apply clarify
apply (frule_tac f = g in NSDERIV_approx)
apply (auto simp add: starfun_lambda_cancel2 starfun_o [symmetric])
apply (case_tac "( *f* g) (hypreal_of_real (x) + xa) = hypreal_of_real (g x) ")
apply (drule_tac g = g in NSDERIV_zero)
apply (auto simp add: divide_inverse)
apply (rule_tac z1 = "( *f* g) (hypreal_of_real (x) + xa) - hypreal_of_real (g x) " and y1 = "inverse xa" in lemma_chain [THEN ssubst])
apply (erule hypreal_not_eq_minus_iff [THEN iffD1])
apply (rule approx_mult_hypreal_of_real)
apply (simp_all add: divide_inverse [symmetric])
apply (blast intro: NSDERIVD1 approx_minus_iff [THEN iffD2])
apply (blast intro: NSDERIVD2)
done

text{*Differentiation of natural number powers*}
lemma NSDERIV_Id [simp]: "NSDERIV (%x. x) x :> 1"
by (simp add: NSDERIV_NSLIM_iff NSLIM_def divide_self del: divide_self_if)

lemma NSDERIV_cmult_Id [simp]: "NSDERIV (op * c) x :> c"
by (cut_tac c = c and x = x in NSDERIV_Id [THEN NSDERIV_cmult], simp)

(*Can't get rid of x \<noteq> 0 because it isn't continuous at zero*)
lemma NSDERIV_inverse:
     "x \<noteq> 0 ==> NSDERIV (%x. inverse(x)) x :> (- (inverse x ^ Suc (Suc 0)))"
apply (simp add: nsderiv_def)
apply (rule ballI, simp, clarify)
apply (frule (1) Infinitesimal_add_not_zero)
apply (simp add: add_commute)
(*apply (auto simp add: starfun_inverse_inverse realpow_two
        simp del: minus_mult_left [symmetric] minus_mult_right [symmetric])*)
apply (simp add: inverse_add inverse_mult_distrib [symmetric]
              inverse_minus_eq [symmetric] add_ac mult_ac diff_def
            del: inverse_mult_distrib inverse_minus_eq
                 minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (simp (no_asm_simp) add: mult_assoc [symmetric] right_distrib
            del: minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (rule_tac y = "inverse (- hypreal_of_real x * hypreal_of_real x)" in approx_trans)
apply (rule inverse_add_Infinitesimal_approx2)
apply (auto dest!: hypreal_of_real_HFinite_diff_Infinitesimal
            simp add: inverse_minus_eq [symmetric] HFinite_minus_iff)
apply (rule Infinitesimal_HFinite_mult2, auto)
done

subsubsection {* Equivalence of NS and Standard definitions *}

lemma divideR_eq_divide [simp]: "x /# y = x / y"
by (simp add: real_scaleR_def divide_inverse mult_commute)

text{*Now equivalence between NSDERIV and DERIV*}
lemma NSDERIV_DERIV_iff: "(NSDERIV f x :> D) = (DERIV f x :> D)"
by (simp add: deriv_def NSDERIV_NSLIM_iff LIM_NSLIM_iff)

(* let's do the standard proof though theorem *)
(* LIM_mult2 follows from a NS proof          *)

lemma DERIV_cmult:
  fixes f :: "real \<Rightarrow> 'a::real_normed_algebra" shows
      "DERIV f x :> D ==> DERIV (%x. c * f x) x :> c*D"
by (drule DERIV_mult' [OF DERIV_const], simp)

(* standard version *)
lemma DERIV_chain: "[| DERIV f (g x) :> Da; DERIV g x :> Db |] ==> DERIV (f o g) x :> Da * Db"
by (drule (1) DERIV_chain', simp add: o_def real_scaleR_def mult_commute)

lemma DERIV_chain2: "[| DERIV f (g x) :> Da; DERIV g x :> Db |] ==> DERIV (%x. f (g x)) x :> Da * Db"
by (auto dest: DERIV_chain simp add: o_def)

(*derivative of linear multiplication*)
lemma DERIV_cmult_Id [simp]: "DERIV (op * c) x :> c"
by (cut_tac c = c and x = x in DERIV_Id [THEN DERIV_cmult], simp)

lemma DERIV_pow: "DERIV (%x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
apply (cut_tac DERIV_power [OF DERIV_Id])
apply (simp add: real_scaleR_def real_of_nat_def)
done

(* NS version *)
lemma NSDERIV_pow: "NSDERIV (%x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
by (simp add: NSDERIV_DERIV_iff DERIV_pow)

text{*Power of -1*}

lemma DERIV_inverse: "x \<noteq> 0 ==> DERIV (%x. inverse(x)) x :> (-(inverse x ^ Suc (Suc 0)))"
by (drule DERIV_inverse' [OF DERIV_Id], simp)

text{*Derivative of inverse*}
lemma DERIV_inverse_fun: "[| DERIV f x :> d; f(x) \<noteq> 0 |]
      ==> DERIV (%x. inverse(f x)::real) x :> (- (d * inverse(f(x) ^ Suc (Suc 0))))"
by (drule (1) DERIV_inverse', simp add: mult_ac)

lemma NSDERIV_inverse_fun: "[| NSDERIV f x :> d; f(x) \<noteq> 0 |]
      ==> NSDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ Suc (Suc 0))))"
by (simp add: NSDERIV_DERIV_iff DERIV_inverse_fun del: realpow_Suc)

text{*Derivative of quotient*}
lemma DERIV_quotient: "[| DERIV f x :> d; DERIV g x :> e; g(x) \<noteq> 0 |]
       ==> DERIV (%y. f(y) / (g y) :: real) x :> (d*g(x) - (e*f(x))) / (g(x) ^ Suc (Suc 0))"
by (drule (2) DERIV_divide, simp add: mult_commute)

lemma NSDERIV_quotient: "[| NSDERIV f x :> d; DERIV g x :> e; g(x) \<noteq> 0 |]
       ==> NSDERIV (%y. f(y) / (g y)) x :> (d*g(x)
                            - (e*f(x))) / (g(x) ^ Suc (Suc 0))"
by (simp add: NSDERIV_DERIV_iff DERIV_quotient del: realpow_Suc)

lemma CARAT_NSDERIV: "NSDERIV f x :> l ==>
      \<exists>g. (\<forall>z. f z - f x = g z * (z-x)) & isNSCont g x & g x = l"
by (auto simp add: NSDERIV_DERIV_iff isNSCont_isCont_iff CARAT_DERIV
                   real_scaleR_def mult_commute)

lemma hypreal_eq_minus_iff3: "(x = y + z) = (x + -z = (y::hypreal))"
by auto

lemma CARAT_DERIVD:
  assumes all: "\<forall>z. f z - f x = g z * (z-x)"
      and nsc: "isNSCont g x"
  shows "NSDERIV f x :> g x"
proof -
  from nsc
  have "\<forall>w. w \<noteq> hypreal_of_real x \<and> w \<approx> hypreal_of_real x \<longrightarrow>
         ( *f* g) w * (w - hypreal_of_real x) / (w - hypreal_of_real x) \<approx>
         hypreal_of_real (g x)"
    by (simp add: diff_minus isNSCont_def)
  thus ?thesis using all
    by (simp add: NSDERIV_iff2 starfun_if_eq cong: if_cong)
qed

subsubsection {* Differentiability predicate *}

lemma differentiableD: "f differentiable x ==> \<exists>D. DERIV f x :> D"
by (simp add: differentiable_def)

lemma differentiableI: "DERIV f x :> D ==> f differentiable x"
by (force simp add: differentiable_def)

lemma NSdifferentiableD: "f NSdifferentiable x ==> \<exists>D. NSDERIV f x :> D"
by (simp add: NSdifferentiable_def)

lemma NSdifferentiableI: "NSDERIV f x :> D ==> f NSdifferentiable x"
by (force simp add: NSdifferentiable_def)

lemma differentiable_const: "(\<lambda>z. a) differentiable x"
  apply (unfold differentiable_def)
  apply (rule_tac x=0 in exI)
  apply simp
  done

lemma differentiable_sum:
  assumes "f differentiable x"
  and "g differentiable x"
  shows "(\<lambda>x. f x + g x) differentiable x"
proof -
  from prems have "\<exists>D. DERIV f x :> D" by (unfold differentiable_def)
  then obtain df where "DERIV f x :> df" ..
  moreover from prems have "\<exists>D. DERIV g x :> D" by (unfold differentiable_def)
  then obtain dg where "DERIV g x :> dg" ..
  ultimately have "DERIV (\<lambda>x. f x + g x) x :> df + dg" by (rule DERIV_add)
  hence "\<exists>D. DERIV (\<lambda>x. f x + g x) x :> D" by auto
  thus ?thesis by (fold differentiable_def)
qed

lemma differentiable_diff:
  assumes "f differentiable x"
  and "g differentiable x"
  shows "(\<lambda>x. f x - g x) differentiable x"
proof -
  from prems have "f differentiable x" by simp
  moreover
  from prems have "\<exists>D. DERIV g x :> D" by (unfold differentiable_def)
  then obtain dg where "DERIV g x :> dg" ..
  then have "DERIV (\<lambda>x. - g x) x :> -dg" by (rule DERIV_minus)
  hence "\<exists>D. DERIV (\<lambda>x. - g x) x :> D" by auto
  hence "(\<lambda>x. - g x) differentiable x" by (fold differentiable_def)
  ultimately 
  show ?thesis
    by (auto simp: real_diff_def dest: differentiable_sum)
qed

lemma differentiable_mult:
  assumes "f differentiable x"
  and "g differentiable x"
  shows "(\<lambda>x. f x * g x) differentiable x"
proof -
  from prems have "\<exists>D. DERIV f x :> D" by (unfold differentiable_def)
  then obtain df where "DERIV f x :> df" ..
  moreover from prems have "\<exists>D. DERIV g x :> D" by (unfold differentiable_def)
  then obtain dg where "DERIV g x :> dg" ..
  ultimately have "DERIV (\<lambda>x. f x * g x) x :> df * g x + dg * f x" by (simp add: DERIV_mult)
  hence "\<exists>D. DERIV (\<lambda>x. f x * g x) x :> D" by auto
  thus ?thesis by (fold differentiable_def)
qed

subsection {*(NS) Increment*}
lemma incrementI:
      "f NSdifferentiable x ==>
      increment f x h = ( *f* f) (hypreal_of_real(x) + h) -
      hypreal_of_real (f x)"
by (simp add: increment_def)

lemma incrementI2: "NSDERIV f x :> D ==>
     increment f x h = ( *f* f) (hypreal_of_real(x) + h) -
     hypreal_of_real (f x)"
apply (erule NSdifferentiableI [THEN incrementI])
done

(* The Increment theorem -- Keisler p. 65 *)
lemma increment_thm: "[| NSDERIV f x :> D; h \<in> Infinitesimal; h \<noteq> 0 |]
      ==> \<exists>e \<in> Infinitesimal. increment f x h = hypreal_of_real(D)*h + e*h"
apply (frule_tac h = h in incrementI2, simp add: nsderiv_def)
apply (drule bspec, auto)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2], clarify)
apply (frule_tac b1 = "hypreal_of_real (D) + y"
        in hypreal_mult_right_cancel [THEN iffD2])
apply (erule_tac [2] V = "(( *f* f) (hypreal_of_real (x) + h) - hypreal_of_real (f x)) / h = hypreal_of_real (D) + y" in thin_rl)
apply assumption
apply (simp add: times_divide_eq_right [symmetric])
apply (auto simp add: left_distrib)
done

lemma increment_thm2:
     "[| NSDERIV f x :> D; h \<approx> 0; h \<noteq> 0 |]
      ==> \<exists>e \<in> Infinitesimal. increment f x h =
              hypreal_of_real(D)*h + e*h"
by (blast dest!: mem_infmal_iff [THEN iffD2] intro!: increment_thm)


lemma increment_approx_zero: "[| NSDERIV f x :> D; h \<approx> 0; h \<noteq> 0 |]
      ==> increment f x h \<approx> 0"
apply (drule increment_thm2,
       auto intro!: Infinitesimal_HFinite_mult2 HFinite_add simp add: left_distrib [symmetric] mem_infmal_iff [symmetric])
apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
done

subsection {* Nested Intervals and Bisection *}

text{*Lemmas about nested intervals and proof by bisection (cf.Harrison).
     All considerably tidied by lcp.*}

lemma lemma_f_mono_add [rule_format (no_asm)]: "(\<forall>n. (f::nat=>real) n \<le> f (Suc n)) --> f m \<le> f(m + no)"
apply (induct "no")
apply (auto intro: order_trans)
done

lemma f_inc_g_dec_Beq_f: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> Bseq (f :: nat \<Rightarrow> real)"
apply (rule_tac k = "f 0" and K = "g 0" in BseqI2, rule allI)
apply (induct_tac "n")
apply (auto intro: order_trans)
apply (rule_tac y = "g (Suc na)" in order_trans)
apply (induct_tac [2] "na")
apply (auto intro: order_trans)
done

lemma f_inc_g_dec_Beq_g: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> Bseq (g :: nat \<Rightarrow> real)"
apply (subst Bseq_minus_iff [symmetric])
apply (rule_tac g = "%x. - (f x)" in f_inc_g_dec_Beq_f)
apply auto
done

lemma f_inc_imp_le_lim:
  fixes f :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<forall>n. f n \<le> f (Suc n); convergent f\<rbrakk> \<Longrightarrow> f n \<le> lim f"
apply (rule linorder_not_less [THEN iffD1])
apply (auto simp add: convergent_LIMSEQ_iff LIMSEQ_iff monoseq_Suc)
apply (drule real_less_sum_gt_zero)
apply (drule_tac x = "f n + - lim f" in spec, safe)
apply (drule_tac P = "%na. no\<le>na --> ?Q na" and x = "no + n" in spec, auto)
apply (subgoal_tac "lim f \<le> f (no + n) ")
apply (drule_tac no=no and m=n in lemma_f_mono_add)
apply (auto simp add: add_commute)
apply (induct_tac "no")
apply simp
apply (auto intro: order_trans simp add: diff_minus abs_if)
done

lemma lim_uminus: "convergent g ==> lim (%x. - g x) = - (lim g)"
apply (rule LIMSEQ_minus [THEN limI])
apply (simp add: convergent_LIMSEQ_iff)
done

lemma g_dec_imp_lim_le:
  fixes g :: "nat \<Rightarrow> real"
  shows "\<lbrakk>\<forall>n. g (Suc n) \<le> g(n); convergent g\<rbrakk> \<Longrightarrow> lim g \<le> g n"
apply (subgoal_tac "- (g n) \<le> - (lim g) ")
apply (cut_tac [2] f = "%x. - (g x)" in f_inc_imp_le_lim)
apply (auto simp add: lim_uminus convergent_minus_iff [symmetric])
done

lemma lemma_nest: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> \<exists>l m :: real. l \<le> m &  ((\<forall>n. f(n) \<le> l) & f ----> l) &
                            ((\<forall>n. m \<le> g(n)) & g ----> m)"
apply (subgoal_tac "monoseq f & monoseq g")
prefer 2 apply (force simp add: LIMSEQ_iff monoseq_Suc)
apply (subgoal_tac "Bseq f & Bseq g")
prefer 2 apply (blast intro: f_inc_g_dec_Beq_f f_inc_g_dec_Beq_g)
apply (auto dest!: Bseq_monoseq_convergent simp add: convergent_LIMSEQ_iff)
apply (rule_tac x = "lim f" in exI)
apply (rule_tac x = "lim g" in exI)
apply (auto intro: LIMSEQ_le)
apply (auto simp add: f_inc_imp_le_lim g_dec_imp_lim_le convergent_LIMSEQ_iff)
done

lemma lemma_nest_unique: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n);
         (%n. f(n) - g(n)) ----> 0 |]
      ==> \<exists>l::real. ((\<forall>n. f(n) \<le> l) & f ----> l) &
                ((\<forall>n. l \<le> g(n)) & g ----> l)"
apply (drule lemma_nest, auto)
apply (subgoal_tac "l = m")
apply (drule_tac [2] X = f in LIMSEQ_diff)
apply (auto intro: LIMSEQ_unique)
done

text{*The universal quantifiers below are required for the declaration
  of @{text Bolzano_nest_unique} below.*}

lemma Bolzano_bisect_le:
 "a \<le> b ==> \<forall>n. fst (Bolzano_bisect P a b n) \<le> snd (Bolzano_bisect P a b n)"
apply (rule allI)
apply (induct_tac "n")
apply (auto simp add: Let_def split_def)
done

lemma Bolzano_bisect_fst_le_Suc: "a \<le> b ==>
   \<forall>n. fst(Bolzano_bisect P a b n) \<le> fst (Bolzano_bisect P a b (Suc n))"
apply (rule allI)
apply (induct_tac "n")
apply (auto simp add: Bolzano_bisect_le Let_def split_def)
done

lemma Bolzano_bisect_Suc_le_snd: "a \<le> b ==>
   \<forall>n. snd(Bolzano_bisect P a b (Suc n)) \<le> snd (Bolzano_bisect P a b n)"
apply (rule allI)
apply (induct_tac "n")
apply (auto simp add: Bolzano_bisect_le Let_def split_def)
done

lemma eq_divide_2_times_iff: "((x::real) = y / (2 * z)) = (2 * x = y/z)"
apply (auto)
apply (drule_tac f = "%u. (1/2) *u" in arg_cong)
apply (simp)
done

lemma Bolzano_bisect_diff:
     "a \<le> b ==>
      snd(Bolzano_bisect P a b n) - fst(Bolzano_bisect P a b n) =
      (b-a) / (2 ^ n)"
apply (induct "n")
apply (auto simp add: eq_divide_2_times_iff add_divide_distrib Let_def split_def)
done

lemmas Bolzano_nest_unique =
    lemma_nest_unique
    [OF Bolzano_bisect_fst_le_Suc Bolzano_bisect_Suc_le_snd Bolzano_bisect_le]


lemma not_P_Bolzano_bisect:
  assumes P:    "!!a b c. [| P(a,b); P(b,c); a \<le> b; b \<le> c|] ==> P(a,c)"
      and notP: "~ P(a,b)"
      and le:   "a \<le> b"
  shows "~ P(fst(Bolzano_bisect P a b n), snd(Bolzano_bisect P a b n))"
proof (induct n)
  case 0 thus ?case by simp
 next
  case (Suc n)
  thus ?case
 by (auto simp del: surjective_pairing [symmetric]
             simp add: Let_def split_def Bolzano_bisect_le [OF le]
     P [of "fst (Bolzano_bisect P a b n)" _ "snd (Bolzano_bisect P a b n)"])
qed

(*Now we re-package P_prem as a formula*)
lemma not_P_Bolzano_bisect':
     "[| \<forall>a b c. P(a,b) & P(b,c) & a \<le> b & b \<le> c --> P(a,c);
         ~ P(a,b);  a \<le> b |] ==>
      \<forall>n. ~ P(fst(Bolzano_bisect P a b n), snd(Bolzano_bisect P a b n))"
by (blast elim!: not_P_Bolzano_bisect [THEN [2] rev_notE])



lemma lemma_BOLZANO:
     "[| \<forall>a b c. P(a,b) & P(b,c) & a \<le> b & b \<le> c --> P(a,c);
         \<forall>x. \<exists>d::real. 0 < d &
                (\<forall>a b. a \<le> x & x \<le> b & (b-a) < d --> P(a,b));
         a \<le> b |]
      ==> P(a,b)"
apply (rule Bolzano_nest_unique [where P1=P, THEN exE], assumption+)
apply (rule LIMSEQ_minus_cancel)
apply (simp (no_asm_simp) add: Bolzano_bisect_diff LIMSEQ_divide_realpow_zero)
apply (rule ccontr)
apply (drule not_P_Bolzano_bisect', assumption+)
apply (rename_tac "l")
apply (drule_tac x = l in spec, clarify)
apply (simp add: LIMSEQ_def)
apply (drule_tac P = "%r. 0<r --> ?Q r" and x = "d/2" in spec)
apply (drule_tac P = "%r. 0<r --> ?Q r" and x = "d/2" in spec)
apply (drule real_less_half_sum, auto)
apply (drule_tac x = "fst (Bolzano_bisect P a b (no + noa))" in spec)
apply (drule_tac x = "snd (Bolzano_bisect P a b (no + noa))" in spec)
apply safe
apply (simp_all (no_asm_simp))
apply (rule_tac y = "abs (fst (Bolzano_bisect P a b (no + noa)) - l) + abs (snd (Bolzano_bisect P a b (no + noa)) - l)" in order_le_less_trans)
apply (simp (no_asm_simp) add: abs_if)
apply (rule real_sum_of_halves [THEN subst])
apply (rule add_strict_mono)
apply (simp_all add: diff_minus [symmetric])
done


lemma lemma_BOLZANO2: "((\<forall>a b c. (a \<le> b & b \<le> c & P(a,b) & P(b,c)) --> P(a,c)) &
       (\<forall>x. \<exists>d::real. 0 < d &
                (\<forall>a b. a \<le> x & x \<le> b & (b-a) < d --> P(a,b))))
      --> (\<forall>a b. a \<le> b --> P(a,b))"
apply clarify
apply (blast intro: lemma_BOLZANO)
done


subsection {* Intermediate Value Theorem *}

text {*Prove Contrapositive by Bisection*}

lemma IVT: "[| f(a::real) \<le> (y::real); y \<le> f(b);
         a \<le> b;
         (\<forall>x. a \<le> x & x \<le> b --> isCont f x) |]
      ==> \<exists>x. a \<le> x & x \<le> b & f(x) = y"
apply (rule contrapos_pp, assumption)
apply (cut_tac P = "% (u,v) . a \<le> u & u \<le> v & v \<le> b --> ~ (f (u) \<le> y & y \<le> f (v))" in lemma_BOLZANO2)
apply safe
apply simp_all
apply (simp add: isCont_iff LIM_def)
apply (rule ccontr)
apply (subgoal_tac "a \<le> x & x \<le> b")
 prefer 2
 apply simp
 apply (drule_tac P = "%d. 0<d --> ?P d" and x = 1 in spec, arith)
apply (drule_tac x = x in spec)+
apply simp
apply (drule_tac P = "%r. ?P r --> (\<exists>s>0. ?Q r s) " and x = "\<bar>y - f x\<bar>" in spec)
apply safe
apply simp
apply (drule_tac x = s in spec, clarify)
apply (cut_tac x = "f x" and y = y in linorder_less_linear, safe)
apply (drule_tac x = "ba-x" in spec)
apply (simp_all add: abs_if)
apply (drule_tac x = "aa-x" in spec)
apply (case_tac "x \<le> aa", simp_all)
done

lemma IVT2: "[| f(b::real) \<le> (y::real); y \<le> f(a);
         a \<le> b;
         (\<forall>x. a \<le> x & x \<le> b --> isCont f x)
      |] ==> \<exists>x. a \<le> x & x \<le> b & f(x) = y"
apply (subgoal_tac "- f a \<le> -y & -y \<le> - f b", clarify)
apply (drule IVT [where f = "%x. - f x"], assumption)
apply (auto intro: isCont_minus)
done

(*HOL style here: object-level formulations*)
lemma IVT_objl: "(f(a::real) \<le> (y::real) & y \<le> f(b) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
apply (blast intro: IVT)
done

lemma IVT2_objl: "(f(b::real) \<le> (y::real) & y \<le> f(a) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
apply (blast intro: IVT2)
done

text{*By bisection, function continuous on closed interval is bounded above*}

lemma isCont_bounded:
     "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
      ==> \<exists>M::real. \<forall>x::real. a \<le> x & x \<le> b --> f(x) \<le> M"
apply (cut_tac P = "% (u,v) . a \<le> u & u \<le> v & v \<le> b --> (\<exists>M. \<forall>x. u \<le> x & x \<le> v --> f x \<le> M)" in lemma_BOLZANO2)
apply safe
apply simp_all
apply (rename_tac x xa ya M Ma)
apply (cut_tac x = M and y = Ma in linorder_linear, safe)
apply (rule_tac x = Ma in exI, clarify)
apply (cut_tac x = xb and y = xa in linorder_linear, force)
apply (rule_tac x = M in exI, clarify)
apply (cut_tac x = xb and y = xa in linorder_linear, force)
apply (case_tac "a \<le> x & x \<le> b")
apply (rule_tac [2] x = 1 in exI)
prefer 2 apply force
apply (simp add: LIM_def isCont_iff)
apply (drule_tac x = x in spec, auto)
apply (erule_tac V = "\<forall>M. \<exists>x. a \<le> x & x \<le> b & ~ f x \<le> M" in thin_rl)
apply (drule_tac x = 1 in spec, auto)
apply (rule_tac x = s in exI, clarify)
apply (rule_tac x = "\<bar>f x\<bar> + 1" in exI, clarify)
apply (drule_tac x = "xa-x" in spec)
apply (auto simp add: abs_ge_self)
done

text{*Refine the above to existence of least upper bound*}

lemma lemma_reals_complete: "((\<exists>x. x \<in> S) & (\<exists>y. isUb UNIV S (y::real))) -->
      (\<exists>t. isLub UNIV S t)"
by (blast intro: reals_complete)

lemma isCont_has_Ub: "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
         ==> \<exists>M::real. (\<forall>x::real. a \<le> x & x \<le> b --> f(x) \<le> M) &
                   (\<forall>N. N < M --> (\<exists>x. a \<le> x & x \<le> b & N < f(x)))"
apply (cut_tac S = "Collect (%y. \<exists>x. a \<le> x & x \<le> b & y = f x)"
        in lemma_reals_complete)
apply auto
apply (drule isCont_bounded, assumption)
apply (auto simp add: isUb_def leastP_def isLub_def setge_def setle_def)
apply (rule exI, auto)
apply (auto dest!: spec simp add: linorder_not_less)
done

text{*Now show that it attains its upper bound*}

lemma isCont_eq_Ub:
  assumes le: "a \<le> b"
      and con: "\<forall>x::real. a \<le> x & x \<le> b --> isCont f x"
  shows "\<exists>M::real. (\<forall>x. a \<le> x & x \<le> b --> f(x) \<le> M) &
             (\<exists>x. a \<le> x & x \<le> b & f(x) = M)"
proof -
  from isCont_has_Ub [OF le con]
  obtain M where M1: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M"
             and M2: "!!N. N<M ==> \<exists>x. a \<le> x \<and> x \<le> b \<and> N < f x"  by blast
  show ?thesis
  proof (intro exI, intro conjI)
    show " \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M" by (rule M1)
    show "\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M"
    proof (rule ccontr)
      assume "\<not> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
      with M1 have M3: "\<forall>x. a \<le> x & x \<le> b --> f x < M"
        by (fastsimp simp add: linorder_not_le [symmetric])
      hence "\<forall>x. a \<le> x & x \<le> b --> isCont (%x. inverse (M - f x)) x"
        by (auto simp add: isCont_inverse isCont_diff con)
      from isCont_bounded [OF le this]
      obtain k where k: "!!x. a \<le> x & x \<le> b --> inverse (M - f x) \<le> k" by auto
      have Minv: "!!x. a \<le> x & x \<le> b --> 0 < inverse (M - f (x))"
        by (simp add: M3 compare_rls)
      have "!!x. a \<le> x & x \<le> b --> inverse (M - f x) < k+1" using k
        by (auto intro: order_le_less_trans [of _ k])
      with Minv
      have "!!x. a \<le> x & x \<le> b --> inverse(k+1) < inverse(inverse(M - f x))"
        by (intro strip less_imp_inverse_less, simp_all)
      hence invlt: "!!x. a \<le> x & x \<le> b --> inverse(k+1) < M - f x"
        by simp
      have "M - inverse (k+1) < M" using k [of a] Minv [of a] le
        by (simp, arith)
      from M2 [OF this]
      obtain x where ax: "a \<le> x & x \<le> b & M - inverse(k+1) < f x" ..
      thus False using invlt [of x] by force
    qed
  qed
qed


text{*Same theorem for lower bound*}

lemma isCont_eq_Lb: "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
         ==> \<exists>M::real. (\<forall>x::real. a \<le> x & x \<le> b --> M \<le> f(x)) &
                   (\<exists>x. a \<le> x & x \<le> b & f(x) = M)"
apply (subgoal_tac "\<forall>x. a \<le> x & x \<le> b --> isCont (%x. - (f x)) x")
prefer 2 apply (blast intro: isCont_minus)
apply (drule_tac f = "(%x. - (f x))" in isCont_eq_Ub)
apply safe
apply auto
done


text{*Another version.*}

lemma isCont_Lb_Ub: "[|a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
      ==> \<exists>L M::real. (\<forall>x::real. a \<le> x & x \<le> b --> L \<le> f(x) & f(x) \<le> M) &
          (\<forall>y. L \<le> y & y \<le> M --> (\<exists>x. a \<le> x & x \<le> b & (f(x) = y)))"
apply (frule isCont_eq_Lb)
apply (frule_tac [2] isCont_eq_Ub)
apply (assumption+, safe)
apply (rule_tac x = "f x" in exI)
apply (rule_tac x = "f xa" in exI, simp, safe)
apply (cut_tac x = x and y = xa in linorder_linear, safe)
apply (cut_tac f = f and a = x and b = xa and y = y in IVT_objl)
apply (cut_tac [2] f = f and a = xa and b = x and y = y in IVT2_objl, safe)
apply (rule_tac [2] x = xb in exI)
apply (rule_tac [4] x = xb in exI, simp_all)
done


text{*If @{term "0 < f'(x)"} then @{term x} is Locally Strictly Increasing At The Right*}

lemma DERIV_left_inc:
  fixes f :: "real => real"
  assumes der: "DERIV f x :> l"
      and l:   "0 < l"
  shows "\<exists>d > 0. \<forall>h > 0. h < d --> f(x) < f(x + h)"
proof -
  from l der [THEN DERIV_D, THEN LIM_D [where r = "l"]]
  have "\<exists>s > 0. (\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < l)"
    by (simp add: diff_minus)
  then obtain s
        where s:   "0 < s"
          and all: "!!z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < l"
    by auto
  thus ?thesis
  proof (intro exI conjI strip)
    show "0<s" .
    fix h::real
    assume "0 < h" "h < s"
    with all [of h] show "f x < f (x+h)"
    proof (simp add: abs_if pos_less_divide_eq diff_minus [symmetric]
    split add: split_if_asm)
      assume "~ (f (x+h) - f x) / h < l" and h: "0 < h"
      with l
      have "0 < (f (x+h) - f x) / h" by arith
      thus "f x < f (x+h)"
  by (simp add: pos_less_divide_eq h)
    qed
  qed
qed

lemma DERIV_left_dec:
  fixes f :: "real => real"
  assumes der: "DERIV f x :> l"
      and l:   "l < 0"
  shows "\<exists>d > 0. \<forall>h > 0. h < d --> f(x) < f(x-h)"
proof -
  from l der [THEN DERIV_D, THEN LIM_D [where r = "-l"]]
  have "\<exists>s > 0. (\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < -l)"
    by (simp add: diff_minus)
  then obtain s
        where s:   "0 < s"
          and all: "!!z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < -l"
    by auto
  thus ?thesis
  proof (intro exI conjI strip)
    show "0<s" .
    fix h::real
    assume "0 < h" "h < s"
    with all [of "-h"] show "f x < f (x-h)"
    proof (simp add: abs_if pos_less_divide_eq diff_minus [symmetric]
    split add: split_if_asm)
      assume " - ((f (x-h) - f x) / h) < l" and h: "0 < h"
      with l
      have "0 < (f (x-h) - f x) / h" by arith
      thus "f x < f (x-h)"
  by (simp add: pos_less_divide_eq h)
    qed
  qed
qed

lemma DERIV_local_max:
  fixes f :: "real => real"
  assumes der: "DERIV f x :> l"
      and d:   "0 < d"
      and le:  "\<forall>y. \<bar>x-y\<bar> < d --> f(y) \<le> f(x)"
  shows "l = 0"
proof (cases rule: linorder_cases [of l 0])
  case equal show ?thesis .
next
  case less
  from DERIV_left_dec [OF der less]
  obtain d' where d': "0 < d'"
             and lt: "\<forall>h > 0. h < d' \<longrightarrow> f x < f (x-h)" by blast
  from real_lbound_gt_zero [OF d d']
  obtain e where "0 < e \<and> e < d \<and> e < d'" ..
  with lt le [THEN spec [where x="x-e"]]
  show ?thesis by (auto simp add: abs_if)
next
  case greater
  from DERIV_left_inc [OF der greater]
  obtain d' where d': "0 < d'"
             and lt: "\<forall>h > 0. h < d' \<longrightarrow> f x < f (x + h)" by blast
  from real_lbound_gt_zero [OF d d']
  obtain e where "0 < e \<and> e < d \<and> e < d'" ..
  with lt le [THEN spec [where x="x+e"]]
  show ?thesis by (auto simp add: abs_if)
qed


text{*Similar theorem for a local minimum*}
lemma DERIV_local_min:
  fixes f :: "real => real"
  shows "[| DERIV f x :> l; 0 < d; \<forall>y. \<bar>x-y\<bar> < d --> f(x) \<le> f(y) |] ==> l = 0"
by (drule DERIV_minus [THEN DERIV_local_max], auto)


text{*In particular, if a function is locally flat*}
lemma DERIV_local_const:
  fixes f :: "real => real"
  shows "[| DERIV f x :> l; 0 < d; \<forall>y. \<bar>x-y\<bar> < d --> f(x) = f(y) |] ==> l = 0"
by (auto dest!: DERIV_local_max)

text{*Lemma about introducing open ball in open interval*}
lemma lemma_interval_lt:
     "[| a < x;  x < b |]
      ==> \<exists>d::real. 0 < d & (\<forall>y. \<bar>x-y\<bar> < d --> a < y & y < b)"
apply (simp add: abs_interval_iff)
apply (insert linorder_linear [of "x-a" "b-x"], safe)
apply (rule_tac x = "x-a" in exI)
apply (rule_tac [2] x = "b-x" in exI, auto)
done

lemma lemma_interval: "[| a < x;  x < b |] ==>
        \<exists>d::real. 0 < d &  (\<forall>y. \<bar>x-y\<bar> < d --> a \<le> y & y \<le> b)"
apply (drule lemma_interval_lt, auto)
apply (auto intro!: exI)
done

text{*Rolle's Theorem.
   If @{term f} is defined and continuous on the closed interval
   @{text "[a,b]"} and differentiable on the open interval @{text "(a,b)"},
   and @{term "f(a) = f(b)"},
   then there exists @{text "x0 \<in> (a,b)"} such that @{term "f'(x0) = 0"}*}
theorem Rolle:
  assumes lt: "a < b"
      and eq: "f(a) = f(b)"
      and con: "\<forall>x. a \<le> x & x \<le> b --> isCont f x"
      and dif [rule_format]: "\<forall>x. a < x & x < b --> f differentiable x"
  shows "\<exists>z. a < z & z < b & DERIV f z :> 0"
proof -
  have le: "a \<le> b" using lt by simp
  from isCont_eq_Ub [OF le con]
  obtain x where x_max: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> f z \<le> f x"
             and alex: "a \<le> x" and xleb: "x \<le> b"
    by blast
  from isCont_eq_Lb [OF le con]
  obtain x' where x'_min: "\<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> f x' \<le> f z"
              and alex': "a \<le> x'" and x'leb: "x' \<le> b"
    by blast
  show ?thesis
  proof cases
    assume axb: "a < x & x < b"
        --{*@{term f} attains its maximum within the interval*}
    hence ax: "a<x" and xb: "x<b" by auto
    from lemma_interval [OF ax xb]
    obtain d where d: "0<d" and bound: "\<forall>y. \<bar>x-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
      by blast
    hence bound': "\<forall>y. \<bar>x-y\<bar> < d \<longrightarrow> f y \<le> f x" using x_max
      by blast
    from differentiableD [OF dif [OF axb]]
    obtain l where der: "DERIV f x :> l" ..
    have "l=0" by (rule DERIV_local_max [OF der d bound'])
        --{*the derivative at a local maximum is zero*}
    thus ?thesis using ax xb der by auto
  next
    assume notaxb: "~ (a < x & x < b)"
    hence xeqab: "x=a | x=b" using alex xleb by arith
    hence fb_eq_fx: "f b = f x" by (auto simp add: eq)
    show ?thesis
    proof cases
      assume ax'b: "a < x' & x' < b"
        --{*@{term f} attains its minimum within the interval*}
      hence ax': "a<x'" and x'b: "x'<b" by auto
      from lemma_interval [OF ax' x'b]
      obtain d where d: "0<d" and bound: "\<forall>y. \<bar>x'-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
  by blast
      hence bound': "\<forall>y. \<bar>x'-y\<bar> < d \<longrightarrow> f x' \<le> f y" using x'_min
  by blast
      from differentiableD [OF dif [OF ax'b]]
      obtain l where der: "DERIV f x' :> l" ..
      have "l=0" by (rule DERIV_local_min [OF der d bound'])
        --{*the derivative at a local minimum is zero*}
      thus ?thesis using ax' x'b der by auto
    next
      assume notax'b: "~ (a < x' & x' < b)"
        --{*@{term f} is constant througout the interval*}
      hence x'eqab: "x'=a | x'=b" using alex' x'leb by arith
      hence fb_eq_fx': "f b = f x'" by (auto simp add: eq)
      from dense [OF lt]
      obtain r where ar: "a < r" and rb: "r < b" by blast
      from lemma_interval [OF ar rb]
      obtain d where d: "0<d" and bound: "\<forall>y. \<bar>r-y\<bar> < d \<longrightarrow> a \<le> y \<and> y \<le> b"
  by blast
      have eq_fb: "\<forall>z. a \<le> z --> z \<le> b --> f z = f b"
      proof (clarify)
        fix z::real
        assume az: "a \<le> z" and zb: "z \<le> b"
        show "f z = f b"
        proof (rule order_antisym)
          show "f z \<le> f b" by (simp add: fb_eq_fx x_max az zb)
          show "f b \<le> f z" by (simp add: fb_eq_fx' x'_min az zb)
        qed
      qed
      have bound': "\<forall>y. \<bar>r-y\<bar> < d \<longrightarrow> f r = f y"
      proof (intro strip)
        fix y::real
        assume lt: "\<bar>r-y\<bar> < d"
        hence "f y = f b" by (simp add: eq_fb bound)
        thus "f r = f y" by (simp add: eq_fb ar rb order_less_imp_le)
      qed
      from differentiableD [OF dif [OF conjI [OF ar rb]]]
      obtain l where der: "DERIV f r :> l" ..
      have "l=0" by (rule DERIV_local_const [OF der d bound'])
        --{*the derivative of a constant function is zero*}
      thus ?thesis using ar rb der by auto
    qed
  qed
qed


subsection{*Mean Value Theorem*}

lemma lemma_MVT:
     "f a - (f b - f a)/(b-a) * a = f b - (f b - f a)/(b-a) * (b::real)"
proof cases
  assume "a=b" thus ?thesis by simp
next
  assume "a\<noteq>b"
  hence ba: "b-a \<noteq> 0" by arith
  show ?thesis
    by (rule real_mult_left_cancel [OF ba, THEN iffD1],
        simp add: right_diff_distrib,
        simp add: left_diff_distrib)
qed

theorem MVT:
  assumes lt:  "a < b"
      and con: "\<forall>x. a \<le> x & x \<le> b --> isCont f x"
      and dif [rule_format]: "\<forall>x. a < x & x < b --> f differentiable x"
  shows "\<exists>l z. a < z & z < b & DERIV f z :> l &
                   (f(b) - f(a) = (b-a) * l)"
proof -
  let ?F = "%x. f x - ((f b - f a) / (b-a)) * x"
  have contF: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont ?F x" using con
    by (fast intro: isCont_diff isCont_const isCont_mult isCont_Id)
  have difF: "\<forall>x. a < x \<and> x < b \<longrightarrow> ?F differentiable x"
  proof (clarify)
    fix x::real
    assume ax: "a < x" and xb: "x < b"
    from differentiableD [OF dif [OF conjI [OF ax xb]]]
    obtain l where der: "DERIV f x :> l" ..
    show "?F differentiable x"
      by (rule differentiableI [where D = "l - (f b - f a)/(b-a)"],
          blast intro: DERIV_diff DERIV_cmult_Id der)
  qed
  from Rolle [where f = ?F, OF lt lemma_MVT contF difF]
  obtain z where az: "a < z" and zb: "z < b" and der: "DERIV ?F z :> 0"
    by blast
  have "DERIV (%x. ((f b - f a)/(b-a)) * x) z :> (f b - f a)/(b-a)"
    by (rule DERIV_cmult_Id)
  hence derF: "DERIV (\<lambda>x. ?F x + (f b - f a) / (b - a) * x) z
                   :> 0 + (f b - f a) / (b - a)"
    by (rule DERIV_add [OF der])
  show ?thesis
  proof (intro exI conjI)
    show "a < z" .
    show "z < b" .
    show "f b - f a = (b - a) * ((f b - f a)/(b-a))" by (simp)
    show "DERIV f z :> ((f b - f a)/(b-a))"  using derF by simp
  qed
qed


text{*A function is constant if its derivative is 0 over an interval.*}

lemma DERIV_isconst_end:
  fixes f :: "real => real"
  shows "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0 |]
        ==> f b = f a"
apply (drule MVT, assumption)
apply (blast intro: differentiableI)
apply (auto dest!: DERIV_unique simp add: diff_eq_eq)
done

lemma DERIV_isconst1:
  fixes f :: "real => real"
  shows "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0 |]
        ==> \<forall>x. a \<le> x & x \<le> b --> f x = f a"
apply safe
apply (drule_tac x = a in order_le_imp_less_or_eq, safe)
apply (drule_tac b = x in DERIV_isconst_end, auto)
done

lemma DERIV_isconst2:
  fixes f :: "real => real"
  shows "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0;
         a \<le> x; x \<le> b |]
        ==> f x = f a"
apply (blast dest: DERIV_isconst1)
done

lemma DERIV_isconst_all:
  fixes f :: "real => real"
  shows "\<forall>x. DERIV f x :> 0 ==> f(x) = f(y)"
apply (rule linorder_cases [of x y])
apply (blast intro: sym DERIV_isCont DERIV_isconst_end)+
done

lemma DERIV_const_ratio_const:
     "[|a \<noteq> b; \<forall>x. DERIV f x :> k |] ==> (f(b) - f(a)) = (b-a) * k"
apply (rule linorder_cases [of a b], auto)
apply (drule_tac [!] f = f in MVT)
apply (auto dest: DERIV_isCont DERIV_unique simp add: differentiable_def)
apply (auto dest: DERIV_unique simp add: left_distrib diff_minus)
done

lemma DERIV_const_ratio_const2:
     "[|a \<noteq> b; \<forall>x. DERIV f x :> k |] ==> (f(b) - f(a))/(b-a) = k"
apply (rule_tac c1 = "b-a" in real_mult_right_cancel [THEN iffD1])
apply (auto dest!: DERIV_const_ratio_const simp add: mult_assoc)
done

lemma real_average_minus_first [simp]: "((a + b) /2 - a) = (b-a)/(2::real)"
by (simp)

lemma real_average_minus_second [simp]: "((b + a)/2 - a) = (b-a)/(2::real)"
by (simp)

text{*Gallileo's "trick": average velocity = av. of end velocities*}

lemma DERIV_const_average:
  fixes v :: "real => real"
  assumes neq: "a \<noteq> (b::real)"
      and der: "\<forall>x. DERIV v x :> k"
  shows "v ((a + b)/2) = (v a + v b)/2"
proof (cases rule: linorder_cases [of a b])
  case equal with neq show ?thesis by simp
next
  case less
  have "(v b - v a) / (b - a) = k"
    by (rule DERIV_const_ratio_const2 [OF neq der])
  hence "(b-a) * ((v b - v a) / (b-a)) = (b-a) * k" by simp
  moreover have "(v ((a + b) / 2) - v a) / ((a + b) / 2 - a) = k"
    by (rule DERIV_const_ratio_const2 [OF _ der], simp add: neq)
  ultimately show ?thesis using neq by force
next
  case greater
  have "(v b - v a) / (b - a) = k"
    by (rule DERIV_const_ratio_const2 [OF neq der])
  hence "(b-a) * ((v b - v a) / (b-a)) = (b-a) * k" by simp
  moreover have " (v ((b + a) / 2) - v a) / ((b + a) / 2 - a) = k"
    by (rule DERIV_const_ratio_const2 [OF _ der], simp add: neq)
  ultimately show ?thesis using neq by (force simp add: add_commute)
qed


text{*Dull lemma: an continuous injection on an interval must have a
strict maximum at an end point, not in the middle.*}

lemma lemma_isCont_inj:
  fixes f :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj [rule_format]: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "\<exists>z. \<bar>z-x\<bar> \<le> d & f x < f z"
proof (rule ccontr)
  assume  "~ (\<exists>z. \<bar>z-x\<bar> \<le> d & f x < f z)"
  hence all [rule_format]: "\<forall>z. \<bar>z - x\<bar> \<le> d --> f z \<le> f x" by auto
  show False
  proof (cases rule: linorder_le_cases [of "f(x-d)" "f(x+d)"])
    case le
    from d cont all [of "x+d"]
    have flef: "f(x+d) \<le> f x"
     and xlex: "x - d \<le> x"
     and cont': "\<forall>z. x - d \<le> z \<and> z \<le> x \<longrightarrow> isCont f z"
       by (auto simp add: abs_if)
    from IVT [OF le flef xlex cont']
    obtain x' where "x-d \<le> x'" "x' \<le> x" "f x' = f(x+d)" by blast
    moreover
    hence "g(f x') = g (f(x+d))" by simp
    ultimately show False using d inj [of x'] inj [of "x+d"]
      by (simp add: abs_le_interval_iff)
  next
    case ge
    from d cont all [of "x-d"]
    have flef: "f(x-d) \<le> f x"
     and xlex: "x \<le> x+d"
     and cont': "\<forall>z. x \<le> z \<and> z \<le> x+d \<longrightarrow> isCont f z"
       by (auto simp add: abs_if)
    from IVT2 [OF ge flef xlex cont']
    obtain x' where "x \<le> x'" "x' \<le> x+d" "f x' = f(x-d)" by blast
    moreover
    hence "g(f x') = g (f(x-d))" by simp
    ultimately show False using d inj [of x'] inj [of "x-d"]
      by (simp add: abs_le_interval_iff)
  qed
qed


text{*Similar version for lower bound.*}

lemma lemma_isCont_inj2:
  fixes f g :: "real \<Rightarrow> real"
  shows "[|0 < d; \<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z;
        \<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z |]
      ==> \<exists>z. \<bar>z-x\<bar> \<le> d & f z < f x"
apply (insert lemma_isCont_inj
          [where f = "%x. - f x" and g = "%y. g(-y)" and x = x and d = d])
apply (simp add: isCont_minus linorder_not_le)
done

text{*Show there's an interval surrounding @{term "f(x)"} in
@{text "f[[x - d, x + d]]"} .*}

lemma isCont_inj_range:
  fixes f :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "\<exists>e>0. \<forall>y. \<bar>y - f x\<bar> \<le> e --> (\<exists>z. \<bar>z-x\<bar> \<le> d & f z = y)"
proof -
  have "x-d \<le> x+d" "\<forall>z. x-d \<le> z \<and> z \<le> x+d \<longrightarrow> isCont f z" using cont d
    by (auto simp add: abs_le_interval_iff)
  from isCont_Lb_Ub [OF this]
  obtain L M
  where all1 [rule_format]: "\<forall>z. x-d \<le> z \<and> z \<le> x+d \<longrightarrow> L \<le> f z \<and> f z \<le> M"
    and all2 [rule_format]:
           "\<forall>y. L \<le> y \<and> y \<le> M \<longrightarrow> (\<exists>z. x-d \<le> z \<and> z \<le> x+d \<and> f z = y)"
    by auto
  with d have "L \<le> f x & f x \<le> M" by simp
  moreover have "L \<noteq> f x"
  proof -
    from lemma_isCont_inj2 [OF d inj cont]
    obtain u where "\<bar>u - x\<bar> \<le> d" "f u < f x"  by auto
    thus ?thesis using all1 [of u] by arith
  qed
  moreover have "f x \<noteq> M"
  proof -
    from lemma_isCont_inj [OF d inj cont]
    obtain u where "\<bar>u - x\<bar> \<le> d" "f x < f u"  by auto
    thus ?thesis using all1 [of u] by arith
  qed
  ultimately have "L < f x & f x < M" by arith
  hence "0 < f x - L" "0 < M - f x" by arith+
  from real_lbound_gt_zero [OF this]
  obtain e where e: "0 < e" "e < f x - L" "e < M - f x" by auto
  thus ?thesis
  proof (intro exI conjI)
    show "0<e" .
    show "\<forall>y. \<bar>y - f x\<bar> \<le> e \<longrightarrow> (\<exists>z. \<bar>z - x\<bar> \<le> d \<and> f z = y)"
    proof (intro strip)
      fix y::real
      assume "\<bar>y - f x\<bar> \<le> e"
      with e have "L \<le> y \<and> y \<le> M" by arith
      from all2 [OF this]
      obtain z where "x - d \<le> z" "z \<le> x + d" "f z = y" by blast
      thus "\<exists>z. \<bar>z - x\<bar> \<le> d \<and> f z = y"
        by (force simp add: abs_le_interval_iff)
    qed
  qed
qed


text{*Continuity of inverse function*}

lemma isCont_inverse_function:
  fixes f g :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "isCont g (f x)"
proof (simp add: isCont_iff LIM_eq)
  show "\<forall>r. 0 < r \<longrightarrow>
         (\<exists>s>0. \<forall>z. z\<noteq>0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>g(f x + z) - g(f x)\<bar> < r)"
  proof (intro strip)
    fix r::real
    assume r: "0<r"
    from real_lbound_gt_zero [OF r d]
    obtain e where e: "0 < e" and e_lt: "e < r \<and> e < d" by blast
    with inj cont
    have e_simps: "\<forall>z. \<bar>z-x\<bar> \<le> e --> g (f z) = z"
                  "\<forall>z. \<bar>z-x\<bar> \<le> e --> isCont f z"   by auto
    from isCont_inj_range [OF e this]
    obtain e' where e': "0 < e'"
        and all: "\<forall>y. \<bar>y - f x\<bar> \<le> e' \<longrightarrow> (\<exists>z. \<bar>z - x\<bar> \<le> e \<and> f z = y)"
          by blast
    show "\<exists>s>0. \<forall>z. z\<noteq>0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>g(f x + z) - g(f x)\<bar> < r"
    proof (intro exI conjI)
      show "0<e'" .
      show "\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < e' \<longrightarrow> \<bar>g (f x + z) - g (f x)\<bar> < r"
      proof (intro strip)
        fix z::real
        assume z: "z \<noteq> 0 \<and> \<bar>z\<bar> < e'"
        with e e_lt e_simps all [rule_format, of "f x + z"]
        show "\<bar>g (f x + z) - g (f x)\<bar> < r" by force
      qed
    qed
  qed
qed

theorem GMVT:
  assumes alb: "a < b"
  and fc: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
  and fd: "\<forall>x. a < x \<and> x < b \<longrightarrow> f differentiable x"
  and gc: "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont g x"
  and gd: "\<forall>x. a < x \<and> x < b \<longrightarrow> g differentiable x"
  shows "\<exists>g'c f'c c. DERIV g c :> g'c \<and> DERIV f c :> f'c \<and> a < c \<and> c < b \<and> ((f b - f a) * g'c) = ((g b - g a) * f'c)"
proof -
  let ?h = "\<lambda>x. (f b - f a)*(g x) - (g b - g a)*(f x)"
  from prems have "a < b" by simp
  moreover have "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont ?h x"
  proof -
    have "\<forall>x. a <= x \<and> x <= b \<longrightarrow> isCont (\<lambda>x. f b - f a) x" by simp
    with gc have "\<forall>x. a <= x \<and> x <= b \<longrightarrow> isCont (\<lambda>x. (f b - f a) * g x) x"
      by (auto intro: isCont_mult)
    moreover
    have "\<forall>x. a <= x \<and> x <= b \<longrightarrow> isCont (\<lambda>x. g b - g a) x" by simp
    with fc have "\<forall>x. a <= x \<and> x <= b \<longrightarrow> isCont (\<lambda>x. (g b - g a) * f x) x"
      by (auto intro: isCont_mult)
    ultimately show ?thesis
      by (fastsimp intro: isCont_diff)
  qed
  moreover
  have "\<forall>x. a < x \<and> x < b \<longrightarrow> ?h differentiable x"
  proof -
    have "\<forall>x. a < x \<and> x < b \<longrightarrow> (\<lambda>x. f b - f a) differentiable x" by (simp add: differentiable_const)
    with gd have "\<forall>x. a < x \<and> x < b \<longrightarrow> (\<lambda>x. (f b - f a) * g x) differentiable x" by (simp add: differentiable_mult)
    moreover
    have "\<forall>x. a < x \<and> x < b \<longrightarrow> (\<lambda>x. g b - g a) differentiable x" by (simp add: differentiable_const)
    with fd have "\<forall>x. a < x \<and> x < b \<longrightarrow> (\<lambda>x. (g b - g a) * f x) differentiable x" by (simp add: differentiable_mult)
    ultimately show ?thesis by (simp add: differentiable_diff)
  qed
  ultimately have "\<exists>l z. a < z \<and> z < b \<and> DERIV ?h z :> l \<and> ?h b - ?h a = (b - a) * l" by (rule MVT)
  then obtain l where ldef: "\<exists>z. a < z \<and> z < b \<and> DERIV ?h z :> l \<and> ?h b - ?h a = (b - a) * l" ..
  then obtain c where cdef: "a < c \<and> c < b \<and> DERIV ?h c :> l \<and> ?h b - ?h a = (b - a) * l" ..

  from cdef have cint: "a < c \<and> c < b" by auto
  with gd have "g differentiable c" by simp
  hence "\<exists>D. DERIV g c :> D" by (rule differentiableD)
  then obtain g'c where g'cdef: "DERIV g c :> g'c" ..

  from cdef have "a < c \<and> c < b" by auto
  with fd have "f differentiable c" by simp
  hence "\<exists>D. DERIV f c :> D" by (rule differentiableD)
  then obtain f'c where f'cdef: "DERIV f c :> f'c" ..

  from cdef have "DERIV ?h c :> l" by auto
  moreover
  {
    from g'cdef have "DERIV (\<lambda>x. (f b - f a) * g x) c :> g'c * (f b - f a)"
      apply (insert DERIV_const [where k="f b - f a"])
      apply (drule meta_spec [of _ c])
      apply (drule DERIV_mult [where f="(\<lambda>x. f b - f a)" and g=g])
      by simp_all
    moreover from f'cdef have "DERIV (\<lambda>x. (g b - g a) * f x) c :> f'c * (g b - g a)"
      apply (insert DERIV_const [where k="g b - g a"])
      apply (drule meta_spec [of _ c])
      apply (drule DERIV_mult [where f="(\<lambda>x. g b - g a)" and g=f])
      by simp_all
    ultimately have "DERIV ?h c :>  g'c * (f b - f a) - f'c * (g b - g a)"
      by (simp add: DERIV_diff)
  }
  ultimately have leq: "l =  g'c * (f b - f a) - f'c * (g b - g a)" by (rule DERIV_unique)

  {
    from cdef have "?h b - ?h a = (b - a) * l" by auto
    also with leq have "\<dots> = (b - a) * (g'c * (f b - f a) - f'c * (g b - g a))" by simp
    finally have "?h b - ?h a = (b - a) * (g'c * (f b - f a) - f'c * (g b - g a))" by simp
  }
  moreover
  {
    have "?h b - ?h a =
         ((f b)*(g b) - (f a)*(g b) - (g b)*(f b) + (g a)*(f b)) -
          ((f b)*(g a) - (f a)*(g a) - (g b)*(f a) + (g a)*(f a))"
      by (simp add: mult_ac add_ac real_diff_mult_distrib)
    hence "?h b - ?h a = 0" by auto
  }
  ultimately have "(b - a) * (g'c * (f b - f a) - f'c * (g b - g a)) = 0" by auto
  with alb have "g'c * (f b - f a) - f'c * (g b - g a) = 0" by simp
  hence "g'c * (f b - f a) = f'c * (g b - g a)" by simp
  hence "(f b - f a) * g'c = (g b - g a) * f'c" by (simp add: mult_ac)

  with g'cdef f'cdef cint show ?thesis by auto
qed


lemma LIMSEQ_SEQ_conv1:
  fixes a :: real
  assumes "X -- a --> L"
  shows "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
proof -
  {
    from prems have Xdef: "\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s --> norm (X x - L) < r" by (unfold LIM_def)
    
    fix S
    assume as: "(\<forall>n. S n \<noteq> a) \<and> S ----> a"
    then have "S ----> a" by auto
    then have Sdef: "(\<forall>r. 0 < r --> (\<exists>no. \<forall>n. no \<le> n --> norm (S n - a) < r))" by (unfold LIMSEQ_def)
    {
      fix r
      from Xdef have Xdef2: "0 < r --> (\<exists>s > 0. \<forall>x. x \<noteq> a \<and> \<bar>x - a\<bar> < s --> norm (X x - L) < r)" by simp
      {
        assume rgz: "0 < r"

        from Xdef2 rgz have "\<exists>s > 0. \<forall>x. x \<noteq> a \<and> \<bar>x - a\<bar> < s --> norm (X x - L) < r" by simp 
        then obtain s where sdef: "s > 0 \<and> (\<forall>x. x\<noteq>a \<and> \<bar>x - a\<bar> < s \<longrightarrow> norm (X x - L) < r)" by auto
        then have aux: "\<forall>x. x\<noteq>a \<and> \<bar>x - a\<bar> < s \<longrightarrow> norm (X x - L) < r" by auto
        {
          fix n
          from aux have "S n \<noteq> a \<and> \<bar>S n - a\<bar> < s \<longrightarrow> norm (X (S n) - L) < r" by simp
          with as have imp2: "\<bar>S n - a\<bar> < s --> norm (X (S n) - L) < r" by auto
        }
        hence "\<forall>n. \<bar>S n - a\<bar> < s --> norm (X (S n) - L) < r" ..
        moreover
        from Sdef sdef have imp1: "\<exists>no. \<forall>n. no \<le> n --> \<bar>S n - a\<bar> < s" by auto  
        then obtain no where "\<forall>n. no \<le> n --> \<bar>S n - a\<bar> < s" by auto
        ultimately have "\<forall>n. no \<le> n \<longrightarrow> norm (X (S n) - L) < r" by simp
        hence "\<exists>no. \<forall>n. no \<le> n \<longrightarrow> norm (X (S n) - L) < r" by auto
      }
    }
    hence "(\<forall>r. 0 < r --> (\<exists>no. \<forall>n. no \<le> n --> norm (X (S n) - L) < r))" by simp
    hence "(\<lambda>n. X (S n)) ----> L" by (fold LIMSEQ_def)
  }
  thus ?thesis by simp
qed

ML {* fast_arith_split_limit := 0; *}  (* FIXME *)

lemma LIMSEQ_SEQ_conv2:
  fixes a :: real
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  shows "X -- a --> L"
proof (rule ccontr)
  assume "\<not> (X -- a --> L)"
  hence "\<not> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s --> norm (X x - L) < r)" by (unfold LIM_def)
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. \<not>(x \<noteq> a \<and> \<bar>x - a\<bar> < s --> norm (X x - L) < r)" by simp
  hence "\<exists>r > 0. \<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r)" by (simp add: linorder_not_less)
  then obtain r where rdef: "r > 0 \<and> (\<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r))" by auto

  let ?F = "\<lambda>n::nat. SOME x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
  have "?F ----> a"
  proof -
    {
      fix e::real
      assume "0 < e"
        (* choose no such that inverse (real (Suc n)) < e *)
      have "\<exists>no. inverse (real (Suc no)) < e" by (rule reals_Archimedean)
      then obtain m where nodef: "inverse (real (Suc m)) < e" by auto
      {
        fix n
        assume mlen: "m \<le> n"
        then have
          "inverse (real (Suc n)) \<le> inverse (real (Suc m))"
          by auto
        moreover have
          "\<bar>?F n - a\<bar> < inverse (real (Suc n))"
        proof -
          from rdef have
            "\<exists>x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
            by simp
          hence
            "(?F n)\<noteq>a \<and> \<bar>(?F n) - a\<bar> < inverse (real (Suc n)) \<and> norm (X (?F n) - L) \<ge> r"
            by (simp add: some_eq_ex [symmetric])
          thus ?thesis by simp
        qed
        moreover from nodef have
          "inverse (real (Suc m)) < e" .
        ultimately have "\<bar>?F n - a\<bar> < e" by arith
      }
      then have "\<exists>no. \<forall>n. no \<le> n --> \<bar>?F n - a\<bar> < e" by auto
    }
    thus ?thesis by (unfold LIMSEQ_def, simp)
  qed
  
  moreover have "\<forall>n. ?F n \<noteq> a"
  proof -
    {
      fix n
      from rdef have
        "\<exists>x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r"
        by simp
      hence "?F n \<noteq> a" by (simp add: some_eq_ex [symmetric])
    }
    thus ?thesis ..
  qed
  moreover from prems have "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by simp
  ultimately have "(\<lambda>n. X (?F n)) ----> L" by simp
  
  moreover have "\<not> ((\<lambda>n. X (?F n)) ----> L)"
  proof -
    {
      fix no::nat
      obtain n where "n = no + 1" by simp
      then have nolen: "no \<le> n" by simp
        (* We prove this by showing that for any m there is an n\<ge>m such that |X (?F n) - L| \<ge> r *)
      from rdef have "\<forall>s > 0. \<exists>x. (x \<noteq> a \<and> \<bar>x - a\<bar> < s \<and> norm (X x - L) \<ge> r)" ..

      then have "\<exists>x. x\<noteq>a \<and> \<bar>x - a\<bar> < inverse (real (Suc n)) \<and> norm (X x - L) \<ge> r" by simp
      
      hence "norm (X (?F n) - L) \<ge> r" by (simp add: some_eq_ex [symmetric])
      with nolen have "\<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> r" by auto
    }
    then have "(\<forall>no. \<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> r)" by simp
    with rdef have "\<exists>e>0. (\<forall>no. \<exists>n. no \<le> n \<and> norm (X (?F n) - L) \<ge> e)" by auto
    thus ?thesis by (unfold LIMSEQ_def, auto simp add: linorder_not_less)
  qed
  ultimately show False by simp
qed

ML {* fast_arith_split_limit := 9; *}  (* FIXME *)

lemma LIMSEQ_SEQ_conv:
  "(\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> (a::real) \<longrightarrow> (\<lambda>n. X (S n)) ----> L) =
   (X -- a --> L)"
proof
  assume "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L"
  show "X -- a --> L" by (rule LIMSEQ_SEQ_conv2)
next
  assume "(X -- a --> L)"
  show "\<forall>S. (\<forall>n. S n \<noteq> a) \<and> S ----> a \<longrightarrow> (\<lambda>n. X (S n)) ----> L" by (rule LIMSEQ_SEQ_conv1)
qed

lemma real_sqz:
  fixes a::real
  assumes "a < c"
  shows "\<exists>b. a < b \<and> b < c"
by (rule dense)

lemma LIM_offset:
  assumes "(\<lambda>x. f x) -- a --> L"
  shows "(\<lambda>x. f (x+c)) -- (a-c) --> L"
proof -
  have "f -- a --> L" .
  hence
    fd: "\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & norm (x - a) < s --> norm (f x - L) < r"
    by (unfold LIM_def)
  {
    fix r::real
    assume rgz: "0 < r"
    with fd have "\<exists>s > 0. \<forall>x. x\<noteq>a \<and> norm (x - a) < s --> norm (f x - L) < r" by simp
    then obtain s where sgz: "s > 0" and ax: "\<forall>x. x\<noteq>a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r" by auto
    from ax have ax2: "\<forall>x. (x+c)\<noteq>a \<and> norm ((x+c) - a) < s \<longrightarrow> norm (f (x+c) - L) < r" by auto
    {
      fix x
      from ax2 have nt: "(x+c)\<noteq>a \<and> norm ((x+c) - a) < s \<longrightarrow> norm (f (x+c) - L) < r" ..
      moreover have "((x+c)\<noteq>a) = (x\<noteq>(a-c))" by auto
      moreover have "((x+c) - a) = (x - (a-c))" by simp
      ultimately have "x\<noteq>(a-c) \<and> norm (x - (a-c)) < s \<longrightarrow> norm (f (x+c) - L) < r" by simp
    }
    then have "\<forall>x. x\<noteq>(a-c) \<and> norm (x - (a-c)) < s \<longrightarrow> norm (f (x+c) - L) < r" ..
    with sgz have "\<exists>s > 0. \<forall>x. x\<noteq>(a-c) \<and> norm (x - (a-c)) < s \<longrightarrow> norm (f (x+c) - L) < r" by auto
  }
  then have
    "\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> (a-c) & norm (x - (a-c)) < s --> norm (f (x+c) - L) < r" by simp
  thus ?thesis by (fold LIM_def)
qed

end
