(*  Title       : Lim.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Limits, Continuity and Differentiation*}

theory Lim = SEQ + RealDef:

text{*Standard and Nonstandard Definitions*}

constdefs
  LIM :: "[real=>real,real,real] => bool"
				("((_)/ -- (_)/ --> (_))" [60, 0, 60] 60)
  "f -- a --> L ==
     \<forall>r. 0 < r -->
	     (\<exists>s. 0 < s & (\<forall>x. (x \<noteq> a & (\<bar>x + -a\<bar> < s)
			  --> \<bar>f x + -L\<bar> < r)))"

  NSLIM :: "[real=>real,real,real] => bool"
			      ("((_)/ -- (_)/ --NS> (_))" [60, 0, 60] 60)
  "f -- a --NS> L == (\<forall>x. (x \<noteq> hypreal_of_real a &
		      x @= hypreal_of_real a -->
		      ( *f* f) x @= hypreal_of_real L))"

  isCont :: "[real=>real,real] => bool"
  "isCont f a == (f -- a --> (f a))"

  (* NS definition dispenses with limit notions *)
  isNSCont :: "[real=>real,real] => bool"
  "isNSCont f a == (\<forall>y. y @= hypreal_of_real a -->
			   ( *f* f) y @= hypreal_of_real (f a))"

  (* differentiation: D is derivative of function f at x *)
  deriv:: "[real=>real,real,real] => bool"
			    ("(DERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60)
  "DERIV f x :> D == ((%h. (f(x + h) + -f x)/h) -- 0 --> D)"

  nsderiv :: "[real=>real,real,real] => bool"
			    ("(NSDERIV (_)/ (_)/ :> (_))" [60, 0, 60] 60)
  "NSDERIV f x :> D == (\<forall>h \<in> Infinitesimal - {0}.
			(( *f* f)(hypreal_of_real x + h) +
			 - hypreal_of_real (f x))/h @= hypreal_of_real D)"

  differentiable :: "[real=>real,real] => bool"   (infixl "differentiable" 60)
  "f differentiable x == (\<exists>D. DERIV f x :> D)"

  NSdifferentiable :: "[real=>real,real] => bool"   
                       (infixl "NSdifferentiable" 60)
  "f NSdifferentiable x == (\<exists>D. NSDERIV f x :> D)"

  increment :: "[real=>real,real,hypreal] => hypreal"
  "increment f x h == (@inc. f NSdifferentiable x &
		       inc = ( *f* f)(hypreal_of_real x + h) + -hypreal_of_real (f x))"

  isUCont :: "(real=>real) => bool"
  "isUCont f ==  (\<forall>r. 0 < r -->
		      (\<exists>s. 0 < s & (\<forall>x y. \<bar>x + -y\<bar> < s
			    --> \<bar>f x + -f y\<bar> < r)))"

  isNSUCont :: "(real=>real) => bool"
  "isNSUCont f == (\<forall>x y. x @= y --> ( *f* f) x @= ( *f* f) y)"


(*Used in the proof of the Bolzano theorem*)
consts
  Bolzano_bisect :: "[real*real=>bool, real, real, nat] => (real*real)"

primrec
  "Bolzano_bisect P a b 0 = (a,b)"
  "Bolzano_bisect P a b (Suc n) =
      (let (x,y) = Bolzano_bisect P a b n
       in if P(x, (x+y)/2) then ((x+y)/2, y)
                            else (x, (x+y)/2))"



section{*Some Purely Standard Proofs*}

lemma LIM_eq:
     "f -- a --> L =
     (\<forall>r. 0<r --> (\<exists>s. 0 < s & (\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < s --> \<bar>f x - L\<bar> < r)))"
by (simp add: LIM_def diff_minus)

lemma LIM_D:
     "[| f -- a --> L; 0<r |]
      ==> \<exists>s. 0 < s & (\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < s --> \<bar>f x - L\<bar> < r)"
by (simp add: LIM_eq)

lemma LIM_const: "(%x. k) -- x --> k"
by (simp add: LIM_def)
declare LIM_const [simp]

lemma LIM_add:
  assumes f: "f -- a --> L" and g: "g -- a --> M"
  shows "(%x. f x + g(x)) -- a --> (L + M)"
proof (simp add: LIM_eq, clarify)
  fix r :: real
  assume r: "0<r"
  from LIM_D [OF f half_gt_zero [OF r]]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < fs --> \<bar>f x - L\<bar> < r/2"
  by blast
  from LIM_D [OF g half_gt_zero [OF r]]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < gs --> \<bar>g x - M\<bar> < r/2"
  by blast
  show "\<exists>s. 0 < s \<and>
            (\<forall>x. x \<noteq> a \<and> \<bar>x-a\<bar> < s \<longrightarrow> \<bar>f x + g x - (L + M)\<bar> < r)"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: real
    assume "x \<noteq> a \<and> \<bar>x-a\<bar> < min fs gs"
    with fs_lt gs_lt
    have "\<bar>f x - L\<bar> < r/2" and "\<bar>g x - M\<bar> < r/2" by (auto simp add: fs_lt)
    hence "\<bar>f x - L\<bar> + \<bar>g x - M\<bar> < r" by arith
    thus "\<bar>f x + g x - (L + M)\<bar> < r"
      by (blast intro: abs_diff_triangle_ineq order_le_less_trans)
  qed
qed

lemma LIM_minus: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
apply (simp add: LIM_eq)
apply (subgoal_tac "\<forall>x. \<bar>- f x + L\<bar> = \<bar>f x - L\<bar>")
apply (simp_all add: abs_if)
done

lemma LIM_add_minus:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (blast dest: LIM_add LIM_minus)

lemma LIM_diff:
    "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) - g(x)) -- x --> l-m"
by (simp add: diff_minus LIM_add_minus) 


lemma LIM_const_not_eq: "k \<noteq> L ==> ~ ((%x. k) -- a --> L)"
proof (simp add: linorder_neq_iff LIM_eq, elim disjE)
  assume k: "k < L"
  show "\<exists>r. 0 < r \<and>
        (\<forall>s. 0 < s \<longrightarrow> (\<exists>x. (x < a \<or> a < x) \<and> \<bar>x-a\<bar> < s) \<and> \<not> \<bar>k-L\<bar> < r)"
  proof (intro exI conjI strip)
    show "0 < L-k" by (simp add: k)
    fix s :: real
    assume s: "0<s"
    { from s show "s/2 + a < a \<or> a < s/2 + a" by arith
     next
      from s show "\<bar>s / 2 + a - a\<bar> < s" by (simp add: abs_if) 
     next
      from s show "~ \<bar>k-L\<bar> < L-k" by (simp add: abs_if) }
  qed
next
  assume k: "L < k"
  show "\<exists>r. 0 < r \<and>
        (\<forall>s. 0 < s \<longrightarrow> (\<exists>x. (x < a \<or> a < x) \<and> \<bar>x-a\<bar> < s) \<and> \<not> \<bar>k-L\<bar> < r)"
  proof (intro exI conjI strip)
    show "0 < k-L" by (simp add: k)
    fix s :: real
    assume s: "0<s"
    { from s show "s/2 + a < a \<or> a < s/2 + a" by arith
     next
      from s show "\<bar>s / 2 + a - a\<bar> < s" by (simp add: abs_if) 
     next
      from s show "~ \<bar>k-L\<bar> < k-L" by (simp add: abs_if) }
  qed
qed

lemma LIM_const_eq: "(%x. k) -- x --> L ==> k = L"
apply (rule ccontr)
apply (blast dest: LIM_const_not_eq) 
done

lemma LIM_unique: "[| f -- a --> L; f -- a --> M |] ==> L = M"
apply (drule LIM_diff, assumption) 
apply (auto dest!: LIM_const_eq)
done

lemma LIM_mult_zero:
  assumes f: "f -- a --> 0" and g: "g -- a --> 0"
  shows "(%x. f(x) * g(x)) -- a --> 0"
proof (simp add: LIM_eq, clarify)
  fix r :: real
  assume r: "0<r"
  from LIM_D [OF f zero_less_one]
  obtain fs
    where fs:    "0 < fs"
      and fs_lt: "\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < fs --> \<bar>f x\<bar> < 1"
  by auto
  from LIM_D [OF g r]
  obtain gs
    where gs:    "0 < gs"
      and gs_lt: "\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < gs --> \<bar>g x\<bar> < r"
  by auto
  show "\<exists>s. 0 < s \<and> (\<forall>x. x \<noteq> a \<and> \<bar>x-a\<bar> < s \<longrightarrow> \<bar>f x\<bar> * \<bar>g x\<bar> < r)"
  proof (intro exI conjI strip)
    show "0 < min fs gs"  by (simp add: fs gs)
    fix x :: real
    assume "x \<noteq> a \<and> \<bar>x-a\<bar> < min fs gs"
    with fs_lt gs_lt
    have "\<bar>f x\<bar> < 1" and "\<bar>g x\<bar> < r" by (auto simp add: fs_lt)
    hence "\<bar>f x\<bar> * \<bar>g x\<bar> < 1*r" by (rule abs_mult_less) 
    thus "\<bar>f x\<bar> * \<bar>g x\<bar> < r" by simp
  qed
qed

lemma LIM_self: "(%x. x) -- a --> a"
by (auto simp add: LIM_def)

text{*Limits are equal for functions equal except at limit point*}
lemma LIM_equal:
     "[| \<forall>x. x \<noteq> a --> (f x = g x) |] ==> (f -- a --> l) = (g -- a --> l)"
by (simp add: LIM_def)

text{*Two uses in Hyperreal/Transcendental.ML*}
lemma LIM_trans:
     "[| (%x. f(x) + -g(x)) -- a --> 0;  g -- a --> l |] ==> f -- a --> l"
apply (drule LIM_add, assumption)
apply (auto simp add: add_assoc)
done


subsection{*Relationships Between Standard and Nonstandard Concepts*}

text{*Standard and NS definitions of Limit*} (*NEEDS STRUCTURING*)
lemma LIM_NSLIM:
      "f -- x --> L ==> f -- x --NS> L"
apply (simp add: LIM_def NSLIM_def approx_def)
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff, safe)
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto simp add: real_add_minus_iff starfun hypreal_minus hypreal_of_real_def hypreal_add)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl, clarify) 
apply (drule_tac x = u in spec, clarify)
apply (drule_tac x = s in spec, clarify)
apply (subgoal_tac "\<forall>n::nat. (xa n) \<noteq> x & abs ((xa n) + - x) < s --> abs (f (xa n) + - L) < u")
prefer 2 apply blast
apply (drule FreeUltrafilterNat_all, ultra)
done

(*---------------------------------------------------------------------
    Limit: NS definition ==> standard definition
 ---------------------------------------------------------------------*)

lemma lemma_LIM: "\<forall>s. 0 < s --> (\<exists>xa.  xa \<noteq> x &
         \<bar>xa + - x\<bar> < s  & r \<le> \<bar>f xa + -L\<bar>)
      ==> \<forall>n::nat. \<exists>xa.  xa \<noteq> x &
              \<bar>xa + -x\<bar> < inverse(real(Suc n)) & r \<le> \<bar>f xa + -L\<bar>"
apply clarify
apply (cut_tac n1 = n in real_of_nat_Suc_gt_zero [THEN positive_imp_inverse_positive], auto)
done

lemma lemma_skolemize_LIM2:
     "\<forall>s. 0 < s --> (\<exists>xa.  xa \<noteq> x &
         \<bar>xa + - x\<bar> < s  & r \<le> \<bar>f xa + -L\<bar>)
      ==> \<exists>X. \<forall>n::nat. X n \<noteq> x &
                \<bar>X n + -x\<bar> < inverse(real(Suc n)) & r \<le> abs(f (X n) + -L)"
apply (drule lemma_LIM)
apply (drule choice, blast)
done

lemma lemma_simp: "\<forall>n. X n \<noteq> x &
          \<bar>X n + - x\<bar> < inverse (real(Suc n)) &
          r \<le> abs (f (X n) + - L) ==>
          \<forall>n. \<bar>X n + - x\<bar> < inverse (real(Suc n))"
by auto


(*-------------------
    NSLIM => LIM
 -------------------*)

lemma NSLIM_LIM: "f -- x --NS> L ==> f -- x --> L"
apply (simp add: LIM_def NSLIM_def approx_def)
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff, clarify)
apply (rule ccontr, simp)  
apply (simp add: linorder_not_less)
apply (drule lemma_skolemize_LIM2, safe)
apply (drule_tac x = "Abs_hypreal (hyprel``{X}) " in spec)
apply (auto simp add: starfun hypreal_minus hypreal_of_real_def hypreal_add)
apply (drule lemma_simp [THEN real_seq_to_hypreal_Infinitesimal])
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff hypreal_of_real_def hypreal_minus hypreal_add, blast)
apply (drule spec, drule mp, assumption)
apply (drule FreeUltrafilterNat_all, ultra)
done


(**** Key result ****)
lemma LIM_NSLIM_iff: "(f -- x --> L) = (f -- x --NS> L)"
by (blast intro: LIM_NSLIM NSLIM_LIM)

(*-------------------------------------------------------------------*)
(*   Proving properties of limits using nonstandard definition and   *)
(*   hence, the properties hold for standard limits as well          *)
(*-------------------------------------------------------------------*)
(*------------------------------------------------
      NSLIM_mult and hence (trivially) LIM_mult
 ------------------------------------------------*)

lemma NSLIM_mult:
     "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) * g(x)) -- x --NS> (l * m)"
apply (simp add: NSLIM_def)
apply (auto intro!: approx_mult_HFinite)
done

lemma LIM_mult2: "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) * g(x)) -- x --> (l * m)"
by (simp add: LIM_NSLIM_iff NSLIM_mult)

(*----------------------------------------------
      NSLIM_add and hence (trivially) LIM_add
      Note the much shorter proof
 ----------------------------------------------*)
lemma NSLIM_add:
     "[| f -- x --NS> l; g -- x --NS> m |]
      ==> (%x. f(x) + g(x)) -- x --NS> (l + m)"
apply (simp add: NSLIM_def)
apply (auto intro!: approx_add)
done

lemma LIM_add2: "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + g(x)) -- x --> (l + m)"
by (simp add: LIM_NSLIM_iff NSLIM_add)


lemma NSLIM_const: "(%x. k) -- x --NS> k"
by (simp add: NSLIM_def)

declare NSLIM_const [simp]

lemma LIM_const2: "(%x. k) -- x --> k"
by (simp add: LIM_NSLIM_iff)


lemma NSLIM_minus: "f -- a --NS> L ==> (%x. -f(x)) -- a --NS> -L"
by (simp add: NSLIM_def)

lemma LIM_minus2: "f -- a --> L ==> (%x. -f(x)) -- a --> -L"
by (simp add: LIM_NSLIM_iff NSLIM_minus)


lemma NSLIM_add_minus: "[| f -- x --NS> l; g -- x --NS> m |] ==> (%x. f(x) + -g(x)) -- x --NS> (l + -m)"
by (blast dest: NSLIM_add NSLIM_minus)

lemma LIM_add_minus2: "[| f -- x --> l; g -- x --> m |] ==> (%x. f(x) + -g(x)) -- x --> (l + -m)"
by (simp add: LIM_NSLIM_iff NSLIM_add_minus)


lemma NSLIM_inverse:
     "[| f -- a --NS> L;  L \<noteq> 0 |]
      ==> (%x. inverse(f(x))) -- a --NS> (inverse L)"
apply (simp add: NSLIM_def, clarify)
apply (drule spec)
apply (auto simp add: hypreal_of_real_approx_inverse)
done

lemma LIM_inverse: "[| f -- a --> L; L \<noteq> 0 |] ==> (%x. inverse(f(x))) -- a --> (inverse L)"
by (simp add: LIM_NSLIM_iff NSLIM_inverse)


lemma NSLIM_zero:
  assumes f: "f -- a --NS> l" shows "(%x. f(x) + -l) -- a --NS> 0"
proof -;
  have "(\<lambda>x. f x + - l) -- a --NS> l + -l"
    by (rule NSLIM_add_minus [OF f NSLIM_const]) 
  thus ?thesis by simp
qed

lemma LIM_zero2: "f -- a --> l ==> (%x. f(x) + -l) -- a --> 0"
by (simp add: LIM_NSLIM_iff NSLIM_zero)

lemma NSLIM_zero_cancel: "(%x. f(x) - l) -- x --NS> 0 ==> f -- x --NS> l"
apply (drule_tac g = "%x. l" and m = l in NSLIM_add)
apply (auto simp add: diff_minus add_assoc)
done

lemma LIM_zero_cancel: "(%x. f(x) - l) -- x --> 0 ==> f -- x --> l"
apply (drule_tac g = "%x. l" and M = l in LIM_add)
apply (auto simp add: diff_minus add_assoc)
done



lemma NSLIM_not_zero: "k \<noteq> 0 ==> ~ ((%x. k) -- x --NS> 0)"
apply (simp add: NSLIM_def)
apply (rule_tac x = "hypreal_of_real x + epsilon" in exI)
apply (auto intro: Infinitesimal_add_approx_self [THEN approx_sym]
            simp add: hypreal_epsilon_not_zero)
done

lemma NSLIM_const_not_eq: "k \<noteq> L ==> ~ ((%x. k) -- x --NS> L)"
apply (simp add: NSLIM_def)
apply (rule_tac x = "hypreal_of_real x + epsilon" in exI)
apply (auto intro: Infinitesimal_add_approx_self [THEN approx_sym]
            simp add: hypreal_epsilon_not_zero)
done

lemma NSLIM_const_eq: "(%x. k) -- x --NS> L ==> k = L"
apply (rule ccontr)
apply (blast dest: NSLIM_const_not_eq) 
done

(* can actually be proved more easily by unfolding def! *)
lemma NSLIM_unique: "[| f -- x --NS> L; f -- x --NS> M |] ==> L = M"
apply (drule NSLIM_minus)
apply (drule NSLIM_add, assumption)
apply (auto dest!: NSLIM_const_eq [symmetric])
done

lemma LIM_unique2: "[| f -- x --> L; f -- x --> M |] ==> L = M"
by (simp add: LIM_NSLIM_iff NSLIM_unique)


lemma NSLIM_mult_zero: "[| f -- x --NS> 0; g -- x --NS> 0 |] ==> (%x. f(x)*g(x)) -- x --NS> 0"
by (drule NSLIM_mult, auto)

(* we can use the corresponding thm LIM_mult2 *)
(* for standard definition of limit           *)

lemma LIM_mult_zero2: "[| f -- x --> 0; g -- x --> 0 |] ==> (%x. f(x)*g(x)) -- x --> 0"
by (drule LIM_mult2, auto)


lemma NSLIM_self: "(%x. x) -- a --NS> a"
by (simp add: NSLIM_def)


(*-----------------------------------------------------------------------------
   Derivatives and Continuity - NS and Standard properties
 -----------------------------------------------------------------------------*)
text{*Continuity*}

lemma isNSContD: "[| isNSCont f a; y \<approx> hypreal_of_real a |] ==> ( *f* f) y \<approx> hypreal_of_real (f a)"
by (simp add: isNSCont_def)

lemma isNSCont_NSLIM: "isNSCont f a ==> f -- a --NS> (f a) "
by (simp add: isNSCont_def NSLIM_def)

lemma NSLIM_isNSCont: "f -- a --NS> (f a) ==> isNSCont f a"
apply (simp add: isNSCont_def NSLIM_def, auto)
apply (rule_tac Q = "y = hypreal_of_real a" in excluded_middle [THEN disjE], auto)
done

(*-----------------------------------------------------
    NS continuity can be defined using NS Limit in
    similar fashion to standard def of continuity
 -----------------------------------------------------*)
lemma isNSCont_NSLIM_iff: "(isNSCont f a) = (f -- a --NS> (f a))"
by (blast intro: isNSCont_NSLIM NSLIM_isNSCont)

(*----------------------------------------------
  Hence, NS continuity can be given
  in terms of standard limit
 ---------------------------------------------*)
lemma isNSCont_LIM_iff: "(isNSCont f a) = (f -- a --> (f a))"
by (simp add: LIM_NSLIM_iff isNSCont_NSLIM_iff)

(*-----------------------------------------------
  Moreover, it's trivial now that NS continuity
  is equivalent to standard continuity
 -----------------------------------------------*)
lemma isNSCont_isCont_iff: "(isNSCont f a) = (isCont f a)"
apply (simp add: isCont_def)
apply (rule isNSCont_LIM_iff)
done

(*----------------------------------------
  Standard continuity ==> NS continuity
 ----------------------------------------*)
lemma isCont_isNSCont: "isCont f a ==> isNSCont f a"
by (erule isNSCont_isCont_iff [THEN iffD2])

(*----------------------------------------
  NS continuity ==> Standard continuity
 ----------------------------------------*)
lemma isNSCont_isCont: "isNSCont f a ==> isCont f a"
by (erule isNSCont_isCont_iff [THEN iffD1])

text{*Alternative definition of continuity*}
(* Prove equivalence between NS limits - *)
(* seems easier than using standard def  *)
lemma NSLIM_h_iff: "(f -- a --NS> L) = ((%h. f(a + h)) -- 0 --NS> L)"
apply (simp add: NSLIM_def, auto)
apply (drule_tac x = "hypreal_of_real a + x" in spec)
apply (drule_tac [2] x = "-hypreal_of_real a + x" in spec, safe, simp)
apply (rule mem_infmal_iff [THEN iffD2, THEN Infinitesimal_add_approx_self [THEN approx_sym]])
apply (rule_tac [4] approx_minus_iff2 [THEN iffD1])
 prefer 3 apply (simp add: add_commute) 
apply (rule_tac [2] z = x in eq_Abs_hypreal)
apply (rule_tac [4] z = x in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_of_real_def hypreal_minus hypreal_add add_assoc approx_refl hypreal_zero_def)
done

lemma NSLIM_isCont_iff: "(f -- a --NS> f a) = ((%h. f(a + h)) -- 0 --NS> f a)"
by (rule NSLIM_h_iff)

lemma LIM_isCont_iff: "(f -- a --> f a) = ((%h. f(a + h)) -- 0 --> f(a))"
by (simp add: LIM_NSLIM_iff NSLIM_isCont_iff)

lemma isCont_iff: "(isCont f x) = ((%h. f(x + h)) -- 0 --> f(x))"
by (simp add: isCont_def LIM_isCont_iff)

(*--------------------------------------------------------------------------
   Immediate application of nonstandard criterion for continuity can offer
   very simple proofs of some standard property of continuous functions
 --------------------------------------------------------------------------*)
text{*sum continuous*}
lemma isCont_add: "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) + g(x)) a"
by (auto intro: approx_add simp add: isNSCont_isCont_iff [symmetric] isNSCont_def)

text{*mult continuous*}
lemma isCont_mult: "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) * g(x)) a"
by (auto intro!: starfun_mult_HFinite_approx 
            simp del: starfun_mult [symmetric] 
            simp add: isNSCont_isCont_iff [symmetric] isNSCont_def)

(*-------------------------------------------
     composition of continuous functions
     Note very short straightforard proof!
 ------------------------------------------*)
lemma isCont_o: "[| isCont f a; isCont g (f a) |] ==> isCont (g o f) a"
by (auto simp add: isNSCont_isCont_iff [symmetric] isNSCont_def starfun_o [symmetric])

lemma isCont_o2: "[| isCont f a; isCont g (f a) |] ==> isCont (%x. g (f x)) a"
by (auto dest: isCont_o simp add: o_def)

lemma isNSCont_minus: "isNSCont f a ==> isNSCont (%x. - f x) a"
by (simp add: isNSCont_def)

lemma isCont_minus: "isCont f a ==> isCont (%x. - f x) a"
by (auto simp add: isNSCont_isCont_iff [symmetric] isNSCont_minus)

lemma isCont_inverse:
      "[| isCont f x; f x \<noteq> 0 |] ==> isCont (%x. inverse (f x)) x"
apply (simp add: isCont_def)
apply (blast intro: LIM_inverse)
done

lemma isNSCont_inverse: "[| isNSCont f x; f x \<noteq> 0 |] ==> isNSCont (%x. inverse (f x)) x"
by (auto intro: isCont_inverse simp add: isNSCont_isCont_iff)

lemma isCont_diff:
      "[| isCont f a; isCont g a |] ==> isCont (%x. f(x) - g(x)) a"
apply (simp add: diff_minus)
apply (auto intro: isCont_add isCont_minus)
done

lemma isCont_const: "isCont (%x. k) a"
by (simp add: isCont_def)
declare isCont_const [simp]

lemma isNSCont_const: "isNSCont (%x. k) a"
by (simp add: isNSCont_def)
declare isNSCont_const [simp]

lemma isNSCont_rabs: "isNSCont abs a"
apply (simp add: isNSCont_def)
apply (auto intro: approx_hrabs simp add: hypreal_of_real_hrabs [symmetric] starfun_rabs_hrabs)
done
declare isNSCont_rabs [simp]

lemma isCont_rabs: "isCont abs a"
by (auto simp add: isNSCont_isCont_iff [symmetric])
declare isCont_rabs [simp]

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

text{*Uniform continuity*}
lemma isNSUContD: "[| isNSUCont f; x \<approx> y|] ==> ( *f* f) x \<approx> ( *f* f) y"
by (simp add: isNSUCont_def)

lemma isUCont_isCont: "isUCont f ==> isCont f x"
by (simp add: isUCont_def isCont_def LIM_def, meson)

lemma isUCont_isNSUCont: "isUCont f ==> isNSUCont f"
apply (simp add: isNSUCont_def isUCont_def approx_def)
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff, safe)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_minus hypreal_add)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl, safe)
apply (drule_tac x = u in spec, clarify)
apply (drule_tac x = s in spec, clarify)
apply (subgoal_tac "\<forall>n::nat. abs ((xa n) + - (xb n)) < s --> abs (f (xa n) + - f (xb n)) < u")
prefer 2 apply blast
apply (erule_tac V = "\<forall>x y. \<bar>x + - y\<bar> < s --> \<bar>f x + - f y\<bar> < u" in thin_rl)
apply (drule FreeUltrafilterNat_all, ultra)
done

lemma lemma_LIMu: "\<forall>s. 0 < s --> (\<exists>z y. \<bar>z + - y\<bar> < s & r \<le> \<bar>f z + -f y\<bar>)
      ==> \<forall>n::nat. \<exists>z y.
               \<bar>z + -y\<bar> < inverse(real(Suc n)) &
               r \<le> \<bar>f z + -f y\<bar>"
apply clarify
apply (cut_tac n1 = n in real_of_nat_Suc_gt_zero [THEN positive_imp_inverse_positive], auto)
done

lemma lemma_skolemize_LIM2u: "\<forall>s. 0 < s --> (\<exists>z y. \<bar>z + - y\<bar> < s  & r \<le> \<bar>f z + -f y\<bar>)
      ==> \<exists>X Y. \<forall>n::nat.
               abs(X n + -(Y n)) < inverse(real(Suc n)) &
               r \<le> abs(f (X n) + -f (Y n))"
apply (drule lemma_LIMu)
apply (drule choice, safe)
apply (drule choice, blast)
done

lemma lemma_simpu: "\<forall>n. \<bar>X n + -Y n\<bar> < inverse (real(Suc n)) &
          r \<le> abs (f (X n) + - f(Y n)) ==>
          \<forall>n. \<bar>X n + - Y n\<bar> < inverse (real(Suc n))"
apply auto
done

lemma isNSUCont_isUCont:
     "isNSUCont f ==> isUCont f"
apply (simp add: isNSUCont_def isUCont_def approx_def)
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff, safe)
apply (rule ccontr, simp) 
apply (simp add: linorder_not_less)
apply (drule lemma_skolemize_LIM2u, safe)
apply (drule_tac x = "Abs_hypreal (hyprel``{X}) " in spec)
apply (drule_tac x = "Abs_hypreal (hyprel``{Y}) " in spec)
apply (simp add: starfun hypreal_minus hypreal_add, auto)
apply (drule lemma_simpu [THEN real_seq_to_hypreal_Infinitesimal2])
apply (simp add: Infinitesimal_FreeUltrafilterNat_iff hypreal_minus hypreal_add, blast)
apply (rotate_tac 2)
apply (drule_tac x = r in spec, clarify)
apply (drule FreeUltrafilterNat_all, ultra)
done

text{*Derivatives*}
lemma DERIV_iff: "(DERIV f x :> D) = ((%h. (f(x + h) + - f(x))/h) -- 0 --> D)"
by (simp add: deriv_def)

lemma DERIV_NS_iff:
      "(DERIV f x :> D) = ((%h. (f(x + h) + - f(x))/h) -- 0 --NS> D)"
by (simp add: deriv_def LIM_NSLIM_iff)

lemma DERIV_D: "DERIV f x :> D ==> (%h. (f(x + h) + - f(x))/h) -- 0 --> D"
by (simp add: deriv_def)

lemma NS_DERIV_D: "DERIV f x :> D ==>
           (%h. (f(x + h) + - f(x))/h) -- 0 --NS> D"
by (simp add: deriv_def LIM_NSLIM_iff)

subsubsection{*Uniqueness*}

lemma DERIV_unique:
      "[| DERIV f x :> D; DERIV f x :> E |] ==> D = E"
apply (simp add: deriv_def)
apply (blast intro: LIM_unique)
done

lemma NSDeriv_unique:
     "[| NSDERIV f x :> D; NSDERIV f x :> E |] ==> D = E"
apply (simp add: nsderiv_def)
apply (cut_tac Infinitesimal_epsilon hypreal_epsilon_not_zero)
apply (auto dest!: bspec [where x=epsilon] 
            intro!: inj_hypreal_of_real [THEN injD] 
            dest: approx_trans3)
done

subsubsection{*Differentiable*}

lemma differentiableD: "f differentiable x ==> \<exists>D. DERIV f x :> D"
by (simp add: differentiable_def)

lemma differentiableI: "DERIV f x :> D ==> f differentiable x"
by (force simp add: differentiable_def)

lemma NSdifferentiableD: "f NSdifferentiable x ==> \<exists>D. NSDERIV f x :> D"
by (simp add: NSdifferentiable_def)

lemma NSdifferentiableI: "NSDERIV f x :> D ==> f NSdifferentiable x"
by (force simp add: NSdifferentiable_def)

subsubsection{*Alternative definition for differentiability*}

lemma LIM_I:
     "(!!r. 0<r ==> (\<exists>s. 0 < s & (\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < s --> \<bar>f x - L\<bar> < r)))
      ==> f -- a --> L"
by (simp add: LIM_eq)

lemma DERIV_LIM_iff:
     "((%h. (f(a + h) - f(a)) / h) -- 0 --> D) =
      ((%x. (f(x)-f(a)) / (x-a)) -- a --> D)"
proof (intro iffI LIM_I)
  fix r::real
  assume r: "0<r"
  assume "(\<lambda>h. (f (a + h) - f a) / h) -- 0 --> D"
  from LIM_D [OF this r]
  obtain s
    where s:    "0 < s"
      and s_lt: "\<forall>x. x \<noteq> 0 & \<bar>x\<bar> < s --> \<bar>(f (a + x) - f a) / x - D\<bar> < r"
  by auto
  show "\<exists>s. 0 < s \<and>
            (\<forall>x. x \<noteq> a \<and> \<bar>x-a\<bar> < s \<longrightarrow> \<bar>(f x - f a) / (x-a) - D\<bar> < r)"
  proof (intro exI conjI strip)
    show "0 < s"  by (rule s)
  next
    fix x::real
    assume "x \<noteq> a \<and> \<bar>x-a\<bar> < s"
    with s_lt [THEN spec [where x="x-a"]]
    show "\<bar>(f x - f a) / (x-a) - D\<bar> < r" by auto
  qed
next
  fix r::real
  assume r: "0<r"
  assume "(\<lambda>x. (f x - f a) / (x-a)) -- a --> D"
  from LIM_D [OF this r]
  obtain s
    where s:    "0 < s"
      and s_lt: "\<forall>x. x \<noteq> a & \<bar>x-a\<bar> < s --> \<bar>(f x - f a)/(x-a) - D\<bar> < r"
  by auto
  show "\<exists>s. 0 < s \<and>
            (\<forall>x. x \<noteq> 0 & \<bar>x - 0\<bar> < s --> \<bar>(f (a + x) - f a) / x - D\<bar> < r)"
  proof (intro exI conjI strip)
    show "0 < s"  by (rule s)
  next
    fix x::real
    assume "x \<noteq> 0 \<and> \<bar>x - 0\<bar> < s"
    with s_lt [THEN spec [where x="x+a"]]
    show "\<bar>(f (a + x) - f a) / x - D\<bar> < r" by (auto simp add: add_ac)
  qed
qed

lemma DERIV_iff2: "(DERIV f x :> D) = ((%z. (f(z) - f(x)) / (z-x)) -- x --> D)"
by (simp add: deriv_def diff_minus [symmetric] DERIV_LIM_iff)


subsection{*Equivalence of NS and standard definitions of differentiation*}

text{*First NSDERIV in terms of NSLIM*}

(*--- first equivalence ---*)
lemma NSDERIV_NSLIM_iff:
      "(NSDERIV f x :> D) = ((%h. (f(x + h) + - f(x))/h) -- 0 --NS> D)"
apply (simp add: nsderiv_def NSLIM_def, auto)
apply (drule_tac x = xa in bspec)
apply (rule_tac [3] ccontr)
apply (drule_tac [3] x = h in spec)
apply (auto simp add: mem_infmal_iff starfun_lambda_cancel)
done

(*--- second equivalence ---*)
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
lemma hypreal_not_eq_minus_iff: "(x \<noteq> a) = (x + -a \<noteq> (0::hypreal))"
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
apply (auto simp add: diff_minus
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

text{*Now equivalence between NSDERIV and DERIV*}
lemma NSDERIV_DERIV_iff: "(NSDERIV f x :> D) = (DERIV f x :> D)"
by (simp add: deriv_def NSDERIV_NSLIM_iff LIM_NSLIM_iff)

(*---------------------------------------------------
         Differentiability implies continuity
         nice and simple "algebraic" proof
 --------------------------------------------------*)
lemma NSDERIV_isNSCont: "NSDERIV f x :> D ==> isNSCont f x"
apply (auto simp add: nsderiv_def isNSCont_NSLIM_iff NSLIM_def)
apply (drule approx_minus_iff [THEN iffD1])
apply (drule hypreal_not_eq_minus_iff [THEN iffD1])
apply (drule_tac x = "-hypreal_of_real x + xa" in bspec)
 prefer 2 apply (simp add: add_assoc [symmetric]) 
apply (auto simp add: mem_infmal_iff [symmetric] hypreal_add_commute)
apply (drule_tac c = "xa + -hypreal_of_real x" in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc)
apply (drule_tac x3=D in
           HFinite_hypreal_of_real [THEN [2] Infinitesimal_HFinite_mult,
             THEN mem_infmal_iff [THEN iffD1]])
apply (auto simp add: mult_commute 
            intro: approx_trans approx_minus_iff [THEN iffD2])
done

text{*Now Sandard proof*}
lemma DERIV_isCont: "DERIV f x :> D ==> isCont f x"
by (simp add: NSDERIV_DERIV_iff [symmetric] isNSCont_isCont_iff [symmetric] 
              NSDERIV_isNSCont)


(*----------------------------------------------------------------------------
      Differentiation rules for combinations of functions
      follow from clear, straightforard, algebraic
      manipulations
 ----------------------------------------------------------------------------*)
text{*Constant function*}

(* use simple constant nslimit theorem *)
lemma NSDERIV_const: "(NSDERIV (%x. k) x :> 0)"
by (simp add: NSDERIV_NSLIM_iff)
declare NSDERIV_const [simp]

lemma DERIV_const: "(DERIV (%x. k) x :> 0)"
by (simp add: NSDERIV_DERIV_iff [symmetric])
declare DERIV_const [simp]

(*-----------------------------------------------------
    Sum of functions- proved easily
 ----------------------------------------------------*)


lemma NSDERIV_add: "[| NSDERIV f x :> Da;  NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x + g x) x :> Da + Db"
apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
apply (auto simp add: add_divide_distrib dest!: spec)
apply (drule_tac b = "hypreal_of_real Da" and d = "hypreal_of_real Db" in approx_add)
apply (auto simp add: add_ac)
done

(* Standard theorem *)
lemma DERIV_add: "[| DERIV f x :> Da; DERIV g x :> Db |]
      ==> DERIV (%x. f x + g x) x :> Da + Db"
apply (simp add: NSDERIV_add NSDERIV_DERIV_iff [symmetric])
done

(*-----------------------------------------------------
  Product of functions - Proof is trivial but tedious
  and long due to rearrangement of terms
 ----------------------------------------------------*)

lemma lemma_nsderiv1: "((a::hypreal)*b) + -(c*d) = (b*(a + -c)) + (c*(b + -d))"
by (simp add: right_distrib)

lemma lemma_nsderiv2: "[| (x + y) / z = hypreal_of_real D + yb; z \<noteq> 0;
         z \<in> Infinitesimal; yb \<in> Infinitesimal |]
      ==> x + y \<approx> 0"
apply (frule_tac c1 = z in hypreal_mult_right_cancel [THEN iffD2], assumption)
apply (erule_tac V = " (x + y) / z = hypreal_of_real D + yb" in thin_rl)
apply (auto intro!: Infinitesimal_HFinite_mult2 HFinite_add
            simp add: hypreal_mult_assoc mem_infmal_iff [symmetric])
apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
done


lemma NSDERIV_mult: "[| NSDERIV f x :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
apply (auto dest!: spec
	    simp add: starfun_lambda_cancel lemma_nsderiv1)
apply (simp (no_asm) add: add_divide_distrib)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply (auto simp del: times_divide_eq_right simp add: times_divide_eq_right [symmetric])
apply (drule_tac D = Db in lemma_nsderiv2)
apply (drule_tac [4]
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

lemma DERIV_mult:
     "[| DERIV f x :> Da; DERIV g x :> Db |] 
      ==> DERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
by (simp add: NSDERIV_mult NSDERIV_DERIV_iff [symmetric])

text{*Multiplying by a constant*}
lemma NSDERIV_cmult: "NSDERIV f x :> D
      ==> NSDERIV (%x. c * f x) x :> c*D"
apply (simp only: times_divide_eq_right [symmetric] NSDERIV_NSLIM_iff 
                  minus_mult_right right_distrib [symmetric])
apply (erule NSLIM_const [THEN NSLIM_mult])
done

(* let's do the standard proof though theorem *)
(* LIM_mult2 follows from a NS proof          *)

lemma DERIV_cmult:
      "DERIV f x :> D ==> DERIV (%x. c * f x) x :> c*D"
apply (simp only: deriv_def times_divide_eq_right [symmetric] 
                  NSDERIV_NSLIM_iff minus_mult_right right_distrib [symmetric])
apply (erule LIM_const [THEN LIM_mult2])
done

text{*Negation of function*}
lemma NSDERIV_minus: "NSDERIV f x :> D ==> NSDERIV (%x. -(f x)) x :> -D"
proof (simp add: NSDERIV_NSLIM_iff)
  assume "(\<lambda>h. (f (x + h) + - f x) / h) -- 0 --NS> D"
  hence deriv: "(\<lambda>h. - ((f(x+h) + - f x) / h)) -- 0 --NS> - D" 
    by (rule NSLIM_minus)
  have "\<forall>h. - ((f (x + h) + - f x) / h) = (- f (x + h) + f x) / h"
    by (simp add: minus_divide_left) 
  with deriv
  show "(\<lambda>h. (- f (x + h) + f x) / h) -- 0 --NS> - D" by simp
qed


lemma DERIV_minus: "DERIV f x :> D ==> DERIV (%x. -(f x)) x :> -D"
by (simp add: NSDERIV_minus NSDERIV_DERIV_iff [symmetric])

text{*Subtraction*}
lemma NSDERIV_add_minus: "[| NSDERIV f x :> Da; NSDERIV g x :> Db |] ==> NSDERIV (%x. f x + -g x) x :> Da + -Db"
by (blast dest: NSDERIV_add NSDERIV_minus)

lemma DERIV_add_minus: "[| DERIV f x :> Da; DERIV g x :> Db |] ==> DERIV (%x. f x + -g x) x :> Da + -Db"
by (blast dest: DERIV_add DERIV_minus)

lemma NSDERIV_diff:
     "[| NSDERIV f x :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x - g x) x :> Da-Db"
apply (simp add: diff_minus)
apply (blast intro: NSDERIV_add_minus)
done

lemma DERIV_diff:
     "[| DERIV f x :> Da; DERIV g x :> Db |]
       ==> DERIV (%x. f x - g x) x :> Da-Db"
apply (simp add: diff_minus)
apply (blast intro: DERIV_add_minus)
done

(*---------------------------------------------------------------
                     (NS) Increment
 ---------------------------------------------------------------*)
lemma incrementI:
      "f NSdifferentiable x ==>
      increment f x h = ( *f* f) (hypreal_of_real(x) + h) +
      -hypreal_of_real (f x)"
by (simp add: increment_def)

lemma incrementI2: "NSDERIV f x :> D ==>
     increment f x h = ( *f* f) (hypreal_of_real(x) + h) +
     -hypreal_of_real (f x)"
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
apply (erule_tac [2] V = "(( *f* f) (hypreal_of_real (x) + h) + - hypreal_of_real (f x)) / h = hypreal_of_real (D) + y" in thin_rl)
apply assumption
apply (simp add: times_divide_eq_right [symmetric] del: times_divide_eq_right)
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
      ==> ( *f* f) (hypreal_of_real(x) + h) + -hypreal_of_real(f x) \<approx> 0"
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
                   + - hypreal_of_real (f (g x)))
              / (( *f* g) (hypreal_of_real(x) + xa) + - hypreal_of_real (g x))
             \<approx> hypreal_of_real(Da)"
by (auto simp add: NSDERIV_NSLIM_iff2 NSLIM_def diff_minus [symmetric])

(*--------------------------------------------------------------
   from other version of differentiability

                f(x + h) - f(x)
               ----------------- \<approx> Db
                       h
 --------------------------------------------------------------*)
lemma NSDERIVD2: "[| NSDERIV g x :> Db; xa \<in> Infinitesimal; xa \<noteq> 0 |]
      ==> (( *f* g) (hypreal_of_real(x) + xa) + - hypreal_of_real(g x)) / xa
          \<approx> hypreal_of_real(Db)"
by (auto simp add: NSDERIV_NSLIM_iff NSLIM_def mem_infmal_iff starfun_lambda_cancel)

lemma lemma_chain: "(z::hypreal) \<noteq> 0 ==> x*y = (x*inverse(z))*(z*y)"
by auto

(*------------------------------------------------------
  This proof uses both definitions of differentiability.
 ------------------------------------------------------*)
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
apply (rule_tac z1 = "( *f* g) (hypreal_of_real (x) + xa) + -hypreal_of_real (g x) " and y1 = "inverse xa" in lemma_chain [THEN ssubst])
apply (erule hypreal_not_eq_minus_iff [THEN iffD1])
apply (rule approx_mult_hypreal_of_real)
apply (simp_all add: divide_inverse [symmetric])
apply (blast intro: NSDERIVD1 approx_minus_iff [THEN iffD2])
apply (blast intro: NSDERIVD2)
done

(* standard version *)
lemma DERIV_chain: "[| DERIV f (g x) :> Da; DERIV g x :> Db |] ==> DERIV (f o g) x :> Da * Db"
by (simp add: NSDERIV_DERIV_iff [symmetric] NSDERIV_chain)

lemma DERIV_chain2: "[| DERIV f (g x) :> Da; DERIV g x :> Db |] ==> DERIV (%x. f (g x)) x :> Da * Db"
by (auto dest: DERIV_chain simp add: o_def)

text{*Differentiation of natural number powers*}
lemma NSDERIV_Id: "NSDERIV (%x. x) x :> 1"
by (auto simp add: NSDERIV_NSLIM_iff NSLIM_def starfun_Id)
declare NSDERIV_Id [simp]

(*derivative of the identity function*)
lemma DERIV_Id: "DERIV (%x. x) x :> 1"
by (simp add: NSDERIV_DERIV_iff [symmetric])
declare DERIV_Id [simp]

lemmas isCont_Id = DERIV_Id [THEN DERIV_isCont, standard]

(*derivative of linear multiplication*)
lemma DERIV_cmult_Id: "DERIV (op * c) x :> c"
by (cut_tac c = c and x = x in DERIV_Id [THEN DERIV_cmult], simp)
declare DERIV_cmult_Id [simp]

lemma NSDERIV_cmult_Id: "NSDERIV (op * c) x :> c"
by (simp add: NSDERIV_DERIV_iff)
declare NSDERIV_cmult_Id [simp]

lemma DERIV_pow: "DERIV (%x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
apply (induct_tac "n")
apply (drule_tac [2] DERIV_Id [THEN DERIV_mult])
apply (auto simp add: real_of_nat_Suc left_distrib)
apply (case_tac "0 < n")
apply (drule_tac x = x in realpow_minus_mult)
apply (auto simp add: real_mult_assoc real_add_commute)
done

(* NS version *)
lemma NSDERIV_pow: "NSDERIV (%x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
by (simp add: NSDERIV_DERIV_iff DERIV_pow)

(*---------------------------------------------------------------
                    Power of -1
 ---------------------------------------------------------------*)

(*Can't get rid of x \<noteq> 0 because it isn't continuous at zero*)
lemma NSDERIV_inverse:
     "x \<noteq> 0 ==> NSDERIV (%x. inverse(x)) x :> (- (inverse x ^ Suc (Suc 0)))"
apply (simp add: nsderiv_def)
apply (rule ballI, simp, clarify) 
apply (frule Infinitesimal_add_not_zero)
prefer 2 apply (simp add: add_commute) 
apply (auto simp add: starfun_inverse_inverse realpow_two 
        simp del: minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (simp add: inverse_add inverse_mult_distrib [symmetric]
              inverse_minus_eq [symmetric] add_ac mult_ac
            del: inverse_mult_distrib inverse_minus_eq 
                 minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (simp (no_asm_simp) add: mult_assoc [symmetric] right_distrib
            del: minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (rule_tac y = " inverse (- hypreal_of_real x * hypreal_of_real x) " in approx_trans)
apply (rule inverse_add_Infinitesimal_approx2)
apply (auto dest!: hypreal_of_real_HFinite_diff_Infinitesimal 
            simp add: inverse_minus_eq [symmetric] HFinite_minus_iff)
apply (rule Infinitesimal_HFinite_mult2, auto)
done




lemma DERIV_inverse: "x \<noteq> 0 ==> DERIV (%x. inverse(x)) x :> (-(inverse x ^ Suc (Suc 0)))"
by (simp add: NSDERIV_inverse NSDERIV_DERIV_iff [symmetric] del: realpow_Suc)

text{*Derivative of inverse*}
lemma DERIV_inverse_fun: "[| DERIV f x :> d; f(x) \<noteq> 0 |]
      ==> DERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ Suc (Suc 0))))"
apply (simp only: mult_commute [of d] minus_mult_left power_inverse)
apply (fold o_def)
apply (blast intro!: DERIV_chain DERIV_inverse)
done

lemma NSDERIV_inverse_fun: "[| NSDERIV f x :> d; f(x) \<noteq> 0 |]
      ==> NSDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ Suc (Suc 0))))"
by (simp add: NSDERIV_DERIV_iff DERIV_inverse_fun del: realpow_Suc)

text{*Derivative of quotient*}
lemma DERIV_quotient: "[| DERIV f x :> d; DERIV g x :> e; g(x) \<noteq> 0 |]
       ==> DERIV (%y. f(y) / (g y)) x :> (d*g(x) + -(e*f(x))) / (g(x) ^ Suc (Suc 0))"
apply (drule_tac f = g in DERIV_inverse_fun)
apply (drule_tac [2] DERIV_mult)
apply (assumption+)
apply (simp add: divide_inverse right_distrib power_inverse minus_mult_left
                 mult_ac 
     del: realpow_Suc minus_mult_right [symmetric] minus_mult_left [symmetric])
done

lemma NSDERIV_quotient: "[| NSDERIV f x :> d; DERIV g x :> e; g(x) \<noteq> 0 |]
       ==> NSDERIV (%y. f(y) / (g y)) x :> (d*g(x)
                            + -(e*f(x))) / (g(x) ^ Suc (Suc 0))"
by (simp add: NSDERIV_DERIV_iff DERIV_quotient del: realpow_Suc)

(* ------------------------------------------------------------------------ *)
(* Caratheodory formulation of derivative at a point: standard proof        *)
(* ------------------------------------------------------------------------ *)

lemma CARAT_DERIV:
     "(DERIV f x :> l) =
      (\<exists>g. (\<forall>z. f z - f x = g z * (z-x)) & isCont g x & g x = l)"
      (is "?lhs = ?rhs")
proof
  assume der: "DERIV f x :> l"
  show "\<exists>g. (\<forall>z. f z - f x = g z * (z-x)) \<and> isCont g x \<and> g x = l"
  proof (intro exI conjI)
    let ?g = "(%z. if z = x then l else (f z - f x) / (z-x))"
    show "\<forall>z. f z - f x = ?g z * (z-x)" by simp
    show "isCont ?g x" using der 
      by (simp add: isCont_iff DERIV_iff diff_minus 
               cong: LIM_equal [rule_format])
    show "?g x = l" by simp
  qed
next
  assume "?rhs"
  then obtain g where 
    "(\<forall>z. f z - f x = g z * (z-x))" and "isCont g x" and "g x = l" by blast
  thus "(DERIV f x :> l)" 
     by (auto simp add: isCont_iff DERIV_iff diff_minus 
               cong: LIM_equal [rule_format])
qed


lemma CARAT_NSDERIV: "NSDERIV f x :> l ==>
      \<exists>g. (\<forall>z. f z - f x = g z * (z-x)) & isNSCont g x & g x = l"
by (auto simp add: NSDERIV_DERIV_iff isNSCont_isCont_iff CARAT_DERIV)

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

(*--------------------------------------------------------------------------*)
(* Lemmas about nested intervals and proof by bisection (cf.Harrison)       *)
(* All considerably tidied by lcp                                           *)
(*--------------------------------------------------------------------------*)

lemma lemma_f_mono_add [rule_format (no_asm)]: "(\<forall>n. (f::nat=>real) n \<le> f (Suc n)) --> f m \<le> f(m + no)"
apply (induct_tac "no")
apply (auto intro: order_trans)
done

lemma f_inc_g_dec_Beq_f: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> Bseq f"
apply (rule_tac k = "f 0" and K = "g 0" in BseqI2, rule allI)
apply (induct_tac "n")
apply (auto intro: order_trans)
apply (rule_tac y = "g (Suc na) " in order_trans)
apply (induct_tac [2] "na")
apply (auto intro: order_trans)
done

lemma f_inc_g_dec_Beq_g: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> Bseq g"
apply (subst Bseq_minus_iff [symmetric])
apply (rule_tac g = "%x. - (f x) " in f_inc_g_dec_Beq_f)
apply auto
done

lemma f_inc_imp_le_lim: "[| \<forall>n. f n \<le> f (Suc n);  convergent f |] ==> f n \<le> lim f"
apply (rule linorder_not_less [THEN iffD1])
apply (auto simp add: convergent_LIMSEQ_iff LIMSEQ_iff monoseq_Suc)
apply (drule real_less_sum_gt_zero)
apply (drule_tac x = "f n + - lim f" in spec, safe)
apply (drule_tac P = "%na. no\<le>na --> ?Q na" and x = "no + n" in spec, auto)
apply (subgoal_tac "lim f \<le> f (no + n) ")
apply (induct_tac [2] "no")
apply (auto intro: order_trans simp add: diff_minus real_abs_def)
apply (drule_tac no=no and m=n in lemma_f_mono_add)
apply (auto simp add: add_commute)
done

lemma lim_uminus: "convergent g ==> lim (%x. - g x) = - (lim g)"
apply (rule LIMSEQ_minus [THEN limI])
apply (simp add: convergent_LIMSEQ_iff)
done

lemma g_dec_imp_lim_le: "[| \<forall>n. g(Suc n) \<le> g(n);  convergent g |] ==> lim g \<le> g n"
apply (subgoal_tac "- (g n) \<le> - (lim g) ")
apply (cut_tac [2] f = "%x. - (g x) " in f_inc_imp_le_lim)
apply (auto simp add: lim_uminus convergent_minus_iff [symmetric])
done

lemma lemma_nest: "[| \<forall>n. f(n) \<le> f(Suc n);
         \<forall>n. g(Suc n) \<le> g(n);
         \<forall>n. f(n) \<le> g(n) |]
      ==> \<exists>l m. l \<le> m &  ((\<forall>n. f(n) \<le> l) & f ----> l) &
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
      ==> \<exists>l. ((\<forall>n. f(n) \<le> l) & f ----> l) &
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
apply auto
apply (drule_tac f = "%u. (1/2) *u" in arg_cong)
apply auto
done

lemma Bolzano_bisect_diff:
     "a \<le> b ==>
      snd(Bolzano_bisect P a b n) - fst(Bolzano_bisect P a b n) =
      (b-a) / (2 ^ n)"
apply (induct_tac "n")
apply (auto simp add: eq_divide_2_times_iff add_divide_distrib Let_def split_def)
apply (auto simp add: add_ac Bolzano_bisect_le diff_minus)
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
apply (rule_tac y = "abs (fst (Bolzano_bisect P a b (no + noa)) - l) + abs (snd (Bolzano_bisect P a b (no + noa)) - l) " in order_le_less_trans)
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


subsection{*Intermediate Value Theorem: Prove Contrapositive by Bisection*}

lemma IVT: "[| f(a) \<le> y; y \<le> f(b);
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
apply (drule_tac P = "%r. ?P r --> (\<exists>s. 0<s & ?Q r s) " and x = "\<bar>y - f x\<bar> " in spec)
apply safe
apply simp
apply (drule_tac x = s in spec, clarify)
apply (cut_tac x = "f x" and y = y in linorder_less_linear, safe)
apply (drule_tac x = "ba-x" in spec)
apply (simp_all add: abs_if)
apply (drule_tac x = "aa-x" in spec)
apply (case_tac "x \<le> aa", simp_all)
apply (drule_tac x = x and y = aa in order_antisym)
apply (assumption, simp)
done

lemma IVT2: "[| f(b) \<le> y; y \<le> f(a);
         a \<le> b;
         (\<forall>x. a \<le> x & x \<le> b --> isCont f x)
      |] ==> \<exists>x. a \<le> x & x \<le> b & f(x) = y"
apply (subgoal_tac "- f a \<le> -y & -y \<le> - f b", clarify) 
apply (drule IVT [where f = "%x. - f x"], assumption)
apply (auto intro: isCont_minus)
done

(*HOL style here: object-level formulations*)
lemma IVT_objl: "(f(a) \<le> y & y \<le> f(b) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
apply (blast intro: IVT)
done

lemma IVT2_objl: "(f(b) \<le> y & y \<le> f(a) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
apply (blast intro: IVT2)
done

(*---------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above     *)
(*---------------------------------------------------------------------------*)


lemma isCont_bounded:
     "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
      ==> \<exists>M. \<forall>x. a \<le> x & x \<le> b --> f(x) \<le> M"
apply (cut_tac P = "% (u,v) . a \<le> u & u \<le> v & v \<le> b --> (\<exists>M. \<forall>x. u \<le> x & x \<le> v --> f x \<le> M) " in lemma_BOLZANO2)
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
apply (auto simp add: abs_ge_self, arith+)
done

(*----------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                         *)
(*----------------------------------------------------------------------------*)

lemma lemma_reals_complete: "((\<exists>x. x \<in> S) & (\<exists>y. isUb UNIV S (y::real))) -->
      (\<exists>t. isLub UNIV S t)"
apply (blast intro: reals_complete)
done

lemma isCont_has_Ub: "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
         ==> \<exists>M. (\<forall>x. a \<le> x & x \<le> b --> f(x) \<le> M) &
                   (\<forall>N. N < M --> (\<exists>x. a \<le> x & x \<le> b & N < f(x)))"
apply (cut_tac S = "Collect (%y. \<exists>x. a \<le> x & x \<le> b & y = f x) " in lemma_reals_complete)
apply auto
apply (drule isCont_bounded, assumption)
apply (auto simp add: isUb_def leastP_def isLub_def setge_def setle_def)
apply (rule exI, auto)
apply (auto dest!: spec simp add: linorder_not_less) 
done

(*----------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                   *)
(*----------------------------------------------------------------------------*)

lemma isCont_eq_Ub:
  assumes le: "a \<le> b"
      and con: "\<forall>x. a \<le> x & x \<le> b --> isCont f x"
  shows "\<exists>M. (\<forall>x. a \<le> x & x \<le> b --> f(x) \<le> M) &
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
        by (auto simp add: linorder_not_le [symmetric] intro: order_antisym)
      hence "\<forall>x. a \<le> x & x \<le> b --> isCont (%x. inverse (M - f x)) x"
        by (auto simp add: isCont_inverse isCont_diff con)
      from isCont_bounded [OF le this]
      obtain k where k: "!!x. a \<le> x & x \<le> b --> inverse (M - f x) \<le> k" by auto
      have Minv: "!!x. a \<le> x & x \<le> b --> 0 < inverse (M - f (x))"
        by (simp add: M3) 
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



(*----------------------------------------------------------------------------*)
(* Same theorem for lower bound                                               *)
(*----------------------------------------------------------------------------*)

lemma isCont_eq_Lb: "[| a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
         ==> \<exists>M. (\<forall>x. a \<le> x & x \<le> b --> M \<le> f(x)) &
                   (\<exists>x. a \<le> x & x \<le> b & f(x) = M)"
apply (subgoal_tac "\<forall>x. a \<le> x & x \<le> b --> isCont (%x. - (f x)) x")
prefer 2 apply (blast intro: isCont_minus)
apply (drule_tac f = " (%x. - (f x))" in isCont_eq_Ub)
apply safe
apply auto
done


(* ------------------------------------------------------------------------- *)
(* Another version.                                                          *)
(* ------------------------------------------------------------------------- *)

lemma isCont_Lb_Ub: "[|a \<le> b; \<forall>x. a \<le> x & x \<le> b --> isCont f x |]
      ==> \<exists>L M. (\<forall>x. a \<le> x & x \<le> b --> L \<le> f(x) & f(x) \<le> M) &
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

(*----------------------------------------------------------------------------*)
(* If f'(x) > 0 then x is locally strictly increasing at the right            *)
(*----------------------------------------------------------------------------*)

lemma DERIV_left_inc:
    "[| DERIV f x :> l;  0 < l |]
     ==> \<exists>d. 0 < d & (\<forall>h. 0 < h & h < d --> f(x) < f(x + h))"
apply (simp add: deriv_def LIM_def)
apply (drule spec, auto)
apply (rule_tac x = s in exI, auto)
apply (subgoal_tac "0 < l*h")
 prefer 2 apply (simp add: zero_less_mult_iff)
apply (drule_tac x = h in spec)
apply (simp add: real_abs_def pos_le_divide_eq pos_less_divide_eq 
            split add: split_if_asm)
done

lemma DERIV_left_dec:
  assumes der: "DERIV f x :> l"
      and l:   "l < 0"
  shows "\<exists>d. 0 < d & (\<forall>h. 0 < h & h < d --> f(x) < f(x-h))"
proof -
  from l der [THEN DERIV_D, THEN LIM_D [where r = "-l"]]
  have "\<exists>s. 0 < s \<and>
              (\<forall>z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < -l)"
    by (simp add: diff_minus)
  then obtain s
        where s:   "0 < s" 
          and all: "!!z. z \<noteq> 0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>(f(x+z) - f x) / z - l\<bar> < -l"
    by auto
  thus ?thesis
  proof (intro exI conjI strip)
    show "0<s" .
    fix h::real
    assume "0 < h \<and> h < s"
    with all [of "-h"] show "f x < f (x-h)" 
    proof (simp add: real_abs_def pos_less_divide_eq diff_minus [symmetric] 
		split add: split_if_asm)
      assume "~ l \<le> - ((f (x-h) - f x) / h)" and h: "0 < h" 
      with l 
      have "0 < (f (x-h) - f x) / h" by arith
      thus "f x < f (x-h)"
	by (simp add: pos_less_divide_eq h)
    qed
  qed
qed

lemma DERIV_local_max: 
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
             and lt: "\<forall>h. 0 < h \<and> h < d' \<longrightarrow> f x < f (x-h)" by blast
  from real_lbound_gt_zero [OF d d']
  obtain e where "0 < e \<and> e < d \<and> e < d'" ..
  with lt le [THEN spec [where x="x-e"]] 
  show ?thesis by (auto simp add: abs_if)
next
  case greater
  from DERIV_left_inc [OF der greater]
  obtain d' where d': "0 < d'"
             and lt: "\<forall>h. 0 < h \<and> h < d' \<longrightarrow> f x < f (x + h)" by blast
  from real_lbound_gt_zero [OF d d']
  obtain e where "0 < e \<and> e < d \<and> e < d'" ..
  with lt le [THEN spec [where x="x+e"]]
  show ?thesis by (auto simp add: abs_if)
qed


text{*Similar theorem for a local minimum*}
lemma DERIV_local_min:
     "[| DERIV f x :> l; 0 < d; \<forall>y. \<bar>x-y\<bar> < d --> f(x) \<le> f(y) |] ==> l = 0"
by (drule DERIV_minus [THEN DERIV_local_max], auto)


text{*In particular, if a function is locally flat*}
lemma DERIV_local_const:
     "[| DERIV f x :> l; 0 < d; \<forall>y. \<bar>x-y\<bar> < d --> f(x) = f(y) |] ==> l = 0"
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
        simp add: right_diff_distrib, simp add: left_diff_distrib)
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
    show "f b - f a = (b - a) * ((f b - f a)/(b-a))" by simp
    show "DERIV f z :> ((f b - f a)/(b-a))"  using derF by simp
  qed
qed


text{*A function is constant if its derivative is 0 over an interval.*}

lemma DERIV_isconst_end: "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0 |]
        ==> (f b = f a)"
apply (drule MVT, assumption)
apply (blast intro: differentiableI)
apply (auto dest!: DERIV_unique simp add: diff_eq_eq)
done

lemma DERIV_isconst1: "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0 |]
        ==> \<forall>x. a \<le> x & x \<le> b --> f x = f a"
apply safe
apply (drule_tac x = a in order_le_imp_less_or_eq, safe)
apply (drule_tac b = x in DERIV_isconst_end, auto)
done

lemma DERIV_isconst2: "[| a < b;
         \<forall>x. a \<le> x & x \<le> b --> isCont f x;
         \<forall>x. a < x & x < b --> DERIV f x :> 0;
         a \<le> x; x \<le> b |]
        ==> f x = f a"
apply (blast dest: DERIV_isconst1)
done

lemma DERIV_isconst_all: "\<forall>x. DERIV f x :> 0 ==> f(x) = f(y)"
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
apply (auto dest!: DERIV_const_ratio_const simp add: real_mult_assoc)
done

lemma real_average_minus_first: "((a + b) /2 - a) = (b-a)/(2::real)"
by auto
declare real_average_minus_first [simp]

lemma real_average_minus_second: "((b + a)/2 - a) = (b-a)/(2::real)"
by auto
declare real_average_minus_second [simp]

text{*Gallileo's "trick": average velocity = av. of end velocities*}

lemma DERIV_const_average:
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
     "[|0 < d; \<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z;
        \<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z |]
      ==> \<exists>z. \<bar>z-x\<bar> \<le> d & f z < f x"
apply (insert lemma_isCont_inj
          [where f = "%x. - f x" and g = "%y. g(-y)" and x = x and d = d])
apply (simp add: isCont_minus linorder_not_le) 
done

text{*Show there's an interval surrounding @{term "f(x)"} in 
@{text "f[[x - d, x + d]]"} .*}

lemma isCont_inj_range: 
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "\<exists>e. 0<e & (\<forall>y. \<bar>y - f x\<bar> \<le> e --> (\<exists>z. \<bar>z-x\<bar> \<le> d & f z = y))"
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
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d --> g(f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d --> isCont f z"
  shows "isCont g (f x)"
proof (simp add: isCont_iff LIM_eq)
  show "\<forall>r. 0 < r \<longrightarrow>
         (\<exists>s. 0<s \<and> (\<forall>z. z\<noteq>0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>g(f x + z) - g(f x)\<bar> < r))"
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
    show "\<exists>s. 0<s \<and> (\<forall>z. z\<noteq>0 \<and> \<bar>z\<bar> < s \<longrightarrow> \<bar>g(f x + z) - g(f x)\<bar> < r)"
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

ML
{*
val LIM_def = thm"LIM_def";
val NSLIM_def = thm"NSLIM_def";
val isCont_def = thm"isCont_def";
val isNSCont_def = thm"isNSCont_def";
val deriv_def = thm"deriv_def";
val nsderiv_def = thm"nsderiv_def";
val differentiable_def = thm"differentiable_def";
val NSdifferentiable_def = thm"NSdifferentiable_def";
val increment_def = thm"increment_def";
val isUCont_def = thm"isUCont_def";
val isNSUCont_def = thm"isNSUCont_def";

val half_gt_zero_iff = thm "half_gt_zero_iff";
val half_gt_zero = thms "half_gt_zero";
val abs_diff_triangle_ineq = thm "abs_diff_triangle_ineq";
val LIM_eq = thm "LIM_eq";
val LIM_D = thm "LIM_D";
val LIM_const = thm "LIM_const";
val LIM_add = thm "LIM_add";
val LIM_minus = thm "LIM_minus";
val LIM_add_minus = thm "LIM_add_minus";
val LIM_diff = thm "LIM_diff";
val LIM_const_not_eq = thm "LIM_const_not_eq";
val LIM_const_eq = thm "LIM_const_eq";
val LIM_unique = thm "LIM_unique";
val LIM_mult_zero = thm "LIM_mult_zero";
val LIM_self = thm "LIM_self";
val LIM_equal = thm "LIM_equal";
val LIM_trans = thm "LIM_trans";
val LIM_NSLIM = thm "LIM_NSLIM";
val NSLIM_LIM = thm "NSLIM_LIM";
val LIM_NSLIM_iff = thm "LIM_NSLIM_iff";
val NSLIM_mult = thm "NSLIM_mult";
val LIM_mult2 = thm "LIM_mult2";
val NSLIM_add = thm "NSLIM_add";
val LIM_add2 = thm "LIM_add2";
val NSLIM_const = thm "NSLIM_const";
val LIM_const2 = thm "LIM_const2";
val NSLIM_minus = thm "NSLIM_minus";
val LIM_minus2 = thm "LIM_minus2";
val NSLIM_add_minus = thm "NSLIM_add_minus";
val LIM_add_minus2 = thm "LIM_add_minus2";
val NSLIM_inverse = thm "NSLIM_inverse";
val LIM_inverse = thm "LIM_inverse";
val NSLIM_zero = thm "NSLIM_zero";
val LIM_zero2 = thm "LIM_zero2";
val NSLIM_zero_cancel = thm "NSLIM_zero_cancel";
val LIM_zero_cancel = thm "LIM_zero_cancel";
val NSLIM_not_zero = thm "NSLIM_not_zero";
val NSLIM_const_not_eq = thm "NSLIM_const_not_eq";
val NSLIM_const_eq = thm "NSLIM_const_eq";
val NSLIM_unique = thm "NSLIM_unique";
val LIM_unique2 = thm "LIM_unique2";
val NSLIM_mult_zero = thm "NSLIM_mult_zero";
val LIM_mult_zero2 = thm "LIM_mult_zero2";
val NSLIM_self = thm "NSLIM_self";
val isNSContD = thm "isNSContD";
val isNSCont_NSLIM = thm "isNSCont_NSLIM";
val NSLIM_isNSCont = thm "NSLIM_isNSCont";
val isNSCont_NSLIM_iff = thm "isNSCont_NSLIM_iff";
val isNSCont_LIM_iff = thm "isNSCont_LIM_iff";
val isNSCont_isCont_iff = thm "isNSCont_isCont_iff";
val isCont_isNSCont = thm "isCont_isNSCont";
val isNSCont_isCont = thm "isNSCont_isCont";
val NSLIM_h_iff = thm "NSLIM_h_iff";
val NSLIM_isCont_iff = thm "NSLIM_isCont_iff";
val LIM_isCont_iff = thm "LIM_isCont_iff";
val isCont_iff = thm "isCont_iff";
val isCont_add = thm "isCont_add";
val isCont_mult = thm "isCont_mult";
val isCont_o = thm "isCont_o";
val isCont_o2 = thm "isCont_o2";
val isNSCont_minus = thm "isNSCont_minus";
val isCont_minus = thm "isCont_minus";
val isCont_inverse = thm "isCont_inverse";
val isNSCont_inverse = thm "isNSCont_inverse";
val isCont_diff = thm "isCont_diff";
val isCont_const = thm "isCont_const";
val isNSCont_const = thm "isNSCont_const";
val isNSCont_rabs = thm "isNSCont_rabs";
val isCont_rabs = thm "isCont_rabs";
val isNSUContD = thm "isNSUContD";
val isUCont_isCont = thm "isUCont_isCont";
val isUCont_isNSUCont = thm "isUCont_isNSUCont";
val isNSUCont_isUCont = thm "isNSUCont_isUCont";
val DERIV_iff = thm "DERIV_iff";
val DERIV_NS_iff = thm "DERIV_NS_iff";
val DERIV_D = thm "DERIV_D";
val NS_DERIV_D = thm "NS_DERIV_D";
val DERIV_unique = thm "DERIV_unique";
val NSDeriv_unique = thm "NSDeriv_unique";
val differentiableD = thm "differentiableD";
val differentiableI = thm "differentiableI";
val NSdifferentiableD = thm "NSdifferentiableD";
val NSdifferentiableI = thm "NSdifferentiableI";
val LIM_I = thm "LIM_I";
val DERIV_LIM_iff = thm "DERIV_LIM_iff";
val DERIV_iff2 = thm "DERIV_iff2";
val NSDERIV_NSLIM_iff = thm "NSDERIV_NSLIM_iff";
val NSDERIV_NSLIM_iff2 = thm "NSDERIV_NSLIM_iff2";
val NSDERIV_iff2 = thm "NSDERIV_iff2";
val hypreal_not_eq_minus_iff = thm "hypreal_not_eq_minus_iff";
val NSDERIVD5 = thm "NSDERIVD5";
val NSDERIVD4 = thm "NSDERIVD4";
val NSDERIVD3 = thm "NSDERIVD3";
val NSDERIV_DERIV_iff = thm "NSDERIV_DERIV_iff";
val NSDERIV_isNSCont = thm "NSDERIV_isNSCont";
val DERIV_isCont = thm "DERIV_isCont";
val NSDERIV_const = thm "NSDERIV_const";
val DERIV_const = thm "DERIV_const";
val NSDERIV_add = thm "NSDERIV_add";
val DERIV_add = thm "DERIV_add";
val NSDERIV_mult = thm "NSDERIV_mult";
val DERIV_mult = thm "DERIV_mult";
val NSDERIV_cmult = thm "NSDERIV_cmult";
val DERIV_cmult = thm "DERIV_cmult";
val NSDERIV_minus = thm "NSDERIV_minus";
val DERIV_minus = thm "DERIV_minus";
val NSDERIV_add_minus = thm "NSDERIV_add_minus";
val DERIV_add_minus = thm "DERIV_add_minus";
val NSDERIV_diff = thm "NSDERIV_diff";
val DERIV_diff = thm "DERIV_diff";
val incrementI = thm "incrementI";
val incrementI2 = thm "incrementI2";
val increment_thm = thm "increment_thm";
val increment_thm2 = thm "increment_thm2";
val increment_approx_zero = thm "increment_approx_zero";
val NSDERIV_zero = thm "NSDERIV_zero";
val NSDERIV_approx = thm "NSDERIV_approx";
val NSDERIVD1 = thm "NSDERIVD1";
val NSDERIVD2 = thm "NSDERIVD2";
val NSDERIV_chain = thm "NSDERIV_chain";
val DERIV_chain = thm "DERIV_chain";
val DERIV_chain2 = thm "DERIV_chain2";
val NSDERIV_Id = thm "NSDERIV_Id";
val DERIV_Id = thm "DERIV_Id";
val isCont_Id = thms "isCont_Id";
val DERIV_cmult_Id = thm "DERIV_cmult_Id";
val NSDERIV_cmult_Id = thm "NSDERIV_cmult_Id";
val DERIV_pow = thm "DERIV_pow";
val NSDERIV_pow = thm "NSDERIV_pow";
val NSDERIV_inverse = thm "NSDERIV_inverse";
val DERIV_inverse = thm "DERIV_inverse";
val DERIV_inverse_fun = thm "DERIV_inverse_fun";
val NSDERIV_inverse_fun = thm "NSDERIV_inverse_fun";
val DERIV_quotient = thm "DERIV_quotient";
val NSDERIV_quotient = thm "NSDERIV_quotient";
val CARAT_DERIV = thm "CARAT_DERIV";
val CARAT_NSDERIV = thm "CARAT_NSDERIV";
val hypreal_eq_minus_iff3 = thm "hypreal_eq_minus_iff3";
val starfun_if_eq = thm "starfun_if_eq";
val CARAT_DERIVD = thm "CARAT_DERIVD";
val f_inc_g_dec_Beq_f = thm "f_inc_g_dec_Beq_f";
val f_inc_g_dec_Beq_g = thm "f_inc_g_dec_Beq_g";
val f_inc_imp_le_lim = thm "f_inc_imp_le_lim";
val lim_uminus = thm "lim_uminus";
val g_dec_imp_lim_le = thm "g_dec_imp_lim_le";
val Bolzano_bisect_le = thm "Bolzano_bisect_le";
val Bolzano_bisect_fst_le_Suc = thm "Bolzano_bisect_fst_le_Suc";
val Bolzano_bisect_Suc_le_snd = thm "Bolzano_bisect_Suc_le_snd";
val eq_divide_2_times_iff = thm "eq_divide_2_times_iff";
val Bolzano_bisect_diff = thm "Bolzano_bisect_diff";
val Bolzano_nest_unique = thms "Bolzano_nest_unique";
val not_P_Bolzano_bisect = thm "not_P_Bolzano_bisect";
val not_P_Bolzano_bisect = thm "not_P_Bolzano_bisect";
val lemma_BOLZANO2 = thm "lemma_BOLZANO2";
val IVT = thm "IVT";
val IVT2 = thm "IVT2";
val IVT_objl = thm "IVT_objl";
val IVT2_objl = thm "IVT2_objl";
val isCont_bounded = thm "isCont_bounded";
val isCont_has_Ub = thm "isCont_has_Ub";
val isCont_eq_Ub = thm "isCont_eq_Ub";
val isCont_eq_Lb = thm "isCont_eq_Lb";
val isCont_Lb_Ub = thm "isCont_Lb_Ub";
val DERIV_left_inc = thm "DERIV_left_inc";
val DERIV_left_dec = thm "DERIV_left_dec";
val DERIV_local_max = thm "DERIV_local_max";
val DERIV_local_min = thm "DERIV_local_min";
val DERIV_local_const = thm "DERIV_local_const";
val Rolle = thm "Rolle";
val MVT = thm "MVT";
val DERIV_isconst_end = thm "DERIV_isconst_end";
val DERIV_isconst1 = thm "DERIV_isconst1";
val DERIV_isconst2 = thm "DERIV_isconst2";
val DERIV_isconst_all = thm "DERIV_isconst_all";
val DERIV_const_ratio_const = thm "DERIV_const_ratio_const";
val DERIV_const_ratio_const2 = thm "DERIV_const_ratio_const2";
val real_average_minus_first = thm "real_average_minus_first";
val real_average_minus_second = thm "real_average_minus_second";
val DERIV_const_average = thm "DERIV_const_average";
val isCont_inj_range = thm "isCont_inj_range";
val isCont_inverse_function = thm "isCont_inverse_function";
*}


end

