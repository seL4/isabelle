theory Barith = Presburger
files ("barith.ML") :

lemma imp_commute: "(PROP P ==> PROP Q
==> PROP R) == (PROP Q ==>
PROP P ==> PROP R)"
proof
  assume h1: "PROP P \<Longrightarrow> PROP Q \<Longrightarrow>
PROP R"
  assume h2: "PROP Q"
  assume h3: "PROP P"
  from h3 h2 show "PROP R" by (rule h1)
next
  assume h1: "PROP Q \<Longrightarrow> PROP P \<Longrightarrow>
PROP R"
 assume h2: "PROP P"
  assume h3: "PROP Q"
  from h3 h2 show "PROP R" by (rule h1)
qed

lemma imp_simplify: "(PROP P \<Longrightarrow> PROP P
\<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow>
PROP Q)"
proof
  assume h1: "PROP P \<Longrightarrow> PROP P \<Longrightarrow>
PROP Q"
  assume h2: "PROP P"
  from h2 h2 show "PROP Q" by (rule h1)
next
  assume h: "PROP P \<Longrightarrow> PROP Q"
  assume "PROP P"
  then show "PROP Q" by (rule h)
qed


(* Abstraction of constants *)
lemma abs_const: "(x::int) <= x \<and> x <= x"
by simp

(* Abstraction of Variables *)
lemma abs_var: "l <= (x::int) \<and> x <= u \<Longrightarrow> l <= (x::int) \<and> x <= u"
by simp


(* Unary operators *)
lemma abs_neg: "l <= (x::int) \<and> x <= u \<Longrightarrow>  -u <= -x \<and> -x <= -l"
by arith


(* Binary operations *)
(* Addition*)
lemma abs_add: "\<lbrakk> l1 <= (x1::int) \<and> x1 <= u1 ; l2 <= (x2::int) \<and> x2 <= u2\<rbrakk> 
  \<Longrightarrow>  l1 + l2 <= x1 + x2 \<and> x1 + x2 <= u1 + u2"
by arith

lemma abs_sub: "\<lbrakk> l1 <= (x1::int) \<and> x1 <= u1 ; l2 <= (x2::int) \<and> x2 <= u2\<rbrakk> 
  \<Longrightarrow>  l1 - u2 <= x1 - x2 \<and> x1 - x2 <= u1 - l2"
by arith

lemma abs_sub_x: "l <= (x::int) \<and> x <= u \<Longrightarrow> 0 <= x - x \<and> x - x <= 0"
by arith

(* For resolving the last step*)
lemma subinterval: "\<lbrakk>l <= (e::int) \<and> e <= u ; l' <= l ; u <= u' \<rbrakk>
  \<Longrightarrow> l' <= e \<and> e <= u'"
by arith

lemma min_max_minus : "min (-a ::int) (-b) = - max a b"
by arith

lemma max_min_minus : " max (-a ::int) (-b) = - min a b"
by arith

lemma max_max_commute : "max (max (a::int) b) (max c d) = max (max a c) (max b d)"
by arith

lemma min_min_commute : "min (min (a::int) b) (min c d) = min (min a c) (min b d)"
by arith

lemma zintervals_min: "\<lbrakk> l1 <= (x1::int) \<and> x1<= u1 ; l2 <= x2 \<and> x2 <= u2 \<rbrakk> 
  \<Longrightarrow> min l1 l2 <= x1 \<and> x1 <= max u1 u2" by arith

lemma zmult_zle_mono: "(i::int) \<le> j \<Longrightarrow> 0 \<le> k \<Longrightarrow> k * i \<le> k * j"
  apply (erule order_le_less [THEN iffD1, THEN disjE, of "0::int"])
  apply (erule order_le_less [THEN iffD1, THEN disjE])
  apply (rule order_less_imp_le)
  apply (rule zmult_zless_mono2)
  apply simp_all
  done
  
lemma zmult_mono:
  assumes l1_pos : "0 <= l1"
  and l2_pos : "0 <= l2"
  and l1_le : "l1 <= (x1::int)"
  and l2_le : "l2 <= (x2::int)"
  shows "l1*l2 <= x1*x2"
proof -
  from l1_pos and l1_le have x1_pos: "0 \<le> x1" by (rule order_trans)
  from l1_le and l2_pos
  have "l2 * l1 \<le> l2 * x1" by (rule zmult_zle_mono)
  then have "l1 * l2 \<le> x1 * l2" by (simp add: mult_ac)
  also from l2_le and x1_pos
  have "x1 * l2 \<le> x1 * x2" by (rule zmult_zle_mono)
  finally show ?thesis .
qed

lemma zinterval_lposlpos:
  assumes x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     l1_pos : "0 <= l1"
  and     l2_pos : "0 <= l2"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
proof-
  from x1_lu have l1_le : "l1 <= x1" by simp
  from x1_lu have x1_le : "x1 <= u1" by simp
  from x2_lu have l2_le : "l2 <= x2" by simp
  from x2_lu have x2_le : "x2 <= u2" by simp
  from x1_lu have l1_leu : "l1 <= u1" by arith
  from x2_lu have l2_leu : "l2 <= u2" by arith
  from l1_pos l2_pos l1_le l2_le 
  have l1l2_le : "l1*l2 <= x1*x2" by (simp add: zmult_mono)
  from l1_pos x1_lu have x1_pos : "0 <= x1" by arith
  from l2_pos x2_lu have x2_pos : "0 <= x2" by arith
  from l1_pos x1_lu have u1_pos : "0 <= u1" by arith
  from l2_pos x2_lu have u2_pos : "0 <= u2" by arith
  from x1_pos x2_pos x1_le x2_le 
  have x1x2_le : "x1*x2 <= u1*u2" by (simp add: zmult_mono)
  from l2_leu l1_pos have l1l2_leu2 : "l1*l2 <= l1*u2" 
    by (simp add: zmult_zle_mono)
  from l1l2_leu2 have min1 : "l1*l2 = min (l1*l2) (l1*u2)" by arith
  from l2_leu u1_pos have u1l2_le : "u1*l2 <=u1*u2" by (simp add: zmult_zle_mono)
  from u1l2_le have min2 : "u1*l2 = min (u1*l2) (u1*u2)" by arith
  from l1_leu l2_pos have "l2*l1 <= l2*u1" by (simp add:zmult_zle_mono) 
  then have l1l2_le_u1l2 : "l1*l2 <= u1*l2" by (simp add: mult_ac)
  from min1 min2 l1l2_le_u1l2 have  min_th : 
    "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) = (l1*l2)" by arith
  from l1l2_leu2 have max1 : "l1*u2 = max (l1*l2) (l1*u2)" by arith
  from u1l2_le have max2 : "u1*u2 = max (u1*l2) (u1*u2)" by arith
  from l1_leu u2_pos have "u2*l1 <= u2*u1" by (simp add:zmult_zle_mono) 
  then have l1u2_le_u1u2 : "l1*u2 <= u1*u2" by (simp add: mult_ac)
  from max1 max2 l1u2_le_u1u2 have  max_th : 
    "max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2)) = (u1*u2)" by arith
  from min_th have min_th' :  "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= l1*l2" by arith
  from max_th have max_th' : "u1*u2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))" by arith
  from min_th' max_th' l1l2_le x1x2_le 
  show ?thesis by simp
qed

lemma min_le_I1 : "min (a::int) b <= a" by arith
lemma min_le_I2 : "min (a::int) b <= b" by arith
lemma zinterval_lneglpos :
  assumes  x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     l1_neg : "l1 <= 0"
  and x1_pos : "0 <= x1" 
  and     l2_pos : "0 <= l2"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"

proof-
    from x1_lu x1_pos have x1_0_u1 : "0 <= x1 \<and> x1 <= u1" by simp
    from l1_neg have ml1_pos : "0 <= -l1" by simp
    from x1_lu x1_pos have u1_pos : "0 <= u1" by arith
    from x2_lu l2_pos have u2_pos : "0 <= u2" by arith
    from x2_lu have l2_le_u2 : "l2 <= u2" by arith
    from l2_le_u2 u1_pos 
     have u1l2_le_u1u2 : "u1*l2 <= u1*u2" by (simp add: zmult_zle_mono)
    have trv_0 : "(0::int) <= 0" by simp
    have "0*0 <= u1*l2" 
      by (simp only: zmult_mono[OF trv_0 trv_0 u1_pos l2_pos])
    then have u1l2_pos : "0 <= u1*l2" by simp
      from l1_neg have ml1_pos : "0 <= -l1" by simp
      from ml1_pos l2_pos have "0*0 <= (-l1)*l2" 
	by (simp only: zmult_mono[OF trv_0 trv_0 ml1_pos l2_pos])
      then have "0 <= -(l1*l2)" by simp  
      then have "0 - (-(l1*l2)) <= 0" by arith 
      then
      have l1l2_neg : "l1*l2 <= 0" by simp
      from ml1_pos u2_pos have "0*0 <= (-l1)*u2" 
	by (simp only: zmult_mono[OF trv_0 trv_0 ml1_pos u2_pos])
      then have "0 <= -(l1*u2)" by simp  
      then have "0 - (-(l1*u2)) <= 0" by arith 
      then
      have l1u2_neg : "l1*u2 <= 0" by simp
      from l1l2_neg u1l2_pos have l1l2_le_u1l2: "l1*l2 <= u1*l2" by simp
      from l1u2_neg u1l2_pos have l1u2_le_u1l2 : "l1*u2 <= u1*l2" by simp
      from ml1_pos l2_le_u2 have "(-l1)*l2 <= (-l1)*u2"
	by (simp only: zmult_zle_mono) 
      then have l1u2_le_l1l2 : "l1*u2 <= l1*l2" by simp
      from l1u2_le_l1l2 l1l2_le_u1l2 u1l2_le_u1u2 
      have min1 : "l1*u2 = min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2))" 
	by arith
      from u1l2_pos u1l2_le_u1u2 have "0 = min (min (0 * l2) (0 * u2)) (min (u1 * l2) (u1 * u2))" by arith
      with l1u2_neg min1 have minth : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= min (min (0 * l2) (0 * u2)) (min (u1 * l2) (u1 * u2))" by simp
      from l1u2_le_l1l2 l1l2_le_u1l2 u1l2_le_u1u2 
      have max1 : "u1*u2 = max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))" 
	by arith
      from u1l2_pos u1l2_le_u1u2 have "u1*u2 = max (max (0 * l2) (0 * u2)) (max (u1 * l2) (u1 * u2))" by arith 
      with  max1 have "max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2)) = max (max (0 * l2) (0 * u2)) (max (u1 * l2) (u1 * u2))" by simp
      then have maxth : " max (max (0 * l2) (0 * u2)) (max (u1 * l2) (u1 * u2)) <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))" by simp
    have x1x2_0_u : "min (min (0 * l2) (0 * u2)) (min (u1 * l2) (u1 * u2)) <= x1 * x2 &
x1 * x2 <= max (max (0 * l2) (0 * u2)) (max (u1 * l2) (u1 * u2))" 
      by (simp only: zinterval_lposlpos[OF x1_0_u1 x2_lu trv_0 l2_pos],simp)
      from minth maxth x1x2_0_u show ?thesis by (simp add: subinterval[OF _ minth maxth])
qed

lemma zinterval_lneglneg :
  assumes  x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     l1_neg : "l1 <= 0"
  and     x1_pos : "0 <= x1" 
  and     l2_neg : "l2 <= 0"
  and     x2_pos : "0 <= x2"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"

proof-
    from x1_lu x1_pos have x1_0_u1 : "0 <= x1 \<and> x1 <= u1" by simp
    from l1_neg have ml1_pos : "0 <= -l1" by simp
    from l1_neg have l1_le0 : "l1 <= 0" by simp
    from x1_lu x1_pos have u1_pos : "0 <= u1" by arith
    from x2_lu x2_pos have x2_0_u2 : "0 <= x2 \<and> x2 <= u2" by simp
    from l2_neg have ml2_pos : "0 <= -l2" by simp
    from l2_neg have l2_le0 : "l2 <= 0" by simp
    from x2_lu x2_pos have u2_pos : "0 <= u2" by arith
    have trv_0 : "(0::int) <= 0" by simp

    have x1x2_th1 : 
      "min (min (l1 * 0) (l1 * u2)) (min (u1 * 0) (u1 * u2)) \<le> x1 * x2 \<and>
      x1 * x2 \<le> max (max (l1 * 0) (l1 * u2)) (max (u1 * 0) (u1 * u2))"
      by (rule_tac  zinterval_lneglpos[OF x1_lu x2_0_u2 l1_le0 x1_pos trv_0])
    
    have x1x2_eq_x2x1 : "x1*x2 = x2*x1" by (simp add: mult_ac)
    have
      "min (min (l2 * 0) (l2 * u1)) (min (u2 * 0) (u2 * u1)) \<le> x2 * x1 \<and>
      x2 * x1 \<le> max (max (l2 * 0) (l2 * u1)) (max (u2 * 0) (u2 * u1))"
      by (rule_tac  zinterval_lneglpos[OF x2_lu x1_0_u1 l2_le0 x2_pos trv_0])
    
    then have x1x2_th2 : 
      "min (min (l2 * 0) (l2 * u1)) (min (u2 * 0) (u2 * u1)) \<le> x1 * x2 \<and>
      x1 * x2 \<le> max (max (l2 * 0) (l2 * u1)) (max (u2 * 0) (u2 * u1))"
      by (simp add: x1x2_eq_x2x1)

    from x1x2_th1 x1x2_th2 have x1x2_th3:
      "min (min (min (l1 * 0) (l1 * u2)) (min (u1 * 0) (u1 * u2)))
      (min (min (l2 * 0) (l2 * u1)) (min (u2 * 0) (u2 * u1)))
      \<le> x1 * x2 \<and>
      x1 * x2
      \<le> max (max (max (l1 * 0) (l1 * u2)) (max (u1 * 0) (u1 * u2)))
      (max (max (l2 * 0) (l2 * u1)) (max (u2 * 0) (u2 * u1)))"
      by (rule_tac zintervals_min[OF x1x2_th1 x1x2_th2])

    from ml1_pos u2_pos 
    have "0*0 <= -l1*u2" 
      by (simp only: zmult_mono[OF trv_0 trv_0 ml1_pos u2_pos]) 
    then have l1u2_neg : "l1*u2 <= 0" by simp
    from l1u2_neg have min_l1u2_0 : "min (0) (l1*u2) = l1*u2" by arith
    from l1u2_neg have max_l1u2_0 : "max (0) (l1*u2) = 0" by arith
    from u1_pos u2_pos 
    have "0*0 <= u1*u2" 
      by (simp only: zmult_mono[OF trv_0 trv_0 u1_pos u2_pos]) 
    then have u1u2_pos :"0 <= u1*u2" by simp
    from u1u2_pos have min_0_u1u2 : "min 0 (u1*u2) = 0" by arith
    from u1u2_pos have max_0_u1u2 : "max 0 (u1*u2) = u1*u2" by arith
    from ml2_pos u1_pos have "0*0 <= -l2*u1" 
      by (simp only: zmult_mono[OF trv_0 trv_0 ml2_pos u1_pos]) 
    then have l2u1_neg : "l2*u1 <= 0" by simp
    from l2u1_neg have min_l2u1_0 : "min 0 (l2*u1) = l2*u1" by arith
    from l2u1_neg have max_l2u1_0 : "max 0 (l2*u1) = 0" by arith
    from min_l1u2_0 min_0_u1u2 min_l2u1_0 
    have min_th1: 
      " min (l2*u1) (l1*u2) <= min (min (min (l1 * 0) (l1 * u2)) (min (u1 * 0) (u1 * u2)))
      (min (min (l2 * 0) (l2 * u1)) (min (u2 * 0) (u2 * u1)))"
      by (simp add: min_commute mult_ac)
    from max_l1u2_0 max_0_u1u2 max_l2u1_0 
    have max_th1: "max (max (max (l1 * 0) (l1 * u2)) (max (u1 * 0) (u1 * u2)))
      (max (max (l2 * 0) (l2 * u1)) (max (u2 * 0) (u2 * u1))) <= u1*u2"
      by (simp add: max_commute mult_ac)
    have x1x2_th4: "min (l2*u1) (l1*u2) <= x1*x2 \<and> x1*x2 <= u1*u2" 
      by (rule_tac subinterval[OF x1x2_th3 min_th1 max_th1])
    
    have " min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) = min (min (l1*l2) (u1*u2)) (min (l1*u2) (l2*u1))" by (simp add: min_min_commute min_commute mult_ac) 
    moreover 
    have " min (min (l1*l2) (u1*u2)) (min (l1*u2) (l2*u1)) <= min (l1*u2) (l2*u1)" 
      by 
    (rule_tac min_le_I2 [of "(min (l1*l2) (u1*u2))" "(min (l1*u2) (l2*u1))"]) 
    ultimately have "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= min (l1*u2) (l2*u1)" by simp 
    then 
    have min_le1: "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <=min (l2*u1) (l1*u2)" 
      by (simp add: min_commute mult_ac)
    have "u1*u2 <= max (u1*l2) (u1*u2)" 
      by (rule_tac le_maxI2[of  "u1*u2" "u1*l2"]) 
    
    moreover have "max (u1*l2) (u1*u2) <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
      by(rule_tac le_maxI2[of "(max (u1*l2) (u1*u2))" "(max (l1*l2) (l1*u2))"])
    then 
    have max_le1:"u1*u2 <= max (max (l1 * l2) (l1 * u2)) (max (u1 * l2) (u1 * u2))" 
      by simp
    show ?thesis by (simp add: subinterval[OF x1x2_th4 min_le1 max_le1])
  qed

lemma zinterval_lpos:
  assumes x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     l1_pos: "0 <= l1"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
proof-
  from x1_lu have l1_le : "l1 <= x1" by simp
  from x1_lu have x1_le : "x1 <= u1" by simp
  from x2_lu have l2_le : "l2 <= x2" by simp
  from x2_lu have x2_le : "x2 <= u2" by simp
  from x1_lu have l1_leu : "l1 <= u1" by arith
  from x2_lu have l2_leu : "l2 <= u2" by arith
  have "(0 <= l2) \<or> (l2 < 0 \<and> 0<= x2) \<or> (x2 <0 \<and> 0 <= u2) \<or> (u2 <0)" by arith
  moreover
  {
    assume l2_pos: "0 <= l2"
    have ?thesis by (simp add: zinterval_lposlpos[OF x1_lu x2_lu l1_pos l2_pos])
  }
moreover
{
  assume  l2_neg : "l2 < 0" and x2_pos: "0<= x2"
  from l2_neg have l2_le_0 : "l2 <= 0" by arith
  thm zinterval_lneglpos[OF x2_lu x1_lu l2_le_0 x2_pos l1_pos]
have th1 : 
  "min (min (l2 * l1) (l2 * u1)) (min (u2 * l1) (u2 * u1)) \<le> x2 * x1 \<and>
  x2 * x1 \<le> max (max (l2 * l1) (l2 * u1)) (max (u2 * l1) (u2 * u1))" 
  by (simp add : zinterval_lneglpos[OF x2_lu x1_lu l2_le_0 x2_pos l1_pos])
have mth1 : "min (min (l2 * l1) (l2 * u1)) (min (u2 * l1) (u2 * u1)) = min (min (l1 * l2) (l1 * u2)) (min (u1 * l2) (u1 * u2))" 
  by (simp add: min_min_commute mult_ac)
have mth2: "max (max (l2 * l1) (l2 * u1)) (max (u2 * l1) (u2 * u1)) = max (max (l1 * l2) (l1 * u2)) (max (u1 * l2) (u1 * u2))"
  by (simp add: max_max_commute mult_ac)
have x1x2_th : "x2*x1 = x1*x2" by (simp add: mult_ac)
from th1 mth1 mth2 x1x2_th have 
   "min (min (l1 * l2) (l1 * u2)) (min (u1 * l2) (u1 * u2)) \<le> x1 * x2 \<and>
   x1 * x2 \<le> max (max (l1 * l2) (l1 * u2)) (max (u1 * l2) (u1 * u2))"
by auto
    then have ?thesis by simp 
}
moreover
{
  assume x2_neg : "x2 <0" and u2_pos : "0 <= u2"
  from x2_lu x2_neg have mx2_mu2_ml2 : "-u2 <= -x2 \<and> -x2 <= -l2" by simp
  from u2_pos have mu2_neg : "-u2 <= 0" by simp
  from x2_neg have mx2_pos : "0 <= -x2" by simp
thm zinterval_lneglpos[OF mx2_mu2_ml2 x1_lu mu2_neg mx2_pos l1_pos]
    have mx1x2_lu : 
"min (min (- u2 * l1) (- u2 * u1)) (min (- l2 * l1) (- l2 * u1))
\<le> - x2 * x1 \<and>
- x2 * x1 \<le> max (max (- u2 * l1) (- u2 * u1)) (max (- l2 * l1) (- l2 * u1))"      
      by (simp only: zinterval_lneglpos [OF  mx2_mu2_ml2 x1_lu mu2_neg mx2_pos l1_pos],simp)
    have min_eq_mmax : 
      "min (min (- u2 * l1) (- u2 * u1)) (min (- l2 * l1) (- l2 * u1)) = 
      - max (max (u2 * l1) (u2 * u1)) (max (l2 * l1) (l2 * u1))" 
      by (simp add: min_max_minus max_min_minus)
    have max_eq_mmin : 
      " max (max (- u2 * l1) (- u2 * u1)) (max (- l2 * l1) (- l2 * u1)) = 
      -min (min (u2 * l1) (u2 * u1)) (min (l2 * l1) (l2 * u1))"
      by (simp add: min_max_minus max_min_minus)
    from mx1x2_lu min_eq_mmax max_eq_mmin 
    have "- max (max (u2 * l1) (u2 * u1)) (max (l2 * l1) (l2 * u1))<= - x1 * x2 &
      - x1*x2 <=  -min (min (u2 * l1) (u2 * u1)) (min (l2 * l1) (l2 * u1))" by (simp add: mult_ac)
 then have ?thesis by (simp add: min_min_commute min_commute max_commute max_max_commute mult_ac) 

}
moreover
{
  assume u2_neg : "u2 < 0"
  from x2_lu have mx2_lu : "-u2 <= -x2 \<and> -x2 <= -l2" by arith
  from u2_neg have mu2_pos : "0 <= -u2" by arith
thm zinterval_lposlpos [OF x1_lu mx2_lu l1_pos mu2_pos]
have "min (min (l1 * - u2) (l1 * - l2)) (min (u1 * - u2) (u1 * - l2))
\<le> x1 * - x2 \<and>
x1 * - x2 \<le> max (max (l1 * - u2) (l1 * - l2)) (max (u1 * - u2) (u1 * - l2))
  " by (rule_tac zinterval_lposlpos [OF x1_lu mx2_lu l1_pos mu2_pos])
then have mx1x2_lu:
  "min (min (-l1 * u2) (- l1 * l2)) (min (- u1 * u2) (- u1 * l2)) \<le> - x1 * x2 \<and>
- x1 * x2 \<le> max (max (- l1 * u2) (- l1 * l2)) (max (- u1 * u2) (- u1 * l2))
  " by simp
moreover have "min (min (-l1 * u2) (- l1 * l2)) (min (- u1 * u2) (- u1 * l2)) =- max (max (l1 * u2) ( l1 * l2)) (max ( u1 * u2) ( u1 * l2)) " 
  by (simp add: min_max_minus max_min_minus)
moreover 
have 
"max (max (- l1 * u2) (- l1 * l2)) (max (- u1 * u2) (- u1 * l2)) = - min (min (l1 * u2) (l1 * l2)) (min (u1 * u2) (u1 * l2))"
 by (simp add: min_max_minus max_min_minus)
thm subinterval[OF mx1x2_lu]
ultimately have "- max (max (l1 * u2) ( l1 * l2)) (max ( u1 * u2) ( u1 * l2))\<le> - x1 * x2 \<and>
- x1 * x2 \<le> - min (min (l1 * u2) (l1 * l2)) (min (u1 * u2) (u1 * l2)) " by simp
 then have ?thesis by (simp add: max_commute min_commute)
}
ultimately show ?thesis by blast
qed

lemma zinterval_uneg :
assumes x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     u1_neg: "u1 <= 0"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
proof-
  from x1_lu  have mx1_lu : "-u1 <= -x1 \<and> -x1 <= -l1" by arith
  from u1_neg have mu1_pos : "0 <= -u1" by arith
  thm zinterval_lpos [OF mx1_lu x2_lu mu1_pos]
  have mx1x2_lu : 
    "min (min (- u1 * l2) (- u1 * u2)) (min (- l1 * l2) (- l1 * u2))
    \<le> - x1 * x2 \<and> - x1 * x2 \<le> 
    max (max (- u1 * l2) (- u1 * u2)) (max (- l1 * l2) (- l1 * u2))"
by (rule_tac zinterval_lpos [OF mx1_lu x2_lu mu1_pos])
moreover have 
  "min (min (- u1 * l2) (- u1 * u2)) (min (- l1 * l2) (- l1 * u2)) = - max (max (u1 * l2) (u1 * u2)) (max (l1 * l2) (l1 * u2))" by (simp add: min_max_minus max_min_minus)
moreover have 
  "max (max (- u1 * l2) (- u1 * u2)) (max (- l1 * l2) (- l1 * u2)) = - min (min (u1 * l2) ( u1 * u2)) (min (l1 * l2) (l1 * u2))" by (simp add: min_max_minus max_min_minus)
ultimately have "- max (max (u1 * l2) (u1 * u2)) (max (l1 * l2) (l1 * u2))\<le> - x1 * x2 \<and> - x1 * x2 \<le>  - min (min (u1 * l2) ( u1 * u2)) (min (l1 * l2) (l1 * u2))" by simp
then show ?thesis by (simp add: min_commute max_commute mult_ac)
qed

lemma zinterval_lnegxpos:
assumes x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     l1_neg: "l1 <= 0"
  and     x1_pos: "0<= x1"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
proof-
  have "(0 <= l2) \<or> (l2 < 0 \<and> 0<= x2) \<or> (x2 <0 \<and> 0 <= u2) \<or> (u2 <= 0)" by arith
  moreover
  {
    assume l2_pos: "0 <= l2"
    thm zinterval_lpos [OF x2_lu x1_lu l2_pos]
    have 
      "min (min (l2 * l1) (l2 * u1)) (min (u2 * l1) (u2 * u1)) \<le> x2 * x1 \<and>
      x2 * x1 \<le> max (max (l2 * l1) (l2 * u1)) (max (u2 * l1) (u2 * u1))"
      by (rule_tac zinterval_lpos [OF x2_lu x1_lu l2_pos])
 moreover have "min (min (l2 * l1) (l2 * u1)) (min (u2 * l1) (u2 * u1)) = min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2))" by (simp add: mult_ac min_commute min_min_commute)
moreover have "max (max (l2 * l1) (l2 * u1)) (max (u2 * l1) (u2 * u1)) = max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
  by (simp add: mult_ac max_commute max_max_commute)
ultimately have ?thesis by (simp add: mult_ac)

}

moreover
{
  assume l2_neg: "l2 < 0" and x2_pos: " 0<= x2"
  from l1_neg have l1_le0 : "l1 <= 0" by simp
  from l2_neg have l2_le0 : "l2 <= 0" by simp
 have ?thesis by (simp add: zinterval_lneglneg [OF x1_lu x2_lu l1_le0 x1_pos l2_le0 x2_pos])
}

moreover
{
 assume x2_neg: "x2 <0" and u2_pos: "0 <= u2"
 from x2_lu have mx2_lu: "-u2 <= -x2 \<and> -x2 <= -l2" by arith
 from x2_neg have mx2_pos: "0 <= -x2" by simp
 from u2_pos have mu2_neg: "-u2 <= 0" by simp
 from l1_neg have l1_le0 : "l1 <= 0" by simp
thm zinterval_lneglneg [OF x1_lu mx2_lu l1_le0 x1_pos mu2_neg mx2_pos]
have "min (min (l1 * - u2) (l1 * - l2)) (min (u1 * - u2) (u1 * - l2))
\<le> x1 * - x2 \<and>
x1 * - x2 \<le> max (max (l1 * - u2) (l1 * - l2)) (max (u1 * - u2) (u1 * - l2))" by (rule_tac zinterval_lneglneg [OF x1_lu mx2_lu l1_le0 x1_pos mu2_neg mx2_pos])
then have "min (min (- l1 * u2) (- l1 * l2)) (min (- u1 * u2) (- u1 * l2))
\<le> - x1 * x2 \<and>
- x1 * x2 \<le> max (max (- l1 * u2) (- l1 * l2)) (max (- u1 * u2) (- u1 * l2))" by simp
moreover have "min (min (- l1 * u2) (- l1 * l2)) (min (- u1 * u2) (- u1 * l2)) = - max (max (l1 * u2) (l1 * l2)) (max (u1 * u2) (u1 * l2))" by (simp add: min_max_minus max_min_minus)
moreover have "max (max (- l1 * u2) (- l1 * l2)) (max (- u1 * u2) (- u1 * l2)) = - min (min (l1 * u2) (l1 * l2)) (min (u1 * u2) (u1 * l2))" by (simp add: min_max_minus max_min_minus)
ultimately have "- max (max (l1 * u2) (l1 * l2)) (max (u1 * u2) (u1 * l2))\<le> - x1 * x2 \<and>
- x1 * x2 \<le>  - min (min (l1 * u2) (l1 * l2)) (min (u1 * u2) (u1 * l2))" by simp

then have ?thesis by (simp add: min_commute max_commute mult_ac) 
}

moreover
{
 assume u2_neg: "u2 <= 0"
 thm zinterval_uneg[OF x2_lu x1_lu u2_neg]
have "min (min (l2 * l1) (l2 * u1)) (min (u2 * l1) (u2 * u1)) \<le> x2 * x1 \<and>
x2 * x1 \<le> max (max (l2 * l1) (l2 * u1)) (max (u2 * l1) (u2 * u1))" by (rule_tac zinterval_uneg[OF x2_lu x1_lu u2_neg])
then have ?thesis by (simp add: mult_ac min_commute max_commute min_min_commute max_max_commute)
}
ultimately show ?thesis by blast

qed

lemma zinterval_xnegupos: 
assumes x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  and     x1_neg: "x1 <= 0"
  and     u1_pos: "0<= u1"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
proof-
  from x1_lu have mx1_lu : "-u1 <= -x1 \<and> -x1 <= -l1" by arith 
  from u1_pos have mu1_neg : "-u1 <= 0" by simp
  from x1_neg have mx1_pos : "0 <= -x1" by simp
  thm zinterval_lnegxpos[OF mx1_lu x2_lu mu1_neg mx1_pos ]
  have "min (min (- u1 * l2) (- u1 * u2)) (min (- l1 * l2) (- l1 * u2))
\<le> - x1 * x2 \<and>
- x1 * x2 \<le> max (max (- u1 * l2) (- u1 * u2)) (max (- l1 * l2) (- l1 * u2))"
    by (rule_tac zinterval_lnegxpos[OF mx1_lu x2_lu mu1_neg mx1_pos ])
  moreover have 
    "min (min (- u1 * l2) (- u1 * u2)) (min (- l1 * l2) (- l1 * u2)) = - max (max (u1 * l2) (u1 * u2)) (max (l1 * l2) (l1 * u2))" 
    by (simp add: min_max_minus max_min_minus)
  moreover have 
    "max (max (- u1 * l2) (- u1 * u2)) (max (- l1 * l2) (- l1 * u2)) = - min (min (u1 * l2) (u1 * u2)) (min (l1 * l2) (l1 * u2))" 
    by (simp add: min_max_minus max_min_minus)
  ultimately have "- max (max (u1 * l2) (u1 * u2)) (max (l1 * l2) (l1 * u2))\<le> - x1 * x2 \<and>
- x1 * x2 \<le> - min (min (u1 * l2) (u1 * u2)) (min (l1 * l2) (l1 * u2))" 
    by simp
then show ?thesis by (simp add: mult_ac min_commute max_commute)
qed

lemma abs_mul: 
  assumes x1_lu : "l1 <= (x1::int) \<and> x1 <= u1"
  and     x2_lu : "l2 <= (x2::int) \<and> x2 <= u2"
  shows conc : "min (min (l1*l2) (l1*u2)) (min (u1*l2) (u1*u2)) <= x1 * x2 
  \<and> x1 * x2 <= max (max (l1*l2) (l1*u2)) (max (u1*l2) (u1*u2))"
proof-
  have "(0 <= l1) \<or> (l1 <= 0 \<and> 0<= x1) \<or> (x1 <=0 \<and> 0 <= u1) \<or> (u1 <= 0)" 
    by arith
  moreover
  {
    assume l1_pos: "0 <= l1"
    have ?thesis by (rule_tac zinterval_lpos [OF x1_lu x2_lu l1_pos])
  }
  
  moreover
  {
    assume l1_neg :"l1 <= 0" and x1_pos: "0<= x1"
    have ?thesis by (rule_tac zinterval_lnegxpos[OF x1_lu x2_lu l1_neg x1_pos])
  }
  
  moreover
  {
    assume x1_neg : "x1 <= 0" and u1_pos: "0 <= u1"
    have ?thesis by (rule_tac zinterval_xnegupos [OF x1_lu x2_lu x1_neg u1_pos])
  }
  
  moreover
  {
    assume u1_neg: "u1 <= 0"
    have ?thesis by (rule_tac zinterval_uneg [OF x1_lu x2_lu u1_neg])
  }
  
  ultimately show ?thesis by blast
qed

lemma mult_x_mono_lpos : 
assumes l_pos : "0 <= (l::int)"
  and   x_lu : "l <= (x::int) \<and> x <= u"
  shows "l*l <= x*x \<and> x*x <= u*u"

proof-
  from x_lu have x_l : "l <= x" by arith
  thm zmult_mono[OF l_pos l_pos x_l x_l]
  then have xx_l : "l*l <= x*x"
    by (simp add: zmult_mono[OF l_pos l_pos x_l x_l])
  moreover 
  from x_lu have x_u : "x <= u" by arith
  from l_pos x_l have x_pos : "0 <= x" by arith
  thm zmult_mono[OF x_pos x_pos x_u x_u]
  then have xx_u : "x*x <= u*u"
    by (simp add: zmult_mono[OF x_pos x_pos x_u x_u])
ultimately show ?thesis by simp
qed

lemma mult_x_mono_luneg : 
assumes l_neg : "(l::int) <= 0"
  and   u_neg : "u <= 0"
  and   x_lu : "l <= (x::int) \<and> x <= u"
  shows "u*u <= x*x \<and> x*x <= l*l"

proof-
  from x_lu have mx_lu : "-u <= -x \<and> -x <= -l" by arith
  from u_neg have mu_pos : "0<= -u" by simp
  thm mult_x_mono_lpos[OF mu_pos mx_lu]
  have "- u * - u \<le> - x * - x \<and> - x * - x \<le> - l * - l"
    by (rule_tac mult_x_mono_lpos[OF mu_pos mx_lu])
  then show ?thesis by simp
qed

lemma mult_x_mono_lxnegupos : 
assumes l_neg : "(l::int) <= 0"
  and   u_pos : "0 <= u"
  and   x_neg : "x <= 0"
  and   x_lu : "l <= (x::int) \<and> x <= u"
  shows "0 <= x*x \<and> x*x <= max (l*l) (u*u)"
proof-
  from x_lu x_neg have mx_0l : "0 <= - x \<and> - x <= - l" by arith
  have trv_0 : "(0::int) <= 0" by arith
  thm mult_x_mono_lpos[OF trv_0 mx_0l]
  have "0 * 0 \<le> - x * - x \<and> - x * - x \<le> - l * - l"
    by (rule_tac  mult_x_mono_lpos[OF trv_0 mx_0l])
  then have xx_0ll : "0 <= x*x \<and> x*x <= l*l" by simp
  have "l*l <= max (l*l) (u*u)" by (simp add: le_maxI1)
  with xx_0ll show ?thesis by arith
qed

lemma mult_x_mono_lnegupos : 
assumes l_neg : "(l::int) <= 0"
  and   u_pos : "0 <= u"
  and   x_lu : "l <= (x::int) \<and> x <= u"
  shows "0 <= x*x \<and> x*x <= max (l*l) (u*u)"
proof-
  have "0<= x \<or> x <= 0" by arith
moreover
{
  assume x_neg : "x <= 0"
  thm mult_x_mono_lxnegupos[OF l_neg u_pos x_neg x_lu]
  have ?thesis by (rule_tac mult_x_mono_lxnegupos[OF l_neg u_pos x_neg x_lu])
}
moreover

{
  assume x_pos : "0 <= x"
  from x_lu have mx_lu : "-u <= -x \<and> -x <= -l" by arith
  from x_pos have mx_neg : "-x <= 0" by simp
  from u_pos have mu_neg : "-u <= 0" by simp
  from x_lu x_pos have ml_pos : "0 <= -l" by simp
  thm mult_x_mono_lxnegupos[OF mu_neg ml_pos mx_neg mx_lu]
  have "0 \<le> - x * - x \<and> - x * - x \<le> max (- u * - u) (- l * - l)"
    by (rule_tac mult_x_mono_lxnegupos[OF mu_neg ml_pos mx_neg mx_lu])
  then have ?thesis by (simp add: max_commute)

}
ultimately show ?thesis by blast

qed
lemma abs_mul_x:
  assumes x_lu : "l <= (x::int) \<and> x <= u"
  shows 
  "(if 0 <= l then l*l  else if u <= 0 then u*u else 0) <= x*x
  \<and> x*x <= (if 0 <= l then u*u  else if u <= 0 then l*l else (max (l*l) (u*u)))"
proof-
  have "(0 <= l) \<or> (l < 0 \<and> u <= 0) \<or> (l < 0 \<and> 0 < u)" by arith 
  
  moreover
  {
    assume l_pos : "0 <= l"
    from l_pos have "(if 0 <= l then l*l  else if u <= 0 then u*u else 0) = l*l"
      by simp
    moreover from l_pos have "(if 0 <= l then u*u  else if u <= 0 then l*l else (max (l*l) (u*u))) = u*u" by simp
    
    moreover have "l * l \<le> x * x \<and> x * x \<le> u * u" 
      by (rule_tac  mult_x_mono_lpos[OF l_pos x_lu])
    ultimately have ?thesis by simp 
  }
  
  moreover
  {
    assume l_neg : "l < 0"  and u_neg : "u <= 0"  
    from l_neg have l_le0 : "l <= 0" by simp
    from l_neg u_neg have "(if 0 <= l then l*l  else if u <= 0 then u*u else 0) = u*u"
      by simp
    moreover 
    from l_neg u_neg have "(if 0 <= l then u*u  else if u <= 0 then l*l else (max (l*l) (u*u))) = l*l" by simp
    moreover 
    have "u * u \<le> x * x \<and> x * x \<le> l * l" 
      by (rule_tac mult_x_mono_luneg[OF l_le0 u_neg x_lu])
    
    ultimately have ?thesis by simp 
  }
  moreover
  {
    assume l_neg : "l < 0" and u_pos: "0 < u"
    from l_neg have l_le0 : "l <= 0" by simp
    from u_pos have u_ge0 : "0 <= u" by simp
    from l_neg u_pos have "(if 0 <= l then l*l  else if u <= 0 then u*u else 0) = 0"
      by simp
    moreover from l_neg u_pos have "(if 0 <= l then u*u  else if u <= 0 then l*l else (max (l*l) (u*u))) = max (l*l) (u*u)" by simp
    moreover have "0 \<le> x * x \<and> x * x \<le> max (l * l) (u * u)" 
      by (rule_tac mult_x_mono_lnegupos[OF l_le0 u_ge0 x_lu])
    
    ultimately have ?thesis by simp 
    
  }
  
  ultimately show ?thesis by blast
qed


use"barith.ML"
setup Barith.setup

end

