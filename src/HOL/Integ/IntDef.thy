(*  Title:      IntDef.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

*)

header{*The Integers as Equivalence Classes over Pairs of Natural Numbers*}

theory IntDef = Equiv + NatArith:
constdefs
  intrel :: "((nat * nat) * (nat * nat)) set"
    "intrel == {p. \<exists>x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1}"

typedef (Integ)
  int = "UNIV//intrel"
    by (auto simp add: quotient_def) 

instance int :: ord ..
instance int :: zero ..
instance int :: one ..
instance int :: plus ..
instance int :: times ..
instance int :: minus ..

constdefs

  int :: "nat => int"
  "int m == Abs_Integ(intrel `` {(m,0)})"
  
defs (overloaded)
  
  zminus_def:    "- Z == Abs_Integ(\<Union>(x,y) \<in> Rep_Integ(Z). intrel``{(y,x)})"

  Zero_int_def:  "0 == int 0"
  One_int_def:   "1 == int 1"

  zadd_def:
   "z + w == 
       Abs_Integ(\<Union>(x1,y1) \<in> Rep_Integ(z). \<Union>(x2,y2) \<in> Rep_Integ(w).   
		 intrel``{(x1+x2, y1+y2)})"

  zdiff_def:  "z - (w::int) == z + (-w)"
  zmult_def:
   "z * w == 
       Abs_Integ(\<Union>(x1,y1) \<in> Rep_Integ(z). \<Union>(x2,y2) \<in> Rep_Integ(w).   
		 intrel``{(x1*x2 + y1*y2, x1*y2 + y1*x2)})"

  zless_def: "(z < (w::int)) == (z \<le> w & z \<noteq> w)"

  zle_def:
  "z \<le> (w::int) == \<exists>x1 y1 x2 y2. x1 + y2 \<le> x2 + y1 &
                            (x1,y1) \<in> Rep_Integ z & (x2,y2) \<in> Rep_Integ w"

lemma intrel_iff [simp]: "(((x1,y1),(x2,y2)) \<in>  intrel) = (x1+y2 = x2+y1)"
by (unfold intrel_def, blast)

lemma equiv_intrel: "equiv UNIV intrel"
by (unfold intrel_def equiv_def refl_def sym_def trans_def, auto)

lemmas equiv_intrel_iff =
       eq_equiv_class_iff [OF equiv_intrel UNIV_I UNIV_I, simp]

lemma intrel_in_integ [simp]: "intrel``{(x,y)}:Integ"
by (unfold Integ_def intrel_def quotient_def, fast)

lemma inj_on_Abs_Integ: "inj_on Abs_Integ Integ"
apply (rule inj_on_inverseI)
apply (erule Abs_Integ_inverse)
done

declare inj_on_Abs_Integ [THEN inj_on_iff, simp] 
        Abs_Integ_inverse [simp]

lemma inj_Rep_Integ: "inj(Rep_Integ)"
apply (rule inj_on_inverseI)
apply (rule Rep_Integ_inverse)
done


(** int: the injection from "nat" to "int" **)

lemma inj_int: "inj int"
apply (rule inj_onI)
apply (unfold int_def)
apply (drule inj_on_Abs_Integ [THEN inj_onD])
apply (rule intrel_in_integ)+
apply (drule eq_equiv_class)
apply (rule equiv_intrel, fast)
apply (simp add: intrel_def)
done

lemma int_int_eq [iff]: "(int m = int n) = (m = n)"
by (fast elim!: inj_int [THEN injD])



subsection{*zminus: unary negation on Integ*}

lemma zminus_congruent: "congruent intrel (%(x,y). intrel``{(y,x)})"
apply (unfold congruent_def intrel_def)
apply (auto simp add: add_ac)
done

lemma zminus: "- Abs_Integ(intrel``{(x,y)}) = Abs_Integ(intrel `` {(y,x)})"
by (simp add: zminus_def equiv_intrel [THEN UN_equiv_class] zminus_congruent)

(*Every integer can be written in the form Abs_Integ(...) *)
lemma eq_Abs_Integ: 
     "(!!x y. z = Abs_Integ(intrel``{(x,y)}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_Integ [unfolded Integ_def, THEN quotientE]) 
apply (drule_tac f = Abs_Integ in arg_cong)
apply (rule_tac p = x in PairE)
apply (simp add: Rep_Integ_inverse)
done

lemma zminus_zminus [simp]: "- (- z) = (z::int)"
apply (rule eq_Abs_Integ [of z])
apply (simp add: zminus)
done

lemma inj_zminus: "inj(%z::int. -z)"
apply (rule inj_onI)
apply (drule_tac f = uminus in arg_cong, simp)
done

lemma zminus_0 [simp]: "- 0 = (0::int)"
by (simp add: int_def Zero_int_def zminus)


subsection{*zadd: addition on Integ*}

lemma zadd: 
  "Abs_Integ(intrel``{(x1,y1)}) + Abs_Integ(intrel``{(x2,y2)}) =  
   Abs_Integ(intrel``{(x1+x2, y1+y2)})"
apply (simp add: zadd_def UN_UN_split_split_eq)
apply (subst equiv_intrel [THEN UN_equiv_class2])
apply (auto simp add: congruent2_def)
done

lemma zminus_zadd_distrib [simp]: "- (z + w) = (- z) + (- w::int)"
apply (rule eq_Abs_Integ [of z])
apply (rule eq_Abs_Integ [of w])
apply (simp add: zminus zadd)
done

lemma zadd_commute: "(z::int) + w = w + z"
apply (rule eq_Abs_Integ [of z])
apply (rule eq_Abs_Integ [of w])
apply (simp add: add_ac zadd)
done

lemma zadd_assoc: "((z1::int) + z2) + z3 = z1 + (z2 + z3)"
apply (rule eq_Abs_Integ [of z1])
apply (rule eq_Abs_Integ [of z2])
apply (rule eq_Abs_Integ [of z3])
apply (simp add: zadd add_assoc)
done

(*For AC rewriting*)
lemma zadd_left_commute: "x + (y + z) = y + ((x + z)  ::int)"
  apply (rule mk_left_commute [of "op +"])
  apply (rule zadd_assoc)
  apply (rule zadd_commute)
  done

(*Integer addition is an AC operator*)
lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute

lemmas zmult_ac = Ring_and_Field.mult_ac

lemma zadd_int: "(int m) + (int n) = int (m + n)"
by (simp add: int_def zadd)

lemma zadd_int_left: "(int m) + (int n + z) = int (m + n) + z"
by (simp add: zadd_int zadd_assoc [symmetric])

lemma int_Suc: "int (Suc m) = 1 + (int m)"
by (simp add: One_int_def zadd_int)

(*also for the instance declaration int :: plus_ac0*)
lemma zadd_0 [simp]: "(0::int) + z = z"
apply (unfold Zero_int_def int_def)
apply (rule eq_Abs_Integ [of z])
apply (simp add: zadd)
done

lemma zadd_0_right [simp]: "z + (0::int) = z"
by (rule trans [OF zadd_commute zadd_0])

lemma zadd_zminus_inverse [simp]: "z + (- z) = (0::int)"
apply (unfold int_def Zero_int_def)
apply (rule eq_Abs_Integ [of z])
apply (simp add: zminus zadd add_commute)
done

lemma zadd_zminus_inverse2 [simp]: "(- z) + z = (0::int)"
apply (rule zadd_commute [THEN trans])
apply (rule zadd_zminus_inverse)
done

lemma zadd_zminus_cancel [simp]: "z + (- z + w) = (w::int)"
by (simp add: zadd_assoc [symmetric] zadd_0)

lemma zminus_zadd_cancel [simp]: "(-z) + (z + w) = (w::int)"
by (simp add: zadd_assoc [symmetric] zadd_0)

lemma zdiff0 [simp]: "(0::int) - x = -x"
by (simp add: zdiff_def)

lemma zdiff0_right [simp]: "x - (0::int) = x"
by (simp add: zdiff_def)

lemma zdiff_self [simp]: "x - x = (0::int)"
by (simp add: zdiff_def Zero_int_def)


(** Lemmas **)

lemma zadd_assoc_cong: "(z::int) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
by (simp add: zadd_assoc [symmetric])


subsection{*zmult: multiplication on Integ*}

text{*Congruence property for multiplication*}
lemma zmult_congruent2: "congruent2 intrel  
        (%p1 p2. (%(x1,y1). (%(x2,y2).    
                    intrel``{(x1*x2 + y1*y2, x1*y2 + y1*x2)}) p2) p1)"
apply (rule equiv_intrel [THEN congruent2_commuteI])
 apply (force simp add: add_ac mult_ac) 
apply (clarify, simp del: equiv_intrel_iff add: add_ac mult_ac)
apply (rename_tac x1 x2 y1 y2 z1 z2)
apply (rule equiv_class_eq [OF equiv_intrel intrel_iff [THEN iffD2]])
apply (subgoal_tac "x1*z1 + y2*z1 = y1*z1 + x2*z1 & x1*z2 + y2*z2 = y1*z2 + x2*z2")
apply (simp add: mult_ac, arith) 
apply (simp add: add_mult_distrib [symmetric])
done

lemma zmult: 
   "Abs_Integ((intrel``{(x1,y1)})) * Abs_Integ((intrel``{(x2,y2)})) =    
    Abs_Integ(intrel `` {(x1*x2 + y1*y2, x1*y2 + y1*x2)})"
by (simp add: zmult_def UN_UN_split_split_eq zmult_congruent2 
              equiv_intrel [THEN UN_equiv_class2])

lemma zmult_zminus: "(- z) * w = - (z * (w::int))"
apply (rule eq_Abs_Integ [of z])
apply (rule eq_Abs_Integ [of w])
apply (simp add: zminus zmult add_ac)
done

lemma zmult_commute: "(z::int) * w = w * z"
apply (rule eq_Abs_Integ [of z])
apply (rule eq_Abs_Integ [of w])
apply (simp add: zmult add_ac mult_ac)
done

lemma zmult_assoc: "((z1::int) * z2) * z3 = z1 * (z2 * z3)"
apply (rule eq_Abs_Integ [of z1])
apply (rule eq_Abs_Integ [of z2])
apply (rule eq_Abs_Integ [of z3])
apply (simp add: add_mult_distrib2 zmult add_ac mult_ac)
done

lemma zadd_zmult_distrib: "((z1::int) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule eq_Abs_Integ [of z1])
apply (rule eq_Abs_Integ [of z2])
apply (rule eq_Abs_Integ [of w])
apply (simp add: add_mult_distrib2 zadd zmult add_ac mult_ac)
done

lemma zmult_zminus_right: "w * (- z) = - (w * (z::int))"
by (simp add: zmult_commute [of w] zmult_zminus)

lemma zadd_zmult_distrib2: "(w::int) * (z1 + z2) = (w * z1) + (w * z2)"
by (simp add: zmult_commute [of w] zadd_zmult_distrib)

lemma zdiff_zmult_distrib: "((z1::int) - z2) * w = (z1 * w) - (z2 * w)"
apply (unfold zdiff_def)
apply (subst zadd_zmult_distrib)
apply (simp add: zmult_zminus)
done

lemma zdiff_zmult_distrib2: "(w::int) * (z1 - z2) = (w * z1) - (w * z2)"
by (simp add: zmult_commute [of w] zdiff_zmult_distrib)

lemmas int_distrib =
  zadd_zmult_distrib zadd_zmult_distrib2 
  zdiff_zmult_distrib zdiff_zmult_distrib2

lemma zmult_int: "(int m) * (int n) = int (m * n)"
by (simp add: int_def zmult)

lemma zmult_0 [simp]: "0 * z = (0::int)"
apply (unfold Zero_int_def int_def)
apply (rule eq_Abs_Integ [of z])
apply (simp add: zmult)
done

lemma zmult_1 [simp]: "(1::int) * z = z"
apply (unfold One_int_def int_def)
apply (rule eq_Abs_Integ [of z])
apply (simp add: zmult)
done

lemma zmult_0_right [simp]: "z * 0 = (0::int)"
by (rule trans [OF zmult_commute zmult_0])

lemma zmult_1_right [simp]: "z * (1::int) = z"
by (rule trans [OF zmult_commute zmult_1])


text{*The Integers Form A Ring*}
instance int :: ring
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)" by (simp add: zadd_assoc)
  show "i + j = j + i" by (simp add: zadd_commute)
  show "0 + i = i" by simp
  show "- i + i = 0" by simp
  show "i - j = i + (-j)" by (simp add: zdiff_def)
  show "(i * j) * k = i * (j * k)" by (rule zmult_assoc)
  show "i * j = j * i" by (rule zmult_commute)
  show "1 * i = i" by simp
  show "(i + j) * k = i * k + j * k" by (simp add: int_distrib)
  show "0 \<noteq> (1::int)" 
    by (simp only: Zero_int_def One_int_def One_nat_def int_int_eq)
qed


subsection{*The @{text "\<le>"} Ordering*}

lemma zle: 
  "(Abs_Integ(intrel``{(x1,y1)}) \<le> Abs_Integ(intrel``{(x2,y2)})) =  
   (x1 + y2 \<le> x2 + y1)"
by (force simp add: zle_def)

lemma zle_refl: "w \<le> (w::int)"
apply (rule eq_Abs_Integ [of w])
apply (force simp add: zle)
done

lemma zle_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::int)"
apply (rule eq_Abs_Integ [of i]) 
apply (rule eq_Abs_Integ [of j]) 
apply (rule eq_Abs_Integ [of k]) 
apply (simp add: zle) 
done

lemma zle_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::int)"
apply (rule eq_Abs_Integ [of w]) 
apply (rule eq_Abs_Integ [of z]) 
apply (simp add: zle) 
done

(* Axiom 'order_less_le' of class 'order': *)
lemma zless_le: "((w::int) < z) = (w \<le> z & w \<noteq> z)"
by (simp add: zless_def)

instance int :: order
proof qed
 (assumption |
  rule zle_refl zle_trans zle_anti_sym zless_le)+

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma zle_linear: "(z::int) \<le> w | w \<le> z"
apply (rule eq_Abs_Integ [of z])
apply (rule eq_Abs_Integ [of w])
apply (simp add: zle linorder_linear) 
done

instance int :: linorder
proof qed (rule zle_linear)


lemmas zless_linear = linorder_less_linear [where 'a = int]


lemma int_eq_0_conv [simp]: "(int n = 0) = (n = 0)"
by (simp add: Zero_int_def)

(*This lemma allows direct proofs of other <-properties*)
lemma zless_iff_Suc_zadd: 
    "(w < z) = (\<exists>n. z = w + int(Suc n))"
apply (rule eq_Abs_Integ [of z])
apply (rule eq_Abs_Integ [of w])
apply (simp add: linorder_not_le [where 'a = int, symmetric] 
                 linorder_not_le [where 'a = nat] 
                 zle int_def zdiff_def zadd zminus) 
apply (safe dest!: less_imp_Suc_add)
apply (rule_tac x = k in exI)
apply (simp_all add: add_ac)
done

lemma zless_int [simp]: "(int m < int n) = (m<n)"
by (simp add: less_iff_Suc_add zless_iff_Suc_zadd zadd_int)

lemma int_less_0_conv [simp]: "~ (int k < 0)"
by (simp add: Zero_int_def)

lemma zero_less_int_conv [simp]: "(0 < int n) = (0 < n)"
by (simp add: Zero_int_def)

lemma int_0_less_1: "0 < (1::int)"
by (simp only: Zero_int_def One_int_def One_nat_def zless_int)

lemma int_0_neq_1 [simp]: "0 \<noteq> (1::int)"
by (simp only: Zero_int_def One_int_def One_nat_def int_int_eq)

lemma zle_int [simp]: "(int m \<le> int n) = (m\<le>n)"
by (simp add: linorder_not_less [symmetric])

lemma zero_zle_int [simp]: "(0 \<le> int n)"
by (simp add: Zero_int_def)

lemma int_le_0_conv [simp]: "(int n \<le> 0) = (n = 0)"
by (simp add: Zero_int_def)

lemma int_0 [simp]: "int 0 = (0::int)"
by (simp add: Zero_int_def)

lemma int_1 [simp]: "int 1 = 1"
by (simp add: One_int_def)

lemma int_Suc0_eq_1: "int (Suc 0) = 1"
by (simp add: One_int_def One_nat_def)

subsection{*Monotonicity results*}

lemma zadd_left_mono: "i \<le> j ==> k + i \<le> k + (j::int)" 
apply (rule eq_Abs_Integ [of i]) 
apply (rule eq_Abs_Integ [of j]) 
apply (rule eq_Abs_Integ [of k]) 
apply (simp add: zle zadd) 
done

lemma zadd_strict_right_mono: "i < j ==> i + k < j + (k::int)" 
apply (rule eq_Abs_Integ [of i]) 
apply (rule eq_Abs_Integ [of j]) 
apply (rule eq_Abs_Integ [of k]) 
apply (simp add: linorder_not_le [where 'a = int, symmetric] 
                 linorder_not_le [where 'a = nat]  zle zadd)
done

lemma zadd_zless_mono: "[| w'<w; z'\<le>z |] ==> w' + z' < w + (z::int)"
by (rule order_less_le_trans [OF zadd_strict_right_mono zadd_left_mono]) 


subsection{*Strict Monotonicity of Multiplication*}

text{*strict, in 1st argument; proof is by induction on k>0*}
lemma zmult_zless_mono2_lemma [rule_format]:
     "i<j ==> 0<k --> int k * i < int k * j"
apply (induct_tac "k", simp) 
apply (simp add: int_Suc)
apply (case_tac "n=0")
apply (simp_all add: zadd_zmult_distrib int_Suc0_eq_1 order_le_less)
apply (simp add: zadd_zless_mono int_Suc0_eq_1 order_le_less)
done

lemma zero_le_imp_eq_int: "0 \<le> k ==> \<exists>n. k = int n"
apply (rule eq_Abs_Integ [of k]) 
apply (auto simp add: zle zadd int_def Zero_int_def)
apply (rule_tac x="x-y" in exI, simp) 
done

lemma zmult_zless_mono2: "[| i<j;  (0::int) < k |] ==> k*i < k*j"
apply (frule order_less_imp_le [THEN zero_le_imp_eq_int]) 
apply (auto simp add: zmult_zless_mono2_lemma) 
done


defs (overloaded)
    zabs_def:  "abs(i::int) == if i < 0 then -i else i"


text{*The Integers Form an Ordered Ring*}
instance int :: ordered_ring
proof
  fix i j k :: int
  show "i \<le> j ==> k + i \<le> k + j" by (rule zadd_left_mono)
  show "i < j ==> 0 < k ==> k * i < k * j" by (rule zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)" by (simp only: zabs_def)
qed


subsection{*Magnitide of an Integer, as a Natural Number: @{term nat}*}

constdefs
   nat  :: "int => nat"
    "nat(Z) == if Z<0 then 0 else (THE m. Z = int m)"

lemma nat_int [simp]: "nat(int n) = n"
by (unfold nat_def, auto)

lemma nat_zero [simp]: "nat 0 = 0"
apply (unfold Zero_int_def)
apply (rule nat_int)
done

lemma nat_0_le [simp]: "0 \<le> z ==> int (nat z) = z"
apply (rule eq_Abs_Integ [of z]) 
apply (simp add: nat_def linorder_not_le [symmetric] zle int_def Zero_int_def)
apply (subgoal_tac "(THE m. x = m + y) = x-y")
apply (auto simp add: the_equality) 
done

lemma nat_le_0 [simp]: "z \<le> 0 ==> nat z = 0"
by (simp add: nat_def  order_less_le eq_commute [of 0])

text{*An alternative condition is @{term "0 \<le> w"} *}
lemma nat_mono_iff: "0 < z ==> (nat w < nat z) = (w < z)"
apply (subst zless_int [symmetric])
apply (simp add: order_le_less)
apply (case_tac "w < 0")
 apply (simp add: order_less_imp_le)
apply (simp add: linorder_not_less)
done

lemma zless_nat_conj: "(nat w < nat z) = (0 < z & w < z)"
apply (case_tac "0 < z")
apply (auto simp add: nat_mono_iff linorder_not_less)
done


subsection{*Lemmas about the Function @{term int} and Orderings*}

lemma negative_zless_0: "- (int (Suc n)) < 0"
by (simp add: zless_def)

lemma negative_zless [iff]: "- (int (Suc n)) < int m"
by (rule negative_zless_0 [THEN order_less_le_trans], simp)

lemma negative_zle_0: "- int n \<le> 0"
by (simp add: minus_le_iff)

lemma negative_zle [iff]: "- int n \<le> int m"
by (rule order_trans [OF negative_zle_0 zero_zle_int])

lemma not_zle_0_negative [simp]: "~ (0 \<le> - (int (Suc n)))"
by (subst le_minus_iff, simp)

lemma int_zle_neg: "(int n \<le> - int m) = (n = 0 & m = 0)"
apply safe 
apply (drule_tac [2] le_minus_iff [THEN iffD1])
apply (auto dest: zle_trans [OF _ negative_zle_0]) 
done

lemma not_int_zless_negative [simp]: "~ (int n < - int m)"
by (simp add: linorder_not_less)

lemma negative_eq_positive [simp]: "(- int n = int m) = (n = 0 & m = 0)"
by (force simp add: order_eq_iff [of "- int n"] int_zle_neg)

lemma zle_iff_zadd: "(w \<le> z) = (\<exists>n. z = w + int n)"
by (force intro: exI [of _ "0::nat"] 
            intro!: not_sym [THEN not0_implies_Suc]
            simp add: zless_iff_Suc_zadd order_le_less)


text{*This version is proved for all ordered rings, not just integers!
      It is proved here because attribute @{text arith_split} is not available
      in theory @{text Ring_and_Field}.
      But is it really better than just rewriting with @{text abs_if}?*}
lemma abs_split [arith_split]:
     "P(abs(a::'a::ordered_ring)) = ((0 \<le> a --> P a) & (a < 0 --> P(-a)))"
by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)

lemma abs_int_eq [simp]: "abs (int m) = int m"
by (simp add: zabs_def)


subsection{*Misc Results*}

lemma nat_zminus_int [simp]: "nat(- (int n)) = 0"
by (auto simp add: nat_def zero_reorient minus_less_iff)

lemma zless_nat_eq_int_zless: "(m < nat z) = (int m < z)"
apply (case_tac "0 \<le> z")
apply (erule nat_0_le [THEN subst], simp) 
apply (simp add: linorder_not_le)
apply (auto dest: order_less_trans simp add: order_less_imp_le)
done

text{*A case theorem distinguishing non-negative and negative int*}

lemma negD: "x<0 ==> \<exists>n. x = - (int (Suc n))"
by (auto simp add: zless_iff_Suc_zadd 
                   diff_eq_eq [symmetric] zdiff_def)

lemma int_cases [cases type: int, case_names nonneg neg]: 
     "[|!! n. z = int n ==> P;  !! n. z =  - (int (Suc n)) ==> P |] ==> P"
apply (case_tac "z < 0", blast dest!: negD)
apply (simp add: linorder_not_less)
apply (blast dest: nat_0_le [THEN sym])
done

lemma int_induct [induct type: int, case_names nonneg neg]: 
     "[|!! n. P (int n);  !!n. P (- (int (Suc n))) |] ==> P z"
  by (cases z) auto


subsection{*The Constants @{term neg} and @{term iszero}*}

constdefs

  neg   :: "'a::ordered_ring => bool"
  "neg(Z) == Z < 0"

  (*For simplifying equalities*)
  iszero :: "'a::semiring => bool"
  "iszero z == z = (0)"
  

lemma not_neg_int [simp]: "~ neg(int n)"
by (simp add: neg_def)

lemma neg_zminus_int [simp]: "neg(- (int (Suc n)))"
by (simp add: neg_def neg_less_0_iff_less)

lemmas neg_eq_less_0 = neg_def

lemma not_neg_eq_ge_0: "(~neg x) = (0 \<le> x)"
by (simp add: neg_def linorder_not_less)

subsection{*To simplify inequalities when Numeral1 can get simplified to 1*}

lemma not_neg_0: "~ neg 0"
by (simp add: One_int_def neg_def)

lemma not_neg_1: "~ neg 1"
by (simp add: neg_def linorder_not_less zero_le_one) 

lemma iszero_0: "iszero 0"
by (simp add: iszero_def)

lemma not_iszero_1: "~ iszero 1"
by (simp add: iszero_def eq_commute) 

lemma neg_nat: "neg z ==> nat z = 0"
by (simp add: nat_def neg_def) 

lemma not_neg_nat: "~ neg z ==> int (nat z) = z"
by (simp add: linorder_not_less neg_def)


subsection{*Embedding of the Naturals into any Semiring: @{term of_nat}*}

consts of_nat :: "nat => 'a::semiring"

primrec
  of_nat_0:   "of_nat 0 = 0"
  of_nat_Suc: "of_nat (Suc m) = of_nat m + 1"

lemma of_nat_1 [simp]: "of_nat 1 = 1"
by simp

lemma of_nat_add [simp]: "of_nat (m+n) = of_nat m + of_nat n"
apply (induct m)
apply (simp_all add: add_ac) 
done

lemma of_nat_mult [simp]: "of_nat (m*n) = of_nat m * of_nat n"
apply (induct m) 
apply (simp_all add: mult_ac add_ac right_distrib) 
done

lemma zero_le_imp_of_nat: "0 \<le> (of_nat m::'a::ordered_semiring)"
apply (induct m, simp_all) 
apply (erule order_trans) 
apply (rule less_add_one [THEN order_less_imp_le]) 
done

lemma less_imp_of_nat_less:
     "m < n ==> of_nat m < (of_nat n::'a::ordered_semiring)"
apply (induct m n rule: diff_induct, simp_all) 
apply (insert add_le_less_mono [OF zero_le_imp_of_nat zero_less_one], force) 
done

lemma of_nat_less_imp_less:
     "of_nat m < (of_nat n::'a::ordered_semiring) ==> m < n"
apply (induct m n rule: diff_induct, simp_all) 
apply (insert zero_le_imp_of_nat) 
apply (force simp add: linorder_not_less [symmetric]) 
done

lemma of_nat_less_iff [simp]:
     "(of_nat m < (of_nat n::'a::ordered_semiring)) = (m<n)"
by (blast intro: of_nat_less_imp_less less_imp_of_nat_less ) 

text{*Special cases where either operand is zero*}
declare of_nat_less_iff [of 0, simplified, simp]
declare of_nat_less_iff [of _ 0, simplified, simp]

lemma of_nat_le_iff [simp]:
     "(of_nat m \<le> (of_nat n::'a::ordered_semiring)) = (m \<le> n)"
by (simp add: linorder_not_less [symmetric]) 

text{*Special cases where either operand is zero*}
declare of_nat_le_iff [of 0, simplified, simp]
declare of_nat_le_iff [of _ 0, simplified, simp]

text{*The ordering on the semiring is necessary to exclude the possibility of
a finite field, which indeed wraps back to zero.*}
lemma of_nat_eq_iff [simp]:
     "(of_nat m = (of_nat n::'a::ordered_semiring)) = (m = n)"
by (simp add: order_eq_iff) 

text{*Special cases where either operand is zero*}
declare of_nat_eq_iff [of 0, simplified, simp]
declare of_nat_eq_iff [of _ 0, simplified, simp]

lemma of_nat_diff [simp]:
     "n \<le> m ==> of_nat (m - n) = of_nat m - (of_nat n :: 'a::ring)"
by (simp del: of_nat_add
	 add: compare_rls of_nat_add [symmetric] split add: nat_diff_split) 


subsection{*The Set of Natural Numbers*}

constdefs
   Nats  :: "'a::semiring set"
    "Nats == range of_nat"

syntax (xsymbols)    Nats :: "'a set"   ("\<nat>")

lemma of_nat_in_Nats [simp]: "of_nat n \<in> Nats"
by (simp add: Nats_def) 

lemma Nats_0 [simp]: "0 \<in> Nats"
apply (simp add: Nats_def) 
apply (rule range_eqI) 
apply (rule of_nat_0 [symmetric])
done

lemma Nats_1 [simp]: "1 \<in> Nats"
apply (simp add: Nats_def) 
apply (rule range_eqI) 
apply (rule of_nat_1 [symmetric])
done

lemma Nats_add [simp]: "[|a \<in> Nats; b \<in> Nats|] ==> a+b \<in> Nats"
apply (auto simp add: Nats_def) 
apply (rule range_eqI) 
apply (rule of_nat_add [symmetric])
done

lemma Nats_mult [simp]: "[|a \<in> Nats; b \<in> Nats|] ==> a*b \<in> Nats"
apply (auto simp add: Nats_def) 
apply (rule range_eqI) 
apply (rule of_nat_mult [symmetric])
done

text{*Agreement with the specific embedding for the integers*}
lemma int_eq_of_nat: "int = (of_nat :: nat => int)"
proof
  fix n
  show "int n = of_nat n"  by (induct n, simp_all add: int_Suc add_ac) 
qed


subsection{*Embedding of the Integers into any Ring: @{term of_int}*}

constdefs
   of_int :: "int => 'a::ring"
   "of_int z ==
      (THE a. \<exists>i j. (i,j) \<in> Rep_Integ z & a = (of_nat i) - (of_nat j))"


lemma of_int: "of_int (Abs_Integ (intrel `` {(i,j)})) = of_nat i - of_nat j"
apply (simp add: of_int_def)
apply (rule the_equality, auto) 
apply (simp add: compare_rls add_ac of_nat_add [symmetric]
            del: of_nat_add) 
done

lemma of_int_0 [simp]: "of_int 0 = 0"
by (simp add: of_int Zero_int_def int_def)

lemma of_int_1 [simp]: "of_int 1 = 1"
by (simp add: of_int One_int_def int_def)

lemma of_int_add [simp]: "of_int (w+z) = of_int w + of_int z"
apply (rule eq_Abs_Integ [of w])
apply (rule eq_Abs_Integ [of z])
apply (simp add: compare_rls of_int zadd) 
done

lemma of_int_minus [simp]: "of_int (-z) = - (of_int z)"
apply (rule eq_Abs_Integ [of z])
apply (simp add: compare_rls of_int zminus) 
done

lemma of_int_diff [simp]: "of_int (w-z) = of_int w - of_int z"
by (simp add: diff_minus)

lemma of_int_mult [simp]: "of_int (w*z) = of_int w * of_int z"
apply (rule eq_Abs_Integ [of w])
apply (rule eq_Abs_Integ [of z])
apply (simp add: compare_rls of_int left_diff_distrib right_diff_distrib 
                 zmult add_ac) 
done

lemma of_int_le_iff [simp]:
     "(of_int w \<le> (of_int z::'a::ordered_ring)) = (w \<le> z)"
apply (rule eq_Abs_Integ [of w])
apply (rule eq_Abs_Integ [of z])
apply (simp add: compare_rls of_int zle zdiff_def zadd zminus 
                 of_nat_add [symmetric]   del: of_nat_add) 
done

text{*Special cases where either operand is zero*}
declare of_int_le_iff [of 0, simplified, simp]
declare of_int_le_iff [of _ 0, simplified, simp]

lemma of_int_less_iff [simp]:
     "(of_int w < (of_int z::'a::ordered_ring)) = (w < z)"
by (simp add: linorder_not_le [symmetric])

text{*Special cases where either operand is zero*}
declare of_int_less_iff [of 0, simplified, simp]
declare of_int_less_iff [of _ 0, simplified, simp]

text{*The ordering on the ring is necessary. See @{text of_nat_eq_iff} above.*}
lemma of_int_eq_iff [simp]:
     "(of_int w = (of_int z::'a::ordered_ring)) = (w = z)"
by (simp add: order_eq_iff) 

text{*Special cases where either operand is zero*}
declare of_int_eq_iff [of 0, simplified, simp]
declare of_int_eq_iff [of _ 0, simplified, simp]


subsection{*The Set of Integers*}

constdefs
   Ints  :: "'a::ring set"
    "Ints == range of_int"


syntax (xsymbols)
  Ints      :: "'a set"                   ("\<int>")

lemma Ints_0 [simp]: "0 \<in> Ints"
apply (simp add: Ints_def) 
apply (rule range_eqI) 
apply (rule of_int_0 [symmetric])
done

lemma Ints_1 [simp]: "1 \<in> Ints"
apply (simp add: Ints_def) 
apply (rule range_eqI) 
apply (rule of_int_1 [symmetric])
done

lemma Ints_add [simp]: "[|a \<in> Ints; b \<in> Ints|] ==> a+b \<in> Ints"
apply (auto simp add: Ints_def) 
apply (rule range_eqI) 
apply (rule of_int_add [symmetric])
done

lemma Ints_minus [simp]: "a \<in> Ints ==> -a \<in> Ints"
apply (auto simp add: Ints_def) 
apply (rule range_eqI) 
apply (rule of_int_minus [symmetric])
done

lemma Ints_diff [simp]: "[|a \<in> Ints; b \<in> Ints|] ==> a-b \<in> Ints"
apply (auto simp add: Ints_def) 
apply (rule range_eqI) 
apply (rule of_int_diff [symmetric])
done

lemma Ints_mult [simp]: "[|a \<in> Ints; b \<in> Ints|] ==> a*b \<in> Ints"
apply (auto simp add: Ints_def) 
apply (rule range_eqI) 
apply (rule of_int_mult [symmetric])
done

text{*Collapse nested embeddings*}
lemma of_int_of_nat_eq [simp]: "of_int (of_nat n) = of_nat n"
by (induct n, auto) 

lemma of_int_int_eq [simp]: "of_int (int n) = int n"
by (simp add: int_eq_of_nat) 


lemma Ints_cases [case_names of_int, cases set: Ints]:
  "q \<in> \<int> ==> (!!z. q = of_int z ==> C) ==> C"
proof (unfold Ints_def)
  assume "!!z. q = of_int z ==> C"
  assume "q \<in> range of_int" thus C ..
qed

lemma Ints_induct [case_names of_int, induct set: Ints]:
  "q \<in> \<int> ==> (!!z. P (of_int z)) ==> P q"
  by (rule Ints_cases) auto


(* int (Suc n) = 1 + int n *)
declare int_Suc [simp]

text{*Simplification of @{term "x-y < 0"}, etc.*}
declare less_iff_diff_less_0 [symmetric, simp]
declare eq_iff_diff_eq_0 [symmetric, simp]
declare le_iff_diff_le_0 [symmetric, simp]


subsection{*More Properties of @{term setsum} and  @{term setprod}*}

text{*By Jeremy Avigad*}


lemma setsum_of_nat: "of_nat (setsum f A) = setsum (of_nat \<circ> f) A"
  apply (case_tac "finite A")
  apply (erule finite_induct, auto)
  apply (simp add: setsum_def)
  done

lemma setsum_of_int: "of_int (setsum f A) = setsum (of_int \<circ> f) A"
  apply (case_tac "finite A")
  apply (erule finite_induct, auto)
  apply (simp add: setsum_def)
  done

lemma int_setsum: "int (setsum f A) = setsum (int \<circ> f) A"
  by (subst int_eq_of_nat, rule setsum_of_nat)

lemma setprod_of_nat: "of_nat (setprod f A) = setprod (of_nat \<circ> f) A"
  apply (case_tac "finite A")
  apply (erule finite_induct, auto)
  apply (simp add: setprod_def)
  done

lemma setprod_of_int: "of_int (setprod f A) = setprod (of_int \<circ> f) A"
  apply (case_tac "finite A")
  apply (erule finite_induct, auto)
  apply (simp add: setprod_def)
  done

lemma int_setprod: "int (setprod f A) = setprod (int \<circ> f) A"
  by (subst int_eq_of_nat, rule setprod_of_nat)

lemma setsum_constant: "finite A ==> (\<Sum>x \<in> A. y) = of_nat(card A) * y"
  apply (erule finite_induct)
  apply (auto simp add: ring_distrib add_ac)
  done

lemma setprod_nonzero_nat:
    "finite A ==> (\<forall>x \<in> A. f x \<noteq> (0::nat)) ==> setprod f A \<noteq> 0"
  by (rule setprod_nonzero, auto)

lemma setprod_zero_eq_nat:
    "finite A ==> (setprod f A = (0::nat)) = (\<exists>x \<in> A. f x = 0)"
  by (rule setprod_zero_eq, auto)

lemma setprod_nonzero_int:
    "finite A ==> (\<forall>x \<in> A. f x \<noteq> (0::int)) ==> setprod f A \<noteq> 0"
  by (rule setprod_nonzero, auto)

lemma setprod_zero_eq_int:
    "finite A ==> (setprod f A = (0::int)) = (\<exists>x \<in> A. f x = 0)"
  by (rule setprod_zero_eq, auto)


(*Legacy ML bindings, but no longer the structure Int.*)
ML
{*
val zabs_def = thm "zabs_def"
val nat_def  = thm "nat_def"

val int_0 = thm "int_0";
val int_1 = thm "int_1";
val int_Suc0_eq_1 = thm "int_Suc0_eq_1";
val neg_eq_less_0 = thm "neg_eq_less_0";
val not_neg_eq_ge_0 = thm "not_neg_eq_ge_0";
val not_neg_0 = thm "not_neg_0";
val not_neg_1 = thm "not_neg_1";
val iszero_0 = thm "iszero_0";
val not_iszero_1 = thm "not_iszero_1";
val int_0_less_1 = thm "int_0_less_1";
val int_0_neq_1 = thm "int_0_neq_1";
val negative_zless = thm "negative_zless";
val negative_zle = thm "negative_zle";
val not_zle_0_negative = thm "not_zle_0_negative";
val not_int_zless_negative = thm "not_int_zless_negative";
val negative_eq_positive = thm "negative_eq_positive";
val zle_iff_zadd = thm "zle_iff_zadd";
val abs_int_eq = thm "abs_int_eq";
val abs_split = thm"abs_split";
val nat_int = thm "nat_int";
val nat_zminus_int = thm "nat_zminus_int";
val nat_zero = thm "nat_zero";
val not_neg_nat = thm "not_neg_nat";
val neg_nat = thm "neg_nat";
val zless_nat_eq_int_zless = thm "zless_nat_eq_int_zless";
val nat_0_le = thm "nat_0_le";
val nat_le_0 = thm "nat_le_0";
val zless_nat_conj = thm "zless_nat_conj";
val int_cases = thm "int_cases";

val int_def = thm "int_def";
val Zero_int_def = thm "Zero_int_def";
val One_int_def = thm "One_int_def";
val zadd_def = thm "zadd_def";
val zdiff_def = thm "zdiff_def";
val zless_def = thm "zless_def";
val zle_def = thm "zle_def";
val zmult_def = thm "zmult_def";

val intrel_iff = thm "intrel_iff";
val equiv_intrel = thm "equiv_intrel";
val equiv_intrel_iff = thm "equiv_intrel_iff";
val intrel_in_integ = thm "intrel_in_integ";
val inj_on_Abs_Integ = thm "inj_on_Abs_Integ";
val inj_Rep_Integ = thm "inj_Rep_Integ";
val inj_int = thm "inj_int";
val zminus_congruent = thm "zminus_congruent";
val zminus = thm "zminus";
val eq_Abs_Integ = thm "eq_Abs_Integ";
val zminus_zminus = thm "zminus_zminus";
val inj_zminus = thm "inj_zminus";
val zminus_0 = thm "zminus_0";
val zadd = thm "zadd";
val zminus_zadd_distrib = thm "zminus_zadd_distrib";
val zadd_commute = thm "zadd_commute";
val zadd_assoc = thm "zadd_assoc";
val zadd_left_commute = thm "zadd_left_commute";
val zadd_ac = thms "zadd_ac";
val zmult_ac = thms "zmult_ac";
val zadd_int = thm "zadd_int";
val zadd_int_left = thm "zadd_int_left";
val int_Suc = thm "int_Suc";
val zadd_0 = thm "zadd_0";
val zadd_0_right = thm "zadd_0_right";
val zadd_zminus_inverse = thm "zadd_zminus_inverse";
val zadd_zminus_inverse2 = thm "zadd_zminus_inverse2";
val zadd_zminus_cancel = thm "zadd_zminus_cancel";
val zminus_zadd_cancel = thm "zminus_zadd_cancel";
val zdiff0 = thm "zdiff0";
val zdiff0_right = thm "zdiff0_right";
val zdiff_self = thm "zdiff_self";
val zmult_congruent2 = thm "zmult_congruent2";
val zmult = thm "zmult";
val zmult_zminus = thm "zmult_zminus";
val zmult_commute = thm "zmult_commute";
val zmult_assoc = thm "zmult_assoc";
val zadd_zmult_distrib = thm "zadd_zmult_distrib";
val zmult_zminus_right = thm "zmult_zminus_right";
val zadd_zmult_distrib2 = thm "zadd_zmult_distrib2";
val zdiff_zmult_distrib = thm "zdiff_zmult_distrib";
val zdiff_zmult_distrib2 = thm "zdiff_zmult_distrib2";
val int_distrib = thms "int_distrib";
val zmult_int = thm "zmult_int";
val zmult_0 = thm "zmult_0";
val zmult_1 = thm "zmult_1";
val zmult_0_right = thm "zmult_0_right";
val zmult_1_right = thm "zmult_1_right";
val zless_iff_Suc_zadd = thm "zless_iff_Suc_zadd";
val int_int_eq = thm "int_int_eq";
val int_eq_0_conv = thm "int_eq_0_conv";
val zless_int = thm "zless_int";
val int_less_0_conv = thm "int_less_0_conv";
val zero_less_int_conv = thm "zero_less_int_conv";
val zle_int = thm "zle_int";
val zero_zle_int = thm "zero_zle_int";
val int_le_0_conv = thm "int_le_0_conv";
val zle_refl = thm "zle_refl";
val zle_linear = thm "zle_linear";
val zle_trans = thm "zle_trans";
val zle_anti_sym = thm "zle_anti_sym";

val Ints_def = thm "Ints_def";
val Nats_def = thm "Nats_def";

val of_nat_0 = thm "of_nat_0";
val of_nat_Suc = thm "of_nat_Suc";
val of_nat_1 = thm "of_nat_1";
val of_nat_add = thm "of_nat_add";
val of_nat_mult = thm "of_nat_mult";
val zero_le_imp_of_nat = thm "zero_le_imp_of_nat";
val less_imp_of_nat_less = thm "less_imp_of_nat_less";
val of_nat_less_imp_less = thm "of_nat_less_imp_less";
val of_nat_less_iff = thm "of_nat_less_iff";
val of_nat_le_iff = thm "of_nat_le_iff";
val of_nat_eq_iff = thm "of_nat_eq_iff";
val Nats_0 = thm "Nats_0";
val Nats_1 = thm "Nats_1";
val Nats_add = thm "Nats_add";
val Nats_mult = thm "Nats_mult";
val int_eq_of_nat = thm"int_eq_of_nat";
val of_int = thm "of_int";
val of_int_0 = thm "of_int_0";
val of_int_1 = thm "of_int_1";
val of_int_add = thm "of_int_add";
val of_int_minus = thm "of_int_minus";
val of_int_diff = thm "of_int_diff";
val of_int_mult = thm "of_int_mult";
val of_int_le_iff = thm "of_int_le_iff";
val of_int_less_iff = thm "of_int_less_iff";
val of_int_eq_iff = thm "of_int_eq_iff";
val Ints_0 = thm "Ints_0";
val Ints_1 = thm "Ints_1";
val Ints_add = thm "Ints_add";
val Ints_minus = thm "Ints_minus";
val Ints_diff = thm "Ints_diff";
val Ints_mult = thm "Ints_mult";
val of_int_of_nat_eq = thm"of_int_of_nat_eq";
val Ints_cases = thm "Ints_cases";
val Ints_induct = thm "Ints_induct";
*}

end
