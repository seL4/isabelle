(*  Title:      Integ/Int.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header {*Type "int" is an Ordered Ring and Other Lemmas*}

theory Int = IntDef:

constdefs
   nat  :: "int => nat"
    "nat(Z) == if neg Z then 0 else (THE m. Z = int m)"

defs (overloaded)
    zabs_def:  "abs(i::int) == if i < 0 then -i else i"


lemma int_0 [simp]: "int 0 = (0::int)"
by (simp add: Zero_int_def)

lemma int_1 [simp]: "int 1 = 1"
by (simp add: One_int_def)

lemma int_Suc0_eq_1: "int (Suc 0) = 1"
by (simp add: One_int_def One_nat_def)

lemma neg_eq_less_0: "neg x = (x < 0)"
by (unfold zdiff_def zless_def, auto)

lemma not_neg_eq_ge_0: "(~neg x) = (0 \<le> x)"
apply (unfold zle_def)
apply (simp add: neg_eq_less_0)
done

subsection{*To simplify inequalities when Numeral1 can get simplified to 1*}

lemma not_neg_0: "~ neg 0"
by (simp add: One_int_def neg_eq_less_0)

lemma not_neg_1: "~ neg 1"
by (simp add: One_int_def neg_eq_less_0)

lemma iszero_0: "iszero 0"
by (simp add: iszero_def)

lemma not_iszero_1: "~ iszero 1"
by (simp only: Zero_int_def One_int_def One_nat_def iszero_def int_int_eq)


subsection{*nat: magnitide of an integer, as a natural number*}

lemma nat_int [simp]: "nat(int n) = n"
by (unfold nat_def, auto)

lemma nat_zero [simp]: "nat 0 = 0"
apply (unfold Zero_int_def)
apply (rule nat_int)
done

lemma neg_nat: "neg z ==> nat z = 0"
by (unfold nat_def, auto)

lemma not_neg_nat: "~ neg z ==> int (nat z) = z"
apply (drule not_neg_eq_ge_0 [THEN iffD1])
apply (drule zle_imp_zless_or_eq)
apply (auto simp add: zless_iff_Suc_zadd)
done

lemma nat_0_le [simp]: "0 \<le> z ==> int (nat z) = z"
by (simp add: neg_eq_less_0 zle_def not_neg_nat)

lemma nat_le_0 [simp]: "z \<le> 0 ==> nat z = 0"
by (auto simp add: order_le_less neg_eq_less_0 zle_def neg_nat)

text{*An alternative condition is @{term "0 \<le> w"} *}
lemma nat_mono_iff: "0 < z ==> (nat w < nat z) = (w < z)"
apply (subst zless_int [symmetric])
apply (simp (no_asm_simp) add: not_neg_nat not_neg_eq_ge_0 order_le_less)
apply (case_tac "neg w")
 apply (simp add: neg_eq_less_0 neg_nat)
 apply (blast intro: order_less_trans)
apply (simp add: not_neg_nat)
done

lemma zless_nat_conj: "(nat w < nat z) = (0 < z & w < z)"
apply (case_tac "0 < z")
apply (auto simp add: nat_mono_iff linorder_not_less)
done

subsection{*Monotonicity results*}

text{*Most are available in theory @{text Ring_and_Field}, but they are
      not yet available: we must prove @{text zadd_zless_mono} before we
      can prove that the integers are a ring.*}

lemma zadd_right_cancel_zless [simp]: "(v+z < w+z) = (v < (w::int))"
by (simp add: zless_def zdiff_def zadd_ac) 

lemma zadd_left_cancel_zless [simp]: "(z+v < z+w) = (v < (w::int))"
by (simp add: zless_def zdiff_def zadd_ac) 

lemma zadd_right_cancel_zle [simp] : "(v+z \<le> w+z) = (v \<le> (w::int))"
by (simp add: linorder_not_less [symmetric]) 

lemma zadd_left_cancel_zle [simp] : "(z+v \<le> z+w) = (v \<le> (w::int))"
by (simp add: linorder_not_less [symmetric]) 

(*"v\<le>w ==> v+z \<le> w+z"*)
lemmas zadd_zless_mono1 = zadd_right_cancel_zless [THEN iffD2, standard]

(*"v\<le>w ==> z+v \<le> z+w"*)
lemmas zadd_zless_mono2 = zadd_left_cancel_zless [THEN iffD2, standard]

(*"v\<le>w ==> v+z \<le> w+z"*)
lemmas zadd_zle_mono1 = zadd_right_cancel_zle [THEN iffD2, standard]

(*"v\<le>w ==> z+v \<le> z+w"*)
lemmas zadd_zle_mono2 = zadd_left_cancel_zle [THEN iffD2, standard]

lemma zadd_zle_mono: "[| w'\<le>w; z'\<le>z |] ==> w' + z' \<le> w + (z::int)"
by (erule zadd_zle_mono1 [THEN zle_trans], simp)

lemma zadd_zless_mono: "[| w'<w; z'\<le>z |] ==> w' + z' < w + (z::int)"
by (erule zadd_zless_mono1 [THEN order_less_le_trans], simp)


subsection{*Strict Monotonicity of Multiplication*}

text{*strict, in 1st argument; proof is by induction on k>0*}
lemma zmult_zless_mono2_lemma: "i<j ==> 0<k --> int k * i < int k * j"
apply (induct_tac "k", simp) 
apply (simp add: int_Suc)
apply (case_tac "n=0")
apply (simp_all add: zadd_zmult_distrib int_Suc0_eq_1 order_le_less)
apply (simp_all add: zadd_zless_mono int_Suc0_eq_1 order_le_less)
done

lemma zmult_zless_mono2: "[| i<j;  (0::int) < k |] ==> k*i < k*j"
apply (rule_tac t = k in not_neg_nat [THEN subst])
apply (erule_tac [2] zmult_zless_mono2_lemma [THEN mp])
apply (simp add: not_neg_eq_ge_0 order_le_less)
apply (frule conjI [THEN zless_nat_conj [THEN iffD2]], auto)
done


text{*The Integers Form an Ordered Ring*}
instance int :: ordered_ring
proof
  fix i j k :: int
  show "i \<le> j ==> k + i \<le> k + j" by simp
  show "i < j ==> 0 < k ==> k * i < k * j" by (simp add: zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)" by (simp only: zabs_def)
qed


subsection{*Comparison laws*}

text{*Legacy bindings: all are in theory @{text Ring_and_Field}.*}

lemma zminus_zless_zminus: "(- x < - y) = (y < (x::int))"
  by (rule Ring_and_Field.neg_less_iff_less)

lemma zminus_zle_zminus: "(- x \<le> - y) = (y \<le> (x::int))"
  by (rule Ring_and_Field.neg_le_iff_le)


text{*The next several equations can make the simplifier loop!*}

lemma zless_zminus: "(x < - y) = (y < - (x::int))"
  by (rule Ring_and_Field.less_minus_iff)

lemma zminus_zless: "(- x < y) = (- y < (x::int))"
  by (rule Ring_and_Field.minus_less_iff)

lemma zle_zminus: "(x \<le> - y) = (y \<le> - (x::int))"
  by (rule Ring_and_Field.le_minus_iff)

lemma zminus_zle: "(- x \<le> y) = (- y \<le> (x::int))"
  by (rule Ring_and_Field.minus_le_iff)

lemma equation_zminus: "(x = - y) = (y = - (x::int))"
  by (rule Ring_and_Field.equation_minus_iff)

lemma zminus_equation: "(- x = y) = (- (y::int) = x)"
  by (rule Ring_and_Field.minus_equation_iff)


subsection{*Lemmas about the Function @{term int} and Orderings*}

lemma negative_zless_0: "- (int (Suc n)) < 0"
by (simp add: zless_def)

lemma negative_zless [iff]: "- (int (Suc n)) < int m"
by (rule negative_zless_0 [THEN order_less_le_trans], simp)

lemma negative_zle_0: "- int n \<le> 0"
by (simp add: zminus_zle)

lemma negative_zle [iff]: "- int n \<le> int m"
by (simp add: zless_def zle_def zdiff_def zadd_int)

lemma not_zle_0_negative [simp]: "~(0 \<le> - (int (Suc n)))"
by (subst zle_zminus, simp)

lemma int_zle_neg: "(int n \<le> - int m) = (n = 0 & m = 0)"
apply safe 
apply (drule_tac [2] zle_zminus [THEN iffD1])
apply (auto dest: zle_trans [OF _ negative_zle_0]) 
done

lemma not_int_zless_negative [simp]: "~(int n < - int m)"
by (simp add: zle_def [symmetric])

lemma negative_eq_positive [simp]: "(- int n = int m) = (n = 0 & m = 0)"
apply (rule iffI)
apply (rule int_zle_neg [THEN iffD1])
apply (drule sym)
apply (simp_all (no_asm_simp))
done

lemma zle_iff_zadd: "(w \<le> z) = (\<exists>n. z = w + int n)"
by (force intro: exI [of _ "0::nat"] 
            intro!: not_sym [THEN not0_implies_Suc]
            simp add: zless_iff_Suc_zadd int_le_less)

lemma abs_int_eq [simp]: "abs (int m) = int m"
by (simp add: zabs_def)

text{*This version is proved for all ordered rings, not just integers!
      But is it really better than just rewriting with @{text abs_if}?*}
lemma abs_split [arith_split]:
     "P(abs(a::'a::ordered_ring)) = ((0 \<le> a --> P a) & (a < 0 --> P(-a)))"
by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)


subsection{*Misc Results*}

lemma nat_zminus_int [simp]: "nat(- (int n)) = 0"
apply (unfold nat_def)
apply (auto simp add: neg_eq_less_0 zero_reorient zminus_zless)
done

lemma zless_nat_eq_int_zless: "(m < nat z) = (int m < z)"
apply (case_tac "neg z")
apply (erule_tac [2] not_neg_nat [THEN subst])
apply (auto simp add: neg_nat)
apply (auto dest: order_less_trans simp add: neg_eq_less_0)
done

lemma zless_eq_neg: "(w<z) = neg(w-z)"
by (simp add: zless_def)

lemma eq_eq_iszero: "(w=z) = iszero(w-z)"
by (simp add: iszero_def diff_eq_eq)

lemma zle_eq_not_neg: "(w\<le>z) = (~ neg(z-w))"
by (simp add: zle_def zless_def)


subsection{*Monotonicity of Multiplication*}

lemma zmult_zle_mono1: "[| i \<le> j;  (0::int) \<le> k |] ==> i*k \<le> j*k"
  by (rule Ring_and_Field.mult_right_mono)

lemma zmult_zle_mono1_neg: "[| i \<le> j;  k \<le> (0::int) |] ==> j*k \<le> i*k"
  by (rule Ring_and_Field.mult_right_mono_neg)

lemma zmult_zle_mono2: "[| i \<le> j;  (0::int) \<le> k |] ==> k*i \<le> k*j"
  by (rule Ring_and_Field.mult_left_mono)

lemma zmult_zle_mono2_neg: "[| i \<le> j;  k \<le> (0::int) |] ==> k*j \<le> k*i"
  by (rule Ring_and_Field.mult_left_mono_neg)

(* \<le> monotonicity, BOTH arguments*)
lemma zmult_zle_mono:
     "[| i \<le> j;  k \<le> l;  (0::int) \<le> j;  (0::int) \<le> k |] ==> i*k \<le> j*l"
  by (rule Ring_and_Field.mult_mono)

lemma zmult_zless_mono1: "[| i<j;  (0::int) < k |] ==> i*k < j*k"
  by (rule Ring_and_Field.mult_strict_right_mono)

lemma zmult_zless_mono1_neg: "[| i<j;  k < (0::int) |] ==> j*k < i*k"
  by (rule Ring_and_Field.mult_strict_right_mono_neg)

lemma zmult_zless_mono2_neg: "[| i<j;  k < (0::int) |] ==> k*j < k*i"
  by (rule Ring_and_Field.mult_strict_left_mono_neg)

lemma zmult_eq_0_iff [iff]: "(m*n = (0::int)) = (m = 0 | n = 0)"
  by simp

lemma zmult_zless_cancel2: "(m*k < n*k) = (((0::int) < k & m<n) | (k<0 & n<m))"
  by (rule Ring_and_Field.mult_less_cancel_right)

lemma zmult_zless_cancel1:
     "(k*m < k*n) = (((0::int) < k & m<n) | (k < 0 & n<m))"
  by (rule Ring_and_Field.mult_less_cancel_left)

lemma zmult_zle_cancel2:
     "(m*k \<le> n*k) = (((0::int) < k --> m\<le>n) & (k < 0 --> n\<le>m))"
  by (rule Ring_and_Field.mult_le_cancel_right)

lemma zmult_zle_cancel1:
     "(k*m \<le> k*n) = (((0::int) < k --> m\<le>n) & (k < 0 --> n\<le>m))"
  by (rule Ring_and_Field.mult_le_cancel_left)

lemma zmult_cancel2: "(m*k = n*k) = (k = (0::int) | m=n)"
 by (rule Ring_and_Field.mult_cancel_right)

lemma zmult_cancel1 [simp]: "(k*m = k*n) = (k = (0::int) | m=n)"
 by (rule Ring_and_Field.mult_cancel_left)


text{*A case theorem distinguishing non-negative and negative int*}

lemma negD: "neg x ==> \<exists>n. x = - (int (Suc n))"
by (auto simp add: neg_eq_less_0 zless_iff_Suc_zadd 
                   diff_eq_eq [symmetric] zdiff_def)

lemma int_cases: 
     "[|!! n. z = int n ==> P;  !! n. z =  - (int (Suc n)) ==> P |] ==> P"
apply (case_tac "neg z")
apply (fast dest!: negD)
apply (drule not_neg_nat [symmetric], auto) 
done


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
val zless_eq_neg = thm "zless_eq_neg";
val eq_eq_iszero = thm "eq_eq_iszero";
val zle_eq_not_neg = thm "zle_eq_not_neg";
val zadd_right_cancel_zless = thm "zadd_right_cancel_zless";
val zadd_left_cancel_zless = thm "zadd_left_cancel_zless";
val zadd_right_cancel_zle = thm "zadd_right_cancel_zle";
val zadd_left_cancel_zle = thm "zadd_left_cancel_zle";
val zadd_zless_mono1 = thm "zadd_zless_mono1";
val zadd_zless_mono2 = thm "zadd_zless_mono2";
val zadd_zle_mono1 = thm "zadd_zle_mono1";
val zadd_zle_mono2 = thm "zadd_zle_mono2";
val zadd_zle_mono = thm "zadd_zle_mono";
val zadd_zless_mono = thm "zadd_zless_mono";
val zminus_zless_zminus = thm "zminus_zless_zminus";
val zminus_zle_zminus = thm "zminus_zle_zminus";
val zless_zminus = thm "zless_zminus";
val zminus_zless = thm "zminus_zless";
val zle_zminus = thm "zle_zminus";
val zminus_zle = thm "zminus_zle";
val equation_zminus = thm "equation_zminus";
val zminus_equation = thm "zminus_equation";
val negative_zless = thm "negative_zless";
val negative_zle = thm "negative_zle";
val not_zle_0_negative = thm "not_zle_0_negative";
val not_int_zless_negative = thm "not_int_zless_negative";
val negative_eq_positive = thm "negative_eq_positive";
val zle_iff_zadd = thm "zle_iff_zadd";
val abs_int_eq = thm "abs_int_eq";
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
val zmult_zle_mono1 = thm "zmult_zle_mono1";
val zmult_zle_mono1_neg = thm "zmult_zle_mono1_neg";
val zmult_zle_mono2 = thm "zmult_zle_mono2";
val zmult_zle_mono2_neg = thm "zmult_zle_mono2_neg";
val zmult_zle_mono = thm "zmult_zle_mono";
val zmult_zless_mono2 = thm "zmult_zless_mono2";
val zmult_zless_mono1 = thm "zmult_zless_mono1";
val zmult_zless_mono1_neg = thm "zmult_zless_mono1_neg";
val zmult_zless_mono2_neg = thm "zmult_zless_mono2_neg";
val zmult_eq_0_iff = thm "zmult_eq_0_iff";
val zmult_zless_cancel2 = thm "zmult_zless_cancel2";
val zmult_zless_cancel1 = thm "zmult_zless_cancel1";
val zmult_zle_cancel2 = thm "zmult_zle_cancel2";
val zmult_zle_cancel1 = thm "zmult_zle_cancel1";
val zmult_cancel2 = thm "zmult_cancel2";
val zmult_cancel1 = thm "zmult_cancel1";
*}

end
