(*  Title:      Integ/Int.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header {*Type "int" is a Linear Order and Other Lemmas*}

theory Int = IntDef:

instance int :: order
proof qed (assumption | rule zle_refl zle_trans zle_anti_sym int_less_le)+

instance int :: plus_ac0
proof qed (rule zadd_commute zadd_assoc zadd_0)+

instance int :: linorder
proof qed (rule zle_linear)

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

lemma int_0_less_1: "0 < (1::int)"
by (simp only: Zero_int_def One_int_def One_nat_def zless_int)

lemma int_0_neq_1 [simp]: "0 \<noteq> (1::int)"
by (simp only: Zero_int_def One_int_def One_nat_def int_int_eq)



subsection{*@{text Abel_Cancel} simproc on the integers*}

(* Lemmas needed for the simprocs *)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
lemma zadd_cancel_21: "((x::int) + (y + z) = y + u) = ((x + z) = u)"
apply (subst zadd_left_commute)
apply (rule zadd_left_cancel)
done

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
lemma zadd_cancel_end: "((x::int) + (y + z) = y) = (x = -z)"
apply (subst zadd_left_commute)
apply (rule_tac t = y in zadd_0_right [THEN subst], subst zadd_left_cancel)
apply (simp add: eq_zdiff_eq [symmetric])
done

(*Legacy ML bindings, but no longer the structure Int.*)
ML
{*
val Int_thy = the_context ()
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
val zadd_cancel_21 = thm "zadd_cancel_21";
val zadd_cancel_end = thm "zadd_cancel_end";

structure Int_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val sg_ref 		= Sign.self_ref (Theory.sign_of (the_context()))
  val T		= HOLogic.intT
  val zero		= Const ("0", HOLogic.intT)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= zadd_cancel_21
  val add_cancel_end	= zadd_cancel_end
  val add_left_cancel	= zadd_left_cancel
  val add_assoc		= zadd_assoc
  val add_commute	= zadd_commute
  val add_left_commute	= zadd_left_commute
  val add_0		= zadd_0
  val add_0_right	= zadd_0_right

  val eq_diff_eq	= eq_zdiff_eq
  val eqI_rules		= [zless_eqI, zeq_eqI, zle_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= zdiff_def
  val minus_add_distrib	= zminus_zadd_distrib
  val minus_minus	= zminus_zminus
  val minus_0		= zminus_0
  val add_inverses	= [zadd_zminus_inverse, zadd_zminus_inverse2]
  val cancel_simps	= [zadd_zminus_cancel, zminus_zadd_cancel]
end;

structure Int_Cancel = Abel_Cancel (Int_Cancel_Data);

Addsimprocs [Int_Cancel.sum_conv, Int_Cancel.rel_conv];
*}


subsection{*Misc Results*}

lemma zminus_zdiff_eq [simp]: "- (z - y) = y - (z::int)"
by simp

lemma zless_eq_neg: "(w<z) = neg(w-z)"
by (simp add: zless_def)

lemma eq_eq_iszero: "(w=z) = iszero(w-z)"
by (simp add: iszero_def zdiff_eq_eq)

lemma zle_eq_not_neg: "(w\<le>z) = (~ neg(z-w))"
by (simp add: zle_def zless_def)

subsection{*Inequality reasoning*}

lemma zless_add1_eq: "(w < z + (1::int)) = (w<z | w=z)"
apply (auto simp add: zless_iff_Suc_zadd int_Suc gr0_conv_Suc zero_reorient)
apply (rule_tac x = "Suc n" in exI)
apply (simp add: int_Suc)
done

lemma add1_zle_eq: "(w + (1::int) \<le> z) = (w<z)"
apply (simp add: zle_def zless_add1_eq)
apply (auto intro: zless_asym zle_anti_sym
            simp add: order_less_imp_le symmetric zle_def)
done

lemma add1_left_zle_eq: "((1::int) + w \<le> z) = (w<z)"
apply (subst zadd_commute)
apply (rule add1_zle_eq)
done


subsection{*Monotonicity results*}

lemma zadd_right_cancel_zless [simp]: "(v+z < w+z) = (v < (w::int))"
by simp

lemma zadd_left_cancel_zless [simp]: "(z+v < z+w) = (v < (w::int))"
by simp

lemma zadd_right_cancel_zle [simp] : "(v+z \<le> w+z) = (v \<le> (w::int))"
by simp

lemma zadd_left_cancel_zle [simp] : "(z+v \<le> z+w) = (v \<le> (w::int))"
by simp

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


subsection{*Comparison laws*}

lemma zminus_zless_zminus [simp]: "(- x < - y) = (y < (x::int))"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zminus_zle_zminus [simp]: "(- x \<le> - y) = (y \<le> (x::int))"
by (simp add: zle_def)

text{*The next several equations can make the simplifier loop!*}

lemma zless_zminus: "(x < - y) = (y < - (x::int))"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zminus_zless: "(- x < y) = (- y < (x::int))"
by (simp add: zless_def zdiff_def zadd_ac)

lemma zle_zminus: "(x \<le> - y) = (y \<le> - (x::int))"
by (simp add: zle_def zminus_zless)

lemma zminus_zle: "(- x \<le> y) = (- y \<le> (x::int))"
by (simp add: zle_def zless_zminus)

lemma equation_zminus: "(x = - y) = (y = - (x::int))"
by auto

lemma zminus_equation: "(- x = y) = (- (y::int) = x)"
by auto


subsection{*Instances of the equations above, for zero*}

(*instantiate a variable to zero and simplify*)

declare zless_zminus [of 0, simplified, simp]
declare zminus_zless [of _ 0, simplified, simp]
declare zle_zminus   [of 0, simplified, simp]
declare zminus_zle [of _ 0, simplified, simp]
declare equation_zminus [of 0, simplified, simp]
declare zminus_equation [of _ 0, simplified, simp]

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

lemma zle_iff_zadd: "(w \<le> z) = (EX n. z = w + int n)"
by (force intro: exI [of _ "0::nat"] 
            intro!: not_sym [THEN not0_implies_Suc]
            simp add: zless_iff_Suc_zadd int_le_less)

lemma abs_int_eq [simp]: "abs (int m) = int m"
by (simp add: zabs_def)


subsection{*nat: magnitide of an integer, as a natural number*}

lemma nat_int [simp]: "nat(int n) = n"
by (unfold nat_def, auto)

lemma nat_zminus_int [simp]: "nat(- (int n)) = 0"
apply (unfold nat_def)
apply (auto simp add: neg_eq_less_0 zero_reorient zminus_zless)
done

lemma nat_zero [simp]: "nat 0 = 0"
apply (unfold Zero_int_def)
apply (rule nat_int)
done

lemma not_neg_nat: "~ neg z ==> int (nat z) = z"
apply (drule not_neg_eq_ge_0 [THEN iffD1])
apply (drule zle_imp_zless_or_eq)
apply (auto simp add: zless_iff_Suc_zadd)
done

lemma negD: "neg x ==> EX n. x = - (int (Suc n))"
by (auto simp add: neg_eq_less_0 zless_iff_Suc_zadd zdiff_eq_eq [symmetric] zdiff_def)

lemma neg_nat: "neg z ==> nat z = 0"
by (unfold nat_def, auto)

lemma zless_nat_eq_int_zless: "(m < nat z) = (int m < z)"
apply (case_tac "neg z")
apply (erule_tac [2] not_neg_nat [THEN subst])
apply (auto simp add: neg_nat)
apply (auto dest: order_less_trans simp add: neg_eq_less_0)
done

lemma nat_0_le [simp]: "0 \<le> z ==> int (nat z) = z"
by (simp add: neg_eq_less_0 zle_def not_neg_nat)

lemma nat_le_0 [simp]: "z \<le> 0 ==> nat z = 0"
by (auto simp add: order_le_less neg_eq_less_0 zle_def neg_nat)

(*An alternative condition is  0 \<le> w  *)
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

(* a case theorem distinguishing non-negative and negative int *)  

lemma int_cases: 
     "[|!! n. z = int n ==> P;  !! n. z =  - (int (Suc n)) ==> P |] ==> P"
apply (case_tac "neg z")
apply (fast dest!: negD)
apply (drule not_neg_nat [symmetric], auto) 
done


subsection{*Monotonicity of Multiplication*}

lemma zmult_zle_mono1_lemma: "i \<le> (j::int) ==> i * int k \<le> j * int k"
apply (induct_tac "k")
apply (simp_all (no_asm_simp) add: int_Suc zadd_zmult_distrib2 zadd_zle_mono int_Suc0_eq_1)
done

lemma zmult_zle_mono1: "[| i \<le> j;  (0::int) \<le> k |] ==> i*k \<le> j*k"
apply (rule_tac t = k in not_neg_nat [THEN subst])
apply (erule_tac [2] zmult_zle_mono1_lemma)
apply (simp (no_asm_use) add: not_neg_eq_ge_0)
done

lemma zmult_zle_mono1_neg: "[| i \<le> j;  k \<le> (0::int) |] ==> j*k \<le> i*k"
apply (rule zminus_zle_zminus [THEN iffD1])
apply (simp add: zmult_zminus_right [symmetric] zmult_zle_mono1 zle_zminus)
done

lemma zmult_zle_mono2: "[| i \<le> j;  (0::int) \<le> k |] ==> k*i \<le> k*j"
apply (drule zmult_zle_mono1)
apply (simp_all add: zmult_commute)
done

lemma zmult_zle_mono2_neg: "[| i \<le> j;  k \<le> (0::int) |] ==> k*j \<le> k*i"
apply (drule zmult_zle_mono1_neg)
apply (simp_all add: zmult_commute)
done

(* \<le> monotonicity, BOTH arguments*)
lemma zmult_zle_mono: "[| i \<le> j;  k \<le> l;  (0::int) \<le> j;  (0::int) \<le> k |] ==> i*k \<le> j*l"
apply (erule zmult_zle_mono1 [THEN order_trans], assumption)
apply (erule zmult_zle_mono2, assumption)
done


subsection{*strict, in 1st argument; proof is by induction on k>0*}

lemma zmult_zless_mono2_lemma: "i<j ==> 0<k --> int k * i < int k * j"
apply (induct_tac "k", simp) 
apply (simp add: int_Suc)
apply (case_tac "n=0")
apply (simp_all add: zadd_zmult_distrib zadd_zless_mono int_Suc0_eq_1 order_le_less)
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
  show "(i + j) + k = i + (j + k)" by simp
  show "i + j = j + i" by simp
  show "0 + i = i" by simp
  show "- i + i = 0" by simp
  show "i - j = i + (-j)" by simp
  show "(i * j) * k = i * (j * k)" by (rule zmult_assoc)
  show "i * j = j * i" by (rule zmult_commute)
  show "1 * i = i" by simp
  show "(i + j) * k = i * k + j * k" by (simp add: int_distrib)
  show "0 \<noteq> (1::int)" by simp
  show "i \<le> j ==> k + i \<le> k + j" by simp
  show "i < j ==> 0 < k ==> k * i < k * j" by (simp add: zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)" by (simp only: zabs_def)
qed

lemma zmult_zless_mono1: "[| i<j;  (0::int) < k |] ==> i*k < j*k"
  by (rule Ring_and_Field.mult_strict_right_mono)

(* < monotonicity, BOTH arguments*)
lemma zmult_zless_mono:
     "[| i < j;  k < l;  (0::int) < j;  (0::int) < k |] ==> i*k < j*l"
  by (rule Ring_and_Field.mult_strict_mono)

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

(*Analogous to zadd_int*)
lemma zdiff_int [rule_format]: "n\<le>m --> int m - int n = int (m-n)"
apply (induct_tac m n rule: diff_induct)
apply (auto simp add: int_Suc symmetric zdiff_def)
done



ML
{*
val zminus_zdiff_eq = thm "zminus_zdiff_eq";
val zless_eq_neg = thm "zless_eq_neg";
val eq_eq_iszero = thm "eq_eq_iszero";
val zle_eq_not_neg = thm "zle_eq_not_neg";
val zless_add1_eq = thm "zless_add1_eq";
val add1_zle_eq = thm "add1_zle_eq";
val add1_left_zle_eq = thm "add1_left_zle_eq";
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
val negative_zless_0 = thm "negative_zless_0";
val negative_zless = thm "negative_zless";
val negative_zle_0 = thm "negative_zle_0";
val negative_zle = thm "negative_zle";
val not_zle_0_negative = thm "not_zle_0_negative";
val int_zle_neg = thm "int_zle_neg";
val not_int_zless_negative = thm "not_int_zless_negative";
val negative_eq_positive = thm "negative_eq_positive";
val zle_iff_zadd = thm "zle_iff_zadd";
val abs_int_eq = thm "abs_int_eq";
val nat_int = thm "nat_int";
val nat_zminus_int = thm "nat_zminus_int";
val nat_zero = thm "nat_zero";
val not_neg_nat = thm "not_neg_nat";
val negD = thm "negD";
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
val zmult_zless_mono = thm "zmult_zless_mono";
val zmult_zless_mono1_neg = thm "zmult_zless_mono1_neg";
val zmult_zless_mono2_neg = thm "zmult_zless_mono2_neg";
val zmult_eq_0_iff = thm "zmult_eq_0_iff";
val zmult_zless_cancel2 = thm "zmult_zless_cancel2";
val zmult_zless_cancel1 = thm "zmult_zless_cancel1";
val zmult_zle_cancel2 = thm "zmult_zle_cancel2";
val zmult_zle_cancel1 = thm "zmult_zle_cancel1";
val zmult_cancel2 = thm "zmult_cancel2";
val zmult_cancel1 = thm "zmult_cancel1";
val zdiff_int = thm "zdiff_int";
*}

end
