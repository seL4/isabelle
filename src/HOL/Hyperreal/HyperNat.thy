(*  Title       : HyperNat.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
*)

header{*Construction of Hypernaturals using Ultrafilters*}

theory HyperNat = Star:

constdefs
    hypnatrel :: "((nat=>nat)*(nat=>nat)) set"
    "hypnatrel == {p. \<exists>X Y. p = ((X::nat=>nat),Y) &
                       {n::nat. X(n) = Y(n)} \<in> FreeUltrafilterNat}"

typedef hypnat = "UNIV//hypnatrel"
    by (auto simp add: quotient_def)

instance hypnat :: ord ..
instance hypnat :: zero ..
instance hypnat :: one ..
instance hypnat :: plus ..
instance hypnat :: times ..
instance hypnat :: minus ..

consts whn :: hypnat

constdefs

  (* embedding the naturals in the hypernaturals *)
  hypnat_of_nat   :: "nat => hypnat"
  "hypnat_of_nat m  == Abs_hypnat(hypnatrel``{%n::nat. m})"

  (* hypernaturals as members of the hyperreals; the set is defined as  *)
  (* the nonstandard extension of set of naturals embedded in the reals *)
  HNat         :: "hypreal set"
  "HNat == *s* {n. \<exists>no::nat. n = real no}"

  (* the set of infinite hypernatural numbers *)
  HNatInfinite :: "hypnat set"
  "HNatInfinite == {n. n \<notin> Nats}"

  (* explicit embedding of the hypernaturals in the hyperreals *)
  hypreal_of_hypnat :: "hypnat => hypreal"
  "hypreal_of_hypnat N  == Abs_hypreal(\<Union>X \<in> Rep_hypnat(N).
                                       hyprel``{%n::nat. real (X n)})"

defs (overloaded)

  (** the overloaded constant "Nats" **)

  (* set of naturals embedded in the hyperreals*)
  SNat_def:  "Nats == {n. \<exists>N. n = hypreal_of_nat N}"

  (* set of naturals embedded in the hypernaturals*)
  SHNat_def: "Nats == {n. \<exists>N. n = hypnat_of_nat N}"

  (** hypernatural arithmetic **)

  hypnat_zero_def:  "0 == Abs_hypnat(hypnatrel``{%n::nat. 0})"
  hypnat_one_def:   "1 == Abs_hypnat(hypnatrel``{%n::nat. 1})"

  (* omega is in fact an infinite hypernatural number = [<1,2,3,...>] *)
  hypnat_omega_def:  "whn == Abs_hypnat(hypnatrel``{%n::nat. n})"

  hypnat_add_def:
  "P + Q == Abs_hypnat(\<Union>X \<in> Rep_hypnat(P). \<Union>Y \<in> Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n + Y n})"

  hypnat_mult_def:
  "P * Q == Abs_hypnat(\<Union>X \<in> Rep_hypnat(P). \<Union>Y \<in> Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n * Y n})"

  hypnat_minus_def:
  "P - Q == Abs_hypnat(\<Union>X \<in> Rep_hypnat(P). \<Union>Y \<in> Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n - Y n})"

  hypnat_le_def:
  "P \<le> (Q::hypnat) == \<exists>X Y. X \<in> Rep_hypnat(P) &
                               Y \<in> Rep_hypnat(Q) &
                               {n::nat. X n \<le> Y n} \<in> FreeUltrafilterNat"

  hypnat_less_def: "(x < (y::hypnat)) == (x \<le> y & x \<noteq> y)"



subsection{*Properties of @{term hypnatrel}*}

text{*Proving that @{term hypnatrel} is an equivalence relation*}

lemma hypnatrel_iff:
     "((X,Y) \<in> hypnatrel) = ({n. X n = Y n}: FreeUltrafilterNat)"
apply (unfold hypnatrel_def, fast)
done

lemma hypnatrel_refl: "(x,x) \<in> hypnatrel"
by (unfold hypnatrel_def, auto)

lemma hypnatrel_sym: "(x,y) \<in> hypnatrel ==> (y,x) \<in> hypnatrel"
by (auto simp add: hypnatrel_def eq_commute)

lemma hypnatrel_trans [rule_format (no_asm)]:
     "(x,y) \<in> hypnatrel --> (y,z) \<in> hypnatrel --> (x,z) \<in> hypnatrel"
apply (unfold hypnatrel_def, auto, ultra)
done

lemma equiv_hypnatrel:
     "equiv UNIV hypnatrel"
apply (simp add: equiv_def refl_def sym_def trans_def hypnatrel_refl)
apply (blast intro: hypnatrel_sym hypnatrel_trans)
done

(* (hypnatrel `` {x} = hypnatrel `` {y}) = ((x,y) \<in> hypnatrel) *)
lemmas equiv_hypnatrel_iff =
    eq_equiv_class_iff [OF equiv_hypnatrel UNIV_I UNIV_I, simp]

lemma hypnatrel_in_hypnat [simp]: "hypnatrel``{x}:hypnat"
by (unfold hypnat_def hypnatrel_def quotient_def, blast)

lemma inj_on_Abs_hypnat: "inj_on Abs_hypnat hypnat"
apply (rule inj_on_inverseI)
apply (erule Abs_hypnat_inverse)
done

declare inj_on_Abs_hypnat [THEN inj_on_iff, simp]
        Abs_hypnat_inverse [simp]

declare equiv_hypnatrel [THEN eq_equiv_class_iff, simp]

declare hypnatrel_iff [iff]


lemma inj_Rep_hypnat: "inj(Rep_hypnat)"
apply (rule inj_on_inverseI)
apply (rule Rep_hypnat_inverse)
done

lemma lemma_hypnatrel_refl: "x \<in> hypnatrel `` {x}"
by (simp add: hypnatrel_def)

declare lemma_hypnatrel_refl [simp]

lemma hypnat_empty_not_mem: "{} \<notin> hypnat"
apply (unfold hypnat_def)
apply (auto elim!: quotientE equalityCE)
done

declare hypnat_empty_not_mem [simp]

lemma Rep_hypnat_nonempty: "Rep_hypnat x \<noteq> {}"
by (cut_tac x = x in Rep_hypnat, auto)

declare Rep_hypnat_nonempty [simp]

subsection{*@{term hypnat_of_nat}:
            the Injection from @{typ nat} to @{typ hypnat}*}

lemma inj_hypnat_of_nat: "inj(hypnat_of_nat)"
apply (rule inj_onI)
apply (unfold hypnat_of_nat_def)
apply (drule inj_on_Abs_hypnat [THEN inj_onD])
apply (rule hypnatrel_in_hypnat)+
apply (drule eq_equiv_class)
apply (rule equiv_hypnatrel)
apply (simp_all split: split_if_asm)
done

lemma eq_Abs_hypnat:
    "(!!x. z = Abs_hypnat(hypnatrel``{x}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_hypnat [unfolded hypnat_def, THEN quotientE])
apply (drule_tac f = Abs_hypnat in arg_cong)
apply (force simp add: Rep_hypnat_inverse)
done

subsection{*Hypernat Addition*}

lemma hypnat_add_congruent2:
     "congruent2 hypnatrel (%X Y. hypnatrel``{%n. X n + Y n})"
apply (unfold congruent2_def, auto, ultra)
done

lemma hypnat_add:
  "Abs_hypnat(hypnatrel``{%n. X n}) + Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypnat(hypnatrel``{%n. X n + Y n})"
by (simp add: hypnat_add_def UN_equiv_class2 [OF equiv_hypnatrel hypnat_add_congruent2])

lemma hypnat_add_commute: "(z::hypnat) + w = w + z"
apply (rule eq_Abs_hypnat [of z])
apply (rule eq_Abs_hypnat [of w])
apply (simp add: add_ac hypnat_add)
done

lemma hypnat_add_assoc: "((z1::hypnat) + z2) + z3 = z1 + (z2 + z3)"
apply (rule eq_Abs_hypnat [of z1])
apply (rule eq_Abs_hypnat [of z2])
apply (rule eq_Abs_hypnat [of z3])
apply (simp add: hypnat_add nat_add_assoc)
done

lemma hypnat_add_zero_left: "(0::hypnat) + z = z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: hypnat_zero_def hypnat_add)
done

instance hypnat :: plus_ac0
  by (intro_classes,
      (assumption |
       rule hypnat_add_commute hypnat_add_assoc hypnat_add_zero_left)+)


subsection{*Subtraction inverse on @{typ hypreal}*}


lemma hypnat_minus_congruent2:
    "congruent2 hypnatrel (%X Y. hypnatrel``{%n. X n - Y n})"
apply (unfold congruent2_def, auto, ultra)
done

lemma hypnat_minus:
  "Abs_hypnat(hypnatrel``{%n. X n}) - Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypnat(hypnatrel``{%n. X n - Y n})"
by (simp add: hypnat_minus_def UN_equiv_class2 [OF equiv_hypnatrel hypnat_minus_congruent2])

lemma hypnat_minus_zero: "z - z = (0::hypnat)"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: hypnat_zero_def hypnat_minus)
done

lemma hypnat_diff_0_eq_0: "(0::hypnat) - n = 0"
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_minus hypnat_zero_def)
done

declare hypnat_minus_zero [simp] hypnat_diff_0_eq_0 [simp]

lemma hypnat_add_is_0: "(m+n = (0::hypnat)) = (m=0 & n=0)"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (auto intro: FreeUltrafilterNat_subset dest: FreeUltrafilterNat_Int simp add: hypnat_zero_def hypnat_add)
done

declare hypnat_add_is_0 [iff]

lemma hypnat_diff_diff_left: "(i::hypnat) - j - k = i - (j+k)"
apply (rule eq_Abs_hypnat [of i])
apply (rule eq_Abs_hypnat [of j])
apply (rule eq_Abs_hypnat [of k])
apply (simp add: hypnat_minus hypnat_add diff_diff_left)
done

lemma hypnat_diff_commute: "(i::hypnat) - j - k = i-k-j"
by (simp add: hypnat_diff_diff_left hypnat_add_commute)

lemma hypnat_diff_add_inverse: "((n::hypnat) + m) - n = m"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_minus hypnat_add)
done
declare hypnat_diff_add_inverse [simp]

lemma hypnat_diff_add_inverse2:  "((m::hypnat) + n) - n = m"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_minus hypnat_add)
done
declare hypnat_diff_add_inverse2 [simp]

lemma hypnat_diff_cancel: "((k::hypnat) + m) - (k+n) = m - n"
apply (rule eq_Abs_hypnat [of k])
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_minus hypnat_add)
done
declare hypnat_diff_cancel [simp]

lemma hypnat_diff_cancel2: "((m::hypnat) + k) - (n+k) = m - n"
by (simp add: hypnat_add_commute [of _ k])
declare hypnat_diff_cancel2 [simp]

lemma hypnat_diff_add_0: "(n::hypnat) - (n+m) = (0::hypnat)"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_zero_def hypnat_minus hypnat_add)
done
declare hypnat_diff_add_0 [simp]


subsection{*Hyperreal Multiplication*}

lemma hypnat_mult_congruent2:
    "congruent2 hypnatrel (%X Y. hypnatrel``{%n. X n * Y n})"
by (unfold congruent2_def, auto, ultra)

lemma hypnat_mult:
  "Abs_hypnat(hypnatrel``{%n. X n}) * Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypnat(hypnatrel``{%n. X n * Y n})"
by (simp add: hypnat_mult_def UN_equiv_class2 [OF equiv_hypnatrel hypnat_mult_congruent2])

lemma hypnat_mult_commute: "(z::hypnat) * w = w * z"
apply (rule eq_Abs_hypnat [of z])
apply (rule eq_Abs_hypnat [of w])
apply (simp add: hypnat_mult mult_ac)
done

lemma hypnat_mult_assoc: "((z1::hypnat) * z2) * z3 = z1 * (z2 * z3)"
apply (rule eq_Abs_hypnat [of z1])
apply (rule eq_Abs_hypnat [of z2])
apply (rule eq_Abs_hypnat [of z3])
apply (simp add: hypnat_mult mult_assoc)
done

lemma hypnat_mult_1: "(1::hypnat) * z = z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: hypnat_mult hypnat_one_def)
done

lemma hypnat_diff_mult_distrib: "((m::hypnat) - n) * k = (m * k) - (n * k)"
apply (rule eq_Abs_hypnat [of k])
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_mult hypnat_minus diff_mult_distrib)
done

lemma hypnat_diff_mult_distrib2: "(k::hypnat) * (m - n) = (k * m) - (k * n)"
by (simp add: hypnat_diff_mult_distrib hypnat_mult_commute [of k])

lemma hypnat_add_mult_distrib: "((z1::hypnat) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule eq_Abs_hypnat [of z1])
apply (rule eq_Abs_hypnat [of z2])
apply (rule eq_Abs_hypnat [of w])
apply (simp add: hypnat_mult hypnat_add add_mult_distrib)
done

lemma hypnat_add_mult_distrib2: "(w::hypnat) * (z1 + z2) = (w * z1) + (w * z2)"
by (simp add: hypnat_mult_commute [of w] hypnat_add_mult_distrib)

text{*one and zero are distinct*}
lemma hypnat_zero_not_eq_one: "(0::hypnat) \<noteq> (1::hypnat)"
by (auto simp add: hypnat_zero_def hypnat_one_def)
declare hypnat_zero_not_eq_one [THEN not_sym, simp]


text{*The Hypernaturals Form A Semiring*}
instance hypnat :: semiring
proof
  fix i j k :: hypnat
  show "(i + j) + k = i + (j + k)" by (rule hypnat_add_assoc)
  show "i + j = j + i" by (rule hypnat_add_commute)
  show "0 + i = i" by simp
  show "(i * j) * k = i * (j * k)" by (rule hypnat_mult_assoc)
  show "i * j = j * i" by (rule hypnat_mult_commute)
  show "1 * i = i" by (rule hypnat_mult_1)
  show "(i + j) * k = i * k + j * k" by (simp add: hypnat_add_mult_distrib)
  show "0 \<noteq> (1::hypnat)" by (rule hypnat_zero_not_eq_one)
  assume "k+i = k+j"
  hence "(k+i) - k = (k+j) - k" by simp
  thus "i=j" by simp
qed


subsection{*Properties of The @{text "\<le>"} Relation*}

lemma hypnat_le:
      "(Abs_hypnat(hypnatrel``{%n. X n}) \<le> Abs_hypnat(hypnatrel``{%n. Y n})) =
       ({n. X n \<le> Y n} \<in> FreeUltrafilterNat)"
apply (unfold hypnat_le_def)
apply (auto intro!: lemma_hypnatrel_refl, ultra)
done

lemma hypnat_le_refl: "w \<le> (w::hypnat)"
apply (rule eq_Abs_hypnat [of w])
apply (simp add: hypnat_le)
done

lemma hypnat_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::hypnat)"
apply (rule eq_Abs_hypnat [of i])
apply (rule eq_Abs_hypnat [of j])
apply (rule eq_Abs_hypnat [of k])
apply (simp add: hypnat_le, ultra)
done

lemma hypnat_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::hypnat)"
apply (rule eq_Abs_hypnat [of z])
apply (rule eq_Abs_hypnat [of w])
apply (simp add: hypnat_le, ultra)
done

(* Axiom 'order_less_le' of class 'order': *)
lemma hypnat_less_le: "((w::hypnat) < z) = (w \<le> z & w \<noteq> z)"
by (simp add: hypnat_less_def)

instance hypnat :: order
proof qed
 (assumption |
  rule hypnat_le_refl hypnat_le_trans hypnat_le_anti_sym hypnat_less_le)+

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma hypnat_le_linear: "(z::hypnat) \<le> w | w \<le> z"
apply (rule eq_Abs_hypnat [of z])
apply (rule eq_Abs_hypnat [of w])
apply (auto simp add: hypnat_le, ultra)
done

instance hypnat :: linorder
  by (intro_classes, rule hypnat_le_linear)

lemma hypnat_add_left_mono: "x \<le> y ==> z + x \<le> z + (y::hypnat)"
apply (rule eq_Abs_hypnat [of x])
apply (rule eq_Abs_hypnat [of y])
apply (rule eq_Abs_hypnat [of z])
apply (auto simp add: hypnat_le hypnat_add)
done

lemma hypnat_mult_less_mono2: "[| (0::hypnat)<z; x<y |] ==> z*x<z*y"
apply (rule eq_Abs_hypnat [of x])
apply (rule eq_Abs_hypnat [of y])
apply (rule eq_Abs_hypnat [of z])
apply (simp add: hypnat_zero_def  hypnat_mult linorder_not_le [symmetric])
apply (auto simp add: hypnat_le, ultra)
done


subsection{*The Hypernaturals Form an Ordered Semiring*}

instance hypnat :: ordered_semiring
proof
  fix x y z :: hypnat
  show "0 < (1::hypnat)"
    by (simp add: hypnat_zero_def hypnat_one_def linorder_not_le [symmetric],
        simp add: hypnat_le)
  show "x \<le> y ==> z + x \<le> z + y"
    by (rule hypnat_add_left_mono)
  show "x < y ==> 0 < z ==> z * x < z * y"
    by (simp add: hypnat_mult_less_mono2)
qed

lemma hypnat_mult_is_0 [simp]: "(m*n = (0::hypnat)) = (m=0 | n=0)"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (auto simp add: hypnat_zero_def hypnat_mult, ultra+)
done


subsection{*Theorems for Ordering*}

lemma hypnat_less:
      "(Abs_hypnat(hypnatrel``{%n. X n}) < Abs_hypnat(hypnatrel``{%n. Y n})) =
       ({n. X n < Y n} \<in> FreeUltrafilterNat)"
apply (auto simp add: hypnat_le  linorder_not_le [symmetric])
apply (ultra+)
done

lemma hypnat_not_less0 [iff]: "~ n < (0::hypnat)"
apply (rule eq_Abs_hypnat [of n])
apply (auto simp add: hypnat_zero_def hypnat_less)
done

lemma hypnat_less_one [iff]:
      "(n < (1::hypnat)) = (n=0)"
apply (rule eq_Abs_hypnat [of n])
apply (auto simp add: hypnat_zero_def hypnat_one_def hypnat_less)
done

lemma hypnat_add_diff_inverse: "~ m<n ==> n+(m-n) = (m::hypnat)"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypnat_minus hypnat_add hypnat_less split: nat_diff_split, ultra)
done

lemma hypnat_le_add_diff_inverse [simp]: "n \<le> m ==> n+(m-n) = (m::hypnat)"
by (simp add: hypnat_add_diff_inverse linorder_not_less [symmetric])

lemma hypnat_le_add_diff_inverse2 [simp]: "n\<le>m ==> (m-n)+n = (m::hypnat)"
by (simp add: hypnat_le_add_diff_inverse hypnat_add_commute)

declare hypnat_le_add_diff_inverse2 [OF order_less_imp_le]

lemma hypnat_le0 [iff]: "(0::hypnat) \<le> n"
by (simp add: linorder_not_less [symmetric])

lemma hypnat_add_self_le [simp]: "(x::hypnat) \<le> n + x"
by (insert add_right_mono [of 0 n x], simp)

lemma hypnat_add_one_self_less [simp]: "(x::hypnat) < x + (1::hypnat)"
by (insert add_strict_left_mono [OF zero_less_one], auto)

lemma hypnat_neq0_conv [iff]: "(n \<noteq> 0) = (0 < (n::hypnat))"
by (simp add: order_less_le)

lemma hypnat_gt_zero_iff: "((0::hypnat) < n) = ((1::hypnat) \<le> n)"
by (auto simp add: linorder_not_less [symmetric])

lemma hypnat_gt_zero_iff2: "(0 < n) = (\<exists>m. n = m + (1::hypnat))"
apply safe
 apply (rule_tac x = "n - (1::hypnat) " in exI)
 apply (simp add: hypnat_gt_zero_iff) 
apply (insert add_le_less_mono [OF _ zero_less_one, of 0], auto) 
done

subsection{*The Embedding @{term hypnat_of_nat} Preserves Ring and 
      Order Properties*}

lemma hypnat_of_nat_add:
      "hypnat_of_nat ((z::nat) + w) = hypnat_of_nat z + hypnat_of_nat w"
by (simp add: hypnat_of_nat_def hypnat_add)

lemma hypnat_of_nat_minus:
      "hypnat_of_nat ((z::nat) - w) = hypnat_of_nat z - hypnat_of_nat w"
by (simp add: hypnat_of_nat_def hypnat_minus)

lemma hypnat_of_nat_mult:
      "hypnat_of_nat (z * w) = hypnat_of_nat z * hypnat_of_nat w"
by (simp add: hypnat_of_nat_def hypnat_mult)

lemma hypnat_of_nat_less_iff [simp]:
      "(hypnat_of_nat z < hypnat_of_nat w) = (z < w)"
by (simp add: hypnat_less hypnat_of_nat_def)

lemma hypnat_of_nat_le_iff [simp]:
      "(hypnat_of_nat z \<le> hypnat_of_nat w) = (z \<le> w)"
by (simp add: linorder_not_less [symmetric])

lemma hypnat_of_nat_one: "hypnat_of_nat (Suc 0) = (1::hypnat)"
by (simp add: hypnat_of_nat_def hypnat_one_def)

lemma hypnat_of_nat_zero: "hypnat_of_nat 0 = 0"
by (simp add: hypnat_of_nat_def hypnat_zero_def)

lemma hypnat_of_nat_zero_iff: "(hypnat_of_nat n = 0) = (n = 0)"
by (auto intro: FreeUltrafilterNat_P 
         simp add: hypnat_of_nat_def hypnat_zero_def)

lemma hypnat_of_nat_Suc:
     "hypnat_of_nat (Suc n) = hypnat_of_nat n + (1::hypnat)"
by (auto simp add: hypnat_add hypnat_of_nat_def hypnat_one_def)


subsection{*Existence of an Infinite Hypernatural Number*}

lemma hypnat_omega: "hypnatrel``{%n::nat. n} \<in> hypnat"
by auto

lemma Rep_hypnat_omega: "Rep_hypnat(whn) \<in> hypnat"
by (simp add: hypnat_omega_def)

text{*Existence of infinite number not corresponding to any natural number
follows because member @{term FreeUltrafilterNat} is not finite.
See @{text HyperDef.thy} for similar argument.*}

lemma not_ex_hypnat_of_nat_eq_omega:
      "~ (\<exists>x. hypnat_of_nat x = whn)"
apply (simp add: hypnat_omega_def hypnat_of_nat_def)
apply (auto dest: FreeUltrafilterNat_not_finite)
done

lemma hypnat_of_nat_not_eq_omega: "hypnat_of_nat x \<noteq> whn"
by (cut_tac not_ex_hypnat_of_nat_eq_omega, auto)
declare hypnat_of_nat_not_eq_omega [THEN not_sym, simp]


subsection{*Properties of the set @{term Nats} of Embedded Natural Numbers*}

(* Infinite hypernatural not in embedded Nats *)
lemma SHNAT_omega_not_mem [simp]: "whn \<notin> Nats"
by (simp add: SHNat_def)

(*-----------------------------------------------------------------------
     Closure laws for members of (embedded) set standard naturals Nats
 -----------------------------------------------------------------------*)
lemma SHNat_add:
     "!!x::hypnat. [| x \<in> Nats; y \<in> Nats |] ==> x + y \<in> Nats"
apply (simp add: SHNat_def, safe)
apply (rule_tac x = "N + Na" in exI)
apply (simp add: hypnat_of_nat_add)
done

lemma SHNat_minus:
     "!!x::hypnat. [| x \<in> Nats; y \<in> Nats |] ==> x - y \<in> Nats"
apply (simp add: SHNat_def, safe)
apply (rule_tac x = "N - Na" in exI)
apply (simp add: hypnat_of_nat_minus)
done

lemma SHNat_mult:
     "!!x::hypnat. [| x \<in> Nats; y \<in> Nats |] ==> x * y \<in> Nats"
apply (simp add: SHNat_def, safe)
apply (rule_tac x = "N * Na" in exI)
apply (simp (no_asm) add: hypnat_of_nat_mult)
done

lemma SHNat_add_cancel: "!!x::hypnat. [| x + y \<in> Nats; y \<in> Nats |] ==> x \<in> Nats"
by (drule_tac x = "x+y" in SHNat_minus, auto)

lemma SHNat_hypnat_of_nat [simp]: "hypnat_of_nat x \<in> Nats"
by (simp add: SHNat_def, blast)

lemma SHNat_hypnat_of_nat_one [simp]: "hypnat_of_nat (Suc 0) \<in> Nats"
by simp

lemma SHNat_hypnat_of_nat_zero [simp]: "hypnat_of_nat 0 \<in> Nats"
by simp

lemma SHNat_one [simp]: "(1::hypnat) \<in> Nats"
by (simp add: hypnat_of_nat_one [symmetric])

lemma SHNat_zero [simp]: "(0::hypnat) \<in> Nats"
by (simp add: hypnat_of_nat_zero [symmetric])

lemma SHNat_iff: "(x \<in> Nats) = (\<exists>y. x = hypnat_of_nat  y)"
by (simp add: SHNat_def)

lemma SHNat_hypnat_of_nat_iff:
      "Nats = hypnat_of_nat ` (UNIV::nat set)"
by (auto simp add: SHNat_def)

lemma leSuc_Un_eq: "{n. n \<le> Suc m} = {n. n \<le> m} Un {n. n = Suc m}"
by (auto simp add: le_Suc_eq)

lemma finite_nat_le_segment: "finite {n::nat. n \<le> m}"
apply (induct_tac "m")
apply (auto simp add: leSuc_Un_eq)
done

lemma lemma_unbounded_set [simp]: "{n::nat. m < n} \<in> FreeUltrafilterNat"
by (insert finite_nat_le_segment
                [THEN FreeUltrafilterNat_finite, 
                 THEN FreeUltrafilterNat_Compl_mem, of m], ultra)

(*????hyperdef*)
lemma cofinite_mem_FreeUltrafilterNat: "finite (-X) ==> X \<in> FreeUltrafilterNat"
apply (drule FreeUltrafilterNat_finite)  
apply (simp add: FreeUltrafilterNat_Compl_iff2 [symmetric])
done

lemma Compl_Collect_le: "- {n::nat. N \<le> n} = {n. n < N}"
by (simp add: Collect_neg_eq [symmetric] linorder_not_le) 

lemma hypnat_omega_gt_SHNat:
     "n \<in> Nats ==> n < whn"
apply (auto simp add: SHNat_def hypnat_of_nat_def hypnat_less_def 
                      hypnat_le_def hypnat_omega_def)
 prefer 2 apply (force dest: FreeUltrafilterNat_not_finite)
apply (auto intro!: exI)
apply (rule cofinite_mem_FreeUltrafilterNat)
apply (simp add: Compl_Collect_le finite_nat_segment) 
done

lemma hypnat_of_nat_less_whn: "hypnat_of_nat n < whn"
by (insert hypnat_omega_gt_SHNat [of "hypnat_of_nat n"], auto)
declare hypnat_of_nat_less_whn [simp]

lemma hypnat_of_nat_le_whn: "hypnat_of_nat n \<le> whn"
by (rule hypnat_of_nat_less_whn [THEN order_less_imp_le])
declare hypnat_of_nat_le_whn [simp]

lemma hypnat_zero_less_hypnat_omega [simp]: "0 < whn"
by (simp add: hypnat_omega_gt_SHNat)

lemma hypnat_one_less_hypnat_omega [simp]: "(1::hypnat) < whn"
by (simp add: hypnat_omega_gt_SHNat)


subsection{*Infinite Hypernatural Numbers -- @{term HNatInfinite}*}

lemma HNatInfinite_whn: "whn \<in> HNatInfinite"
by (simp add: HNatInfinite_def SHNat_def)
declare HNatInfinite_whn [simp]

lemma SHNat_not_HNatInfinite: "x \<in> Nats ==> x \<notin> HNatInfinite"
by (simp add: HNatInfinite_def)

lemma not_HNatInfinite_SHNat: "x \<notin> HNatInfinite ==> x \<in> Nats"
by (simp add: HNatInfinite_def)

lemma not_SHNat_HNatInfinite: "x \<notin> Nats ==> x \<in> HNatInfinite"
by (simp add: HNatInfinite_def)

lemma HNatInfinite_not_SHNat: "x \<in> HNatInfinite ==> x \<notin> Nats"
by (simp add: HNatInfinite_def)

lemma SHNat_not_HNatInfinite_iff: "(x \<in> Nats) = (x \<notin> HNatInfinite)"
by (blast intro!: SHNat_not_HNatInfinite not_HNatInfinite_SHNat)

lemma not_SHNat_HNatInfinite_iff: "(x \<notin> Nats) = (x \<in> HNatInfinite)"
by (blast intro!: not_SHNat_HNatInfinite HNatInfinite_not_SHNat)

lemma SHNat_HNatInfinite_disj: "x \<in> Nats | x \<in> HNatInfinite"
by (simp add: SHNat_not_HNatInfinite_iff)


subsection{*Alternative Characterization of the Set of Infinite Hypernaturals:
@{term "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"}*}

(*??delete? similar reasoning in hypnat_omega_gt_SHNat above*)
lemma HNatInfinite_FreeUltrafilterNat_lemma: "\<forall>N::nat. {n. f n \<noteq> N} \<in> FreeUltrafilterNat
      ==> {n. N < f n} \<in> FreeUltrafilterNat"
apply (induct_tac "N")
apply (drule_tac x = 0 in spec)
apply (rule ccontr, drule FreeUltrafilterNat_Compl_mem, drule FreeUltrafilterNat_Int, assumption, simp)
apply (drule_tac x = "Suc n" in spec, ultra)
done

lemma HNatInfinite_iff: "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"
apply (unfold HNatInfinite_def SHNat_def hypnat_of_nat_def, safe)
apply (drule_tac [2] x = "Abs_hypnat (hypnatrel `` {%n. N}) " in bspec)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: hypnat_less)
apply (auto  elim: HNatInfinite_FreeUltrafilterNat_lemma 
           simp add: FreeUltrafilterNat_Compl_iff1 Collect_neg_eq [symmetric])
done

subsection{*Alternative Characterization of @{term HNatInfinite} using 
Free Ultrafilter*}

lemma HNatInfinite_FreeUltrafilterNat:
     "x \<in> HNatInfinite 
      ==> \<exists>X \<in> Rep_hypnat x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat"
apply (rule eq_Abs_hypnat [of x])
apply (auto simp add: HNatInfinite_iff SHNat_iff hypnat_of_nat_def)
apply (rule bexI [OF _ lemma_hypnatrel_refl], clarify) 
apply (drule_tac x = "hypnat_of_nat u" in bspec, simp) 
apply (auto simp add: hypnat_of_nat_def hypnat_less)
done

lemma FreeUltrafilterNat_HNatInfinite:
     "\<exists>X \<in> Rep_hypnat x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat
      ==> x \<in> HNatInfinite"
apply (rule eq_Abs_hypnat [of x])
apply (auto simp add: hypnat_less HNatInfinite_iff SHNat_iff hypnat_of_nat_def)
apply (drule spec, ultra, auto) 
done

lemma HNatInfinite_FreeUltrafilterNat_iff:
     "(x \<in> HNatInfinite) = 
      (\<exists>X \<in> Rep_hypnat x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat)"
apply (blast intro: HNatInfinite_FreeUltrafilterNat FreeUltrafilterNat_HNatInfinite)
done

lemma HNatInfinite_gt_one: "x \<in> HNatInfinite ==> (1::hypnat) < x"
by (auto simp add: HNatInfinite_iff)
declare HNatInfinite_gt_one [simp]

lemma zero_not_mem_HNatInfinite: "0 \<notin> HNatInfinite"
apply (auto simp add: HNatInfinite_iff)
apply (drule_tac a = " (1::hypnat) " in equals0D)
apply simp
done
declare zero_not_mem_HNatInfinite [simp]

lemma HNatInfinite_not_eq_zero: "x \<in> HNatInfinite ==> 0 < x"
apply (drule HNatInfinite_gt_one) 
apply (auto simp add: order_less_trans [OF zero_less_one])
done

lemma HNatInfinite_ge_one [simp]: "x \<in> HNatInfinite ==> (1::hypnat) \<le> x"
by (blast intro: order_less_imp_le HNatInfinite_gt_one)


subsection{*Closure Rules*}

lemma HNatInfinite_add: "[| x \<in> HNatInfinite; y \<in> HNatInfinite |]
            ==> x + y \<in> HNatInfinite"
apply (auto simp add: HNatInfinite_iff)
apply (drule bspec, assumption)
apply (drule bspec [OF _ SHNat_zero])
apply (drule add_strict_mono, assumption, simp)
done

lemma HNatInfinite_SHNat_add: "[| x \<in> HNatInfinite; y \<in> Nats |] ==> x + y \<in> HNatInfinite"
apply (rule ccontr, drule not_HNatInfinite_SHNat)
apply (drule_tac x = "x + y" in SHNat_minus)
apply (auto simp add: SHNat_not_HNatInfinite_iff)
done

lemma HNatInfinite_SHNat_diff: "[| x \<in> HNatInfinite; y \<in> Nats |] ==> x - y \<in> HNatInfinite"
apply (rule ccontr, drule not_HNatInfinite_SHNat)
apply (drule_tac x = "x - y" in SHNat_add)
apply (subgoal_tac [2] "y \<le> x")
apply (auto dest!: hypnat_le_add_diff_inverse2 simp add: not_SHNat_HNatInfinite_iff [symmetric])
apply (auto intro!: order_less_imp_le simp add: not_SHNat_HNatInfinite_iff HNatInfinite_iff)
done

lemma HNatInfinite_add_one: "x \<in> HNatInfinite ==> x + (1::hypnat) \<in> HNatInfinite"
by (auto intro: HNatInfinite_SHNat_add)

lemma HNatInfinite_minus_one: "x \<in> HNatInfinite ==> x - (1::hypnat) \<in> HNatInfinite"
apply (rule ccontr, drule not_HNatInfinite_SHNat)
apply (drule_tac x = "x - (1::hypnat) " and y = " (1::hypnat) " in SHNat_add)
apply (auto simp add: not_SHNat_HNatInfinite_iff [symmetric])
done

lemma HNatInfinite_is_Suc: "x \<in> HNatInfinite ==> \<exists>y. x = y + (1::hypnat)"
apply (rule_tac x = "x - (1::hypnat) " in exI)
apply auto
done


subsection{*@{term HNat}: the Hypernaturals Embedded in the Hyperreals*}

text{*Obtained using the nonstandard extension of the naturals*}

lemma HNat_hypreal_of_nat: "hypreal_of_nat N \<in> HNat"
apply (simp add: HNat_def starset_def hypreal_of_nat_def hypreal_of_real_def, auto, ultra)
apply (rule_tac x = N in exI, auto)
done
declare HNat_hypreal_of_nat [simp]

lemma HNat_add: "[| x \<in> HNat; y \<in> HNat |] ==> x + y \<in> HNat"
apply (simp add: HNat_def starset_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto dest!: bspec intro: lemma_hyprel_refl simp add: hypreal_add, ultra)
apply (rule_tac x = "no+noa" in exI, auto)
done

lemma HNat_mult:
     "[| x \<in> HNat; y \<in> HNat |] ==> x * y \<in> HNat"
apply (simp add: HNat_def starset_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto dest!: bspec intro: lemma_hyprel_refl simp add: hypreal_mult, ultra)
apply (rule_tac x = "no*noa" in exI, auto)
done


subsection{*Embedding of the Hypernaturals into the Hyperreals*}

(*WARNING: FRAGILE!*)
lemma lemma_hyprel_FUFN: "(Ya \<in> hyprel ``{%n. f(n)}) =
      ({n. f n = Ya n} \<in> FreeUltrafilterNat)"
apply auto
done

lemma hypreal_of_hypnat:
      "hypreal_of_hypnat (Abs_hypnat(hypnatrel``{%n. X n})) =
       Abs_hypreal(hyprel `` {%n. real (X n)})"
apply (simp add: hypreal_of_hypnat_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto elim: FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset] 
       simp add: lemma_hyprel_FUFN)
done

lemma inj_hypreal_of_hypnat: "inj(hypreal_of_hypnat)"
apply (rule inj_onI)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (rule_tac z = y in eq_Abs_hypnat)
apply (auto simp add: hypreal_of_hypnat)
done

declare inj_hypreal_of_hypnat [THEN inj_eq, simp]
declare inj_hypnat_of_nat [THEN inj_eq, simp]

lemma hypreal_of_hypnat_zero: "hypreal_of_hypnat 0 = 0"
by (simp add: hypnat_zero_def hypreal_zero_def hypreal_of_hypnat)

lemma hypreal_of_hypnat_one: "hypreal_of_hypnat (1::hypnat) = 1"
by (simp add: hypnat_one_def hypreal_one_def hypreal_of_hypnat)

lemma hypreal_of_hypnat_add [simp]:
     "hypreal_of_hypnat (m + n) = hypreal_of_hypnat m + hypreal_of_hypnat n"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypreal_of_hypnat hypreal_add hypnat_add real_of_nat_add)
done

lemma hypreal_of_hypnat_mult [simp]:
     "hypreal_of_hypnat (m * n) = hypreal_of_hypnat m * hypreal_of_hypnat n"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypreal_of_hypnat hypreal_mult hypnat_mult real_of_nat_mult)
done

lemma hypreal_of_hypnat_less_iff [simp]:
     "(hypreal_of_hypnat n < hypreal_of_hypnat m) = (n < m)"
apply (rule eq_Abs_hypnat [of m])
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypreal_of_hypnat hypreal_less hypnat_less)
done

lemma hypreal_of_hypnat_eq_zero_iff: "(hypreal_of_hypnat N = 0) = (N = 0)"
by (simp add: hypreal_of_hypnat_zero [symmetric])
declare hypreal_of_hypnat_eq_zero_iff [simp]

lemma hypreal_of_hypnat_ge_zero [simp]: "0 \<le> hypreal_of_hypnat n"
apply (rule eq_Abs_hypnat [of n])
apply (simp add: hypreal_of_hypnat hypreal_zero_num hypreal_le)
done

(*????DELETE??*)
lemma hypnat_eq_zero: "\<forall>n. N \<le> n ==> N = (0::hypnat)"
apply (drule_tac x = 0 in spec)
apply (rule_tac z = N in eq_Abs_hypnat)
apply (auto simp add: hypnat_le hypnat_zero_def)
done

(*????DELETE??*)
lemma hypnat_not_all_eq_zero: "~ (\<forall>n. n = (0::hypnat))"
by auto

(*????DELETE??*)
lemma hypnat_le_one_eq_one: "n \<noteq> 0 ==> (n \<le> (1::hypnat)) = (n = (1::hypnat))"
by (auto simp add: order_le_less)

(*WHERE DO THESE BELONG???*)
lemma HNatInfinite_inverse_Infinitesimal: "n \<in> HNatInfinite ==> inverse (hypreal_of_hypnat n) \<in> Infinitesimal"
apply (rule eq_Abs_hypnat [of n])
apply (auto simp add: hypreal_of_hypnat hypreal_inverse HNatInfinite_FreeUltrafilterNat_iff Infinitesimal_FreeUltrafilterNat_iff2)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl, auto)
apply (drule_tac x = "m + 1" in spec, ultra)
done
declare HNatInfinite_inverse_Infinitesimal [simp]

lemma HNatInfinite_inverse_not_zero: "n \<in> HNatInfinite ==> hypreal_of_hypnat n \<noteq> 0"
by (simp add: HNatInfinite_not_eq_zero)



ML
{*
val hypnat_of_nat_def = thm"hypnat_of_nat_def";
val HNat_def = thm"HNat_def";
val HNatInfinite_def = thm"HNatInfinite_def";
val hypreal_of_hypnat_def = thm"hypreal_of_hypnat_def";
val SNat_def = thm"SNat_def";
val SHNat_def = thm"SHNat_def";
val hypnat_zero_def = thm"hypnat_zero_def";
val hypnat_one_def = thm"hypnat_one_def";
val hypnat_omega_def = thm"hypnat_omega_def";

val hypnatrel_iff = thm "hypnatrel_iff";
val hypnatrel_refl = thm "hypnatrel_refl";
val hypnatrel_sym = thm "hypnatrel_sym";
val hypnatrel_trans = thm "hypnatrel_trans";
val equiv_hypnatrel = thm "equiv_hypnatrel";
val equiv_hypnatrel_iff = thms "equiv_hypnatrel_iff";
val hypnatrel_in_hypnat = thm "hypnatrel_in_hypnat";
val inj_on_Abs_hypnat = thm "inj_on_Abs_hypnat";
val inj_Rep_hypnat = thm "inj_Rep_hypnat";
val lemma_hypnatrel_refl = thm "lemma_hypnatrel_refl";
val hypnat_empty_not_mem = thm "hypnat_empty_not_mem";
val Rep_hypnat_nonempty = thm "Rep_hypnat_nonempty";
val inj_hypnat_of_nat = thm "inj_hypnat_of_nat";
val eq_Abs_hypnat = thm "eq_Abs_hypnat";
val hypnat_add_congruent2 = thm "hypnat_add_congruent2";
val hypnat_add = thm "hypnat_add";
val hypnat_add_commute = thm "hypnat_add_commute";
val hypnat_add_assoc = thm "hypnat_add_assoc";
val hypnat_add_zero_left = thm "hypnat_add_zero_left";
val hypnat_minus_congruent2 = thm "hypnat_minus_congruent2";
val hypnat_minus = thm "hypnat_minus";
val hypnat_minus_zero = thm "hypnat_minus_zero";
val hypnat_diff_0_eq_0 = thm "hypnat_diff_0_eq_0";
val hypnat_add_is_0 = thm "hypnat_add_is_0";
val hypnat_diff_diff_left = thm "hypnat_diff_diff_left";
val hypnat_diff_commute = thm "hypnat_diff_commute";
val hypnat_diff_add_inverse = thm "hypnat_diff_add_inverse";
val hypnat_diff_add_inverse2 = thm "hypnat_diff_add_inverse2";
val hypnat_diff_cancel = thm "hypnat_diff_cancel";
val hypnat_diff_cancel2 = thm "hypnat_diff_cancel2";
val hypnat_diff_add_0 = thm "hypnat_diff_add_0";
val hypnat_mult_congruent2 = thm "hypnat_mult_congruent2";
val hypnat_mult = thm "hypnat_mult";
val hypnat_mult_commute = thm "hypnat_mult_commute";
val hypnat_mult_assoc = thm "hypnat_mult_assoc";
val hypnat_mult_1 = thm "hypnat_mult_1";
val hypnat_diff_mult_distrib = thm "hypnat_diff_mult_distrib";
val hypnat_diff_mult_distrib2 = thm "hypnat_diff_mult_distrib2";
val hypnat_add_mult_distrib = thm "hypnat_add_mult_distrib";
val hypnat_add_mult_distrib2 = thm "hypnat_add_mult_distrib2";
val hypnat_zero_not_eq_one = thm "hypnat_zero_not_eq_one";
val hypnat_le = thm "hypnat_le";
val hypnat_le_refl = thm "hypnat_le_refl";
val hypnat_le_trans = thm "hypnat_le_trans";
val hypnat_le_anti_sym = thm "hypnat_le_anti_sym";
val hypnat_less_le = thm "hypnat_less_le";
val hypnat_le_linear = thm "hypnat_le_linear";
val hypnat_add_left_mono = thm "hypnat_add_left_mono";
val hypnat_mult_less_mono2 = thm "hypnat_mult_less_mono2";
val hypnat_mult_is_0 = thm "hypnat_mult_is_0";
val hypnat_less = thm "hypnat_less";
val hypnat_not_less0 = thm "hypnat_not_less0";
val hypnat_less_one = thm "hypnat_less_one";
val hypnat_add_diff_inverse = thm "hypnat_add_diff_inverse";
val hypnat_le_add_diff_inverse = thm "hypnat_le_add_diff_inverse";
val hypnat_le_add_diff_inverse2 = thm "hypnat_le_add_diff_inverse2";
val hypnat_le0 = thm "hypnat_le0";
val hypnat_add_self_le = thm "hypnat_add_self_le";
val hypnat_add_one_self_less = thm "hypnat_add_one_self_less";
val hypnat_neq0_conv = thm "hypnat_neq0_conv";
val hypnat_gt_zero_iff = thm "hypnat_gt_zero_iff";
val hypnat_gt_zero_iff2 = thm "hypnat_gt_zero_iff2";
val hypnat_of_nat_add = thm "hypnat_of_nat_add";
val hypnat_of_nat_minus = thm "hypnat_of_nat_minus";
val hypnat_of_nat_mult = thm "hypnat_of_nat_mult";
val hypnat_of_nat_less_iff = thm "hypnat_of_nat_less_iff";
val hypnat_of_nat_le_iff = thm "hypnat_of_nat_le_iff";
val hypnat_of_nat_one = thm "hypnat_of_nat_one";
val hypnat_of_nat_zero = thm "hypnat_of_nat_zero";
val hypnat_of_nat_zero_iff = thm "hypnat_of_nat_zero_iff";
val hypnat_of_nat_Suc = thm "hypnat_of_nat_Suc";
val hypnat_omega = thm "hypnat_omega";
val Rep_hypnat_omega = thm "Rep_hypnat_omega";
val not_ex_hypnat_of_nat_eq_omega = thm "not_ex_hypnat_of_nat_eq_omega";
val hypnat_of_nat_not_eq_omega = thm "hypnat_of_nat_not_eq_omega";
val SHNAT_omega_not_mem = thm "SHNAT_omega_not_mem";
val SHNat_add = thm "SHNat_add";
val SHNat_minus = thm "SHNat_minus";
val SHNat_mult = thm "SHNat_mult";
val SHNat_add_cancel = thm "SHNat_add_cancel";
val SHNat_hypnat_of_nat = thm "SHNat_hypnat_of_nat";
val SHNat_hypnat_of_nat_one = thm "SHNat_hypnat_of_nat_one";
val SHNat_hypnat_of_nat_zero = thm "SHNat_hypnat_of_nat_zero";
val SHNat_one = thm "SHNat_one";
val SHNat_zero = thm "SHNat_zero";
val SHNat_iff = thm "SHNat_iff";
val SHNat_hypnat_of_nat_iff = thm "SHNat_hypnat_of_nat_iff";
val leSuc_Un_eq = thm "leSuc_Un_eq";
val finite_nat_le_segment = thm "finite_nat_le_segment";
val lemma_unbounded_set = thm "lemma_unbounded_set";
val cofinite_mem_FreeUltrafilterNat = thm "cofinite_mem_FreeUltrafilterNat";
val Compl_Collect_le = thm "Compl_Collect_le";
val hypnat_omega_gt_SHNat = thm "hypnat_omega_gt_SHNat";
val hypnat_of_nat_less_whn = thm "hypnat_of_nat_less_whn";
val hypnat_of_nat_le_whn = thm "hypnat_of_nat_le_whn";
val hypnat_zero_less_hypnat_omega = thm "hypnat_zero_less_hypnat_omega";
val hypnat_one_less_hypnat_omega = thm "hypnat_one_less_hypnat_omega";
val HNatInfinite_whn = thm "HNatInfinite_whn";
val SHNat_not_HNatInfinite = thm "SHNat_not_HNatInfinite";
val not_HNatInfinite_SHNat = thm "not_HNatInfinite_SHNat";
val not_SHNat_HNatInfinite = thm "not_SHNat_HNatInfinite";
val HNatInfinite_not_SHNat = thm "HNatInfinite_not_SHNat";
val SHNat_not_HNatInfinite_iff = thm "SHNat_not_HNatInfinite_iff";
val not_SHNat_HNatInfinite_iff = thm "not_SHNat_HNatInfinite_iff";
val SHNat_HNatInfinite_disj = thm "SHNat_HNatInfinite_disj";
val HNatInfinite_FreeUltrafilterNat_lemma = thm "HNatInfinite_FreeUltrafilterNat_lemma";
val HNatInfinite_iff = thm "HNatInfinite_iff";
val HNatInfinite_FreeUltrafilterNat = thm "HNatInfinite_FreeUltrafilterNat";
val FreeUltrafilterNat_HNatInfinite = thm "FreeUltrafilterNat_HNatInfinite";
val HNatInfinite_FreeUltrafilterNat_iff = thm "HNatInfinite_FreeUltrafilterNat_iff";
val HNatInfinite_gt_one = thm "HNatInfinite_gt_one";
val zero_not_mem_HNatInfinite = thm "zero_not_mem_HNatInfinite";
val HNatInfinite_not_eq_zero = thm "HNatInfinite_not_eq_zero";
val HNatInfinite_ge_one = thm "HNatInfinite_ge_one";
val HNatInfinite_add = thm "HNatInfinite_add";
val HNatInfinite_SHNat_add = thm "HNatInfinite_SHNat_add";
val HNatInfinite_SHNat_diff = thm "HNatInfinite_SHNat_diff";
val HNatInfinite_add_one = thm "HNatInfinite_add_one";
val HNatInfinite_minus_one = thm "HNatInfinite_minus_one";
val HNatInfinite_is_Suc = thm "HNatInfinite_is_Suc";
val HNat_hypreal_of_nat = thm "HNat_hypreal_of_nat";
val HNat_add = thm "HNat_add";
val HNat_mult = thm "HNat_mult";
val lemma_hyprel_FUFN = thm "lemma_hyprel_FUFN";
val hypreal_of_hypnat = thm "hypreal_of_hypnat";
val inj_hypreal_of_hypnat = thm "inj_hypreal_of_hypnat";
val hypreal_of_hypnat_zero = thm "hypreal_of_hypnat_zero";
val hypreal_of_hypnat_one = thm "hypreal_of_hypnat_one";
val hypreal_of_hypnat_add = thm "hypreal_of_hypnat_add";
val hypreal_of_hypnat_mult = thm "hypreal_of_hypnat_mult";
val hypreal_of_hypnat_less_iff = thm "hypreal_of_hypnat_less_iff";
val hypreal_of_hypnat_eq_zero_iff = thm "hypreal_of_hypnat_eq_zero_iff";
val hypreal_of_hypnat_ge_zero = thm "hypreal_of_hypnat_ge_zero";
val hypnat_eq_zero = thm "hypnat_eq_zero";
val hypnat_not_all_eq_zero = thm "hypnat_not_all_eq_zero";
val hypnat_le_one_eq_one = thm "hypnat_le_one_eq_one";
val HNatInfinite_inverse_Infinitesimal = thm "HNatInfinite_inverse_Infinitesimal";
val HNatInfinite_inverse_not_zero = thm "HNatInfinite_inverse_not_zero";
*}

end
