(*  Title       : HyperNat.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp    
*)

header{*Construction of Hypernaturals using Ultrafilters*}

theory HyperNat = Star:

constdefs
    hypnatrel :: "((nat=>nat)*(nat=>nat)) set"
    "hypnatrel == {p. \<exists>X Y. p = ((X::nat=>nat),Y) &
                       {n::nat. X(n) = Y(n)} \<in> FreeUltrafilterNat}"

typedef hypnat = "UNIV//hypnatrel"
    by (auto simp add: quotient_def)

instance hypnat :: "{ord, zero, one, plus, times, minus}" ..

consts whn :: hypnat


defs (overloaded)

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
  "P \<le> (Q::hypnat) == \<exists>X Y. X \<in> Rep_hypnat(P) & Y \<in> Rep_hypnat(Q) &
                            {n::nat. X n \<le> Y n} \<in> FreeUltrafilterNat"

  hypnat_less_def: "(x < (y::hypnat)) == (x \<le> y & x \<noteq> y)"



subsection{*Properties of @{term hypnatrel}*}

text{*Proving that @{term hypnatrel} is an equivalence relation*}

lemma hypnatrel_iff:
     "((X,Y) \<in> hypnatrel) = ({n. X n = Y n}: FreeUltrafilterNat)"
apply (simp add: hypnatrel_def)
done

lemma hypnatrel_refl: "(x,x) \<in> hypnatrel"
by (simp add: hypnatrel_def)

lemma hypnatrel_sym: "(x,y) \<in> hypnatrel ==> (y,x) \<in> hypnatrel"
by (auto simp add: hypnatrel_def eq_commute)

lemma hypnatrel_trans [rule_format (no_asm)]:
     "(x,y) \<in> hypnatrel --> (y,z) \<in> hypnatrel --> (x,z) \<in> hypnatrel"
by (auto simp add: hypnatrel_def, ultra)

lemma equiv_hypnatrel:
     "equiv UNIV hypnatrel"
apply (simp add: equiv_def refl_def sym_def trans_def hypnatrel_refl)
apply (blast intro: hypnatrel_sym hypnatrel_trans)
done

(* (hypnatrel `` {x} = hypnatrel `` {y}) = ((x,y) \<in> hypnatrel) *)
lemmas equiv_hypnatrel_iff =
    eq_equiv_class_iff [OF equiv_hypnatrel UNIV_I UNIV_I, simp]

lemma hypnatrel_in_hypnat [simp]: "hypnatrel``{x}:hypnat"
by (simp add: hypnat_def hypnatrel_def quotient_def, blast)

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
apply (simp add: hypnat_def)
apply (auto elim!: quotientE equalityCE)
done

declare hypnat_empty_not_mem [simp]

lemma Rep_hypnat_nonempty: "Rep_hypnat x \<noteq> {}"
by (cut_tac x = x in Rep_hypnat, auto)

declare Rep_hypnat_nonempty [simp]


lemma eq_Abs_hypnat:
    "(!!x. z = Abs_hypnat(hypnatrel``{x}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_hypnat [unfolded hypnat_def, THEN quotientE])
apply (drule_tac f = Abs_hypnat in arg_cong)
apply (force simp add: Rep_hypnat_inverse)
done

theorem hypnat_cases [case_names Abs_hypnat, cases type: hypnat]:
    "(!!x. z = Abs_hypnat(hypnatrel``{x}) ==> P) ==> P"
by (rule eq_Abs_hypnat [of z], blast)

subsection{*Hypernat Addition*}

lemma hypnat_add_congruent2:
     "congruent2 hypnatrel hypnatrel (%X Y. hypnatrel``{%n. X n + Y n})"
by (simp add: congruent2_def, auto, ultra)

lemma hypnat_add:
  "Abs_hypnat(hypnatrel``{%n. X n}) + Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypnat(hypnatrel``{%n. X n + Y n})"
by (simp add: hypnat_add_def 
    UN_equiv_class2 [OF equiv_hypnatrel equiv_hypnatrel hypnat_add_congruent2])

lemma hypnat_add_commute: "(z::hypnat) + w = w + z"
apply (cases z, cases w)
apply (simp add: add_ac hypnat_add)
done

lemma hypnat_add_assoc: "((z1::hypnat) + z2) + z3 = z1 + (z2 + z3)"
apply (cases z1, cases z2, cases z3)
apply (simp add: hypnat_add nat_add_assoc)
done

lemma hypnat_add_zero_left: "(0::hypnat) + z = z"
apply (cases z)
apply (simp add: hypnat_zero_def hypnat_add)
done

instance hypnat :: plus_ac0
  by intro_classes
    (assumption |
      rule hypnat_add_commute hypnat_add_assoc hypnat_add_zero_left)+


subsection{*Subtraction inverse on @{typ hypreal}*}


lemma hypnat_minus_congruent2:
    "congruent2 hypnatrel hypnatrel (%X Y. hypnatrel``{%n. X n - Y n})"
by (simp add: congruent2_def, auto, ultra)

lemma hypnat_minus:
  "Abs_hypnat(hypnatrel``{%n. X n}) - Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypnat(hypnatrel``{%n. X n - Y n})"
by (simp add: hypnat_minus_def 
  UN_equiv_class2 [OF equiv_hypnatrel equiv_hypnatrel hypnat_minus_congruent2])

lemma hypnat_minus_zero: "z - z = (0::hypnat)"
apply (cases z)
apply (simp add: hypnat_zero_def hypnat_minus)
done

lemma hypnat_diff_0_eq_0: "(0::hypnat) - n = 0"
apply (cases n)
apply (simp add: hypnat_minus hypnat_zero_def)
done

declare hypnat_minus_zero [simp] hypnat_diff_0_eq_0 [simp]

lemma hypnat_add_is_0: "(m+n = (0::hypnat)) = (m=0 & n=0)"
apply (cases m, cases n)
apply (auto intro: FreeUltrafilterNat_subset dest: FreeUltrafilterNat_Int simp add: hypnat_zero_def hypnat_add)
done

declare hypnat_add_is_0 [iff]

lemma hypnat_diff_diff_left: "(i::hypnat) - j - k = i - (j+k)"
apply (cases i, cases j, cases k)
apply (simp add: hypnat_minus hypnat_add diff_diff_left)
done

lemma hypnat_diff_commute: "(i::hypnat) - j - k = i-k-j"
by (simp add: hypnat_diff_diff_left hypnat_add_commute)

lemma hypnat_diff_add_inverse: "((n::hypnat) + m) - n = m"
apply (cases m, cases n)
apply (simp add: hypnat_minus hypnat_add)
done
declare hypnat_diff_add_inverse [simp]

lemma hypnat_diff_add_inverse2:  "((m::hypnat) + n) - n = m"
apply (cases m, cases n)
apply (simp add: hypnat_minus hypnat_add)
done
declare hypnat_diff_add_inverse2 [simp]

lemma hypnat_diff_cancel: "((k::hypnat) + m) - (k+n) = m - n"
apply (cases k, cases m, cases n)
apply (simp add: hypnat_minus hypnat_add)
done
declare hypnat_diff_cancel [simp]

lemma hypnat_diff_cancel2: "((m::hypnat) + k) - (n+k) = m - n"
by (simp add: hypnat_add_commute [of _ k])
declare hypnat_diff_cancel2 [simp]

lemma hypnat_diff_add_0: "(n::hypnat) - (n+m) = (0::hypnat)"
apply (cases m, cases n)
apply (simp add: hypnat_zero_def hypnat_minus hypnat_add)
done
declare hypnat_diff_add_0 [simp]


subsection{*Hyperreal Multiplication*}

lemma hypnat_mult_congruent2:
    "congruent2 hypnatrel hypnatrel (%X Y. hypnatrel``{%n. X n * Y n})"
by (simp add: congruent2_def, auto, ultra)

lemma hypnat_mult:
  "Abs_hypnat(hypnatrel``{%n. X n}) * Abs_hypnat(hypnatrel``{%n. Y n}) =
   Abs_hypnat(hypnatrel``{%n. X n * Y n})"
by (simp add: hypnat_mult_def
   UN_equiv_class2 [OF equiv_hypnatrel equiv_hypnatrel hypnat_mult_congruent2])

lemma hypnat_mult_commute: "(z::hypnat) * w = w * z"
by (cases z, cases w, simp add: hypnat_mult mult_ac)

lemma hypnat_mult_assoc: "((z1::hypnat) * z2) * z3 = z1 * (z2 * z3)"
apply (cases z1, cases z2, cases z3)
apply (simp add: hypnat_mult mult_assoc)
done

lemma hypnat_mult_1: "(1::hypnat) * z = z"
apply (cases z)
apply (simp add: hypnat_mult hypnat_one_def)
done

lemma hypnat_diff_mult_distrib: "((m::hypnat) - n) * k = (m * k) - (n * k)"
apply (cases k, cases m, cases n)
apply (simp add: hypnat_mult hypnat_minus diff_mult_distrib)
done

lemma hypnat_diff_mult_distrib2: "(k::hypnat) * (m - n) = (k * m) - (k * n)"
by (simp add: hypnat_diff_mult_distrib hypnat_mult_commute [of k])

lemma hypnat_add_mult_distrib: "((z1::hypnat) + z2) * w = (z1 * w) + (z2 * w)"
apply (cases z1, cases z2, cases w)
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
apply (simp add: hypnat_le_def)
apply (auto intro!: lemma_hypnatrel_refl, ultra)
done

lemma hypnat_le_refl: "w \<le> (w::hypnat)"
apply (cases w)
apply (simp add: hypnat_le)
done

lemma hypnat_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::hypnat)"
apply (cases i, cases j, cases k)
apply (simp add: hypnat_le, ultra)
done

lemma hypnat_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::hypnat)"
apply (cases z, cases w)
apply (simp add: hypnat_le, ultra)
done

(* Axiom 'order_less_le' of class 'order': *)
lemma hypnat_less_le: "((w::hypnat) < z) = (w \<le> z & w \<noteq> z)"
by (simp add: hypnat_less_def)

instance hypnat :: order
  by intro_classes
    (assumption |
      rule hypnat_le_refl hypnat_le_trans hypnat_le_anti_sym hypnat_less_le)+

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma hypnat_le_linear: "(z::hypnat) \<le> w | w \<le> z"
apply (cases z, cases w)
apply (auto simp add: hypnat_le, ultra)
done

instance hypnat :: linorder
  by intro_classes (rule hypnat_le_linear)

lemma hypnat_add_left_mono: "x \<le> y ==> z + x \<le> z + (y::hypnat)"
apply (cases x, cases y, cases z)
apply (auto simp add: hypnat_le hypnat_add)
done

lemma hypnat_mult_less_mono2: "[| (0::hypnat)<z; x<y |] ==> z*x<z*y"
apply (cases x, cases y, cases z)
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

lemma hypnat_le_zero_cancel [iff]: "(n \<le> (0::hypnat)) = (n = 0)"
apply (cases n)
apply (simp add: hypnat_zero_def hypnat_le)
done

lemma hypnat_mult_is_0 [simp]: "(m*n = (0::hypnat)) = (m=0 | n=0)"
apply (cases m, cases n)
apply (auto simp add: hypnat_zero_def hypnat_mult, ultra+)
done

lemma hypnat_diff_is_0_eq [simp]: "((m::hypnat) - n = 0) = (m \<le> n)"
apply (cases m, cases n)
apply (simp add: hypnat_le hypnat_minus hypnat_zero_def)
done



subsection{*Theorems for Ordering*}

lemma hypnat_less:
      "(Abs_hypnat(hypnatrel``{%n. X n}) < Abs_hypnat(hypnatrel``{%n. Y n})) =
       ({n. X n < Y n} \<in> FreeUltrafilterNat)"
apply (auto simp add: hypnat_le  linorder_not_le [symmetric])
apply (ultra+)
done

lemma hypnat_not_less0 [iff]: "~ n < (0::hypnat)"
apply (cases n)
apply (auto simp add: hypnat_zero_def hypnat_less)
done

lemma hypnat_less_one [iff]:
      "(n < (1::hypnat)) = (n=0)"
apply (cases n)
apply (auto simp add: hypnat_zero_def hypnat_one_def hypnat_less)
done

lemma hypnat_add_diff_inverse: "~ m<n ==> n+(m-n) = (m::hypnat)"
apply (cases m, cases n)
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

lemma hypnat_add_self_not_less: "~ (x + y < (x::hypnat))"
by (simp add: linorder_not_le [symmetric] add_commute [of x]) 

lemma hypnat_diff_split:
    "P(a - b::hypnat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
    -- {* elimination of @{text -} on @{text hypnat} *}
proof (cases "a<b" rule: case_split)
  case True
    thus ?thesis
      by (auto simp add: hypnat_add_self_not_less order_less_imp_le 
                         hypnat_diff_is_0_eq [THEN iffD2])
next
  case False
    thus ?thesis
      by (auto simp add: linorder_not_less dest: order_le_less_trans) 
qed


subsection{*The Embedding @{term hypnat_of_nat} Preserves Ring and 
      Order Properties*}

constdefs

  hypnat_of_nat   :: "nat => hypnat"
  "hypnat_of_nat m  == of_nat m"

  (* the set of infinite hypernatural numbers *)
  HNatInfinite :: "hypnat set"
  "HNatInfinite == {n. n \<notin> Nats}"


lemma hypnat_of_nat_add:
      "hypnat_of_nat ((z::nat) + w) = hypnat_of_nat z + hypnat_of_nat w"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_mult:
      "hypnat_of_nat (z * w) = hypnat_of_nat z * hypnat_of_nat w"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_less_iff [simp]:
      "(hypnat_of_nat z < hypnat_of_nat w) = (z < w)"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_le_iff [simp]:
      "(hypnat_of_nat z \<le> hypnat_of_nat w) = (z \<le> w)"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_eq_iff [simp]:
      "(hypnat_of_nat z = hypnat_of_nat w) = (z = w)"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_one [simp]: "hypnat_of_nat (Suc 0) = (1::hypnat)"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_zero [simp]: "hypnat_of_nat 0 = 0"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_zero_iff [simp]: "(hypnat_of_nat n = 0) = (n = 0)"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_Suc [simp]:
     "hypnat_of_nat (Suc n) = hypnat_of_nat n + (1::hypnat)"
by (simp add: hypnat_of_nat_def)

lemma hypnat_of_nat_minus:
      "hypnat_of_nat ((j::nat) - k) = hypnat_of_nat j - hypnat_of_nat k"
by (simp add: hypnat_of_nat_def split: nat_diff_split hypnat_diff_split)


subsection{*Existence of an Infinite Hypernatural Number*}

lemma hypnat_omega: "hypnatrel``{%n::nat. n} \<in> hypnat"
by auto

lemma Rep_hypnat_omega: "Rep_hypnat(whn) \<in> hypnat"
by (simp add: hypnat_omega_def)

text{*Existence of infinite number not corresponding to any natural number
follows because member @{term FreeUltrafilterNat} is not finite.
See @{text HyperDef.thy} for similar argument.*}


subsection{*Properties of the set @{term Nats} of Embedded Natural Numbers*}

lemma of_nat_eq_add [rule_format]:
     "\<forall>d::hypnat. of_nat m = of_nat n + d --> d \<in> range of_nat"
apply (induct n) 
apply (auto simp add: add_assoc) 
apply (case_tac x) 
apply (auto simp add: add_commute [of 1]) 
done

lemma Nats_diff [simp]: "[|a \<in> Nats; b \<in> Nats|] ==> (a-b :: hypnat) \<in> Nats"
by (auto simp add: of_nat_eq_add Nats_def split: hypnat_diff_split)

lemma lemma_unbounded_set [simp]: "{n::nat. m < n} \<in> FreeUltrafilterNat"
apply (insert finite_atMost [of m]) 
apply (simp add: atMost_def) 
apply (drule FreeUltrafilterNat_finite) 
apply (drule FreeUltrafilterNat_Compl_mem, ultra)
done

lemma Compl_Collect_le: "- {n::nat. N \<le> n} = {n. n < N}"
by (simp add: Collect_neg_eq [symmetric] linorder_not_le) 


lemma hypnat_of_nat_eq:
     "hypnat_of_nat m  = Abs_hypnat(hypnatrel``{%n::nat. m})"
apply (induct m) 
apply (simp_all add: hypnat_zero_def hypnat_one_def hypnat_add) 
done

lemma SHNat_eq: "Nats = {n. \<exists>N. n = hypnat_of_nat N}"
by (force simp add: hypnat_of_nat_def Nats_def) 

lemma hypnat_omega_gt_SHNat:
     "n \<in> Nats ==> n < whn"
apply (auto simp add: hypnat_of_nat_eq hypnat_less_def hypnat_le_def
                      hypnat_omega_def SHNat_eq)
 prefer 2 apply (force dest: FreeUltrafilterNat_not_finite)
apply (auto intro!: exI)
apply (rule cofinite_mem_FreeUltrafilterNat)
apply (simp add: Compl_Collect_le finite_nat_segment) 
done

(* Infinite hypernatural not in embedded Nats *)
lemma SHNAT_omega_not_mem [simp]: "whn \<notin> Nats"
by (blast dest: hypnat_omega_gt_SHNat)

lemma hypnat_of_nat_less_whn [simp]: "hypnat_of_nat n < whn"
apply (insert hypnat_omega_gt_SHNat [of "hypnat_of_nat n"])
apply (simp add: hypnat_of_nat_def) 
done

lemma hypnat_of_nat_le_whn [simp]: "hypnat_of_nat n \<le> whn"
by (rule hypnat_of_nat_less_whn [THEN order_less_imp_le])

lemma hypnat_zero_less_hypnat_omega [simp]: "0 < whn"
by (simp add: hypnat_omega_gt_SHNat)

lemma hypnat_one_less_hypnat_omega [simp]: "(1::hypnat) < whn"
by (simp add: hypnat_omega_gt_SHNat)


subsection{*Infinite Hypernatural Numbers -- @{term HNatInfinite}*}

lemma HNatInfinite_whn [simp]: "whn \<in> HNatInfinite"
by (simp add: HNatInfinite_def)

lemma Nats_not_HNatInfinite_iff: "(x \<in> Nats) = (x \<notin> HNatInfinite)"
by (simp add: HNatInfinite_def)

lemma HNatInfinite_not_Nats_iff: "(x \<in> HNatInfinite) = (x \<notin> Nats)"
by (simp add: HNatInfinite_def)


subsection{*Alternative Characterization of the Set of Infinite Hypernaturals:
@{term "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"}*}

(*??delete? similar reasoning in hypnat_omega_gt_SHNat above*)
lemma HNatInfinite_FreeUltrafilterNat_lemma:
     "\<forall>N::nat. {n. f n \<noteq> N} \<in> FreeUltrafilterNat
      ==> {n. N < f n} \<in> FreeUltrafilterNat"
apply (induct_tac "N")
apply (drule_tac x = 0 in spec)
apply (rule ccontr, drule FreeUltrafilterNat_Compl_mem, drule FreeUltrafilterNat_Int, assumption, simp)
apply (drule_tac x = "Suc n" in spec, ultra)
done

lemma HNatInfinite_iff: "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"
apply (auto simp add: HNatInfinite_def SHNat_eq hypnat_of_nat_eq)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (auto elim: HNatInfinite_FreeUltrafilterNat_lemma 
            simp add: hypnat_less FreeUltrafilterNat_Compl_iff1 
                      Collect_neg_eq [symmetric])
done


subsection{*Alternative Characterization of @{term HNatInfinite} using 
Free Ultrafilter*}

lemma HNatInfinite_FreeUltrafilterNat:
     "x \<in> HNatInfinite 
      ==> \<exists>X \<in> Rep_hypnat x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat"
apply (cases x)
apply (auto simp add: HNatInfinite_iff SHNat_eq hypnat_of_nat_eq)
apply (rule bexI [OF _ lemma_hypnatrel_refl], clarify) 
apply (auto simp add: hypnat_of_nat_def hypnat_less)
done

lemma FreeUltrafilterNat_HNatInfinite:
     "\<exists>X \<in> Rep_hypnat x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat
      ==> x \<in> HNatInfinite"
apply (cases x)
apply (auto simp add: hypnat_less HNatInfinite_iff SHNat_eq hypnat_of_nat_eq)
apply (drule spec, ultra, auto) 
done

lemma HNatInfinite_FreeUltrafilterNat_iff:
     "(x \<in> HNatInfinite) = 
      (\<exists>X \<in> Rep_hypnat x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat)"
by (blast intro: HNatInfinite_FreeUltrafilterNat 
                 FreeUltrafilterNat_HNatInfinite)

lemma HNatInfinite_gt_one [simp]: "x \<in> HNatInfinite ==> (1::hypnat) < x"
by (auto simp add: HNatInfinite_iff)

lemma zero_not_mem_HNatInfinite [simp]: "0 \<notin> HNatInfinite"
apply (auto simp add: HNatInfinite_iff)
apply (drule_tac a = " (1::hypnat) " in equals0D)
apply simp
done

lemma HNatInfinite_not_eq_zero: "x \<in> HNatInfinite ==> 0 < x"
apply (drule HNatInfinite_gt_one) 
apply (auto simp add: order_less_trans [OF zero_less_one])
done

lemma HNatInfinite_ge_one [simp]: "x \<in> HNatInfinite ==> (1::hypnat) \<le> x"
by (blast intro: order_less_imp_le HNatInfinite_gt_one)


subsection{*Closure Rules*}

lemma HNatInfinite_add:
     "[| x \<in> HNatInfinite; y \<in> HNatInfinite |] ==> x + y \<in> HNatInfinite"
apply (auto simp add: HNatInfinite_iff)
apply (drule bspec, assumption)
apply (drule bspec [OF _ Nats_0])
apply (drule add_strict_mono, assumption, simp)
done

lemma HNatInfinite_SHNat_add:
     "[| x \<in> HNatInfinite; y \<in> Nats |] ==> x + y \<in> HNatInfinite"
apply (auto simp add: HNatInfinite_not_Nats_iff) 
apply (drule_tac a = "x + y" in Nats_diff, auto) 
done

lemma HNatInfinite_Nats_imp_less: "[| x \<in> HNatInfinite; y \<in> Nats |] ==> y < x"
by (simp add: HNatInfinite_iff) 

lemma HNatInfinite_SHNat_diff:
  assumes x: "x \<in> HNatInfinite" and y: "y \<in> Nats" 
  shows "x - y \<in> HNatInfinite"
proof -
  have "y < x" by (simp add: HNatInfinite_Nats_imp_less prems)
  hence "x - y + y = x" by (simp add: order_less_imp_le)
  with x show ?thesis
    by (force simp add: HNatInfinite_not_Nats_iff 
              dest: Nats_add [of "x-y", OF _ y]) 
qed

lemma HNatInfinite_add_one:
     "x \<in> HNatInfinite ==> x + (1::hypnat) \<in> HNatInfinite"
by (auto intro: HNatInfinite_SHNat_add)

lemma HNatInfinite_is_Suc: "x \<in> HNatInfinite ==> \<exists>y. x = y + (1::hypnat)"
apply (rule_tac x = "x - (1::hypnat) " in exI)
apply auto
done


subsection{*Embedding of the Hypernaturals into the Hyperreals*}
text{*Obtained using the nonstandard extension of the naturals*}

constdefs
  hypreal_of_hypnat :: "hypnat => hypreal"
   "hypreal_of_hypnat N  == 
      Abs_hypreal(\<Union>X \<in> Rep_hypnat(N). hyprel``{%n::nat. real (X n)})"


lemma HNat_hypreal_of_nat [simp]: "hypreal_of_nat N \<in> Nats"
by (simp add: hypreal_of_nat_def) 

(*WARNING: FRAGILE!*)
lemma lemma_hyprel_FUFN:
     "(Ya \<in> hyprel ``{%n. f(n)}) = ({n. f n = Ya n} \<in> FreeUltrafilterNat)"
by force

lemma hypreal_of_hypnat:
      "hypreal_of_hypnat (Abs_hypnat(hypnatrel``{%n. X n})) =
       Abs_hypreal(hyprel `` {%n. real (X n)})"
apply (simp add: hypreal_of_hypnat_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (auto elim: FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset] 
       simp add: lemma_hyprel_FUFN)
done

lemma hypreal_of_hypnat_inject [simp]:
     "(hypreal_of_hypnat m = hypreal_of_hypnat n) = (m=n)"
apply (cases m, cases n)
apply (auto simp add: hypreal_of_hypnat)
done

lemma hypreal_of_hypnat_zero: "hypreal_of_hypnat 0 = 0"
by (simp add: hypnat_zero_def hypreal_zero_def hypreal_of_hypnat)

lemma hypreal_of_hypnat_one: "hypreal_of_hypnat (1::hypnat) = 1"
by (simp add: hypnat_one_def hypreal_one_def hypreal_of_hypnat)

lemma hypreal_of_hypnat_add [simp]:
     "hypreal_of_hypnat (m + n) = hypreal_of_hypnat m + hypreal_of_hypnat n"
apply (cases m, cases n)
apply (simp add: hypreal_of_hypnat hypreal_add hypnat_add real_of_nat_add)
done

lemma hypreal_of_hypnat_mult [simp]:
     "hypreal_of_hypnat (m * n) = hypreal_of_hypnat m * hypreal_of_hypnat n"
apply (cases m, cases n)
apply (simp add: hypreal_of_hypnat hypreal_mult hypnat_mult real_of_nat_mult)
done

lemma hypreal_of_hypnat_less_iff [simp]:
     "(hypreal_of_hypnat n < hypreal_of_hypnat m) = (n < m)"
apply (cases m, cases n)
apply (simp add: hypreal_of_hypnat hypreal_less hypnat_less)
done

lemma hypreal_of_hypnat_eq_zero_iff: "(hypreal_of_hypnat N = 0) = (N = 0)"
by (simp add: hypreal_of_hypnat_zero [symmetric])
declare hypreal_of_hypnat_eq_zero_iff [simp]

lemma hypreal_of_hypnat_ge_zero [simp]: "0 \<le> hypreal_of_hypnat n"
apply (cases n)
apply (simp add: hypreal_of_hypnat hypreal_zero_num hypreal_le)
done

lemma HNatInfinite_inverse_Infinitesimal [simp]:
     "n \<in> HNatInfinite ==> inverse (hypreal_of_hypnat n) \<in> Infinitesimal"
apply (cases n)
apply (auto simp add: hypreal_of_hypnat hypreal_inverse 
      HNatInfinite_FreeUltrafilterNat_iff Infinitesimal_FreeUltrafilterNat_iff2)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl, auto)
apply (drule_tac x = "m + 1" in spec, ultra)
done

lemma HNatInfinite_hypreal_of_hypnat_gt_zero:
     "N \<in> HNatInfinite ==> 0 < hypreal_of_hypnat N"
apply (rule ccontr)
apply (simp add: hypreal_of_hypnat_zero [symmetric] linorder_not_less)
done


ML
{*
val hypnat_of_nat_def = thm"hypnat_of_nat_def";
val HNatInfinite_def = thm"HNatInfinite_def";
val hypreal_of_hypnat_def = thm"hypreal_of_hypnat_def";
val hypnat_zero_def = thm"hypnat_zero_def";
val hypnat_one_def = thm"hypnat_one_def";
val hypnat_omega_def = thm"hypnat_omega_def";

val hypnatrel_iff = thm "hypnatrel_iff";
val hypnatrel_in_hypnat = thm "hypnatrel_in_hypnat";
val inj_on_Abs_hypnat = thm "inj_on_Abs_hypnat";
val inj_Rep_hypnat = thm "inj_Rep_hypnat";
val lemma_hypnatrel_refl = thm "lemma_hypnatrel_refl";
val hypnat_empty_not_mem = thm "hypnat_empty_not_mem";
val Rep_hypnat_nonempty = thm "Rep_hypnat_nonempty";
val eq_Abs_hypnat = thm "eq_Abs_hypnat";
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
val hypnat_of_nat_eq = thm"hypnat_of_nat_eq"
val SHNat_eq = thm"SHNat_eq"
val hypnat_of_nat_one = thm "hypnat_of_nat_one";
val hypnat_of_nat_zero = thm "hypnat_of_nat_zero";
val hypnat_of_nat_zero_iff = thm "hypnat_of_nat_zero_iff";
val hypnat_of_nat_Suc = thm "hypnat_of_nat_Suc";
val hypnat_omega = thm "hypnat_omega";
val Rep_hypnat_omega = thm "Rep_hypnat_omega";
val SHNAT_omega_not_mem = thm "SHNAT_omega_not_mem";
val cofinite_mem_FreeUltrafilterNat = thm "cofinite_mem_FreeUltrafilterNat";
val hypnat_omega_gt_SHNat = thm "hypnat_omega_gt_SHNat";
val hypnat_of_nat_less_whn = thm "hypnat_of_nat_less_whn";
val hypnat_of_nat_le_whn = thm "hypnat_of_nat_le_whn";
val hypnat_zero_less_hypnat_omega = thm "hypnat_zero_less_hypnat_omega";
val hypnat_one_less_hypnat_omega = thm "hypnat_one_less_hypnat_omega";
val HNatInfinite_whn = thm "HNatInfinite_whn";
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
val HNatInfinite_is_Suc = thm "HNatInfinite_is_Suc";
val HNat_hypreal_of_nat = thm "HNat_hypreal_of_nat";
val hypreal_of_hypnat = thm "hypreal_of_hypnat";
val hypreal_of_hypnat_zero = thm "hypreal_of_hypnat_zero";
val hypreal_of_hypnat_one = thm "hypreal_of_hypnat_one";
val hypreal_of_hypnat_add = thm "hypreal_of_hypnat_add";
val hypreal_of_hypnat_mult = thm "hypreal_of_hypnat_mult";
val hypreal_of_hypnat_less_iff = thm "hypreal_of_hypnat_less_iff";
val hypreal_of_hypnat_ge_zero = thm "hypreal_of_hypnat_ge_zero";
val HNatInfinite_inverse_Infinitesimal = thm "HNatInfinite_inverse_Infinitesimal";
*}

end
