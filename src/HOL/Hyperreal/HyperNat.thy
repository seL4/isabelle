(*  Title       : HyperNat.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp    
*)

header{*Construction of Hypernaturals using Ultrafilters*}

theory HyperNat
imports Star
begin

types hypnat = "nat star"
(*
constdefs
    hypnatrel :: "((nat=>nat)*(nat=>nat)) set"
    "hypnatrel == {p. \<exists>X Y. p = ((X::nat=>nat),Y) &
                       {n::nat. X(n) = Y(n)} \<in> FreeUltrafilterNat}"

typedef hypnat = "UNIV//hypnatrel"
    by (auto simp add: quotient_def)

instance hypnat :: "{ord, zero, one, plus, times, minus}" ..
*)
consts whn :: hypnat


defs
  (* omega is in fact an infinite hypernatural number = [<1,2,3,...>] *)
  hypnat_omega_def:  "whn == Abs_star(starrel``{%n::nat. n})"

lemma hypnat_zero_def:  "0 == Abs_star(starrel``{%n::nat. 0})"
by (simp only: star_zero_def star_of_def star_n_def)

lemma hypnat_one_def:   "1 == Abs_star(starrel``{%n::nat. 1})"
by (simp only: star_one_def star_of_def star_n_def)

  (** hypernatural arithmetic **)
(*
  hypnat_zero_def:  "0 == Abs_hypnat(hypnatrel``{%n::nat. 0})"
  hypnat_one_def:   "1 == Abs_hypnat(hypnatrel``{%n::nat. 1})"
*)
(*
  hypnat_add_def:
  "P + Q == Abs_hypnat(\<Union>X \<in> Rep_hypnat(P). \<Union>Y \<in> Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n + Y n})"

  hypnat_mult_def:
  "P * Q == Abs_hypnat(\<Union>X \<in> Rep_hypnat(P). \<Union>Y \<in> Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n * Y n})"

  hypnat_minus_def:
  "P - Q == Abs_hypnat(\<Union>X \<in> Rep_hypnat(P). \<Union>Y \<in> Rep_hypnat(Q).
                hypnatrel``{%n::nat. X n - Y n})"
*)

(*
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
*)
(* (hypnatrel `` {x} = hypnatrel `` {y}) = ((x,y) \<in> hypnatrel) *)
(*
lemmas equiv_hypnatrel_iff =
    eq_equiv_class_iff [OF equiv_hypnatrel UNIV_I UNIV_I, simp]

lemma hypnatrel_in_hypnat [simp]: "hypnatrel``{x}:hypnat"
by (simp add: hypnat_def hypnatrel_def quotient_def, blast)

declare Abs_hypnat_inject [simp] Abs_hypnat_inverse [simp]
declare equiv_hypnatrel [THEN eq_equiv_class_iff, simp]
declare hypnatrel_iff [iff]

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
*)
subsection{*Hypernat Addition*}
(*
lemma hypnat_add_congruent2:
     "(%X Y. hypnatrel``{%n. X n + Y n}) respects2 hypnatrel"
by (simp add: congruent2_def, auto, ultra)
*)
lemma hypnat_add:
  "Abs_star(starrel``{%n. X n}) + Abs_star(starrel``{%n. Y n}) =
   Abs_star(starrel``{%n. X n + Y n})"
by (rule hypreal_add)

lemma hypnat_add_commute: "(z::hypnat) + w = w + z"
by (rule add_commute)

lemma hypnat_add_assoc: "((z1::hypnat) + z2) + z3 = z1 + (z2 + z3)"
by (rule add_assoc)

lemma hypnat_add_zero_left: "(0::hypnat) + z = z"
by (rule comm_monoid_add_class.add_0)

(*
instance hypnat :: comm_monoid_add
  by intro_classes
    (assumption |
      rule hypnat_add_commute hypnat_add_assoc hypnat_add_zero_left)+
*)

subsection{*Subtraction inverse on @{typ hypreal}*}

(*
lemma hypnat_minus_congruent2:
    "(%X Y. starrel``{%n. X n - Y n}) respects2 starrel"
by (simp add: congruent2_def, auto, ultra)
*)
lemma hypnat_minus:
  "Abs_star(starrel``{%n. X n}) - Abs_star(starrel``{%n. Y n}) =
   Abs_star(starrel``{%n. X n - Y n})"
by (rule hypreal_diff)

lemma hypnat_minus_zero: "!!z. z - z = (0::hypnat)"
by transfer (rule diff_self_eq_0)

lemma hypnat_diff_0_eq_0: "!!n. (0::hypnat) - n = 0"
by transfer (rule diff_0_eq_0)

declare hypnat_minus_zero [simp] hypnat_diff_0_eq_0 [simp]

lemma hypnat_add_is_0: "!!m n. (m+n = (0::hypnat)) = (m=0 & n=0)"
by transfer (rule add_is_0)

declare hypnat_add_is_0 [iff]

lemma hypnat_diff_diff_left: "!!i j k. (i::hypnat) - j - k = i - (j+k)"
by transfer (rule diff_diff_left)

lemma hypnat_diff_commute: "!!i j k. (i::hypnat) - j - k = i-k-j"
by transfer (rule diff_commute)

lemma hypnat_diff_add_inverse: "!!m n. ((n::hypnat) + m) - n = m"
by transfer (rule diff_add_inverse)
declare hypnat_diff_add_inverse [simp]

lemma hypnat_diff_add_inverse2:  "!!m n. ((m::hypnat) + n) - n = m"
by transfer (rule diff_add_inverse2)
declare hypnat_diff_add_inverse2 [simp]

lemma hypnat_diff_cancel: "!!k m n. ((k::hypnat) + m) - (k+n) = m - n"
by transfer (rule diff_cancel)
declare hypnat_diff_cancel [simp]

lemma hypnat_diff_cancel2: "!!k m n. ((m::hypnat) + k) - (n+k) = m - n"
by transfer (rule diff_cancel2)
declare hypnat_diff_cancel2 [simp]

lemma hypnat_diff_add_0: "!!m n. (n::hypnat) - (n+m) = (0::hypnat)"
by transfer (rule diff_add_0)
declare hypnat_diff_add_0 [simp]


subsection{*Hyperreal Multiplication*}
(*
lemma hypnat_mult_congruent2:
    "(%X Y. starrel``{%n. X n * Y n}) respects2 starrel"
by (simp add: congruent2_def, auto, ultra)
*)
lemma hypnat_mult:
  "Abs_star(starrel``{%n. X n}) * Abs_star(starrel``{%n. Y n}) =
   Abs_star(starrel``{%n. X n * Y n})"
by (rule hypreal_mult)

lemma hypnat_mult_commute: "(z::hypnat) * w = w * z"
by (rule mult_commute)

lemma hypnat_mult_assoc: "((z1::hypnat) * z2) * z3 = z1 * (z2 * z3)"
by (rule mult_assoc)

lemma hypnat_mult_1: "(1::hypnat) * z = z"
by (rule mult_1_left)

lemma hypnat_diff_mult_distrib: "!!k m n. ((m::hypnat) - n) * k = (m * k) - (n * k)"
by transfer (rule diff_mult_distrib)

lemma hypnat_diff_mult_distrib2: "!!k m n. (k::hypnat) * (m - n) = (k * m) - (k * n)"
by transfer (rule diff_mult_distrib2)

lemma hypnat_add_mult_distrib: "((z1::hypnat) + z2) * w = (z1 * w) + (z2 * w)"
by (rule left_distrib)

lemma hypnat_add_mult_distrib2: "(w::hypnat) * (z1 + z2) = (w * z1) + (w * z2)"
by (rule right_distrib)

text{*one and zero are distinct*}
lemma hypnat_zero_not_eq_one: "(0::hypnat) \<noteq> (1::hypnat)"
by (rule zero_neq_one)
declare hypnat_zero_not_eq_one [THEN not_sym, simp]

(*
text{*The hypernaturals form a @{text comm_semiring_1_cancel}: *}
instance hypnat :: comm_semiring_1_cancel
proof
  fix i j k :: hypnat
  show "(i * j) * k = i * (j * k)" by (rule hypnat_mult_assoc)
  show "i * j = j * i" by (rule hypnat_mult_commute)
  show "1 * i = i" by (rule hypnat_mult_1)
  show "(i + j) * k = i * k + j * k" by (simp add: hypnat_add_mult_distrib)
  show "0 \<noteq> (1::hypnat)" by (rule hypnat_zero_not_eq_one)
  assume "k+i = k+j"
  hence "(k+i) - k = (k+j) - k" by simp
  thus "i=j" by simp
qed
*)

subsection{*Properties of The @{text "\<le>"} Relation*}

lemma hypnat_le:
      "(Abs_star(starrel``{%n. X n}) \<le> Abs_star(starrel``{%n. Y n})) =
       ({n. X n \<le> Y n} \<in> FreeUltrafilterNat)"
by (rule hypreal_le)

lemma hypnat_le_refl: "w \<le> (w::hypnat)"
by (rule order_refl)

lemma hypnat_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::hypnat)"
by (rule order_trans)

lemma hypnat_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::hypnat)"
by (rule order_antisym)

(* Axiom 'order_less_le' of class 'order': *)
lemma hypnat_less_le: "((w::hypnat) < z) = (w \<le> z & w \<noteq> z)"
by (rule order_less_le)

(*
instance hypnat :: order
  by intro_classes
    (assumption |
      rule hypnat_le_refl hypnat_le_trans hypnat_le_anti_sym hypnat_less_le)+
*)
(* Axiom 'linorder_linear' of class 'linorder': *)
lemma hypnat_le_linear: "(z::hypnat) \<le> w | w \<le> z"
by (rule linorder_linear)
(*
instance hypnat :: linorder
  by intro_classes (rule hypnat_le_linear)
*)
lemma hypnat_add_left_mono: "x \<le> y ==> z + x \<le> z + (y::hypnat)"
by (rule add_left_mono)

lemma hypnat_mult_less_mono2: "[| (0::hypnat)<z; x<y |] ==> z*x<z*y"
by (rule mult_strict_left_mono)


subsection{*The Hypernaturals Form an Ordered @{text comm_semiring_1_cancel} *}
(*
instance hypnat :: ordered_semidom
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
*)
lemma hypnat_le_zero_cancel [iff]: "!!n. (n \<le> (0::hypnat)) = (n = 0)"
by transfer (rule le_0_eq)

lemma hypnat_mult_is_0 [simp]: "!!m n. (m*n = (0::hypnat)) = (m=0 | n=0)"
by transfer (rule mult_is_0)

lemma hypnat_diff_is_0_eq [simp]: "!!m n. ((m::hypnat) - n = 0) = (m \<le> n)"
by transfer (rule diff_is_0_eq)



subsection{*Theorems for Ordering*}

lemma hypnat_less:
      "(Abs_star(starrel``{%n. X n}) < Abs_star(starrel``{%n. Y n})) =
       ({n. X n < Y n} \<in> FreeUltrafilterNat)"
by (rule hypreal_less)

lemma hypnat_not_less0 [iff]: "!!n. ~ n < (0::hypnat)"
by transfer (rule not_less0)

lemma hypnat_less_one [iff]:
      "!!n. (n < (1::hypnat)) = (n=0)"
by transfer (rule less_one)

lemma hypnat_add_diff_inverse: "!!m n. ~ m<n ==> n+(m-n) = (m::hypnat)"
by transfer (rule add_diff_inverse)

lemma hypnat_le_add_diff_inverse [simp]: "!!m n. n \<le> m ==> n+(m-n) = (m::hypnat)"
by transfer (rule le_add_diff_inverse)

lemma hypnat_le_add_diff_inverse2 [simp]: "!!m n. n\<le>m ==> (m-n)+n = (m::hypnat)"
by transfer (rule le_add_diff_inverse2)

declare hypnat_le_add_diff_inverse2 [OF order_less_imp_le]

lemma hypnat_le0 [iff]: "!!n. (0::hypnat) \<le> n"
by transfer (rule le0)

lemma hypnat_add_self_le [simp]: "!!x n. (x::hypnat) \<le> n + x"
by transfer (rule le_add2)

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


subsection{*The Embedding @{term hypnat_of_nat} Preserves @{text
comm_ring_1} and Order Properties*}

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


subsection{*Existence of an infinite hypernatural number*}

lemma hypnat_omega: "starrel``{%n::nat. n} \<in> star"
by auto

lemma Rep_star_omega: "Rep_star(whn) \<in> star"
by (simp add: hypnat_omega_def)

text{*Existence of infinite number not corresponding to any natural number
follows because member @{term FreeUltrafilterNat} is not finite.
See @{text HyperDef.thy} for similar argument.*}


subsection{*Properties of the set of embedded natural numbers*}

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
     "hypnat_of_nat m  = Abs_star(starrel``{%n::nat. m})"
apply (induct m) 
apply (simp_all add: hypnat_zero_def hypnat_one_def hypnat_add) 
done

lemma SHNat_eq: "Nats = {n. \<exists>N. n = hypnat_of_nat N}"
by (force simp add: hypnat_of_nat_def Nats_def) 

lemma hypnat_omega_gt_SHNat:
     "n \<in> Nats ==> n < whn"
by (auto simp add: hypnat_of_nat_eq hypnat_less hypnat_omega_def SHNat_eq)

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


subsection{*Alternative characterization of the set of infinite hypernaturals*}

text{* @{term "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"}*}

(*??delete? similar reasoning in hypnat_omega_gt_SHNat above*)
lemma HNatInfinite_FreeUltrafilterNat_lemma:
     "\<forall>N::nat. {n. f n \<noteq> N} \<in> FreeUltrafilterNat
      ==> {n. N < f n} \<in> FreeUltrafilterNat"
apply (induct_tac N)
apply (drule_tac x = 0 in spec)
apply (rule ccontr, drule FreeUltrafilterNat_Compl_mem, drule FreeUltrafilterNat_Int, assumption, simp)
apply (drule_tac x = "Suc n" in spec, ultra)
done

lemma HNatInfinite_iff: "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"
apply (auto simp add: HNatInfinite_def SHNat_eq hypnat_of_nat_eq)
apply (rule_tac z = x in eq_Abs_star)
apply (auto elim: HNatInfinite_FreeUltrafilterNat_lemma 
            simp add: hypnat_less FreeUltrafilterNat_Compl_iff1 
                      Collect_neg_eq [symmetric])
done


subsection{*Alternative Characterization of @{term HNatInfinite} using 
Free Ultrafilter*}

lemma HNatInfinite_FreeUltrafilterNat:
     "x \<in> HNatInfinite 
      ==> \<exists>X \<in> Rep_star x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat"
apply (rule_tac z=x in eq_Abs_star)
apply (auto simp add: HNatInfinite_iff SHNat_eq hypnat_of_nat_eq)
apply (rule bexI [OF _ lemma_starrel_refl], clarify) 
apply (auto simp add: hypnat_of_nat_def hypnat_less)
done

lemma FreeUltrafilterNat_HNatInfinite:
     "\<exists>X \<in> Rep_star x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat
      ==> x \<in> HNatInfinite"
apply (rule_tac z=x in eq_Abs_star)
apply (auto simp add: hypnat_less HNatInfinite_iff SHNat_eq hypnat_of_nat_eq)
apply (drule spec, ultra, auto) 
done

lemma HNatInfinite_FreeUltrafilterNat_iff:
     "(x \<in> HNatInfinite) = 
      (\<exists>X \<in> Rep_star x. \<forall>u. {n. u < X n}:  FreeUltrafilterNat)"
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
      Abs_star(\<Union>X \<in> Rep_star(N). starrel``{%n::nat. real (X n)})"


lemma HNat_hypreal_of_nat [simp]: "hypreal_of_nat N \<in> Nats"
by (simp add: hypreal_of_nat_def) 

(*WARNING: FRAGILE!*)
lemma lemma_starrel_FUFN:
     "(Ya \<in> starrel ``{%n. f(n)}) = ({n. f n = Ya n} \<in> FreeUltrafilterNat)"
by force

lemma hypreal_of_hypnat:
      "hypreal_of_hypnat (Abs_star(starrel``{%n. X n})) =
       Abs_star(starrel `` {%n. real (X n)})"
apply (simp add: hypreal_of_hypnat_def)
apply (rule_tac f = Abs_star in arg_cong)
apply (auto elim: FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset] 
       simp add: lemma_starrel_FUFN)
done

lemma hypreal_of_hypnat_inject [simp]:
     "(hypreal_of_hypnat m = hypreal_of_hypnat n) = (m=n)"
apply (rule_tac z=m in eq_Abs_star, rule_tac z=n in eq_Abs_star)
apply (auto simp add: hypreal_of_hypnat)
done

lemma hypreal_of_hypnat_zero: "hypreal_of_hypnat 0 = 0"
by (simp add: hypnat_zero_def hypreal_zero_def hypreal_of_hypnat)

lemma hypreal_of_hypnat_one: "hypreal_of_hypnat (1::hypnat) = 1"
by (simp add: hypnat_one_def hypreal_one_def hypreal_of_hypnat)

lemma hypreal_of_hypnat_add [simp]:
     "hypreal_of_hypnat (m + n) = hypreal_of_hypnat m + hypreal_of_hypnat n"
apply (rule_tac z=m in eq_Abs_star, rule_tac z=n in eq_Abs_star)
apply (simp add: hypreal_of_hypnat hypreal_add hypnat_add real_of_nat_add)
done

lemma hypreal_of_hypnat_mult [simp]:
     "hypreal_of_hypnat (m * n) = hypreal_of_hypnat m * hypreal_of_hypnat n"
apply (rule_tac z=m in eq_Abs_star, rule_tac z=n in eq_Abs_star)
apply (simp add: hypreal_of_hypnat hypreal_mult hypnat_mult real_of_nat_mult)
done

lemma hypreal_of_hypnat_less_iff [simp]:
     "(hypreal_of_hypnat n < hypreal_of_hypnat m) = (n < m)"
apply (rule_tac z=m in eq_Abs_star, rule_tac z=n in eq_Abs_star)
apply (simp add: hypreal_of_hypnat hypreal_less hypnat_less)
done

lemma hypreal_of_hypnat_eq_zero_iff: "(hypreal_of_hypnat N = 0) = (N = 0)"
by (simp add: hypreal_of_hypnat_zero [symmetric])
declare hypreal_of_hypnat_eq_zero_iff [simp]

lemma hypreal_of_hypnat_ge_zero [simp]: "0 \<le> hypreal_of_hypnat n"
apply (rule_tac z=n in eq_Abs_star)
apply (simp add: hypreal_of_hypnat hypreal_zero_num hypreal_le)
done

lemma HNatInfinite_inverse_Infinitesimal [simp]:
     "n \<in> HNatInfinite ==> inverse (hypreal_of_hypnat n) \<in> Infinitesimal"
apply (rule_tac z=n in eq_Abs_star)
apply (auto simp add: hypreal_of_hypnat hypreal_inverse 
      HNatInfinite_FreeUltrafilterNat_iff Infinitesimal_FreeUltrafilterNat_iff2)
apply (rule bexI, rule_tac [2] lemma_starrel_refl, auto)
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

val starrel_iff = thm "starrel_iff";
(* val starrel_in_hypnat = thm "starrel_in_hypnat"; *)
val lemma_starrel_refl = thm "lemma_starrel_refl";
(* val hypnat_empty_not_mem = thm "hypnat_empty_not_mem"; *)
(* val Rep_star_nonempty = thm "Rep_star_nonempty"; *)
val eq_Abs_star = thm "eq_Abs_star";
val hypnat_add = thm "hypnat_add";
val hypnat_add_commute = thm "hypnat_add_commute";
val hypnat_add_assoc = thm "hypnat_add_assoc";
val hypnat_add_zero_left = thm "hypnat_add_zero_left";
(* val hypnat_minus_congruent2 = thm "hypnat_minus_congruent2"; *)
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
(* val hypnat_mult_congruent2 = thm "hypnat_mult_congruent2"; *)
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
val Rep_star_omega = thm "Rep_star_omega";
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
