(*  Title       : HOL/Real/Hyperreal/HyperDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Construction of Hyperreals Using Ultrafilters*}

theory HyperDef
(*imports Filter "../Real/Real"*)
imports StarClasses "../Real/Real"
uses ("fuf.ML")  (*Warning: file fuf.ML refers to the name Hyperdef!*)
begin

types hypreal = "real star"
(*
constdefs

  FreeUltrafilterNat   :: "nat set set"    ("\<U>")
    "FreeUltrafilterNat == (SOME U. freeultrafilter U)"

  hyprel :: "((nat=>real)*(nat=>real)) set"
    "hyprel == {p. \<exists>X Y. p = ((X::nat=>real),Y) &
                   {n::nat. X(n) = Y(n)} \<in> FreeUltrafilterNat}"

typedef hypreal = "UNIV//hyprel" 
    by (auto simp add: quotient_def) 

instance hypreal :: "{ord, zero, one, plus, times, minus, inverse}" ..

defs (overloaded)

  hypreal_zero_def:
  "0 == Abs_hypreal(hyprel``{%n. 0})"

  hypreal_one_def:
  "1 == Abs_hypreal(hyprel``{%n. 1})"

  hypreal_minus_def:
  "- P == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P). hyprel``{%n. - (X n)})"

  hypreal_diff_def:
  "x - y == x + -(y::hypreal)"

  hypreal_inverse_def:
  "inverse P == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P).
                    hyprel``{%n. if X n = 0 then 0 else inverse (X n)})"

  hypreal_divide_def:
  "P / Q::hypreal == P * inverse Q"
*)

lemma hypreal_zero_def: "0 == Abs_star(starrel``{%n. 0})"
by (simp only: star_zero_def star_of_def star_n_def)

lemma hypreal_one_def: "1 == Abs_star(starrel``{%n. 1})"
by (simp only: star_one_def star_of_def star_n_def)

lemma hypreal_diff_def: "x - y == x + -(y::hypreal)"
by (rule diff_def)

lemma hypreal_divide_def: "P / Q::hypreal == P * inverse Q"
by (rule divide_inverse [THEN eq_reflection])

constdefs

  hypreal_of_real  :: "real => hypreal"
(*  "hypreal_of_real r         == Abs_hypreal(hyprel``{%n. r})" *)
  "hypreal_of_real r == star_of r"

  omega   :: hypreal   -- {*an infinite number @{text "= [<1,2,3,...>]"} *}
(*  "omega == Abs_hypreal(hyprel``{%n. real (Suc n)})" *)
  "omega == star_n (%n. real (Suc n))"

  epsilon :: hypreal   -- {*an infinitesimal number @{text "= [<1,1/2,1/3,...>]"} *}
(*  "epsilon == Abs_hypreal(hyprel``{%n. inverse (real (Suc n))})" *)
  "epsilon == star_n (%n. inverse (real (Suc n)))"

syntax (xsymbols)
  omega   :: hypreal   ("\<omega>")
  epsilon :: hypreal   ("\<epsilon>")

syntax (HTML output)
  omega   :: hypreal   ("\<omega>")
  epsilon :: hypreal   ("\<epsilon>")

(*
defs (overloaded)

  hypreal_add_def:
  "P + Q == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P). \<Union>Y \<in> Rep_hypreal(Q).
                hyprel``{%n. X n + Y n})"

  hypreal_mult_def:
  "P * Q == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P). \<Union>Y \<in> Rep_hypreal(Q).
                hyprel``{%n. X n * Y n})"

  hypreal_le_def:
  "P \<le> (Q::hypreal) == \<exists>X Y. X \<in> Rep_hypreal(P) &
                               Y \<in> Rep_hypreal(Q) &
                               {n. X n \<le> Y n} \<in> FreeUltrafilterNat"

  hypreal_less_def: "(x < (y::hypreal)) == (x \<le> y & x \<noteq> y)"

  hrabs_def:  "abs (r::hypreal) == (if 0 \<le> r then r else -r)"
*)

subsection{*The Set of Naturals is not Finite*}

(*** based on James' proof that the set of naturals is not finite ***)
lemma finite_exhausts [rule_format]:
     "finite (A::nat set) --> (\<exists>n. \<forall>m. Suc (n + m) \<notin> A)"
apply (rule impI)
apply (erule_tac F = A in finite_induct)
apply (blast, erule exE)
apply (rule_tac x = "n + x" in exI)
apply (rule allI, erule_tac x = "x + m" in allE)
apply (auto simp add: add_ac)
done

lemma finite_not_covers [rule_format (no_asm)]:
     "finite (A :: nat set) --> (\<exists>n. n \<notin>A)"
by (rule impI, drule finite_exhausts, blast)

lemma not_finite_nat: "~ finite(UNIV:: nat set)"
by (fast dest!: finite_exhausts)


subsection{*Existence of Free Ultrafilter over the Naturals*}

text{*Also, proof of various properties of @{term FreeUltrafilterNat}: 
an arbitrary free ultrafilter*}

lemma FreeUltrafilterNat_Ex: "\<exists>U::nat set set. freeultrafilter U"
by (rule not_finite_nat [THEN freeultrafilter_Ex])

lemma FreeUltrafilterNat_mem: "freeultrafilter FreeUltrafilterNat"
apply (unfold FreeUltrafilterNat_def)
apply (rule someI_ex)
apply (rule FreeUltrafilterNat_Ex)
done

lemma UltrafilterNat_mem: "ultrafilter FreeUltrafilterNat"
by (rule FreeUltrafilterNat_mem [THEN freeultrafilter.ultrafilter])

lemma FilterNat_mem: "filter FreeUltrafilterNat"
by (rule FreeUltrafilterNat_mem [THEN freeultrafilter.filter])

lemma FreeUltrafilterNat_finite: "finite x ==> x \<notin> FreeUltrafilterNat"
by (rule FreeUltrafilterNat_mem [THEN freeultrafilter.finite])

lemma FreeUltrafilterNat_not_finite: "x \<in> FreeUltrafilterNat ==> ~ finite x"
by (rule FreeUltrafilterNat_mem [THEN freeultrafilter.infinite])

lemma FreeUltrafilterNat_empty [simp]: "{} \<notin> FreeUltrafilterNat"
by (rule FilterNat_mem [THEN filter.empty])

lemma FreeUltrafilterNat_Int:
     "[| X \<in> FreeUltrafilterNat;  Y \<in> FreeUltrafilterNat |]   
      ==> X Int Y \<in> FreeUltrafilterNat"
by (rule FilterNat_mem [THEN filter.Int])

lemma FreeUltrafilterNat_subset:
     "[| X \<in> FreeUltrafilterNat;  X \<subseteq> Y |]  
      ==> Y \<in> FreeUltrafilterNat"
by (rule FilterNat_mem [THEN filter.subset])

lemma FreeUltrafilterNat_Compl:
     "X \<in> FreeUltrafilterNat ==> -X \<notin> FreeUltrafilterNat"
apply (erule contrapos_pn)
apply (erule UltrafilterNat_mem [THEN ultrafilter.not_mem_iff, THEN iffD2])
done

lemma FreeUltrafilterNat_Compl_mem:
     "X\<notin> FreeUltrafilterNat ==> -X \<in> FreeUltrafilterNat"
by (rule UltrafilterNat_mem [THEN ultrafilter.not_mem_iff, THEN iffD1])

lemma FreeUltrafilterNat_Compl_iff1:
     "(X \<notin> FreeUltrafilterNat) = (-X \<in> FreeUltrafilterNat)"
by (rule UltrafilterNat_mem [THEN ultrafilter.not_mem_iff])

lemma FreeUltrafilterNat_Compl_iff2:
     "(X \<in> FreeUltrafilterNat) = (-X \<notin> FreeUltrafilterNat)"
by (auto simp add: FreeUltrafilterNat_Compl_iff1 [symmetric])

lemma cofinite_mem_FreeUltrafilterNat: "finite (-X) ==> X \<in> FreeUltrafilterNat"
apply (drule FreeUltrafilterNat_finite)  
apply (simp add: FreeUltrafilterNat_Compl_iff2 [symmetric])
done

lemma FreeUltrafilterNat_UNIV [iff]: "UNIV \<in> FreeUltrafilterNat"
by (rule FilterNat_mem [THEN filter.UNIV])

lemma FreeUltrafilterNat_Nat_set_refl [intro]:
     "{n. P(n) = P(n)} \<in> FreeUltrafilterNat"
by simp

lemma FreeUltrafilterNat_P: "{n::nat. P} \<in> FreeUltrafilterNat ==> P"
by (rule ccontr, simp)

lemma FreeUltrafilterNat_Ex_P: "{n. P(n)} \<in> FreeUltrafilterNat ==> \<exists>n. P(n)"
by (rule ccontr, simp)

lemma FreeUltrafilterNat_all: "\<forall>n. P(n) ==> {n. P(n)} \<in> FreeUltrafilterNat"
by (auto)


text{*Define and use Ultrafilter tactics*}
use "fuf.ML"

method_setup fuf = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            fuf_tac (local_clasimpset_of ctxt) 1)) *}
    "free ultrafilter tactic"

method_setup ultra = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            ultra_tac (local_clasimpset_of ctxt) 1)) *}
    "ultrafilter tactic"


text{*One further property of our free ultrafilter*}
lemma FreeUltrafilterNat_Un:
     "X Un Y \<in> FreeUltrafilterNat  
      ==> X \<in> FreeUltrafilterNat | Y \<in> FreeUltrafilterNat"
by (auto, ultra)


subsection{*Properties of @{term starrel}*}

text{*Proving that @{term starrel} is an equivalence relation*}

lemma starrel_iff: "((X,Y) \<in> starrel) = ({n. X n = Y n} \<in> FreeUltrafilterNat)"
by (simp add: starrel_def)

lemma starrel_refl: "(x,x) \<in> starrel"
by (simp add: starrel_def)

lemma starrel_sym [rule_format (no_asm)]: "(x,y) \<in> starrel --> (y,x) \<in> starrel"
by (simp add: starrel_def eq_commute)

lemma starrel_trans: 
      "[|(x,y) \<in> starrel; (y,z) \<in> starrel|] ==> (x,z) \<in> starrel"
by (simp add: starrel_def, ultra)

lemma equiv_starrel: "equiv UNIV starrel"
by (rule StarType.equiv_starrel)

(* (starrel `` {x} = starrel `` {y}) = ((x,y) \<in> starrel) *)
lemmas equiv_starrel_iff =
    eq_equiv_class_iff [OF equiv_starrel UNIV_I UNIV_I, simp] 

lemma starrel_in_hypreal [simp]: "starrel``{x}:star"
by (simp add: star_def starrel_def quotient_def, blast)

declare Abs_star_inject [simp] Abs_star_inverse [simp]
declare equiv_starrel [THEN eq_equiv_class_iff, simp]
declare starrel_iff [iff]

lemmas eq_starrelD = eq_equiv_class [OF _ equiv_starrel]

lemma lemma_starrel_refl [simp]: "x \<in> starrel `` {x}"
by (simp add: starrel_def)

lemma hypreal_empty_not_mem [simp]: "{} \<notin> star"
apply (simp add: star_def)
apply (auto elim!: quotientE equalityCE)
done

lemma Rep_hypreal_nonempty [simp]: "Rep_star x \<noteq> {}"
by (insert Rep_star [of x], auto)

subsection{*@{term hypreal_of_real}: 
            the Injection from @{typ real} to @{typ hypreal}*}

lemma inj_hypreal_of_real: "inj(hypreal_of_real)"
apply (rule inj_onI)
apply (simp add: hypreal_of_real_def split: split_if_asm)
done

lemma eq_Abs_star:
    "(!!x. z = Abs_star(starrel``{x}) ==> P) ==> P"
by (fold star_n_def, auto intro: star_cases)

(*
theorem hypreal_cases [case_names Abs_hypreal, cases type: hypreal]:
    "(!!x. z = star_n x ==> P) ==> P"
by (rule eq_Abs_hypreal [of z], blast)
*)

subsection{*Hyperreal Addition*}
(*
lemma hypreal_add_congruent2: 
    "congruent2 starrel starrel (%X Y. starrel``{%n. X n + Y n})"
by (simp add: congruent2_def, auto, ultra)
*)
lemma hypreal_add [unfolded star_n_def]: 
  "star_n X + star_n Y = star_n (%n. X n + Y n)"
by (simp add: star_add_def Ifun2_of_def star_of_def Ifun_star_n)

lemma hypreal_add_commute: "(z::hypreal) + w = w + z"
by (rule add_commute)

lemma hypreal_add_assoc: "((z1::hypreal) + z2) + z3 = z1 + (z2 + z3)"
by (rule add_assoc)

lemma hypreal_add_zero_left: "(0::hypreal) + z = z"
by (rule comm_monoid_add_class.add_0)

(*instance hypreal :: comm_monoid_add
  by intro_classes
    (assumption | 
      rule hypreal_add_commute hypreal_add_assoc hypreal_add_zero_left)+*)

lemma hypreal_add_zero_right [simp]: "z + (0::hypreal) = z"
by (rule OrderedGroup.add_0_right)


subsection{*Additive inverse on @{typ hypreal}*}
(*
lemma hypreal_minus_congruent: "(%X. starrel``{%n. - (X n)}) respects starrel"
by (force simp add: congruent_def)
*)
lemma hypreal_minus [unfolded star_n_def]: 
   "- star_n X = star_n (%n. -(X n))"
by (simp add: star_minus_def Ifun_of_def star_of_def Ifun_star_n)

lemma hypreal_diff [unfolded star_n_def]:
     "star_n X - star_n Y = star_n (%n. X n - Y n)"
by (simp add: star_diff_def Ifun2_of_def star_of_def Ifun_star_n)

lemma hypreal_add_minus [simp]: "z + -z = (0::hypreal)"
by (rule right_minus)

lemma hypreal_add_minus_left: "-z + z = (0::hypreal)"
by (rule left_minus)


subsection{*Hyperreal Multiplication*}
(*
lemma hypreal_mult_congruent2: 
    "congruent2 starrel starrel (%X Y. starrel``{%n. X n * Y n})"
by (simp add: congruent2_def, auto, ultra)
*)

lemma hypreal_mult [unfolded star_n_def]: 
  "star_n X * star_n Y = star_n (%n. X n * Y n)"
by (simp add: star_mult_def Ifun2_of_def star_of_def Ifun_star_n)

lemma hypreal_mult_commute: "(z::hypreal) * w = w * z"
by (rule mult_commute)

lemma hypreal_mult_assoc: "((z1::hypreal) * z2) * z3 = z1 * (z2 * z3)"
by (rule mult_assoc)

lemma hypreal_mult_1: "(1::hypreal) * z = z"
by (rule mult_1_left)

lemma hypreal_add_mult_distrib:
     "((z1::hypreal) + z2) * w = (z1 * w) + (z2 * w)"
by (rule left_distrib)

text{*one and zero are distinct*}
lemma hypreal_zero_not_eq_one: "0 \<noteq> (1::hypreal)"
by (rule zero_neq_one)


subsection{*Multiplicative Inverse on @{typ hypreal} *}
(*
lemma hypreal_inverse_congruent: 
  "(%X. starrel``{%n. if X n = 0 then 0 else inverse(X n)}) respects starrel"
by (auto simp add: congruent_def, ultra)
*)
lemma hypreal_inverse [unfolded star_n_def]: 
      "inverse (star_n X) = star_n (%n. if X n = (0::real) then 0 else inverse(X n))"
apply (simp add: star_inverse_def Ifun_of_def star_of_def Ifun_star_n)
apply (rule_tac f=star_n in arg_cong)
apply (rule ext)
apply simp
done

lemma hypreal_mult_inverse: 
     "x \<noteq> 0 ==> x*inverse(x) = (1::hypreal)"
by (rule right_inverse)

lemma hypreal_mult_inverse_left:
     "x \<noteq> 0 ==> inverse(x)*x = (1::hypreal)"
by (rule left_inverse)

(*
instance hypreal :: field
proof
  fix x y z :: hypreal
  show "- x + x = 0" by (simp add: hypreal_add_minus_left)
  show "x - y = x + (-y)" by (simp add: hypreal_diff_def)
  show "(x * y) * z = x * (y * z)" by (rule hypreal_mult_assoc)
  show "x * y = y * x" by (rule hypreal_mult_commute)
  show "1 * x = x" by (simp add: hypreal_mult_1)
  show "(x + y) * z = x * z + y * z" by (simp add: hypreal_add_mult_distrib)
  show "0 \<noteq> (1::hypreal)" by (rule hypreal_zero_not_eq_one)
  show "x \<noteq> 0 ==> inverse x * x = 1" by (simp add: hypreal_mult_inverse_left)
  show "x / y = x * inverse y" by (simp add: hypreal_divide_def)
qed


instance hypreal :: division_by_zero
proof
  show "inverse 0 = (0::hypreal)" 
    by (simp add: hypreal_inverse hypreal_zero_def)
qed
*)

subsection{*Properties of The @{text "\<le>"} Relation*}

lemma hypreal_le [unfolded star_n_def]: 
      "star_n X \<le> star_n Y =  
       ({n. X n \<le> Y n} \<in> FreeUltrafilterNat)"
by (simp add: star_le_def Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)

lemma hypreal_le_refl: "w \<le> (w::hypreal)"
by (rule order_refl)

lemma hypreal_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::hypreal)"
by (rule order_trans)

lemma hypreal_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::hypreal)"
by (rule order_antisym)

(* Axiom 'order_less_le' of class 'order': *)
lemma hypreal_less_le: "((w::hypreal) < z) = (w \<le> z & w \<noteq> z)"
by (rule order_less_le)

(*
instance hypreal :: order
  by intro_classes
    (assumption |
      rule hypreal_le_refl hypreal_le_trans hypreal_le_anti_sym hypreal_less_le)+
*)

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma hypreal_le_linear: "(z::hypreal) \<le> w | w \<le> z"
by (rule linorder_linear)

(*
instance hypreal :: linorder 
  by intro_classes (rule hypreal_le_linear)
*)

lemma hypreal_not_refl2: "!!(x::hypreal). x < y ==> x \<noteq> y"
by (auto)

lemma hypreal_add_left_mono: "x \<le> y ==> z + x \<le> z + (y::hypreal)"
by (rule add_left_mono)

lemma hypreal_mult_less_mono2: "[| (0::hypreal)<z; x<y |] ==> z*x<z*y"
by (rule mult_strict_left_mono)


subsection{*The Hyperreals Form an Ordered Field*}

(*
instance hypreal :: ordered_field
proof
  fix x y z :: hypreal
  show "x \<le> y ==> z + x \<le> z + y" 
    by (rule hypreal_add_left_mono)
  show "x < y ==> 0 < z ==> z * x < z * y" 
    by (simp add: hypreal_mult_less_mono2)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)"
    by (auto dest: order_le_less_trans simp add: hrabs_def linorder_not_le)
qed
*)

lemma hypreal_eq_minus_iff: "((x::hypreal) = y) = (x + - y = 0)"
by auto

lemma hypreal_mult_left_cancel: "(c::hypreal) \<noteq> 0 ==> (c*a=c*b) = (a=b)"
by auto
    
lemma hypreal_mult_right_cancel: "(c::hypreal) \<noteq> 0 ==> (a*c=b*c) = (a=b)"
by auto


subsection{*The Embedding @{term hypreal_of_real} Preserves Field and 
      Order Properties*}

lemma hypreal_of_real_add [simp]: 
     "hypreal_of_real (w + z) = hypreal_of_real w + hypreal_of_real z"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_minus [simp]:
     "hypreal_of_real (-r) = - hypreal_of_real  r"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_diff [simp]: 
     "hypreal_of_real (w - z) = hypreal_of_real w - hypreal_of_real z"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_mult [simp]: 
     "hypreal_of_real (w * z) = hypreal_of_real w * hypreal_of_real z"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_one [simp]: "hypreal_of_real 1 = (1::hypreal)"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_zero [simp]: "hypreal_of_real 0 = 0"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_le_iff [simp]: 
     "(hypreal_of_real w \<le> hypreal_of_real z) = (w \<le> z)"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_less_iff [simp]: 
     "(hypreal_of_real w < hypreal_of_real z) = (w < z)"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_eq_iff [simp]:
     "(hypreal_of_real w = hypreal_of_real z) = (w = z)"
by (simp add: hypreal_of_real_def)

text{*As above, for 0*}

declare hypreal_of_real_less_iff [of 0, simplified, simp]
declare hypreal_of_real_le_iff   [of 0, simplified, simp]
declare hypreal_of_real_eq_iff   [of 0, simplified, simp]

declare hypreal_of_real_less_iff [of _ 0, simplified, simp]
declare hypreal_of_real_le_iff   [of _ 0, simplified, simp]
declare hypreal_of_real_eq_iff   [of _ 0, simplified, simp]

text{*As above, for 1*}

declare hypreal_of_real_less_iff [of 1, simplified, simp]
declare hypreal_of_real_le_iff   [of 1, simplified, simp]
declare hypreal_of_real_eq_iff   [of 1, simplified, simp]

declare hypreal_of_real_less_iff [of _ 1, simplified, simp]
declare hypreal_of_real_le_iff   [of _ 1, simplified, simp]
declare hypreal_of_real_eq_iff   [of _ 1, simplified, simp]

lemma hypreal_of_real_inverse [simp]:
     "hypreal_of_real (inverse r) = inverse (hypreal_of_real r)"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_divide [simp]:
     "hypreal_of_real (w / z) = hypreal_of_real w / hypreal_of_real z"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_of_nat [simp]: "hypreal_of_real (of_nat n) = of_nat n"
by (simp add: hypreal_of_real_def)

lemma hypreal_of_real_of_int [simp]:  "hypreal_of_real (of_int z) = of_int z"
by (simp add: hypreal_of_real_def)


subsection{*Misc Others*}

lemma hypreal_less [unfolded star_n_def]: 
      "star_n X < star_n Y = ({n. X n < Y n} \<in> FreeUltrafilterNat)"
by (simp add: star_less_def Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)

lemma hypreal_zero_num [unfolded star_n_def]: "0 = star_n (%n. 0)"
by (simp add: star_zero_def star_of_def)

lemma hypreal_one_num [unfolded star_n_def]: "1 = star_n (%n. 1)"
by (simp add: star_one_def star_of_def)

lemma hypreal_omega_gt_zero [simp]: "0 < omega"
apply (simp only: omega_def star_zero_def star_less_def star_of_def)
apply (simp add: Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)
done

lemma hypreal_hrabs [unfolded star_n_def]:
     "abs (star_n X) = star_n (%n. abs (X n))"
by (simp add: star_abs_def Ifun_of_def star_of_def Ifun_star_n)

subsection{*Existence of Infinite Hyperreal Number*}
(*
lemma Rep_hypreal_omega: "Rep_hypreal(omega) \<in> hypreal"
by (simp add: omega_def)
*)
text{*Existence of infinite number not corresponding to any real number.
Use assumption that member @{term FreeUltrafilterNat} is not finite.*}


text{*A few lemmas first*}

lemma lemma_omega_empty_singleton_disj: "{n::nat. x = real n} = {} |  
      (\<exists>y. {n::nat. x = real n} = {y})"
by force

lemma lemma_finite_omega_set: "finite {n::nat. x = real n}"
by (cut_tac x = x in lemma_omega_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_omega: 
      "~ (\<exists>x. hypreal_of_real x = omega)"
apply (simp add: omega_def hypreal_of_real_def)
apply (simp add: star_of_def star_n_eq_iff)
apply (auto simp add: real_of_nat_Suc diff_eq_eq [symmetric] 
            lemma_finite_omega_set [THEN FreeUltrafilterNat_finite])
done

lemma hypreal_of_real_not_eq_omega: "hypreal_of_real x \<noteq> omega"
by (insert not_ex_hypreal_of_real_eq_omega, auto)

text{*Existence of infinitesimal number also not corresponding to any
 real number*}

lemma lemma_epsilon_empty_singleton_disj:
     "{n::nat. x = inverse(real(Suc n))} = {} |  
      (\<exists>y. {n::nat. x = inverse(real(Suc n))} = {y})"
by auto

lemma lemma_finite_epsilon_set: "finite {n. x = inverse(real(Suc n))}"
by (cut_tac x = x in lemma_epsilon_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_epsilon: "~ (\<exists>x. hypreal_of_real x = epsilon)"
by (auto simp add: epsilon_def hypreal_of_real_def 
                   star_of_def star_n_eq_iff
                   lemma_finite_epsilon_set [THEN FreeUltrafilterNat_finite])

lemma hypreal_of_real_not_eq_epsilon: "hypreal_of_real x \<noteq> epsilon"
by (insert not_ex_hypreal_of_real_eq_epsilon, auto)

lemma hypreal_epsilon_not_zero: "epsilon \<noteq> 0"
by (simp add: epsilon_def star_zero_def star_of_def star_n_eq_iff
         del: star_of_zero)

lemma hypreal_epsilon_inverse_omega: "epsilon = inverse(omega)"
apply (simp add: epsilon_def omega_def star_inverse_def)
apply (simp add: Ifun_of_def star_of_def Ifun_star_n)
done


ML
{*
(* val hrabs_def = thm "hrabs_def"; *)
(* val hypreal_hrabs = thm "hypreal_hrabs"; *)

val hypreal_zero_def = thm "hypreal_zero_def";
(* val hypreal_one_def = thm "hypreal_one_def"; *)
(* val hypreal_minus_def = thm "hypreal_minus_def"; *)
(* val hypreal_diff_def = thm "hypreal_diff_def"; *)
(* val hypreal_inverse_def = thm "hypreal_inverse_def"; *)
(* val hypreal_divide_def = thm "hypreal_divide_def"; *)
val hypreal_of_real_def = thm "hypreal_of_real_def";
val omega_def = thm "omega_def";
val epsilon_def = thm "epsilon_def";
(* val hypreal_add_def = thm "hypreal_add_def"; *)
(* val hypreal_mult_def = thm "hypreal_mult_def"; *)
(* val hypreal_less_def = thm "hypreal_less_def"; *)
(* val hypreal_le_def = thm "hypreal_le_def"; *)

val finite_exhausts = thm "finite_exhausts";
val finite_not_covers = thm "finite_not_covers";
val not_finite_nat = thm "not_finite_nat";
val FreeUltrafilterNat_Ex = thm "FreeUltrafilterNat_Ex";
val FreeUltrafilterNat_mem = thm "FreeUltrafilterNat_mem";
val FreeUltrafilterNat_finite = thm "FreeUltrafilterNat_finite";
val FreeUltrafilterNat_not_finite = thm "FreeUltrafilterNat_not_finite";
val FreeUltrafilterNat_empty = thm "FreeUltrafilterNat_empty";
val FreeUltrafilterNat_Int = thm "FreeUltrafilterNat_Int";
val FreeUltrafilterNat_subset = thm "FreeUltrafilterNat_subset";
val FreeUltrafilterNat_Compl = thm "FreeUltrafilterNat_Compl";
val FreeUltrafilterNat_Compl_mem = thm "FreeUltrafilterNat_Compl_mem";
val FreeUltrafilterNat_Compl_iff1 = thm "FreeUltrafilterNat_Compl_iff1";
val FreeUltrafilterNat_Compl_iff2 = thm "FreeUltrafilterNat_Compl_iff2";
val FreeUltrafilterNat_UNIV = thm "FreeUltrafilterNat_UNIV";
val FreeUltrafilterNat_Nat_set_refl = thm "FreeUltrafilterNat_Nat_set_refl";
val FreeUltrafilterNat_P = thm "FreeUltrafilterNat_P";
val FreeUltrafilterNat_Ex_P = thm "FreeUltrafilterNat_Ex_P";
val FreeUltrafilterNat_all = thm "FreeUltrafilterNat_all";
val FreeUltrafilterNat_Un = thm "FreeUltrafilterNat_Un";
val starrel_iff = thm "starrel_iff";
val starrel_in_hypreal = thm "starrel_in_hypreal";
val Abs_star_inverse = thm "Abs_star_inverse";
val lemma_starrel_refl = thm "lemma_starrel_refl";
val hypreal_empty_not_mem = thm "hypreal_empty_not_mem";
val Rep_hypreal_nonempty = thm "Rep_hypreal_nonempty";
val inj_hypreal_of_real = thm "inj_hypreal_of_real";
val eq_Abs_star = thm "eq_Abs_star";
(* val hypreal_minus_congruent = thm "hypreal_minus_congruent"; *)
val hypreal_minus = thm "hypreal_minus";
val hypreal_add = thm "hypreal_add";
val hypreal_diff = thm "hypreal_diff";
val hypreal_add_commute = thm "hypreal_add_commute";
val hypreal_add_assoc = thm "hypreal_add_assoc";
val hypreal_add_zero_left = thm "hypreal_add_zero_left";
val hypreal_add_zero_right = thm "hypreal_add_zero_right";
val hypreal_add_minus = thm "hypreal_add_minus";
val hypreal_add_minus_left = thm "hypreal_add_minus_left";
val hypreal_mult = thm "hypreal_mult";
val hypreal_mult_commute = thm "hypreal_mult_commute";
val hypreal_mult_assoc = thm "hypreal_mult_assoc";
val hypreal_mult_1 = thm "hypreal_mult_1";
val hypreal_zero_not_eq_one = thm "hypreal_zero_not_eq_one";
(* val hypreal_inverse_congruent = thm "hypreal_inverse_congruent"; *)
val hypreal_inverse = thm "hypreal_inverse";
val hypreal_mult_inverse = thm "hypreal_mult_inverse";
val hypreal_mult_inverse_left = thm "hypreal_mult_inverse_left";
val hypreal_mult_left_cancel = thm "hypreal_mult_left_cancel";
val hypreal_mult_right_cancel = thm "hypreal_mult_right_cancel";
val hypreal_not_refl2 = thm "hypreal_not_refl2";
val hypreal_less = thm "hypreal_less";
val hypreal_eq_minus_iff = thm "hypreal_eq_minus_iff";
val hypreal_le = thm "hypreal_le";
val hypreal_le_refl = thm "hypreal_le_refl";
val hypreal_le_linear = thm "hypreal_le_linear";
val hypreal_le_trans = thm "hypreal_le_trans";
val hypreal_le_anti_sym = thm "hypreal_le_anti_sym";
val hypreal_less_le = thm "hypreal_less_le";
val hypreal_of_real_add = thm "hypreal_of_real_add";
val hypreal_of_real_mult = thm "hypreal_of_real_mult";
val hypreal_of_real_less_iff = thm "hypreal_of_real_less_iff";
val hypreal_of_real_le_iff = thm "hypreal_of_real_le_iff";
val hypreal_of_real_eq_iff = thm "hypreal_of_real_eq_iff";
val hypreal_of_real_minus = thm "hypreal_of_real_minus";
val hypreal_of_real_one = thm "hypreal_of_real_one";
val hypreal_of_real_zero = thm "hypreal_of_real_zero";
val hypreal_of_real_inverse = thm "hypreal_of_real_inverse";
val hypreal_of_real_divide = thm "hypreal_of_real_divide";
val hypreal_zero_num = thm "hypreal_zero_num";
val hypreal_one_num = thm "hypreal_one_num";
val hypreal_omega_gt_zero = thm "hypreal_omega_gt_zero";

(* val Rep_hypreal_omega = thm"Rep_hypreal_omega"; *)
val lemma_omega_empty_singleton_disj = thm"lemma_omega_empty_singleton_disj";
val lemma_finite_omega_set = thm"lemma_finite_omega_set";
val not_ex_hypreal_of_real_eq_omega = thm"not_ex_hypreal_of_real_eq_omega";
val hypreal_of_real_not_eq_omega = thm"hypreal_of_real_not_eq_omega";
val not_ex_hypreal_of_real_eq_epsilon = thm"not_ex_hypreal_of_real_eq_epsilon";
val hypreal_of_real_not_eq_epsilon = thm"hypreal_of_real_not_eq_epsilon";
val hypreal_epsilon_not_zero = thm"hypreal_epsilon_not_zero";
val hypreal_epsilon_inverse_omega = thm"hypreal_epsilon_inverse_omega";
*}

end
