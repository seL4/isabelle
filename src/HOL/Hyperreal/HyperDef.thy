(*  Title       : HOL/Real/Hyperreal/HyperDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Construction of hyperreals using ultrafilters
*)

theory HyperDef = Filter + Real
files ("fuf.ML"):  (*Warning: file fuf.ML refers to the name Hyperdef!*)


constdefs

  FreeUltrafilterNat   :: "nat set set"    ("\\<U>")
    "FreeUltrafilterNat == (SOME U. U \<in> FreeUltrafilter (UNIV:: nat set))"

  hyprel :: "((nat=>real)*(nat=>real)) set"
    "hyprel == {p. \<exists>X Y. p = ((X::nat=>real),Y) &
                   {n::nat. X(n) = Y(n)}: FreeUltrafilterNat}"

typedef hypreal = "UNIV//hyprel" 
    by (auto simp add: quotient_def) 

instance hypreal :: ord ..
instance hypreal :: zero ..
instance hypreal :: one ..
instance hypreal :: plus ..
instance hypreal :: times ..
instance hypreal :: minus ..
instance hypreal :: inverse ..


defs (overloaded)

  hypreal_zero_def:
  "0 == Abs_hypreal(hyprel``{%n::nat. (0::real)})"

  hypreal_one_def:
  "1 == Abs_hypreal(hyprel``{%n::nat. (1::real)})"

  hypreal_minus_def:
  "- P == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P). hyprel``{%n::nat. - (X n)})"

  hypreal_diff_def:
  "x - y == x + -(y::hypreal)"

  hypreal_inverse_def:
  "inverse P == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P).
                    hyprel``{%n. if X n = 0 then 0 else inverse (X n)})"

  hypreal_divide_def:
  "P / Q::hypreal == P * inverse Q"

constdefs

  hypreal_of_real  :: "real => hypreal"
  "hypreal_of_real r         == Abs_hypreal(hyprel``{%n::nat. r})"

  omega   :: hypreal   (*an infinite number = [<1,2,3,...>] *)
  "omega == Abs_hypreal(hyprel``{%n::nat. real (Suc n)})"

  epsilon :: hypreal   (*an infinitesimal number = [<1,1/2,1/3,...>] *)
  "epsilon == Abs_hypreal(hyprel``{%n::nat. inverse (real (Suc n))})"

syntax (xsymbols)
  omega   :: hypreal   ("\<omega>")
  epsilon :: hypreal   ("\<epsilon>")


defs

  hypreal_add_def:
  "P + Q == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P). \<Union>Y \<in> Rep_hypreal(Q).
                hyprel``{%n::nat. X n + Y n})"

  hypreal_mult_def:
  "P * Q == Abs_hypreal(\<Union>X \<in> Rep_hypreal(P). \<Union>Y \<in> Rep_hypreal(Q).
                hyprel``{%n::nat. X n * Y n})"

  hypreal_less_def:
  "P < (Q::hypreal) == \<exists>X Y. X \<in> Rep_hypreal(P) &
                               Y \<in> Rep_hypreal(Q) &
                               {n::nat. X n < Y n} \<in> FreeUltrafilterNat"
  hypreal_le_def:
  "P <= (Q::hypreal) == ~(Q < P)"

  hrabs_def:  "abs (r::hypreal) == (if 0 \<le> r then r else -r)"


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

lemma FreeUltrafilterNat_Ex: "\<exists>U. U: FreeUltrafilter (UNIV::nat set)"
by (rule not_finite_nat [THEN FreeUltrafilter_Ex])

lemma FreeUltrafilterNat_mem [simp]: 
     "FreeUltrafilterNat: FreeUltrafilter(UNIV:: nat set)"
apply (unfold FreeUltrafilterNat_def)
apply (rule FreeUltrafilterNat_Ex [THEN exE])
apply (rule someI2, assumption+)
done

lemma FreeUltrafilterNat_finite: "finite x ==> x \<notin> FreeUltrafilterNat"
apply (unfold FreeUltrafilterNat_def)
apply (rule FreeUltrafilterNat_Ex [THEN exE])
apply (rule someI2, assumption)
apply (blast dest: mem_FreeUltrafiltersetD1)
done

lemma FreeUltrafilterNat_not_finite: "x: FreeUltrafilterNat ==> ~ finite x"
by (blast dest: FreeUltrafilterNat_finite)

lemma FreeUltrafilterNat_empty [simp]: "{} \<notin> FreeUltrafilterNat"
apply (unfold FreeUltrafilterNat_def)
apply (rule FreeUltrafilterNat_Ex [THEN exE])
apply (rule someI2, assumption)
apply (blast dest: FreeUltrafilter_Ultrafilter Ultrafilter_Filter 
                   Filter_empty_not_mem)
done

lemma FreeUltrafilterNat_Int:
     "[| X: FreeUltrafilterNat;  Y: FreeUltrafilterNat |]   
      ==> X Int Y \<in> FreeUltrafilterNat"
apply (cut_tac FreeUltrafilterNat_mem)
apply (blast dest: FreeUltrafilter_Ultrafilter Ultrafilter_Filter mem_FiltersetD1)
done

lemma FreeUltrafilterNat_subset:
     "[| X: FreeUltrafilterNat;  X <= Y |]  
      ==> Y \<in> FreeUltrafilterNat"
apply (cut_tac FreeUltrafilterNat_mem)
apply (blast dest: FreeUltrafilter_Ultrafilter Ultrafilter_Filter mem_FiltersetD2)
done

lemma FreeUltrafilterNat_Compl:
     "X: FreeUltrafilterNat ==> -X \<notin> FreeUltrafilterNat"
apply safe
apply (drule FreeUltrafilterNat_Int, assumption, auto)
done

lemma FreeUltrafilterNat_Compl_mem:
     "X\<notin> FreeUltrafilterNat ==> -X \<in> FreeUltrafilterNat"
apply (cut_tac FreeUltrafilterNat_mem [THEN FreeUltrafilter_iff [THEN iffD1]])
apply (safe, drule_tac x = X in bspec)
apply (auto simp add: UNIV_diff_Compl)
done

lemma FreeUltrafilterNat_Compl_iff1:
     "(X \<notin> FreeUltrafilterNat) = (-X: FreeUltrafilterNat)"
by (blast dest: FreeUltrafilterNat_Compl FreeUltrafilterNat_Compl_mem)

lemma FreeUltrafilterNat_Compl_iff2:
     "(X: FreeUltrafilterNat) = (-X \<notin> FreeUltrafilterNat)"
by (auto simp add: FreeUltrafilterNat_Compl_iff1 [symmetric])

lemma FreeUltrafilterNat_UNIV [simp]: "(UNIV::nat set) \<in> FreeUltrafilterNat"
by (rule FreeUltrafilterNat_mem [THEN FreeUltrafilter_Ultrafilter, THEN Ultrafilter_Filter, THEN mem_FiltersetD4])

lemma FreeUltrafilterNat_Nat_set [simp]: "UNIV \<in> FreeUltrafilterNat"
by auto

lemma FreeUltrafilterNat_Nat_set_refl [intro]:
     "{n. P(n) = P(n)} \<in> FreeUltrafilterNat"
by simp

lemma FreeUltrafilterNat_P: "{n::nat. P} \<in> FreeUltrafilterNat ==> P"
by (rule ccontr, simp)

lemma FreeUltrafilterNat_Ex_P: "{n. P(n)} \<in> FreeUltrafilterNat ==> \<exists>n. P(n)"
by (rule ccontr, simp)

lemma FreeUltrafilterNat_all: "\<forall>n. P(n) ==> {n. P(n)} \<in> FreeUltrafilterNat"
by (auto intro: FreeUltrafilterNat_Nat_set)


text{*Define and use Ultrafilter tactics*}
use "fuf.ML"

method_setup fuf = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            fuf_tac (Classical.get_local_claset ctxt,
                     Simplifier.get_local_simpset ctxt) 1)) *}
    "free ultrafilter tactic"

method_setup ultra = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            ultra_tac (Classical.get_local_claset ctxt,
                       Simplifier.get_local_simpset ctxt) 1)) *}
    "ultrafilter tactic"


text{*One further property of our free ultrafilter*}
lemma FreeUltrafilterNat_Un:
     "X Un Y: FreeUltrafilterNat  
      ==> X: FreeUltrafilterNat | Y: FreeUltrafilterNat"
apply auto
apply ultra
done


subsection{*Properties of @{term hyprel}*}

text{*Proving that @{term hyprel} is an equivalence relation*}

lemma hyprel_iff: "((X,Y): hyprel) = ({n. X n = Y n}: FreeUltrafilterNat)"
by (unfold hyprel_def, fast)

lemma hyprel_refl: "(x,x): hyprel"
apply (unfold hyprel_def)
apply (auto simp add: FreeUltrafilterNat_Nat_set)
done

lemma hyprel_sym [rule_format (no_asm)]: "(x,y): hyprel --> (y,x):hyprel"
by (simp add: hyprel_def eq_commute)

lemma hyprel_trans: 
      "[|(x,y): hyprel; (y,z):hyprel|] ==> (x,z):hyprel"
apply (unfold hyprel_def, auto, ultra)
done

lemma equiv_hyprel: "equiv UNIV hyprel"
apply (simp add: equiv_def refl_def sym_def trans_def hyprel_refl)
apply (blast intro: hyprel_sym hyprel_trans) 
done

(* (hyprel `` {x} = hyprel `` {y}) = ((x,y) \<in> hyprel) *)
lemmas equiv_hyprel_iff =
    eq_equiv_class_iff [OF equiv_hyprel UNIV_I UNIV_I, simp] 

lemma hyprel_in_hypreal [simp]: "hyprel``{x}:hypreal"
by (unfold hypreal_def hyprel_def quotient_def, blast)

lemma inj_on_Abs_hypreal: "inj_on Abs_hypreal hypreal"
apply (rule inj_on_inverseI)
apply (erule Abs_hypreal_inverse)
done

declare inj_on_Abs_hypreal [THEN inj_on_iff, simp] 
        Abs_hypreal_inverse [simp]

declare equiv_hyprel [THEN eq_equiv_class_iff, simp]

declare hyprel_iff [iff]

lemmas eq_hyprelD = eq_equiv_class [OF _ equiv_hyprel]

lemma inj_Rep_hypreal: "inj(Rep_hypreal)"
apply (rule inj_on_inverseI)
apply (rule Rep_hypreal_inverse)
done

lemma lemma_hyprel_refl [simp]: "x \<in> hyprel `` {x}"
apply (unfold hyprel_def, safe)
apply (auto intro!: FreeUltrafilterNat_Nat_set)
done

lemma hypreal_empty_not_mem [simp]: "{} \<notin> hypreal"
apply (unfold hypreal_def)
apply (auto elim!: quotientE equalityCE)
done

lemma Rep_hypreal_nonempty [simp]: "Rep_hypreal x \<noteq> {}"
by (cut_tac x = x in Rep_hypreal, auto)


subsection{*@{term hypreal_of_real}: 
            the Injection from @{typ real} to @{typ hypreal}*}

lemma inj_hypreal_of_real: "inj(hypreal_of_real)"
apply (rule inj_onI)
apply (unfold hypreal_of_real_def)
apply (drule inj_on_Abs_hypreal [THEN inj_onD])
apply (rule hyprel_in_hypreal)+
apply (drule eq_equiv_class)
apply (rule equiv_hyprel)
apply (simp_all add: split: split_if_asm) 
done

lemma eq_Abs_hypreal:
    "(!!x y. z = Abs_hypreal(hyprel``{x}) ==> P) ==> P"
apply (rule_tac x1=z in Rep_hypreal [unfolded hypreal_def, THEN quotientE])
apply (drule_tac f = Abs_hypreal in arg_cong)
apply (force simp add: Rep_hypreal_inverse)
done


subsection{*Hyperreal Addition*}

lemma hypreal_add_congruent2: 
    "congruent2 hyprel (%X Y. hyprel``{%n. X n + Y n})"
apply (unfold congruent2_def, auto, ultra)
done

lemma hypreal_add: 
  "Abs_hypreal(hyprel``{%n. X n}) + Abs_hypreal(hyprel``{%n. Y n}) =  
   Abs_hypreal(hyprel``{%n. X n + Y n})"
apply (unfold hypreal_add_def)
apply (simp add: UN_equiv_class2 [OF equiv_hyprel hypreal_add_congruent2])
done

lemma hypreal_add_commute: "(z::hypreal) + w = w + z"
apply (rule_tac z = z in eq_Abs_hypreal)
apply (rule_tac z = w in eq_Abs_hypreal)
apply (simp add: add_ac hypreal_add)
done

lemma hypreal_add_assoc: "((z1::hypreal) + z2) + z3 = z1 + (z2 + z3)"
apply (rule_tac z = z1 in eq_Abs_hypreal)
apply (rule_tac z = z2 in eq_Abs_hypreal)
apply (rule_tac z = z3 in eq_Abs_hypreal)
apply (simp add: hypreal_add real_add_assoc)
done

lemma hypreal_add_zero_left: "(0::hypreal) + z = z"
apply (unfold hypreal_zero_def)
apply (rule_tac z = z in eq_Abs_hypreal)
apply (simp add: hypreal_add)
done

instance hypreal :: plus_ac0
  by (intro_classes,
      (assumption | 
       rule hypreal_add_commute hypreal_add_assoc hypreal_add_zero_left)+)

lemma hypreal_add_zero_right [simp]: "z + (0::hypreal) = z"
by (simp add: hypreal_add_zero_left hypreal_add_commute)


subsection{*Additive inverse on @{typ hypreal}*}

lemma hypreal_minus_congruent: 
  "congruent hyprel (%X. hyprel``{%n. - (X n)})"
by (force simp add: congruent_def)

lemma hypreal_minus: 
   "- (Abs_hypreal(hyprel``{%n. X n})) = Abs_hypreal(hyprel `` {%n. -(X n)})"
apply (unfold hypreal_minus_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (simp add: hyprel_in_hypreal [THEN Abs_hypreal_inverse] 
               UN_equiv_class [OF equiv_hyprel hypreal_minus_congruent])
done

lemma hypreal_diff:
     "Abs_hypreal(hyprel``{%n. X n}) - Abs_hypreal(hyprel``{%n. Y n}) =  
      Abs_hypreal(hyprel``{%n. X n - Y n})"
apply (simp add: hypreal_diff_def hypreal_minus hypreal_add)
done

lemma hypreal_add_minus [simp]: "z + -z = (0::hypreal)"
apply (unfold hypreal_zero_def)
apply (rule_tac z = z in eq_Abs_hypreal)
apply (simp add: hypreal_minus hypreal_add)
done

lemma hypreal_add_minus_left: "-z + z = (0::hypreal)"
by (simp add: hypreal_add_commute hypreal_add_minus)


subsection{*Hyperreal Multiplication*}

lemma hypreal_mult_congruent2: 
    "congruent2 hyprel (%X Y. hyprel``{%n. X n * Y n})"
apply (unfold congruent2_def, auto, ultra)
done

lemma hypreal_mult: 
  "Abs_hypreal(hyprel``{%n. X n}) * Abs_hypreal(hyprel``{%n. Y n}) =  
   Abs_hypreal(hyprel``{%n. X n * Y n})"
apply (unfold hypreal_mult_def)
apply (simp add: UN_equiv_class2 [OF equiv_hyprel hypreal_mult_congruent2])
done

lemma hypreal_mult_commute: "(z::hypreal) * w = w * z"
apply (rule_tac z = z in eq_Abs_hypreal)
apply (rule_tac z = w in eq_Abs_hypreal)
apply (simp add: hypreal_mult mult_ac)
done

lemma hypreal_mult_assoc: "((z1::hypreal) * z2) * z3 = z1 * (z2 * z3)"
apply (rule_tac z = z1 in eq_Abs_hypreal)
apply (rule_tac z = z2 in eq_Abs_hypreal)
apply (rule_tac z = z3 in eq_Abs_hypreal)
apply (simp add: hypreal_mult mult_assoc)
done

lemma hypreal_mult_1: "(1::hypreal) * z = z"
apply (unfold hypreal_one_def)
apply (rule_tac z = z in eq_Abs_hypreal)
apply (simp add: hypreal_mult)
done

lemma hypreal_add_mult_distrib:
     "((z1::hypreal) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule_tac z = z1 in eq_Abs_hypreal)
apply (rule_tac z = z2 in eq_Abs_hypreal)
apply (rule_tac z = w in eq_Abs_hypreal)
apply (simp add: hypreal_mult hypreal_add left_distrib)
done

text{*one and zero are distinct*}
lemma hypreal_zero_not_eq_one: "0 \<noteq> (1::hypreal)"
apply (unfold hypreal_zero_def hypreal_one_def)
apply (auto simp add: real_zero_not_eq_one)
done


subsection{*Multiplicative Inverse on @{typ hypreal} *}

lemma hypreal_inverse_congruent: 
  "congruent hyprel (%X. hyprel``{%n. if X n = 0 then 0 else inverse(X n)})"
apply (unfold congruent_def)
apply (auto, ultra)
done

lemma hypreal_inverse: 
      "inverse (Abs_hypreal(hyprel``{%n. X n})) =  
       Abs_hypreal(hyprel `` {%n. if X n = 0 then 0 else inverse(X n)})"
apply (unfold hypreal_inverse_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (simp add: hyprel_in_hypreal [THEN Abs_hypreal_inverse] 
           UN_equiv_class [OF equiv_hyprel hypreal_inverse_congruent])
done

lemma hypreal_mult_inverse: 
     "x \<noteq> 0 ==> x*inverse(x) = (1::hypreal)"
apply (unfold hypreal_one_def hypreal_zero_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (simp add: hypreal_inverse hypreal_mult)
apply (drule FreeUltrafilterNat_Compl_mem)
apply (blast intro!: right_inverse FreeUltrafilterNat_subset)
done

lemma hypreal_mult_inverse_left:
     "x \<noteq> 0 ==> inverse(x)*x = (1::hypreal)"
by (simp add: hypreal_mult_inverse hypreal_mult_commute)

instance hypreal :: field
proof
  fix x y z :: hypreal
  show "(x + y) + z = x + (y + z)" by (rule hypreal_add_assoc)
  show "x + y = y + x" by (rule hypreal_add_commute)
  show "0 + x = x" by simp
  show "- x + x = 0" by (simp add: hypreal_add_minus_left)
  show "x - y = x + (-y)" by (simp add: hypreal_diff_def)
  show "(x * y) * z = x * (y * z)" by (rule hypreal_mult_assoc)
  show "x * y = y * x" by (rule hypreal_mult_commute)
  show "1 * x = x" by (simp add: hypreal_mult_1)
  show "(x + y) * z = x * z + y * z" by (simp add: hypreal_add_mult_distrib)
  show "0 \<noteq> (1::hypreal)" by (rule hypreal_zero_not_eq_one)
  show "x \<noteq> 0 ==> inverse x * x = 1" by (simp add: hypreal_mult_inverse_left)
  show "y \<noteq> 0 ==> x / y = x * inverse y" by (simp add: hypreal_divide_def)
  assume eq: "z+x = z+y" 
    hence "(-z + z) + x = (-z + z) + y" by (simp only: eq hypreal_add_assoc)
    thus "x = y" by (simp add: hypreal_add_minus_left)
qed


lemma HYPREAL_INVERSE_ZERO: "inverse 0 = (0::hypreal)"
by (simp add: hypreal_inverse hypreal_zero_def)

lemma HYPREAL_DIVISION_BY_ZERO: "a / (0::hypreal) = 0"
by (simp add: hypreal_divide_def HYPREAL_INVERSE_ZERO 
              hypreal_mult_commute [of a])

instance hypreal :: division_by_zero
proof
  fix x :: hypreal
  show "inverse 0 = (0::hypreal)" by (rule HYPREAL_INVERSE_ZERO)
  show "x/0 = 0" by (rule HYPREAL_DIVISION_BY_ZERO) 
qed


subsection{*Theorems for Ordering*}

text{*TODO: define @{text "\<le>"} as the primitive concept and quickly 
establish membership in class @{text linorder}. Then proofs could be
simplified, since properties of @{text "<"} would be generic.*}

text{*TODO: The following theorem should be used througout the proofs
  as it probably makes many of them more straightforward.*}
lemma hypreal_less: 
      "(Abs_hypreal(hyprel``{%n. X n}) < Abs_hypreal(hyprel``{%n. Y n})) =  
       ({n. X n < Y n} \<in> FreeUltrafilterNat)"
apply (unfold hypreal_less_def)
apply (auto intro!: lemma_hyprel_refl, ultra)
done

lemma hypreal_less_not_refl: "~ (R::hypreal) < R"
apply (rule_tac z = R in eq_Abs_hypreal)
apply (auto simp add: hypreal_less_def, ultra)
done

lemmas hypreal_less_irrefl = hypreal_less_not_refl [THEN notE, standard]
declare hypreal_less_irrefl [elim!]

lemma hypreal_not_refl2: "!!(x::hypreal). x < y ==> x \<noteq> y"
by (auto simp add: hypreal_less_not_refl)

lemma hypreal_less_trans: "!!(R1::hypreal). [| R1 < R2; R2 < R3 |] ==> R1 < R3"
apply (rule_tac z = R1 in eq_Abs_hypreal)
apply (rule_tac z = R2 in eq_Abs_hypreal)
apply (rule_tac z = R3 in eq_Abs_hypreal)
apply (auto intro!: exI simp add: hypreal_less_def, ultra)
done

lemma hypreal_less_asym: "!! (R1::hypreal). [| R1 < R2; R2 < R1 |] ==> P"
apply (drule hypreal_less_trans, assumption)
apply (simp add: hypreal_less_not_refl)
done


subsection{*Trichotomy: the hyperreals are Linearly Ordered*}

lemma lemma_hyprel_0_mem: "\<exists>x. x: hyprel `` {%n. 0}"
apply (unfold hyprel_def)
apply (rule_tac x = "%n. 0" in exI, safe)
apply (auto intro!: FreeUltrafilterNat_Nat_set)
done

lemma hypreal_trichotomy: "0 <  x | x = 0 | x < (0::hypreal)"
apply (unfold hypreal_zero_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: hypreal_less_def)
apply (cut_tac lemma_hyprel_0_mem, erule exE)
apply (drule_tac x = xa in spec)
apply (drule_tac x = x in spec)
apply (cut_tac x = x in lemma_hyprel_refl, auto)
apply (drule_tac x = x in spec)
apply (drule_tac x = xa in spec, auto, ultra)
done

lemma hypreal_trichotomyE:
     "[| (0::hypreal) < x ==> P;  
         x = 0 ==> P;  
         x < 0 ==> P |] ==> P"
apply (insert hypreal_trichotomy [of x], blast) 
done

lemma hypreal_less_minus_iff: "((x::hypreal) < y) = (0 < y + -x)"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto simp add: hypreal_add hypreal_zero_def hypreal_minus hypreal_less)
done

lemma hypreal_less_minus_iff2: "((x::hypreal) < y) = (x + -y < 0)"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto simp add: hypreal_add hypreal_zero_def hypreal_minus hypreal_less)
done

lemma hypreal_eq_minus_iff2: "((x::hypreal) = y) = (0 = y + - x)"
apply auto
apply (rule Ring_and_Field.add_right_cancel [of _ "-x", THEN iffD1], auto)
done

lemma hypreal_linear: "(x::hypreal) < y | x = y | y < x"
apply (subst hypreal_eq_minus_iff2)
apply (rule_tac x1 = x in hypreal_less_minus_iff [THEN ssubst])
apply (rule_tac x1 = y in hypreal_less_minus_iff2 [THEN ssubst])
apply (rule hypreal_trichotomyE, auto)
done

lemma hypreal_neq_iff: "((w::hypreal) \<noteq> z) = (w<z | z<w)"
by (cut_tac hypreal_linear, blast)

lemma hypreal_linear_less2: "!!(x::hypreal). [| x < y ==> P;  x = y ==> P;  
           y < x ==> P |] ==> P"
apply (cut_tac x = x and y = y in hypreal_linear, auto)
done


subsection{*Properties of The @{text "\<le>"} Relation*}

lemma hypreal_le: 
      "(Abs_hypreal(hyprel``{%n. X n}) <=  
            Abs_hypreal(hyprel``{%n. Y n})) =  
       ({n. X n <= Y n} \<in> FreeUltrafilterNat)"
apply (unfold hypreal_le_def real_le_def)
apply (auto simp add: hypreal_less)
apply (ultra+)
done

lemma hypreal_le_imp_less_or_eq: "!!(x::hypreal). x <= y ==> x < y | x = y"
apply (unfold hypreal_le_def)
apply (cut_tac hypreal_linear)
apply (fast elim: hypreal_less_irrefl hypreal_less_asym)
done

lemma hypreal_less_or_eq_imp_le: "z<w | z=w ==> z <=(w::hypreal)"
apply (unfold hypreal_le_def)
apply (cut_tac hypreal_linear)
apply (fast elim: hypreal_less_irrefl hypreal_less_asym)
done

lemma hypreal_le_eq_less_or_eq: "(x <= (y::hypreal)) = (x < y | x=y)"
by (blast intro!: hypreal_less_or_eq_imp_le dest: hypreal_le_imp_less_or_eq) 

lemmas hypreal_le_less = hypreal_le_eq_less_or_eq

lemma hypreal_le_refl: "w <= (w::hypreal)"
by (simp add: hypreal_le_eq_less_or_eq)

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma hypreal_le_linear: "(z::hypreal) <= w | w <= z"
apply (simp add: hypreal_le_less)
apply (cut_tac hypreal_linear, blast)
done

lemma hypreal_le_trans: "[| i <= j; j <= k |] ==> i <= (k::hypreal)"
apply (drule hypreal_le_imp_less_or_eq) 
apply (drule hypreal_le_imp_less_or_eq) 
apply (rule hypreal_less_or_eq_imp_le) 
apply (blast intro: hypreal_less_trans) 
done

lemma hypreal_le_anti_sym: "[| z <= w; w <= z |] ==> z = (w::hypreal)"
apply (drule hypreal_le_imp_less_or_eq) 
apply (drule hypreal_le_imp_less_or_eq) 
apply (fast elim: hypreal_less_irrefl hypreal_less_asym)
done

(* Axiom 'order_less_le' of class 'order': *)
lemma hypreal_less_le: "((w::hypreal) < z) = (w <= z & w \<noteq> z)"
apply (simp add: hypreal_le_def hypreal_neq_iff)
apply (blast intro: hypreal_less_asym)
done

instance hypreal :: order
  by (intro_classes,
      (assumption | 
       rule hypreal_le_refl hypreal_le_trans hypreal_le_anti_sym
            hypreal_less_le)+)

instance hypreal :: linorder 
  by (intro_classes, rule hypreal_le_linear)


lemma hypreal_add_less_mono1: "(A::hypreal) < B ==> A + C < B + C"
apply (rule_tac z = A in eq_Abs_hypreal)
apply (rule_tac z = B in eq_Abs_hypreal)
apply (rule_tac z = C in eq_Abs_hypreal)
apply (auto intro!: exI simp add: hypreal_less_def hypreal_add, ultra)
done

lemma hypreal_mult_order: "[| 0 < x; 0 < y |] ==> (0::hypreal) < x * y"
apply (unfold hypreal_zero_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto intro!: exI simp add: hypreal_less_def hypreal_mult, ultra)
apply (auto intro: real_mult_order)
done

lemma hypreal_add_left_le_mono1: "(q1::hypreal) \<le> q2  ==> x + q1 \<le> x + q2"
apply (drule order_le_imp_less_or_eq)
apply (auto intro: order_less_imp_le hypreal_add_less_mono1 simp add: hypreal_add_commute)
done

lemma hypreal_mult_less_mono1: "[| (0::hypreal) < z; x < y |] ==> x*z < y*z"
apply (rotate_tac 1)
apply (drule hypreal_less_minus_iff [THEN iffD1])
apply (rule hypreal_less_minus_iff [THEN iffD2])
apply (drule hypreal_mult_order, assumption)
apply (simp add: right_distrib hypreal_mult_commute)
done

lemma hypreal_mult_less_mono2: "[| (0::hypreal)<z; x<y |] ==> z*x<z*y"
apply (simp (no_asm_simp) add: hypreal_mult_commute hypreal_mult_less_mono1)
done

subsection{*The Hyperreals Form an Ordered Field*}

instance hypreal :: ordered_field
proof
  fix x y z :: hypreal
  show "x \<le> y ==> z + x \<le> z + y" by (rule hypreal_add_left_le_mono1)
  show "x < y ==> 0 < z ==> z * x < z * y" by (simp add: hypreal_mult_less_mono2)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)"
    by (auto dest: order_le_less_trans simp add: hrabs_def linorder_not_le)
qed

lemma hypreal_mult_1_right: "z * (1::hypreal) = z"
  by (rule Ring_and_Field.mult_1_right)

lemma hypreal_mult_minus_1 [simp]: "(- (1::hypreal)) * z = -z"
by (simp)

lemma hypreal_mult_minus_1_right [simp]: "z * (- (1::hypreal)) = -z"
by (subst hypreal_mult_commute, simp)

(*Used ONCE: in NSA.ML*)
lemma hypreal_minus_distrib1: "-(y + -(x::hypreal)) = x + -y"
by (simp add: hypreal_add_commute)

(*Used ONCE: in Lim.ML*)
lemma hypreal_eq_minus_iff3: "(x = y + z) = (x + -z = (y::hypreal))"
by (auto simp add: hypreal_add_assoc)

lemma hypreal_eq_minus_iff: "((x::hypreal) = y) = (x + - y = 0)"
apply auto
apply (rule Ring_and_Field.add_right_cancel [of _ "-y", THEN iffD1], auto)
done

(*Used 3 TIMES: in Lim.ML*)
lemma hypreal_not_eq_minus_iff: "(x \<noteq> a) = (x + -a \<noteq> (0::hypreal))"
by (auto dest: hypreal_eq_minus_iff [THEN iffD2])

lemma hypreal_mult_left_cancel: "(c::hypreal) \<noteq> 0 ==> (c*a=c*b) = (a=b)"
apply auto
done
    
lemma hypreal_mult_right_cancel: "(c::hypreal) \<noteq> 0 ==> (a*c=b*c) = (a=b)"
apply auto
done

lemma hypreal_inverse_not_zero: "x \<noteq> 0 ==> inverse (x::hypreal) \<noteq> 0"
  by (rule Ring_and_Field.nonzero_imp_inverse_nonzero)

lemma hypreal_mult_not_0: "[| x \<noteq> 0; y \<noteq> 0 |] ==> x * y \<noteq> (0::hypreal)"
by simp

lemma hypreal_minus_inverse: "inverse(-x) = -inverse(x::hypreal)"
  by (rule Ring_and_Field.inverse_minus_eq)

lemma hypreal_inverse_distrib: "inverse(x*y) = inverse(x)*inverse(y::hypreal)"
  by (rule Ring_and_Field.inverse_mult_distrib)


subsection{* Division lemmas *}

lemma hypreal_divide_one: "x/(1::hypreal) = x"
by (simp add: hypreal_divide_def)


(** As with multiplication, pull minus signs OUT of the / operator **)

lemma hypreal_add_divide_distrib: "(x+y)/(z::hypreal) = x/z + y/z"
  by (rule Ring_and_Field.add_divide_distrib)

lemma hypreal_inverse_add:
     "[|(x::hypreal) \<noteq> 0;  y \<noteq> 0 |]   
      ==> inverse(x) + inverse(y) = (x + y)*inverse(x*y)"
by (simp add: Ring_and_Field.inverse_add mult_assoc)


subsection{*@{term hypreal_of_real} Preserves Field and Order Properties*}

lemma hypreal_of_real_add [simp]: 
     "hypreal_of_real (z1 + z2) = hypreal_of_real z1 + hypreal_of_real z2"
apply (unfold hypreal_of_real_def)
apply (simp add: hypreal_add left_distrib)
done

lemma hypreal_of_real_mult [simp]: 
     "hypreal_of_real (z1 * z2) = hypreal_of_real z1 * hypreal_of_real z2"
apply (unfold hypreal_of_real_def)
apply (simp add: hypreal_mult right_distrib)
done

lemma hypreal_of_real_less_iff [simp]: 
     "(hypreal_of_real z1 <  hypreal_of_real z2) = (z1 < z2)"
apply (unfold hypreal_less_def hypreal_of_real_def, auto)
apply (rule_tac [2] x = "%n. z1" in exI, safe)
apply (rule_tac [3] x = "%n. z2" in exI, auto)
apply (rule FreeUltrafilterNat_P, ultra)
done

lemma hypreal_of_real_le_iff [simp]: 
     "(hypreal_of_real z1 <= hypreal_of_real z2) = (z1 <= z2)"
apply (unfold hypreal_le_def real_le_def, auto)
done

lemma hypreal_of_real_eq_iff [simp]:
     "(hypreal_of_real z1 = hypreal_of_real z2) = (z1 = z2)"
by (force intro: order_antisym hypreal_of_real_le_iff [THEN iffD1])

lemma hypreal_of_real_minus [simp]:
     "hypreal_of_real (-r) = - hypreal_of_real  r"
apply (unfold hypreal_of_real_def)
apply (auto simp add: hypreal_minus)
done

lemma hypreal_of_real_one [simp]: "hypreal_of_real 1 = (1::hypreal)"
by (unfold hypreal_of_real_def hypreal_one_def, simp)

lemma hypreal_of_real_zero [simp]: "hypreal_of_real 0 = 0"
by (unfold hypreal_of_real_def hypreal_zero_def, simp)

lemma hypreal_of_real_zero_iff: "(hypreal_of_real r = 0) = (r = 0)"
by (auto intro: FreeUltrafilterNat_P simp add: hypreal_of_real_def hypreal_zero_def FreeUltrafilterNat_Nat_set)

lemma hypreal_of_real_inverse [simp]:
     "hypreal_of_real (inverse r) = inverse (hypreal_of_real r)"
apply (case_tac "r=0")
apply (simp add: DIVISION_BY_ZERO INVERSE_ZERO HYPREAL_INVERSE_ZERO)
apply (rule_tac c1 = "hypreal_of_real r" in hypreal_mult_left_cancel [THEN iffD1])
apply (auto simp add: hypreal_of_real_zero_iff hypreal_of_real_mult [symmetric])
done

lemma hypreal_of_real_divide [simp]:
     "hypreal_of_real (z1 / z2) = hypreal_of_real z1 / hypreal_of_real z2"
by (simp add: hypreal_divide_def real_divide_def)


subsection{*Misc Others*}

lemma hypreal_zero_num: "0 = Abs_hypreal (hyprel `` {%n. 0})"
by (simp add: hypreal_zero_def [THEN meta_eq_to_obj_eq, symmetric])

lemma hypreal_one_num: "1 = Abs_hypreal (hyprel `` {%n. 1})"
by (simp add: hypreal_one_def [THEN meta_eq_to_obj_eq, symmetric])

lemma hypreal_omega_gt_zero [simp]: "0 < omega"
apply (unfold omega_def)
apply (auto simp add: hypreal_less hypreal_zero_num)
done


lemma hypreal_hrabs:
     "abs (Abs_hypreal (hyprel `` {X})) = 
      Abs_hypreal(hyprel `` {%n. abs (X n)})"
apply (auto simp add: hrabs_def hypreal_zero_def hypreal_le hypreal_minus)
apply (ultra, arith)+
done

ML
{*
val hrabs_def = thm "hrabs_def";
val hypreal_hrabs = thm "hypreal_hrabs";

val hypreal_zero_def = thm "hypreal_zero_def";
val hypreal_one_def = thm "hypreal_one_def";
val hypreal_minus_def = thm "hypreal_minus_def";
val hypreal_diff_def = thm "hypreal_diff_def";
val hypreal_inverse_def = thm "hypreal_inverse_def";
val hypreal_divide_def = thm "hypreal_divide_def";
val hypreal_of_real_def = thm "hypreal_of_real_def";
val omega_def = thm "omega_def";
val epsilon_def = thm "epsilon_def";
val hypreal_add_def = thm "hypreal_add_def";
val hypreal_mult_def = thm "hypreal_mult_def";
val hypreal_less_def = thm "hypreal_less_def";
val hypreal_le_def = thm "hypreal_le_def";

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
val FreeUltrafilterNat_Nat_set = thm "FreeUltrafilterNat_Nat_set";
val FreeUltrafilterNat_Nat_set_refl = thm "FreeUltrafilterNat_Nat_set_refl";
val FreeUltrafilterNat_P = thm "FreeUltrafilterNat_P";
val FreeUltrafilterNat_Ex_P = thm "FreeUltrafilterNat_Ex_P";
val FreeUltrafilterNat_all = thm "FreeUltrafilterNat_all";
val FreeUltrafilterNat_Un = thm "FreeUltrafilterNat_Un";
val hyprel_iff = thm "hyprel_iff";
val hyprel_refl = thm "hyprel_refl";
val hyprel_sym = thm "hyprel_sym";
val hyprel_trans = thm "hyprel_trans";
val equiv_hyprel = thm "equiv_hyprel";
val hyprel_in_hypreal = thm "hyprel_in_hypreal";
val Abs_hypreal_inverse = thm "Abs_hypreal_inverse";
val inj_on_Abs_hypreal = thm "inj_on_Abs_hypreal";
val inj_Rep_hypreal = thm "inj_Rep_hypreal";
val lemma_hyprel_refl = thm "lemma_hyprel_refl";
val hypreal_empty_not_mem = thm "hypreal_empty_not_mem";
val Rep_hypreal_nonempty = thm "Rep_hypreal_nonempty";
val inj_hypreal_of_real = thm "inj_hypreal_of_real";
val eq_Abs_hypreal = thm "eq_Abs_hypreal";
val hypreal_minus_congruent = thm "hypreal_minus_congruent";
val hypreal_minus = thm "hypreal_minus";
val hypreal_add_congruent2 = thm "hypreal_add_congruent2";
val hypreal_add = thm "hypreal_add";
val hypreal_diff = thm "hypreal_diff";
val hypreal_add_commute = thm "hypreal_add_commute";
val hypreal_add_assoc = thm "hypreal_add_assoc";
val hypreal_add_zero_left = thm "hypreal_add_zero_left";
val hypreal_add_zero_right = thm "hypreal_add_zero_right";
val hypreal_add_minus = thm "hypreal_add_minus";
val hypreal_add_minus_left = thm "hypreal_add_minus_left";
val hypreal_minus_distrib1 = thm "hypreal_minus_distrib1";
val hypreal_mult_congruent2 = thm "hypreal_mult_congruent2";
val hypreal_mult = thm "hypreal_mult";
val hypreal_mult_commute = thm "hypreal_mult_commute";
val hypreal_mult_assoc = thm "hypreal_mult_assoc";
val hypreal_mult_1 = thm "hypreal_mult_1";
val hypreal_mult_1_right = thm "hypreal_mult_1_right";
val hypreal_mult_minus_1 = thm "hypreal_mult_minus_1";
val hypreal_mult_minus_1_right = thm "hypreal_mult_minus_1_right";
val hypreal_zero_not_eq_one = thm "hypreal_zero_not_eq_one";
val hypreal_inverse_congruent = thm "hypreal_inverse_congruent";
val hypreal_inverse = thm "hypreal_inverse";
val HYPREAL_INVERSE_ZERO = thm "HYPREAL_INVERSE_ZERO";
val HYPREAL_DIVISION_BY_ZERO = thm "HYPREAL_DIVISION_BY_ZERO";
val hypreal_mult_inverse = thm "hypreal_mult_inverse";
val hypreal_mult_inverse_left = thm "hypreal_mult_inverse_left";
val hypreal_mult_left_cancel = thm "hypreal_mult_left_cancel";
val hypreal_mult_right_cancel = thm "hypreal_mult_right_cancel";
val hypreal_inverse_not_zero = thm "hypreal_inverse_not_zero";
val hypreal_mult_not_0 = thm "hypreal_mult_not_0";
val hypreal_minus_inverse = thm "hypreal_minus_inverse";
val hypreal_inverse_distrib = thm "hypreal_inverse_distrib";
val hypreal_less_not_refl = thm "hypreal_less_not_refl";
val hypreal_less_irrefl = thm"hypreal_less_irrefl";
val hypreal_not_refl2 = thm "hypreal_not_refl2";
val hypreal_less_trans = thm "hypreal_less_trans";
val hypreal_less_asym = thm "hypreal_less_asym";
val hypreal_less = thm "hypreal_less";
val hypreal_trichotomy = thm "hypreal_trichotomy";
val hypreal_less_minus_iff = thm "hypreal_less_minus_iff";
val hypreal_less_minus_iff2 = thm "hypreal_less_minus_iff2";
val hypreal_eq_minus_iff = thm "hypreal_eq_minus_iff";
val hypreal_eq_minus_iff2 = thm "hypreal_eq_minus_iff2";
val hypreal_eq_minus_iff3 = thm "hypreal_eq_minus_iff3";
val hypreal_not_eq_minus_iff = thm "hypreal_not_eq_minus_iff";
val hypreal_linear = thm "hypreal_linear";
val hypreal_neq_iff = thm "hypreal_neq_iff";
val hypreal_linear_less2 = thm "hypreal_linear_less2";
val hypreal_le = thm "hypreal_le";
val hypreal_le_imp_less_or_eq = thm "hypreal_le_imp_less_or_eq";
val hypreal_le_eq_less_or_eq = thm "hypreal_le_eq_less_or_eq";
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
val hypreal_of_real_zero_iff = thm "hypreal_of_real_zero_iff";
val hypreal_of_real_inverse = thm "hypreal_of_real_inverse";
val hypreal_of_real_divide = thm "hypreal_of_real_divide";
val hypreal_divide_one = thm "hypreal_divide_one";
val hypreal_add_divide_distrib = thm "hypreal_add_divide_distrib";
val hypreal_inverse_add = thm "hypreal_inverse_add";
val hypreal_zero_num = thm "hypreal_zero_num";
val hypreal_one_num = thm "hypreal_one_num";
val hypreal_omega_gt_zero = thm "hypreal_omega_gt_zero";
*}

end
