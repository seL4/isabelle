(*  Title       : HOL/Real/Hyperreal/HyperDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Construction of Hyperreals Using Ultrafilters*}

theory HyperDef
imports StarClasses "../Real/Real"
uses ("fuf.ML")  (*Warning: file fuf.ML refers to the name Hyperdef!*)
begin

types hypreal = "real star"

syntax hypreal_of_real :: "real => real star"
translations "hypreal_of_real" => "star_of :: real => real star"

typed_print_translation {*
  let
    fun hr_tr' _ (Type ("fun", (Type ("real", []) :: _))) [t] =
          Syntax.const "hypreal_of_real" $ t
      | hr_tr' _ _ _ = raise Match;
  in [("star_of", hr_tr')] end
*}

constdefs

  omega   :: hypreal   -- {*an infinite number @{text "= [<1,2,3,...>]"} *}
  "omega == star_n (%n. real (Suc n))"

  epsilon :: hypreal   -- {*an infinitesimal number @{text "= [<1,1/2,1/3,...>]"} *}
  "epsilon == star_n (%n. inverse (real (Suc n)))"

syntax (xsymbols)
  omega   :: hypreal   ("\<omega>")
  epsilon :: hypreal   ("\<epsilon>")

syntax (HTML output)
  omega   :: hypreal   ("\<omega>")
  epsilon :: hypreal   ("\<epsilon>")


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
by (rule inj_onI, simp)

lemma eq_Abs_star:
    "(!!x. z = Abs_star(starrel``{x}) ==> P) ==> P"
by (fold star_n_def, auto intro: star_cases)

lemma Rep_star_star_n_iff [simp]:
  "(X \<in> Rep_star (star_n Y)) = ({n. Y n = X n} \<in> \<U>)"
by (simp add: star_n_def)

lemma Rep_star_star_n: "X \<in> Rep_star (star_n X)"
by simp

subsection{*Hyperreal Addition*}

lemma star_n_add:
  "star_n X + star_n Y = star_n (%n. X n + Y n)"
by (simp add: star_add_def Ifun2_of_def star_of_def Ifun_star_n)

subsection{*Additive inverse on @{typ hypreal}*}

lemma star_n_minus:
   "- star_n X = star_n (%n. -(X n))"
by (simp add: star_minus_def Ifun_of_def star_of_def Ifun_star_n)

lemma star_n_diff:
     "star_n X - star_n Y = star_n (%n. X n - Y n)"
by (simp add: star_diff_def Ifun2_of_def star_of_def Ifun_star_n)


subsection{*Hyperreal Multiplication*}

lemma star_n_mult:
  "star_n X * star_n Y = star_n (%n. X n * Y n)"
by (simp add: star_mult_def Ifun2_of_def star_of_def Ifun_star_n)


subsection{*Multiplicative Inverse on @{typ hypreal} *}

lemma star_n_inverse:
      "inverse (star_n X) = star_n (%n. if X n = (0::real) then 0 else inverse(X n))"
apply (simp add: star_inverse_def Ifun_of_def star_of_def Ifun_star_n)
apply (rule_tac f=star_n in arg_cong)
apply (rule ext)
apply simp
done

lemma star_n_inverse2:
      "inverse (star_n X) = star_n (%n. inverse(X n))"
by (simp add: star_inverse_def Ifun_of_def star_of_def Ifun_star_n)


subsection{*Properties of The @{text "\<le>"} Relation*}

lemma star_n_le:
      "star_n X \<le> star_n Y =  
       ({n. X n \<le> Y n} \<in> FreeUltrafilterNat)"
by (simp add: star_le_def Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)

lemma hypreal_not_refl2: "!!(x::hypreal). x < y ==> x \<noteq> y"
by (auto)

subsection{*The Hyperreals Form an Ordered Field*}

lemma hypreal_eq_minus_iff: "((x::hypreal) = y) = (x + - y = 0)"
by auto

lemma hypreal_mult_left_cancel: "(c::hypreal) \<noteq> 0 ==> (c*a=c*b) = (a=b)"
by auto
    
lemma hypreal_mult_right_cancel: "(c::hypreal) \<noteq> 0 ==> (a*c=b*c) = (a=b)"
by auto


subsection{*Misc Others*}

lemma star_n_less:
      "star_n X < star_n Y = ({n. X n < Y n} \<in> FreeUltrafilterNat)"
by (simp add: star_less_def Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)

lemma star_n_zero_num: "0 = star_n (%n. 0)"
by (simp add: star_zero_def star_of_def)

lemma star_n_one_num: "1 = star_n (%n. 1)"
by (simp add: star_one_def star_of_def)

lemma hypreal_omega_gt_zero [simp]: "0 < omega"
apply (simp only: omega_def star_zero_def star_less_def star_of_def)
apply (simp add: Ipred2_of_def star_of_def Ifun_star_n unstar_star_n)
done

lemma star_n_abs:
     "abs (star_n X) = star_n (%n. abs (X n))"
by (simp add: star_abs_def Ifun_of_def star_of_def Ifun_star_n)

subsection{*Existence of Infinite Hyperreal Number*}

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
apply (simp add: omega_def)
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
by (auto simp add: epsilon_def star_of_def star_n_eq_iff
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
val omega_def = thm "omega_def";
val epsilon_def = thm "epsilon_def";

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
val star_n_minus = thm "star_n_minus";
val star_n_add = thm "star_n_add";
val star_n_diff = thm "star_n_diff";
val star_n_mult = thm "star_n_mult";
val star_n_inverse = thm "star_n_inverse";
val hypreal_mult_left_cancel = thm "hypreal_mult_left_cancel";
val hypreal_mult_right_cancel = thm "hypreal_mult_right_cancel";
val hypreal_not_refl2 = thm "hypreal_not_refl2";
val star_n_less = thm "star_n_less";
val hypreal_eq_minus_iff = thm "hypreal_eq_minus_iff";
val star_n_le = thm "star_n_le";
val star_n_zero_num = thm "star_n_zero_num";
val star_n_one_num = thm "star_n_one_num";
val hypreal_omega_gt_zero = thm "hypreal_omega_gt_zero";

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
