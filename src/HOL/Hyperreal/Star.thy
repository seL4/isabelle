(*  Title       : Star.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

header{*Star-Transforms in Non-Standard Analysis*}

theory Star
imports NSA
begin

definition
    (* internal sets *)
  starset_n :: "(nat => 'a set) => 'a star set"        ("*sn* _" [80] 80)
  "*sn* As = Iset (star_n As)"

  InternalSets :: "'a star set set"
  "InternalSets = {X. \<exists>As. X = *sn* As}"

  (* nonstandard extension of function *)
  is_starext  :: "['a star => 'a star, 'a => 'a] => bool"
  "is_starext F f = (\<forall>x y. \<exists>X \<in> Rep_star(x). \<exists>Y \<in> Rep_star(y).
                        ((y = (F x)) = ({n. Y n = f(X n)} : FreeUltrafilterNat)))"
  (* internal functions *)
  starfun_n :: "(nat => ('a => 'b)) => 'a star => 'b star"   ("*fn* _" [80] 80)
  "*fn* F = Ifun (star_n F)"

  InternalFuns :: "('a star => 'b star) set"
  "InternalFuns = {X. \<exists>F. X = *fn* F}"


(*--------------------------------------------------------
   Preamble - Pulling "EX" over "ALL"
 ---------------------------------------------------------*)

(* This proof does not need AC and was suggested by the
   referee for the JCM Paper: let f(x) be least y such
   that  Q(x,y)
*)
lemma no_choice: "\<forall>x. \<exists>y. Q x y ==> \<exists>(f :: nat => nat). \<forall>x. Q x (f x)"
apply (rule_tac x = "%x. LEAST y. Q x y" in exI)
apply (blast intro: LeastI)
done

subsection{*Properties of the Star-transform Applied to Sets of Reals*}

lemma STAR_UNIV_set: "*s*(UNIV::'a set) = (UNIV::'a star set)"
by (transfer UNIV_def, rule refl)

lemma STAR_empty_set: "*s* {} = {}"
by (transfer empty_def, rule refl)

lemma STAR_Un: "*s* (A Un B) = *s* A Un *s* B"
by (transfer Un_def, rule refl)

lemma STAR_Int: "*s* (A Int B) = *s* A Int *s* B"
by (transfer Int_def, rule refl)

lemma STAR_Compl: "*s* -A = -( *s* A)"
by (transfer Compl_def, rule refl)

lemma STAR_mem_Compl: "!!x. x \<notin> *s* F ==> x : *s* (- F)"
by (transfer Compl_def, simp)

lemma STAR_diff: "*s* (A - B) = *s* A - *s* B"
by (transfer set_diff_def, rule refl)

lemma STAR_subset: "A <= B ==> *s* A <= *s* B"
by (transfer subset_def, simp)

lemma STAR_mem: "a \<in> A ==> star_of a : *s* A"
by transfer

lemma STAR_mem_iff: "(star_of x \<in> *s* A) = (x \<in> A)"
by (transfer, rule refl)

lemma STAR_star_of_image_subset: "star_of ` A <= *s* A"
by (auto simp add: STAR_mem)

lemma STAR_hypreal_of_real_Int: "*s* X Int Reals = hypreal_of_real ` X"
by (auto simp add: SReal_def STAR_mem_iff)

lemma lemma_not_hyprealA: "x \<notin> hypreal_of_real ` A ==> \<forall>y \<in> A. x \<noteq> hypreal_of_real y"
by auto

lemma lemma_Compl_eq: "- {n. X n = xa} = {n. X n \<noteq> xa}"
by auto

lemma STAR_real_seq_to_hypreal:
    "\<forall>n. (X n) \<notin> M ==> star_n X \<notin> *s* M"
apply (unfold starset_def star_of_def)
apply (simp add: Iset_star_n)
done

lemma STAR_singleton: "*s* {x} = {star_of x}"
by simp

lemma STAR_not_mem: "x \<notin> F ==> star_of x \<notin> *s* F"
by transfer

lemma STAR_subset_closed: "[| x : *s* A; A <= B |] ==> x : *s* B"
by (blast dest: STAR_subset)

text{*Nonstandard extension of a set (defined using a constant
   sequence) as a special case of an internal set*}

lemma starset_n_starset: "\<forall>n. (As n = A) ==> *sn* As = *s* A"
apply (drule expand_fun_eq [THEN iffD2])
apply (simp add: starset_n_def starset_def star_of_def)
done


(*----------------------------------------------------------------*)
(* Theorems about nonstandard extensions of functions             *)
(*----------------------------------------------------------------*)

(*----------------------------------------------------------------*)
(* Nonstandard extension of a function (defined using a           *)
(* constant sequence) as a special case of an internal function   *)
(*----------------------------------------------------------------*)

lemma starfun_n_starfun: "\<forall>n. (F n = f) ==> *fn* F = *f* f"
apply (drule expand_fun_eq [THEN iffD2])
apply (simp add: starfun_n_def starfun_def star_of_def)
done


(*
   Prove that abs for hypreal is a nonstandard extension of abs for real w/o
   use of congruence property (proved after this for general
   nonstandard extensions of real valued functions). 

   Proof now Uses the ultrafilter tactic!
*)

lemma hrabs_is_starext_rabs: "is_starext abs abs"
apply (simp add: is_starext_def, safe)
apply (rule_tac x=x in star_cases)
apply (rule_tac x=y in star_cases)
apply (unfold star_n_def, auto)
apply (rule bexI, rule_tac [2] lemma_starrel_refl)
apply (rule bexI, rule_tac [2] lemma_starrel_refl)
apply (fold star_n_def)
apply (unfold star_abs_def starfun_def star_of_def)
apply (simp add: Ifun_star_n star_n_eq_iff)
done

lemma Rep_star_FreeUltrafilterNat:
     "[| X \<in> Rep_star z; Y \<in> Rep_star z |]
      ==> {n. X n = Y n} : FreeUltrafilterNat"
by (rule FreeUltrafilterNat_Rep_hypreal)

text{*Nonstandard extension of functions*}

lemma starfun:
      "( *f* f) (star_n X) = star_n (%n. f (X n))"
by (simp add: starfun_def star_of_def Ifun_star_n)

lemma starfun_if_eq:
     "!!w. w \<noteq> star_of x
       ==> ( *f* (\<lambda>z. if z = x then a else g z)) w = ( *f* g) w"
by (transfer, simp)

(*-------------------------------------------
  multiplication: ( *f) x ( *g) = *(f x g)
 ------------------------------------------*)
lemma starfun_mult: "!!x. ( *f* f) x * ( *f* g) x = ( *f* (%x. f x * g x)) x"
by (transfer, rule refl)
declare starfun_mult [symmetric, simp]

(*---------------------------------------
  addition: ( *f) + ( *g) = *(f + g)
 ---------------------------------------*)
lemma starfun_add: "!!x. ( *f* f) x + ( *f* g) x = ( *f* (%x. f x + g x)) x"
by (transfer, rule refl)
declare starfun_add [symmetric, simp]

(*--------------------------------------------
  subtraction: ( *f) + -( *g) = *(f + -g)
 -------------------------------------------*)
lemma starfun_minus: "!!x. - ( *f* f) x = ( *f* (%x. - f x)) x"
by (transfer, rule refl)
declare starfun_minus [symmetric, simp]

(*FIXME: delete*)
lemma starfun_add_minus: "!!x. ( *f* f) x + -( *f* g) x = ( *f* (%x. f x + -g x)) x"
by (transfer, rule refl)
declare starfun_add_minus [symmetric, simp]

lemma starfun_diff: "!!x. ( *f* f) x  - ( *f* g) x = ( *f* (%x. f x - g x)) x"
by (transfer, rule refl)
declare starfun_diff [symmetric, simp]

(*--------------------------------------
  composition: ( *f) o ( *g) = *(f o g)
 ---------------------------------------*)

lemma starfun_o2: "(%x. ( *f* f) (( *f* g) x)) = *f* (%x. f (g x))"
by (transfer, rule refl)

lemma starfun_o: "( *f* f) o ( *f* g) = ( *f* (f o g))"
by (transfer o_def, rule refl)

text{*NS extension of constant function*}
lemma starfun_const_fun [simp]: "!!x. ( *f* (%x. k)) x = star_of k"
by (transfer, rule refl)

text{*the NS extension of the identity function*}

lemma starfun_Id [simp]: "!!x. ( *f* (%x. x)) x = x"
by (transfer, rule refl)

(* this is trivial, given starfun_Id *)
lemma starfun_Idfun_approx:
  "x @= hypreal_of_real a ==> ( *f* (%x. x)) x @= hypreal_of_real a"
by (simp only: starfun_Id)

text{*The Star-function is a (nonstandard) extension of the function*}

lemma is_starext_starfun: "is_starext ( *f* f) f"
apply (simp add: is_starext_def, auto)
apply (rule_tac x = x in star_cases)
apply (rule_tac x = y in star_cases)
apply (auto intro!: bexI [OF _ Rep_star_star_n]
            simp add: starfun star_n_eq_iff)
done

text{*Any nonstandard extension is in fact the Star-function*}

lemma is_starfun_starext: "is_starext F f ==> F = *f* f"
apply (simp add: is_starext_def)
apply (rule ext)
apply (rule_tac x = x in star_cases)
apply (drule_tac x = x in spec)
apply (drule_tac x = "( *f* f) x" in spec)
apply (auto dest!: FreeUltrafilterNat_Compl_mem simp add: starfun, ultra)
done

lemma is_starext_starfun_iff: "(is_starext F f) = (F = *f* f)"
by (blast intro: is_starfun_starext is_starext_starfun)

text{*extented function has same solution as its standard
   version for real arguments. i.e they are the same
   for all real arguments*}
lemma starfun_eq [simp]: "( *f* f) (star_of a) = star_of (f a)"
by (transfer, rule refl)

lemma starfun_approx: "( *f* f) (star_of a) @= hypreal_of_real (f a)"
by simp

(* useful for NS definition of derivatives *)
lemma starfun_lambda_cancel:
  "!!x'. ( *f* (%h. f (x + h))) x'  = ( *f* f) (star_of x + x')"
by (transfer, rule refl)

lemma starfun_lambda_cancel2:
  "( *f* (%h. f(g(x + h)))) x' = ( *f* (f o g)) (star_of x + x')"
by (unfold o_def, rule starfun_lambda_cancel)

lemma starfun_mult_HFinite_approx: "[| ( *f* f) x @= l; ( *f* g) x @= m;
                  l: HFinite; m: HFinite
               |] ==>  ( *f* (%x. f x * g x)) x @= l * m"
apply (drule (3) approx_mult_HFinite)
apply (auto intro: approx_HFinite [OF _ approx_sym])
done

lemma starfun_add_approx: "[| ( *f* f) x @= l; ( *f* g) x @= m
               |] ==>  ( *f* (%x. f x + g x)) x @= l + m"
by (auto intro: approx_add)

text{*Examples: hrabs is nonstandard extension of rabs
              inverse is nonstandard extension of inverse*}

(* can be proved easily using theorem "starfun" and *)
(* properties of ultrafilter as for inverse below we  *)
(* use the theorem we proved above instead          *)

lemma starfun_rabs_hrabs: "*f* abs = abs"
by (rule hrabs_is_starext_rabs [THEN is_starext_starfun_iff [THEN iffD1], symmetric])

lemma starfun_inverse_inverse [simp]: "( *f* inverse) x = inverse(x)"
by (unfold star_inverse_def, rule refl)

lemma starfun_inverse: "!!x. inverse (( *f* f) x) = ( *f* (%x. inverse (f x))) x"
by (transfer, rule refl)
declare starfun_inverse [symmetric, simp]

lemma starfun_divide: "!!x. ( *f* f) x / ( *f* g) x = ( *f* (%x. f x / g x)) x"
by (transfer, rule refl)
declare starfun_divide [symmetric, simp]

lemma starfun_inverse2: "!!x. inverse (( *f* f) x) = ( *f* (%x. inverse (f x))) x"
by (transfer, rule refl)

text{*General lemma/theorem needed for proofs in elementary
    topology of the reals*}
lemma starfun_mem_starset:
      "!!x. ( *f* f) x : *s* A ==> x : *s* {x. f x  \<in> A}"
by (transfer, simp)

text{*Alternative definition for hrabs with rabs function
   applied entrywise to equivalence class representative.
   This is easily proved using starfun and ns extension thm*}
lemma hypreal_hrabs:
     "abs (star_n X) = star_n (%n. abs (X n))"
by (simp only: starfun_rabs_hrabs [symmetric] starfun)

text{*nonstandard extension of set through nonstandard extension
   of rabs function i.e hrabs. A more general result should be
   where we replace rabs by some arbitrary function f and hrabs
   by its NS extenson. See second NS set extension below.*}
lemma STAR_rabs_add_minus:
   "*s* {x. abs (x + - y) < r} =
     {x. abs(x + -hypreal_of_real y) < hypreal_of_real r}"
by (transfer, rule refl)

lemma STAR_starfun_rabs_add_minus:
  "*s* {x. abs (f x + - y) < r} =
       {x. abs(( *f* f) x + -hypreal_of_real y) < hypreal_of_real r}"
by (transfer, rule refl)

text{*Another characterization of Infinitesimal and one of @= relation.
   In this theory since @{text hypreal_hrabs} proved here. Maybe
   move both theorems??*}
lemma Infinitesimal_FreeUltrafilterNat_iff2:
     "(x \<in> Infinitesimal) =
      (\<exists>X \<in> Rep_star(x).
        \<forall>m. {n. abs(X n) < inverse(real(Suc m))}
                \<in>  FreeUltrafilterNat)"
apply (cases x)
apply (auto intro!: bexI lemma_starrel_refl 
            simp add: Infinitesimal_hypreal_of_nat_iff star_of_def
     star_n_inverse star_n_abs star_n_less hypreal_of_nat_eq)
apply (drule_tac x = n in spec, ultra)
done

lemma approx_FreeUltrafilterNat_iff: "star_n X @= star_n Y =
      (\<forall>m. {n. abs (X n + - Y n) <
                  inverse(real(Suc m))} : FreeUltrafilterNat)"
apply (subst approx_minus_iff)
apply (rule mem_infmal_iff [THEN subst])
apply (auto simp add: star_n_minus star_n_add Infinitesimal_FreeUltrafilterNat_iff2)
apply (drule_tac x = m in spec, ultra)
done

lemma inj_starfun: "inj starfun"
apply (rule inj_onI)
apply (rule ext, rule ccontr)
apply (drule_tac x = "star_n (%n. xa)" in fun_cong)
apply (auto simp add: starfun star_n_eq_iff)
done

end
