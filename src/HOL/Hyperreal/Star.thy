(*  Title       : Star.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : defining *-transforms in NSA which extends sets of reals,
                  and real=>real functions
*)

header{*Star-Transforms in Non-Standard Analysis*}

theory Star = NSA:

constdefs
    (* nonstandard extension of sets *)
    starset :: "real set => hypreal set"          ("*s* _" [80] 80)
    "*s* A  == {x. ALL X: Rep_hypreal(x). {n::nat. X n : A}: FreeUltrafilterNat}"

    (* internal sets *)
    starset_n :: "(nat => real set) => hypreal set"        ("*sn* _" [80] 80)
    "*sn* As  == {x. ALL X: Rep_hypreal(x). {n::nat. X n : (As n)}: FreeUltrafilterNat}"

    InternalSets :: "hypreal set set"
    "InternalSets == {X. EX As. X = *sn* As}"

    (* nonstandard extension of function *)
    is_starext  :: "[hypreal => hypreal, real => real] => bool"
    "is_starext F f == (ALL x y. EX X: Rep_hypreal(x). EX Y: Rep_hypreal(y).
                        ((y = (F x)) = ({n. Y n = f(X n)} : FreeUltrafilterNat)))"

    starfun :: "(real => real) => hypreal => hypreal"       ("*f* _" [80] 80)
    "*f* f  == (%x. Abs_hypreal(UN X: Rep_hypreal(x). hyprel``{%n. f(X n)}))"

    (* internal functions *)
    starfun_n :: "(nat => (real => real)) => hypreal => hypreal"
                 ("*fn* _" [80] 80)
    "*fn* F  == (%x. Abs_hypreal(UN X: Rep_hypreal(x). hyprel``{%n. (F n)(X n)}))"

    InternalFuns :: "(hypreal => hypreal) set"
    "InternalFuns == {X. EX F. X = *fn* F}"



(*--------------------------------------------------------
   Preamble - Pulling "EX" over "ALL"
 ---------------------------------------------------------*)

(* This proof does not need AC and was suggested by the
   referee for the JCM Paper: let f(x) be least y such
   that  Q(x,y)
*)
lemma no_choice: "ALL x. EX y. Q x y ==> EX (f :: nat => nat). ALL x. Q x (f x)"
apply (rule_tac x = "%x. LEAST y. Q x y" in exI)
apply (blast intro: LeastI)
done

(*------------------------------------------------------------
    Properties of the *-transform applied to sets of reals
 ------------------------------------------------------------*)

lemma STAR_real_set: "*s*(UNIV::real set) = (UNIV::hypreal set)"

apply (unfold starset_def, auto)
done
declare STAR_real_set [simp]

lemma STAR_empty_set: "*s* {} = {}"
apply (unfold starset_def, safe)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (drule_tac x = "%n. xa n" in bspec, auto)
done
declare STAR_empty_set [simp]

lemma STAR_Un: "*s* (A Un B) = *s* A Un *s* B"
apply (unfold starset_def, auto)
  prefer 3 apply (blast intro: FreeUltrafilterNat_subset)
 prefer 2 apply (blast intro: FreeUltrafilterNat_subset)
apply (drule FreeUltrafilterNat_Compl_mem)
apply (drule bspec, assumption)
apply (rule_tac z = x in eq_Abs_hypreal, auto, ultra)
done

lemma STAR_Int: "*s* (A Int B) = *s* A Int *s* B"
apply (unfold starset_def, auto)
prefer 3 apply (blast intro: FreeUltrafilterNat_Int FreeUltrafilterNat_subset)
apply (blast intro: FreeUltrafilterNat_subset)+
done

lemma STAR_Compl: "*s* -A = -( *s* A)"
apply (auto simp add: starset_def)
apply (rule_tac [!] z = x in eq_Abs_hypreal)
apply (auto dest!: bspec, ultra)
apply (drule FreeUltrafilterNat_Compl_mem, ultra)
done

lemma STAR_mem_Compl: "x \<notin> *s* F ==> x : *s* (- F)"
by (auto simp add: STAR_Compl)

lemma STAR_diff: "*s* (A - B) = *s* A - *s* B"
by (auto simp add: Diff_eq STAR_Int STAR_Compl)

lemma STAR_subset: "A <= B ==> *s* A <= *s* B"
apply (unfold starset_def)
apply (blast intro: FreeUltrafilterNat_subset)+
done

lemma STAR_mem: "a : A ==> hypreal_of_real a : *s* A"
apply (unfold starset_def hypreal_of_real_def)
apply (auto intro: FreeUltrafilterNat_subset)
done

lemma STAR_hypreal_of_real_image_subset: "hypreal_of_real ` A <= *s* A"
apply (unfold starset_def)
apply (auto simp add: hypreal_of_real_def)
apply (blast intro: FreeUltrafilterNat_subset)
done

lemma STAR_hypreal_of_real_Int: "*s* X Int Reals = hypreal_of_real ` X"
apply (unfold starset_def)
apply (auto simp add: hypreal_of_real_def SReal_def)
apply (simp add: hypreal_of_real_def [symmetric])
apply (rule imageI, rule ccontr)
apply (drule bspec)
apply (rule lemma_hyprel_refl)
prefer 2 apply (blast intro: FreeUltrafilterNat_subset, auto)
done

lemma lemma_not_hyprealA: "x \<notin> hypreal_of_real ` A ==> ALL y: A. x \<noteq> hypreal_of_real y"
by auto

lemma lemma_Compl_eq: "- {n. X n = xa} = {n. X n \<noteq> xa}"
by auto

lemma STAR_real_seq_to_hypreal:
    "ALL n. (X n) \<notin> M
          ==> Abs_hypreal(hyprel``{X}) \<notin> *s* M"
apply (unfold starset_def)
apply (auto, rule bexI, rule_tac [2] lemma_hyprel_refl, auto)
done

lemma STAR_singleton: "*s* {x} = {hypreal_of_real x}"
apply (unfold starset_def)
apply (auto simp add: hypreal_of_real_def)
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto intro: FreeUltrafilterNat_subset)
done
declare STAR_singleton [simp]

lemma STAR_not_mem: "x \<notin> F ==> hypreal_of_real x \<notin> *s* F"
apply (auto simp add: starset_def hypreal_of_real_def)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl, auto)
done

lemma STAR_subset_closed: "[| x : *s* A; A <= B |] ==> x : *s* B"
by (blast dest: STAR_subset)

(*------------------------------------------------------------------
   Nonstandard extension of a set (defined using a constant
   sequence) as a special case of an internal set
 -----------------------------------------------------------------*)

lemma starset_n_starset:
     "ALL n. (As n = A) ==> *sn* As = *s* A"

apply (unfold starset_n_def starset_def, auto)
done


(*----------------------------------------------------------------*)
(* Theorems about nonstandard extensions of functions             *)
(*----------------------------------------------------------------*)

(*----------------------------------------------------------------*)
(* Nonstandard extension of a function (defined using a           *)
(* constant sequence) as a special case of an internal function   *)
(*----------------------------------------------------------------*)

lemma starfun_n_starfun:
     "ALL n. (F n = f) ==> *fn* F = *f* f"

apply (unfold starfun_n_def starfun_def, auto)
done


(*
   Prove that hrabs is a nonstandard extension of rabs without
   use of congruence property (proved after this for general
   nonstandard extensions of real valued functions). This makes
   proof much longer- see comments at end of HREALABS.thy where
   we proved a congruence theorem for hrabs.

   NEW!!! No need to prove all the lemmas anymore. Use the ultrafilter
   tactic!
*)

lemma hrabs_is_starext_rabs: "is_starext abs abs"

apply (unfold is_starext_def, safe)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal, auto)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl)
apply (auto dest!: spec simp add: hypreal_minus hrabs_def hypreal_zero_def hypreal_le_def hypreal_less_def)
apply (arith | ultra)+
done

lemma Rep_hypreal_FreeUltrafilterNat: "[| X: Rep_hypreal z; Y: Rep_hypreal z |]
      ==> {n. X n = Y n} : FreeUltrafilterNat"
apply (rule_tac z = z in eq_Abs_hypreal)
apply (auto, ultra)
done

(*-----------------------------------------------------------------------
    Nonstandard extension of functions- congruence
 -----------------------------------------------------------------------*)

lemma starfun_congruent: "congruent hyprel (%X. hyprel``{%n. f (X n)})"
by (unfold congruent_def, auto, ultra)

lemma starfun:
      "( *f* f) (Abs_hypreal(hyprel``{%n. X n})) =
       Abs_hypreal(hyprel `` {%n. f (X n)})"
apply (unfold starfun_def)
apply (rule_tac f = Abs_hypreal in arg_cong)
apply (simp add: hyprel_in_hypreal [THEN Abs_hypreal_inverse] 
                 UN_equiv_class [OF equiv_hyprel starfun_congruent])
done

(*-------------------------------------------
  multiplication: ( *f) x ( *g) = *(f x g)
 ------------------------------------------*)
lemma starfun_mult: "( *f* f) xa * ( *f* g) xa = ( *f* (%x. f x * g x)) xa"
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_mult)
done
declare starfun_mult [symmetric, simp]

(*---------------------------------------
  addition: ( *f) + ( *g) = *(f + g)
 ---------------------------------------*)
lemma starfun_add: "( *f* f) xa + ( *f* g) xa = ( *f* (%x. f x + g x)) xa"
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_add)
done
declare starfun_add [symmetric, simp]

(*--------------------------------------------
  subtraction: ( *f) + -( *g) = *(f + -g)
 -------------------------------------------*)

lemma starfun_minus: "- ( *f* f) x = ( *f* (%x. - f x)) x"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_minus)
done
declare starfun_minus [symmetric, simp]

(*FIXME: delete*)
lemma starfun_add_minus: "( *f* f) xa + -( *f* g) xa = ( *f* (%x. f x + -g x)) xa"
apply (simp (no_asm))
done
declare starfun_add_minus [symmetric, simp]

lemma starfun_diff:
  "( *f* f) xa  - ( *f* g) xa = ( *f* (%x. f x - g x)) xa"
apply (unfold hypreal_diff_def real_diff_def)
apply (rule starfun_add_minus)
done
declare starfun_diff [symmetric, simp]

(*--------------------------------------
  composition: ( *f) o ( *g) = *(f o g)
 ---------------------------------------*)

lemma starfun_o2: "(%x. ( *f* f) (( *f* g) x)) = *f* (%x. f (g x))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun)
done

lemma starfun_o: "( *f* f) o ( *f* g) = ( *f* (f o g))"
apply (unfold o_def)
apply (simp (no_asm) add: starfun_o2)
done

(*--------------------------------------
  NS extension of constant function
 --------------------------------------*)
lemma starfun_const_fun: "( *f* (%x. k)) xa = hypreal_of_real  k"
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_of_real_def)
done

declare starfun_const_fun [simp]

(*----------------------------------------------------
   the NS extension of the identity function
 ----------------------------------------------------*)

lemma starfun_Idfun_approx: "x @= hypreal_of_real a ==> ( *f* (%x. x)) x @= hypreal_of_real  a"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun)
done

lemma starfun_Id: "( *f* (%x. x)) x = x"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun)
done
declare starfun_Id [simp]

(*----------------------------------------------------------------------
      the *-function is a (nonstandard) extension of the function
 ----------------------------------------------------------------------*)

lemma is_starext_starfun: "is_starext ( *f* f) f"

apply (unfold is_starext_def, auto)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto intro!: bexI simp add: starfun)
done

(*----------------------------------------------------------------------
     Any nonstandard extension is in fact the *-function
 ----------------------------------------------------------------------*)

lemma is_starfun_starext: "is_starext F f ==> F = *f* f"

apply (unfold is_starext_def)
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (drule_tac x = x in spec)
apply (drule_tac x = "( *f* f) x" in spec)
apply (auto dest!: FreeUltrafilterNat_Compl_mem simp add: starfun, ultra)
done

lemma is_starext_starfun_iff: "(is_starext F f) = (F = *f* f)"
by (blast intro: is_starfun_starext is_starext_starfun)

(*--------------------------------------------------------
   extented function has same solution as its standard
   version for real arguments. i.e they are the same
   for all real arguments
 -------------------------------------------------------*)
lemma starfun_eq: "( *f* f) (hypreal_of_real a) = hypreal_of_real (f a)"
by (auto simp add: starfun hypreal_of_real_def)

declare starfun_eq [simp]

lemma starfun_approx: "( *f* f) (hypreal_of_real a) @= hypreal_of_real (f a)"
by auto

(* useful for NS definition of derivatives *)
lemma starfun_lambda_cancel: "( *f* (%h. f (x + h))) xa  = ( *f* f) (hypreal_of_real  x + xa)"
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_of_real_def hypreal_add)
done

lemma starfun_lambda_cancel2: "( *f* (%h. f(g(x + h)))) xa = ( *f* (f o g)) (hypreal_of_real x + xa)"
apply (rule_tac z = xa in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_of_real_def hypreal_add)
done

lemma starfun_mult_HFinite_approx: "[| ( *f* f) xa @= l; ( *f* g) xa @= m;
                  l: HFinite; m: HFinite
               |] ==>  ( *f* (%x. f x * g x)) xa @= l * m"
apply (drule approx_mult_HFinite, assumption+)
apply (auto intro: approx_HFinite [OF _ approx_sym])
done

lemma starfun_add_approx: "[| ( *f* f) xa @= l; ( *f* g) xa @= m
               |] ==>  ( *f* (%x. f x + g x)) xa @= l + m"
apply (auto intro: approx_add)
done

(*----------------------------------------------------
    Examples: hrabs is nonstandard extension of rabs
              inverse is nonstandard extension of inverse
 ---------------------------------------------------*)

(* can be proved easily using theorem "starfun" and *)
(* properties of ultrafilter as for inverse below we  *)
(* use the theorem we proved above instead          *)

lemma starfun_rabs_hrabs: "*f* abs = abs"
by (rule hrabs_is_starext_rabs [THEN is_starext_starfun_iff [THEN iffD1], symmetric])

lemma starfun_inverse_inverse: "( *f* inverse) x = inverse(x)"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_inverse hypreal_zero_def)
done
declare starfun_inverse_inverse [simp]

lemma starfun_inverse: "inverse (( *f* f) x) = ( *f* (%x. inverse (f x))) x"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun hypreal_inverse)
done
declare starfun_inverse [symmetric, simp]

lemma starfun_divide:
  "( *f* f) xa  / ( *f* g) xa = ( *f* (%x. f x / g x)) xa"
apply (unfold hypreal_divide_def real_divide_def, auto)
done
declare starfun_divide [symmetric, simp]

lemma starfun_inverse2: "inverse (( *f* f) x) = ( *f* (%x. inverse (f x))) x"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto intro: FreeUltrafilterNat_subset dest!: FreeUltrafilterNat_Compl_mem simp add: starfun hypreal_inverse hypreal_zero_def)
done

(*-------------------------------------------------------------
    General lemma/theorem needed for proofs in elementary
    topology of the reals
 ------------------------------------------------------------*)
lemma starfun_mem_starset:
      "( *f* f) x : *s* A ==> x : *s* {x. f x : A}"
apply (unfold starset_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: starfun)
apply (rename_tac "X")
apply (drule_tac x = "%n. f (X n) " in bspec)
apply (auto, ultra)
done

(*------------------------------------------------------------
   Alternative definition for hrabs with rabs function
   applied entrywise to equivalence class representative.
   This is easily proved using starfun and ns extension thm
 ------------------------------------------------------------*)
lemma hypreal_hrabs: "abs (Abs_hypreal (hyprel `` {X})) =
                  Abs_hypreal(hyprel `` {%n. abs (X n)})"
apply (simp (no_asm) add: starfun_rabs_hrabs [symmetric] starfun)
done

(*----------------------------------------------------------------
   nonstandard extension of set through nonstandard extension
   of rabs function i.e hrabs. A more general result should be
   where we replace rabs by some arbitrary function f and hrabs
   by its NS extenson ( *f* f). See second NS set extension below.
 ----------------------------------------------------------------*)
lemma STAR_rabs_add_minus:
   "*s* {x. abs (x + - y) < r} =
     {x. abs(x + -hypreal_of_real y) < hypreal_of_real r}"
apply (unfold starset_def, safe)
apply (rule_tac [!] z = x in eq_Abs_hypreal)
apply (auto intro!: exI dest!: bspec simp add: hypreal_minus hypreal_of_real_def hypreal_add hypreal_hrabs hypreal_less, ultra)
done

lemma STAR_starfun_rabs_add_minus:
  "*s* {x. abs (f x + - y) < r} =
       {x. abs(( *f* f) x + -hypreal_of_real y) < hypreal_of_real r}"
apply (unfold starset_def, safe)
apply (rule_tac [!] z = x in eq_Abs_hypreal)
apply (auto intro!: exI dest!: bspec simp add: hypreal_minus hypreal_of_real_def hypreal_add hypreal_hrabs hypreal_less starfun, ultra)
done

(*-------------------------------------------------------------------
   Another characterization of Infinitesimal and one of @= relation.
   In this theory since hypreal_hrabs proved here. (To Check:) Maybe
   move both if possible?
 -------------------------------------------------------------------*)
lemma Infinitesimal_FreeUltrafilterNat_iff2: "(x:Infinitesimal) =
      (EX X:Rep_hypreal(x).
        ALL m. {n. abs(X n) < inverse(real(Suc m))}
               : FreeUltrafilterNat)"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto intro!: bexI lemma_hyprel_refl 
            simp add: Infinitesimal_hypreal_of_nat_iff hypreal_of_real_def 
     hypreal_inverse hypreal_hrabs hypreal_less hypreal_of_nat_def)
apply (drule_tac x = n in spec, ultra)
done

lemma approx_FreeUltrafilterNat_iff: "(Abs_hypreal(hyprel``{X}) @= Abs_hypreal(hyprel``{Y})) =
      (ALL m. {n. abs (X n + - Y n) <
                  inverse(real(Suc m))} : FreeUltrafilterNat)"
apply (subst approx_minus_iff)
apply (rule mem_infmal_iff [THEN subst])
apply (auto simp add: hypreal_minus hypreal_add Infinitesimal_FreeUltrafilterNat_iff2)
apply (drule_tac x = m in spec, ultra)
done

lemma inj_starfun: "inj starfun"
apply (rule inj_onI)
apply (rule ext, rule ccontr)
apply (drule_tac x = "Abs_hypreal (hyprel ``{%n. xa}) " in fun_cong)
apply (auto simp add: starfun)
done

ML
{*
val starset_def = thm"starset_def";
val starset_n_def = thm"starset_n_def";
val InternalSets_def = thm"InternalSets_def";
val is_starext_def = thm"is_starext_def";
val starfun_def = thm"starfun_def";
val starfun_n_def = thm"starfun_n_def";
val InternalFuns_def = thm"InternalFuns_def";

val no_choice = thm "no_choice";
val STAR_real_set = thm "STAR_real_set";
val STAR_empty_set = thm "STAR_empty_set";
val STAR_Un = thm "STAR_Un";
val STAR_Int = thm "STAR_Int";
val STAR_Compl = thm "STAR_Compl";
val STAR_mem_Compl = thm "STAR_mem_Compl";
val STAR_diff = thm "STAR_diff";
val STAR_subset = thm "STAR_subset";
val STAR_mem = thm "STAR_mem";
val STAR_hypreal_of_real_image_subset = thm "STAR_hypreal_of_real_image_subset";
val STAR_hypreal_of_real_Int = thm "STAR_hypreal_of_real_Int";
val STAR_real_seq_to_hypreal = thm "STAR_real_seq_to_hypreal";
val STAR_singleton = thm "STAR_singleton";
val STAR_not_mem = thm "STAR_not_mem";
val STAR_subset_closed = thm "STAR_subset_closed";
val starset_n_starset = thm "starset_n_starset";
val starfun_n_starfun = thm "starfun_n_starfun";
val hrabs_is_starext_rabs = thm "hrabs_is_starext_rabs";
val Rep_hypreal_FreeUltrafilterNat = thm "Rep_hypreal_FreeUltrafilterNat";
val starfun_congruent = thm "starfun_congruent";
val starfun = thm "starfun";
val starfun_mult = thm "starfun_mult";
val starfun_add = thm "starfun_add";
val starfun_minus = thm "starfun_minus";
val starfun_add_minus = thm "starfun_add_minus";
val starfun_diff = thm "starfun_diff";
val starfun_o2 = thm "starfun_o2";
val starfun_o = thm "starfun_o";
val starfun_const_fun = thm "starfun_const_fun";
val starfun_Idfun_approx = thm "starfun_Idfun_approx";
val starfun_Id = thm "starfun_Id";
val is_starext_starfun = thm "is_starext_starfun";
val is_starfun_starext = thm "is_starfun_starext";
val is_starext_starfun_iff = thm "is_starext_starfun_iff";
val starfun_eq = thm "starfun_eq";
val starfun_approx = thm "starfun_approx";
val starfun_lambda_cancel = thm "starfun_lambda_cancel";
val starfun_lambda_cancel2 = thm "starfun_lambda_cancel2";
val starfun_mult_HFinite_approx = thm "starfun_mult_HFinite_approx";
val starfun_add_approx = thm "starfun_add_approx";
val starfun_rabs_hrabs = thm "starfun_rabs_hrabs";
val starfun_inverse_inverse = thm "starfun_inverse_inverse";
val starfun_inverse = thm "starfun_inverse";
val starfun_divide = thm "starfun_divide";
val starfun_inverse2 = thm "starfun_inverse2";
val starfun_mem_starset = thm "starfun_mem_starset";
val hypreal_hrabs = thm "hypreal_hrabs";
val STAR_rabs_add_minus = thm "STAR_rabs_add_minus";
val STAR_starfun_rabs_add_minus = thm "STAR_starfun_rabs_add_minus";
val Infinitesimal_FreeUltrafilterNat_iff2 = thm "Infinitesimal_FreeUltrafilterNat_iff2";
val approx_FreeUltrafilterNat_iff = thm "approx_FreeUltrafilterNat_iff";
val inj_starfun = thm "inj_starfun";
*}

end
