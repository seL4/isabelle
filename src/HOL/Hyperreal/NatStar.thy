(*  Title       : NatStar.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp
*)

header{*Star-transforms for the Hypernaturals*}

theory NatStar = RealPow + HyperPow:


text{*Extends sets of nats, and functions from the nats to nats or reals*}


constdefs

  (* internal sets and nonstandard extensions -- see Star.thy as well *)

    starsetNat :: "nat set => hypnat set"          ("*sNat* _" [80] 80)
    "*sNat* A ==
       {x. \<forall>X\<in>Rep_hypnat(x). {n::nat. X n \<in> A}: FreeUltrafilterNat}"

   starsetNat_n :: "(nat => nat set) => hypnat set"      ("*sNatn* _" [80] 80)
    "*sNatn* As ==
       {x. \<forall>X\<in>Rep_hypnat(x). {n::nat. X n \<in> (As n)}: FreeUltrafilterNat}"

   InternalNatSets :: "hypnat set set"
    "InternalNatSets == {X. \<exists>As. X = *sNatn* As}"

    (* star transform of functions f:Nat --> Real *)

    starfunNat :: "(nat => real) => hypnat => hypreal"
                  ("*fNat* _" [80] 80)
    "*fNat* f  == (%x. Abs_hypreal(\<Union>X\<in>Rep_hypnat(x). hyprel``{%n. f (X n)}))"

   starfunNat_n :: "(nat => (nat => real)) => hypnat => hypreal"
                   ("*fNatn* _" [80] 80)
    "*fNatn* F ==
      (%x. Abs_hypreal(\<Union>X\<in>Rep_hypnat(x). hyprel``{%n. (F n)(X n)}))"

   InternalNatFuns :: "(hypnat => hypreal) set"
    "InternalNatFuns == {X. \<exists>F. X = *fNatn* F}"

    (* star transform of functions f:Nat --> Nat *)

   starfunNat2 :: "(nat => nat) => hypnat => hypnat"
                   ("*fNat2* _" [80] 80)
    "*fNat2* f == %x. Abs_hypnat(\<Union>X\<in>Rep_hypnat(x). hypnatrel``{%n. f (X n)})"

   starfunNat2_n :: "(nat => (nat => nat)) => hypnat => hypnat"
                     ("*fNat2n* _" [80] 80)
    "*fNat2n* F == 
        %x. Abs_hypnat(\<Union>X\<in>Rep_hypnat(x). hypnatrel``{%n. (F n)(X n)})"

   InternalNatFuns2 :: "(hypnat => hypnat) set"
    "InternalNatFuns2 == {X. \<exists>F. X = *fNat2n* F}"


lemma NatStar_real_set: "*sNat*(UNIV::nat set) = (UNIV::hypnat set)"
by (simp add: starsetNat_def)

lemma NatStar_empty_set [simp]: "*sNat* {} = {}"
by (simp add: starsetNat_def)

lemma NatStar_Un: "*sNat* (A Un B) = *sNat* A Un *sNat* B"
apply (auto simp add: starsetNat_def)
 prefer 2 apply (blast intro: FreeUltrafilterNat_subset)
 prefer 2 apply (blast intro: FreeUltrafilterNat_subset)
apply (drule FreeUltrafilterNat_Compl_mem)
apply (drule bspec, assumption)
apply (rule_tac z = x in eq_Abs_hypnat, auto, ultra)
done

lemma starsetNat_n_Un: "*sNatn* (%n. (A n) Un (B n)) = *sNatn* A Un *sNatn* B"
apply (auto simp add: starsetNat_n_def)
apply (drule_tac x = Xa in bspec)
apply (rule_tac [2] z = x in eq_Abs_hypnat)
apply (auto dest!: bspec, ultra+)
done

lemma InternalNatSets_Un:
     "[| X \<in> InternalNatSets; Y \<in> InternalNatSets |]
      ==> (X Un Y) \<in> InternalNatSets"
by (auto simp add: InternalNatSets_def starsetNat_n_Un [symmetric])

lemma NatStar_Int: "*sNat* (A Int B) = *sNat* A Int *sNat* B"
apply (auto simp add: starsetNat_def)
prefer 3 apply (blast intro: FreeUltrafilterNat_Int FreeUltrafilterNat_subset)
apply (blast intro: FreeUltrafilterNat_subset)+
done

lemma starsetNat_n_Int:
      "*sNatn* (%n. (A n) Int (B n)) = *sNatn* A Int *sNatn* B"
apply (auto simp add: starsetNat_n_def)
apply (auto dest!: bspec, ultra+)
done

lemma InternalNatSets_Int:
     "[| X \<in> InternalNatSets; Y \<in> InternalNatSets |]
      ==> (X Int Y) \<in> InternalNatSets"
by (auto simp add: InternalNatSets_def starsetNat_n_Int [symmetric])

lemma NatStar_Compl: "*sNat* (-A) = -( *sNat* A)"
apply (auto simp add: starsetNat_def)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (rule_tac [2] z = x in eq_Abs_hypnat)
apply (auto dest!: bspec, ultra+)
done

lemma starsetNat_n_Compl: "*sNatn* ((%n. - A n)) = -( *sNatn* A)"
apply (auto simp add: starsetNat_n_def)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (rule_tac [2] z = x in eq_Abs_hypnat)
apply (auto dest!: bspec, ultra+)
done

lemma InternalNatSets_Compl: "X \<in> InternalNatSets ==> -X \<in> InternalNatSets"
by (auto simp add: InternalNatSets_def starsetNat_n_Compl [symmetric])

lemma starsetNat_n_diff: "*sNatn* (%n. (A n) - (B n)) = *sNatn* A - *sNatn* B"
apply (auto simp add: starsetNat_n_def)
apply (rule_tac [2] z = x in eq_Abs_hypnat)
apply (rule_tac [3] z = x in eq_Abs_hypnat)
apply (auto dest!: bspec, ultra+)
done

lemma InternalNatSets_diff:
     "[| X \<in> InternalNatSets; Y \<in> InternalNatSets |]
      ==> (X - Y) \<in> InternalNatSets"
by (auto simp add: InternalNatSets_def starsetNat_n_diff [symmetric])

lemma NatStar_subset: "A \<le> B ==> *sNat* A \<le> *sNat* B"
apply (simp add: starsetNat_def)
apply (blast intro: FreeUltrafilterNat_subset)
done

lemma NatStar_mem: "a \<in> A ==> hypnat_of_nat a \<in> *sNat* A"
by (auto intro: FreeUltrafilterNat_subset 
         simp add: starsetNat_def hypnat_of_nat_eq)

lemma NatStar_hypreal_of_real_image_subset: "hypnat_of_nat ` A \<le> *sNat* A"
apply (auto simp add: starsetNat_def hypnat_of_nat_eq)
apply (blast intro: FreeUltrafilterNat_subset)
done

lemma NatStar_SHNat_subset: "Nats \<le> *sNat* (UNIV:: nat set)"
by (simp add: starsetNat_def SHNat_eq hypnat_of_nat_eq)

lemma NatStar_hypreal_of_real_Int:
     "*sNat* X Int Nats = hypnat_of_nat ` X"
apply (auto simp add: starsetNat_def hypnat_of_nat_eq SHNat_eq)
apply (simp add: hypnat_of_nat_eq [symmetric])
apply (rule imageI, rule ccontr)
apply (drule bspec)
apply (rule lemma_hypnatrel_refl)
prefer 2 apply (blast intro: FreeUltrafilterNat_subset, auto)
done

lemma starsetNat_starsetNat_n_eq: "*sNat* X = *sNatn* (%n. X)"
by (simp add: starsetNat_n_def starsetNat_def)

lemma InternalNatSets_starsetNat_n [simp]: "( *sNat* X) \<in> InternalNatSets"
by (auto simp add: InternalNatSets_def starsetNat_starsetNat_n_eq)

lemma InternalNatSets_UNIV_diff:
     "X \<in> InternalNatSets ==> UNIV - X \<in> InternalNatSets"
by (auto intro: InternalNatSets_Compl)

text{*Nonstandard extension of a set (defined using a constant
   sequence) as a special case of an internal set*}
lemma starsetNat_n_starsetNat: "\<forall>n. (As n = A) ==> *sNatn* As = *sNat* A"
by (simp add: starsetNat_n_def starsetNat_def)


subsection{*Nonstandard Extensions of Functions*}

text{* Nonstandard extension of a function (defined using a constant
   sequence) as a special case of an internal function*}

lemma starfunNat_n_starfunNat: "\<forall>n. (F n = f) ==> *fNatn* F = *fNat* f"
by (simp add: starfunNat_n_def starfunNat_def)

lemma starfunNat2_n_starfunNat2: "\<forall>n. (F n = f) ==> *fNat2n* F = *fNat2* f"
by (simp add: starfunNat2_n_def starfunNat2_def)

lemma starfunNat_congruent:
      "congruent hypnatrel (%X. hypnatrel``{%n. f (X n)})"
apply (simp add: congruent_def, safe)
apply (ultra+)
done

(* f::nat=>real *)
lemma starfunNat:
      "( *fNat* f) (Abs_hypnat(hypnatrel``{%n. X n})) =
       Abs_hypreal(hyprel `` {%n. f (X n)})"
apply (simp add: starfunNat_def)
apply (rule arg_cong [where f = Abs_hypreal])
apply (auto, ultra)
done

(* f::nat=>nat *)
lemma starfunNat2:
      "( *fNat2* f) (Abs_hypnat(hypnatrel``{%n. X n})) =
       Abs_hypnat(hypnatrel `` {%n. f (X n)})"
apply (simp add: starfunNat2_def)
apply (rule arg_cong [where f = Abs_hypnat])
apply (simp add: hypnatrel_in_hypnat [THEN Abs_hypnat_inverse]
         UN_equiv_class [OF equiv_hypnatrel starfunNat_congruent])
done

subsubsection{*Multiplication: @{text "( *f) x ( *g) = *(f x g)"}*}

lemma starfunNat_mult:
     "( *fNat* f) z * ( *fNat* g) z = ( *fNat* (%x. f x * g x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat hypreal_mult)
done

lemma starfunNat2_mult:
     "( *fNat2* f) z * ( *fNat2* g) z = ( *fNat2* (%x. f x * g x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat2 hypnat_mult)
done

subsubsection{*Addition: @{text "( *f) + ( *g) = *(f + g)"}*}

lemma starfunNat_add:
     "( *fNat* f) z + ( *fNat* g) z = ( *fNat* (%x. f x + g x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat hypreal_add)
done

lemma starfunNat2_add:
     "( *fNat2* f) z + ( *fNat2* g) z = ( *fNat2* (%x. f x + g x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat2 hypnat_add)
done

lemma starfunNat2_minus:
     "( *fNat2* f) z - ( *fNat2* g) z = ( *fNat2* (%x. f x - g x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat2 hypnat_minus)
done

subsubsection{*Composition: @{text "( *f) o ( *g) = *(f o g)"}*}

(***** ( *f::nat=>real) o ( *g::nat=>nat) = *(f o g) *****)

lemma starfunNatNat2_o:
     "( *fNat* f) o ( *fNat2* g) = ( *fNat* (f o g))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (simp add: starfunNat2 starfunNat)
done

lemma starfunNatNat2_o2:
     "(%x. ( *fNat* f) (( *fNat2* g) x)) = ( *fNat* (%x. f(g x)))"
apply (insert starfunNatNat2_o [of f g]) 
apply (simp add: o_def) 
done

(***** ( *f::nat=>nat) o ( *g::nat=>nat) = *(f o g) *****)
lemma starfunNat2_o: "( *fNat2* f) o ( *fNat2* g) = ( *fNat2* (f o g))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (simp add: starfunNat2)
done

(***** ( *f::real=>real) o ( *g::nat=>real) = *(f o g) *****)

lemma starfun_stafunNat_o: "( *f* f) o ( *fNat* g) = ( *fNat* (f o g))"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (simp add: starfunNat starfun)
done

lemma starfun_stafunNat_o2:
     "(%x. ( *f* f) (( *fNat* g) x)) = ( *fNat* (%x. f (g x)))"
apply (insert starfun_stafunNat_o [of f g]) 
apply (simp add: o_def) 
done


text{*NS extension of constant function*}

lemma starfunNat_const_fun [simp]: "( *fNat* (%x. k)) z = hypreal_of_real k"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat hypreal_of_real_def)
done

lemma starfunNat2_const_fun [simp]: "( *fNat2* (%x. k)) z = hypnat_of_nat  k"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat2 hypnat_of_nat_eq)
done

lemma starfunNat_minus: "- ( *fNat* f) x = ( *fNat* (%x. - f x)) x"
apply (rule eq_Abs_hypnat [of x])
apply (simp add: starfunNat hypreal_minus)
done

lemma starfunNat_inverse:
     "inverse (( *fNat* f) x) = ( *fNat* (%x. inverse (f x))) x"
apply (rule eq_Abs_hypnat [of x])
apply (simp add: starfunNat hypreal_inverse)
done

text{* Extended function has same solution as its standard
   version for natural arguments. i.e they are the same
   for all natural arguments (c.f. Hoskins pg. 107- SEQ)*}

lemma starfunNat_eq [simp]:
     "( *fNat* f) (hypnat_of_nat a) = hypreal_of_real (f a)"
by (simp add: starfunNat hypnat_of_nat_eq hypreal_of_real_def)

lemma starfunNat2_eq [simp]:
     "( *fNat2* f) (hypnat_of_nat a) = hypnat_of_nat (f a)"
by (simp add: starfunNat2 hypnat_of_nat_eq)

lemma starfunNat_approx:
     "( *fNat* f) (hypnat_of_nat a) @= hypreal_of_real (f a)"
by auto


text{* Example of transfer of a property from reals to hyperreals
    --- used for limit comparison of sequences*}

lemma starfun_le_mono:
     "\<forall>n. N \<le> n --> f n \<le> g n
      ==> \<forall>n. hypnat_of_nat N \<le> n --> ( *fNat* f) n \<le> ( *fNat* g) n"
apply safe
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: starfunNat hypnat_of_nat_eq hypreal_le hypreal_less hypnat_le hypnat_less, ultra, auto)
done

(*****----- and another -----*****)
lemma starfun_less_mono:
     "\<forall>n. N \<le> n --> f n < g n
      ==> \<forall>n. hypnat_of_nat N \<le> n --> ( *fNat* f) n < ( *fNat* g) n"
apply safe
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: starfunNat hypnat_of_nat_eq hypreal_le hypreal_less hypnat_le hypnat_less, ultra, auto)
done

text{*Nonstandard extension when we increment the argument by one*}

lemma starfunNat_shift_one:
     "( *fNat* (%n. f (Suc n))) N = ( *fNat* f) (N + (1::hypnat))"
apply (rule eq_Abs_hypnat [of N])
apply (simp add: starfunNat hypnat_one_def hypnat_add)
done

text{*Nonstandard extension with absolute value*}

lemma starfunNat_rabs: "( *fNat* (%n. abs (f n))) N = abs(( *fNat* f) N)"
apply (rule eq_Abs_hypnat [of N])
apply (simp add: starfunNat hypreal_hrabs)
done

text{*The hyperpow function as a nonstandard extension of realpow*}

lemma starfunNat_pow: "( *fNat* (%n. r ^ n)) N = (hypreal_of_real r) pow N"
apply (rule eq_Abs_hypnat [of N])
apply (simp add: hyperpow hypreal_of_real_def starfunNat)
done

lemma starfunNat_pow2:
     "( *fNat* (%n. (X n) ^ m)) N = ( *fNat* X) N pow hypnat_of_nat m"
apply (rule eq_Abs_hypnat [of N])
apply (simp add: hyperpow hypnat_of_nat_eq starfunNat)
done

lemma starfun_pow: "( *f* (%r. r ^ n)) R = (R) pow hypnat_of_nat n"
apply (rule_tac z = R in eq_Abs_hypreal)
apply (simp add: hyperpow starfun hypnat_of_nat_eq)
done

text{*The @{term hypreal_of_hypnat} function as a nonstandard extension of
  @{term real_of_nat} *}

lemma starfunNat_real_of_nat: "( *fNat* real) = hypreal_of_hypnat"
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (simp add: hypreal_of_hypnat starfunNat)
done

lemma starfunNat_inverse_real_of_nat_eq:
     "N \<in> HNatInfinite
   ==> ( *fNat* (%x::nat. inverse(real x))) N = inverse(hypreal_of_hypnat N)"
apply (rule_tac f1 = inverse in starfun_stafunNat_o2 [THEN subst])
apply (subgoal_tac "hypreal_of_hypnat N ~= 0")
apply (simp_all add: HNatInfinite_not_eq_zero starfunNat_real_of_nat starfun_inverse_inverse)
done

text{*Internal functions - some redundancy with *fNat* now*}

lemma starfunNat_n_congruent:
      "congruent hypnatrel (%X. hypnatrel``{%n. f n (X n)})"
apply (simp add: congruent_def, safe)
apply (ultra+)
done

lemma starfunNat_n:
     "( *fNatn* f) (Abs_hypnat(hypnatrel``{%n. X n})) =
      Abs_hypreal(hyprel `` {%n. f n (X n)})"
apply (simp add: starfunNat_n_def)
apply (rule_tac f = Abs_hypreal in arg_cong, auto, ultra)
done

text{*Multiplication: @{text "( *fn) x ( *gn) = *(fn x gn)"}*}

lemma starfunNat_n_mult:
     "( *fNatn* f) z * ( *fNatn* g) z = ( *fNatn* (% i x. f i x * g i x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat_n hypreal_mult)
done

text{*Addition: @{text "( *fn) + ( *gn) = *(fn + gn)"}*}

lemma starfunNat_n_add:
     "( *fNatn* f) z + ( *fNatn* g) z = ( *fNatn* (%i x. f i x + g i x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat_n hypreal_add)
done

text{*Subtraction: @{text "( *fn) - ( *gn) = *(fn + - gn)"}*}

lemma starfunNat_n_add_minus:
     "( *fNatn* f) z + -( *fNatn* g) z = ( *fNatn* (%i x. f i x + -g i x)) z"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat_n hypreal_minus hypreal_add)
done


text{*Composition: @{text "( *fn) o ( *gn) = *(fn o gn)"}*}

lemma starfunNat_n_const_fun [simp]:
     "( *fNatn* (%i x. k)) z = hypreal_of_real  k"
apply (rule eq_Abs_hypnat [of z])
apply (simp add: starfunNat_n hypreal_of_real_def)
done

lemma starfunNat_n_minus: "- ( *fNatn* f) x = ( *fNatn* (%i x. - (f i) x)) x"
apply (rule eq_Abs_hypnat [of x])
apply (simp add: starfunNat_n hypreal_minus)
done

lemma starfunNat_n_eq [simp]:
     "( *fNatn* f) (hypnat_of_nat n) = Abs_hypreal(hyprel `` {%i. f i n})"
by (simp add: starfunNat_n hypnat_of_nat_eq)

lemma starfun_eq_iff: "(( *fNat* f) = ( *fNat* g)) = (f = g)"
apply auto
apply (rule ext, rule ccontr)
apply (drule_tac x = "hypnat_of_nat (x) " in fun_cong)
apply (simp add: starfunNat hypnat_of_nat_eq)
done


lemma starfunNat_inverse_real_of_nat_Infinitesimal [simp]:
     "N \<in> HNatInfinite ==> ( *fNat* (%x. inverse (real x))) N \<in> Infinitesimal"
apply (rule_tac f1 = inverse in starfun_stafunNat_o2 [THEN subst])
apply (subgoal_tac "hypreal_of_hypnat N ~= 0")
apply (simp_all add: HNatInfinite_not_eq_zero starfunNat_real_of_nat)
done

ML
{*
val starsetNat_def = thm "starsetNat_def";

val NatStar_real_set = thm "NatStar_real_set";
val NatStar_empty_set = thm "NatStar_empty_set";
val NatStar_Un = thm "NatStar_Un";
val starsetNat_n_Un = thm "starsetNat_n_Un";
val InternalNatSets_Un = thm "InternalNatSets_Un";
val NatStar_Int = thm "NatStar_Int";
val starsetNat_n_Int = thm "starsetNat_n_Int";
val InternalNatSets_Int = thm "InternalNatSets_Int";
val NatStar_Compl = thm "NatStar_Compl";
val starsetNat_n_Compl = thm "starsetNat_n_Compl";
val InternalNatSets_Compl = thm "InternalNatSets_Compl";
val starsetNat_n_diff = thm "starsetNat_n_diff";
val InternalNatSets_diff = thm "InternalNatSets_diff";
val NatStar_subset = thm "NatStar_subset";
val NatStar_mem = thm "NatStar_mem";
val NatStar_hypreal_of_real_image_subset = thm "NatStar_hypreal_of_real_image_subset";
val NatStar_SHNat_subset = thm "NatStar_SHNat_subset";
val NatStar_hypreal_of_real_Int = thm "NatStar_hypreal_of_real_Int";
val starsetNat_starsetNat_n_eq = thm "starsetNat_starsetNat_n_eq";
val InternalNatSets_starsetNat_n = thm "InternalNatSets_starsetNat_n";
val InternalNatSets_UNIV_diff = thm "InternalNatSets_UNIV_diff";
val starsetNat_n_starsetNat = thm "starsetNat_n_starsetNat";
val starfunNat_n_starfunNat = thm "starfunNat_n_starfunNat";
val starfunNat2_n_starfunNat2 = thm "starfunNat2_n_starfunNat2";
val starfunNat_congruent = thm "starfunNat_congruent";
val starfunNat = thm "starfunNat";
val starfunNat2 = thm "starfunNat2";
val starfunNat_mult = thm "starfunNat_mult";
val starfunNat2_mult = thm "starfunNat2_mult";
val starfunNat_add = thm "starfunNat_add";
val starfunNat2_add = thm "starfunNat2_add";
val starfunNat2_minus = thm "starfunNat2_minus";
val starfunNatNat2_o = thm "starfunNatNat2_o";
val starfunNatNat2_o2 = thm "starfunNatNat2_o2";
val starfunNat2_o = thm "starfunNat2_o";
val starfun_stafunNat_o = thm "starfun_stafunNat_o";
val starfun_stafunNat_o2 = thm "starfun_stafunNat_o2";
val starfunNat_const_fun = thm "starfunNat_const_fun";
val starfunNat2_const_fun = thm "starfunNat2_const_fun";
val starfunNat_minus = thm "starfunNat_minus";
val starfunNat_inverse = thm "starfunNat_inverse";
val starfunNat_eq = thm "starfunNat_eq";
val starfunNat2_eq = thm "starfunNat2_eq";
val starfunNat_approx = thm "starfunNat_approx";
val starfun_le_mono = thm "starfun_le_mono";
val starfun_less_mono = thm "starfun_less_mono";
val starfunNat_shift_one = thm "starfunNat_shift_one";
val starfunNat_rabs = thm "starfunNat_rabs";
val starfunNat_pow = thm "starfunNat_pow";
val starfunNat_pow2 = thm "starfunNat_pow2";
val starfun_pow = thm "starfun_pow";
val starfunNat_real_of_nat = thm "starfunNat_real_of_nat";
val starfunNat_inverse_real_of_nat_eq = thm "starfunNat_inverse_real_of_nat_eq";
val starfunNat_n_congruent = thm "starfunNat_n_congruent";
val starfunNat_n = thm "starfunNat_n";
val starfunNat_n_mult = thm "starfunNat_n_mult";
val starfunNat_n_add = thm "starfunNat_n_add";
val starfunNat_n_add_minus = thm "starfunNat_n_add_minus";
val starfunNat_n_const_fun = thm "starfunNat_n_const_fun";
val starfunNat_n_minus = thm "starfunNat_n_minus";
val starfunNat_n_eq = thm "starfunNat_n_eq";
val starfun_eq_iff = thm "starfun_eq_iff";
val starfunNat_inverse_real_of_nat_Infinitesimal = thm "starfunNat_inverse_real_of_nat_Infinitesimal";
*}

end


