(*  Title:       NSInduct.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
*)

header{*Nonstandard Characterization of Induction*}

theory NSInduct =  Complex:

constdefs

  starPNat :: "(nat => bool) => hypnat => bool"  ("*pNat* _" [80] 80)
  "*pNat* P == (%x. \<exists>X. (X \<in> Rep_hypnat(x) &
                      {n. P(X n)} \<in> FreeUltrafilterNat))"


  starPNat2 :: "(nat => nat => bool) => hypnat =>hypnat => bool"
               ("*pNat2* _" [80] 80)
  "*pNat2* P == (%x y. \<exists>X. \<exists>Y. (X \<in> Rep_hypnat(x) & Y \<in> Rep_hypnat(y) &
                      {n. P(X n) (Y n)} \<in> FreeUltrafilterNat))"

  hSuc :: "hypnat => hypnat"
  "hSuc n == n + 1"


lemma starPNat:
     "(( *pNat* P) (Abs_hypnat(hypnatrel``{%n. X n}))) =
      ({n. P (X n)} \<in> FreeUltrafilterNat)"
by (auto simp add: starPNat_def, ultra)

lemma starPNat_hypnat_of_nat [simp]: "( *pNat* P) (hypnat_of_nat n) = P n"
by (auto simp add: starPNat hypnat_of_nat_eq)

lemma hypnat_induct_obj:
    "(( *pNat* P) 0 &
            (\<forall>n. ( *pNat* P)(n) --> ( *pNat* P)(n + 1)))
       --> ( *pNat* P)(n)"
apply (rule eq_Abs_hypnat [of n])
apply (auto simp add: hypnat_zero_def hypnat_one_def starPNat, ultra)
apply (erule nat_induct)
apply (drule_tac x = "hypnat_of_nat n" in spec)
apply (rule ccontr)
apply (auto simp add: starPNat hypnat_of_nat_eq hypnat_add)
done

lemma hypnat_induct:
  "[| ( *pNat* P) 0;
      !!n. ( *pNat* P)(n) ==> ( *pNat* P)(n + 1)|]
     ==> ( *pNat* P)(n)"
by (insert hypnat_induct_obj [of P n], auto)

lemma starPNat2:
"(( *pNat2* P) (Abs_hypnat(hypnatrel``{%n. X n}))
             (Abs_hypnat(hypnatrel``{%n. Y n}))) =
      ({n. P (X n) (Y n)} \<in> FreeUltrafilterNat)"
by (auto simp add: starPNat2_def, ultra)

lemma starPNat2_eq_iff: "( *pNat2* (op =)) = (op =)"
apply (simp add: starPNat2_def)
apply (rule ext)
apply (rule ext)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (rule_tac z = y in eq_Abs_hypnat)
apply (auto, ultra)
done

lemma starPNat2_eq_iff2: "( *pNat2* (%x y. x = y)) X Y = (X = Y)"
by (simp add: starPNat2_eq_iff)

lemma lemma_hyp: "(\<exists>h. P(h::hypnat)) = (\<exists>x. P(Abs_hypnat(hypnatrel `` {x})))"
apply auto
apply (rule_tac z = h in eq_Abs_hypnat, auto)
done

lemma hSuc_not_zero [iff]: "hSuc m \<noteq> 0"
by (simp add: hSuc_def)

lemmas zero_not_hSuc = hSuc_not_zero [THEN not_sym, standard, iff]

lemma hSuc_hSuc_eq [iff]: "(hSuc m = hSuc n) = (m = n)"
by (simp add: hSuc_def hypnat_one_def)

lemma nonempty_nat_set_Least_mem: "c \<in> (S :: nat set) ==> (LEAST n. n  \<in> S)  \<in> S"
by (erule LeastI)

lemma nonempty_InternalNatSet_has_least:
    "[| S \<in> InternalNatSets; S \<noteq> {} |] ==> \<exists>n \<in> S. \<forall>m \<in> S. n \<le> m"
apply (auto simp add: InternalNatSets_def starsetNat_n_def lemma_hyp)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (auto dest!: bspec simp add: hypnat_le)
apply (drule_tac x = "%m. LEAST n. n \<in> As m" in spec, auto)
apply (ultra, force dest: nonempty_nat_set_Least_mem)
apply (drule_tac x = x in bspec, auto)
apply (ultra, auto intro: Least_le)
done

text{* Goldblatt page 129 Thm 11.3.2*}
lemma internal_induct:
     "[| X \<in> InternalNatSets; 0 \<in> X; \<forall>n. n \<in> X --> n + 1 \<in> X |]
      ==> X = (UNIV:: hypnat set)"
apply (rule ccontr)
apply (frule InternalNatSets_Compl)
apply (drule_tac S = "- X" in nonempty_InternalNatSet_has_least, auto)
apply (subgoal_tac "1 \<le> n")
apply (drule_tac x = "n - 1" in bspec, safe)
apply (drule_tac x = "n - 1" in spec)
apply (drule_tac [2] c = 1 and a = n in add_right_mono)
apply (auto simp add: linorder_not_less [symmetric] iff del: hypnat_neq0_conv)
done

ML
{*
val starPNat = thm "starPNat";
val starPNat_hypnat_of_nat = thm "starPNat_hypnat_of_nat";
val hypnat_induct = thm "hypnat_induct";
val starPNat2 = thm "starPNat2";
val starPNat2_eq_iff = thm "starPNat2_eq_iff";
val starPNat2_eq_iff2 = thm "starPNat2_eq_iff2";
val hSuc_not_zero = thm "hSuc_not_zero";
val zero_not_hSuc = thms "zero_not_hSuc";
val hSuc_hSuc_eq = thm "hSuc_hSuc_eq";
val nonempty_nat_set_Least_mem = thm "nonempty_nat_set_Least_mem";
val nonempty_InternalNatSet_has_least = thm "nonempty_InternalNatSet_has_least";
val internal_induct = thm "internal_induct";
*}

end
