(*  Title       : NSPrimes.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2002 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*The Nonstandard Primes as an Extension of the Prime Numbers*}

theory NSPrimes
imports "~~/src/HOL/NumberTheory/Factorization" Complex_Main
begin

text{*These can be used to derive an alternative proof of the infinitude of
primes by considering a property of nonstandard sets.*}


constdefs
  hdvd  :: "[hypnat, hypnat] => bool"       (infixl "hdvd" 50)
   "(M::hypnat) hdvd N ==
	           \<exists>X Y. X: Rep_hypnat(M) & Y: Rep_hypnat(N) &
                               {n::nat. X n dvd Y n} : FreeUltrafilterNat"

constdefs
  starprime :: "hypnat set"
  "starprime == ( *sNat* prime)"

constdefs
  choicefun :: "'a set => 'a"
  "choicefun E == (@x. \<exists>X \<in> Pow(E) -{{}}. x : X)"

consts injf_max :: "nat => ('a::{order} set) => 'a"
primrec
  injf_max_zero: "injf_max 0 E = choicefun E"
  injf_max_Suc:  "injf_max (Suc n) E = choicefun({e. e:E & injf_max n E < e})"


text{*A "choice" theorem for ultrafilters, like almost everywhere
quantification*}

lemma UF_choice: "{n. \<exists>m. Q n m} : FreeUltrafilterNat
      ==> \<exists>f. {n. Q n (f n)} : FreeUltrafilterNat"
apply (rule_tac x = "%n. (@x. Q n x) " in exI)
apply (ultra, rule someI, auto)
done

lemma UF_if: "({n. P n} : FreeUltrafilterNat --> {n. Q n} : FreeUltrafilterNat) =
      ({n. P n --> Q n} : FreeUltrafilterNat)"
apply auto
apply ultra+
done

lemma UF_conj: "({n. P n} : FreeUltrafilterNat & {n. Q n} : FreeUltrafilterNat) =
      ({n. P n & Q n} : FreeUltrafilterNat)"
apply auto
apply ultra+
done

lemma UF_choice_ccontr: "(\<forall>f. {n. Q n (f n)} : FreeUltrafilterNat) =
      ({n. \<forall>m. Q n m} : FreeUltrafilterNat)"
apply auto
 prefer 2 apply ultra
apply (rule ccontr)
apply (rule contrapos_np)
 apply (erule_tac [2] asm_rl)
apply (simp (no_asm) add: FreeUltrafilterNat_Compl_iff1 Collect_neg_eq [symmetric])
apply (rule UF_choice, ultra)
done

lemma dvd_by_all: "\<forall>M. \<exists>N. 0 < N & (\<forall>m. 0 < m & (m::nat) <= M --> m dvd N)"
apply (rule allI)
apply (induct_tac "M", auto)
apply (rule_tac x = "N * (Suc n) " in exI)
apply (safe, force)
apply (drule le_imp_less_or_eq, erule disjE)
apply (force intro!: dvd_mult2)
apply (force intro!: dvd_mult)
done

lemmas dvd_by_all2 = dvd_by_all [THEN spec, standard]

lemma lemma_hypnat_P_EX: "(\<exists>(x::hypnat). P x) = (\<exists>f. P (Abs_hypnat(hypnatrel `` {f})))"
apply auto
apply (rule_tac z = x in eq_Abs_hypnat, auto)
done

lemma lemma_hypnat_P_ALL: "(\<forall>(x::hypnat). P x) = (\<forall>f. P (Abs_hypnat(hypnatrel `` {f})))"
apply auto
apply (rule_tac z = x in eq_Abs_hypnat, auto)
done

lemma hdvd:
      "(Abs_hypnat(hypnatrel``{%n. X n}) hdvd
            Abs_hypnat(hypnatrel``{%n. Y n})) =
       ({n. X n dvd Y n} : FreeUltrafilterNat)"
apply (unfold hdvd_def)
apply (auto, ultra)
done

lemma hypnat_of_nat_le_zero_iff: "(hypnat_of_nat n <= 0) = (n = 0)"
by (subst hypnat_of_nat_zero [symmetric], auto)
declare hypnat_of_nat_le_zero_iff [simp]


(* Goldblatt: Exercise 5.11(2) - p. 57 *)
lemma hdvd_by_all: "\<forall>M. \<exists>N. 0 < N & (\<forall>m. 0 < m & (m::hypnat) <= M --> m hdvd N)"
apply safe
apply (rule_tac z = M in eq_Abs_hypnat)
apply (auto simp add: lemma_hypnat_P_EX lemma_hypnat_P_ALL
              hypnat_zero_def hypnat_le hypnat_less hdvd)
apply (cut_tac dvd_by_all)
apply (subgoal_tac " \<forall>(n::nat) . \<exists>N. 0 < N & (\<forall>m. 0 < (m::nat) & m <= (x n) --> m dvd N)")
 prefer 2 apply blast
apply (erule thin_rl)
apply (drule choice, safe)
apply (rule_tac x = f in exI, auto, ultra)
apply auto
done

lemmas hdvd_by_all2 = hdvd_by_all [THEN spec, standard]

(* Goldblatt: Exercise 5.11(2) - p. 57 *)
lemma hypnat_dvd_all_hypnat_of_nat:
     "\<exists>(N::hypnat). 0 < N & (\<forall>n \<in> -{0::nat}. hypnat_of_nat(n) hdvd N)"
apply (cut_tac hdvd_by_all)
apply (drule_tac x = whn in spec, auto)
apply (rule exI, auto)
apply (drule_tac x = "hypnat_of_nat n" in spec)
apply (auto simp add: linorder_not_less hypnat_of_nat_zero_iff)
done


text{*The nonstandard extension of the set prime numbers consists of precisely
those hypernaturals exceeding 1 that have no nontrivial factors*}

(* Goldblatt: Exercise 5.11(3a) - p 57  *)
lemma starprime:
  "starprime = {p. 1 < p & (\<forall>m. m hdvd p --> m = 1 | m = p)}"
apply (unfold starprime_def prime_def)
apply (auto simp add: Collect_conj_eq NatStar_Int)
apply (rule_tac [!] z = x in eq_Abs_hypnat)
apply (rule_tac [2] z = m in eq_Abs_hypnat)
apply (auto simp add: hdvd hypnat_one_def hypnat_less lemma_hypnat_P_ALL starsetNat_def)
apply (drule bspec, drule_tac [2] bspec, auto)
apply (ultra, ultra)
apply (rule ccontr)
apply (drule FreeUltrafilterNat_Compl_mem)
apply (auto simp add: Collect_neg_eq [symmetric])
apply (drule UF_choice, auto)
apply (drule_tac x = f in spec, auto, ultra+)
done

lemma prime_two:  "2 : prime"
apply (unfold prime_def, auto)
apply (frule dvd_imp_le)
apply (auto dest: dvd_0_left)
apply (case_tac m, simp, arith)
done
declare prime_two [simp]

(* proof uses course-of-value induction *)
lemma prime_factor_exists [rule_format]: "Suc 0 < n --> (\<exists>k \<in> prime. k dvd n)"
apply (rule_tac n = n in nat_less_induct, auto)
apply (case_tac "n \<in> prime")
apply (rule_tac x = n in bexI, auto)
apply (drule conjI [THEN not_prime_ex_mk], auto)
apply (drule_tac x = m in spec, auto)
apply (rule_tac x = ka in bexI)
apply (auto intro: dvd_mult2)
done

(* Goldblatt Exercise 5.11(3b) - p 57  *)
lemma hyperprime_factor_exists [rule_format]: "1 < n ==> (\<exists>k \<in> starprime. k hdvd n)"
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: hypnat_one_def hypnat_less starprime_def
    lemma_hypnat_P_EX lemma_hypnat_P_ALL hdvd starsetNat_def Ball_def UF_if)
apply (rule_tac x = "%n. @y. y \<in> prime & y dvd x n" in exI, auto, ultra)
apply (drule sym, simp (no_asm_simp))
 prefer 2 apply ultra
apply (rule_tac [!] someI2_ex)
apply (auto dest!: prime_factor_exists)
done

(* behaves as expected! *)
lemma NatStar_insert: "( *sNat* insert x A) = insert (hypnat_of_nat x) ( *sNat* A)"
apply (auto simp add: starsetNat_def hypnat_of_nat_eq)
apply (rule_tac [!] z = xa in eq_Abs_hypnat, auto)
apply (drule_tac [!] bspec asm_rl, auto, ultra+)
done

(* Goldblatt Exercise 3.10(1) - p. 29 *)
lemma NatStar_hypnat_of_nat: "finite A ==> *sNat* A = hypnat_of_nat ` A"
apply (rule_tac P = "%x. *sNat* x = hypnat_of_nat ` x" in finite_induct)
apply (auto simp add: NatStar_insert)
done

(* proved elsewhere? *)
lemma FreeUltrafilterNat_singleton_not_mem: "{x} \<notin> FreeUltrafilterNat"
by (auto intro!: FreeUltrafilterNat_finite)
declare FreeUltrafilterNat_singleton_not_mem [simp]


subsection{*Another characterization of infinite set of natural numbers*}

lemma finite_nat_set_bounded: "finite N ==> \<exists>n. (\<forall>i \<in> N. i<(n::nat))"
apply (erule_tac F = N in finite_induct, auto)
apply (rule_tac x = "Suc n + x" in exI, auto)
done

lemma finite_nat_set_bounded_iff: "finite N = (\<exists>n. (\<forall>i \<in> N. i<(n::nat)))"
by (blast intro: finite_nat_set_bounded bounded_nat_set_is_finite)

lemma not_finite_nat_set_iff: "(~ finite N) = (\<forall>n. \<exists>i \<in> N. n <= (i::nat))"
by (auto simp add: finite_nat_set_bounded_iff le_def)

lemma bounded_nat_set_is_finite2: "(\<forall>i \<in> N. i<=(n::nat)) ==> finite N"
apply (rule finite_subset)
 apply (rule_tac [2] finite_atMost, auto)
done

lemma finite_nat_set_bounded2: "finite N ==> \<exists>n. (\<forall>i \<in> N. i<=(n::nat))"
apply (erule_tac F = N in finite_induct, auto)
apply (rule_tac x = "n + x" in exI, auto)
done

lemma finite_nat_set_bounded_iff2: "finite N = (\<exists>n. (\<forall>i \<in> N. i<=(n::nat)))"
by (blast intro: finite_nat_set_bounded2 bounded_nat_set_is_finite2)

lemma not_finite_nat_set_iff2: "(~ finite N) = (\<forall>n. \<exists>i \<in> N. n < (i::nat))"
by (auto simp add: finite_nat_set_bounded_iff2 le_def)


subsection{*An injective function cannot define an embedded natural number*}

lemma lemma_infinite_set_singleton: "\<forall>m n. m \<noteq> n --> f n \<noteq> f m
      ==>  {n. f n = N} = {} |  (\<exists>m. {n. f n = N} = {m})"
apply auto
apply (drule_tac x = x in spec, auto)
apply (subgoal_tac "\<forall>n. (f n = f x) = (x = n) ")
apply auto
done

lemma inj_fun_not_hypnat_in_SHNat: "inj f ==> Abs_hypnat(hypnatrel `` {f}) \<notin> Nats"
apply (auto simp add: SHNat_eq hypnat_of_nat_eq)
apply (subgoal_tac "\<forall>m n. m \<noteq> n --> f n \<noteq> f m", auto)
apply (drule_tac [2] injD)
prefer 2 apply assumption
apply (drule_tac N = N in lemma_infinite_set_singleton, auto)
done

lemma range_subset_mem_starsetNat:
   "range f <= A ==> Abs_hypnat(hypnatrel `` {f}) \<in> *sNat* A"
apply (unfold starsetNat_def, auto, ultra)
apply (drule_tac c = "f x" in subsetD)
apply (rule rangeI, auto)
done

(*--------------------------------------------------------------------------------*)
(* Gleason Proposition 11-5.5. pg 149, pg 155 (ex. 3) and pg. 360                 *)
(* Let E be a nonvoid ordered set with no maximal elements (note: effectively an  *)
(* infinite set if we take E = N (Nats)). Then there exists an order-preserving   *)
(* injection from N to E. Of course, (as some doofus will undoubtedly point out!  *)
(* :-)) can use notion of least element in proof (i.e. no need for choice) if     *)
(* dealing with nats as we have well-ordering property                            *)
(*--------------------------------------------------------------------------------*)

lemma lemmaPow3: "E \<noteq> {} ==> \<exists>x. \<exists>X \<in> (Pow E - {{}}). x: X"
by auto

lemma choicefun_mem_set: "E \<noteq> {} ==> choicefun E \<in> E"
apply (unfold choicefun_def)
apply (rule lemmaPow3 [THEN someI2_ex], auto)
done
declare choicefun_mem_set [simp]

lemma injf_max_mem_set: "[| E \<noteq>{}; \<forall>x. \<exists>y \<in> E. x < y |] ==> injf_max n E \<in> E"
apply (induct_tac "n", force)
apply (simp (no_asm) add: choicefun_def)
apply (rule lemmaPow3 [THEN someI2_ex], auto)
done

lemma injf_max_order_preserving: "\<forall>x. \<exists>y \<in> E. x < y ==> injf_max n E < injf_max (Suc n) E"
apply (simp (no_asm) add: choicefun_def)
apply (rule lemmaPow3 [THEN someI2_ex], auto)
done

lemma injf_max_order_preserving2: "\<forall>x. \<exists>y \<in> E. x < y
      ==> \<forall>n m. m < n --> injf_max m E < injf_max n E"
apply (rule allI)
apply (induct_tac "n", auto)
apply (simp (no_asm) add: choicefun_def)
apply (rule lemmaPow3 [THEN someI2_ex])
apply (auto simp add: less_Suc_eq)
apply (drule_tac x = m in spec)
apply (drule subsetD, auto)
apply (drule_tac x = "injf_max m E" in order_less_trans, auto)
done

lemma inj_injf_max: "\<forall>x. \<exists>y \<in> E. x < y ==> inj (%n. injf_max n E)"
apply (rule inj_onI)
apply (rule ccontr, auto)
apply (drule injf_max_order_preserving2)
apply (cut_tac m = x and n = y in less_linear, auto)
apply (auto dest!: spec)
done

lemma infinite_set_has_order_preserving_inj:
     "[| (E::('a::{order} set)) \<noteq> {}; \<forall>x. \<exists>y \<in> E. x < y |]
      ==> \<exists>f. range f <= E & inj (f::nat => 'a) & (\<forall>m. f m < f(Suc m))"
apply (rule_tac x = "%n. injf_max n E" in exI, safe)
apply (rule injf_max_mem_set)
apply (rule_tac [3] inj_injf_max)
apply (rule_tac [4] injf_max_order_preserving, auto)
done

text{*Only need the existence of an injective function from N to A for proof*}

lemma hypnat_infinite_has_nonstandard:
     "~ finite A ==> hypnat_of_nat ` A < ( *sNat* A)"
apply auto
apply (rule subsetD)
apply (rule NatStar_hypreal_of_real_image_subset, auto)
apply (subgoal_tac "A \<noteq> {}")
prefer 2 apply force
apply (drule infinite_set_has_order_preserving_inj)
apply (erule not_finite_nat_set_iff2 [THEN iffD1], auto)
apply (drule inj_fun_not_hypnat_in_SHNat)
apply (drule range_subset_mem_starsetNat)
apply (auto simp add: SHNat_eq)
done

lemma starsetNat_eq_hypnat_of_nat_image_finite: "*sNat* A =  hypnat_of_nat ` A ==> finite A"
apply (rule ccontr)
apply (auto dest: hypnat_infinite_has_nonstandard)
done

lemma finite_starsetNat_iff: "( *sNat* A = hypnat_of_nat ` A) = (finite A)"
by (blast intro!: starsetNat_eq_hypnat_of_nat_image_finite NatStar_hypnat_of_nat)

lemma hypnat_infinite_has_nonstandard_iff: "(~ finite A) = (hypnat_of_nat ` A < *sNat* A)"
apply (rule iffI)
apply (blast intro!: hypnat_infinite_has_nonstandard)
apply (auto simp add: finite_starsetNat_iff [symmetric])
done

subsection{*Existence of Infinitely Many Primes: a Nonstandard Proof*}

lemma lemma_not_dvd_hypnat_one: "~ (\<forall>n \<in> - {0}. hypnat_of_nat n hdvd 1)"
apply auto
apply (rule_tac x = 2 in bexI)
apply (auto simp add: hypnat_of_nat_eq hypnat_one_def hdvd dvd_def)
done
declare lemma_not_dvd_hypnat_one [simp]

lemma lemma_not_dvd_hypnat_one2: "\<exists>n \<in> - {0}. ~ hypnat_of_nat n hdvd 1"
apply (cut_tac lemma_not_dvd_hypnat_one)
apply (auto simp del: lemma_not_dvd_hypnat_one)
done
declare lemma_not_dvd_hypnat_one2 [simp]

(* not needed here *)
lemma hypnat_gt_zero_gt_one:
  "[| 0 < (N::hypnat); N \<noteq> 1 |] ==> 1 < N"
apply (unfold hypnat_zero_def hypnat_one_def)
apply (rule_tac z = N in eq_Abs_hypnat)
apply (auto simp add: hypnat_less, ultra)
done

lemma hypnat_add_one_gt_one:
    "0 < N ==> 1 < (N::hypnat) + 1"
apply (unfold hypnat_zero_def hypnat_one_def)
apply (rule_tac z = N in eq_Abs_hypnat)
apply (auto simp add: hypnat_less hypnat_add)
done

lemma zero_not_prime: "0 \<notin> prime"
apply safe
apply (drule prime_g_zero, auto)
done
declare zero_not_prime [simp]

lemma hypnat_of_nat_zero_not_prime: "hypnat_of_nat 0 \<notin> starprime"
by (auto intro!: bexI simp add: starprime_def starsetNat_def hypnat_of_nat_eq)
declare hypnat_of_nat_zero_not_prime [simp]

lemma hypnat_zero_not_prime:
   "0 \<notin> starprime"
apply (unfold starprime_def starsetNat_def hypnat_zero_def)
apply (auto intro!: bexI)
done
declare hypnat_zero_not_prime [simp]

lemma one_not_prime: "1 \<notin> prime"
apply safe
apply (drule prime_g_one, auto)
done
declare one_not_prime [simp]

lemma one_not_prime2: "Suc 0 \<notin> prime"
apply safe
apply (drule prime_g_one, auto)
done
declare one_not_prime2 [simp]

lemma hypnat_of_nat_one_not_prime: "hypnat_of_nat 1 \<notin> starprime"
by (auto intro!: bexI simp add: starprime_def starsetNat_def hypnat_of_nat_eq)
declare hypnat_of_nat_one_not_prime [simp]

lemma hypnat_one_not_prime: "1 \<notin> starprime"
apply (unfold starprime_def starsetNat_def hypnat_one_def)
apply (auto intro!: bexI)
done
declare hypnat_one_not_prime [simp]

lemma hdvd_diff: "[| k hdvd m; k hdvd n |] ==> k hdvd (m - n)"
apply (rule_tac z = k in eq_Abs_hypnat)
apply (rule_tac z = m in eq_Abs_hypnat)
apply (rule_tac z = n in eq_Abs_hypnat)
apply (auto simp add: hdvd hypnat_minus, ultra)
apply (blast intro: dvd_diff)
done

lemma dvd_one_eq_one: "x dvd (1::nat) ==> x = 1"
by (unfold dvd_def, auto)

lemma hdvd_one_eq_one: "x hdvd 1 ==> x = 1"
apply (unfold hypnat_one_def)
apply (rule_tac z = x in eq_Abs_hypnat)
apply (auto simp add: hdvd)
done

theorem not_finite_prime: "~ finite prime"
apply (rule hypnat_infinite_has_nonstandard_iff [THEN iffD2])
apply (cut_tac hypnat_dvd_all_hypnat_of_nat)
apply (erule exE)
apply (erule conjE)
apply (subgoal_tac "1 < N + 1")
prefer 2 apply (blast intro: hypnat_add_one_gt_one)
apply (drule hyperprime_factor_exists)
apply (auto intro: NatStar_mem)
apply (subgoal_tac "k \<notin> hypnat_of_nat ` prime")
apply (force simp add: starprime_def, safe)
apply (drule_tac x = x in bspec)
apply (rule ccontr, simp)
apply (drule hdvd_diff, assumption)
apply (auto dest: hdvd_one_eq_one)
done

end
