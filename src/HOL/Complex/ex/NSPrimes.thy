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
   "(M::hypnat) hdvd N == ( *p2* (op dvd)) M N"
(*
   "(M::hypnat) hdvd N ==
	           \<exists>X Y. X: Rep_hypnat(M) & Y: Rep_hypnat(N) &
                               {n::nat. X n dvd Y n} : FreeUltrafilterNat"
*)
constdefs
  starprime :: "hypnat set"
  "starprime == ( *s* {p. prime p})"

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

lemma lemma_hypnat_P_EX: "(\<exists>(x::hypnat). P x) = (\<exists>f. P (star_n f))"
apply auto
apply (rule_tac x = x in star_cases, auto)
done

lemma lemma_hypnat_P_ALL: "(\<forall>(x::hypnat). P x) = (\<forall>f. P (star_n f))"
apply auto
apply (rule_tac x = x in star_cases, auto)
done

lemma hdvd:
      "(star_n X hdvd star_n Y) =
       ({n. X n dvd Y n} : FreeUltrafilterNat)"
by (simp add: hdvd_def starP2)

lemma hypnat_of_nat_le_zero_iff: "(hypnat_of_nat n <= 0) = (n = 0)"
by (subst hypnat_of_nat_zero [symmetric], auto)
declare hypnat_of_nat_le_zero_iff [simp]


(* Goldblatt: Exercise 5.11(2) - p. 57 *)
lemma hdvd_by_all: "\<forall>M. \<exists>N. 0 < N & (\<forall>m. 0 < m & (m::hypnat) <= M --> m hdvd N)"
by (unfold hdvd_def, transfer, rule dvd_by_all)

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
apply (unfold hdvd_def, transfer, rule refl)
done

lemma prime_two:  "prime 2"
apply (unfold prime_def, auto)
apply (frule dvd_imp_le)
apply (auto dest: dvd_0_left)
apply (case_tac m, simp, arith)
done
declare prime_two [simp]

(* proof uses course-of-value induction *)
lemma prime_factor_exists [rule_format]: "Suc 0 < n --> (\<exists>k. prime k & k dvd n)"
apply (rule_tac n = n in nat_less_induct, auto)
apply (case_tac "prime n")
apply (rule_tac x = n in exI, auto)
apply (drule conjI [THEN not_prime_ex_mk], auto)
apply (drule_tac x = m in spec, auto)
apply (rule_tac x = ka in exI)
apply (auto intro: dvd_mult2)
done

(* Goldblatt Exercise 5.11(3b) - p 57  *)
lemma hyperprime_factor_exists [rule_format]:
  "!!n. 1 < n ==> (\<exists>k \<in> starprime. k hdvd n)"
apply (unfold starprime_def hdvd_def)
apply (transfer prime_def)
apply (simp add: prime_factor_exists)
done

(* Goldblatt Exercise 3.10(1) - p. 29 *)
lemma NatStar_hypnat_of_nat: "finite A ==> *s* A = hypnat_of_nat ` A"
apply (rule_tac P = "%x. *s* x = hypnat_of_nat ` x" in finite_induct)
apply auto
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

lemma inj_fun_not_hypnat_in_SHNat: "inj (f::nat=>nat) ==> star_n f \<notin> Nats"
apply (auto simp add: SHNat_eq hypnat_of_nat_eq star_n_eq_iff)
apply (subgoal_tac "\<forall>m n. m \<noteq> n --> f n \<noteq> f m", auto)
apply (drule_tac [2] injD)
prefer 2 apply assumption
apply (drule_tac N = N in lemma_infinite_set_singleton, auto)
done

lemma range_subset_mem_starsetNat:
   "range f <= A ==> star_n f \<in> *s* A"
apply (simp add: Iset_of_def star_of_def Iset_star_n)
apply (subgoal_tac "\<forall>n. f n \<in> A", auto)
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
     "~ finite A ==> hypnat_of_nat ` A < ( *s* A)"
apply auto
apply (rule subsetD)
apply (rule STAR_star_of_image_subset, auto)
apply (subgoal_tac "A \<noteq> {}")
prefer 2 apply force
apply (drule infinite_set_has_order_preserving_inj)
apply (erule not_finite_nat_set_iff2 [THEN iffD1], auto)
apply (drule inj_fun_not_hypnat_in_SHNat)
apply (drule range_subset_mem_starsetNat)
apply (auto simp add: SHNat_eq)
done

lemma starsetNat_eq_hypnat_of_nat_image_finite: "*s* A =  hypnat_of_nat ` A ==> finite A"
apply (rule ccontr)
apply (auto dest: hypnat_infinite_has_nonstandard)
done

lemma finite_starsetNat_iff: "( *s* A = hypnat_of_nat ` A) = (finite A)"
by (blast intro!: starsetNat_eq_hypnat_of_nat_image_finite NatStar_hypnat_of_nat)

lemma hypnat_infinite_has_nonstandard_iff: "(~ finite A) = (hypnat_of_nat ` A < *s* A)"
apply (rule iffI)
apply (blast intro!: hypnat_infinite_has_nonstandard)
apply (auto simp add: finite_starsetNat_iff [symmetric])
done

subsection{*Existence of Infinitely Many Primes: a Nonstandard Proof*}

lemma lemma_not_dvd_hypnat_one: "~ (\<forall>n \<in> - {0}. hypnat_of_nat n hdvd 1)"
apply auto
apply (rule_tac x = 2 in bexI)
apply (unfold hdvd_def, transfer, auto)
done
declare lemma_not_dvd_hypnat_one [simp]

lemma lemma_not_dvd_hypnat_one2: "\<exists>n \<in> - {0}. ~ hypnat_of_nat n hdvd 1"
apply (cut_tac lemma_not_dvd_hypnat_one)
apply (auto simp del: lemma_not_dvd_hypnat_one)
done
declare lemma_not_dvd_hypnat_one2 [simp]

(* not needed here *)
lemma hypnat_gt_zero_gt_one:
  "!!N. [| 0 < (N::hypnat); N \<noteq> 1 |] ==> 1 < N"
by (transfer, simp)

lemma hypnat_add_one_gt_one:
    "!!N. 0 < N ==> 1 < (N::hypnat) + 1"
by (transfer, simp)

lemma zero_not_prime: "\<not> prime 0"
apply safe
apply (drule prime_g_zero, auto)
done
declare zero_not_prime [simp]

lemma hypnat_of_nat_zero_not_prime: "hypnat_of_nat 0 \<notin> starprime"
by (unfold starprime_def, transfer prime_def, simp)
declare hypnat_of_nat_zero_not_prime [simp]

lemma hypnat_zero_not_prime:
   "0 \<notin> starprime"
by (cut_tac hypnat_of_nat_zero_not_prime, simp)
declare hypnat_zero_not_prime [simp]

lemma one_not_prime: "\<not> prime 1"
apply safe
apply (drule prime_g_one, auto)
done
declare one_not_prime [simp]

lemma one_not_prime2: "\<not> prime(Suc 0)"
apply safe
apply (drule prime_g_one, auto)
done
declare one_not_prime2 [simp]

lemma hypnat_of_nat_one_not_prime: "hypnat_of_nat 1 \<notin> starprime"
by (unfold starprime_def, transfer prime_def, simp)
declare hypnat_of_nat_one_not_prime [simp]

lemma hypnat_one_not_prime: "1 \<notin> starprime"
by (cut_tac hypnat_of_nat_one_not_prime, simp)
declare hypnat_one_not_prime [simp]

lemma hdvd_diff: "!!k m n. [| k hdvd m; k hdvd n |] ==> k hdvd (m - n)"
by (unfold hdvd_def, transfer, rule dvd_diff)

lemma dvd_one_eq_one: "x dvd (1::nat) ==> x = 1"
by (unfold dvd_def, auto)

lemma hdvd_one_eq_one: "!!x. x hdvd 1 ==> x = 1"
by (unfold hdvd_def, transfer, rule dvd_one_eq_one)

theorem not_finite_prime: "~ finite {p. prime p}"
apply (rule hypnat_infinite_has_nonstandard_iff [THEN iffD2])
apply (cut_tac hypnat_dvd_all_hypnat_of_nat)
apply (erule exE)
apply (erule conjE)
apply (subgoal_tac "1 < N + 1")
prefer 2 apply (blast intro: hypnat_add_one_gt_one)
apply (drule hyperprime_factor_exists)
apply (auto intro: STAR_mem)
apply (subgoal_tac "k \<notin> hypnat_of_nat ` {p. prime p}")
apply (force simp add: starprime_def, safe)
apply (drule_tac x = x in bspec)
apply (rule ccontr, simp)
apply (drule hdvd_diff, assumption)
apply (auto dest: hdvd_one_eq_one)
done

end
