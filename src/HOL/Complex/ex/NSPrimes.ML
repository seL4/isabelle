(*  Title       : NSPrimes.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2002 University of Edinburgh
    Description : The nonstandard primes as an extension of 
                  the prime numbers
*)

(*--------------------------------------------------------------*) 
(* A "choice" theorem for ultrafilters cf. almost everywhere    *)
(* quantification                                               *)
(*--------------------------------------------------------------*) 
    
Goal "{n. EX m. Q n m} : FreeUltrafilterNat \
\     ==> EX f. {n. Q n (f n)} : FreeUltrafilterNat";
by (res_inst_tac [("x","%n. (@x. Q n x)")] exI 1);
by (Ultra_tac 1 THEN rtac someI 1 THEN Auto_tac);
qed "UF_choice";

Goal "({n. P n} : FreeUltrafilterNat --> {n. Q n} : FreeUltrafilterNat) = \
\     ({n. P n --> Q n} : FreeUltrafilterNat)";
by Auto_tac;
by (ALLGOALS(Ultra_tac));
qed "UF_if";

Goal "({n. P n} : FreeUltrafilterNat & {n. Q n} : FreeUltrafilterNat) = \
\     ({n. P n & Q n} : FreeUltrafilterNat)";
by Auto_tac;
by (ALLGOALS(Ultra_tac));
qed "UF_conj";

Goal "(ALL f. {n. Q n (f n)} : FreeUltrafilterNat) = \
\     ({n. ALL m. Q n m} : FreeUltrafilterNat)";
by Auto_tac;
by (Ultra_tac 2);
by (rtac ccontr 1);
by (rtac swap 1 THEN assume_tac 2);
by (simp_tac (simpset() addsimps [FreeUltrafilterNat_Compl_iff1,
    CLAIM "-{n. Q n} = {n. ~ Q n}"]) 1);
by (rtac UF_choice 1);
by (Ultra_tac 1 THEN Auto_tac);
qed "UF_choice_ccontr";

Goal "ALL M. EX N. 0 < N & (ALL m. 0 < m & (m::nat) <= M --> m dvd N)";
by (rtac allI 1);
by (induct_tac "M" 1);
by Auto_tac;
by (res_inst_tac [("x","N * (Suc n)")] exI 1);
by (Step_tac 1 THEN Force_tac 1);
by (dtac le_imp_less_or_eq 1 THEN etac disjE 1);
by (force_tac (claset() addSIs [dvd_mult2],simpset()) 1);
by (force_tac (claset() addSIs [dvd_mult],simpset()) 1);
qed "dvd_by_all";

bind_thm ("dvd_by_all2",dvd_by_all RS spec);

Goal "(EX (x::hypnat). P x) = (EX f. P (Abs_hypnat(hypnatrel `` {f})))";
by Auto_tac;
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by Auto_tac;
qed "lemma_hypnat_P_EX";

Goal "(ALL (x::hypnat). P x) = (ALL f. P (Abs_hypnat(hypnatrel `` {f})))";
by Auto_tac;
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by Auto_tac;
qed "lemma_hypnat_P_ALL";

Goalw [hdvd_def]
      "(Abs_hypnat(hypnatrel``{%n. X n}) hdvd \
\           Abs_hypnat(hypnatrel``{%n. Y n})) = \
\      ({n. X n dvd Y n} : FreeUltrafilterNat)";
by (Auto_tac THEN Ultra_tac 1);
qed "hdvd";

Goal "(hypnat_of_nat n <= 0) = (n = 0)";
by (stac (hypnat_of_nat_zero RS sym) 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_of_nat_le_iff RS sym]));
qed "hypnat_of_nat_le_zero_iff";
Addsimps [hypnat_of_nat_le_zero_iff];


(* Goldblatt: Exercise 5.11(2) - p. 57 *)
Goal "ALL M. EX N. 0 < N & (ALL m. 0 < m & (m::hypnat) <= M --> m hdvd N)";
by (Step_tac 1);
by (res_inst_tac [("z","M")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [lemma_hypnat_P_EX,
    lemma_hypnat_P_ALL,hypnat_zero_def,hypnat_le,hypnat_less,hdvd]));
by (cut_facts_tac [dvd_by_all] 1);
by (dtac (CLAIM "(ALL (M::nat). EX N. 0 < N & (ALL m. 0 < m & m <= M \
\                               --> m dvd N)) \
\                ==> ALL (n::nat). EX N. 0 < N & (ALL m. 0 < (m::nat) & m <= (x n) \
\                                  --> m dvd N)") 1);
by (dtac choice 1);
by (Step_tac 1);
by (res_inst_tac [("x","f")] exI 1);
by Auto_tac;
by (ALLGOALS(Ultra_tac));
by Auto_tac;
qed "hdvd_by_all";

bind_thm ("hdvd_by_all2",hdvd_by_all RS spec);

(* Goldblatt: Exercise 5.11(2) - p. 57 *)
Goal "EX (N::hypnat). 0 < N & (ALL n : - {0::nat}. hypnat_of_nat(n) hdvd N)"; 
by (cut_facts_tac [hdvd_by_all] 1);
by (dres_inst_tac [("x","whn")] spec 1);
by Auto_tac;
by (rtac exI 1 THEN Auto_tac);
by (dres_inst_tac [("x","hypnat_of_nat n")] spec 1);
by (auto_tac (claset(),simpset() addsimps [symmetric hypnat_le_def,
    hypnat_of_nat_zero_iff]));
qed "hypnat_dvd_all_hypnat_of_nat";


(*--------------------------------------------------------------*)
(* the nonstandard extension of the set prime numbers consists  *)
(* of precisely those hypernaturals > 1 that have no nontrivial *)
(* factors                                                      *)
(*--------------------------------------------------------------*) 

(* Goldblatt: Exercise 5.11(3a) - p 57  *)
Goalw [starprime_def,thm "prime_def"]
  "starprime = {p. 1 < p & (ALL m. m hdvd p --> m = 1 | m = p)}";
by (auto_tac (claset(),simpset() addsimps 
    [CLAIM "{p. Q(p) & R(p)} = {p. Q(p)} Int {p. R(p)}",NatStar_Int]));
by (ALLGOALS(res_inst_tac [("z","x")] eq_Abs_hypnat));
by (res_inst_tac [("z","m")] eq_Abs_hypnat 2);
by (auto_tac (claset(),simpset() addsimps [hdvd,hypnat_one_def,hypnat_less,
    lemma_hypnat_P_ALL,starsetNat_def]));
by (dtac bspec 1 THEN dtac bspec 2 THEN Auto_tac);
by (Ultra_tac 1 THEN Ultra_tac 1); 
by (rtac ccontr 1);
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (auto_tac (claset(),simpset() addsimps [CLAIM "- {p. Q p} = {p. ~ Q p}"]));
by (dtac UF_choice 1 THEN Auto_tac);
by (dres_inst_tac [("x","f")] spec 1 THEN Auto_tac);
by (ALLGOALS(Ultra_tac));
qed "starprime";

Goalw [thm "prime_def"] "2 : prime";
by Auto_tac;
by (ftac dvd_imp_le 1);
by (auto_tac (claset() addDs [dvd_0_left],simpset() addsimps 
    [ARITH_PROVE "(m <= (2::nat)) = (m = 0 | m = 1 | m = 2)"]));
qed "prime_two";
Addsimps [prime_two];

(* proof uses course-of-value induction *)
Goal "Suc 0 < n --> (EX k : prime. k dvd n)";
by (res_inst_tac [("n","n")] nat_less_induct 1);
by Auto_tac;
by (case_tac "n : prime" 1);
by (res_inst_tac [("x","n")] bexI 1 THEN Auto_tac);
by (dtac (conjI RS (thm "not_prime_ex_mk")) 1 THEN Auto_tac);
by (dres_inst_tac [("x","m")] spec 1 THEN Auto_tac);
by (res_inst_tac [("x","ka")] bexI 1);
by (auto_tac (claset() addIs [dvd_mult2],simpset()));
qed_spec_mp "prime_factor_exists";

(* Goldblatt Exercise 5.11(3b) - p 57  *)
Goal "1 < n ==> (EX k : starprime. k hdvd n)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_one_def,
    hypnat_less,starprime_def,lemma_hypnat_P_EX,lemma_hypnat_P_ALL,
    hdvd,starsetNat_def,CLAIM "(ALL X: S. P X) = (ALL X. X : S --> P X)",
    UF_if]));
by (res_inst_tac [("x","%n. @y. y : prime & y dvd x n")] exI 1);
by Auto_tac;
by (ALLGOALS (Ultra_tac));
by (dtac sym 1 THEN Asm_simp_tac 1);
by (ALLGOALS(rtac someI2_ex));
by (auto_tac (claset() addSDs [prime_factor_exists],simpset()));
qed_spec_mp "hyperprime_factor_exists";

(* behaves as expected! *)
Goal "( *sNat* insert x A) = insert (hypnat_of_nat x) ( *sNat* A)";
by (auto_tac (claset(),simpset() addsimps [starsetNat_def,
    hypnat_of_nat_def]));
by (ALLGOALS(res_inst_tac [("z","xa")] eq_Abs_hypnat));
by Auto_tac;
by (TRYALL(dtac bspec));
by Auto_tac;
by (ALLGOALS(Ultra_tac));
qed "NatStar_insert";

(* Goldblatt Exercise 3.10(1) - p. 29 *)
Goal "finite A ==> *sNat* A = hypnat_of_nat ` A";
by (res_inst_tac [("P","%x. *sNat* x = hypnat_of_nat ` x")] finite_induct 1);
by (auto_tac (claset(),simpset() addsimps [NatStar_insert]));
qed "NatStar_hypnat_of_nat";

(* proved elsewhere? *)
Goal "{x} ~: FreeUltrafilterNat";
by (auto_tac (claset() addSIs [FreeUltrafilterNat_finite],simpset()));
qed "FreeUltrafilterNat_singleton_not_mem";
Addsimps [FreeUltrafilterNat_singleton_not_mem];

(*-------------------------------------------------------------------------------*)
(* Another characterization of infinite set of natural numbers                   *)
(*-------------------------------------------------------------------------------*)

Goal "finite N ==> EX n. (ALL i:N. i<(n::nat))";
by (eres_inst_tac [("F","N")] finite_induct 1);
by Auto_tac;
by (res_inst_tac [("x","Suc n + x")] exI 1);
by Auto_tac;
qed "finite_nat_set_bounded";

Goal "finite N = (EX n. (ALL i:N. i<(n::nat)))";
by (blast_tac (claset() addIs [finite_nat_set_bounded,
    bounded_nat_set_is_finite]) 1);
qed "finite_nat_set_bounded_iff";

Goal "(~ finite N) = (ALL n. EX i:N. n <= (i::nat))";
by (auto_tac (claset(),simpset() addsimps [finite_nat_set_bounded_iff,
    le_def]));
qed "not_finite_nat_set_iff";

Goal "(ALL i:N. i<=(n::nat)) ==> finite N";
by (rtac finite_subset 1);
 by (rtac finite_atMost 2);
by Auto_tac;
qed "bounded_nat_set_is_finite2";

Goal "finite N ==> EX n. (ALL i:N. i<=(n::nat))";
by (eres_inst_tac [("F","N")] finite_induct 1);
by Auto_tac;
by (res_inst_tac [("x","n + x")] exI 1);
by Auto_tac;
qed "finite_nat_set_bounded2";

Goal "finite N = (EX n. (ALL i:N. i<=(n::nat)))";
by (blast_tac (claset() addIs [finite_nat_set_bounded2,
    bounded_nat_set_is_finite2]) 1);
qed "finite_nat_set_bounded_iff2";

Goal "(~ finite N) = (ALL n. EX i:N. n < (i::nat))";
by (auto_tac (claset(),simpset() addsimps [finite_nat_set_bounded_iff2,
    le_def]));
qed "not_finite_nat_set_iff2";

(*-------------------------------------------------------------------------------*)
(* An injective function cannot define an embedded natural number                *)
(*-------------------------------------------------------------------------------*)

Goal "ALL m n. m ~= n --> f n ~= f m \
\     ==>  {n. f n = N} = {} |  (EX m. {n. f n = N} = {m})";
by Auto_tac;
by (dres_inst_tac [("x","x")] spec 1 THEN Auto_tac); 
by (subgoal_tac "ALL n. (f n = f x) = (x = n)" 1);
by Auto_tac;
qed "lemma_infinite_set_singleton";

Goalw [SHNat_def,hypnat_of_nat_def] 
   "inj f ==> Abs_hypnat(hypnatrel `` {f}) ~: Nats";
by Auto_tac;
by (subgoal_tac "ALL m n. m ~= n --> f n ~= f m" 1);
by Auto_tac;
by (dtac injD 2);
by (assume_tac 2 THEN Force_tac 2);
by (dres_inst_tac[("N","N")] lemma_infinite_set_singleton 1);
by Auto_tac;
qed "inj_fun_not_hypnat_in_SHNat";

Goalw [starsetNat_def] 
   "range f <= A ==> Abs_hypnat(hypnatrel `` {f}) : *sNat* A";
by Auto_tac;
by (Ultra_tac 1);
by (dres_inst_tac [("c","f x")] subsetD 1);
by (rtac rangeI 1);
by Auto_tac;
qed "range_subset_mem_starsetNat";

(*--------------------------------------------------------------------------------*)
(* Gleason Proposition 11-5.5. pg 149, pg 155 (ex. 3) and pg. 360                 *)
(* Let E be a nonvoid ordered set with no maximal elements (note: effectively an  *) 
(* infinite set if we take E = N (Nats)). Then there exists an order-preserving   *) 
(* injection from N to E. Of course, (as some doofus will undoubtedly point out!  *)
(* :-)) can use notion of least element in proof (i.e. no need for choice) if     *)
(* dealing with nats as we have well-ordering property                            *) 
(*--------------------------------------------------------------------------------*)

Goal "E ~= {} ==> EX x. EX X : (Pow E - {{}}). x: X";
by Auto_tac;
val lemmaPow3 = result();

Goalw [choicefun_def] "E ~= {} ==> choicefun E : E";
by (rtac (lemmaPow3 RS someI2_ex) 1);
by Auto_tac;
qed "choicefun_mem_set";
Addsimps [choicefun_mem_set];

Goal "[| E ~={}; ALL x. EX y: E. x < y |] ==> injf_max n E : E";
by (induct_tac "n" 1);
by (Force_tac 1);
by (simp_tac (simpset() addsimps [choicefun_def]) 1);
by (rtac (lemmaPow3 RS someI2_ex) 1);
by Auto_tac;
qed "injf_max_mem_set";

Goal "ALL x. EX y: E. x < y ==> injf_max n E < injf_max (Suc n) E";
by (simp_tac (simpset() addsimps [choicefun_def]) 1);
by (rtac (lemmaPow3 RS someI2_ex) 1);
by Auto_tac;
qed "injf_max_order_preserving";

Goal "ALL x. EX y: E. x < y \
\     ==> ALL n m. m < n --> injf_max m E < injf_max n E";
by (rtac allI 1);
by (induct_tac "n" 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [choicefun_def]) 1);
by (rtac (lemmaPow3 RS someI2_ex) 1);
by Auto_tac;
by (dtac (CLAIM "m < Suc n ==> m = n | m < n") 1);
by Auto_tac;
by (dres_inst_tac [("x","m")] spec 1);
by Auto_tac;
by (dtac subsetD 1 THEN Auto_tac);
by (dres_inst_tac [("x","injf_max m E")] order_less_trans 1);
by Auto_tac;
qed "injf_max_order_preserving2";

Goal "ALL x. EX y: E. x < y ==> inj (%n. injf_max n E)";
by (rtac injI 1);
by (rtac ccontr 1);
by Auto_tac;
by (dtac injf_max_order_preserving2 1);
by (cut_inst_tac [("m","x"),("n","y")] less_linear 1);
by Auto_tac;
by (auto_tac (claset() addSDs [spec],simpset()));
qed "inj_injf_max";

Goal "[| (E::('a::{order} set)) ~= {}; ALL x. EX y: E. x < y |] \
\     ==> EX f. range f <= E & inj (f::nat => 'a) & (ALL m. f m < f(Suc m))";
by (res_inst_tac [("x","%n. injf_max n E")] exI 1);
by (Step_tac 1);
by (rtac injf_max_mem_set 1);
by (rtac inj_injf_max 3);
by (rtac injf_max_order_preserving 4);
by Auto_tac;
qed "infinite_set_has_order_preserving_inj";

(*-------------------------------------------------------------------------------*)
(* Only need fact that we can have an injective function from N to A for proof   *)
(*-------------------------------------------------------------------------------*)

Goal "~ finite A ==> hypnat_of_nat ` A < ( *sNat* A)";
by Auto_tac;
by (rtac subsetD 1);
by (rtac NatStar_hypreal_of_real_image_subset 1);
by Auto_tac;
by (subgoal_tac "A ~= {}" 1);
by (Force_tac 2);
by (dtac infinite_set_has_order_preserving_inj 1);
by (etac (not_finite_nat_set_iff2 RS iffD1) 1);
by Auto_tac;
by (dtac inj_fun_not_hypnat_in_SHNat 1);
by (dtac range_subset_mem_starsetNat 1);
by (auto_tac (claset(),simpset() addsimps [SHNat_def]));
qed "hypnat_infinite_has_nonstandard";

Goal "*sNat* A =  hypnat_of_nat ` A ==> finite A";
by (rtac ccontr 1);
by (auto_tac (claset() addDs [hypnat_infinite_has_nonstandard],
    simpset()));
qed "starsetNat_eq_hypnat_of_nat_image_finite";

Goal "( *sNat* A = hypnat_of_nat ` A) = (finite A)";
by (blast_tac (claset() addSIs [starsetNat_eq_hypnat_of_nat_image_finite,
    NatStar_hypnat_of_nat]) 1);
qed "finite_starsetNat_iff";

Goal "(~ finite A) = (hypnat_of_nat ` A < *sNat* A)";
by (rtac iffI 1);
by (blast_tac (claset() addSIs [hypnat_infinite_has_nonstandard]) 1);
by (auto_tac (claset(),simpset() addsimps [finite_starsetNat_iff RS sym]));
qed "hypnat_infinite_has_nonstandard_iff";


(*-------------------------------------------------------------------------------*)
(* Existence of infinitely many primes: a nonstandard proof                      *)
(*-------------------------------------------------------------------------------*)

Goal "~ (ALL n:- {0}. hypnat_of_nat n hdvd 1)";
by Auto_tac;
by (res_inst_tac [("x","2")] bexI 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_of_nat_def,
    hypnat_one_def,hdvd,dvd_def]));
val lemma_not_dvd_hypnat_one = result();
Addsimps [lemma_not_dvd_hypnat_one];

Goal "EX n:- {0}. ~ hypnat_of_nat n hdvd 1";
by (cut_facts_tac [lemma_not_dvd_hypnat_one] 1);
by (auto_tac (claset(),simpset() delsimps [lemma_not_dvd_hypnat_one]));
val lemma_not_dvd_hypnat_one2 = result();
Addsimps [lemma_not_dvd_hypnat_one2];

(* not needed here *)
Goalw [hypnat_zero_def,hypnat_one_def] 
  "[| 0 < (N::hypnat); N ~= 1 |] ==> 1 < N";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_less]));
by (Ultra_tac 1);
qed "hypnat_gt_zero_gt_one";

Goalw [hypnat_zero_def,hypnat_one_def]
    "0 < N ==> 1 < (N::hypnat) + 1";
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_less,hypnat_add]));
qed "hypnat_add_one_gt_one";

Goal "0 ~: prime";
by (Step_tac 1);
by (dtac (thm "prime_g_zero") 1);
by Auto_tac;
qed "zero_not_prime";
Addsimps [zero_not_prime];

Goalw [starprime_def,starsetNat_def,hypnat_of_nat_def]
   "hypnat_of_nat 0 ~: starprime";
by (auto_tac (claset() addSIs [bexI],simpset()));
qed "hypnat_of_nat_zero_not_prime";
Addsimps [hypnat_of_nat_zero_not_prime];

Goalw [starprime_def,starsetNat_def,hypnat_zero_def]
   "0 ~: starprime";
by (auto_tac (claset() addSIs [bexI],simpset()));
qed "hypnat_zero_not_prime";
Addsimps [hypnat_zero_not_prime];

Goal "1 ~: prime";
by (Step_tac 1);
by (dtac (thm "prime_g_one") 1);
by Auto_tac;
qed "one_not_prime";
Addsimps [one_not_prime];

Goal "Suc 0 ~: prime";
by (Step_tac 1);
by (dtac (thm "prime_g_one") 1);
by Auto_tac;
qed "one_not_prime2";
Addsimps [one_not_prime2];

Goalw [starprime_def,starsetNat_def,hypnat_of_nat_def]
   "hypnat_of_nat 1 ~: starprime";
by (auto_tac (claset() addSIs [bexI],simpset()));
qed "hypnat_of_nat_one_not_prime";
Addsimps [hypnat_of_nat_one_not_prime];

Goalw [starprime_def,starsetNat_def,hypnat_one_def]
   "1 ~: starprime";
by (auto_tac (claset() addSIs [bexI],simpset()));
qed "hypnat_one_not_prime";
Addsimps [hypnat_one_not_prime];

Goal "[| k hdvd m; k hdvd n |] ==> k hdvd (m - n)";
by (res_inst_tac [("z","k")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hdvd,hypnat_minus]));
by (Ultra_tac 1);
by (blast_tac (claset() addIs [dvd_diff]) 1);
qed "hdvd_diff";

Goalw [dvd_def] "x dvd (1::nat) ==> x = 1";
by Auto_tac;
qed "dvd_one_eq_one";

Goalw [hypnat_one_def] "x hdvd 1 ==> x = 1";
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hdvd]));
qed "hdvd_one_eq_one";

Goal "~ finite prime";
by (rtac (hypnat_infinite_has_nonstandard_iff RS iffD2) 1);
by (cut_facts_tac [hypnat_dvd_all_hypnat_of_nat] 1);
by (etac exE 1);
by (etac conjE 1);
by (subgoal_tac "1 < N + 1" 1);
by (blast_tac (claset() addIs [hypnat_add_one_gt_one]) 2);
by (dtac hyperprime_factor_exists 1);
by (auto_tac (claset() addIs [NatStar_mem],simpset()));
by (subgoal_tac "k ~: hypnat_of_nat ` prime" 1);
by (force_tac (claset(),simpset() addsimps [starprime_def]) 1);
by (Step_tac 1);
by (dres_inst_tac [("x","x")] bspec 1);
by (rtac ccontr 1 THEN Asm_full_simp_tac 1);
by (dtac hdvd_diff 1 THEN assume_tac 1);
by (auto_tac (claset() addDs [hdvd_one_eq_one],simpset()));
qed "not_finite_prime";
