section \<open>Rational Subfields and Irreducibility over the Rationals\<close>

theory Rats_Irreducibility
  imports Galois_Transitivity Rat_Fract_Iso
begin

text \<open>A complex polynomial all of whose coefficients are rational is the \<open>of_rat\<close>-image of a
  rational polynomial.\<close>
lemma poly_over_Rats_imp_map_of_rat:
  assumes "p \<in> poly_over (\<rat> :: complex set)"
  shows "\<exists>r :: rat poly. p = map_poly of_rat r"
proof -
  have coeffs_rat: "coeff p i \<in> \<rat>" for i
    using Rats_0 assms poly_over_iff_aux by blast
  have inv0: "inv of_rat (0::complex) = 0"
    by (metis injI inv_f_f of_rat_0 of_rat_eq_iff)
  define r where "r = map_poly (inv of_rat) p"
  have cr: "coeff r i = inv of_rat (coeff p i)" for i
    unfolding r_def by (rule coeff_map_poly) (rule inv0)
  have "p = map_poly of_rat r"
  proof (rule poly_eqI)
    fix i
    have "of_rat (inv of_rat (coeff p i)) = coeff p i"
      by (metis Rats_def coeffs_rat f_inv_into_f)
    then show "coeff p i = coeff (map_poly of_rat r) i"
      by (simp add: cr coeff_map_poly)
  qed
  then show ?thesis by blast
qed

lemma map_poly_of_rat_mult:
  "map_poly of_rat (a * b) = (map_poly of_rat a :: complex poly) * map_poly of_rat b"
  by (intro poly_eqI) (simp add: coeff_map_poly of_rat_mult of_rat_sum coeff_mult)

lemma map_poly_of_rat_inj: "inj (map_poly of_rat :: rat poly \<Rightarrow> complex poly)"
  by (intro injI poly_eqI) (metis coeff_map_poly of_rat_0 of_rat_eq_iff)

lemma degree_map_poly_of_rat:
  "degree (map_poly of_rat r :: complex poly) = degree r"
  by (rule degree_map_poly) (simp_all add: of_rat_eq_0_iff)

text \<open>Irreducibility of a rational polynomial transfers to irreducibility \<^emph>\<open>over @{term \<rat>}\<close>
  of its complex image: a factorisation over @{term \<rat>} pulls back along the injective ring
  homomorphism @{term "map_poly of_rat"} to a factorisation of the rational polynomial.\<close>
lemma irreducible_imp_irreducible_over_Rats:
  fixes r :: "rat poly"
  assumes irr: "irreducible r" and deg: "degree r > 0"
  shows "irreducible_over (\<rat> :: complex set) (map_poly of_rat r)"
  unfolding irreducible_over_def
proof (intro conjI allI impI)
  show "map_poly of_rat r \<noteq> (0 :: complex poly)"
    by (metis deg degree_0 degree_map_poly_of_rat not_less_zero)
  show "0 < degree (map_poly of_rat r :: complex poly)"
    using deg by (simp add: degree_map_poly_of_rat)
next
  fix b c :: "complex poly"
  assume bover: "b \<in> poly_over \<rat>" and cover: "c \<in> poly_over \<rat>"
    and eq: "map_poly of_rat r = b * c"
  obtain b' where b': "b = map_poly of_rat b'" using bover poly_over_Rats_imp_map_of_rat by blast
  obtain c' where c': "c = map_poly of_rat c'" using cover poly_over_Rats_imp_map_of_rat by blast
  have key: "(map_poly of_rat r :: complex poly) = map_poly of_rat (b' * c')"
    by (simp add: b' c' eq map_poly_of_rat_mult)
  have rbc: "r = b' * c'" using key map_poly_of_rat_inj by (simp add: inj_eq)
  have unit_deg0: "degree u = 0" if "(u :: rat poly) dvd 1" for u
    using that by (auto simp: is_unit_poly_iff)
  have "b' dvd 1 \<or> c' dvd 1" using irreducibleD[OF irr rbc] .
  then have "degree b' = 0 \<or> degree c' = 0"
    using unit_deg0 by presburger
  then show "degree b = 0 \<or> degree c = 0"
    using b' c' degree_map_poly_of_rat by presburger
qed

end
