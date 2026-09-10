section \<open>Rational Subfields and Irreducibility over the Rationals\<close>

theory Rats_Irreducibility
  imports Galois_Transitivity Rat_Fract_Iso
begin

text \<open>A complex polynomial all of whose coefficients are rational is the \<open>of_rat\<close>-image of a
  rational polynomial.\<close>
lemma poly_over_Rats_imp_map_of_rat:
  assumes "p \<in> poly_over (\<rat> :: complex set)"
  shows "\<exists>r :: rat poly. p = map_poly of_rat r"
  using assms by (meson Rats_0 poly_over_iff_aux ratpolyE)

lemma map_poly_of_rat_mult:
  "map_poly of_rat (a * b) = (map_poly of_rat a :: complex poly) * map_poly of_rat b"
  by (intro poly_eqI) (simp add: coeff_map_poly of_rat_mult of_rat_sum coeff_mult)

lemma map_poly_of_rat_inj: "inj (map_poly of_rat :: rat poly \<Rightarrow> complex poly)"
  by (intro injI poly_eqI) (metis coeff_map_poly of_rat_0 of_rat_eq_iff)

lemma degree_map_poly_of_rat:
  "degree (map_poly of_rat r :: complex poly) = degree r"
  by (simp add: degree_map_poly)

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
  have "(map_poly of_rat r :: complex poly) = map_poly of_rat (b' * c')"
    by (simp add: b' c' eq map_poly_of_rat_mult)
  then have rbc: "r = b' * c'" using map_poly_of_rat_inj by (simp add: inj_eq)
  show "degree b = 0 \<or> degree c = 0"
    using irreducibleD[OF irr rbc] b' c' degree_map_poly_of_rat poly_dvd_1 by auto
qed

end
