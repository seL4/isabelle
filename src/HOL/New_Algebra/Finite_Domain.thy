section \<open>Finite integral domains\<close>

theory Finite_Domain
  imports Divisibility_Theory
begin

text \<open>A finite integral domain is a field.  Multiplication by a nonzero element is an
  injective self-map of the finite carrier, hence surjective; a preimage of the unit is a
  multiplicative inverse.\<close>
theorem (in integral_domain) finite_integral_domain_imp_field:
  assumes fin: "finite R"
  shows "Field R (+) (\<cdot>) \<zero> \<one>"
proof (rule Field.intro[OF commutative_ring_axioms nontrivial_ring_axioms])
  show "Field_axioms R (\<cdot>) \<zero> \<one>"
  proof
    fix a
    assume aR: "a \<in> R" and anz: "a \<noteq> \<zero>"
    have inj: "inj_on ((\<cdot>) a) R"
      by (rule inj_onI) (rule mult_cancel_left[OF aR _ _ anz])
    have closed: "((\<cdot>) a) ` R \<subseteq> R"
      using aR by (blast intro: multiplicative.composition_closed)
    have "\<one> \<in> (\<cdot>) a ` R"
      using endo_inj_surj[OF fin closed inj] multiplicative.unit_closed by simp
    then obtain b where bR: "b \<in> R" and ab: "a \<cdot> b = \<one>" by blast
    have ba: "b \<cdot> a = \<one>"
      using multiplicative.commutative[OF bR aR] ab by simp
    show "multiplicative.invertible a"
      by (rule multiplicative.invertibleI[OF ab ba bR])
  qed
qed

end
