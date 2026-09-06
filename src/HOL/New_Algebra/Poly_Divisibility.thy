section \<open>The polynomial ring over a field is a Euclidean domain\<close>

theory Poly_Divisibility
  imports Poly_Ring Divisibility_Theory
begin

text \<open>Over a field \<open>F\<close>, the polynomial ring \<open>F[X]\<close> is a Euclidean domain, with the polynomial
  degree as Euclidean function: this is exactly the division algorithm of
  \<open>Poly_Ring\<close> (@{thm [source] Field.poly_divide}) packaged into the abstract
  @{locale Euclidean_Domain} of \<open>Divisibility_Theory\<close>.  The interpretation is
  the bridge that endows \<open>F[X]\<close> --- for free --- with the whole divisibility tower: it is a
  principal ideal domain and a factorial (unique factorization) domain, in which irreducible
  polynomials are prime and factorizations into irreducibles exist and are unique up to the number
  of factors.\<close>

context Field
begin

text \<open>The carrier-set polynomial ring satisfies the abstract Euclidean-domain interface.  This
  named theorem keeps the division-algorithm proof reusable by the exported sublocale below.\<close>
theorem poly_euclidean_domain:
  "Euclidean_Domain poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P degree"
proof -
  show "Euclidean_Domain poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P degree"
  proof (rule Euclidean_Domain.intro)
    show "integral_domain poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P"
      by (rule poly_integral_domain)
  next
    show "Euclidean_Domain_axioms poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P degree"
    proof
      fix a b assume a: "a \<in> poly_carrier" and b: "b \<in> poly_carrier"
        and anz: "a \<noteq> \<zero>\<^sub>P" and bnz: "b \<noteq> \<zero>\<^sub>P"
      show "\<exists>q\<in>poly_carrier. \<exists>r\<in>poly_carrier.
              a = (b \<otimes>\<^sub>P q) \<oplus>\<^sub>P r \<and> (r = \<zero>\<^sub>P \<or> degree r < degree b)"
        using poly_divide[OF a b bnz] by blast
    qed
  qed
qed

end

sublocale Field \<subseteq> FX: Euclidean_Domain
  poly_carrier "(\<oplus>\<^sub>P)" "(\<otimes>\<^sub>P)" "\<zero>\<^sub>P" "\<one>\<^sub>P" degree
proof -
  show "Euclidean_Domain poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P degree"
    by (rule poly_euclidean_domain)
qed

context Field
begin

text \<open>Consequences, transported from the abstract tower.  Every nonzero non-unit polynomial factors
  into irreducibles (@{thm [source] FX.factorization_exists}), an irreducible polynomial is prime
  (@{thm [source] FX.irreducible_imp_prime}), and any two prime factorizations of associated
  polynomials have the same length (@{thm [source] FX.prime_factorization_length_unique}).\<close>

theorem poly_factorization_exists:
  "\<lbrakk> p \<in> poly_carrier; p \<noteq> \<zero>\<^sub>P; \<not> FX.is_unit p \<rbrakk> \<Longrightarrow> \<exists>fs. FX.factorization fs p"
  by (rule FX.factorization_exists)

theorem poly_irreducible_imp_prime:
  "FX.irreducible_elem p \<Longrightarrow> FX.prime_elem p"
  by (rule FX.irreducible_imp_prime)

end

end
