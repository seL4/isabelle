section \<open>Euclidean type classes as locale Euclidean domains; the integers\<close>

theory Int_Ring
  imports Field_Typeclass Divisibility_Theory
begin

text \<open>Isabelle's type class @{class euclidean_ring} (an @{class idom} with a @{const euclidean_size}
  and division with remainder) is exactly the type-class analogue of our locale
  @{locale Euclidean_Domain}.  A single bridge lemma therefore endows \<^emph>\<open>every\<close> Euclidean-ring type
  --- on its whole carrier @{term UNIV} --- with the locale-based divisibility tower (principal ideal
  domain, factorial domain, irreducible \<open>=\<close> prime, existence and uniqueness of factorizations).  The
  ring of integers \<open>\<int>\<close> is the primary instance, whence the fundamental theorem of arithmetic.\<close>

text \<open>Restore HOL arithmetic notation locally (\<open>Ring_Theory\<close> suppresses it).\<close>
notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

subsection \<open>The general type-class bridge\<close>

text \<open>The division-with-remainder axiom of @{locale Euclidean_Domain} is witnessed by \<open>q = a div b\<close>,
  \<open>r = a mod b\<close>: the identity @{thm mult_div_mod_eq} gives \<open>a = b \<cdot> q + r\<close>, and @{thm mod_size_less}
  bounds the remainder's size.  (The class's extra axioms --- @{thm size_0}, @{thm size_mult_mono}
  --- exceed what the locale requires, so this is a one-directional bridge, which is all we need.)\<close>
lemma euclidean_domain_TC:
  "Euclidean_Domain (UNIV :: 'a :: euclidean_ring set) (+) (*) 0 1 euclidean_size"
proof (rule Euclidean_Domain.intro)
  show "integral_domain (UNIV :: 'a set) (+) (*) 0 1" by (rule idom_TC)
next
  show "Euclidean_Domain_axioms (UNIV :: 'a set) (+) (*) 0 euclidean_size"
  proof
    fix a b :: 'a assume "a \<in> UNIV" "b \<in> UNIV" "a \<noteq> 0" and bnz: "b \<noteq> 0"
    have "a = b * (a div b) + a mod b" by (simp add: mult_div_mod_eq)
    moreover have "a mod b = 0 \<or> euclidean_size (a mod b) < euclidean_size b"
      using mod_size_less[OF bnz] by blast
    ultimately show "\<exists>q\<in>UNIV. \<exists>r\<in>UNIV.
        a = b * q + r \<and> (r = 0 \<or> euclidean_size r < euclidean_size b)"
      by (intro bexI[of _ "a div b"] bexI[of _ "a mod b"]) auto
  qed
qed


subsection \<open>The integers\<close>

text \<open>\<open>\<int>\<close> is a Euclidean ring with Euclidean size the absolute value, so the bridge specialises to
  it directly.  Through the interpretation \<open>\<int>\<close> inherits the whole tower: it is a principal ideal
  domain and a factorial (unique factorization) domain --- the fundamental theorem of arithmetic.\<close>
interpretation Int: Euclidean_Domain
  "UNIV :: int set" "(+)" "(*)" "0" "1" "euclidean_size :: int \<Rightarrow> nat"
  by (rule euclidean_domain_TC)

text \<open>Consequences, transported from the abstract tower.\<close>
lemmas int_factorization_exists = Int.factorization_exists
lemmas int_irreducible_imp_prime = Int.irreducible_imp_prime
lemmas int_bezout = Int.bezout

end
