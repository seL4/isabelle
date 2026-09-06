(*MOVED to HOL-Computational_Algebra.Factorial_Ring*)
section \<open>Transfer of Irreducibility across a Ring Isomorphism\<close>

theory Ring_Iso_Irreducible
  imports "HOL-Computational_Algebra.Factorial_Ring"
begin

text \<open>
  Irreducibility (in the sense of @{const irreducible} for type-class commutative semirings)
  is preserved and reflected by a bijective multiplicative homomorphism that fixes \<open>0\<close> and
  \<open>1\<close>.  This is generic infrastructure: it lets an irreducibility result be transported along
  any ring isomorphism.
\<close>

lemma ring_iso_dvd:
  fixes f :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_semiring_1"
  assumes hom: "\<And>x y. f (x * y) = f x * f y" and bij: "bij f"
  shows "f a dvd f b \<longleftrightarrow> a dvd b"
  using bij_pointE [OF bij] hom unfolding dvd_def
  by metis

lemma ring_iso_unit:
  fixes f :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_semiring_1"
  assumes hom: "\<And>x y. f (x * y) = f x * f y" and one: "f 1 = 1" and bij: "bij f"
  shows "f a dvd 1 \<longleftrightarrow> a dvd 1"
  using ring_iso_dvd[OF hom bij, of a 1] one by simp

theorem ring_iso_irreducible:
  fixes f :: "'a::comm_semiring_1 \<Rightarrow> 'b::comm_semiring_1"
  assumes hom: "\<And>x y. f (x * y) = f x * f y" and one: "f 1 = 1"
    and zero: "f 0 = 0" and bij: "bij f"
  shows "irreducible (f a) \<longleftrightarrow> irreducible a"
proof -
  have ne: "f a = 0 \<longleftrightarrow> a = 0"
    by (metis bij bij_is_inj inj_eq zero)
  show ?thesis
  proof
    assume "irreducible (f a)"
    then show "irreducible a"
      by (metis bij hom irreducible_def ne one ring_iso_unit)
  next
    assume "irreducible a"
    then have a: "a \<noteq> 0" "\<not> a dvd 1" "\<And>u v. a = u * v \<Longrightarrow> u dvd 1 \<or> v dvd 1"
      by (auto simp: irreducible_def)
    show "irreducible (f a)"
    proof (rule irreducibleI)
      show "f a \<noteq> 0" using a(1) ne by simp
      show "\<not> f a dvd 1" using a(2) ring_iso_unit[OF hom one bij] by simp
    next
      fix u v assume "f a = u * v"
      then obtain u' v' where uv: "u = f u'" "v = f v'"  "a = u' * v'" 
        using bij_pointE[OF bij] by (metis hom)
      then show "u dvd 1 \<or> v dvd 1" using uv ring_iso_unit[OF hom one bij]
        using a(3) by blast
    qed
  qed
qed

end
