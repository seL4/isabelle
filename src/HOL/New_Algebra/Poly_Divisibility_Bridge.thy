section \<open>Bridges for Polynomial Divisibility\<close>

theory Poly_Divisibility_Bridge
  imports Poly_Divisibility Poly_Ideal
begin

text \<open>
  \<open>Poly_Divisibility\<close> interprets the carrier-set polynomial ring as an
  abstract Euclidean domain, while \<open>Poly_Ideal\<close> exposes the same multiples
  through @{const Field.poly_dvd} and @{const Field.poly_pideal}.  The two interfaces are
  intentionally kept in their original theories so that each remains independently usable.  This
  theory is the explicit seam between them.
\<close>

context Field
begin

text \<open>
  The concrete polynomial divisibility relation and the abstract relation differ only by the
  orientation of the product.  Commutativity of the polynomial ring supplies the bridge.
\<close>
lemma FX_divides_iff_poly_dvd:
  assumes d: "d \<in> poly_carrier"
  shows "FX.divides d x \<longleftrightarrow> poly_dvd d x"
proof
  assume dvd: "FX.divides d x"
  obtain q where q: "q \<in> poly_carrier" and xeq: "x = d \<otimes>\<^sub>P q"
    using FX.dividesE[OF dvd] by blast
  have "x = q \<otimes>\<^sub>P d"
  proof -
    have "d \<otimes>\<^sub>P q = q \<otimes>\<^sub>P d" using d q by (rule poly_mult_comm)
    then show ?thesis using xeq by simp
  qed
  then show "poly_dvd d x"
    unfolding poly_dvd_def using q by blast
next
  assume dvd: "poly_dvd d x"
  obtain q where q: "q \<in> poly_carrier" and xeq: "x = q \<otimes>\<^sub>P d"
    using dvd unfolding poly_dvd_def by blast
  have "x = d \<otimes>\<^sub>P q"
  proof -
    have "q \<otimes>\<^sub>P d = d \<otimes>\<^sub>P q" using q d by (rule poly_mult_comm)
    then show ?thesis using xeq by simp
  qed
  show "FX.divides d x"
  proof (rule FX.dividesI)
    show "q \<in> poly_carrier" using q .
    show "x = d \<otimes>\<^sub>P q" using \<open>x = d \<otimes>\<^sub>P q\<close> .
  qed
qed

text \<open>
  The concrete principal ideal and the abstract divisibility relation now have a common
  polynomial-level formulation.
\<close>
lemma FX_divides_iff_mem_poly_pideal:
  assumes d: "d \<in> poly_carrier"
  shows "FX.divides d x \<longleftrightarrow> x \<in> poly_pideal d"
  using FX_divides_iff_poly_dvd[OF d] poly_dvd_iff_mem_pideal by blast

lemma poly_dvd_iff_mem_FX_principal:
  assumes d: "d \<in> poly_carrier" and x: "x \<in> poly_carrier"
  shows "poly_dvd d x \<longleftrightarrow> x \<in> FX.principal_ideal d"
  using FX_divides_iff_poly_dvd[OF d] FX.divides_iff_mem_principal[OF d x] by blast

lemma FX_divides_iff_pmod_zero:
  assumes d: "d \<in> poly_carrier" and dnz: "d \<noteq> \<zero>\<^sub>P"
    and x: "x \<in> poly_carrier"
  shows "FX.divides d x \<longleftrightarrow> pmod x d = \<zero>\<^sub>P"
  using FX_divides_iff_poly_dvd[OF d] poly_dvd_iff_pmod_zero[OF d dnz x] by blast


subsection \<open>Units and irreducibility across the seam\<close>

text \<open>
  The same seam again one notion up.  @{const poly_unit} spells out invertibility in the polynomial
  ring directly, while @{term FX.is_unit} is the abstract @{const Monoid.invertible} at that ring.
  \<^emph>\<open>They are not quite the same predicate\<close>: @{const Monoid.invertible} does not require its argument to
  lie in the carrier, whereas @{const poly_unit} does, so the two agree only on @{const poly_carrier}.
  That is enough for the notion actually wanted, because @{const poly_irreducible} and
  @{term FX.irreducible_elem} both demand carrier membership outright and apply their unit test only
  to carrier elements.  Their agreement is what lets a factor produced by
  @{thm [source] poly_factorization_exists} be fed to @{thm [source] poly_quotient_field}.
\<close>

lemma FX_is_unit_iff_poly_unit:
  assumes p: "p \<in> poly_carrier" shows "FX.is_unit p \<longleftrightarrow> poly_unit p"
proof
  assume "FX.is_unit p"
  then obtain q where "q \<in> poly_carrier" and "p \<otimes>\<^sub>P q = \<one>\<^sub>P" and "q \<otimes>\<^sub>P p = \<one>\<^sub>P" by blast
  with p show "poly_unit p" by (rule poly_unitI)
next
  assume "poly_unit p"
  then obtain q where q: "q \<in> poly_carrier" and pq: "p \<otimes>\<^sub>P q = \<one>\<^sub>P" and qp: "q \<otimes>\<^sub>P p = \<one>\<^sub>P"
    unfolding poly_unit_def by blast
  show "FX.is_unit p" by (rule FX.is_unitI [OF pq qp q])
qed

lemma FX_irreducible_iff_poly_irreducible:
  "FX.irreducible_elem p \<longleftrightarrow> poly_irreducible p"
  unfolding FX.irreducible_elem_def poly_irreducible_def
  by (auto simp: FX_is_unit_iff_poly_unit)

text \<open>
  Every polynomial that is neither zero nor a unit has an irreducible factor: factor it and take the
  head of the list, which is nonempty because the empty product is @{term "\<one>\<^sub>P"}.  This is the form
  in which the adjunction of a root consumes factorization --- a root of an irreducible factor of
  @{term p} is a root of @{term p} --- and it is stated with @{const poly_irreducible} so that
  @{thm [source] poly_quotient_field} applies directly.
\<close>
theorem exists_poly_irreducible_factor:
  assumes p: "p \<in> poly_carrier" and pnz: "p \<noteq> \<zero>\<^sub>P" and pnu: "\<not> poly_unit p"
  obtains q where "poly_irreducible q" and "poly_dvd q p"
proof -
  have "\<not> FX.is_unit p" using pnu by (simp add: FX_is_unit_iff_poly_unit [OF p])
  then obtain fs where fs: "FX.factorization fs p"
    using poly_factorization_exists [OF p pnz] by blast
  have prod: "FX.list_prod fs = p" by (rule FX.factorization_prod [OF fs])
  have "fs \<noteq> []"
  proof
    assume "fs = []"
    with prod have peq: "p = \<one>\<^sub>P" by simp
    have "poly_unit \<one>\<^sub>P"
      by (rule poly_unitI [OF poly_one_closed poly_one_closed])
         (simp_all add: poly_mult_one_left poly_one_closed)
    with peq pnu show False by simp
  qed
  then obtain f gs where feq: "fs = f # gs" by (cases fs) auto
  have irr: "FX.irreducible_elem f" using fs feq by (simp add: FX.factorization_irreducible)
  have fc: "f \<in> poly_carrier" using irr by (rule FX.irreducible_elemD(1))
  have gsR: "set gs \<subseteq> poly_carrier" using FX.factorization_set_R [OF fs] feq by simp
  have "p = f \<otimes>\<^sub>P FX.list_prod gs" using prod feq by simp
  then have "poly_dvd f p"
    using FX.list_prod_closed [OF gsR] fc by (auto simp: poly_dvd_def poly_mult_comm)
  with irr show thesis
    using that FX_irreducible_iff_poly_irreducible by blast
qed

text \<open>Each member of a list divides the product of the list.  Needed to feed a single irreducible
  factor of a factorisation to the adjunction of a root.\<close>
lemma poly_dvd_poly_prod:
  assumes fs: "\<And>g. g \<in> set fs \<Longrightarrow> g \<in> poly_carrier" and f: "f \<in> set fs"
  shows "poly_dvd f (poly_prod fs)"
  using fs f
proof (induct fs)
  case (Cons g gs)
  have gc: "g \<in> poly_carrier" and gsc: "\<And>h. h \<in> set gs \<Longrightarrow> h \<in> poly_carrier"
    using Cons.prems(1) by auto
  have Pgs: "poly_prod gs \<in> poly_carrier" by (rule poly_prod_closed [OF gsc])
  show ?case
  proof (cases "f = g")
    case True
    have "poly_prod (g # gs) = poly_prod gs \<otimes>\<^sub>P g"
      using poly_mult_comm [OF gc Pgs] by simp
    then show ?thesis unfolding poly_dvd_def using True Pgs by blast
  next
    case False
    then have "f \<in> set gs" using Cons.prems(2) by simp
    then obtain q where q: "q \<in> poly_carrier" and eq: "poly_prod gs = q \<otimes>\<^sub>P f"
      using Cons.hyps [OF gsc] unfolding poly_dvd_def by blast
    have fc: "f \<in> poly_carrier" using \<open>f \<in> set gs\<close> by (rule gsc)
    have "poly_prod (g # gs) = (g \<otimes>\<^sub>P q) \<otimes>\<^sub>P f"
      using eq poly_mult_assoc [OF gc q fc] by simp
    then show ?thesis unfolding poly_dvd_def using gc q by (blast intro: poly_mult_closed)
  qed
qed simp

subsection \<open>The field of remainders modulo an irreducible polynomial\<close>

text \<open>
  Kronecker's theorem in \<^emph>\<open>normal-form\<close> presentation: rather than the cosets of \<open>(p)\<close>, take the
  polynomials of degree below @{term p}, with addition unchanged and multiplication followed by
  reduction.  This is the same field as @{thm [source] poly_quotient_field} exhibits, but its carrier
  is a set of polynomials rather than a set of cosets, so it stays inside the coefficient type.  That
  is what a construction adjoining roots inside a fixed ambient type needs, and it is also the form
  in which one computes.

  Invertibility is the only substantial part, and it does not need gcds: a nonzero remainder is not a
  multiple of @{term p}, so it lies outside the maximal ideal \<open>(p)\<close>, and extending that ideal by it
  gives the whole ring --- which is to say @{term "\<one>\<^sub>P"} is a combination @{term "m \<oplus>\<^sub>P r \<otimes>\<^sub>P S"} with
  @{term m} a multiple of @{term p}.  Reducing that equation is exactly the inverse.
\<close>
theorem remainder_field:
  assumes irr: "poly_irreducible p"
  shows "Field (low_poly (degree p)) (\<oplus>\<^sub>P) (\<lambda>S T. pmod (S \<otimes>\<^sub>P T) p) \<zero>\<^sub>P \<one>\<^sub>P"
proof -
  have p: "p \<in> poly_carrier" using irr by (rule poly_irreducibleD_carrier)
  have pnz: "p \<noteq> \<zero>\<^sub>P" using irr by (rule poly_irreducibleD_nonzero)
  have dpos: "0 < degree p" using irr by (rule poly_irreducible_degree_pos)
  define K where "K = low_poly (degree p)"
  define mult where "mult = (\<lambda>S T. pmod (S \<otimes>\<^sub>P T) p)"
  \<comment> \<open>Basic facts about the carrier.\<close>
  have Kc: "S \<in> poly_carrier" if "S \<in> K" for S
    using that unfolding K_def by (rule low_poly_closed)
  have Ksmall: "pmod S p = S" if "S \<in> K" for S
    using that low_poly_iff_degree [OF Kc [OF that]] pmod_small [OF p pnz Kc [OF that]]
    unfolding K_def by blast
  have Kadd: "S \<oplus>\<^sub>P T \<in> K" if "S \<in> K" "T \<in> K" for S T
    using that unfolding K_def by (rule low_poly_add_closed)
  have Kneg: "\<ominus>\<^sub>P S \<in> K" if "S \<in> K" for S
    using that unfolding K_def by (rule low_poly_neg_closed)
  have Kzero: "\<zero>\<^sub>P \<in> K" unfolding K_def by (rule low_poly_zero)
  have Kone: "\<one>\<^sub>P \<in> K" unfolding K_def using dpos by (rule low_poly_one)
  have Kmult: "mult S T \<in> K" if "S \<in> K" "T \<in> K" for S T
    unfolding mult_def K_def
    using poly_mult_closed [OF Kc [OF that(1)] Kc [OF that(2)]] p pnz by (rule pmod_low_poly)
  \<comment> \<open>Reduction is a homomorphism, so it carries the ring laws over from @{text "F[X]"}.\<close>
  have reduce: "pmod (S \<otimes>\<^sub>P T) p = mult S T" for S T unfolding mult_def by rule
  have mult_assoc: "mult (mult S T) U = mult S (mult T U)" if K: "S \<in> K" "T \<in> K" "U \<in> K" for S T U
  proof -
    have c: "S \<in> poly_carrier" "T \<in> poly_carrier" "U \<in> poly_carrier"
      using K by (blast intro: Kc)+
    have "mult (mult S T) U = pmod (pmod (S \<otimes>\<^sub>P T) p \<otimes>\<^sub>P pmod U p) p"
      unfolding mult_def using Ksmall [OF K(3)] by simp
    also have "\<dots> = pmod ((S \<otimes>\<^sub>P T) \<otimes>\<^sub>P U) p"
      by (rule pmod_mult [OF poly_mult_closed [OF c(1) c(2)] c(3) p pnz, symmetric])
    also have "\<dots> = pmod (S \<otimes>\<^sub>P (T \<otimes>\<^sub>P U)) p" using poly_mult_assoc [OF c] by simp
    also have "\<dots> = pmod (pmod S p \<otimes>\<^sub>P pmod (T \<otimes>\<^sub>P U) p) p"
      by (rule pmod_mult [OF c(1) poly_mult_closed [OF c(2) c(3)] p pnz])
    also have "\<dots> = mult S (mult T U)"
      unfolding mult_def using Ksmall [OF K(1)] by simp
    finally show ?thesis .
  qed
  have mult_comm: "mult S T = mult T S" if "S \<in> K" "T \<in> K" for S T
    unfolding mult_def using poly_mult_comm [OF Kc [OF that(1)] Kc [OF that(2)]] by simp
  have mult_one: "mult \<one>\<^sub>P S = S" if "S \<in> K" for S
    unfolding mult_def
    using poly_mult_one_left [OF Kc [OF that]] Ksmall [OF that] by simp
  have distrib: "mult S (T \<oplus>\<^sub>P U) = mult S T \<oplus>\<^sub>P mult S U" if K: "S \<in> K" "T \<in> K" "U \<in> K" for S T U
  proof -
    have c: "S \<in> poly_carrier" "T \<in> poly_carrier" "U \<in> poly_carrier"
      using K by (blast intro: Kc)+
    have "mult S (T \<oplus>\<^sub>P U) = pmod ((S \<otimes>\<^sub>P T) \<oplus>\<^sub>P (S \<otimes>\<^sub>P U)) p"
      unfolding mult_def using poly_mult_add_distrib_left [OF c] by simp
    also have "\<dots> = pmod (S \<otimes>\<^sub>P T) p \<oplus>\<^sub>P pmod (S \<otimes>\<^sub>P U) p"
      by (rule pmod_add [OF poly_mult_closed [OF c(1) c(2)] poly_mult_closed [OF c(1) c(3)] p pnz])
    finally show ?thesis unfolding mult_def .
  qed
  \<comment> \<open>A nonzero remainder is invertible: it escapes the maximal ideal \<open>(p)\<close>.\<close>
  have inverse: "\<exists>T \<in> K. mult S T = \<one>\<^sub>P" if S: "S \<in> K" and Snz: "S \<noteq> \<zero>\<^sub>P" for S
  proof -
    interpret I: ideal_in_comm_ring "poly_pideal p" poly_carrier "(\<oplus>\<^sub>P)" "(\<otimes>\<^sub>P)" "\<zero>\<^sub>P" "\<one>\<^sub>P"
      by (rule poly_pideal_in_comm_ring [OF p])
    have Sc: "S \<in> poly_carrier" using S by (rule Kc)
    have "pmod S p \<noteq> \<zero>\<^sub>P" using Ksmall [OF S] Snz by simp
    then have SnotI: "S \<notin> poly_pideal p" using poly_pideal_iff_pmod [OF p pnz Sc] by simp
    have "\<one>\<^sub>P \<in> I.ext_ideal S"
      using I.maximal_ext_ideal_eq_whole [OF poly_irreducible_maximal [OF irr] Sc SnotI]
            poly_one_closed by simp
    then obtain m r where m: "m \<in> poly_pideal p" and r: "r \<in> poly_carrier"
        and one: "\<one>\<^sub>P = m \<oplus>\<^sub>P (r \<otimes>\<^sub>P S)"
      unfolding I.ext_ideal_def by blast
    have mc: "m \<in> poly_carrier"
    proof -
      obtain u where u: "u \<in> poly_carrier" and meq: "m = u \<otimes>\<^sub>P p"
        using m unfolding poly_pideal_def by blast
      show ?thesis using meq poly_mult_closed [OF u p] by simp
    qed
    have mz: "pmod m p = \<zero>\<^sub>P" using m poly_pideal_iff_pmod [OF p pnz mc] by simp
    \<comment> \<open>Reduce the combination: the multiple of @{term p} disappears.\<close>
    have "\<one>\<^sub>P = pmod \<one>\<^sub>P p" using pmod_small [OF p pnz poly_one_closed] Kone Ksmall by simp
    also have "\<dots> = pmod m p \<oplus>\<^sub>P pmod (r \<otimes>\<^sub>P S) p"
      using one pmod_add [OF mc poly_mult_closed [OF r Sc] p pnz] by simp
    also have "\<dots> = pmod (r \<otimes>\<^sub>P S) p"
      using mz pmod_closed [OF poly_mult_closed [OF r Sc] p pnz] by (simp add: poly_add_zero)
    also have "\<dots> = pmod (pmod r p \<otimes>\<^sub>P pmod S p) p"
      by (rule pmod_mult [OF r Sc p pnz])
    also have "\<dots> = mult S (pmod r p)"
      unfolding mult_def using Ksmall [OF S] poly_mult_comm [OF Sc pmod_closed [OF r p pnz]] by simp
    finally have "mult S (pmod r p) = \<one>\<^sub>P" by simp
    moreover have "pmod r p \<in> K" unfolding K_def using r p pnz by (rule pmod_low_poly)
    ultimately show ?thesis by blast
  qed
  \<comment> \<open>Assemble.\<close>
  have grp: "Group K (\<oplus>\<^sub>P) \<zero>\<^sub>P"
  proof (rule GroupI)
    show "\<And>x y. \<lbrakk> x \<in> K; y \<in> K \<rbrakk> \<Longrightarrow> x \<oplus>\<^sub>P y \<in> K" by (rule Kadd)
    show "\<zero>\<^sub>P \<in> K" by (rule Kzero)
    show "\<And>x y z. \<lbrakk> x \<in> K; y \<in> K; z \<in> K \<rbrakk> \<Longrightarrow> (x \<oplus>\<^sub>P y) \<oplus>\<^sub>P z = x \<oplus>\<^sub>P (y \<oplus>\<^sub>P z)"
      using Kc by (blast intro: poly_add_assoc)
    show "\<And>x. x \<in> K \<Longrightarrow> \<zero>\<^sub>P \<oplus>\<^sub>P x = x" using Kc by (blast intro: poly_add_zero)
    show "\<And>x. x \<in> K \<Longrightarrow> x \<oplus>\<^sub>P \<zero>\<^sub>P = x"
      using Kc poly_add_comm poly_zero_closed by (metis poly_add_zero)
    show "\<And>x. x \<in> K \<Longrightarrow> \<exists>y \<in> K. x \<oplus>\<^sub>P y = \<zero>\<^sub>P \<and> y \<oplus>\<^sub>P x = \<zero>\<^sub>P"
      using Kneg Kc poly_add_neg poly_add_neg_right by blast
  qed
  interpret A: Group K "(\<oplus>\<^sub>P)" "\<zero>\<^sub>P" by (rule grp)
  interpret A: Abelian_Group K "(\<oplus>\<^sub>P)" "\<zero>\<^sub>P"
    by unfold_locales (use Kc poly_add_comm in blast)
  have mult_one': "mult S \<one>\<^sub>P = S" if S: "S \<in> K" for S
  proof -
    have "mult S \<one>\<^sub>P = mult \<one>\<^sub>P S" by (rule mult_comm [OF S Kone])
    also have "\<dots> = S" by (rule mult_one [OF S])
    finally show ?thesis .
  qed
  interpret M: commutative_monoid K mult "\<one>\<^sub>P"
  proof unfold_locales
    show "\<And>a b. \<lbrakk> a \<in> K; b \<in> K \<rbrakk> \<Longrightarrow> mult a b \<in> K" by (rule Kmult)
    show "\<one>\<^sub>P \<in> K" by (rule Kone)
    show "\<And>a b c. \<lbrakk> a \<in> K; b \<in> K; c \<in> K \<rbrakk>
                   \<Longrightarrow> mult (mult a b) c = mult a (mult b c)" by (rule mult_assoc)
    show "\<And>a. a \<in> K \<Longrightarrow> mult \<one>\<^sub>P a = a" by (rule mult_one)
    show "\<And>a. a \<in> K \<Longrightarrow> mult a \<one>\<^sub>P = a" by (rule mult_one')
    show "\<And>x y. \<lbrakk> x \<in> K; y \<in> K \<rbrakk> \<Longrightarrow> mult x y = mult y x" by (rule mult_comm)
  qed
  show ?thesis
    unfolding sym [OF K_def] sym [OF mult_def]
  proof unfold_locales
    show "\<And>x y z. \<lbrakk> x \<in> K; y \<in> K; z \<in> K \<rbrakk>
                   \<Longrightarrow> mult x (y \<oplus>\<^sub>P z) = mult x y \<oplus>\<^sub>P mult x z" by (rule distrib)
    show "\<And>x y z. \<lbrakk> x \<in> K; y \<in> K; z \<in> K \<rbrakk>
                   \<Longrightarrow> mult (y \<oplus>\<^sub>P z) x = mult y x \<oplus>\<^sub>P mult z x"
    proof -
      fix x y z assume K: "x \<in> K" "y \<in> K" "z \<in> K"
      have "mult (y \<oplus>\<^sub>P z) x = mult x (y \<oplus>\<^sub>P z)"
        by (rule mult_comm [OF Kadd [OF K(2) K(3)] K(1)])
      also have "\<dots> = mult x y \<oplus>\<^sub>P mult x z" by (rule distrib [OF K])
      also have "\<dots> = mult y x \<oplus>\<^sub>P mult z x"
        using mult_comm [OF K(1) K(2)] mult_comm [OF K(1) K(3)] by simp
      finally show "mult (y \<oplus>\<^sub>P z) x = mult y x \<oplus>\<^sub>P mult z x" .
    qed
    show "\<one>\<^sub>P \<noteq> \<zero>\<^sub>P" by (metis nontrivial poly_one_def poly_zero_def)
    show "\<And>x. \<lbrakk> x \<in> K; x \<noteq> \<zero>\<^sub>P \<rbrakk> \<Longrightarrow> M.invertible x"
    proof -
      fix x assume x: "x \<in> K" and xnz: "x \<noteq> \<zero>\<^sub>P"
      obtain T where T: "T \<in> K" and xT: "mult x T = \<one>\<^sub>P" using inverse [OF x xnz] by blast
      have "mult T x = \<one>\<^sub>P" using xT mult_comm [OF x T] by simp
      with xT T show "M.invertible x" by (blast intro: M.invertibleI)
    qed
  qed
qed

text \<open>\<^emph>\<open>The adjoined root really is a root.\<close>  Evaluating in the field of remainders, at the variable
  and with the coefficients embedded as constants, reduces the polynomial modulo the modulus.  So the
  class of @{term q} is the value of @{term q} at the variable, and when the modulus divides @{term q}
  that value is zero.

  Reduction is a ring homomorphism from @{text "F[X]"} onto the remainders, by
  @{thm [source] pmod_add} and @{thm [source] pmod_mult}, and it fixes the variable and the constants
  because those are already of low degree --- which is where @{term "2 \<le> degree p"} is needed.  So
  @{thm [source] eval_hom} applies, and the source evaluation is the polynomial itself by
  @{thm [source] eval_const_lift_at_var}.\<close>
theorem eval_remainder_at_var:
  assumes irr: "poly_irreducible p" and d2: "2 \<le> degree p" and q: "q \<in> poly_carrier"
  shows "Ring.eval (low_poly (degree p)) (\<oplus>\<^sub>P) (\<lambda>S T. pmod (S \<otimes>\<^sub>P T) p)
           \<zero>\<^sub>P \<one>\<^sub>P X\<^sub>P (\<lambda>k. poly_const (q k)) = pmod q p"
proof -
  have pc: "p \<in> poly_carrier" using irr by (rule poly_irreducibleD_carrier)
  have pnz: "p \<noteq> \<zero>\<^sub>P" using irr by (rule poly_irreducibleD_nonzero)
  have RB: "Ring (low_poly (degree p)) (\<oplus>\<^sub>P) (\<lambda>S T. pmod (S \<otimes>\<^sub>P T) p) \<zero>\<^sub>P \<one>\<^sub>P"
    using remainder_field [OF irr] by (simp add: Field_def commutative_ring_def)
  have coeffR: "q k \<in> R" for k using q by (rule poly_carrier_coeff_closed)
  have constc: "poly_const (q k) \<in> poly_carrier" for k using coeffR by (rule poly_const_closed)
  \<comment> \<open>Reduction fixes the constants and the variable, both being of low degree.\<close>
  have fix_const: "pmod (poly_const (q k)) p = poly_const (q k)" for k
  proof (rule pmod_small [OF pc pnz constc])
    have "degree (poly_const (q k)) = 0" using degree_const_le by (simp add: le_zero_eq)
    then show "poly_const (q k) = \<zero>\<^sub>P \<or> degree (poly_const (q k)) < degree p"
      using d2 by simp
  qed
  have fix_var: "pmod X\<^sub>P p = X\<^sub>P"
    by (rule pmod_small [OF pc pnz var_closed])
       (use d2 degree_var [OF nontrivial] in simp)
  have "Ring.eval (low_poly (degree p)) (\<oplus>\<^sub>P) (\<lambda>S T. pmod (S \<otimes>\<^sub>P T) p)
          \<zero>\<^sub>P \<one>\<^sub>P (pmod X\<^sub>P p) (\<lambda>k. pmod (poly_const (q k)) p)
        = pmod (Ring.eval poly_carrier (\<oplus>\<^sub>P) (\<otimes>\<^sub>P) \<zero>\<^sub>P \<one>\<^sub>P X\<^sub>P (\<lambda>k. poly_const (q k))) p"
  proof (rule eval_hom [OF poly_ring RB])
    show "\<And>S. S \<in> poly_carrier \<Longrightarrow> pmod S p \<in> low_poly (degree p)"
      using pc pnz by (blast intro: pmod_low_poly)
    show "pmod \<zero>\<^sub>P p = \<zero>\<^sub>P" by (rule pmod_small [OF pc pnz poly_zero_closed]) simp
    show "pmod \<one>\<^sub>P p = \<one>\<^sub>P"
      by (rule pmod_small [OF pc pnz poly_one_closed]) (use d2 degree_one in simp)
    show "\<And>S T. \<lbrakk> S \<in> poly_carrier; T \<in> poly_carrier \<rbrakk>
                  \<Longrightarrow> pmod (S \<oplus>\<^sub>P T) p = pmod S p \<oplus>\<^sub>P pmod T p"
      using pc pnz by (blast intro: pmod_add)
    show "\<And>S T. \<lbrakk> S \<in> poly_carrier; T \<in> poly_carrier \<rbrakk>
                  \<Longrightarrow> pmod (S \<otimes>\<^sub>P T) p = pmod (pmod S p \<otimes>\<^sub>P pmod T p) p"
      using pc pnz by (blast intro: pmod_mult)
    show "X\<^sub>P \<in> poly_carrier" by (rule var_closed)
    show "\<And>k. poly_const (q k) \<in> poly_carrier" by (rule constc)
    show "Ring.degree \<zero>\<^sub>P (\<lambda>k. pmod (poly_const (q k)) p)
          = Ring.degree \<zero>\<^sub>P (\<lambda>k. poly_const (q k))"
      using fix_const by simp
  qed
  then show ?thesis
    using fix_var fix_const eval_const_lift_at_var [OF q] by simp
qed

end

end