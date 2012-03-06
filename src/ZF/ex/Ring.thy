(* Title:  ZF/ex/Ring.thy

*)

header {* Rings *}

theory Ring imports Group begin

no_notation
  cadd  (infixl "\<oplus>" 65) and
  cmult  (infixl "\<otimes>" 70)

(*First, we must simulate a record declaration:
record ring = monoid +
  add :: "[i, i] => i" (infixl "\<oplus>\<index>" 65)
  zero :: i ("\<zero>\<index>")
*)

definition
  add_field :: "i => i" where
  "add_field(M) = fst(snd(snd(snd(M))))"

definition
  ring_add :: "[i, i, i] => i" (infixl "\<oplus>\<index>" 65) where
  "ring_add(M,x,y) = add_field(M) ` <x,y>"

definition
  zero :: "i => i" ("\<zero>\<index>") where
  "zero(M) = fst(snd(snd(snd(snd(M)))))"


lemma add_field_eq [simp]: "add_field(<C,M,I,A,z>) = A"
  by (simp add: add_field_def)

lemma add_eq [simp]: "ring_add(<C,M,I,A,z>, x, y) = A ` <x,y>"
  by (simp add: ring_add_def)

lemma zero_eq [simp]: "zero(<C,M,I,A,Z,z>) = Z"
  by (simp add: zero_def)


text {* Derived operations. *}

definition
  a_inv :: "[i,i] => i" ("\<ominus>\<index> _" [81] 80) where
  "a_inv(R) == m_inv (<carrier(R), add_field(R), zero(R), 0>)"

definition
  minus :: "[i,i,i] => i" (infixl "\<ominus>\<index>" 65) where
  "\<lbrakk>x \<in> carrier(R); y \<in> carrier(R)\<rbrakk> \<Longrightarrow> x \<ominus>\<^bsub>R\<^esub> y = x \<oplus>\<^bsub>R\<^esub> (\<ominus>\<^bsub>R\<^esub> y)"

locale abelian_monoid = fixes G (structure)
  assumes a_comm_monoid:
    "comm_monoid (<carrier(G), add_field(G), zero(G), 0>)"

text {*
  The following definition is redundant but simple to use.
*}

locale abelian_group = abelian_monoid +
  assumes a_comm_group:
    "comm_group (<carrier(G), add_field(G), zero(G), 0>)"

locale ring = abelian_group R + monoid R for R (structure) +
  assumes l_distr: "\<lbrakk>x \<in> carrier(R); y \<in> carrier(R); z \<in> carrier(R)\<rbrakk>
      \<Longrightarrow> (x \<oplus> y) \<cdot> z = x \<cdot> z \<oplus> y \<cdot> z"
    and r_distr: "\<lbrakk>x \<in> carrier(R); y \<in> carrier(R); z \<in> carrier(R)\<rbrakk>
      \<Longrightarrow> z \<cdot> (x \<oplus> y) = z \<cdot> x \<oplus> z \<cdot> y"

locale cring = ring + comm_monoid R

locale "domain" = cring +
  assumes one_not_zero [simp]: "\<one> \<noteq> \<zero>"
    and integral: "\<lbrakk>a \<cdot> b = \<zero>; a \<in> carrier(R); b \<in> carrier(R)\<rbrakk> \<Longrightarrow>
                  a = \<zero> | b = \<zero>"


subsection {* Basic Properties *}

lemma (in abelian_monoid) a_monoid:
     "monoid (<carrier(G), add_field(G), zero(G), 0>)"
apply (insert a_comm_monoid)
apply (simp add: comm_monoid_def)
done

lemma (in abelian_group) a_group:
     "group (<carrier(G), add_field(G), zero(G), 0>)"
apply (insert a_comm_group)
apply (simp add: comm_group_def group_def)
done


lemma (in abelian_monoid) l_zero [simp]:
     "x \<in> carrier(G) \<Longrightarrow> \<zero> \<oplus> x = x"
apply (insert monoid.l_one [OF a_monoid])
apply (simp add: ring_add_def)
done

lemma (in abelian_monoid) zero_closed [intro, simp]:
     "\<zero> \<in> carrier(G)"
by (rule monoid.one_closed [OF a_monoid, simplified])

lemma (in abelian_group) a_inv_closed [intro, simp]:
     "x \<in> carrier(G) \<Longrightarrow> \<ominus> x \<in> carrier(G)"
by (simp add: a_inv_def  group.inv_closed [OF a_group, simplified])

lemma (in abelian_monoid) a_closed [intro, simp]:
     "[| x \<in> carrier(G); y \<in> carrier(G) |] ==> x \<oplus> y \<in> carrier(G)"
by (rule monoid.m_closed [OF a_monoid,
                  simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_group) minus_closed [intro, simp]:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<ominus> y \<in> carrier(G)"
by (simp add: minus_def)

lemma (in abelian_group) a_l_cancel [simp]:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (x \<oplus> y = x \<oplus> z) <-> (y = z)"
by (rule group.l_cancel [OF a_group,
             simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_group) a_r_cancel [simp]:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (y \<oplus> x = z \<oplus> x) <-> (y = z)"
by (rule group.r_cancel [OF a_group, simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_monoid) a_assoc:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk>
   \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
by (rule monoid.m_assoc [OF a_monoid, simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_group) l_neg:
     "x \<in> carrier(G) \<Longrightarrow> \<ominus> x \<oplus> x = \<zero>"
by (simp add: a_inv_def
     group.l_inv [OF a_group, simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_monoid) a_comm:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
by (rule comm_monoid.m_comm [OF a_comm_monoid,
    simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_monoid) a_lcomm:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> x \<oplus> (y \<oplus> z) = y \<oplus> (x \<oplus> z)"
by (rule comm_monoid.m_lcomm [OF a_comm_monoid,
    simplified, simplified ring_add_def [symmetric]])

lemma (in abelian_monoid) r_zero [simp]:
     "x \<in> carrier(G) \<Longrightarrow> x \<oplus> \<zero> = x"
  using monoid.r_one [OF a_monoid]
  by (simp add: ring_add_def [symmetric])

lemma (in abelian_group) r_neg:
     "x \<in> carrier(G) \<Longrightarrow> x \<oplus> (\<ominus> x) = \<zero>"
  using group.r_inv [OF a_group]
  by (simp add: a_inv_def ring_add_def [symmetric])

lemma (in abelian_group) minus_zero [simp]:
     "\<ominus> \<zero> = \<zero>"
  by (simp add: a_inv_def
    group.inv_one [OF a_group, simplified ])

lemma (in abelian_group) minus_minus [simp]:
     "x \<in> carrier(G) \<Longrightarrow> \<ominus> (\<ominus> x) = x"
  using group.inv_inv [OF a_group, simplified]
  by (simp add: a_inv_def)

lemma (in abelian_group) minus_add:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> \<ominus> (x \<oplus> y) = \<ominus> x \<oplus> \<ominus> y"
  using comm_group.inv_mult [OF a_comm_group]
  by (simp add: a_inv_def ring_add_def [symmetric])

lemmas (in abelian_monoid) a_ac = a_assoc a_comm a_lcomm

text {*
  The following proofs are from Jacobson, Basic Algebra I, pp.~88--89
*}

context ring
begin

lemma l_null [simp]: "x \<in> carrier(R) \<Longrightarrow> \<zero> \<cdot> x = \<zero>"
proof -
  assume R: "x \<in> carrier(R)"
  then have "\<zero> \<cdot> x \<oplus> \<zero> \<cdot> x = (\<zero> \<oplus> \<zero>) \<cdot> x"
    by (blast intro: l_distr [THEN sym])
  also from R have "... = \<zero> \<cdot> x \<oplus> \<zero>" by simp
  finally have "\<zero> \<cdot> x \<oplus> \<zero> \<cdot> x = \<zero> \<cdot> x \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma r_null [simp]: "x \<in> carrier(R) \<Longrightarrow> x \<cdot> \<zero> = \<zero>"
proof -
  assume R: "x \<in> carrier(R)"
  then have "x \<cdot> \<zero> \<oplus> x \<cdot> \<zero> = x \<cdot> (\<zero> \<oplus> \<zero>)"
    by (simp add: r_distr del: l_zero r_zero)
  also from R have "... = x \<cdot> \<zero> \<oplus> \<zero>" by simp
  finally have "x \<cdot> \<zero> \<oplus> x \<cdot> \<zero> = x \<cdot> \<zero> \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma l_minus:
  "\<lbrakk>x \<in> carrier(R); y \<in> carrier(R)\<rbrakk> \<Longrightarrow> \<ominus> x \<cdot> y = \<ominus> (x \<cdot> y)"
proof -
  assume R: "x \<in> carrier(R)" "y \<in> carrier(R)"
  then have "(\<ominus> x) \<cdot> y \<oplus> x \<cdot> y = (\<ominus> x \<oplus> x) \<cdot> y" by (simp add: l_distr)
  also from R have "... = \<zero>" by (simp add: l_neg)
  finally have "(\<ominus> x) \<cdot> y \<oplus> x \<cdot> y = \<zero>" .
  with R have "(\<ominus> x) \<cdot> y \<oplus> x \<cdot> y \<oplus> \<ominus> (x \<cdot> y) = \<zero> \<oplus> \<ominus> (x \<cdot> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg)
qed

lemma r_minus:
  "\<lbrakk>x \<in> carrier(R); y \<in> carrier(R)\<rbrakk> \<Longrightarrow> x \<cdot> \<ominus> y = \<ominus> (x \<cdot> y)"
proof -
  assume R: "x \<in> carrier(R)" "y \<in> carrier(R)"
  then have "x \<cdot> (\<ominus> y) \<oplus> x \<cdot> y = x \<cdot> (\<ominus> y \<oplus> y)" by (simp add: r_distr)
  also from R have "... = \<zero>" by (simp add: l_neg)
  finally have "x \<cdot> (\<ominus> y) \<oplus> x \<cdot> y = \<zero>" .
  with R have "x \<cdot> (\<ominus> y) \<oplus> x \<cdot> y \<oplus> \<ominus> (x \<cdot> y) = \<zero> \<oplus> \<ominus> (x \<cdot> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg)
qed

lemma minus_eq:
  "\<lbrakk>x \<in> carrier(R); y \<in> carrier(R)\<rbrakk> \<Longrightarrow> x \<ominus> y = x \<oplus> \<ominus> y"
  by (simp only: minus_def)

end


subsection {* Morphisms *}

definition
  ring_hom :: "[i,i] => i" where
  "ring_hom(R,S) ==
    {h \<in> carrier(R) -> carrier(S).
      (\<forall>x y. x \<in> carrier(R) & y \<in> carrier(R) -->
        h ` (x \<cdot>\<^bsub>R\<^esub> y) = (h ` x) \<cdot>\<^bsub>S\<^esub> (h ` y) &
        h ` (x \<oplus>\<^bsub>R\<^esub> y) = (h ` x) \<oplus>\<^bsub>S\<^esub> (h ` y)) &
      h ` \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub>}"

lemma ring_hom_memI:
  assumes hom_type: "h \<in> carrier(R) \<rightarrow> carrier(S)"
    and hom_mult: "\<And>x y. \<lbrakk>x \<in> carrier(R); y \<in> carrier(R)\<rbrakk> \<Longrightarrow>
      h ` (x \<cdot>\<^bsub>R\<^esub> y) = (h ` x) \<cdot>\<^bsub>S\<^esub> (h ` y)"
    and hom_add: "\<And>x y. \<lbrakk>x \<in> carrier(R); y \<in> carrier(R)\<rbrakk> \<Longrightarrow>
      h ` (x \<oplus>\<^bsub>R\<^esub> y) = (h ` x) \<oplus>\<^bsub>S\<^esub> (h ` y)"
    and hom_one: "h ` \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub>"
  shows "h \<in> ring_hom(R,S)"
by (auto simp add: ring_hom_def assms)

lemma ring_hom_closed:
     "\<lbrakk>h \<in> ring_hom(R,S); x \<in> carrier(R)\<rbrakk> \<Longrightarrow> h ` x \<in> carrier(S)"
by (auto simp add: ring_hom_def)

lemma ring_hom_mult:
     "\<lbrakk>h \<in> ring_hom(R,S); x \<in> carrier(R); y \<in> carrier(R)\<rbrakk>
      \<Longrightarrow> h ` (x \<cdot>\<^bsub>R\<^esub> y) = (h ` x) \<cdot>\<^bsub>S\<^esub> (h ` y)"
by (simp add: ring_hom_def)

lemma ring_hom_add:
     "\<lbrakk>h \<in> ring_hom(R,S); x \<in> carrier(R); y \<in> carrier(R)\<rbrakk>
      \<Longrightarrow> h ` (x \<oplus>\<^bsub>R\<^esub> y) = (h ` x) \<oplus>\<^bsub>S\<^esub> (h ` y)"
by (simp add: ring_hom_def)

lemma ring_hom_one: "h \<in> ring_hom(R,S) \<Longrightarrow> h ` \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub>"
by (simp add: ring_hom_def)

locale ring_hom_cring = R: cring R + S: cring S
  for R (structure) and S (structure) and h +
  assumes homh [simp, intro]: "h \<in> ring_hom(R,S)"
  notes hom_closed [simp, intro] = ring_hom_closed [OF homh]
    and hom_mult [simp] = ring_hom_mult [OF homh]
    and hom_add [simp] = ring_hom_add [OF homh]
    and hom_one [simp] = ring_hom_one [OF homh]

lemma (in ring_hom_cring) hom_zero [simp]:
     "h ` \<zero>\<^bsub>R\<^esub> = \<zero>\<^bsub>S\<^esub>"
proof -
  have "h ` \<zero>\<^bsub>R\<^esub> \<oplus>\<^bsub>S\<^esub> h ` \<zero> = h ` \<zero>\<^bsub>R\<^esub> \<oplus>\<^bsub>S\<^esub> \<zero>\<^bsub>S\<^esub>"
    by (simp add: hom_add [symmetric] del: hom_add)
  then show ?thesis by (simp del: S.r_zero)
qed

lemma (in ring_hom_cring) hom_a_inv [simp]:
     "x \<in> carrier(R) \<Longrightarrow> h ` (\<ominus>\<^bsub>R\<^esub> x) = \<ominus>\<^bsub>S\<^esub> h ` x"
proof -
  assume R: "x \<in> carrier(R)"
  then have "h ` x \<oplus>\<^bsub>S\<^esub> h ` (\<ominus> x) = h ` x \<oplus>\<^bsub>S\<^esub> (\<ominus>\<^bsub>S\<^esub> (h ` x))"
    by (simp add: hom_add [symmetric] R.r_neg S.r_neg del: hom_add)
  with R show ?thesis by simp
qed

lemma (in ring) id_ring_hom [simp]: "id(carrier(R)) \<in> ring_hom(R,R)"
apply (rule ring_hom_memI)
apply (auto simp add: id_type)
done

end
