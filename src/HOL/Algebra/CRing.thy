(*
  Title:     The algebraic hierarchy of rings
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* Abelian Groups *}

theory CRing = FiniteProduct
files ("ringsimp.ML"):

record 'a ring = "'a monoid" +
  zero :: 'a ("\<zero>\<index>")
  add :: "['a, 'a] => 'a" (infixl "\<oplus>\<index>" 65)

text {* Derived operations. *}

constdefs
  a_inv :: "[('a, 'm) ring_scheme, 'a ] => 'a" ("\<ominus>\<index> _" [81] 80)
  "a_inv R == m_inv (| carrier = carrier R, mult = add R, one = zero R |)"

  minus :: "[('a, 'm) ring_scheme, 'a, 'a] => 'a" (infixl "\<ominus>\<index>" 65)
  "[| x \<in> carrier R; y \<in> carrier R |] ==> minus R x y == add R x (a_inv R y)"

locale abelian_monoid = struct G +
  assumes a_comm_monoid: "comm_monoid (| carrier = carrier G,
      mult = add G, one = zero G |)"

text {*
  The following definition is redundant but simple to use.
*}

locale abelian_group = abelian_monoid +
  assumes a_comm_group: "comm_group (| carrier = carrier G,
      mult = add G, one = zero G |)"

subsection {* Basic Properties *}

lemma abelian_monoidI:
  assumes a_closed:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> add R x y \<in> carrier R"
    and zero_closed: "zero R \<in> carrier R"
    and a_assoc:
      "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |] ==>
      add R (add R x y) z = add R x (add R y z)"
    and l_zero: "!!x. x \<in> carrier R ==> add R (zero R) x = x"
    and a_comm:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> add R x y = add R y x"
  shows "abelian_monoid R"
  by (auto intro!: abelian_monoid.intro comm_monoidI intro: prems)

lemma abelian_groupI:
  assumes a_closed:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> add R x y \<in> carrier R"
    and zero_closed: "zero R \<in> carrier R"
    and a_assoc:
      "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |] ==>
      add R (add R x y) z = add R x (add R y z)"
    and a_comm:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> add R x y = add R y x"
    and l_zero: "!!x. x \<in> carrier R ==> add R (zero R) x = x"
    and l_inv_ex: "!!x. x \<in> carrier R ==> EX y : carrier R. add R y x = zero R"
  shows "abelian_group R"
  by (auto intro!: abelian_group.intro abelian_monoidI
      abelian_group_axioms.intro comm_monoidI comm_groupI
    intro: prems)

(* TODO: The following thms are probably unnecessary. *)

lemma (in abelian_monoid) a_magma:
  "magma (| carrier = carrier G, mult = add G, one = zero G |)"
  by (rule comm_monoid.axioms) (rule a_comm_monoid)

lemma (in abelian_monoid) a_semigroup:
  "semigroup (| carrier = carrier G, mult = add G, one = zero G |)"
  by (unfold semigroup_def) (fast intro: comm_monoid.axioms a_comm_monoid)

lemma (in abelian_monoid) a_monoid:
  "monoid (| carrier = carrier G, mult = add G, one = zero G |)"
  by (unfold monoid_def) (fast intro: a_comm_monoid comm_monoid.axioms)

lemma (in abelian_group) a_group:
  "group (| carrier = carrier G, mult = add G, one = zero G |)"
  by (unfold group_def semigroup_def)
    (fast intro: comm_group.axioms a_comm_group)

lemma (in abelian_monoid) a_comm_semigroup:
  "comm_semigroup (| carrier = carrier G, mult = add G, one = zero G |)"
  by (unfold comm_semigroup_def semigroup_def)
    (fast intro: comm_monoid.axioms a_comm_monoid)

lemmas monoid_record_simps = partial_object.simps semigroup.simps monoid.simps

lemma (in abelian_monoid) a_closed [intro, simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<oplus> y \<in> carrier G"
  by (rule magma.m_closed [OF a_magma, simplified monoid_record_simps]) 

lemma (in abelian_monoid) zero_closed [intro, simp]:
  "\<zero> \<in> carrier G"
  by (rule monoid.one_closed [OF a_monoid, simplified monoid_record_simps])

lemma (in abelian_group) a_inv_closed [intro, simp]:
  "x \<in> carrier G ==> \<ominus> x \<in> carrier G"
  by (simp add: a_inv_def
    group.inv_closed [OF a_group, simplified monoid_record_simps])

lemma (in abelian_group) minus_closed [intro, simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<ominus> y \<in> carrier G"
  by (simp add: minus_def)

lemma (in abelian_group) a_l_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<oplus> y = x \<oplus> z) = (y = z)"
  by (rule group.l_cancel [OF a_group, simplified monoid_record_simps])

lemma (in abelian_group) a_r_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (y \<oplus> x = z \<oplus> x) = (y = z)"
  by (rule group.r_cancel [OF a_group, simplified monoid_record_simps])

lemma (in abelian_monoid) a_assoc:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
  (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  by (rule semigroup.m_assoc [OF a_semigroup, simplified monoid_record_simps])

lemma (in abelian_monoid) l_zero [simp]:
  "x \<in> carrier G ==> \<zero> \<oplus> x = x"
  by (rule monoid.l_one [OF a_monoid, simplified monoid_record_simps])

lemma (in abelian_group) l_neg:
  "x \<in> carrier G ==> \<ominus> x \<oplus> x = \<zero>"
  by (simp add: a_inv_def
    group.l_inv [OF a_group, simplified monoid_record_simps])

lemma (in abelian_monoid) a_comm:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<oplus> y = y \<oplus> x"
  by (rule comm_semigroup.m_comm [OF a_comm_semigroup,
    simplified monoid_record_simps])

lemma (in abelian_monoid) a_lcomm:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   x \<oplus> (y \<oplus> z) = y \<oplus> (x \<oplus> z)"
  by (rule comm_semigroup.m_lcomm [OF a_comm_semigroup,
    simplified monoid_record_simps])

lemma (in abelian_monoid) r_zero [simp]:
  "x \<in> carrier G ==> x \<oplus> \<zero> = x"
  using monoid.r_one [OF a_monoid]
  by simp

lemma (in abelian_group) r_neg:
  "x \<in> carrier G ==> x \<oplus> (\<ominus> x) = \<zero>"
  using group.r_inv [OF a_group]
  by (simp add: a_inv_def)

lemma (in abelian_group) minus_zero [simp]:
  "\<ominus> \<zero> = \<zero>"
  by (simp add: a_inv_def
    group.inv_one [OF a_group, simplified monoid_record_simps])

lemma (in abelian_group) minus_minus [simp]:
  "x \<in> carrier G ==> \<ominus> (\<ominus> x) = x"
  using group.inv_inv [OF a_group, simplified monoid_record_simps]
  by (simp add: a_inv_def)

lemma (in abelian_group) a_inv_inj:
  "inj_on (a_inv G) (carrier G)"
  using group.inv_inj [OF a_group, simplified monoid_record_simps]
  by (simp add: a_inv_def)

lemma (in abelian_group) minus_add:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> \<ominus> (x \<oplus> y) = \<ominus> x \<oplus> \<ominus> y"
  using comm_group.inv_mult [OF a_comm_group]
  by (simp add: a_inv_def)

lemmas (in abelian_monoid) a_ac = a_assoc a_comm a_lcomm

subsection {* Sums over Finite Sets *}

text {*
  This definition makes it easy to lift lemmas from @{term finprod}.
*}

constdefs
  finsum :: "[('b, 'm) ring_scheme, 'a => 'b, 'a set] => 'b"
  "finsum G f A == finprod (| carrier = carrier G,
     mult = add G, one = zero G |) f A"

(*
  lemmas (in abelian_monoid) finsum_empty [simp] =
    comm_monoid.finprod_empty [OF a_comm_monoid, simplified]
  is dangeous, because attributes (like simplified) are applied upon opening
  the locale, simplified refers to the simpset at that time!!!

  lemmas (in abelian_monoid) finsum_empty [simp] =
    abelian_monoid.finprod_empty [OF a_abelian_monoid, folded finsum_def,
      simplified monoid_record_simps]
makes the locale slow, because proofs are repeated for every
"lemma (in abelian_monoid)" command.
When lemma is used time in UnivPoly.thy from beginning to UP_cring goes down
from 110 secs to 60 secs.
*)

lemma (in abelian_monoid) finsum_empty [simp]:
  "finsum G f {} = \<zero>"
  by (rule comm_monoid.finprod_empty [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_insert [simp]:
  "[| finite F; a \<notin> F; f \<in> F -> carrier G; f a \<in> carrier G |]
  ==> finsum G f (insert a F) = f a \<oplus> finsum G f F"
  by (rule comm_monoid.finprod_insert [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_zero [simp]:
  "finite A ==> finsum G (%i. \<zero>) A = \<zero>"
  by (rule comm_monoid.finprod_one [OF a_comm_monoid, folded finsum_def,
    simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_closed [simp]:
  fixes A
  assumes fin: "finite A" and f: "f \<in> A -> carrier G" 
  shows "finsum G f A \<in> carrier G"
  by (rule comm_monoid.finprod_closed [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_Un_Int:
  "[| finite A; finite B; g \<in> A -> carrier G; g \<in> B -> carrier G |] ==>
     finsum G g (A Un B) \<oplus> finsum G g (A Int B) =
     finsum G g A \<oplus> finsum G g B"
  by (rule comm_monoid.finprod_Un_Int [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_Un_disjoint:
  "[| finite A; finite B; A Int B = {};
      g \<in> A -> carrier G; g \<in> B -> carrier G |]
   ==> finsum G g (A Un B) = finsum G g A \<oplus> finsum G g B"
  by (rule comm_monoid.finprod_Un_disjoint [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_addf:
  "[| finite A; f \<in> A -> carrier G; g \<in> A -> carrier G |] ==>
   finsum G (%x. f x \<oplus> g x) A = (finsum G f A \<oplus> finsum G g A)"
  by (rule comm_monoid.finprod_multf [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_cong':
  "[| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> finsum G f A = finsum G g B"
  by (rule comm_monoid.finprod_cong' [OF a_comm_monoid,
    folded finsum_def, simplified monoid_record_simps]) auto

lemma (in abelian_monoid) finsum_0 [simp]:
  "f : {0::nat} -> carrier G ==> finsum G f {..0} = f 0"
  by (rule comm_monoid.finprod_0 [OF a_comm_monoid, folded finsum_def,
    simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_Suc [simp]:
  "f : {..Suc n} -> carrier G ==>
   finsum G f {..Suc n} = (f (Suc n) \<oplus> finsum G f {..n})"
  by (rule comm_monoid.finprod_Suc [OF a_comm_monoid, folded finsum_def,
    simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_Suc2:
  "f : {..Suc n} -> carrier G ==>
   finsum G f {..Suc n} = (finsum G (%i. f (Suc i)) {..n} \<oplus> f 0)"
  by (rule comm_monoid.finprod_Suc2 [OF a_comm_monoid, folded finsum_def,
    simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_add [simp]:
  "[| f : {..n} -> carrier G; g : {..n} -> carrier G |] ==>
     finsum G (%i. f i \<oplus> g i) {..n::nat} =
     finsum G f {..n} \<oplus> finsum G g {..n}"
  by (rule comm_monoid.finprod_mult [OF a_comm_monoid, folded finsum_def,
    simplified monoid_record_simps])

lemma (in abelian_monoid) finsum_cong:
  "[| A = B; f : B -> carrier G = True;
      !!i. i : B ==> f i = g i |] ==> finsum G f A = finsum G g B"
  by (rule comm_monoid.finprod_cong [OF a_comm_monoid, folded finsum_def,
    simplified monoid_record_simps]) auto

text {*Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise @{text "g \<in> B -> carrier G"} cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful. *}

section {* The Algebraic Hierarchy of Rings *}

subsection {* Basic Definitions *}

locale ring = abelian_group R + monoid R +
  assumes l_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
    and r_distr: "[| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"

locale cring = ring + comm_monoid R

locale "domain" = cring +
  assumes one_not_zero [simp]: "\<one> ~= \<zero>"
    and integral: "[| a \<otimes> b = \<zero>; a \<in> carrier R; b \<in> carrier R |] ==>
                  a = \<zero> | b = \<zero>"

locale field = "domain" +
  assumes field_Units: "Units R = carrier R - {\<zero>}"

subsection {* Basic Facts of Rings *}

lemma ringI:
  includes struct R
  assumes abelian_group: "abelian_group R"
    and monoid: "monoid R"
    and l_distr: "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> mult R (add R x y) z = add R (mult R x z) (mult R y z)"
    and r_distr: "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
  shows "ring R"
  by (auto intro: ring.intro
    abelian_group.axioms monoid.axioms ring_axioms.intro prems)

lemma (in ring) is_abelian_group:
  "abelian_group R"
  by (auto intro!: abelian_groupI a_assoc a_comm l_neg)

lemma (in ring) is_monoid:
  "monoid R"
  by (auto intro!: monoidI m_assoc)

lemma cringI:
  includes struct R
  assumes abelian_group: "abelian_group R"
    and comm_monoid: "comm_monoid R"
    and l_distr: "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> mult R (add R x y) z = add R (mult R x z) (mult R y z)"
  shows "cring R"
  proof (rule cring.intro)
    show "ring_axioms R"
    -- {* Right-distributivity follows from left-distributivity and
          commutativity. *}
    proof (rule ring_axioms.intro)
      fix x y z
      assume R: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
      note [simp]= comm_monoid.axioms [OF comm_monoid]
        abelian_group.axioms [OF abelian_group]
        abelian_monoid.a_closed
        magma.m_closed
        
      from R have "z \<otimes> (x \<oplus> y) = (x \<oplus> y) \<otimes> z"
        by (simp add: comm_semigroup.m_comm [OF comm_semigroup.intro])
      also from R have "... = x \<otimes> z \<oplus> y \<otimes> z" by (simp add: l_distr)
      also from R have "... = z \<otimes> x \<oplus> z \<otimes> y"
        by (simp add: comm_semigroup.m_comm [OF comm_semigroup.intro])
      finally show "z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y" .
    qed
  qed (auto intro: cring.intro
      abelian_group.axioms comm_monoid.axioms ring_axioms.intro prems)

lemma (in cring) is_comm_monoid:
  "comm_monoid R"
  by (auto intro!: comm_monoidI m_assoc m_comm)

subsection {* Normaliser for Rings *}

lemma (in abelian_group) r_neg2:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<oplus> (\<ominus> x \<oplus> y) = y"
proof -
  assume G: "x \<in> carrier G" "y \<in> carrier G"
  then have "(x \<oplus> \<ominus> x) \<oplus> y = y"
    by (simp only: r_neg l_zero)
  with G show ?thesis 
    by (simp add: a_ac)
qed

lemma (in abelian_group) r_neg1:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> \<ominus> x \<oplus> (x \<oplus> y) = y"
proof -
  assume G: "x \<in> carrier G" "y \<in> carrier G"
  then have "(\<ominus> x \<oplus> x) \<oplus> y = y" 
    by (simp only: l_neg l_zero)
  with G show ?thesis by (simp add: a_ac)
qed

text {* 
  The following proofs are from Jacobson, Basic Algebra I, pp.~88--89
*}

lemma (in ring) l_null [simp]:
  "x \<in> carrier R ==> \<zero> \<otimes> x = \<zero>"
proof -
  assume R: "x \<in> carrier R"
  then have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = (\<zero> \<oplus> \<zero>) \<otimes> x"
    by (simp add: l_distr del: l_zero r_zero)
  also from R have "... = \<zero> \<otimes> x \<oplus> \<zero>" by simp
  finally have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = \<zero> \<otimes> x \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma (in ring) r_null [simp]:
  "x \<in> carrier R ==> x \<otimes> \<zero> = \<zero>"
proof -
  assume R: "x \<in> carrier R"
  then have "x \<otimes> \<zero> \<oplus> x \<otimes> \<zero> = x \<otimes> (\<zero> \<oplus> \<zero>)"
    by (simp add: r_distr del: l_zero r_zero)
  also from R have "... = x \<otimes> \<zero> \<oplus> \<zero>" by simp
  finally have "x \<otimes> \<zero> \<oplus> x \<otimes> \<zero> = x \<otimes> \<zero> \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma (in ring) l_minus:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> \<ominus> x \<otimes> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = (\<ominus> x \<oplus> x) \<otimes> y" by (simp add: l_distr)
  also from R have "... = \<zero>" by (simp add: l_neg l_null)
  finally have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = \<zero>" .
  with R have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg )
qed

lemma (in ring) r_minus:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<otimes> \<ominus> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y = x \<otimes> (\<ominus> y \<oplus> y)" by (simp add: r_distr)
  also from R have "... = \<zero>" by (simp add: l_neg r_null)
  finally have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y = \<zero>" .
  with R have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg )
qed

lemma (in ring) minus_eq:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<ominus> y = x \<oplus> \<ominus> y"
  by (simp only: minus_def)

lemmas (in ring) ring_simprules =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr minus_eq
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm r_distr l_null r_null l_minus r_minus

lemmas (in cring) cring_simprules =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr m_comm minus_eq
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm m_lcomm r_distr l_null r_null l_minus r_minus

use "ringsimp.ML"

method_setup algebra =
  {* Method.ctxt_args cring_normalise *}
  {* computes distributive normal form in locale context cring *}

lemma (in cring) nat_pow_zero:
  "(n::nat) ~= 0 ==> \<zero> (^) n = \<zero>"
  by (induct n) simp_all

text {* Two examples for use of method algebra *}

lemma
  includes ring R + cring S
  shows "[| a \<in> carrier R; b \<in> carrier R; c \<in> carrier S; d \<in> carrier S |] ==> 
  a \<oplus> \<ominus> (a \<oplus> \<ominus> b) = b & c \<otimes>\<^sub>2 d = d \<otimes>\<^sub>2 c"
  by algebra

lemma
  includes cring
  shows "[| a \<in> carrier R; b \<in> carrier R |] ==> a \<ominus> (a \<ominus> b) = b"
  by algebra

subsection {* Sums over Finite Sets *}

lemma (in cring) finsum_ldistr:
  "[| finite A; a \<in> carrier R; f \<in> A -> carrier R |] ==>
   finsum R f A \<otimes> a = finsum R (%i. f i \<otimes> a) A"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case (insert F x) then show ?case by (simp add: Pi_def l_distr)
qed

lemma (in cring) finsum_rdistr:
  "[| finite A; a \<in> carrier R; f \<in> A -> carrier R |] ==>
   a \<otimes> finsum R f A = finsum R (%i. a \<otimes> f i) A"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case (insert F x) then show ?case by (simp add: Pi_def r_distr)
qed

subsection {* Facts of Integral Domains *}

lemma (in "domain") zero_not_one [simp]:
  "\<zero> ~= \<one>"
  by (rule not_sym) simp

lemma (in "domain") integral_iff: (* not by default a simp rule! *)
  "[| a \<in> carrier R; b \<in> carrier R |] ==> (a \<otimes> b = \<zero>) = (a = \<zero> | b = \<zero>)"
proof
  assume "a \<in> carrier R" "b \<in> carrier R" "a \<otimes> b = \<zero>"
  then show "a = \<zero> | b = \<zero>" by (simp add: integral)
next
  assume "a \<in> carrier R" "b \<in> carrier R" "a = \<zero> | b = \<zero>"
  then show "a \<otimes> b = \<zero>" by auto
qed

lemma (in "domain") m_lcancel:
  assumes prem: "a ~= \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "(a \<otimes> b = a \<otimes> c) = (b = c)"
proof
  assume eq: "a \<otimes> b = a \<otimes> c"
  with R have "a \<otimes> (b \<ominus> c) = \<zero>" by algebra
  with R have "a = \<zero> | (b \<ominus> c) = \<zero>" by (simp add: integral_iff)
  with prem and R have "b \<ominus> c = \<zero>" by auto 
  with R have "b = b \<ominus> (b \<ominus> c)" by algebra 
  also from R have "b \<ominus> (b \<ominus> c) = c" by algebra
  finally show "b = c" .
next
  assume "b = c" then show "a \<otimes> b = a \<otimes> c" by simp
qed

lemma (in "domain") m_rcancel:
  assumes prem: "a ~= \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows conc: "(b \<otimes> a = c \<otimes> a) = (b = c)"
proof -
  from prem and R have "(a \<otimes> b = a \<otimes> c) = (b = c)" by (rule m_lcancel)
  with R show ?thesis by algebra
qed

subsection {* Morphisms *}

constdefs
  ring_hom :: "[('a, 'm) ring_scheme, ('b, 'n) ring_scheme] => ('a => 'b) set"
  "ring_hom R S == {h. h \<in> carrier R -> carrier S &
      (ALL x y. x \<in> carrier R & y \<in> carrier R -->
        h (mult R x y) = mult S (h x) (h y) &
        h (add R x y) = add S (h x) (h y)) &
      h (one R) = one S}"

lemma ring_hom_memI:
  assumes hom_closed: "!!x. x \<in> carrier R ==> h x \<in> carrier S"
    and hom_mult: "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==>
      h (mult R x y) = mult S (h x) (h y)"
    and hom_add: "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==>
      h (add R x y) = add S (h x) (h y)"
    and hom_one: "h (one R) = one S"
  shows "h \<in> ring_hom R S"
  by (auto simp add: ring_hom_def prems Pi_def)

lemma ring_hom_closed:
  "[| h \<in> ring_hom R S; x \<in> carrier R |] ==> h x \<in> carrier S"
  by (auto simp add: ring_hom_def funcset_mem)

lemma ring_hom_mult:
  "[| h \<in> ring_hom R S; x \<in> carrier R; y \<in> carrier R |] ==>
  h (mult R x y) = mult S (h x) (h y)"
  by (simp add: ring_hom_def)

lemma ring_hom_add:
  "[| h \<in> ring_hom R S; x \<in> carrier R; y \<in> carrier R |] ==>
  h (add R x y) = add S (h x) (h y)"
  by (simp add: ring_hom_def)

lemma ring_hom_one:
  "h \<in> ring_hom R S ==> h (one R) = one S"
  by (simp add: ring_hom_def)

locale ring_hom_cring = cring R + cring S + var h +
  assumes homh [simp, intro]: "h \<in> ring_hom R S"
  notes hom_closed [simp, intro] = ring_hom_closed [OF homh]
    and hom_mult [simp] = ring_hom_mult [OF homh]
    and hom_add [simp] = ring_hom_add [OF homh]
    and hom_one [simp] = ring_hom_one [OF homh]

lemma (in ring_hom_cring) hom_zero [simp]:
  "h \<zero> = \<zero>\<^sub>2"
proof -
  have "h \<zero> \<oplus>\<^sub>2 h \<zero> = h \<zero> \<oplus>\<^sub>2 \<zero>\<^sub>2"
    by (simp add: hom_add [symmetric] del: hom_add)
  then show ?thesis by (simp del: S.r_zero)
qed

lemma (in ring_hom_cring) hom_a_inv [simp]:
  "x \<in> carrier R ==> h (\<ominus> x) = \<ominus>\<^sub>2 h x"
proof -
  assume R: "x \<in> carrier R"
  then have "h x \<oplus>\<^sub>2 h (\<ominus> x) = h x \<oplus>\<^sub>2 (\<ominus>\<^sub>2 h x)"
    by (simp add: hom_add [symmetric] R.r_neg S.r_neg del: hom_add)
  with R show ?thesis by simp
qed

lemma (in ring_hom_cring) hom_finsum [simp]:
  "[| finite A; f \<in> A -> carrier R |] ==>
  h (finsum R f A) = finsum S (h o f) A"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: Pi_def)
qed

lemma (in ring_hom_cring) hom_finprod:
  "[| finite A; f \<in> A -> carrier R |] ==>
  h (finprod R f A) = finprod S (h o f) A"
proof (induct set: Finites)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: Pi_def)
qed

declare ring_hom_cring.hom_finprod [simp]

lemma id_ring_hom [simp]:
  "id \<in> ring_hom R R"
  by (auto intro!: ring_hom_memI)

end
