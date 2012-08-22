(*  Title:      HOL/Algebra/Ring.thy
    Author:     Clemens Ballarin, started 9 December 1996
    Copyright:  Clemens Ballarin
*)

theory Ring
imports FiniteProduct
begin

section {* The Algebraic Hierarchy of Rings *}

subsection {* Abelian Groups *}

record 'a ring = "'a monoid" +
  zero :: 'a ("\<zero>\<index>")
  add :: "['a, 'a] => 'a" (infixl "\<oplus>\<index>" 65)

text {* Derived operations. *}

definition
  a_inv :: "[('a, 'm) ring_scheme, 'a ] => 'a" ("\<ominus>\<index> _" [81] 80)
  where "a_inv R = m_inv (| carrier = carrier R, mult = add R, one = zero R |)"

definition
  a_minus :: "[('a, 'm) ring_scheme, 'a, 'a] => 'a" (infixl "\<ominus>\<index>" 65)
  where "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<ominus>\<^bsub>R\<^esub> y = x \<oplus>\<^bsub>R\<^esub> (\<ominus>\<^bsub>R\<^esub> y)"

locale abelian_monoid =
  fixes G (structure)
  assumes a_comm_monoid:
     "comm_monoid (| carrier = carrier G, mult = add G, one = zero G |)"

definition
  finsum :: "[('b, 'm) ring_scheme, 'a => 'b, 'a set] => 'b" where
  "finsum G = finprod (| carrier = carrier G, mult = add G, one = zero G |)"

syntax
  "_finsum" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Oplus>__:_. _)" [1000, 0, 51, 10] 10)
syntax (xsymbols)
  "_finsum" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Oplus>__\<in>_. _)" [1000, 0, 51, 10] 10)
syntax (HTML output)
  "_finsum" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Oplus>__\<in>_. _)" [1000, 0, 51, 10] 10)
translations
  "\<Oplus>\<index>i:A. b" == "CONST finsum \<struct>\<index> (%i. b) A"
  -- {* Beware of argument permutation! *}


locale abelian_group = abelian_monoid +
  assumes a_comm_group:
     "comm_group (| carrier = carrier G, mult = add G, one = zero G |)"


subsection {* Basic Properties *}

lemma abelian_monoidI:
  fixes R (structure)
  assumes a_closed:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> x \<oplus> y \<in> carrier R"
    and zero_closed: "\<zero> \<in> carrier R"
    and a_assoc:
      "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |] ==>
      (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    and l_zero: "!!x. x \<in> carrier R ==> \<zero> \<oplus> x = x"
    and a_comm:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> x \<oplus> y = y \<oplus> x"
  shows "abelian_monoid R"
  by (auto intro!: abelian_monoid.intro comm_monoidI intro: assms)

lemma abelian_groupI:
  fixes R (structure)
  assumes a_closed:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> x \<oplus> y \<in> carrier R"
    and zero_closed: "zero R \<in> carrier R"
    and a_assoc:
      "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |] ==>
      (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    and a_comm:
      "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==> x \<oplus> y = y \<oplus> x"
    and l_zero: "!!x. x \<in> carrier R ==> \<zero> \<oplus> x = x"
    and l_inv_ex: "!!x. x \<in> carrier R ==> EX y : carrier R. y \<oplus> x = \<zero>"
  shows "abelian_group R"
  by (auto intro!: abelian_group.intro abelian_monoidI
      abelian_group_axioms.intro comm_monoidI comm_groupI
    intro: assms)

lemma (in abelian_monoid) a_monoid:
  "monoid (| carrier = carrier G, mult = add G, one = zero G |)"
by (rule comm_monoid.axioms, rule a_comm_monoid) 

lemma (in abelian_group) a_group:
  "group (| carrier = carrier G, mult = add G, one = zero G |)"
  by (simp add: group_def a_monoid)
    (simp add: comm_group.axioms group.axioms a_comm_group)

lemmas monoid_record_simps = partial_object.simps monoid.simps

text {* Transfer facts from multiplicative structures via interpretation. *}

sublocale abelian_monoid <
  add!: monoid "(| carrier = carrier G, mult = add G, one = zero G |)"
  where "carrier (| carrier = carrier G, mult = add G, one = zero G |) = carrier G"
    and "mult (| carrier = carrier G, mult = add G, one = zero G |) = add G"
    and "one (| carrier = carrier G, mult = add G, one = zero G |) = zero G"
  by (rule a_monoid) auto

context abelian_monoid begin

lemmas a_closed = add.m_closed 
lemmas zero_closed = add.one_closed
lemmas a_assoc = add.m_assoc
lemmas l_zero = add.l_one
lemmas r_zero = add.r_one
lemmas minus_unique = add.inv_unique

end

sublocale abelian_monoid <
  add!: comm_monoid "(| carrier = carrier G, mult = add G, one = zero G |)"
  where "carrier (| carrier = carrier G, mult = add G, one = zero G |) = carrier G"
    and "mult (| carrier = carrier G, mult = add G, one = zero G |) = add G"
    and "one (| carrier = carrier G, mult = add G, one = zero G |) = zero G"
    and "finprod (| carrier = carrier G, mult = add G, one = zero G |) = finsum G"
  by (rule a_comm_monoid) (auto simp: finsum_def)

context abelian_monoid begin

lemmas a_comm = add.m_comm
lemmas a_lcomm = add.m_lcomm
lemmas a_ac = a_assoc a_comm a_lcomm

lemmas finsum_empty = add.finprod_empty
lemmas finsum_insert = add.finprod_insert
lemmas finsum_zero = add.finprod_one
lemmas finsum_closed = add.finprod_closed
lemmas finsum_Un_Int = add.finprod_Un_Int
lemmas finsum_Un_disjoint = add.finprod_Un_disjoint
lemmas finsum_addf = add.finprod_multf
lemmas finsum_cong' = add.finprod_cong'
lemmas finsum_0 = add.finprod_0
lemmas finsum_Suc = add.finprod_Suc
lemmas finsum_Suc2 = add.finprod_Suc2
lemmas finsum_add = add.finprod_mult

lemmas finsum_cong = add.finprod_cong
text {*Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise @{text "g \<in> B -> carrier G"} cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful. *}

lemmas finsum_reindex = add.finprod_reindex

(* The following would be wrong.  Needed is the equivalent of (^) for addition,
  or indeed the canonical embedding from Nat into the monoid.

lemma finsum_const:
  assumes fin [simp]: "finite A"
      and a [simp]: "a : carrier G"
    shows "finsum G (%x. a) A = a (^) card A"
  using fin apply induct
  apply force
  apply (subst finsum_insert)
  apply auto
  apply (force simp add: Pi_def)
  apply (subst m_comm)
  apply auto
done
*)

lemmas finsum_singleton = add.finprod_singleton

end

sublocale abelian_group <
  add!: group "(| carrier = carrier G, mult = add G, one = zero G |)"
  where "carrier (| carrier = carrier G, mult = add G, one = zero G |) = carrier G"
    and "mult (| carrier = carrier G, mult = add G, one = zero G |) = add G"
    and "one (| carrier = carrier G, mult = add G, one = zero G |) = zero G"
    and "m_inv (| carrier = carrier G, mult = add G, one = zero G |) = a_inv G"
  by (rule a_group) (auto simp: m_inv_def a_inv_def)

context abelian_group begin

lemmas a_inv_closed = add.inv_closed

lemma minus_closed [intro, simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<ominus> y \<in> carrier G"
  by (simp add: a_minus_def)

lemmas a_l_cancel = add.l_cancel
lemmas a_r_cancel = add.r_cancel
lemmas l_neg = add.l_inv [simp del]
lemmas r_neg = add.r_inv [simp del]
lemmas minus_zero = add.inv_one
lemmas minus_minus = add.inv_inv
lemmas a_inv_inj = add.inv_inj
lemmas minus_equality = add.inv_equality

end

sublocale abelian_group <
  add!: comm_group "(| carrier = carrier G, mult = add G, one = zero G |)"
  where "carrier (| carrier = carrier G, mult = add G, one = zero G |) = carrier G"
    and "mult (| carrier = carrier G, mult = add G, one = zero G |) = add G"
    and "one (| carrier = carrier G, mult = add G, one = zero G |) = zero G"
    and "m_inv (| carrier = carrier G, mult = add G, one = zero G |) = a_inv G"
    and "finprod (| carrier = carrier G, mult = add G, one = zero G |) = finsum G"
  by (rule a_comm_group) (auto simp: m_inv_def a_inv_def finsum_def)

lemmas (in abelian_group) minus_add = add.inv_mult
 
text {* Derive an @{text "abelian_group"} from a @{text "comm_group"} *}

lemma comm_group_abelian_groupI:
  fixes G (structure)
  assumes cg: "comm_group \<lparr>carrier = carrier G, mult = add G, one = zero G\<rparr>"
  shows "abelian_group G"
proof -
  interpret comm_group "\<lparr>carrier = carrier G, mult = add G, one = zero G\<rparr>"
    by (rule cg)
  show "abelian_group G" ..
qed


subsection {* Rings: Basic Definitions *}

locale ring = abelian_group R + monoid R for R (structure) +
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


subsection {* Rings *}

lemma ringI:
  fixes R (structure)
  assumes abelian_group: "abelian_group R"
    and monoid: "monoid R"
    and l_distr: "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
    and r_distr: "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
  shows "ring R"
  by (auto intro: ring.intro
    abelian_group.axioms ring_axioms.intro assms)

context ring begin

lemma is_abelian_group: "abelian_group R" ..

lemma is_monoid: "monoid R"
  by (auto intro!: monoidI m_assoc)

lemma is_ring: "ring R"
  by (rule ring_axioms)

end

lemmas ring_record_simps = monoid_record_simps ring.simps

lemma cringI:
  fixes R (structure)
  assumes abelian_group: "abelian_group R"
    and comm_monoid: "comm_monoid R"
    and l_distr: "!!x y z. [| x \<in> carrier R; y \<in> carrier R; z \<in> carrier R |]
      ==> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
  shows "cring R"
proof (intro cring.intro ring.intro)
  show "ring_axioms R"
    -- {* Right-distributivity follows from left-distributivity and
          commutativity. *}
  proof (rule ring_axioms.intro)
    fix x y z
    assume R: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
    note [simp] = comm_monoid.axioms [OF comm_monoid]
      abelian_group.axioms [OF abelian_group]
      abelian_monoid.a_closed
        
    from R have "z \<otimes> (x \<oplus> y) = (x \<oplus> y) \<otimes> z"
      by (simp add: comm_monoid.m_comm [OF comm_monoid.intro])
    also from R have "... = x \<otimes> z \<oplus> y \<otimes> z" by (simp add: l_distr)
    also from R have "... = z \<otimes> x \<oplus> z \<otimes> y"
      by (simp add: comm_monoid.m_comm [OF comm_monoid.intro])
    finally show "z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y" .
  qed (rule l_distr)
qed (auto intro: cring.intro
  abelian_group.axioms comm_monoid.axioms ring_axioms.intro assms)

(*
lemma (in cring) is_comm_monoid:
  "comm_monoid R"
  by (auto intro!: comm_monoidI m_assoc m_comm)
*)

lemma (in cring) is_cring:
  "cring R" by (rule cring_axioms)


subsubsection {* Normaliser for Rings *}

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

context ring begin

text {* 
  The following proofs are from Jacobson, Basic Algebra I, pp.~88--89.
*}

lemma l_null [simp]:
  "x \<in> carrier R ==> \<zero> \<otimes> x = \<zero>"
proof -
  assume R: "x \<in> carrier R"
  then have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = (\<zero> \<oplus> \<zero>) \<otimes> x"
    by (simp add: l_distr del: l_zero r_zero)
  also from R have "... = \<zero> \<otimes> x \<oplus> \<zero>" by simp
  finally have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = \<zero> \<otimes> x \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma r_null [simp]:
  "x \<in> carrier R ==> x \<otimes> \<zero> = \<zero>"
proof -
  assume R: "x \<in> carrier R"
  then have "x \<otimes> \<zero> \<oplus> x \<otimes> \<zero> = x \<otimes> (\<zero> \<oplus> \<zero>)"
    by (simp add: r_distr del: l_zero r_zero)
  also from R have "... = x \<otimes> \<zero> \<oplus> \<zero>" by simp
  finally have "x \<otimes> \<zero> \<oplus> x \<otimes> \<zero> = x \<otimes> \<zero> \<oplus> \<zero>" .
  with R show ?thesis by (simp del: r_zero)
qed

lemma l_minus:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> \<ominus> x \<otimes> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = (\<ominus> x \<oplus> x) \<otimes> y" by (simp add: l_distr)
  also from R have "... = \<zero>" by (simp add: l_neg)
  finally have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = \<zero>" .
  with R have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg)
qed

lemma r_minus:
  "[| x \<in> carrier R; y \<in> carrier R |] ==> x \<otimes> \<ominus> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y = x \<otimes> (\<ominus> y \<oplus> y)" by (simp add: r_distr)
  also from R have "... = \<zero>" by (simp add: l_neg)
  finally have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y = \<zero>" .
  with R have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg )
qed

end

lemma (in abelian_group) minus_eq:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<ominus> y = x \<oplus> \<ominus> y"
  by (simp only: a_minus_def)

text {* Setup algebra method:
  compute distributive normal form in locale contexts *}

ML_file "ringsimp.ML"

setup Algebra.attrib_setup

method_setup algebra = {*
  Scan.succeed (SIMPLE_METHOD' o Algebra.algebra_tac)
*} "normalisation of algebraic structure"

lemmas (in ring) ring_simprules
  [algebra ring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr minus_eq
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm r_distr l_null r_null l_minus r_minus

lemmas (in cring)
  [algebra del: ring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  _

lemmas (in cring) cring_simprules
  [algebra add: cring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr m_comm minus_eq
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm m_lcomm r_distr l_null r_null l_minus r_minus

lemma (in cring) nat_pow_zero:
  "(n::nat) ~= 0 ==> \<zero> (^) n = \<zero>"
  by (induct n) simp_all

context ring begin

lemma one_zeroD:
  assumes onezero: "\<one> = \<zero>"
  shows "carrier R = {\<zero>}"
proof (rule, rule)
  fix x
  assume xcarr: "x \<in> carrier R"
  from xcarr have "x = x \<otimes> \<one>" by simp
  with onezero have "x = x \<otimes> \<zero>" by simp
  with xcarr have "x = \<zero>" by simp
  then show "x \<in> {\<zero>}" by fast
qed fast

lemma one_zeroI:
  assumes carrzero: "carrier R = {\<zero>}"
  shows "\<one> = \<zero>"
proof -
  from one_closed and carrzero
      show "\<one> = \<zero>" by simp
qed

lemma carrier_one_zero: "(carrier R = {\<zero>}) = (\<one> = \<zero>)"
  apply rule
   apply (erule one_zeroI)
  apply (erule one_zeroD)
  done

lemma carrier_one_not_zero: "(carrier R \<noteq> {\<zero>}) = (\<one> \<noteq> \<zero>)"
  by (simp add: carrier_one_zero)

end

text {* Two examples for use of method algebra *}

lemma
  fixes R (structure) and S (structure)
  assumes "ring R" "cring S"
  assumes RS: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier S" "d \<in> carrier S"
  shows "a \<oplus> \<ominus> (a \<oplus> \<ominus> b) = b & c \<otimes>\<^bsub>S\<^esub> d = d \<otimes>\<^bsub>S\<^esub> c"
proof -
  interpret ring R by fact
  interpret cring S by fact
  from RS show ?thesis by algebra
qed

lemma
  fixes R (structure)
  assumes "ring R"
  assumes R: "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<ominus> (a \<ominus> b) = b"
proof -
  interpret ring R by fact
  from R show ?thesis by algebra
qed


subsubsection {* Sums over Finite Sets *}

lemma (in ring) finsum_ldistr:
  "[| finite A; a \<in> carrier R; f \<in> A -> carrier R |] ==>
   finsum R f A \<otimes> a = finsum R (%i. f i \<otimes> a) A"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by (simp add: Pi_def l_distr)
qed

lemma (in ring) finsum_rdistr:
  "[| finite A; a \<in> carrier R; f \<in> A -> carrier R |] ==>
   a \<otimes> finsum R f A = finsum R (%i. a \<otimes> f i) A"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by (simp add: Pi_def r_distr)
qed


subsection {* Integral Domains *}

context "domain" begin

lemma zero_not_one [simp]:
  "\<zero> ~= \<one>"
  by (rule not_sym) simp

lemma integral_iff: (* not by default a simp rule! *)
  "[| a \<in> carrier R; b \<in> carrier R |] ==> (a \<otimes> b = \<zero>) = (a = \<zero> | b = \<zero>)"
proof
  assume "a \<in> carrier R" "b \<in> carrier R" "a \<otimes> b = \<zero>"
  then show "a = \<zero> | b = \<zero>" by (simp add: integral)
next
  assume "a \<in> carrier R" "b \<in> carrier R" "a = \<zero> | b = \<zero>"
  then show "a \<otimes> b = \<zero>" by auto
qed

lemma m_lcancel:
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

lemma m_rcancel:
  assumes prem: "a ~= \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows conc: "(b \<otimes> a = c \<otimes> a) = (b = c)"
proof -
  from prem and R have "(a \<otimes> b = a \<otimes> c) = (b = c)" by (rule m_lcancel)
  with R show ?thesis by algebra
qed

end


subsection {* Fields *}

text {* Field would not need to be derived from domain, the properties
  for domain follow from the assumptions of field *}
lemma (in cring) cring_fieldI:
  assumes field_Units: "Units R = carrier R - {\<zero>}"
  shows "field R"
proof
  from field_Units have "\<zero> \<notin> Units R" by fast
  moreover have "\<one> \<in> Units R" by fast
  ultimately show "\<one> \<noteq> \<zero>" by force
next
  fix a b
  assume acarr: "a \<in> carrier R"
    and bcarr: "b \<in> carrier R"
    and ab: "a \<otimes> b = \<zero>"
  show "a = \<zero> \<or> b = \<zero>"
  proof (cases "a = \<zero>", simp)
    assume "a \<noteq> \<zero>"
    with field_Units and acarr have aUnit: "a \<in> Units R" by fast
    from bcarr have "b = \<one> \<otimes> b" by algebra
    also from aUnit acarr have "... = (inv a \<otimes> a) \<otimes> b" by simp
    also from acarr bcarr aUnit[THEN Units_inv_closed]
    have "... = (inv a) \<otimes> (a \<otimes> b)" by algebra
    also from ab and acarr bcarr aUnit have "... = (inv a) \<otimes> \<zero>" by simp
    also from aUnit[THEN Units_inv_closed] have "... = \<zero>" by algebra
    finally have "b = \<zero>" .
    then show "a = \<zero> \<or> b = \<zero>" by simp
  qed
qed (rule field_Units)

text {* Another variant to show that something is a field *}
lemma (in cring) cring_fieldI2:
  assumes notzero: "\<zero> \<noteq> \<one>"
  and invex: "\<And>a. \<lbrakk>a \<in> carrier R; a \<noteq> \<zero>\<rbrakk> \<Longrightarrow> \<exists>b\<in>carrier R. a \<otimes> b = \<one>"
  shows "field R"
  apply (rule cring_fieldI, simp add: Units_def)
  apply (rule, clarsimp)
  apply (simp add: notzero)
proof (clarsimp)
  fix x
  assume xcarr: "x \<in> carrier R"
    and "x \<noteq> \<zero>"
  then have "\<exists>y\<in>carrier R. x \<otimes> y = \<one>" by (rule invex)
  then obtain y where ycarr: "y \<in> carrier R" and xy: "x \<otimes> y = \<one>" by fast
  from xy xcarr ycarr have "y \<otimes> x = \<one>" by (simp add: m_comm)
  with ycarr and xy show "\<exists>y\<in>carrier R. y \<otimes> x = \<one> \<and> x \<otimes> y = \<one>" by fast
qed


subsection {* Morphisms *}

definition
  ring_hom :: "[('a, 'm) ring_scheme, ('b, 'n) ring_scheme] => ('a => 'b) set"
  where "ring_hom R S =
    {h. h \<in> carrier R -> carrier S &
      (ALL x y. x \<in> carrier R & y \<in> carrier R -->
        h (x \<otimes>\<^bsub>R\<^esub> y) = h x \<otimes>\<^bsub>S\<^esub> h y & h (x \<oplus>\<^bsub>R\<^esub> y) = h x \<oplus>\<^bsub>S\<^esub> h y) &
      h \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub>}"

lemma ring_hom_memI:
  fixes R (structure) and S (structure)
  assumes hom_closed: "!!x. x \<in> carrier R ==> h x \<in> carrier S"
    and hom_mult: "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==>
      h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
    and hom_add: "!!x y. [| x \<in> carrier R; y \<in> carrier R |] ==>
      h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
    and hom_one: "h \<one> = \<one>\<^bsub>S\<^esub>"
  shows "h \<in> ring_hom R S"
  by (auto simp add: ring_hom_def assms Pi_def)

lemma ring_hom_closed:
  "[| h \<in> ring_hom R S; x \<in> carrier R |] ==> h x \<in> carrier S"
  by (auto simp add: ring_hom_def funcset_mem)

lemma ring_hom_mult:
  fixes R (structure) and S (structure)
  shows
    "[| h \<in> ring_hom R S; x \<in> carrier R; y \<in> carrier R |] ==>
    h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
    by (simp add: ring_hom_def)

lemma ring_hom_add:
  fixes R (structure) and S (structure)
  shows
    "[| h \<in> ring_hom R S; x \<in> carrier R; y \<in> carrier R |] ==>
    h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
    by (simp add: ring_hom_def)

lemma ring_hom_one:
  fixes R (structure) and S (structure)
  shows "h \<in> ring_hom R S ==> h \<one> = \<one>\<^bsub>S\<^esub>"
  by (simp add: ring_hom_def)

locale ring_hom_cring = R: cring R + S: cring S
    for R (structure) and S (structure) +
  fixes h
  assumes homh [simp, intro]: "h \<in> ring_hom R S"
  notes hom_closed [simp, intro] = ring_hom_closed [OF homh]
    and hom_mult [simp] = ring_hom_mult [OF homh]
    and hom_add [simp] = ring_hom_add [OF homh]
    and hom_one [simp] = ring_hom_one [OF homh]

lemma (in ring_hom_cring) hom_zero [simp]:
  "h \<zero> = \<zero>\<^bsub>S\<^esub>"
proof -
  have "h \<zero> \<oplus>\<^bsub>S\<^esub> h \<zero> = h \<zero> \<oplus>\<^bsub>S\<^esub> \<zero>\<^bsub>S\<^esub>"
    by (simp add: hom_add [symmetric] del: hom_add)
  then show ?thesis by (simp del: S.r_zero)
qed

lemma (in ring_hom_cring) hom_a_inv [simp]:
  "x \<in> carrier R ==> h (\<ominus> x) = \<ominus>\<^bsub>S\<^esub> h x"
proof -
  assume R: "x \<in> carrier R"
  then have "h x \<oplus>\<^bsub>S\<^esub> h (\<ominus> x) = h x \<oplus>\<^bsub>S\<^esub> (\<ominus>\<^bsub>S\<^esub> h x)"
    by (simp add: hom_add [symmetric] R.r_neg S.r_neg del: hom_add)
  with R show ?thesis by simp
qed

lemma (in ring_hom_cring) hom_finsum [simp]:
  "[| finite A; f \<in> A -> carrier R |] ==>
  h (finsum R f A) = finsum S (h o f) A"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: Pi_def)
qed

lemma (in ring_hom_cring) hom_finprod:
  "[| finite A; f \<in> A -> carrier R |] ==>
  h (finprod R f A) = finprod S (h o f) A"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: Pi_def)
qed

declare ring_hom_cring.hom_finprod [simp]

lemma id_ring_hom [simp]:
  "id \<in> ring_hom R R"
  by (auto intro!: ring_hom_memI)

end
