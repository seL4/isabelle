(*
  Title:  HOL/Algebra/Group.thy
  Id:     $Id$
  Author: Clemens Ballarin, started 4 February 2003

Based on work by Florian Kammueller, L C Paulson and Markus Wenzel.
*)

header {* Algebraic Structures up to Abelian Groups *}

theory Group = FuncSet + FoldSet:

text {*
  Definitions follow Jacobson, Basic Algebra I, Freeman, 1985; with
  the exception of \emph{magma} which, following Bourbaki, is a set
  together with a binary, closed operation.
*}

section {* From Magmas to Groups *}

subsection {* Definitions *}

record 'a semigroup =
  carrier :: "'a set"
  mult :: "['a, 'a] => 'a" (infixl "\<otimes>\<index>" 70)

record 'a monoid = "'a semigroup" +
  one :: 'a ("\<one>\<index>")

record 'a group = "'a monoid" +
  m_inv :: "'a => 'a" ("inv\<index> _" [81] 80)

locale magma = struct G +
  assumes m_closed [intro, simp]:
    "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"

locale semigroup = magma +
  assumes m_assoc:
    "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
     (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

locale l_one = struct G +
  assumes one_closed [intro, simp]: "\<one> \<in> carrier G"
    and l_one [simp]: "x \<in> carrier G ==> \<one> \<otimes> x = x"

locale group = semigroup + l_one +
  assumes inv_closed [intro, simp]: "x \<in> carrier G ==> inv x \<in> carrier G"
    and l_inv: "x \<in> carrier G ==> inv x \<otimes> x = \<one>"

subsection {* Cancellation Laws and Basic Properties *}

lemma (in group) l_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<otimes> y = x \<otimes> z) = (y = z)"
proof
  assume eq: "x \<otimes> y = x \<otimes> z"
    and G: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
  then have "(inv x \<otimes> x) \<otimes> y = (inv x \<otimes> x) \<otimes> z" by (simp add: m_assoc)
  with G show "y = z" by (simp add: l_inv)
next
  assume eq: "y = z"
    and G: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
  then show "x \<otimes> y = x \<otimes> z" by simp
qed

lemma (in group) r_one [simp]:  
  "x \<in> carrier G ==> x \<otimes> \<one> = x"
proof -
  assume x: "x \<in> carrier G"
  then have "inv x \<otimes> (x \<otimes> \<one>) = inv x \<otimes> x"
    by (simp add: m_assoc [symmetric] l_inv)
  with x show ?thesis by simp 
qed

lemma (in group) r_inv:
  "x \<in> carrier G ==> x \<otimes> inv x = \<one>"
proof -
  assume x: "x \<in> carrier G"
  then have "inv x \<otimes> (x \<otimes> inv x) = inv x \<otimes> \<one>"
    by (simp add: m_assoc [symmetric] l_inv)
  with x show ?thesis by (simp del: r_one)
qed

lemma (in group) r_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (y \<otimes> x = z \<otimes> x) = (y = z)"
proof
  assume eq: "y \<otimes> x = z \<otimes> x"
    and G: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
  then have "y \<otimes> (x \<otimes> inv x) = z \<otimes> (x \<otimes> inv x)"
    by (simp add: m_assoc [symmetric])
  with G show "y = z" by (simp add: r_inv)
next
  assume eq: "y = z"
    and G: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
  then show "y \<otimes> x = z \<otimes> x" by simp
qed

lemma (in group) inv_inv [simp]:
  "x \<in> carrier G ==> inv (inv x) = x"
proof -
  assume x: "x \<in> carrier G"
  then have "inv x \<otimes> inv (inv x) = inv x \<otimes> x" by (simp add: l_inv r_inv)
  with x show ?thesis by simp
qed

lemma (in group) inv_mult:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv y \<otimes> inv x"
proof -
  assume G: "x \<in> carrier G" "y \<in> carrier G"
  then have "inv (x \<otimes> y) \<otimes> (x \<otimes> y) = (inv y \<otimes> inv x) \<otimes> (x \<otimes> y)"
    by (simp add: m_assoc l_inv) (simp add: m_assoc [symmetric] l_inv)
  with G show ?thesis by simp
qed

subsection {* Substructures *}

locale submagma = var H + struct G +
  assumes subset [intro, simp]: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "[| x \<in> H; y \<in> H |] ==> x \<otimes> y \<in> H"

declare (in submagma) magma.intro [intro] semigroup.intro [intro]

(*
alternative definition of submagma

locale submagma = var H + struct G +
  assumes subset [intro, simp]: "carrier H \<subseteq> carrier G"
    and m_equal [simp]: "mult H = mult G"
    and m_closed [intro, simp]:
      "[| x \<in> carrier H; y \<in> carrier H |] ==> x \<otimes> y \<in> carrier H"
*)

lemma submagma_imp_subset:
  "submagma H G ==> H \<subseteq> carrier G"
  by (rule submagma.subset)

lemma (in submagma) subsetD [dest, simp]:
  "x \<in> H ==> x \<in> carrier G"
  using subset by blast

lemma (in submagma) magmaI [intro]:
  includes magma G
  shows "magma (G(| carrier := H |))"
  by rule simp

lemma (in submagma) semigroup_axiomsI [intro]:
  includes semigroup G
  shows "semigroup_axioms (G(| carrier := H |))"
    by rule (simp add: m_assoc)

lemma (in submagma) semigroupI [intro]:
  includes semigroup G
  shows "semigroup (G(| carrier := H |))"
  using prems by fast

locale subgroup = submagma H G +
  assumes one_closed [intro, simp]: "\<one> \<in> H"
    and m_inv_closed [intro, simp]: "x \<in> H ==> inv x \<in> H"

declare (in subgroup) group.intro [intro]

lemma (in subgroup) l_oneI [intro]:
  includes l_one G
  shows "l_one (G(| carrier := H |))"
  by rule simp_all

lemma (in subgroup) group_axiomsI [intro]:
  includes group G
  shows "group_axioms (G(| carrier := H |))"
  by rule (simp_all add: l_inv)

lemma (in subgroup) groupI [intro]:
  includes group G
  shows "group (G(| carrier := H |))"
  using prems by fast

text {*
  Since @{term H} is nonempty, it contains some element @{term x}.  Since
  it is closed under inverse, it contains @{text "inv x"}.  Since
  it is closed under product, it contains @{text "x \<otimes> inv x = \<one>"}.
*}

lemma (in group) one_in_subset:
  "[| H \<subseteq> carrier G; H \<noteq> {}; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<otimes> b \<in> H |]
   ==> \<one> \<in> H"
by (force simp add: l_inv)

text {* A characterization of subgroups: closed, non-empty subset. *}

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier G" and non_empty: "H \<noteq> {}"
    and inv: "!!a. a \<in> H ==> inv a \<in> H"
    and mult: "!!a b. [|a \<in> H; b \<in> H|] ==> a \<otimes> b \<in> H"
  shows "subgroup H G"
proof
  from subset and mult show "submagma H G" ..
next
  have "\<one> \<in> H" by (rule one_in_subset) (auto simp only: prems)
  with inv show "subgroup_axioms H G"
    by (intro subgroup_axioms.intro) simp_all
qed

text {*
  Repeat facts of submagmas for subgroups.  Necessary???
*}

lemma (in subgroup) subset:
  "H \<subseteq> carrier G"
  ..

lemma (in subgroup) m_closed:
  "[| x \<in> H; y \<in> H |] ==> x \<otimes> y \<in> H"
  ..

declare magma.m_closed [simp]

declare l_one.one_closed [iff] group.inv_closed [simp]
  l_one.l_one [simp] group.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "~ subgroup {} G"
  by (blast dest: subgroup.one_closed)

lemma (in subgroup) finite_imp_card_positive:
  "finite (carrier G) ==> 0 < card H"
proof (rule classical)
  have sub: "subgroup H G" using prems ..
  assume fin: "finite (carrier G)"
    and zero: "~ 0 < card H"
  then have "finite H" by (blast intro: finite_subset dest: subset)
  with zero sub have "subgroup {} G" by simp
  with subgroup_nonempty show ?thesis by contradiction
qed

subsection {* Direct Products *}

constdefs
  DirProdSemigroup ::
    "[('a, 'c) semigroup_scheme, ('b, 'd) semigroup_scheme]
    => ('a \<times> 'b) semigroup"
    (infixr "\<times>\<^sub>s" 80)
  "G \<times>\<^sub>s H == (| carrier = carrier G \<times> carrier H,
    mult = (%(xg, xh) (yg, yh). (mult G xg yg, mult H xh yh)) |)"

  DirProdMonoid ::
    "[('a, 'c) monoid_scheme, ('b, 'd) monoid_scheme] => ('a \<times> 'b) monoid"
    (infixr "\<times>\<^sub>m" 80)
  "G \<times>\<^sub>m H == (| carrier = carrier (G \<times>\<^sub>s H),
    mult = mult (G \<times>\<^sub>s H),
    one = (one G, one H) |)"

  DirProdGroup ::
    "[('a, 'c) group_scheme, ('b, 'd) group_scheme] => ('a \<times> 'b) group"
    (infixr "\<times>\<^sub>g" 80)
  "G \<times>\<^sub>g H == (| carrier = carrier (G \<times>\<^sub>m H),
    mult = mult (G \<times>\<^sub>m H),
    one = one (G \<times>\<^sub>m H),
    m_inv = (%(g, h). (m_inv G g, m_inv H h)) |)"

lemma DirProdSemigroup_magma:
  includes magma G + magma H
  shows "magma (G \<times>\<^sub>s H)"
  by rule (auto simp add: DirProdSemigroup_def)

lemma DirProdSemigroup_semigroup_axioms:
  includes semigroup G + semigroup H
  shows "semigroup_axioms (G \<times>\<^sub>s H)"
  by rule (auto simp add: DirProdSemigroup_def G.m_assoc H.m_assoc)

lemma DirProdSemigroup_semigroup:
  includes semigroup G + semigroup H
  shows "semigroup (G \<times>\<^sub>s H)"
  using prems
  by (fast intro: semigroup.intro
    DirProdSemigroup_magma DirProdSemigroup_semigroup_axioms)

lemma DirProdGroup_magma:
  includes magma G + magma H
  shows "magma (G \<times>\<^sub>g H)"
  by rule
    (auto simp add: DirProdGroup_def DirProdMonoid_def DirProdSemigroup_def)

lemma DirProdGroup_semigroup_axioms:
  includes semigroup G + semigroup H
  shows "semigroup_axioms (G \<times>\<^sub>g H)"
  by rule
    (auto simp add: DirProdGroup_def DirProdMonoid_def DirProdSemigroup_def
      G.m_assoc H.m_assoc)

lemma DirProdGroup_semigroup:
  includes semigroup G + semigroup H
  shows "semigroup (G \<times>\<^sub>g H)"
  using prems
  by (fast intro: semigroup.intro
    DirProdGroup_magma DirProdGroup_semigroup_axioms)

(* ... and further lemmas for group ... *)

lemma DirProdGroup_group:
  includes group G + group H
  shows "group (G \<times>\<^sub>g H)"
by rule
  (auto intro: magma.intro l_one.intro
      semigroup_axioms.intro group_axioms.intro
    simp add: DirProdGroup_def DirProdMonoid_def DirProdSemigroup_def
      G.m_assoc H.m_assoc G.l_inv H.l_inv)

subsection {* Homomorphisms *}

constdefs
  hom :: "[('a, 'c) semigroup_scheme, ('b, 'd) semigroup_scheme]
    => ('a => 'b)set"
  "hom G H ==
    {h. h \<in> carrier G -> carrier H &
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (mult G x y) = mult H (h x) (h y))}"

lemma (in semigroup) hom:
  includes semigroup G
  shows "semigroup (| carrier = hom G G, mult = op o |)"
proof
  show "magma (| carrier = hom G G, mult = op o |)"
    by rule (simp add: Pi_def hom_def)
next
  show "semigroup_axioms (| carrier = hom G G, mult = op o |)"
    by rule (simp add: o_assoc)
qed

lemma hom_mult:
  "[| h \<in> hom G H; x \<in> carrier G; y \<in> carrier G |] 
   ==> h (mult G x y) = mult H (h x) (h y)"
  by (simp add: hom_def) 

lemma hom_closed:
  "[| h \<in> hom G H; x \<in> carrier G |] ==> h x \<in> carrier H"
  by (auto simp add: hom_def funcset_mem)

locale group_hom = group G + group H + var h +
  assumes homh: "h \<in> hom G H"
  notes hom_mult [simp] = hom_mult [OF homh]
    and hom_closed [simp] = hom_closed [OF homh]

lemma (in group_hom) one_closed [simp]:
  "h \<one> \<in> carrier H"
  by simp

lemma (in group_hom) hom_one [simp]:
  "h \<one> = \<one>\<^sub>2"
proof -
  have "h \<one> \<otimes>\<^sub>2 \<one>\<^sub>2 = h \<one> \<otimes>\<^sub>2 h \<one>"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis by (simp del: r_one)
qed

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier G ==> h (inv x) \<in> carrier H"
  by simp

lemma (in group_hom) hom_inv [simp]:
  "x \<in> carrier G ==> h (inv x) = inv\<^sub>2 (h x)"
proof -
  assume x: "x \<in> carrier G"
  then have "h x \<otimes>\<^sub>2 h (inv x) = \<one>\<^sub>2"
    by (simp add: hom_mult [symmetric] G.r_inv del: hom_mult)
  also from x have "... = h x \<otimes>\<^sub>2 inv\<^sub>2 (h x)"
    by (simp add: hom_mult [symmetric] H.r_inv del: hom_mult)
  finally have "h x \<otimes>\<^sub>2 h (inv x) = h x \<otimes>\<^sub>2 inv\<^sub>2 (h x)" .
  with x show ?thesis by simp
qed

section {* Abelian Structures *}

subsection {* Definition *}

locale abelian_semigroup = semigroup +
  assumes m_comm: "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"

lemma (in abelian_semigroup) m_lcomm:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   x \<otimes> (y \<otimes> z) = y \<otimes> (x \<otimes> z)"
proof -
  assume xyz: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
  from xyz have "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z" by (simp add: m_assoc)
  also from xyz have "... = (y \<otimes> x) \<otimes> z" by (simp add: m_comm)
  also from xyz have "... = y \<otimes> (x \<otimes> z)" by (simp add: m_assoc)
  finally show ?thesis .
qed

lemmas (in abelian_semigroup) ac = m_assoc m_comm m_lcomm

locale abelian_monoid = abelian_semigroup + l_one

lemma (in abelian_monoid) l_one [simp]:
  "x \<in> carrier G ==> x \<otimes> \<one> = x"
proof -
  assume G: "x \<in> carrier G"
  then have "x \<otimes> \<one> = \<one> \<otimes> x" by (simp add: m_comm)
  also from G have "... = x" by simp
  finally show ?thesis .
qed

locale abelian_group = abelian_monoid + group

subsection {* Products over Finite Sets *}

locale finite_prod = abelian_monoid + var prod +
  defines "prod == (%f A. if finite A
      then foldD (carrier G) (op \<otimes> o f) \<one> A
      else arbitrary)"

(* TODO: nice syntax for the summation operator inside the locale
   like \<Otimes>\<index> i\<in>A. f i, probably needs hand-coded translation *)

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_full_simp_tac; thy)) *}

lemma (in finite_prod) prod_empty [simp]: 
  "prod f {} = \<one>"
  by (simp add: prod_def)

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_simp_tac; thy)) *}

declare funcsetI [intro]
  funcset_mem [dest]

lemma (in finite_prod) prod_insert [simp]:
  "[| finite F; a \<notin> F; f \<in> F -> carrier G; f a \<in> carrier G |] ==>
   prod f (insert a F) = f a \<otimes> prod f F"
  apply (rule trans)
  apply (simp add: prod_def)
  apply (rule trans)
  apply (rule LCD.foldD_insert [OF LCD.intro [of "insert a F"]])
    apply simp
    apply (rule m_lcomm)
      apply fast apply fast apply assumption
    apply (fastsimp intro: m_closed)
    apply simp+ apply fast
  apply (auto simp add: prod_def)
  done

lemma (in finite_prod) prod_one:
  "finite A ==> prod (%i. \<one>) A = \<one>"
proof (induct set: Finites)
  case empty show ?case by simp
next
  case (insert A a)
  have "(%i. \<one>) \<in> A -> carrier G" by auto
  with insert show ?case by simp
qed

(*
lemma prod_eq_0_iff [simp]:
    "finite F ==> (prod f F = 0) = (ALL a:F. f a = (0::nat))"
  by (induct set: Finites) auto

lemma prod_SucD: "prod f A = Suc n ==> EX a:A. 0 < f a"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: prod_def)
  apply (erule rev_mp)
  apply (erule finite_induct)
   apply auto
  done

lemma card_eq_prod: "finite A ==> card A = prod (\<lambda>x. 1) A"
*)  -- {* Could allow many @{text "card"} proofs to be simplified. *}
(*
  by (induct set: Finites) auto
*)

lemma (in finite_prod) prod_closed:
  fixes A
  assumes fin: "finite A" and f: "f \<in> A -> carrier G" 
  shows "prod f A \<in> carrier G"
using fin f
proof induct
  case empty show ?case by simp
next
  case (insert A a)
  then have a: "f a \<in> carrier G" by fast
  from insert have A: "f \<in> A -> carrier G" by fast
  from insert A a show ?case by simp
qed

lemma funcset_Int_left [simp, intro]:
  "[| f \<in> A -> C; f \<in> B -> C |] ==> f \<in> A Int B -> C"
  by fast

lemma funcset_Un_left [iff]:
  "(f \<in> A Un B -> C) = (f \<in> A -> C & f \<in> B -> C)"
  by fast

lemma (in finite_prod) prod_Un_Int:
  "[| finite A; finite B; g \<in> A -> carrier G; g \<in> B -> carrier G |] ==>
   prod g (A Un B) \<otimes> prod g (A Int B) = prod g A \<otimes> prod g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
proof (induct set: Finites)
  case empty then show ?case by (simp add: prod_closed)
next
  case (insert A a)
  then have a: "g a \<in> carrier G" by fast
  from insert have A: "g \<in> A -> carrier G" by fast
  from insert A a show ?case
    by (simp add: ac Int_insert_left insert_absorb prod_closed
          Int_mono2 Un_subset_iff) 
qed

lemma (in finite_prod) prod_Un_disjoint:
  "[| finite A; finite B; A Int B = {};
      g \<in> A -> carrier G; g \<in> B -> carrier G |]
   ==> prod g (A Un B) = prod g A \<otimes> prod g B"
  apply (subst prod_Un_Int [symmetric])
    apply (auto simp add: prod_closed)
  done

(*
lemma prod_UN_disjoint:
  fixes f :: "'a => 'b::plus_ac0"
  shows
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      prod f (UNION I A) = prod (\<lambda>i. prod f (A i)) I"
  apply (induct set: Finites)
   apply simp
  apply atomize
  apply (subgoal_tac "ALL i:F. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x Int UNION F A = {}")
   prefer 2 apply blast
  apply (simp add: prod_Un_disjoint)
  done
*)

lemma (in finite_prod) prod_addf:
  "[| finite A; f \<in> A -> carrier G; g \<in> A -> carrier G |] ==>
   prod (%x. f x \<otimes> g x) A = (prod f A \<otimes> prod g A)"
proof (induct set: Finites)
  case empty show ?case by simp
next
  case (insert A a) then
  have fA: "f : A -> carrier G" by fast
  from insert have fa: "f a : carrier G" by fast
  from insert have gA: "g : A -> carrier G" by fast
  from insert have ga: "g a : carrier G" by fast
  from insert have fga: "(%x. f x \<otimes> g x) a : carrier G" by (simp add: Pi_def)
  from insert have fgA: "(%x. f x \<otimes> g x) : A -> carrier G"
    by (simp add: Pi_def)
  show ?case  (* check if all simps are really necessary *)
    by (simp add: insert fA fa gA ga fgA fga ac prod_closed Int_insert_left insert_absorb Int_mono2 Un_subset_iff)
qed

(*
lemma prod_Un: "finite A ==> finite B ==>
    (prod f (A Un B) :: nat) = prod f A + prod f B - prod f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
  apply (subst prod_Un_Int [symmetric])
    apply auto
  done

lemma prod_diff1: "(prod f (A - {a}) :: nat) =
    (if a:A then prod f A - f a else prod f A)"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: prod_def)
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (drule_tac a = a in mk_disjoint_insert)
  apply auto
  done
*)

lemma (in finite_prod) prod_cong:
  "[| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> prod f A = prod g B"
proof -
  assume prems: "A = B" "g : B -> carrier G"
    "!!i. i : B ==> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. [| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> prod f A = prod g B"
    proof induct
      case empty thus ?case by simp
    next
      case (insert B x)
      then have "prod f A = prod f (insert x B)" by simp
      also from insert have "... = f x \<otimes> prod f B"
      proof (intro prod_insert)
	show "finite B" .
      next
	show "x ~: B" .
      next
	assume "x ~: B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
	  "g \<in> insert x B \<rightarrow> carrier G"
	thus "f : B -> carrier G" by fastsimp
      next
	assume "x ~: B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
	  "g \<in> insert x B \<rightarrow> carrier G"
	thus "f x \<in> carrier G" by fastsimp
      qed
      also from insert have "... = g x \<otimes> prod g B" by fastsimp
      also from insert have "... = prod g (insert x B)"
      by (intro prod_insert [THEN sym]) auto
      finally show ?case .
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by (simp add: prod_def)
  qed
qed

lemma (in finite_prod) prod_cong1 [cong]:
  "[| A = B; !!i. i : B ==> f i = g i;
      g : B -> carrier G = True |] ==> prod f A = prod g B"
  by (rule prod_cong) fast+

text {*Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise @{text "g : B -> carrier G"} cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful. *}

declare funcsetI [rule del]
  funcset_mem [rule del]

subsection {* Summation over the integer interval @{term "{..n}"} *}

text {*
  For technical reasons (locales) a new locale where the index set is
  restricted to @{term "nat"} is necessary.
*}

locale finite_prod_nat = finite_prod +
  assumes "False ==> prod f (A::nat set) = prod f A"

lemma (in finite_prod_nat) natSum_0 [simp]:
  "f : {0::nat} -> carrier G ==> prod f {..0} = f 0"
by (simp add: Pi_def)

lemma (in finite_prod_nat) natsum_Suc [simp]:
  "f : {..Suc n} -> carrier G ==>
   prod f {..Suc n} = (f (Suc n) \<otimes> prod f {..n})"
by (simp add: Pi_def atMost_Suc)

lemma (in finite_prod_nat) natsum_Suc2:
  "f : {..Suc n} -> carrier G ==>
   prod f {..Suc n} = (prod (%i. f (Suc i)) {..n} \<otimes> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case by (simp add: m_assoc Pi_def prod_closed)
qed

lemma (in finite_prod_nat) natsum_zero [simp]:
  "prod (%i. \<one>) {..n::nat} = \<one>"
by (induct n) (simp_all add: Pi_def)

lemma (in finite_prod_nat) natsum_add [simp]:
  "[| f : {..n} -> carrier G; g : {..n} -> carrier G |] ==>
   prod (%i. f i \<otimes> g i) {..n::nat} = prod f {..n} \<otimes> prod g {..n}"
by (induct n) (simp_all add: ac Pi_def prod_closed)

thm setsum_cong

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_full_simp_tac; thy)) *}

lemma "(\<Sum>i\<in>{..10::nat}. if i<=10 then 0 else 1) = (0::nat)"
apply simp done

lemma (in finite_prod_nat) "prod (%i. if i<=10 then \<one> else x) {..10} = \<one>"
apply (simp add: Pi_def)

end
