(*  Title:      Summation Operator for Abelian Groups
    ID:         $Id$
    Author:     Clemens Ballarin, started 19 November 2002

This file is largely based on HOL/Finite_Set.thy.
*)

header {* Summation Operator *}

theory Summation = Group:

(* Instantiation of LC from Finite_Set.thy is not possible,
   because here we have explicit typing rules like x : carrier G.
   We introduce an explicit argument for the domain D *)

consts
  foldSetD :: "['a set, 'b => 'a => 'a, 'a] => ('b set * 'a) set"

inductive "foldSetD D f e"
  intros
    emptyI [intro]: "e : D ==> ({}, e) : foldSetD D f e"
    insertI [intro]: "[| x ~: A; f x y : D; (A, y) : foldSetD D f e |] ==>
                      (insert x A, f x y) : foldSetD D f e"

inductive_cases empty_foldSetDE [elim!]: "({}, x) : foldSetD D f e"

constdefs
  foldD :: "['a set, 'b => 'a => 'a, 'a, 'b set] => 'a"
  "foldD D f e A == THE x. (A, x) : foldSetD D f e"

lemma foldSetD_closed:
  "[| (A, z) : foldSetD D f e ; e : D; !!x y. [| x : A; y : D |] ==> f x y : D 
      |] ==> z : D";
  by (erule foldSetD.elims) auto

lemma Diff1_foldSetD:
  "[| (A - {x}, y) : foldSetD D f e; x : A; f x y : D |] ==>
   (A, f x y) : foldSetD D f e"
  apply (erule insert_Diff [THEN subst], rule foldSetD.intros)
   apply auto
  done

lemma foldSetD_imp_finite [simp]: "(A, x) : foldSetD D f e ==> finite A"
  by (induct set: foldSetD) auto

lemma finite_imp_foldSetD:
  "[| finite A; e : D; !!x y. [| x : A; y : D |] ==> f x y : D |] ==>
   EX x. (A, x) : foldSetD D f e"
proof (induct set: Finites)
  case empty then show ?case by auto
next
  case (insert F x)
  then obtain y where y: "(F, y) : foldSetD D f e" by auto
  with insert have "y : D" by (auto dest: foldSetD_closed)
  with y and insert have "(insert x F, f x y) : foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed

subsection {* Left-commutative operations *}

locale LCD =
  fixes B :: "'b set"
  and D :: "'a set"
  and f :: "'b => 'a => 'a"    (infixl "\<cdot>" 70)
  assumes left_commute: "[| x : B; y : B; z : D |] ==> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  and f_closed [simp, intro!]: "!!x y. [| x : B; y : D |] ==> f x y : D"

lemma (in LCD) foldSetD_closed [dest]:
  "(A, z) : foldSetD D f e ==> z : D";
  by (erule foldSetD.elims) auto

lemma (in LCD) Diff1_foldSetD:
  "[| (A - {x}, y) : foldSetD D f e; x : A; A <= B |] ==>
   (A, f x y) : foldSetD D f e"
  apply (subgoal_tac "x : B")
  prefer 2 apply fast
  apply (erule insert_Diff [THEN subst], rule foldSetD.intros)
   apply auto
  done

lemma (in LCD) foldSetD_imp_finite [simp]:
  "(A, x) : foldSetD D f e ==> finite A"
  by (induct set: foldSetD) auto

lemma (in LCD) finite_imp_foldSetD:
  "[| finite A; A <= B; e : D |] ==> EX x. (A, x) : foldSetD D f e"
proof (induct set: Finites)
  case empty then show ?case by auto
next
  case (insert F x)
  then obtain y where y: "(F, y) : foldSetD D f e" by auto
  with insert have "y : D" by auto
  with y and insert have "(insert x F, f x y) : foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed

lemma (in LCD) foldSetD_determ_aux:
  "e : D ==> ALL A x. A <= B & card A < n --> (A, x) : foldSetD D f e -->
    (ALL y. (A, y) : foldSetD D f e --> y = x)"
  apply (induct n)
   apply (auto simp add: less_Suc_eq)
  apply (erule foldSetD.cases)
   apply blast
  apply (erule foldSetD.cases)
   apply blast
  apply clarify
  txt {* force simplification of @{text "card A < card (insert ...)"}. *}
  apply (erule rev_mp)
  apply (simp add: less_Suc_eq_le)
  apply (rule impI)
  apply (rename_tac Aa xa ya Ab xb yb, case_tac "xa = xb")
   apply (subgoal_tac "Aa = Ab")
    prefer 2 apply (blast elim!: equalityE)
   apply blast
  txt {* case @{prop "xa \<notin> xb"}. *}
  apply (subgoal_tac "Aa - {xb} = Ab - {xa} & xb : Aa & xa : Ab")
   prefer 2 apply (blast elim!: equalityE)
  apply clarify
  apply (subgoal_tac "Aa = insert xb Ab - {xa}")
   prefer 2 apply blast
  apply (subgoal_tac "card Aa <= card Ab")
   prefer 2
   apply (rule Suc_le_mono [THEN subst])
   apply (simp add: card_Suc_Diff1)
  apply (rule_tac A1 = "Aa - {xb}" in finite_imp_foldSetD [THEN exE])
  apply (blast intro: foldSetD_imp_finite finite_Diff)
(* new subgoal from finite_imp_foldSetD *)
    apply best (* blast doesn't seem to solve this *)
   apply assumption
  apply (frule (1) Diff1_foldSetD)
(* new subgoal from Diff1_foldSetD *)
    apply best
(*
apply (best del: foldSetD_closed elim: foldSetD_closed)
    apply (rule f_closed) apply assumption apply (rule foldSetD_closed)
    prefer 3 apply assumption apply (rule e_closed)
    apply (rule f_closed) apply force apply assumption
*)
  apply (subgoal_tac "ya = f xb x")
   prefer 2
(* new subgoal to make IH applicable *) 
  apply (subgoal_tac "Aa <= B")
   prefer 2 apply best
   apply (blast del: equalityCE)
  apply (subgoal_tac "(Ab - {xa}, x) : foldSetD D f e")
   prefer 2 apply simp
  apply (subgoal_tac "yb = f xa x")
   prefer 2 
(*   apply (drule_tac x = xa in Diff1_foldSetD)
     apply assumption
     apply (rule f_closed) apply best apply (rule foldSetD_closed)
     prefer 3 apply assumption apply (rule e_closed)
     apply (rule f_closed) apply best apply assumption
*)
   apply (blast del: equalityCE dest: Diff1_foldSetD)
   apply (simp (no_asm_simp))
   apply (rule left_commute)
   apply assumption apply best apply best
 done

lemma (in LCD) foldSetD_determ:
  "[| (A, x) : foldSetD D f e; (A, y) : foldSetD D f e; e : D; A <= B |]
   ==> y = x"
  by (blast intro: foldSetD_determ_aux [rule_format])

lemma (in LCD) foldD_equality:
  "[| (A, y) : foldSetD D f e; e : D; A <= B |] ==> foldD D f e A = y"
  by (unfold foldD_def) (blast intro: foldSetD_determ)

lemma foldD_empty [simp]:
  "e : D ==> foldD D f e {} = e"
  by (unfold foldD_def) blast

lemma (in LCD) foldD_insert_aux:
  "[| x ~: A; x : B; e : D; A <= B |] ==>
    ((insert x A, v) : foldSetD D f e) =
    (EX y. (A, y) : foldSetD D f e & v = f x y)"
  apply auto
  apply (rule_tac A1 = A in finite_imp_foldSetD [THEN exE])
   apply (fastsimp dest: foldSetD_imp_finite)
(* new subgoal by finite_imp_foldSetD *)
    apply assumption
    apply assumption
  apply (blast intro: foldSetD_determ)
  done

lemma (in LCD) foldD_insert:
    "[| finite A; x ~: A; x : B; e : D; A <= B |] ==>
     foldD D f e (insert x A) = f x (foldD D f e A)"
  apply (unfold foldD_def)
  apply (simp add: foldD_insert_aux)
  apply (rule the_equality)
  apply (auto intro: finite_imp_foldSetD
    cong add: conj_cong simp add: foldD_def [symmetric] foldD_equality)
  done

lemma (in LCD) foldD_closed [simp]:
  "[| finite A; e : D; A <= B |] ==> foldD D f e A : D"
proof (induct set: Finites)
  case empty then show ?case by (simp add: foldD_empty)
next
  case insert then show ?case by (simp add: foldD_insert)
qed

lemma (in LCD) foldD_commute:
  "[| finite A; x : B; e : D; A <= B |] ==>
   f x (foldD D f e A) = foldD D f (f x e) A"
  apply (induct set: Finites)
   apply simp
  apply (auto simp add: left_commute foldD_insert)
  done

lemma Int_mono2:
  "[| A <= C; B <= C |] ==> A Int B <= C"
  by blast

lemma (in LCD) foldD_nest_Un_Int:
  "[| finite A; finite C; e : D; A <= B; C <= B |] ==>
   foldD D f (foldD D f e C) A = foldD D f (foldD D f e (A Int C)) (A Un C)"
  apply (induct set: Finites)
   apply simp
  apply (simp add: foldD_insert foldD_commute Int_insert_left insert_absorb
    Int_mono2 Un_subset_iff)
  done

lemma (in LCD) foldD_nest_Un_disjoint:
  "[| finite A; finite B; A Int B = {}; e : D; A <= B; C <= B |]
    ==> foldD D f e (A Un B) = foldD D f (foldD D f e B) A"
  by (simp add: foldD_nest_Un_Int)

-- {* Delete rules to do with @{text foldSetD} relation. *}

declare foldSetD_imp_finite [simp del]
  empty_foldSetDE [rule del]
  foldSetD.intros [rule del]
declare (in LCD)
  foldSetD_closed [rule del]

subsection {* Commutative monoids *}

text {*
  We enter a more restrictive context, with @{text "f :: 'a => 'a => 'a"}
  instead of @{text "'b => 'a => 'a"}.
*}

locale ACeD =
  fixes D :: "'a set"
    and f :: "'a => 'a => 'a"    (infixl "\<cdot>" 70)
    and e :: 'a
  assumes ident [simp]: "x : D ==> x \<cdot> e = x"
    and commute: "[| x : D; y : D |] ==> x \<cdot> y = y \<cdot> x"
    and assoc: "[| x : D; y : D; z : D |] ==> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and e_closed [simp]: "e : D"
    and f_closed [simp]: "[| x : D; y : D |] ==> x \<cdot> y : D"

lemma (in ACeD) left_commute:
  "[| x : D; y : D; z : D |] ==> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  assume D: "x : D" "y : D" "z : D"
  then have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp add: commute)
  also from D have "... = y \<cdot> (z \<cdot> x)" by (simp add: assoc)
  also from D have "z \<cdot> x = x \<cdot> z" by (simp add: commute)
  finally show ?thesis .
qed

lemmas (in ACeD) AC = assoc commute left_commute

lemma (in ACeD) left_ident [simp]: "x : D ==> e \<cdot> x = x"
proof -
  assume D: "x : D"
  have "x \<cdot> e = x" by (rule ident)
  with D show ?thesis by (simp add: commute)
qed

lemma (in ACeD) foldD_Un_Int:
  "[| finite A; finite B; A <= D; B <= D |] ==>
    foldD D f e A \<cdot> foldD D f e B =
    foldD D f e (A Un B) \<cdot> foldD D f e (A Int B)"
  apply (induct set: Finites)
   apply (simp add: left_commute LCD.foldD_closed [OF LCD.intro [of D]])
(* left_commute is required to show premise of LCD.intro *)
  apply (simp add: AC insert_absorb Int_insert_left
    LCD.foldD_insert [OF LCD.intro [of D]]
    LCD.foldD_closed [OF LCD.intro [of D]]
    Int_mono2 Un_subset_iff)
  done

lemma (in ACeD) foldD_Un_disjoint:
  "[| finite A; finite B; A Int B = {}; A <= D; B <= D |] ==>
    foldD D f e (A Un B) = foldD D f e A \<cdot> foldD D f e B"
  by (simp add: foldD_Un_Int
    left_commute LCD.foldD_closed [OF LCD.intro [of D]] Un_subset_iff)

subsection {* Products over Finite Sets *}

constdefs
  finprod :: "[('b, 'm) monoid_scheme, 'a => 'b, 'a set] => 'b"
  "finprod G f A == if finite A
      then foldD (carrier G) (mult G o f) (one G) A
      else arbitrary"

(*
locale finite_prod = abelian_monoid + var prod +
  defines "prod == (%f A. if finite A
      then foldD (carrier G) (op \<otimes> o f) \<one> A
      else arbitrary)"
*)
(* TODO: nice syntax for the summation operator inside the locale
   like \<Otimes>\<index> i\<in>A. f i, probably needs hand-coded translation *)

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_full_simp_tac; thy)) *}

lemma (in abelian_monoid) finprod_empty [simp]: 
  "finprod G f {} = \<one>"
  by (simp add: finprod_def)

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_simp_tac; thy)) *}

declare funcsetI [intro]
  funcset_mem [dest]

lemma (in abelian_monoid) finprod_insert [simp]:
  "[| finite F; a \<notin> F; f \<in> F -> carrier G; f a \<in> carrier G |] ==>
   finprod G f (insert a F) = f a \<otimes> finprod G f F"
  apply (rule trans)
  apply (simp add: finprod_def)
  apply (rule trans)
  apply (rule LCD.foldD_insert [OF LCD.intro [of "insert a F"]])
    apply simp
    apply (rule m_lcomm)
      apply fast apply fast apply assumption
    apply (fastsimp intro: m_closed)
    apply simp+ apply fast
  apply (auto simp add: finprod_def)
  done

lemma (in abelian_monoid) finprod_one:
  "finite A ==> finprod G (%i. \<one>) A = \<one>"
proof (induct set: Finites)
  case empty show ?case by simp
next
  case (insert A a)
  have "(%i. \<one>) \<in> A -> carrier G" by auto
  with insert show ?case by simp
qed

lemma (in abelian_monoid) finprod_closed [simp]:
  fixes A
  assumes fin: "finite A" and f: "f \<in> A -> carrier G" 
  shows "finprod G f A \<in> carrier G"
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

lemma (in abelian_monoid) finprod_Un_Int:
  "[| finite A; finite B; g \<in> A -> carrier G; g \<in> B -> carrier G |] ==>
     finprod G g (A Un B) \<otimes> finprod G g (A Int B) =
     finprod G g A \<otimes> finprod G g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
proof (induct set: Finites)
  case empty then show ?case by (simp add: finprod_closed)
next
  case (insert A a)
  then have a: "g a \<in> carrier G" by fast
  from insert have A: "g \<in> A -> carrier G" by fast
  from insert A a show ?case
    by (simp add: ac Int_insert_left insert_absorb finprod_closed
          Int_mono2 Un_subset_iff) 
qed

lemma (in abelian_monoid) finprod_Un_disjoint:
  "[| finite A; finite B; A Int B = {};
      g \<in> A -> carrier G; g \<in> B -> carrier G |]
   ==> finprod G g (A Un B) = finprod G g A \<otimes> finprod G g B"
  apply (subst finprod_Un_Int [symmetric])
    apply (auto simp add: finprod_closed)
  done

lemma (in abelian_monoid) finprod_multf:
  "[| finite A; f \<in> A -> carrier G; g \<in> A -> carrier G |] ==>
   finprod G (%x. f x \<otimes> g x) A = (finprod G f A \<otimes> finprod G g A)"
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
    by (simp add: insert fA fa gA ga fgA fga ac finprod_closed Int_insert_left insert_absorb Int_mono2 Un_subset_iff)
qed

lemma (in abelian_monoid) finprod_cong:
  "[| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> finprod G f A = finprod G g B"
proof -
  assume prems: "A = B" "g : B -> carrier G"
    "!!i. i : B ==> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. [| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> finprod G f A = finprod G g B"
    proof induct
      case empty thus ?case by simp
    next
      case (insert B x)
      then have "finprod G f A = finprod G f (insert x B)" by simp
      also from insert have "... = f x \<otimes> finprod G f B"
      proof (intro finprod_insert)
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
      also from insert have "... = g x \<otimes> finprod G g B" by fastsimp
      also from insert have "... = finprod G g (insert x B)"
      by (intro finprod_insert [THEN sym]) auto
      finally show ?case .
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by (simp add: finprod_def)
  qed
qed

lemma (in abelian_monoid) finprod_cong' [cong]:
  "[| A = B; !!i. i : B ==> f i = g i;
      g : B -> carrier G = True |] ==> finprod G f A = finprod G g B"
  by (rule finprod_cong) fast+

text {*Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise @{text "g : B -> carrier G"} cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful. *}

declare funcsetI [rule del]
  funcset_mem [rule del]

lemma (in abelian_monoid) finprod_0 [simp]:
  "f : {0::nat} -> carrier G ==> finprod G f {..0} = f 0"
by (simp add: Pi_def)

lemma (in abelian_monoid) finprod_Suc [simp]:
  "f : {..Suc n} -> carrier G ==>
   finprod G f {..Suc n} = (f (Suc n) \<otimes> finprod G f {..n})"
by (simp add: Pi_def atMost_Suc)

lemma (in abelian_monoid) finprod_Suc2:
  "f : {..Suc n} -> carrier G ==>
   finprod G f {..Suc n} = (finprod G (%i. f (Suc i)) {..n} \<otimes> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case by (simp add: m_assoc Pi_def finprod_closed)
qed

lemma (in abelian_monoid) finprod_mult [simp]:
  "[| f : {..n} -> carrier G; g : {..n} -> carrier G |] ==>
     finprod G (%i. f i \<otimes> g i) {..n::nat} =
     finprod G f {..n} \<otimes> finprod G g {..n}"
  by (induct n) (simp_all add: ac Pi_def finprod_closed)

end

