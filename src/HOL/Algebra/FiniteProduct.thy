(*  Title:      HOL/Algebra/FiniteProduct.thy
    Author:     Clemens Ballarin, started 19 November 2002

This file is largely based on HOL/Finite_Set.thy.
*)

theory FiniteProduct
imports Group
begin

subsection {* Product Operator for Commutative Monoids *}

subsubsection {* Inductive Definition of a Relation for Products over Sets *}

text {* Instantiation of locale @{text LC} of theory @{text Finite_Set} is not
  possible, because here we have explicit typing rules like 
  @{text "x \<in> carrier G"}.  We introduce an explicit argument for the domain
  @{text D}. *}

inductive_set
  foldSetD :: "['a set, 'b => 'a => 'a, 'a] => ('b set * 'a) set"
  for D :: "'a set" and f :: "'b => 'a => 'a" and e :: 'a
  where
    emptyI [intro]: "e \<in> D ==> ({}, e) \<in> foldSetD D f e"
  | insertI [intro]: "[| x ~: A; f x y \<in> D; (A, y) \<in> foldSetD D f e |] ==>
                      (insert x A, f x y) \<in> foldSetD D f e"

inductive_cases empty_foldSetDE [elim!]: "({}, x) \<in> foldSetD D f e"

definition
  foldD :: "['a set, 'b => 'a => 'a, 'a, 'b set] => 'a"
  where "foldD D f e A = (THE x. (A, x) \<in> foldSetD D f e)"

lemma foldSetD_closed:
  "[| (A, z) \<in> foldSetD D f e ; e \<in> D; !!x y. [| x \<in> A; y \<in> D |] ==> f x y \<in> D 
      |] ==> z \<in> D";
  by (erule foldSetD.cases) auto

lemma Diff1_foldSetD:
  "[| (A - {x}, y) \<in> foldSetD D f e; x \<in> A; f x y \<in> D |] ==>
   (A, f x y) \<in> foldSetD D f e"
  apply (erule insert_Diff [THEN subst], rule foldSetD.intros)
    apply auto
  done

lemma foldSetD_imp_finite [simp]: "(A, x) \<in> foldSetD D f e ==> finite A"
  by (induct set: foldSetD) auto

lemma finite_imp_foldSetD:
  "[| finite A; e \<in> D; !!x y. [| x \<in> A; y \<in> D |] ==> f x y \<in> D |] ==>
   EX x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by (auto dest: foldSetD_closed)
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed


text {* Left-Commutative Operations *}

locale LCD =
  fixes B :: "'b set"
  and D :: "'a set"
  and f :: "'b => 'a => 'a"    (infixl "\<cdot>" 70)
  assumes left_commute:
    "[| x \<in> B; y \<in> B; z \<in> D |] ==> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  and f_closed [simp, intro!]: "!!x y. [| x \<in> B; y \<in> D |] ==> f x y \<in> D"

lemma (in LCD) foldSetD_closed [dest]:
  "(A, z) \<in> foldSetD D f e ==> z \<in> D";
  by (erule foldSetD.cases) auto

lemma (in LCD) Diff1_foldSetD:
  "[| (A - {x}, y) \<in> foldSetD D f e; x \<in> A; A \<subseteq> B |] ==>
  (A, f x y) \<in> foldSetD D f e"
  apply (subgoal_tac "x \<in> B")
   prefer 2 apply fast
  apply (erule insert_Diff [THEN subst], rule foldSetD.intros)
    apply auto
  done

lemma (in LCD) foldSetD_imp_finite [simp]:
  "(A, x) \<in> foldSetD D f e ==> finite A"
  by (induct set: foldSetD) auto

lemma (in LCD) finite_imp_foldSetD:
  "[| finite A; A \<subseteq> B; e \<in> D |] ==> EX x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by auto
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed

lemma (in LCD) foldSetD_determ_aux:
  "e \<in> D ==> \<forall>A x. A \<subseteq> B & card A < n --> (A, x) \<in> foldSetD D f e -->
    (\<forall>y. (A, y) \<in> foldSetD D f e --> y = x)"
  apply (induct n)
   apply (auto simp add: less_Suc_eq) (* slow *)
  apply (erule foldSetD.cases)
   apply blast
  apply (erule foldSetD.cases)
   apply blast
  apply clarify
  txt {* force simplification of @{text "card A < card (insert ...)"}. *}
  apply (erule rev_mp)
  apply (simp add: less_Suc_eq_le)
  apply (rule impI)
  apply (rename_tac xa Aa ya xb Ab yb, case_tac "xa = xb")
   apply (subgoal_tac "Aa = Ab")
    prefer 2 apply (blast elim!: equalityE)
   apply blast
  txt {* case @{prop "xa \<notin> xb"}. *}
  apply (subgoal_tac "Aa - {xb} = Ab - {xa} & xb \<in> Aa & xa \<in> Ab")
   prefer 2 apply (blast elim!: equalityE)
  apply clarify
  apply (subgoal_tac "Aa = insert xb Ab - {xa}")
   prefer 2 apply blast
  apply (subgoal_tac "card Aa \<le> card Ab")
   prefer 2
   apply (rule Suc_le_mono [THEN subst])
   apply (simp add: card_Suc_Diff1)
  apply (rule_tac A1 = "Aa - {xb}" in finite_imp_foldSetD [THEN exE])
     apply (blast intro: foldSetD_imp_finite)
    apply best
   apply assumption
  apply (frule (1) Diff1_foldSetD)
   apply best
  apply (subgoal_tac "ya = f xb x")
   prefer 2
   apply (subgoal_tac "Aa \<subseteq> B")
    prefer 2 apply best (* slow *)
   apply (blast del: equalityCE)
  apply (subgoal_tac "(Ab - {xa}, x) \<in> foldSetD D f e")
   prefer 2 apply simp
  apply (subgoal_tac "yb = f xa x")
   prefer 2 
   apply (blast del: equalityCE dest: Diff1_foldSetD)
  apply (simp (no_asm_simp))
  apply (rule left_commute)
    apply assumption
   apply best (* slow *)
  apply best
  done

lemma (in LCD) foldSetD_determ:
  "[| (A, x) \<in> foldSetD D f e; (A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B |]
  ==> y = x"
  by (blast intro: foldSetD_determ_aux [rule_format])

lemma (in LCD) foldD_equality:
  "[| (A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B |] ==> foldD D f e A = y"
  by (unfold foldD_def) (blast intro: foldSetD_determ)

lemma foldD_empty [simp]:
  "e \<in> D ==> foldD D f e {} = e"
  by (unfold foldD_def) blast

lemma (in LCD) foldD_insert_aux:
  "[| x ~: A; x \<in> B; e \<in> D; A \<subseteq> B |] ==>
    ((insert x A, v) \<in> foldSetD D f e) =
    (EX y. (A, y) \<in> foldSetD D f e & v = f x y)"
  apply auto
  apply (rule_tac A1 = A in finite_imp_foldSetD [THEN exE])
     apply (fastforce dest: foldSetD_imp_finite)
    apply assumption
   apply assumption
  apply (blast intro: foldSetD_determ)
  done

lemma (in LCD) foldD_insert:
    "[| finite A; x ~: A; x \<in> B; e \<in> D; A \<subseteq> B |] ==>
     foldD D f e (insert x A) = f x (foldD D f e A)"
  apply (unfold foldD_def)
  apply (simp add: foldD_insert_aux)
  apply (rule the_equality)
   apply (auto intro: finite_imp_foldSetD
     cong add: conj_cong simp add: foldD_def [symmetric] foldD_equality)
  done

lemma (in LCD) foldD_closed [simp]:
  "[| finite A; e \<in> D; A \<subseteq> B |] ==> foldD D f e A \<in> D"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: foldD_insert)
qed

lemma (in LCD) foldD_commute:
  "[| finite A; x \<in> B; e \<in> D; A \<subseteq> B |] ==>
   f x (foldD D f e A) = foldD D f (f x e) A"
  apply (induct set: finite)
   apply simp
  apply (auto simp add: left_commute foldD_insert)
  done

lemma Int_mono2:
  "[| A \<subseteq> C; B \<subseteq> C |] ==> A Int B \<subseteq> C"
  by blast

lemma (in LCD) foldD_nest_Un_Int:
  "[| finite A; finite C; e \<in> D; A \<subseteq> B; C \<subseteq> B |] ==>
   foldD D f (foldD D f e C) A = foldD D f (foldD D f e (A Int C)) (A Un C)"
  apply (induct set: finite)
   apply simp
  apply (simp add: foldD_insert foldD_commute Int_insert_left insert_absorb
    Int_mono2)
  done

lemma (in LCD) foldD_nest_Un_disjoint:
  "[| finite A; finite B; A Int B = {}; e \<in> D; A \<subseteq> B; C \<subseteq> B |]
    ==> foldD D f e (A Un B) = foldD D f (foldD D f e B) A"
  by (simp add: foldD_nest_Un_Int)

-- {* Delete rules to do with @{text foldSetD} relation. *}

declare foldSetD_imp_finite [simp del]
  empty_foldSetDE [rule del]
  foldSetD.intros [rule del]
declare (in LCD)
  foldSetD_closed [rule del]


text {* Commutative Monoids *}

text {*
  We enter a more restrictive context, with @{text "f :: 'a => 'a => 'a"}
  instead of @{text "'b => 'a => 'a"}.
*}

locale ACeD =
  fixes D :: "'a set"
    and f :: "'a => 'a => 'a"    (infixl "\<cdot>" 70)
    and e :: 'a
  assumes ident [simp]: "x \<in> D ==> x \<cdot> e = x"
    and commute: "[| x \<in> D; y \<in> D |] ==> x \<cdot> y = y \<cdot> x"
    and assoc: "[| x \<in> D; y \<in> D; z \<in> D |] ==> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and e_closed [simp]: "e \<in> D"
    and f_closed [simp]: "[| x \<in> D; y \<in> D |] ==> x \<cdot> y \<in> D"

lemma (in ACeD) left_commute:
  "[| x \<in> D; y \<in> D; z \<in> D |] ==> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  assume D: "x \<in> D" "y \<in> D" "z \<in> D"
  then have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp add: commute)
  also from D have "... = y \<cdot> (z \<cdot> x)" by (simp add: assoc)
  also from D have "z \<cdot> x = x \<cdot> z" by (simp add: commute)
  finally show ?thesis .
qed

lemmas (in ACeD) AC = assoc commute left_commute

lemma (in ACeD) left_ident [simp]: "x \<in> D ==> e \<cdot> x = x"
proof -
  assume "x \<in> D"
  then have "x \<cdot> e = x" by (rule ident)
  with `x \<in> D` show ?thesis by (simp add: commute)
qed

lemma (in ACeD) foldD_Un_Int:
  "[| finite A; finite B; A \<subseteq> D; B \<subseteq> D |] ==>
    foldD D f e A \<cdot> foldD D f e B =
    foldD D f e (A Un B) \<cdot> foldD D f e (A Int B)"
  apply (induct set: finite)
   apply (simp add: left_commute LCD.foldD_closed [OF LCD.intro [of D]])
  apply (simp add: AC insert_absorb Int_insert_left
    LCD.foldD_insert [OF LCD.intro [of D]]
    LCD.foldD_closed [OF LCD.intro [of D]]
    Int_mono2)
  done

lemma (in ACeD) foldD_Un_disjoint:
  "[| finite A; finite B; A Int B = {}; A \<subseteq> D; B \<subseteq> D |] ==>
    foldD D f e (A Un B) = foldD D f e A \<cdot> foldD D f e B"
  by (simp add: foldD_Un_Int
    left_commute LCD.foldD_closed [OF LCD.intro [of D]])


subsubsection {* Products over Finite Sets *}

definition
  finprod :: "[('b, 'm) monoid_scheme, 'a => 'b, 'a set] => 'b"
  where "finprod G f A =
   (if finite A
    then foldD (carrier G) (mult G o f) \<one>\<^bsub>G\<^esub> A
    else undefined)"

syntax
  "_finprod" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Otimes>__:_. _)" [1000, 0, 51, 10] 10)
syntax (xsymbols)
  "_finprod" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Otimes>__\<in>_. _)" [1000, 0, 51, 10] 10)
syntax (HTML output)
  "_finprod" :: "index => idt => 'a set => 'b => 'b"
      ("(3\<Otimes>__\<in>_. _)" [1000, 0, 51, 10] 10)
translations
  "\<Otimes>\<index>i:A. b" == "CONST finprod \<struct>\<index> (%i. b) A"
  -- {* Beware of argument permutation! *}

lemma (in comm_monoid) finprod_empty [simp]: 
  "finprod G f {} = \<one>"
  by (simp add: finprod_def)

declare funcsetI [intro]
  funcset_mem [dest]

context comm_monoid begin

lemma finprod_insert [simp]:
  "[| finite F; a \<notin> F; f \<in> F -> carrier G; f a \<in> carrier G |] ==>
   finprod G f (insert a F) = f a \<otimes> finprod G f F"
  apply (rule trans)
   apply (simp add: finprod_def)
  apply (rule trans)
   apply (rule LCD.foldD_insert [OF LCD.intro [of "insert a F"]])
         apply simp
         apply (rule m_lcomm)
           apply fast
          apply fast
         apply assumption
        apply fastforce
       apply simp+
   apply fast
  apply (auto simp add: finprod_def)
  done

lemma finprod_one [simp]:
  "finite A ==> (\<Otimes>i:A. \<one>) = \<one>"
proof (induct set: finite)
  case empty show ?case by simp
next
  case (insert a A)
  have "(%i. \<one>) \<in> A -> carrier G" by auto
  with insert show ?case by simp
qed

lemma finprod_closed [simp]:
  fixes A
  assumes fin: "finite A" and f: "f \<in> A -> carrier G" 
  shows "finprod G f A \<in> carrier G"
using fin f
proof induct
  case empty show ?case by simp
next
  case (insert a A)
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

lemma finprod_Un_Int:
  "[| finite A; finite B; g \<in> A -> carrier G; g \<in> B -> carrier G |] ==>
     finprod G g (A Un B) \<otimes> finprod G g (A Int B) =
     finprod G g A \<otimes> finprod G g B"
-- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert a A)
  then have a: "g a \<in> carrier G" by fast
  from insert have A: "g \<in> A -> carrier G" by fast
  from insert A a show ?case
    by (simp add: m_ac Int_insert_left insert_absorb Int_mono2) 
qed

lemma finprod_Un_disjoint:
  "[| finite A; finite B; A Int B = {};
      g \<in> A -> carrier G; g \<in> B -> carrier G |]
   ==> finprod G g (A Un B) = finprod G g A \<otimes> finprod G g B"
  apply (subst finprod_Un_Int [symmetric])
      apply auto
  done

lemma finprod_multf:
  "[| finite A; f \<in> A -> carrier G; g \<in> A -> carrier G |] ==>
   finprod G (%x. f x \<otimes> g x) A = (finprod G f A \<otimes> finprod G g A)"
proof (induct set: finite)
  case empty show ?case by simp
next
  case (insert a A) then
  have fA: "f \<in> A -> carrier G" by fast
  from insert have fa: "f a \<in> carrier G" by fast
  from insert have gA: "g \<in> A -> carrier G" by fast
  from insert have ga: "g a \<in> carrier G" by fast
  from insert have fgA: "(%x. f x \<otimes> g x) \<in> A -> carrier G"
    by (simp add: Pi_def)
  show ?case
    by (simp add: insert fA fa gA ga fgA m_ac)
qed

lemma finprod_cong':
  "[| A = B; g \<in> B -> carrier G;
      !!i. i \<in> B ==> f i = g i |] ==> finprod G f A = finprod G g B"
proof -
  assume prems: "A = B" "g \<in> B -> carrier G"
    "!!i. i \<in> B ==> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. [| A = B; g \<in> B -> carrier G;
      !!i. i \<in> B ==> f i = g i |] ==> finprod G f A = finprod G g B"
    proof induct
      case empty thus ?case by simp
    next
      case (insert x B)
      then have "finprod G f A = finprod G f (insert x B)" by simp
      also from insert have "... = f x \<otimes> finprod G f B"
      proof (intro finprod_insert)
        show "finite B" by fact
      next
        show "x ~: B" by fact
      next
        assume "x ~: B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
          "g \<in> insert x B \<rightarrow> carrier G"
        thus "f \<in> B -> carrier G" by fastforce
      next
        assume "x ~: B" "!!i. i \<in> insert x B \<Longrightarrow> f i = g i"
          "g \<in> insert x B \<rightarrow> carrier G"
        thus "f x \<in> carrier G" by fastforce
      qed
      also from insert have "... = g x \<otimes> finprod G g B" by fastforce
      also from insert have "... = finprod G g (insert x B)"
      by (intro finprod_insert [THEN sym]) auto
      finally show ?case .
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by (simp add: finprod_def)
  qed
qed

lemma finprod_cong:
  "[| A = B; f \<in> B -> carrier G = True;
      !!i. i \<in> B =simp=> f i = g i |] ==> finprod G f A = finprod G g B"
  (* This order of prems is slightly faster (3%) than the last two swapped. *)
  by (rule finprod_cong') (auto simp add: simp_implies_def)

text {*Usually, if this rule causes a failed congruence proof error,
  the reason is that the premise @{text "g \<in> B -> carrier G"} cannot be shown.
  Adding @{thm [source] Pi_def} to the simpset is often useful.
  For this reason, @{thm [source] comm_monoid.finprod_cong}
  is not added to the simpset by default.
*}

end

declare funcsetI [rule del]
  funcset_mem [rule del]

context comm_monoid begin

lemma finprod_0 [simp]:
  "f \<in> {0::nat} -> carrier G ==> finprod G f {..0} = f 0"
by (simp add: Pi_def)

lemma finprod_Suc [simp]:
  "f \<in> {..Suc n} -> carrier G ==>
   finprod G f {..Suc n} = (f (Suc n) \<otimes> finprod G f {..n})"
by (simp add: Pi_def atMost_Suc)

lemma finprod_Suc2:
  "f \<in> {..Suc n} -> carrier G ==>
   finprod G f {..Suc n} = (finprod G (%i. f (Suc i)) {..n} \<otimes> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case by (simp add: m_assoc Pi_def)
qed

lemma finprod_mult [simp]:
  "[| f \<in> {..n} -> carrier G; g \<in> {..n} -> carrier G |] ==>
     finprod G (%i. f i \<otimes> g i) {..n::nat} =
     finprod G f {..n} \<otimes> finprod G g {..n}"
  by (induct n) (simp_all add: m_ac Pi_def)

(* The following two were contributed by Jeremy Avigad. *)

lemma finprod_reindex:
  assumes fin: "finite A"
    shows "f : (h ` A) \<rightarrow> carrier G \<Longrightarrow> 
        inj_on h A ==> finprod G f (h ` A) = finprod G (%x. f (h x)) A"
  using fin
  by induct (auto simp add: Pi_def)

lemma finprod_const:
  assumes fin [simp]: "finite A"
      and a [simp]: "a : carrier G"
    shows "finprod G (%x. a) A = a (^) card A"
  using fin apply induct
  apply force
  apply (subst finprod_insert)
  apply auto
  apply (subst m_comm)
  apply auto
  done

(* The following lemma was contributed by Jesus Aransay. *)

lemma finprod_singleton:
  assumes i_in_A: "i \<in> A" and fin_A: "finite A" and f_Pi: "f \<in> A \<rightarrow> carrier G"
  shows "(\<Otimes>j\<in>A. if i = j then f j else \<one>) = f i"
  using i_in_A finprod_insert [of "A - {i}" i "(\<lambda>j. if i = j then f j else \<one>)"]
    fin_A f_Pi finprod_one [of "A - {i}"]
    finprod_cong [of "A - {i}" "A - {i}" "(\<lambda>j. if i = j then f j else \<one>)" "(\<lambda>i. \<one>)"] 
  unfolding Pi_def simp_implies_def by (force simp add: insert_absorb)

end

end
