(*  Title:      Summation Operator for Abelian Groups
    ID:         $Id$
    Author:     Clemens Ballarin, started 19 November 2002
    Copyright:  TU Muenchen
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

subsection {* Abelian groups with summation operator *}

lemma (in abelian_group) sum_lcomm:
  "[| x : carrier G; y : carrier G; z : carrier G |] ==>
   x \<oplus> (y \<oplus> z) = y \<oplus> (x \<oplus> z)"
proof -
  assume "x : carrier G" "y : carrier G" "z : carrier G"
  then have "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z" by (simp add: sum_assoc)
  also from prems have "... = (y \<oplus> x) \<oplus> z" by (simp add: sum_commute)
  also from prems have "... = y \<oplus> (x \<oplus> z)" by (simp add: sum_assoc)
  finally show ?thesis .
qed

lemmas (in abelian_group) AC = sum_assoc sum_commute sum_lcomm

record ('a, 'b) group_with_sum = "'a group" +
  setSum :: "['b => 'a, 'b set] => 'a"

(* TODO: nice syntax for the summation operator inside the locale
   like \<Oplus>\<index> i\<in>A. f i, probably needs hand-coded translation *)

locale agroup_with_sum = abelian_group +
  assumes setSum_def:
  "setSum G f A = (if finite A then foldD (carrier G) (op \<oplus> o f) \<zero> A else \<zero>)"

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_full_simp_tac; thy)) *}

lemma (in agroup_with_sum) setSum_empty [simp]: 
  "setSum G f {} = \<zero>"
  by (simp add: setSum_def)

ML_setup {* 

Context.>> (fn thy => (simpset_ref_of thy :=
  simpset_of thy setsubgoaler asm_simp_tac; thy)) *}

lemma insert_conj:
  "[| a = b; a : B |] ==> a : insert b B"
  by blast

declare funcsetI [intro]
  funcset_mem [dest]

lemma (in agroup_with_sum) setSum_insert [simp]:
  "[| finite F; a \<notin> F; f : F -> carrier G; f a : carrier G |] ==>
   setSum G f (insert a F) = f a \<oplus> setSum G f F"
  apply (rule trans)
  apply (simp add: setSum_def)
  apply (rule trans)
  apply (rule LCD.foldD_insert [OF LCD.intro [of "insert a F"]])
    apply simp
    apply (rule sum_lcomm)
      apply fast apply fast apply assumption
    apply (fastsimp intro: sum_closed)
    apply simp+ apply fast
  apply (auto simp add: setSum_def)
  done

lemma (in agroup_with_sum) setSum_0:
  "setSum G (%i. \<zero>) A = \<zero>"
(*  apply (case_tac "finite A")
   prefer 2 apply (simp add: setSum_def) *)
proof (cases "finite A")
  case True then show ?thesis
  proof (induct set: Finites)
    case empty show ?case by simp
  next
    case (insert A a)
    have "(%i. \<zero>) : A -> carrier G" by auto
    with insert show ?case by simp
  qed
next
  case False then show ?thesis by (simp add: setSum_def)
qed

(*
lemma setSum_eq_0_iff [simp]:
    "finite F ==> (setSum f F = 0) = (ALL a:F. f a = (0::nat))"
  by (induct set: Finites) auto

lemma setSum_SucD: "setSum f A = Suc n ==> EX a:A. 0 < f a"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setSum_def)
  apply (erule rev_mp)
  apply (erule finite_induct)
   apply auto
  done

lemma card_eq_setSum: "finite A ==> card A = setSum (\<lambda>x. 1) A"
*)  -- {* Could allow many @{text "card"} proofs to be simplified. *}
(*
  by (induct set: Finites) auto
*)

lemma (in agroup_with_sum) setSum_closed:
  "[| finite A; f : A -> carrier G |] ==> setSum G f A : carrier G"
proof (induct set: Finites)
  case empty show ?case by simp
next
  case (insert A a)
  then have a: "f a : carrier G" by fast
  from insert have A: "f : A -> carrier G" by fast
  from insert A a show ?case by simp
qed
(*
lemma (in agroup_with_sum) setSum_closed:
  "[| finite A; f``A <= carrier G |] ==> setSum G f A : carrier G"

lemma (in agroup_with_sum) setSum_closed:
  "[| finite A; !!i. i : A ==> f i : carrier G |] ==>
   setSum G f A : carrier G"
*)

lemma funcset_Int_left [simp, intro]:
  "[| f : A -> C; f : B -> C |] ==> f : A Int B -> C"
  by fast

lemma funcset_Int_right:
  "(f : A -> B Int C) = (f : A -> B & f : A -> C)"
  by fast

lemma funcset_Un_right:
  "[| f : A -> B; f : A -> C |] ==> f : A -> B Un C"
  by fast

lemma funcset_Un_left [iff]:
  "(f : A Un B -> C) = (f : A -> C & f : B -> C)"
  by fast

lemma (in agroup_with_sum) setSum_Un_Int:
  "[| finite A; finite B; g : A -> carrier G; g : B -> carrier G |] ==>
   setSum G g (A Un B) \<oplus> setSum G g (A Int B) = setSum G g A \<oplus> setSum G g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
proof (induct set: Finites)
  case empty then show ?case by (simp add: setSum_closed)
next
  case (insert A a)
  then have a: "g a : carrier G" by fast
  from insert have A: "g : A -> carrier G" by fast
  from insert A a show ?case
    by (simp add: AC Int_insert_left insert_absorb setSum_closed
          Int_mono2 Un_subset_iff) 
qed

lemma (in agroup_with_sum) setSum_Un_disjoint:
  "[| finite A; finite B; A Int B = {};
      g : A -> carrier G; g : B -> carrier G |]
   ==> setSum G g (A Un B) = setSum G g A \<oplus> setSum G g B"
  apply (subst setSum_Un_Int [symmetric])
    apply (auto simp add: setSum_closed)
  done

(*
lemma setSum_UN_disjoint:
  fixes f :: "'a => 'b::plus_ac0"
  shows
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setSum f (UNION I A) = setSum (\<lambda>i. setSum f (A i)) I"
  apply (induct set: Finites)
   apply simp
  apply atomize
  apply (subgoal_tac "ALL i:F. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x Int UNION F A = {}")
   prefer 2 apply blast
  apply (simp add: setSum_Un_disjoint)
  done
*)
lemma (in agroup_with_sum) setSum_addf:
  "[| finite A; f : A -> carrier G; g : A -> carrier G |] ==>
   setSum G (%x. f x \<oplus> g x) A = (setSum G f A \<oplus> setSum G g A)"
proof (induct set: Finites)
  case empty show ?case by simp
next
  case (insert A a) then
  have fA: "f : A -> carrier G" by fast
  from insert have fa: "f a : carrier G" by fast
  from insert have gA: "g : A -> carrier G" by fast
  from insert have ga: "g a : carrier G" by fast
  from insert have fga: "(%x. f x \<oplus> g x) a : carrier G" by (simp add: Pi_def)
  from insert have fgA: "(%x. f x \<oplus> g x) : A -> carrier G"
    by (simp add: Pi_def)
  show ?case  (* check if all simps are really necessary *)
    by (simp add: insert fA fa gA ga fgA fga AC setSum_closed Int_insert_left insert_absorb Int_mono2 Un_subset_iff)
qed

(*
lemma setSum_Un: "finite A ==> finite B ==>
    (setSum f (A Un B) :: nat) = setSum f A + setSum f B - setSum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
  apply (subst setSum_Un_Int [symmetric])
    apply auto
  done

lemma setSum_diff1: "(setSum f (A - {a}) :: nat) =
    (if a:A then setSum f A - f a else setSum f A)"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setSum_def)
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (drule_tac a = a in mk_disjoint_insert)
  apply auto
  done
*)

lemma (in agroup_with_sum) setSum_cong:
  "[| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> setSum G f A = setSum G g B"
proof -
  assume prems: "A = B" "g : B -> carrier G"
    "!!i. i : B ==> f i = g i"
  show ?thesis
  proof (cases "finite B")
    case True
    then have "!!A. [| A = B; g : B -> carrier G;
      !!i. i : B ==> f i = g i |] ==> setSum G f A = setSum G g B"
    proof induct
      case empty thus ?case by simp
    next
      case (insert B x)
      then have "setSum G f A = setSum G f (insert x B)" by simp
      also from insert have "... = f x \<oplus> setSum G f B"
      proof (intro setSum_insert)
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
      also from insert have "... = g x \<oplus> setSum G g B" by fastsimp
      also from insert have "... = setSum G g (insert x B)"
      by (intro setSum_insert [THEN sym]) auto
      finally show ?case .
    qed
    with prems show ?thesis by simp
  next
    case False with prems show ?thesis by (simp add: setSum_def)
  qed
qed

lemma (in agroup_with_sum) setSum_cong1 [cong]:
  "[| A = B; !!i. i : B ==> f i = g i;
      g : B -> carrier G = True |] ==> setSum G f A = setSum G g B"
  by (rule setSum_cong) fast+

text {*Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise @{text "g : B -> carrier G"} cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful. *}

declare funcsetI [rule del]
  funcset_mem [rule del]

(*** Examples --- Summation over the integer interval {..n} ***)

(* New locale where index set is restricted to nat *)

locale agroup_with_natsum = agroup_with_sum +
  assumes "False ==> setSum G f (A::nat set) = setSum G f A"

lemma (in agroup_with_natsum) natSum_0 [simp]:
  "f : {0::nat} -> carrier G ==> setSum G f {..0} = f 0"
by (simp add: Pi_def)

lemma (in agroup_with_natsum) natsum_Suc [simp]:
  "f : {..Suc n} -> carrier G ==>
   setSum G f {..Suc n} = (f (Suc n) \<oplus> setSum G f {..n})"
by (simp add: Pi_def atMost_Suc)

lemma (in agroup_with_natsum) natsum_Suc2:
  "f : {..Suc n} -> carrier G ==>
   setSum G f {..Suc n} = (setSum G (%i. f (Suc i)) {..n} \<oplus> f 0)"
proof (induct n)
  case 0 thus ?case by (simp add: Pi_def)
next
  case Suc thus ?case by (simp add: sum_assoc Pi_def setSum_closed)
qed

lemma (in agroup_with_natsum) natsum_zero [simp]:
  "setSum G (%i. \<zero>) {..n::nat} = \<zero>"
by (induct n) (simp_all add: Pi_def)

lemma (in agroup_with_natsum) natsum_add [simp]:
  "[| f : {..n} -> carrier G; g : {..n} -> carrier G |] ==>
   setSum G (%i. f i \<oplus> g i) {..n::nat} = setSum G f {..n} \<oplus> setSum G g {..n}"
by (induct n) (simp_all add: AC Pi_def setSum_closed)

end

