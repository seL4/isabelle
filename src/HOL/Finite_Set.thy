(*  Title:      HOL/Finite_Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Finite sets *}

theory Finite_Set = Divides + Power + Inductive + SetInterval:

subsection {* Collection of finite sets *}

consts Finites :: "'a set set"

inductive Finites
  intros
    emptyI [simp, intro!]: "{} : Finites"
    insertI [simp, intro!]: "A : Finites ==> insert a A : Finites"

syntax
  finite :: "'a set => bool"
translations
  "finite A" == "A : Finites"

axclass finite \<subseteq> type
  finite: "finite UNIV"


lemma finite_induct [case_names empty insert, induct set: Finites]:
  "finite F ==>
    P {} ==> (!!F x. finite F ==> x \<notin> F ==> P F ==> P (insert x F)) ==> P F"
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
proof -
  assume "P {}" and insert: "!!F x. finite F ==> x \<notin> F ==> P F ==> P (insert x F)"
  assume "finite F"
  thus "P F"
  proof induct
    show "P {}" .
    fix F x assume F: "finite F" and P: "P F"
    show "P (insert x F)"
    proof cases
      assume "x \<in> F"
      hence "insert x F = F" by (rule insert_absorb)
      with P show ?thesis by (simp only:)
    next
      assume "x \<notin> F"
      from F this P show ?thesis by (rule insert)
    qed
  qed
qed

lemma finite_subset_induct [consumes 2, case_names empty insert]:
  "finite F ==> F \<subseteq> A ==>
    P {} ==> (!!F a. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)) ==>
    P F"
proof -
  assume "P {}" and insert: "!!F a. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)"
  assume "finite F"
  thus "F \<subseteq> A ==> P F"
  proof induct
    show "P {}" .
    fix F x assume "finite F" and "x \<notin> F"
      and P: "F \<subseteq> A ==> P F" and i: "insert x F \<subseteq> A"
    show "P (insert x F)"
    proof (rule insert)
      from i show "x \<in> A" by blast
      from i have "F \<subseteq> A" by blast
      with P show "P F" .
    qed
  qed
qed

lemma finite_UnI: "finite F ==> finite G ==> finite (F Un G)"
  -- {* The union of two finite sets is finite. *}
  by (induct set: Finites) simp_all

lemma finite_subset: "A \<subseteq> B ==> finite B ==> finite A"
  -- {* Every subset of a finite set is finite. *}
proof -
  assume "finite B"
  thus "!!A. A \<subseteq> B ==> finite A"
  proof induct
    case empty
    thus ?case by simp
  next
    case (insert F x A)
    have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F ==> finite (A - {x})" .
    show "finite A"
    proof cases
      assume x: "x \<in> A"
      with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff)
      with r have "finite (A - {x})" .
      hence "finite (insert x (A - {x}))" ..
      also have "insert x (A - {x}) = A" by (rule insert_Diff)
      finally show ?thesis .
    next
      show "A \<subseteq> F ==> ?thesis" .
      assume "x \<notin> A"
      with A show "A \<subseteq> F" by (simp add: subset_insert_iff)
    qed
  qed
qed

lemma finite_Un [iff]: "finite (F Un G) = (finite F & finite G)"
  by (blast intro: finite_subset [of _ "X Un Y", standard] finite_UnI)

lemma finite_Int [simp, intro]: "finite F | finite G ==> finite (F Int G)"
  -- {* The converse obviously fails. *}
  by (blast intro: finite_subset)

lemma finite_insert [simp]: "finite (insert a A) = finite A"
  apply (subst insert_is_Un)
  apply (simp only: finite_Un)
  apply blast
  done

lemma finite_imageI: "finite F ==> finite (h ` F)"
  -- {* The image of a finite set is finite. *}
  by (induct set: Finites) simp_all

lemma finite_range_imageI:
    "finite (range g) ==> finite (range (%x. f (g x)))"
  apply (drule finite_imageI)
  apply simp
  done

lemma finite_empty_induct:
  "finite A ==>
  P A ==> (!!a A. finite A ==> a:A ==> P A ==> P (A - {a})) ==> P {}"
proof -
  assume "finite A"
    and "P A" and "!!a A. finite A ==> a:A ==> P A ==> P (A - {a})"
  have "P (A - A)"
  proof -
    fix c b :: "'a set"
    presume c: "finite c" and b: "finite b"
      and P1: "P b" and P2: "!!x y. finite y ==> x \<in> y ==> P y ==> P (y - {x})"
    from c show "c \<subseteq> b ==> P (b - c)"
    proof induct
      case empty
      from P1 show ?case by simp
    next
      case (insert F x)
      have "P (b - F - {x})"
      proof (rule P2)
        from _ b show "finite (b - F)" by (rule finite_subset) blast
        from insert show "x \<in> b - F" by simp
        from insert show "P (b - F)" by simp
      qed
      also have "b - F - {x} = b - insert x F" by (rule Diff_insert [symmetric])
      finally show ?case .
    qed
  next
    show "A \<subseteq> A" ..
  qed
  thus "P {}" by simp
qed

lemma finite_Diff [simp]: "finite B ==> finite (B - Ba)"
  by (rule Diff_subset [THEN finite_subset])

lemma finite_Diff_insert [iff]: "finite (A - insert a B) = finite (A - B)"
  apply (subst Diff_insert)
  apply (case_tac "a : A - B")
   apply (rule finite_insert [symmetric, THEN trans])
   apply (subst insert_Diff)
    apply simp_all
  done


lemma finite_imageD: "finite (f`A) ==> inj_on f A ==> finite A"
proof -
  have aux: "!!A. finite (A - {}) = finite A" by simp
  fix B :: "'a set"
  assume "finite B"
  thus "!!A. f`A = B ==> inj_on f A ==> finite A"
    apply induct
     apply simp
    apply (subgoal_tac "EX y:A. f y = x & F = f ` (A - {y})")
     apply clarify
     apply (simp (no_asm_use) add: inj_on_def)
     apply (blast dest!: aux [THEN iffD1])
    apply atomize
    apply (erule_tac V = "ALL A. ?PP (A)" in thin_rl)
    apply (frule subsetD [OF equalityD2 insertI1])
    apply clarify
    apply (rule_tac x = xa in bexI)
     apply (simp_all add: inj_on_image_set_diff)
    done
qed (rule refl)


subsubsection {* The finite UNION of finite sets *}

lemma finite_UN_I: "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (UN a:A. B a)"
  by (induct set: Finites) simp_all

text {*
  Strengthen RHS to
  @{prop "((ALL x:A. finite (B x)) & finite {x. x:A & B x ~= {}})"}?

  We'd need to prove
  @{prop "finite C ==> ALL A B. (UNION A B) <= C --> finite {x. x:A & B x ~= {}}"}
  by induction. *}

lemma finite_UN [simp]: "finite A ==> finite (UNION A B) = (ALL x:A. finite (B x))"
  by (blast intro: finite_UN_I finite_subset)


subsubsection {* Sigma of finite sets *}

lemma finite_SigmaI [simp]:
    "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (SIGMA a:A. B a)"
  by (unfold Sigma_def) (blast intro!: finite_UN_I)

lemma finite_Prod_UNIV:
    "finite (UNIV::'a set) ==> finite (UNIV::'b set) ==> finite (UNIV::('a * 'b) set)"
  apply (subgoal_tac "(UNIV:: ('a * 'b) set) = Sigma UNIV (%x. UNIV)")
   apply (erule ssubst)
   apply (erule finite_SigmaI)
   apply auto
  done

instance unit :: finite
proof
  have "finite {()}" by simp
  also have "{()} = UNIV" by auto
  finally show "finite (UNIV :: unit set)" .
qed

instance * :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a \<times> 'b) set)"
  proof (rule finite_Prod_UNIV)
    show "finite (UNIV :: 'a set)" by (rule finite)
    show "finite (UNIV :: 'b set)" by (rule finite)
  qed
qed


subsubsection {* The powerset of a finite set *}

lemma finite_Pow_iff [iff]: "finite (Pow A) = finite A"
proof
  assume "finite (Pow A)"
  with _ have "finite ((%x. {x}) ` A)" by (rule finite_subset) blast
  thus "finite A" by (rule finite_imageD [unfolded inj_on_def]) simp
next
  assume "finite A"
  thus "finite (Pow A)"
    by induct (simp_all add: finite_UnI finite_imageI Pow_insert)
qed

lemma finite_converse [iff]: "finite (r^-1) = finite r"
  apply (subgoal_tac "r^-1 = (%(x,y). (y,x))`r")
   apply simp
   apply (rule iffI)
    apply (erule finite_imageD [unfolded inj_on_def])
    apply (simp split add: split_split)
   apply (erule finite_imageI)
  apply (simp add: converse_def image_def)
  apply auto
  apply (rule bexI)
   prefer 2 apply assumption
  apply simp
  done

lemma finite_lessThan [iff]: (fixes k :: nat) "finite {..k(}"
  by (induct k) (simp_all add: lessThan_Suc)

lemma finite_atMost [iff]: (fixes k :: nat) "finite {..k}"
  by (induct k) (simp_all add: atMost_Suc)

lemma bounded_nat_set_is_finite:
    "(ALL i:N. i < (n::nat)) ==> finite N"
  -- {* A bounded set of natural numbers is finite. *}
  apply (rule finite_subset)
   apply (rule_tac [2] finite_lessThan)
  apply auto
  done


subsubsection {* Finiteness of transitive closure *}

text {* (Thanks to Sidi Ehmety) *}

lemma finite_Field: "finite r ==> finite (Field r)"
  -- {* A finite relation has a finite field (@{text "= domain \<union> range"}. *}
  apply (induct set: Finites)
   apply (auto simp add: Field_def Domain_insert Range_insert)
  done

lemma trancl_subset_Field2: "r^+ <= Field r \<times> Field r"
  apply clarify
  apply (erule trancl_induct)
   apply (auto simp add: Field_def)
  done

lemma finite_trancl: "finite (r^+) = finite r"
  apply auto
   prefer 2
   apply (rule trancl_subset_Field2 [THEN finite_subset])
   apply (rule finite_SigmaI)
    prefer 3
    apply (blast intro: r_into_trancl finite_subset)
   apply (auto simp add: finite_Field)
  done


subsection {* Finite cardinality *}

text {*
  This definition, although traditional, is ugly to work with: @{text
  "card A == LEAST n. EX f. A = {f i | i. i < n}"}.  Therefore we have
  switched to an inductive one:
*}

consts cardR :: "('a set \<times> nat) set"

inductive cardR
  intros
    EmptyI: "({}, 0) : cardR"
    InsertI: "(A, n) : cardR ==> a \<notin> A ==> (insert a A, Suc n) : cardR"

constdefs
  card :: "'a set => nat"
  "card A == THE n. (A, n) : cardR"

inductive_cases cardR_emptyE: "({}, n) : cardR"
inductive_cases cardR_insertE: "(insert a A,n) : cardR"

lemma cardR_SucD: "(A, n) : cardR ==> a : A --> (EX m. n = Suc m)"
  by (induct set: cardR) simp_all

lemma cardR_determ_aux1:
    "(A, m): cardR ==> (!!n a. m = Suc n ==> a:A ==> (A - {a}, n) : cardR)"
  apply (induct set: cardR)
   apply auto
  apply (simp add: insert_Diff_if)
  apply auto
  apply (drule cardR_SucD)
  apply (blast intro!: cardR.intros)
  done

lemma cardR_determ_aux2: "(insert a A, Suc m) : cardR ==> a \<notin> A ==> (A, m) : cardR"
  by (drule cardR_determ_aux1) auto

lemma cardR_determ: "(A, m): cardR ==> (!!n. (A, n) : cardR ==> n = m)"
  apply (induct set: cardR)
   apply (safe elim!: cardR_emptyE cardR_insertE)
  apply (rename_tac B b m)
  apply (case_tac "a = b")
   apply (subgoal_tac "A = B")
    prefer 2 apply (blast elim: equalityE)
   apply blast
  apply (subgoal_tac "EX C. A = insert b C & B = insert a C")
   prefer 2
   apply (rule_tac x = "A Int B" in exI)
   apply (blast elim: equalityE)
  apply (frule_tac A = B in cardR_SucD)
  apply (blast intro!: cardR.intros dest!: cardR_determ_aux2)
  done

lemma cardR_imp_finite: "(A, n) : cardR ==> finite A"
  by (induct set: cardR) simp_all

lemma finite_imp_cardR: "finite A ==> EX n. (A, n) : cardR"
  by (induct set: Finites) (auto intro!: cardR.intros)

lemma card_equality: "(A,n) : cardR ==> card A = n"
  by (unfold card_def) (blast intro: cardR_determ)

lemma card_empty [simp]: "card {} = 0"
  by (unfold card_def) (blast intro!: cardR.intros elim!: cardR_emptyE)

lemma card_insert_disjoint [simp]:
  "finite A ==> x \<notin> A ==> card (insert x A) = Suc(card A)"
proof -
  assume x: "x \<notin> A"
  hence aux: "!!n. ((insert x A, n) : cardR) = (EX m. (A, m) : cardR & n = Suc m)"
    apply (auto intro!: cardR.intros)
    apply (rule_tac A1 = A in finite_imp_cardR [THEN exE])
     apply (force dest: cardR_imp_finite)
    apply (blast intro!: cardR.intros intro: cardR_determ)
    done
  assume "finite A"
  thus ?thesis
    apply (simp add: card_def aux)
    apply (rule the_equality)
     apply (auto intro: finite_imp_cardR
       cong: conj_cong simp: card_def [symmetric] card_equality)
    done
qed

lemma card_0_eq [simp]: "finite A ==> (card A = 0) = (A = {})"
  apply auto
  apply (drule_tac a = x in mk_disjoint_insert)
  apply clarify
  apply (rotate_tac -1)
  apply auto
  done

lemma card_insert_if:
    "finite A ==> card (insert x A) = (if x:A then card A else Suc(card(A)))"
  by (simp add: insert_absorb)

lemma card_Suc_Diff1: "finite A ==> x: A ==> Suc (card (A - {x})) = card A"
  apply (rule_tac t = A in insert_Diff [THEN subst])
   apply assumption
  apply simp
  done

lemma card_Diff_singleton:
    "finite A ==> x: A ==> card (A - {x}) = card A - 1"
  by (simp add: card_Suc_Diff1 [symmetric])

lemma card_Diff_singleton_if:
    "finite A ==> card (A-{x}) = (if x : A then card A - 1 else card A)"
  by (simp add: card_Diff_singleton)

lemma card_insert: "finite A ==> card (insert x A) = Suc (card (A - {x}))"
  by (simp add: card_insert_if card_Suc_Diff1)

lemma card_insert_le: "finite A ==> card A <= card (insert x A)"
  by (simp add: card_insert_if)

lemma card_seteq: "finite B ==> (!!A. A <= B ==> card B <= card A ==> A = B)"
  apply (induct set: Finites)
   apply simp
  apply clarify
  apply (subgoal_tac "finite A & A - {x} <= F")
   prefer 2 apply (blast intro: finite_subset)
  apply atomize
  apply (drule_tac x = "A - {x}" in spec)
  apply (simp add: card_Diff_singleton_if split add: split_if_asm)
  apply (case_tac "card A")
   apply auto
  done

lemma psubset_card_mono: "finite B ==> A < B ==> card A < card B"
  apply (simp add: psubset_def linorder_not_le [symmetric])
  apply (blast dest: card_seteq)
  done

lemma card_mono: "finite B ==> A <= B ==> card A <= card B"
  apply (case_tac "A = B")
   apply simp
  apply (simp add: linorder_not_less [symmetric])
  apply (blast dest: card_seteq intro: order_less_imp_le)
  done

lemma card_Un_Int: "finite A ==> finite B
    ==> card A + card B = card (A Un B) + card (A Int B)"
  apply (induct set: Finites)
   apply simp
  apply (simp add: insert_absorb Int_insert_left)
  done

lemma card_Un_disjoint: "finite A ==> finite B
    ==> A Int B = {} ==> card (A Un B) = card A + card B"
  by (simp add: card_Un_Int)

lemma card_Diff_subset:
    "finite A ==> B <= A ==> card A - card B = card (A - B)"
  apply (subgoal_tac "(A - B) Un B = A")
   prefer 2 apply blast
  apply (rule add_right_cancel [THEN iffD1])
  apply (rule card_Un_disjoint [THEN subst])
     apply (erule_tac [4] ssubst)
     prefer 3 apply blast
    apply (simp_all add: add_commute not_less_iff_le
      add_diff_inverse card_mono finite_subset)
  done

lemma card_Diff1_less: "finite A ==> x: A ==> card (A - {x}) < card A"
  apply (rule Suc_less_SucD)
  apply (simp add: card_Suc_Diff1)
  done

lemma card_Diff2_less:
    "finite A ==> x: A ==> y: A ==> card (A - {x} - {y}) < card A"
  apply (case_tac "x = y")
   apply (simp add: card_Diff1_less)
  apply (rule less_trans)
   prefer 2 apply (auto intro!: card_Diff1_less)
  done

lemma card_Diff1_le: "finite A ==> card (A - {x}) <= card A"
  apply (case_tac "x : A")
   apply (simp_all add: card_Diff1_less less_imp_le)
  done

lemma card_psubset: "finite B ==> A \<subseteq> B ==> card A < card B ==> A < B"
  apply (erule psubsetI)
  apply blast
  done


subsubsection {* Cardinality of image *}

lemma card_image_le: "finite A ==> card (f ` A) <= card A"
  apply (induct set: Finites)
   apply simp
  apply (simp add: le_SucI finite_imageI card_insert_if)
  done

lemma card_image: "finite A ==> inj_on f A ==> card (f ` A) = card A"
  apply (induct set: Finites)
   apply simp_all
  apply atomize
  apply safe
   apply (unfold inj_on_def)
   apply blast
  apply (subst card_insert_disjoint)
    apply (erule finite_imageI)
   apply blast
  apply blast
  done

lemma endo_inj_surj: "finite A ==> f ` A \<subseteq> A ==> inj_on f A ==> f ` A = A"
  by (simp add: card_seteq card_image)


subsubsection {* Cardinality of the Powerset *}

lemma card_Pow: "finite A ==> card (Pow A) = Suc (Suc 0) ^ card A"  (* FIXME numeral 2 (!?) *)
  apply (induct set: Finites)
   apply (simp_all add: Pow_insert)
  apply (subst card_Un_disjoint)
     apply blast
    apply (blast intro: finite_imageI)
   apply blast
  apply (subgoal_tac "inj_on (insert x) (Pow F)")
   apply (simp add: card_image Pow_insert)
  apply (unfold inj_on_def)
  apply (blast elim!: equalityE)
  done

text {*
  \medskip Relates to equivalence classes.  Based on a theorem of
  F. Kammüller's.  The @{prop "finite C"} premise is redundant.
*}

lemma dvd_partition:
  "finite C ==> finite (Union C) ==>
    ALL c : C. k dvd card c ==>
    (ALL c1: C. ALL c2: C. c1 ~= c2 --> c1 Int c2 = {}) ==>
  k dvd card (Union C)"
  apply (induct set: Finites)
   apply simp_all
  apply clarify
  apply (subst card_Un_disjoint)
  apply (auto simp add: dvd_add disjoint_eq_subset_Compl)
  done


subsection {* A fold functional for finite sets *}

text {*
  For @{text n} non-negative we have @{text "fold f e {x1, ..., xn} =
  f x1 (... (f xn e))"} where @{text f} is at least left-commutative.
*}

consts
  foldSet :: "('b => 'a => 'a) => 'a => ('b set \<times> 'a) set"

inductive "foldSet f e"
  intros
    emptyI [intro]: "({}, e) : foldSet f e"
    insertI [intro]: "x \<notin> A ==> (A, y) : foldSet f e ==> (insert x A, f x y) : foldSet f e"

inductive_cases empty_foldSetE [elim!]: "({}, x) : foldSet f e"

constdefs
  fold :: "('b => 'a => 'a) => 'a => 'b set => 'a"
  "fold f e A == THE x. (A, x) : foldSet f e"

lemma Diff1_foldSet: "(A - {x}, y) : foldSet f e ==> x: A ==> (A, f x y) : foldSet f e"
  apply (erule insert_Diff [THEN subst], rule foldSet.intros)
   apply auto
  done

lemma foldSet_imp_finite [simp]: "(A, x) : foldSet f e ==> finite A"
  by (induct set: foldSet) auto

lemma finite_imp_foldSet: "finite A ==> EX x. (A, x) : foldSet f e"
  by (induct set: Finites) auto


subsubsection {* Left-commutative operations *}

locale LC =
  fixes f :: "'b => 'a => 'a"    (infixl "\<cdot>" 70)
  assumes left_commute: "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"

lemma (in LC) foldSet_determ_aux:
  "ALL A x. card A < n --> (A, x) : foldSet f e -->
    (ALL y. (A, y) : foldSet f e --> y = x)"
  apply (induct n)
   apply (auto simp add: less_Suc_eq)
  apply (erule foldSet.cases)
   apply blast
  apply (erule foldSet.cases)
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
  apply (rule_tac A1 = "Aa - {xb}" and f1 = f in finite_imp_foldSet [THEN exE])
  apply (blast intro: foldSet_imp_finite finite_Diff)
  apply (frule (1) Diff1_foldSet)
  apply (subgoal_tac "ya = f xb x")
   prefer 2 apply (blast del: equalityCE)
  apply (subgoal_tac "(Ab - {xa}, x) : foldSet f e")
   prefer 2 apply simp
  apply (subgoal_tac "yb = f xa x")
   prefer 2 apply (blast del: equalityCE dest: Diff1_foldSet)
  apply (simp (no_asm_simp) add: left_commute)
  done

lemma (in LC) foldSet_determ: "(A, x) : foldSet f e ==> (A, y) : foldSet f e ==> y = x"
  by (blast intro: foldSet_determ_aux [rule_format])

lemma (in LC) fold_equality: "(A, y) : foldSet f e ==> fold f e A = y"
  by (unfold fold_def) (blast intro: foldSet_determ)

lemma fold_empty [simp]: "fold f e {} = e"
  by (unfold fold_def) blast

lemma (in LC) fold_insert_aux: "x \<notin> A ==>
    ((insert x A, v) : foldSet f e) =
    (EX y. (A, y) : foldSet f e & v = f x y)"
  apply auto
  apply (rule_tac A1 = A and f1 = f in finite_imp_foldSet [THEN exE])
   apply (fastsimp dest: foldSet_imp_finite)
  apply (blast intro: foldSet_determ)
  done

lemma (in LC) fold_insert:
    "finite A ==> x \<notin> A ==> fold f e (insert x A) = f x (fold f e A)"
  apply (unfold fold_def)
  apply (simp add: fold_insert_aux)
  apply (rule the_equality)
  apply (auto intro: finite_imp_foldSet
    cong add: conj_cong simp add: fold_def [symmetric] fold_equality)
  done

lemma (in LC) fold_commute: "finite A ==> (!!e. f x (fold f e A) = fold f (f x e) A)"
  apply (induct set: Finites)
   apply simp
  apply (simp add: left_commute fold_insert)
  done

lemma (in LC) fold_nest_Un_Int:
  "finite A ==> finite B
    ==> fold f (fold f e B) A = fold f (fold f e (A Int B)) (A Un B)"
  apply (induct set: Finites)
   apply simp
  apply (simp add: fold_insert fold_commute Int_insert_left insert_absorb)
  done

lemma (in LC) fold_nest_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {}
    ==> fold f e (A Un B) = fold f (fold f e B) A"
  by (simp add: fold_nest_Un_Int)

declare foldSet_imp_finite [simp del]
    empty_foldSetE [rule del]  foldSet.intros [rule del]
  -- {* Delete rules to do with @{text foldSet} relation. *}



subsubsection {* Commutative monoids *}

text {*
  We enter a more restrictive context, with @{text "f :: 'a => 'a => 'a"}
  instead of @{text "'b => 'a => 'a"}.
*}

locale ACe =
  fixes f :: "'a => 'a => 'a"    (infixl "\<cdot>" 70)
    and e :: 'a
  assumes ident [simp]: "x \<cdot> e = x"
    and commute: "x \<cdot> y = y \<cdot> x"
    and assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

lemma (in ACe) left_commute: "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp only: commute)
  also have "... = y \<cdot> (z \<cdot> x)" by (simp only: assoc)
  also have "z \<cdot> x = x \<cdot> z" by (simp only: commute)
  finally show ?thesis .
qed

lemmas (in ACe) AC = assoc commute left_commute

lemma (in ACe) left_ident [simp]: "e \<cdot> x = x"
proof -
  have "x \<cdot> e = x" by (rule ident)
  thus ?thesis by (subst commute)
qed

lemma (in ACe) fold_Un_Int:
  "finite A ==> finite B ==>
    fold f e A \<cdot> fold f e B = fold f e (A Un B) \<cdot> fold f e (A Int B)"
  apply (induct set: Finites)
   apply simp
  apply (simp add: AC LC.fold_insert insert_absorb Int_insert_left)
  done

lemma (in ACe) fold_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {} ==>
    fold f e (A Un B) = fold f e A \<cdot> fold f e B"
  by (simp add: fold_Un_Int)

lemma (in ACe) fold_Un_disjoint2:
  "finite A ==> finite B ==> A Int B = {} ==>
    fold (f o g) e (A Un B) = fold (f o g) e A \<cdot> fold (f o g) e B"
proof -
  assume b: "finite B"
  assume "finite A"
  thus "A Int B = {} ==>
    fold (f o g) e (A Un B) = fold (f o g) e A \<cdot> fold (f o g) e B"
  proof induct
    case empty
    thus ?case by simp
  next
    case (insert F x)
    have "fold (f \<circ> g) e (insert x F \<union> B) = fold (f \<circ> g) e (insert x (F \<union> B))"
      by simp
    also have "... = (f \<circ> g) x (fold (f \<circ> g) e (F \<union> B))"
      by (rule LC.fold_insert) (insert b insert, auto simp add: left_commute)  (* FIXME import of fold_insert (!?) *)
    also from insert have "fold (f \<circ> g) e (F \<union> B) =
      fold (f \<circ> g) e F \<cdot> fold (f \<circ> g) e B" by blast
    also have "(f \<circ> g) x ... = (f \<circ> g) x (fold (f \<circ> g) e F) \<cdot> fold (f \<circ> g) e B"
      by (simp add: AC)
    also have "(f \<circ> g) x (fold (f \<circ> g) e F) = fold (f \<circ> g) e (insert x F)"
      by (rule LC.fold_insert [symmetric]) (insert b insert, auto simp add: left_commute)
    finally show ?case .
  qed
qed


subsection {* Generalized summation over a set *}

constdefs
  setsum :: "('a => 'b) => 'a set => 'b::plus_ac0"
  "setsum f A == if finite A then fold (op + o f) 0 A else 0"

syntax
  "_setsum" :: "idt => 'a set => 'b => 'b::plus_ac0"    ("\<Sum>_:_. _" [0, 51, 10] 10)
syntax (xsymbols)
  "_setsum" :: "idt => 'a set => 'b => 'b::plus_ac0"    ("\<Sum>_\<in>_. _" [0, 51, 10] 10)
translations
  "\<Sum>i:A. b" == "setsum (%i. b) A"  -- {* Beware of argument permutation! *}


lemma setsum_empty [simp]: "setsum f {} = 0"
  by (simp add: setsum_def)

lemma setsum_insert [simp]:
    "finite F ==> a \<notin> F ==> setsum f (insert a F) = f a + setsum f F"
  by (simp add: setsum_def LC.fold_insert plus_ac0_left_commute)

lemma setsum_0: "setsum (\<lambda>i. 0) A = 0"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule finite_induct)
   apply auto
  done

lemma setsum_eq_0_iff [simp]:
    "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))"
  by (induct set: Finites) auto

lemma setsum_SucD: "setsum f A = Suc n ==> EX a:A. 0 < f a"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule rev_mp)
  apply (erule finite_induct)
   apply auto
  done

lemma card_eq_setsum: "finite A ==> card A = setsum (\<lambda>x. 1) A"
  -- {* Could allow many @{text "card"} proofs to be simplified. *}
  by (induct set: Finites) auto

lemma setsum_Un_Int: "finite A ==> finite B
    ==> setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
  apply (induct set: Finites)
   apply simp
  apply (simp add: plus_ac0 Int_insert_left insert_absorb)
  done

lemma setsum_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setsum g (A Un B) = setsum g A + setsum g B"
  apply (subst setsum_Un_Int [symmetric])
    apply auto
  done

lemma setsum_UN_disjoint: (fixes f :: "'a => 'b::plus_ac0")
  "finite I ==> (ALL i:I. finite (A i)) ==>
      (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
    setsum f (UNION I A) = setsum (\<lambda>i. setsum f (A i)) I"
  apply (induct set: Finites)
   apply simp
  apply atomize
  apply (subgoal_tac "ALL i:F. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x Int UNION F A = {}")
   prefer 2 apply blast
  apply (simp add: setsum_Un_disjoint)
  done

lemma setsum_addf: "setsum (\<lambda>x. f x + g x) A = (setsum f A + setsum g A)"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule finite_induct)
   apply auto
  apply (simp add: plus_ac0)
  done

lemma setsum_Un: "finite A ==> finite B ==>
    (setsum f (A Un B) :: nat) = setsum f A + setsum f B - setsum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
  apply (subst setsum_Un_Int [symmetric])
    apply auto
  done

lemma setsum_diff1: "(setsum f (A - {a}) :: nat) =
    (if a:A then setsum f A - f a else setsum f A)"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (drule_tac a = a in mk_disjoint_insert)
  apply auto
  done

lemma setsum_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setsum f A = setsum g B"
  apply (case_tac "finite B")
   prefer 2 apply (simp add: setsum_def)
  apply simp
  apply (subgoal_tac "ALL C. C <= B --> (ALL x:C. f x = g x) --> setsum f C = setsum g C")
   apply simp
  apply (erule finite_induct)
  apply simp
  apply (simp add: subset_insert_iff)
  apply clarify
  apply (subgoal_tac "finite C")
   prefer 2 apply (blast dest: finite_subset [COMP swap_prems_rl])
  apply (subgoal_tac "C = insert x (C - {x})")
   prefer 2 apply blast
  apply (erule ssubst)
  apply (drule spec)
  apply (erule (1) notE impE)
  apply (simp add: Ball_def)
  done


text {*
  \medskip Basic theorem about @{text "choose"}.  By Florian
  Kammüller, tidied by LCP.
*}

lemma card_s_0_eq_empty:
    "finite A ==> card {B. B \<subseteq> A & card B = 0} = 1"
  apply (simp cong add: conj_cong add: finite_subset [THEN card_0_eq])
  apply (simp cong add: rev_conj_cong)
  done

lemma choose_deconstruct: "finite M ==> x \<notin> M
  ==> {s. s <= insert x M & card(s) = Suc k}
       = {s. s <= M & card(s) = Suc k} Un
         {s. EX t. t <= M & card(t) = k & s = insert x t}"
  apply safe
   apply (auto intro: finite_subset [THEN card_insert_disjoint])
  apply (drule_tac x = "xa - {x}" in spec)
  apply (subgoal_tac "x ~: xa")
   apply auto
  apply (erule rev_mp, subst card_Diff_singleton)
  apply (auto intro: finite_subset)
  done

lemma card_inj_on_le:
    "finite A ==> finite B ==> f ` A \<subseteq> B ==> inj_on f A ==> card A <= card B"
  by (auto intro: card_mono simp add: card_image [symmetric])

lemma card_bij_eq: "finite A ==> finite B ==>
  f ` A \<subseteq> B ==> inj_on f A ==> g ` B \<subseteq> A ==> inj_on g B ==> card A = card B"
  by (auto intro: le_anti_sym card_inj_on_le)

lemma constr_bij: "finite A ==> x \<notin> A ==>
  card {B. EX C. C <= A & card(C) = k & B = insert x C} =
    card {B. B <= A & card(B) = k}"
  apply (rule_tac f = "%s. s - {x}" and g = "insert x" in card_bij_eq)
       apply (rule_tac B = "Pow (insert x A) " in finite_subset)
        apply (rule_tac [3] B = "Pow (A) " in finite_subset)
         apply fast+
     txt {* arity *}
     apply (auto elim!: equalityE simp add: inj_on_def)
  apply (subst Diff_insert0)
  apply auto
  done

text {*
  Main theorem: combinatorial statement about number of subsets of a set.
*}

lemma n_sub_lemma:
  "!!A. finite A ==> card {B. B <= A & card B = k} = (card A choose k)"
  apply (induct k)
   apply (simp add: card_s_0_eq_empty)
  apply atomize
  apply (rotate_tac -1, erule finite_induct)
   apply (simp_all (no_asm_simp) cong add: conj_cong add: card_s_0_eq_empty choose_deconstruct)
  apply (subst card_Un_disjoint)
     prefer 4 apply (force simp add: constr_bij)
    prefer 3 apply force
   prefer 2 apply (blast intro: finite_Pow_iff [THEN iffD2]
     finite_subset [of _ "Pow (insert x F)", standard])
  apply (blast intro: finite_Pow_iff [THEN iffD2, THEN [2] finite_subset])
  done

theorem n_subsets: "finite A ==> card {B. B <= A & card(B) = k} = (card A choose k)"
  by (simp add: n_sub_lemma)

end
