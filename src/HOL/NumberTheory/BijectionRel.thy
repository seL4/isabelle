(*  Title:      HOL/NumberTheory/BijectionRel.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Bijections between sets *}

theory BijectionRel = Main:

text {*
  Inductive definitions of bijections between two different sets and
  between the same set.  Theorem for relating the two definitions.

  \bigskip
*}

consts
  bijR :: "('a => 'b => bool) => ('a set * 'b set) set"

inductive "bijR P"
  intros
  empty [simp]: "({}, {}) \<in> bijR P"
  insert: "P a b ==> a \<notin> A ==> b \<notin> B ==> (A, B) \<in> bijR P
    ==> (insert a A, insert b B) \<in> bijR P"

text {*
  Add extra condition to @{term insert}: @{term "\<forall>b \<in> B. \<not> P a b"}
  (and similar for @{term A}).
*}

constdefs
  bijP :: "('a => 'a => bool) => 'a set => bool"
  "bijP P F == \<forall>a b. a \<in> F \<and> P a b --> b \<in> F"

  uniqP :: "('a => 'a => bool) => bool"
  "uniqP P == \<forall>a b c d. P a b \<and> P c d --> (a = c) = (b = d)"

  symP :: "('a => 'a => bool) => bool"
  "symP P == \<forall>a b. P a b = P b a"

consts
  bijER :: "('a => 'a => bool) => 'a set set"

inductive "bijER P"
  intros
  empty [simp]: "{} \<in> bijER P"
  insert1: "P a a ==> a \<notin> A ==> A \<in> bijER P ==> insert a A \<in> bijER P"
  insert2: "P a b ==> a \<noteq> b ==> a \<notin> A ==> b \<notin> A ==> A \<in> bijER P
    ==> insert a (insert b A) \<in> bijER P"


text {* \medskip @{term bijR} *}

lemma fin_bijRl: "(A, B) \<in> bijR P ==> finite A"
  apply (erule bijR.induct)
  apply auto
  done

lemma fin_bijRr: "(A, B) \<in> bijR P ==> finite B"
  apply (erule bijR.induct)
  apply auto
  done

lemma aux_induct:
  "finite F ==> F \<subseteq> A ==> P {} ==>
    (!!F a. F \<subseteq> A ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F))
  ==> P F"
proof -
  case antecedent
  assume major: "finite F"
    and subs: "F \<subseteq> A"
  show ?thesis
    apply (rule subs [THEN rev_mp])
    apply (rule major [THEN finite_induct])
     apply (blast intro: antecedent)+
    done
qed

lemma aux: "A \<subseteq> B ==> a \<notin> A ==> a \<in> B ==> inj_on f B ==> f a \<notin> f ` A"
  apply (unfold inj_on_def)
  apply auto
  done

lemma aux:
  "\<forall>a. a \<in> A --> P a (f a) ==> inj_on f A ==> finite A ==> F <= A
    ==> (F, f ` F) \<in> bijR P"
  apply (rule_tac F = F and A = A in aux_induct)
     apply (rule finite_subset)
      apply auto
  apply (rule bijR.insert)
     apply (rule_tac [3] aux)
        apply auto
  done

lemma inj_func_bijR:
  "\<forall>a. a \<in> A --> P a (f a) ==> inj_on f A ==> finite A
    ==> (A, f ` A) \<in> bijR P"
  apply (rule aux)
     apply auto
  done


text {* \medskip @{term bijER} *}

lemma fin_bijER: "A \<in> bijER P ==> finite A"
  apply (erule bijER.induct)
    apply auto
  done

lemma aux1:
  "a \<notin> A ==> a \<notin> B ==> F \<subseteq> insert a A ==> F \<subseteq> insert a B ==> a \<in> F
    ==> \<exists>C. F = insert a C \<and> a \<notin> C \<and> C <= A \<and> C <= B"
  apply (rule_tac x = "F - {a}" in exI)
  apply auto
  done

lemma aux2: "a \<noteq> b ==> a \<notin> A ==> b \<notin> B ==> a \<in> F ==> b \<in> F
    ==> F \<subseteq> insert a A ==> F \<subseteq> insert b B
    ==> \<exists>C. F = insert a (insert b C) \<and> a \<notin> C \<and> b \<notin> C \<and> C \<subseteq> A \<and> C \<subseteq> B"
  apply (rule_tac x = "F - {a, b}" in exI)
  apply auto
  done

lemma aux_uniq: "uniqP P ==> P a b ==> P c d ==> (a = c) = (b = d)"
  apply (unfold uniqP_def)
  apply auto
  done

lemma aux_sym: "symP P ==> P a b = P b a"
  apply (unfold symP_def)
  apply auto
  done

lemma aux_in1:
    "uniqP P ==> b \<notin> C ==> P b b ==> bijP P (insert b C) ==> bijP P C"
  apply (unfold bijP_def)
  apply auto
  apply (subgoal_tac "b \<noteq> a")
   prefer 2
   apply clarify
  apply (simp add: aux_uniq)
  apply auto
  done

lemma aux_in2:
  "symP P ==> uniqP P ==> a \<notin> C ==> b \<notin> C ==> a \<noteq> b ==> P a b
    ==> bijP P (insert a (insert b C)) ==> bijP P C"
  apply (unfold bijP_def)
  apply auto
  apply (subgoal_tac "aa \<noteq> a")
   prefer 2
   apply clarify
  apply (subgoal_tac "aa \<noteq> b")
   prefer 2
   apply clarify
  apply (simp add: aux_uniq)
  apply (subgoal_tac "ba \<noteq> a")
   apply auto
  apply (subgoal_tac "P a aa")
   prefer 2
   apply (simp add: aux_sym)
  apply (subgoal_tac "b = aa")
   apply (rule_tac [2] iffD1)
    apply (rule_tac [2] a = a and c = a and P = P in aux_uniq)
      apply auto
  done

lemma aux: "\<forall>a b. Q a \<and> P a b --> R b ==> P a b ==> Q a ==> R b"
  apply auto
  done

lemma aux_bij: "bijP P F ==> symP P ==> P a b ==> (a \<in> F) = (b \<in> F)"
  apply (unfold bijP_def)
  apply (rule iffI)
  apply (erule_tac [!] aux)
      apply simp_all
  apply (rule iffD2)
   apply (rule_tac P = P in aux_sym)
   apply simp_all
  done


lemma aux_bijRER:
  "(A, B) \<in> bijR P ==> uniqP P ==> symP P
    ==> \<forall>F. bijP P F \<and> F \<subseteq> A \<and> F \<subseteq> B --> F \<in> bijER P"
  apply (erule bijR.induct)
   apply simp
  apply (case_tac "a = b")
   apply clarify
   apply (case_tac "b \<in> F")
    prefer 2
    apply (rotate_tac -1)
    apply (simp add: subset_insert)
   apply (cut_tac F = F and a = b and A = A and B = B in aux1)
        prefer 6
        apply clarify
        apply (rule bijER.insert1)
          apply simp_all
   apply (subgoal_tac "bijP P C")
    apply simp
   apply (rule aux_in1)
      apply simp_all
  apply clarify
  apply (case_tac "a \<in> F")
   apply (case_tac [!] "b \<in> F")
     apply (rotate_tac [2-4] -2)
     apply (cut_tac F = F and a = a and b = b and A = A and B = B
       in aux2)
            apply (simp_all add: subset_insert)
    apply clarify
    apply (rule bijER.insert2)
        apply simp_all
    apply (subgoal_tac "bijP P C")
     apply simp
    apply (rule aux_in2)
          apply simp_all
   apply (subgoal_tac "b \<in> F")
    apply (rule_tac [2] iffD1)
     apply (rule_tac [2] a = a and F = F and P = P in aux_bij)
       apply (simp_all (no_asm_simp))
   apply (subgoal_tac [2] "a \<in> F")
    apply (rule_tac [3] iffD2)
     apply (rule_tac [3] b = b and F = F and P = P in aux_bij)
       apply auto
  done

lemma bijR_bijER:
  "(A, A) \<in> bijR P ==>
    bijP P A ==> uniqP P ==> symP P ==> A \<in> bijER P"
  apply (cut_tac A = A and B = A and P = P in aux_bijRER)
     apply auto
  done

end
