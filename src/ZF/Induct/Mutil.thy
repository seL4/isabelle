(*  Title:      ZF/Induct/Mutil.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* The Mutilated Chess Board Problem, formalized inductively *}

theory Mutil = Main:

text {*
  Originator is Max Black, according to J A Robinson.  Popularized as
  the Mutilated Checkerboard Problem by J McCarthy.
*}

consts
  domino :: i
  tiling :: "i => i"

inductive
  domains "domino" \<subseteq> "Pow(nat \<times> nat)"
  intros
    horiz: "[| i \<in> nat;  j \<in> nat |] ==> {<i,j>, <i,succ(j)>} \<in> domino"
    vertl: "[| i \<in> nat;  j \<in> nat |] ==> {<i,j>, <succ(i),j>} \<in> domino"
  type_intros empty_subsetI cons_subsetI PowI SigmaI nat_succI

inductive
  domains "tiling(A)" \<subseteq> "Pow(Union(A))"
  intros
    empty: "0 \<in> tiling(A)"
    Un: "[| a \<in> A;  t \<in> tiling(A);  a Int t = 0 |] ==> a Un t \<in> tiling(A)"
  type_intros empty_subsetI Union_upper Un_least PowI
  type_elims PowD [elim_format]

constdefs
  evnodd :: "[i, i] => i"
  "evnodd(A,b) == {z \<in> A. \<exists>i j. z = <i,j> \<and> (i #+ j) mod 2 = b}"


subsection {* Basic properties of evnodd *}

lemma evnodd_iff: "<i,j>: evnodd(A,b) <-> <i,j>: A & (i#+j) mod 2 = b"
  by (unfold evnodd_def) blast

lemma evnodd_subset: "evnodd(A, b) \<subseteq> A"
  by (unfold evnodd_def) blast

lemma Finite_evnodd: "Finite(X) ==> Finite(evnodd(X,b))"
  by (rule lepoll_Finite, rule subset_imp_lepoll, rule evnodd_subset)

lemma evnodd_Un: "evnodd(A Un B, b) = evnodd(A,b) Un evnodd(B,b)"
  by (simp add: evnodd_def Collect_Un)

lemma evnodd_Diff: "evnodd(A - B, b) = evnodd(A,b) - evnodd(B,b)"
  by (simp add: evnodd_def Collect_Diff)

lemma evnodd_cons [simp]:
  "evnodd(cons(<i,j>,C), b) =
    (if (i#+j) mod 2 = b then cons(<i,j>, evnodd(C,b)) else evnodd(C,b))"
  by (simp add: evnodd_def Collect_cons)

lemma evnodd_0 [simp]: "evnodd(0, b) = 0"
  by (simp add: evnodd_def)


subsection {* Dominoes *}

lemma domino_Finite: "d \<in> domino ==> Finite(d)"
  by (blast intro!: Finite_cons Finite_0 elim: domino.cases)

lemma domino_singleton:
    "[| d \<in> domino; b<2 |] ==> \<exists>i' j'. evnodd(d,b) = {<i',j'>}"
  apply (erule domino.cases)
   apply (rule_tac [2] k1 = "i#+j" in mod2_cases [THEN disjE])
     apply (rule_tac k1 = "i#+j" in mod2_cases [THEN disjE])
       apply (rule add_type | assumption)+
      (*Four similar cases: case (i#+j) mod 2 = b, 2#-b, ...*)
      apply (auto simp add: mod_succ succ_neq_self dest: ltD)
  done


subsection {* Tilings *}

text {* The union of two disjoint tilings is a tiling *}

lemma tiling_UnI:
    "t \<in> tiling(A) ==> u \<in> tiling(A) ==> t Int u = 0 ==> t Un u \<in> tiling(A)"
  apply (induct set: tiling)
   apply (simp add: tiling.intros)
  apply (simp add: Un_assoc subset_empty_iff [THEN iff_sym])
  apply (blast intro: tiling.intros)
  done

lemma tiling_domino_Finite: "t \<in> tiling(domino) ==> Finite(t)"
  apply (induct rule: tiling.induct)
   apply (rule Finite_0)
  apply (blast intro!: Finite_Un intro: domino_Finite)
  done

lemma tiling_domino_0_1: "t \<in> tiling(domino) ==> |evnodd(t,0)| = |evnodd(t,1)|"
  apply (induct rule: tiling.induct)
   apply (simp add: evnodd_def)
  apply (rule_tac b1 = 0 in domino_singleton [THEN exE])
    prefer 2
    apply simp
   apply assumption
  apply (rule_tac b1 = 1 in domino_singleton [THEN exE])
    prefer 2
    apply simp
   apply assumption
  apply safe
  apply (subgoal_tac "\<forall>p b. p \<in> evnodd (a,b) --> p\<notin>evnodd (t,b)")
   apply (simp add: evnodd_Un Un_cons tiling_domino_Finite
     evnodd_subset [THEN subset_Finite] Finite_imp_cardinal_cons)
  apply (blast dest!: evnodd_subset [THEN subsetD] elim: equalityE)
  done

lemma dominoes_tile_row:
    "[| i \<in> nat;  n \<in> nat |] ==> {i} * (n #+ n) \<in> tiling(domino)"
  apply (induct_tac n)
   apply (simp add: tiling.intros)
  apply (simp add: Un_assoc [symmetric] Sigma_succ2)
  apply (rule tiling.intros)
    prefer 2 apply assumption
   apply (rename_tac n')
   apply (subgoal_tac (*seems the easiest way of turning one to the other*)
     "{i}*{succ (n'#+n') } Un {i}*{n'#+n'} =
       {<i,n'#+n'>, <i,succ (n'#+n') >}")
    prefer 2 apply blast
  apply (simp add: domino.horiz)
  apply (blast elim: mem_irrefl mem_asym)
  done

lemma dominoes_tile_matrix:
    "[| m \<in> nat;  n \<in> nat |] ==> m * (n #+ n) \<in> tiling(domino)"
  apply (induct_tac m)
   apply (simp add: tiling.intros)
  apply (simp add: Sigma_succ1)
  apply (blast intro: tiling_UnI dominoes_tile_row elim: mem_irrefl)
  done

lemma eq_lt_E: "[| x=y; x<y |] ==> P"
  by auto

theorem mutil_not_tiling: "[| m \<in> nat;  n \<in> nat;
         t = (succ(m)#+succ(m))*(succ(n)#+succ(n));
         t' = t - {<0,0>} - {<succ(m#+m), succ(n#+n)>} |]
      ==> t' \<notin> tiling(domino)"
  apply (rule notI)
  apply (drule tiling_domino_0_1)
  apply (erule_tac x = "|?A|" in eq_lt_E)
  apply (subgoal_tac "t \<in> tiling (domino)")
   prefer 2 (*Requires a small simpset that won't move the succ applications*)
   apply (simp only: nat_succI add_type dominoes_tile_matrix)
  apply (simp add: evnodd_Diff mod2_add_self mod2_succ_succ
    tiling_domino_0_1 [symmetric])
  apply (rule lt_trans)
   apply (rule Finite_imp_cardinal_Diff,
     simp add: tiling_domino_Finite Finite_evnodd Finite_Diff,
     simp add: evnodd_iff nat_0_le [THEN ltD] mod2_add_self)+
  done

end
