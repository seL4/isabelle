(*  Title:      HOL/Imperative_HOL/ex/SatChecker.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

header {* An efficient checker for proofs from a SAT solver *}

theory SatChecker
imports RBT_Impl Sorted_List "~~/src/HOL/Imperative_HOL/Imperative_HOL" 
begin

section{* General settings and functions for our representation of clauses *}

subsection{* Types for Literals, Clauses and ProofSteps *}
text {* We encode Literals as integers and Clauses as sorted Lists. *}

types ClauseId = nat
types Lit = int
types Clause = "Lit list"

text {* This resembles exactly to Isat's Proof Steps *}

types Resolvants = "ClauseId * (Lit * ClauseId) list"
datatype ProofStep =
  ProofDone bool
  | Root ClauseId Clause
  | Conflict ClauseId Resolvants
  | Delete ClauseId
  | Xstep ClauseId ClauseId

subsection{* Interpretation of Literals, Clauses, and an array of Clauses *} 
text {* Specific definitions for Literals as integers *}

definition compl :: "Lit \<Rightarrow> Lit"
where
  "compl a = -a"

definition interpLit :: "(nat \<Rightarrow> bool) \<Rightarrow> Lit \<Rightarrow> bool"
where
  "interpLit assgnmt lit = (if lit > 0 then assgnmt (nat lit) else (if (lit < 0) then \<not> (assgnmt (nat (- lit))) else undefined))"

lemma interpLit_compl[simp]:
  assumes lit_not_zero: "lit \<noteq> 0"
  shows "interpLit a (compl lit) = (\<not> interpLit a lit)"
unfolding interpLit_def compl_def using lit_not_zero by auto

lemma compl_compl_is_id[simp]:
  "compl (compl x) = x"
unfolding compl_def by simp

lemma compl_not_zero[simp]:
  "(compl x \<noteq> 0) = (x \<noteq> 0)"
unfolding compl_def by simp

lemma compl_exists: "\<exists>l'. l = compl l'"
unfolding compl_def by arith

text {* Specific definitions for Clauses as sorted lists *}

definition interpClause :: "(nat \<Rightarrow> bool) \<Rightarrow> Clause \<Rightarrow> bool"
where
  "interpClause assgnmt cl = (\<exists> l \<in> set cl. interpLit assgnmt l)" 

lemma interpClause_empty[simp]:
  "interpClause a [] = False" 
unfolding interpClause_def by simp

lemma interpClause_sort[simp]: "interpClause a (sort clause) = interpClause a clause"
unfolding interpClause_def
by simp

lemma interpClause_remdups[simp]: "interpClause a (remdups clause) = interpClause a clause"
unfolding interpClause_def
by simp

definition 
  "inconsistent cs = (\<forall>a.\<exists>c\<in>set cs. \<not> interpClause a c)"

lemma interpClause_resolvants':
  assumes lit_not_zero: "lit \<noteq> 0"
  assumes resolv_clauses: "lit \<in> cli" "compl lit \<in> clj"
  assumes interp: "\<exists>x \<in> cli. interpLit a x" "\<exists>x \<in> clj. interpLit a x"
  shows "\<exists>x \<in> (cli - {lit} \<union> (clj - {compl lit})). interpLit a x"
proof -
  from resolv_clauses interp have "(\<exists>l \<in> cli - {lit}. interpLit a l) \<or> interpLit a lit"
    "(\<exists>l \<in> clj - {compl lit}. interpLit a l) \<or> interpLit a (compl lit)" by auto
  with lit_not_zero show ?thesis by (fastsimp simp add: bex_Un)
qed

lemma interpClause_resolvants:
  assumes lit_not_zero: "lit \<noteq> 0"
  assumes sorted_and_distinct: "sorted cli" "distinct cli" "sorted clj" "distinct clj"
  assumes resolv_clauses: "lit \<in> set cli" "compl lit \<in> set clj"
  assumes interp: "interpClause a cli" "interpClause a clj"
  shows "interpClause a (merge (remove lit cli) (remove (compl lit) clj))"
proof -
  from lit_not_zero resolv_clauses interp sorted_and_distinct show ?thesis
    unfolding interpClause_def
    using interpClause_resolvants' by simp
qed

definition correctClause :: "Clause list \<Rightarrow> Clause \<Rightarrow> bool"
where
  "correctClause rootcls cl = (\<forall>a. (\<forall>rcl \<in> set rootcls. interpClause a rcl) \<longrightarrow> (interpClause a cl))"

lemma correctClause_resolvants:
  assumes lit_not_zero: "lit \<noteq> 0"
  assumes sorted_and_distinct: "sorted cli" "distinct cli" "sorted clj" "distinct clj"
  assumes resolv_clauses: "lit \<in> set cli" "compl lit \<in> set clj"
  assumes correct: "correctClause r cli" "correctClause r clj"
  shows "correctClause r (merge (remove lit cli) (remove (compl lit) clj))"
  using assms interpClause_resolvants unfolding correctClause_def by auto


lemma implies_empty_inconsistent: 
  "correctClause cs [] \<Longrightarrow> inconsistent cs"
unfolding inconsistent_def correctClause_def
by auto

text {* Specific definition for derived clauses in the Array *}

definition correctArray :: "Clause list \<Rightarrow> Clause option array \<Rightarrow> heap \<Rightarrow> bool"
where
  "correctArray rootcls a h =
  (\<forall>cl \<in> array_ran a h. correctClause rootcls cl \<and> sorted cl \<and> distinct cl)"

lemma correctArray_update:
  assumes "correctArray rcs a h"
  assumes "correctClause rcs c" "sorted c" "distinct c"
  shows "correctArray rcs a (Heap.upd a i (Some c) h)"
  using assms
  unfolding correctArray_def
  by (auto dest:array_ran_upd_array_Some)

lemma correctClause_mono:
  assumes "correctClause rcs c"
  assumes "set rcs \<subseteq> set rcs'"
  shows "correctClause rcs' c"
  using assms unfolding correctClause_def
  by auto


section{* Improved version of SatChecker *}

text{* This version just uses a single list traversal. *}

subsection{* Function definitions *}

fun res_mem :: "Lit \<Rightarrow> Clause \<Rightarrow> Clause Heap"
where
  "res_mem l [] = raise ''MiniSatChecked.res_thm: Cannot find literal''"
| "res_mem l (x#xs) = (if (x = l) then return xs else (do v \<leftarrow> res_mem l xs; return (x # v) done))"

fun resolve1 :: "Lit \<Rightarrow> Clause \<Rightarrow> Clause \<Rightarrow> Clause Heap"
where
  "resolve1 l (x#xs) (y#ys) =
  (if (x = l) then return (merge xs (y#ys))
  else (if (x < y) then (do v \<leftarrow> resolve1 l xs (y#ys); return (x # v) done)
  else (if (x > y) then (do v \<leftarrow> resolve1 l (x#xs) ys; return (y # v) done)
  else (do v \<leftarrow> resolve1 l xs ys; return (x # v) done))))"
| "resolve1 l [] ys = raise ''MiniSatChecked.res_thm: Cannot find literal''"
| "resolve1 l xs [] = res_mem l xs"

fun resolve2 :: "Lit \<Rightarrow> Clause \<Rightarrow> Clause \<Rightarrow> Clause Heap" 
where
  "resolve2 l (x#xs) (y#ys) =
  (if (y = l) then return (merge (x#xs) ys)
  else (if (x < y) then (do v \<leftarrow> resolve2 l xs (y#ys); return (x # v) done)
  else (if (x > y) then (do v \<leftarrow> resolve2 l (x#xs) ys; return (y # v) done) 
  else (do v \<leftarrow> resolve2 l xs ys; return (x # v) done))))"
  | "resolve2 l xs [] = raise ''MiniSatChecked.res_thm: Cannot find literal''"
  | "resolve2 l [] ys = res_mem l ys"

fun res_thm' :: "Lit \<Rightarrow> Clause \<Rightarrow> Clause \<Rightarrow> Clause Heap"
where
  "res_thm' l (x#xs) (y#ys) = 
  (if (x = l \<or> x = compl l) then resolve2 (compl x) xs (y#ys)
  else (if (y = l \<or> y = compl l) then resolve1 (compl y) (x#xs) ys
  else (if (x < y) then (res_thm' l xs (y#ys)) \<guillemotright>= (\<lambda>v. return (x # v))
  else (if (x > y) then (res_thm' l (x#xs) ys) \<guillemotright>= (\<lambda>v. return (y # v))
  else (res_thm' l xs ys) \<guillemotright>= (\<lambda>v. return (x # v))))))"
| "res_thm' l [] ys = raise (''MiniSatChecked.res_thm: Cannot find literal'')"
| "res_thm' l xs [] = raise (''MiniSatChecked.res_thm: Cannot find literal'')"

declare res_mem.simps [simp del] resolve1.simps [simp del] resolve2.simps [simp del] res_thm'.simps [simp del]

subsection {* Proofs about these functions *}

lemma res_mem:
assumes "crel (res_mem l xs) h h' r"
  shows "l \<in> set xs \<and> r = remove1 l xs"
using assms
proof (induct xs arbitrary: r)
  case Nil
  thus ?case unfolding res_mem.simps by (auto elim: crel_raise)
next
  case (Cons x xs')
  thus ?case
    unfolding res_mem.simps
    by (elim crel_raise crel_return crel_if crelE) auto
qed

lemma resolve1_Inv:
assumes "crel (resolve1 l xs ys) h h' r"
  shows "l \<in> set xs \<and> r = merge (remove1 l xs) ys"
using assms
proof (induct xs ys arbitrary: r rule: resolve1.induct)
  case (1 l x xs y ys r)
  thus ?case
    unfolding resolve1.simps
    by (elim crelE crel_if crel_return) auto
next
  case (2 l ys r)
  thus ?case
    unfolding resolve1.simps
    by (elim crel_raise) auto
next
  case (3 l v va r)
  thus ?case
    unfolding resolve1.simps
    by (fastsimp dest!: res_mem)
qed

lemma resolve2_Inv: 
  assumes "crel (resolve2 l xs ys) h h' r"
  shows "l \<in> set ys \<and> r = merge xs (remove1 l ys)"
using assms
proof (induct xs ys arbitrary: r rule: resolve2.induct)
  case (1 l x xs y ys r)
  thus ?case
    unfolding resolve2.simps
    by (elim crelE crel_if crel_return) auto
next
  case (2 l ys r)
  thus ?case
    unfolding resolve2.simps
    by (elim crel_raise) auto
next
  case (3 l v va r)
  thus ?case
    unfolding resolve2.simps
    by (fastsimp dest!: res_mem simp add: merge_Nil)
qed

lemma res_thm'_Inv:
assumes "crel (res_thm' l xs ys) h h' r"
shows "\<exists>l'. (l' \<in> set xs \<and> compl l' \<in> set ys \<and> (l' = compl l \<or> l' = l)) \<and> r = merge (remove1 l' xs) (remove1 (compl l') ys)"
using assms
proof (induct xs ys arbitrary: r rule: res_thm'.induct)
case (1 l x xs y ys r)
(* There are five cases for res_thm: We will consider them one after another: *) 
  {
    assume cond: "x = l \<or> x = compl l"
    assume resolve2: "crel (resolve2 (compl x) xs (y # ys)) h h' r"   
    from resolve2_Inv [OF resolve2] cond have ?case
      apply -
      by (rule exI[of _ "x"]) fastsimp
  } moreover
  {
    assume cond: "\<not> (x = l \<or> x = compl l)" "y = l \<or> y = compl l" 
    assume resolve1: "crel (resolve1 (compl y) (x # xs) ys) h h' r"
    from resolve1_Inv [OF resolve1] cond have ?case
      apply -
      by (rule exI[of _ "compl y"]) fastsimp
  } moreover
  {
    fix r'
    assume cond: "\<not> (x = l \<or> x = compl l)" "\<not> (y = l \<or> y = compl l)" "x < y"
    assume res_thm: "crel (res_thm' l xs (y # ys)) h h' r'"
    assume return: "r = x # r'"
    from "1.hyps"(1) [OF cond res_thm] cond return have ?case by auto
  } moreover
  {
    fix r'
    assume cond: "\<not> (x = l \<or> x = compl l)" "\<not> (y = l \<or> y = compl l)" "\<not> x < y" "y < x"
    assume res_thm: "crel (res_thm' l (x # xs) ys) h h' r'"
    assume return: "r = y # r'"
    from "1.hyps"(2) [OF cond res_thm] cond return have ?case by auto
  } moreover
  {
    fix r'
    assume cond: "\<not> (x = l \<or> x = compl l)" "\<not> (y = l \<or> y = compl l)" "\<not> x < y" "\<not> y < x"
    assume res_thm: "crel (res_thm' l xs ys) h h' r'"
    assume return: "r = x # r'"
    from "1.hyps"(3) [OF cond res_thm] cond return have ?case by auto
  } moreover
  note "1.prems"
  ultimately show ?case
    unfolding res_thm'.simps
    apply (elim crelE crel_if crel_return)
    apply simp
    apply simp
    apply simp
    apply simp
    apply fastsimp
    done
next
  case (2 l ys r)
  thus ?case
    unfolding res_thm'.simps
    by (elim crel_raise) auto
next
  case (3 l v va r)
  thus ?case
    unfolding res_thm'.simps
    by (elim crel_raise) auto
qed

lemma res_mem_no_heap:
assumes "crel (res_mem l xs) h h' r"
  shows "h = h'"
using assms
apply (induct xs arbitrary: r)
unfolding res_mem.simps
apply (elim crel_raise)
apply auto
apply (elim crel_if crelE crel_raise crel_return)
apply auto
done

lemma resolve1_no_heap:
assumes "crel (resolve1 l xs ys) h h' r"
  shows "h = h'"
using assms
apply (induct xs ys arbitrary: r rule: resolve1.induct)
unfolding resolve1.simps
apply (elim crelE crel_if crel_return crel_raise)
apply (auto simp add: res_mem_no_heap)
by (elim crel_raise) auto

lemma resolve2_no_heap:
assumes "crel (resolve2 l xs ys) h h' r"
  shows "h = h'"
using assms
apply (induct xs ys arbitrary: r rule: resolve2.induct)
unfolding resolve2.simps
apply (elim crelE crel_if crel_return crel_raise)
apply (auto simp add: res_mem_no_heap)
by (elim crel_raise) auto


lemma res_thm'_no_heap:
  assumes "crel (res_thm' l xs ys) h h' r"
  shows "h = h'"
  using assms
proof (induct xs ys arbitrary: r rule: res_thm'.induct)
  case (1 l x xs y ys r)
  thus ?thesis
    unfolding res_thm'.simps
    by (elim crelE crel_if crel_return)
  (auto simp add: resolve1_no_heap resolve2_no_heap)
next
  case (2 l ys r)
  thus ?case
    unfolding res_thm'.simps
    by (elim crel_raise) auto
next
  case (3 l v va r)
  thus ?case
    unfolding res_thm'.simps
    by (elim crel_raise) auto
qed


lemma res_thm'_Inv2:
  assumes res_thm: "crel (res_thm' l xs ys) h h' rcl"
  assumes l_not_null: "l \<noteq> 0"
  assumes ys: "correctClause r ys \<and> sorted ys \<and> distinct ys"
  assumes xs: "correctClause r xs \<and> sorted xs \<and> distinct xs"
  shows "correctClause r rcl \<and> sorted rcl \<and> distinct rcl"
proof -
  from res_thm'_Inv [OF res_thm] xs ys l_not_null show ?thesis
    apply (auto simp add: sorted_remove1)
    unfolding correctClause_def
    apply (auto simp add: remove1_eq_remove)
    prefer 2
    apply (rule interpClause_resolvants)
    apply simp_all
    apply (insert compl_exists [of l])
    apply auto
    apply (rule interpClause_resolvants)
    apply simp_all
    done
qed

subsection {* res_thm and doProofStep *}

definition get_clause :: "Clause option array \<Rightarrow> ClauseId \<Rightarrow> Clause Heap"
where
  "get_clause a i = 
       (do c \<leftarrow> nth a i;
           (case c of None \<Rightarrow> raise (''Clause not found'')
                    | Some x \<Rightarrow> return x)
        done)"


fun res_thm2 :: "Clause option array \<Rightarrow> (Lit * ClauseId) \<Rightarrow> Clause \<Rightarrow> Clause Heap"
where
  "res_thm2 a (l, j) cli =
  ( if l = 0 then raise(''Illegal literal'')
    else
     (do clj \<leftarrow> get_clause a j;
         res_thm' l cli clj
      done))"

primrec
  foldM :: "('a \<Rightarrow> 'b \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b Heap"
where
  "foldM f [] s = return s"
  | "foldM f (x#xs) s = f x s \<guillemotright>= foldM f xs"

fun doProofStep2 :: "Clause option array \<Rightarrow> ProofStep \<Rightarrow> Clause list \<Rightarrow> Clause list Heap"
where
  "doProofStep2 a (Conflict saveTo (i, rs)) rcs =
  (do
     cli \<leftarrow> get_clause a i;
     result \<leftarrow> foldM (res_thm2 a) rs cli;
     upd saveTo (Some result) a; 
     return rcs
   done)"
| "doProofStep2 a (Delete cid) rcs = (do upd cid None a; return rcs done)"
| "doProofStep2 a (Root cid clause) rcs = (do upd cid (Some (remdups (sort clause))) a; return (clause # rcs) done)"
| "doProofStep2 a (Xstep cid1 cid2) rcs = raise ''MiniSatChecked.doProofStep: Xstep constructor found.''"
| "doProofStep2 a (ProofDone b) rcs = raise ''MiniSatChecked.doProofStep: ProofDone constructor found.''"

definition checker :: "nat \<Rightarrow> ProofStep list \<Rightarrow> nat \<Rightarrow> Clause list Heap"
where
  "checker n p i =
  (do 
     a \<leftarrow> Array.new n None;
     rcs \<leftarrow> foldM (doProofStep2 a) p [];
     ec \<leftarrow> Array.nth a i;
     (if ec = Some [] then return rcs 
                else raise(''No empty clause''))
   done)"

lemma res_thm2_Inv:
  assumes res_thm: "crel (res_thm2 a (l, j) cli) h h' rs"
  assumes correct_a: "correctArray r a h"
  assumes correct_cli: "correctClause r cli \<and> sorted cli \<and> distinct cli"
  shows "h = h' \<and> correctClause r rs \<and> sorted rs \<and> distinct rs"
proof -
  from res_thm have l_not_zero: "l \<noteq> 0" 
    by (auto elim: crel_raise)
  {
    fix clj
    let ?rs = "merge (remove l cli) (remove (compl l) clj)"
    let ?rs' = "merge (remove (compl l) cli) (remove l clj)"
    assume "h = h'" "Some clj = get_array a h' ! j" "j < Heap.length a h'"
    with correct_a have clj: "correctClause r clj" "sorted clj" "distinct clj"
      unfolding correctArray_def by (auto intro: array_ranI)
    with clj l_not_zero correct_cli
    have "(l \<in> set cli \<and> compl l \<in> set clj
      \<longrightarrow> correctClause r ?rs \<and> sorted ?rs \<and> distinct ?rs) \<and>
      (compl l \<in> set cli \<and> l \<in> set clj
      \<longrightarrow> correctClause r ?rs' \<and> sorted ?rs' \<and> distinct ?rs')"
      apply (auto intro!: correctClause_resolvants)
      apply (insert compl_exists [of l])
      by (auto intro!: correctClause_resolvants)
  }
  {
    fix v clj
    assume "Some clj = get_array a h ! j" "j < Heap.length a h"
    with correct_a have clj: "correctClause r clj \<and> sorted clj \<and> distinct clj"
      unfolding correctArray_def by (auto intro: array_ranI)
    assume "crel (res_thm' l cli clj) h h' rs"
    from res_thm'_no_heap[OF this] res_thm'_Inv2[OF this l_not_zero clj correct_cli]
    have "h = h' \<and> correctClause r rs \<and> sorted rs \<and> distinct rs" by simp
  }
  with assms show ?thesis
    unfolding res_thm2.simps get_clause_def
    by (elim crelE crelE' crel_if crel_nth crel_raise crel_return crel_option_case) auto
qed

lemma foldM_Inv2:
  assumes "crel (foldM (res_thm2 a) rs cli) h h' rcl"
  assumes correct_a: "correctArray r a h"
  assumes correct_cli: "correctClause r cli \<and> sorted cli \<and> distinct cli"
  shows "h = h' \<and> correctClause r rcl \<and> sorted rcl \<and> distinct rcl"
using assms
proof (induct rs arbitrary: h h' cli)
  case Nil thus ?case
    unfolding foldM.simps
    by (elim crel_return) auto
next
  case (Cons x xs)
  {
    fix h1 ret
    obtain l j where x_is: "x = (l, j)" by fastsimp
    assume res_thm2: "crel (res_thm2 a x cli) h h1 ret"
    with x_is have res_thm2': "crel (res_thm2 a (l, j) cli) h h1 ret" by simp
    note step = res_thm2_Inv [OF res_thm2' Cons.prems(2) Cons.prems(3)]
    from step have ret: "correctClause r ret \<and> sorted ret \<and> distinct ret" by simp
    from step Cons.prems(2) have correct_a: "correctArray r a h1"  by simp
    assume foldM: "crel (foldM (res_thm2 a) xs ret) h1 h' rcl"
    from step Cons.hyps [OF foldM correct_a ret] have
    "h = h' \<and> correctClause r rcl \<and> sorted rcl \<and> distinct rcl" by auto
  }
  with Cons show ?case
    unfolding foldM.simps
    by (elim crelE) auto
qed


lemma step_correct2:
  assumes crel: "crel (doProofStep2 a step rcs) h h' res"
  assumes correctArray: "correctArray rcs a h"
  shows "correctArray res a h'"
proof (cases "(a,step,rcs)" rule: doProofStep2.cases)
  case (1 a saveTo i rs rcs)
  with crel correctArray
  show ?thesis
    apply auto
    apply (auto simp: get_clause_def elim!: crelE crel_nth)
    apply (auto elim!: crelE crel_nth crel_option_case crel_raise 
      crel_return crel_upd)
    apply (frule foldM_Inv2)
    apply assumption
    apply (simp add: correctArray_def)
    apply (drule_tac x="y" in bspec)
    apply (rule array_ranI[where i=i])
    by (auto intro: correctArray_update)
next
  case (2 a cid rcs)
  with crel correctArray
  show ?thesis
    by (auto simp: correctArray_def elim!: crelE crel_upd crel_return
     dest: array_ran_upd_array_None)
next
  case (3 a cid c rcs)
  with crel correctArray
  show ?thesis
    apply (auto elim!: crelE crel_upd crel_return)
    apply (auto simp: correctArray_def dest!: array_ran_upd_array_Some)
    apply (auto intro: correctClause_mono)
    by (auto simp: correctClause_def)
next
  case 4
  with crel correctArray
  show ?thesis by (auto elim: crel_raise)
next
  case 5
  with crel correctArray
  show ?thesis by (auto elim: crel_raise)
qed
  

theorem fold_steps_correct:
  assumes "crel (foldM (doProofStep2 a) steps rcs) h h' res"
  assumes "correctArray rcs a h"
  shows "correctArray res a h'"
using assms
by (induct steps arbitrary: rcs h h' res)
 (auto elim!: crelE crel_return dest:step_correct2)

theorem checker_soundness:
  assumes "crel (checker n p i) h h' cs"
  shows "inconsistent cs"
using assms unfolding checker_def
apply (elim crelE crel_nth crel_if crel_return crel_raise crel_new_weak)
prefer 2 apply simp
apply auto
apply (drule fold_steps_correct)
apply (simp add: correctArray_def array_ran_def)
apply (rule implies_empty_inconsistent)
apply (simp add:correctArray_def)
apply (drule bspec)
by (rule array_ranI, auto)

section {* Functional version with Lists as Array *}

subsection {* List specific definitions *}

definition list_ran :: "'a option list \<Rightarrow> 'a set"
where
  "list_ran xs = {e. Some e \<in> set xs }"

lemma list_ranI: "\<lbrakk> i < List.length xs; xs ! i = Some b \<rbrakk> \<Longrightarrow> b \<in> list_ran xs"
unfolding list_ran_def by (drule sym, simp)

lemma list_ran_update_Some:
  "cl \<in> list_ran (xs[i := (Some b)]) \<Longrightarrow> cl \<in> list_ran xs \<or> cl = b"
proof -
  assume assms: "cl \<in> list_ran (xs[i := (Some b)])"
  have "set (xs[i := Some b]) \<subseteq> insert (Some b) (set xs)"
    by (simp only: set_update_subset_insert)
  with assms have "Some cl \<in> insert (Some b) (set xs)"
    unfolding list_ran_def by fastsimp
  thus ?thesis
    unfolding list_ran_def by auto
qed

lemma list_ran_update_None:
  "cl \<in> list_ran (xs[i := None]) \<Longrightarrow> cl \<in> list_ran xs"
proof -
  assume assms: "cl \<in> list_ran (xs[i := None])"
  have "set (xs[i := None]) \<subseteq> insert None (set xs)"
    by (simp only: set_update_subset_insert)
  with assms show ?thesis
    unfolding list_ran_def by auto
qed

definition correctList :: "Clause list \<Rightarrow> Clause option list \<Rightarrow> bool"
where
  "correctList rootcls xs =
  (\<forall>cl \<in> list_ran xs. correctClause rootcls cl \<and> sorted cl \<and> distinct cl)"

subsection {* Checker functions *}

fun lres_thm :: "Clause option list \<Rightarrow> (Lit * ClauseId) \<Rightarrow> Clause \<Rightarrow> Clause Heap" 
where
  "lres_thm xs (l, j) cli = (if (j < List.length xs) then (case (xs ! j) of
  None \<Rightarrow> raise (''MiniSatChecked.res_thm: No resolvant clause in thms array for Conflict step.'')
  | Some clj \<Rightarrow> res_thm' l cli clj
 ) else raise ''Error'')"


fun ldoProofStep :: " ProofStep \<Rightarrow> (Clause option list  * Clause list) \<Rightarrow> (Clause option list * Clause list) Heap"
where
  "ldoProofStep (Conflict saveTo (i, rs)) (xs, rcl) =
     (case (xs ! i) of
       None \<Rightarrow> raise (''MiniSatChecked.doProofStep: No starting clause in thms array for Conflict step.'')
     | Some cli \<Rightarrow> (do
                      result \<leftarrow> foldM (lres_thm xs) rs cli ;
                      return ((xs[saveTo:=Some result]), rcl)
                    done))"
| "ldoProofStep (Delete cid) (xs, rcl) = return (xs[cid:=None], rcl)"
| "ldoProofStep (Root cid clause) (xs, rcl) = return (xs[cid:=Some (sort clause)], (remdups(sort clause)) # rcl)"
| "ldoProofStep (Xstep cid1 cid2) (xs, rcl) = raise ''MiniSatChecked.doProofStep: Xstep constructor found.''"
| "ldoProofStep (ProofDone b) (xs, rcl) = raise ''MiniSatChecked.doProofStep: ProofDone constructor found.''"

definition lchecker :: "nat \<Rightarrow> ProofStep list \<Rightarrow> nat \<Rightarrow> Clause list Heap"
where
  "lchecker n p i =
  (do 
     rcs \<leftarrow> foldM (ldoProofStep) p ([], []);
     (if (fst rcs ! i) = Some [] then return (snd rcs) 
                else raise(''No empty clause''))
   done)"


section {* Functional version with RedBlackTrees *}

fun tres_thm :: "(ClauseId, Clause) RBT_Impl.rbt \<Rightarrow> Lit \<times> ClauseId \<Rightarrow> Clause \<Rightarrow> Clause Heap"
where
  "tres_thm t (l, j) cli =
  (case (RBT_Impl.lookup t j) of 
     None \<Rightarrow> raise (''MiniSatChecked.res_thm: No resolvant clause in thms array for Conflict step.'')
   | Some clj \<Rightarrow> res_thm' l cli clj)"

fun tdoProofStep :: " ProofStep \<Rightarrow> ((ClauseId, Clause) RBT_Impl.rbt * Clause list) \<Rightarrow> ((ClauseId, Clause) RBT_Impl.rbt * Clause list) Heap"
where
  "tdoProofStep (Conflict saveTo (i, rs)) (t, rcl) =
     (case (RBT_Impl.lookup t i) of
       None \<Rightarrow> raise (''MiniSatChecked.doProofStep: No starting clause in thms array for Conflict step.'')
     | Some cli \<Rightarrow> (do
                      result \<leftarrow> foldM (tres_thm t) rs cli;
                      return ((RBT_Impl.insert saveTo result t), rcl)
                    done))"
| "tdoProofStep (Delete cid) (t, rcl) = return ((RBT_Impl.delete cid t), rcl)"
| "tdoProofStep (Root cid clause) (t, rcl) = return (RBT_Impl.insert cid (sort clause) t, (remdups(sort clause)) # rcl)"
| "tdoProofStep (Xstep cid1 cid2) (t, rcl) = raise ''MiniSatChecked.doProofStep: Xstep constructor found.''"
| "tdoProofStep (ProofDone b) (t, rcl) = raise ''MiniSatChecked.doProofStep: ProofDone constructor found.''"

definition tchecker :: "nat \<Rightarrow> ProofStep list \<Rightarrow> nat \<Rightarrow> Clause list Heap"
where
  "tchecker n p i =
  (do 
     rcs \<leftarrow> foldM (tdoProofStep) p (RBT_Impl.Empty, []);
     (if (RBT_Impl.lookup (fst rcs) i) = Some [] then return (snd rcs) 
                else raise(''No empty clause''))
   done)"

section {* Code generation setup *}

code_type ProofStep
  (SML "MinisatProofStep.ProofStep")

code_const ProofDone  and  Root              and  Conflict              and  Delete  and  Xstep
     (SML "MinisatProofStep.ProofDone" and "MinisatProofStep.Root ((_),/ (_))" and "MinisatProofStep.Conflict ((_),/ (_))" and "MinisatProofStep.Delete" and "MinisatProofStep.Xstep ((_),/ (_))")

export_code checker in SML module_name SAT file -
export_code tchecker in SML module_name SAT file -
export_code lchecker in SML module_name SAT file -

end
