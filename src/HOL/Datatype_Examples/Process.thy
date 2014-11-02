(*  Title:      HOL/Datatype_Examples/Process.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Processes.
*)

section {* Processes *}

theory Process
imports "~~/src/HOL/Library/Stream"
begin

codatatype 'a process =
  isAction: Action (prefOf: 'a) (contOf: "'a process") |
  isChoice: Choice (ch1Of: "'a process") (ch2Of: "'a process")

(* Read: prefix of, continuation of, choice 1 of, choice 2 of *)

section {* Customization *}

subsection {* Basic properties *}

declare
  rel_pre_process_def[simp]
  rel_sum_def[simp]
  rel_prod_def[simp]

(* Constructors versus discriminators *)
theorem isAction_isChoice:
"isAction p \<or> isChoice p"
by (rule process.exhaust_disc) auto

theorem not_isAction_isChoice: "\<not> (isAction p \<and> isChoice p)"
by (cases rule: process.exhaust[of p]) auto


subsection{* Coinduction *}

theorem process_coind[elim, consumes 1, case_names iss Action Choice, induct pred: "HOL.eq"]:
  assumes phi: "\<phi> p p'" and
  iss: "\<And>p p'. \<phi> p p' \<Longrightarrow> (isAction p \<longleftrightarrow> isAction p') \<and> (isChoice p \<longleftrightarrow> isChoice p')" and
  Act: "\<And> a a' p p'. \<phi> (Action a p) (Action a' p') \<Longrightarrow> a = a' \<and> \<phi> p p'" and
  Ch: "\<And> p q p' q'. \<phi> (Choice p q) (Choice p' q') \<Longrightarrow> \<phi> p p' \<and> \<phi> q q'"
  shows "p = p'"
  using assms
  by (coinduct rule: process.coinduct) (metis process.collapse(1,2) process.disc(3))

(* Stronger coinduction, up to equality: *)
theorem process_strong_coind[elim, consumes 1, case_names iss Action Choice]:
  assumes phi: "\<phi> p p'" and
  iss: "\<And>p p'. \<phi> p p' \<Longrightarrow> (isAction p \<longleftrightarrow> isAction p') \<and> (isChoice p \<longleftrightarrow> isChoice p')" and
  Act: "\<And> a a' p p'. \<phi> (Action a p) (Action a' p') \<Longrightarrow> a = a' \<and> (\<phi> p p' \<or> p = p')" and
  Ch: "\<And> p q p' q'. \<phi> (Choice p q) (Choice p' q') \<Longrightarrow> (\<phi> p p' \<or> p = p') \<and> (\<phi> q q' \<or> q = q')"
  shows "p = p'"
  using assms
  by (coinduct rule: process.coinduct_strong) (metis process.collapse(1,2) process.disc(3))


subsection {* Coiteration (unfold) *}


section{* Coinductive definition of the notion of trace *}
coinductive trace where
"trace p as \<Longrightarrow> trace (Action a p) (a ## as)"
|
"trace p as \<or> trace q as \<Longrightarrow> trace (Choice p q) as"


section{* Examples of corecursive definitions: *}

subsection{* Single-guard fixpoint definition *}

primcorec BX where
  "isAction BX"
| "prefOf BX = ''a''"
| "contOf BX = BX"


subsection{* Multi-guard fixpoint definitions, simulated with auxiliary arguments *}

datatype x_y_ax = x | y | ax

primcorec F :: "x_y_ax \<Rightarrow> char list process" where
  "xyax = x \<Longrightarrow> isChoice (F xyax)"
| "ch1Of (F xyax) = F ax"
| "ch2Of (F xyax) = F y"
| "prefOf (F xyax) = (if xyax = y then ''b'' else ''a'')"
| "contOf (F xyax) = F x"

definition "X = F x"  definition "Y = F y"  definition "AX = F ax"

lemma X_Y_AX: "X = Choice AX Y"  "Y = Action ''b'' X"  "AX = Action ''a'' X"
unfolding X_def Y_def AX_def by (subst F.code, simp)+

(* end product: *)
lemma X_AX:
"X = Choice AX (Action ''b'' X)"
"AX = Action ''a'' X"
using X_Y_AX by simp_all



section{* Case study: Multi-guard fixpoint definitions, without auxiliary arguments *}

hide_const x y ax X Y AX

(* Process terms *)
datatype ('a,'pvar) process_term =
 VAR 'pvar |
 PROC "'a process" |
 ACT 'a "('a,'pvar) process_term" | CH "('a,'pvar) process_term" "('a,'pvar) process_term"

(* below, sys represents a system of equations *)
fun isACT where
"isACT sys (VAR X) =
 (case sys X of ACT a T \<Rightarrow> True |PROC p \<Rightarrow> isAction p |_ \<Rightarrow> False)"
|
"isACT sys (PROC p) = isAction p"
|
"isACT sys (ACT a T) = True"
|
"isACT sys (CH T1 T2) = False"

fun PREF where
"PREF sys (VAR X) =
 (case sys X of ACT a T \<Rightarrow> a | PROC p \<Rightarrow> prefOf p)"
|
"PREF sys (PROC p) = prefOf p"
|
"PREF sys (ACT a T) = a"

fun CONT where
"CONT sys (VAR X) =
 (case sys X of ACT a T \<Rightarrow> T | PROC p \<Rightarrow> PROC (contOf p))"
|
"CONT sys (PROC p) = PROC (contOf p)"
|
"CONT sys (ACT a T) = T"

fun CH1 where
"CH1 sys (VAR X) =
 (case sys X of CH T1 T2 \<Rightarrow> T1 |PROC p \<Rightarrow> PROC (ch1Of p))"
|
"CH1 sys (PROC p) = PROC (ch1Of p)"
|
"CH1 sys (CH T1 T2) = T1"

fun CH2 where
"CH2 sys (VAR X) =
 (case sys X of CH T1 T2 \<Rightarrow> T2 |PROC p \<Rightarrow> PROC (ch2Of p))"
|
"CH2 sys (PROC p) = PROC (ch2Of p)"
|
"CH2 sys (CH T1 T2) = T2"

definition "guarded sys \<equiv> \<forall> X Y. sys X \<noteq> VAR Y"

primcorec solution where
  "isACT sys T \<Longrightarrow> solution sys T = Action (PREF sys T) (solution sys (CONT sys T))"
| "_ \<Longrightarrow> solution sys T = Choice (solution sys (CH1 sys T)) (solution sys (CH2 sys T))"

lemma isACT_VAR:
assumes g: "guarded sys"
shows "isACT sys (VAR X) \<longleftrightarrow> isACT sys (sys X)"
using g unfolding guarded_def by (cases "sys X") auto

lemma solution_VAR:
assumes g: "guarded sys"
shows "solution sys (VAR X) = solution sys (sys X)"
proof(cases "isACT sys (VAR X)")
  case True
  hence T: "isACT sys (sys X)" unfolding isACT_VAR[OF g] .
  show ?thesis
  unfolding solution.ctr(1)[OF T] using solution.ctr(1)[of sys "VAR X"] True g
  unfolding guarded_def by (cases "sys X", auto)
next
  case False note FFalse = False
  hence TT: "\<not> isACT sys (sys X)" unfolding isACT_VAR[OF g] .
  show ?thesis
  unfolding solution.ctr(2)[OF TT] using solution.ctr(2)[of sys "VAR X"] FFalse g
  unfolding guarded_def by (cases "sys X", auto)
qed

lemma solution_PROC[simp]:
"solution sys (PROC p) = p"
proof-
  {fix q assume "q = solution sys (PROC p)"
   hence "p = q"
   proof (coinduct rule: process_coind)
     case (iss p p')
     from isAction_isChoice[of p] show ?case
     proof
       assume p: "isAction p"
       hence 0: "isACT sys (PROC p)" by simp
       thus ?thesis using iss not_isAction_isChoice by auto
     next
       assume "isChoice p"
       hence 0: "\<not> isACT sys (PROC p)"
       using not_isAction_isChoice by auto
       thus ?thesis using iss isAction_isChoice by auto
     qed
   next
     case (Action a a' p p')
     hence 0: "isACT sys (PROC (Action a p))" by simp
     show ?case using Action unfolding solution.ctr(1)[OF 0] by simp
   next
     case (Choice p q p' q')
     hence 0: "\<not> isACT sys (PROC (Choice p q))" using not_isAction_isChoice by auto
     show ?case using Choice unfolding solution.ctr(2)[OF 0] by simp
   qed
  }
  thus ?thesis by metis
qed

lemma solution_ACT[simp]:
"solution sys (ACT a T) = Action a (solution sys T)"
by (metis CONT.simps(3) PREF.simps(3) isACT.simps(3) solution.ctr(1))

lemma solution_CH[simp]:
"solution sys (CH T1 T2) = Choice (solution sys T1) (solution sys T2)"
by (metis CH1.simps(3) CH2.simps(3) isACT.simps(4) solution.ctr(2))


(* Example: *)

fun sys where
"sys 0 = CH (VAR (Suc 0)) (ACT ''b'' (VAR 0))"
|
"sys (Suc 0) = ACT ''a'' (VAR 0)"
| (* dummy guarded term for variables outside the system: *)
"sys X = ACT ''a'' (VAR 0)"

lemma guarded_sys:
"guarded sys"
unfolding guarded_def proof (intro allI)
  fix X Y show "sys X \<noteq> VAR Y" by (cases X, simp, case_tac nat, auto)
qed

(* the actual processes: *)
definition "x \<equiv> solution sys (VAR 0)"
definition "ax \<equiv> solution sys (VAR (Suc 0))"

(* end product: *)
lemma x_ax:
"x = Choice ax (Action ''b'' x)"
"ax = Action ''a'' x"
unfolding x_def ax_def by (subst solution_VAR[OF guarded_sys], simp)+


(* Thanks to the inclusion of processes as process terms, one can
also consider parametrized systems of equations---here, x is a (semantic)
process parameter: *)

fun sys' where
"sys' 0 = CH (PROC x) (ACT ''b'' (VAR 0))"
|
"sys' (Suc 0) = CH (ACT ''a'' (VAR 0)) (PROC x)"
| (* dummy guarded term : *)
"sys' X = ACT ''a'' (VAR 0)"

lemma guarded_sys':
"guarded sys'"
unfolding guarded_def proof (intro allI)
  fix X Y show "sys' X \<noteq> VAR Y" by (cases X, simp, case_tac nat, auto)
qed

(* the actual processes: *)
definition "y \<equiv> solution sys' (VAR 0)"
definition "ay \<equiv> solution sys' (VAR (Suc 0))"

(* end product: *)
lemma y_ay:
"y = Choice x (Action ''b'' y)"
"ay = Choice (Action ''a'' y) x"
unfolding y_def ay_def by (subst solution_VAR[OF guarded_sys'], simp)+

end
