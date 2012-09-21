(*  Title:      HOL/Codatatype/Examples/Process.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Processes.
*)

header {* Processes *}

theory Process
imports "../Codatatype"
begin

hide_fact (open) Quotient_Product.prod_rel_def

codata 'a process =
  isAction: Action (prefOf: 'a) (contOf: "'a process") |
  isChoice: Choice (ch1Of: "'a process") (ch2Of: "'a process")

(* Read: prefix of, continuation of, choice 1 of, choice 2 of *)

section {* Customization *}

subsection {* Basic properties *}

declare
  pre_process_rel_def[simp]
  sum_rel_def[simp]
  prod_rel_def[simp]

(* Constructors versus discriminators *)
theorem isAction_isChoice:
"isAction p \<or> isChoice p"
by (rule process.disc_exhaust) auto

theorem not_isAction_isChoice: "\<not> (isAction p \<and> isChoice p)"
by (cases rule: process.exhaust[of p]) auto


subsection{* Coinduction *}

theorem process_coind[elim, consumes 1, case_names iss Action Choice, induct pred: "HOL.eq"]:
assumes phi: "\<phi> p p'" and
iss: "\<And>p p'. \<phi> p p' \<Longrightarrow> (isAction p \<longleftrightarrow> isAction p') \<and> (isChoice p \<longleftrightarrow> isChoice p')" and
Act: "\<And> a a' p p'. \<phi> (Action a p) (Action a' p') \<Longrightarrow> a = a' \<and> \<phi> p p'" and
Ch: "\<And> p q p' q'. \<phi> (Choice p q) (Choice p' q') \<Longrightarrow> \<phi> p p' \<and> \<phi> q q'"
shows "p = p'"
proof(intro mp[OF process.rel_coinduct, of \<phi>, OF _ phi], clarify)
  fix p p'  assume \<phi>: "\<phi> p p'"
  show "pre_process_rel (op =) \<phi> (process_dtor p) (process_dtor p')"
  proof(cases rule: process.exhaust[of p])
    case (Action a q) note p = Action
    hence "isAction p'" using iss[OF \<phi>] by (cases rule: process.exhaust[of p'], auto)
    then obtain a' q' where p': "p' = Action a' q'" by (cases rule: process.exhaust[of p'], auto)
    have 0: "a = a' \<and> \<phi> q q'" using Act[OF \<phi>[unfolded p p']] .
    have dtor: "process_dtor p = Inl (a,q)" "process_dtor p' = Inl (a',q')"
    unfolding p p' Action_def process.dtor_ctor by simp_all
    show ?thesis using 0 unfolding dtor by simp
  next
    case (Choice p1 p2) note p = Choice
    hence "isChoice p'" using iss[OF \<phi>] by (cases rule: process.exhaust[of p'], auto)
    then obtain p1' p2' where p': "p' = Choice p1' p2'"
    by (cases rule: process.exhaust[of p'], auto)
    have 0: "\<phi> p1 p1' \<and> \<phi> p2 p2'" using Ch[OF \<phi>[unfolded p p']] .
    have dtor: "process_dtor p = Inr (p1,p2)" "process_dtor p' = Inr (p1',p2')"
    unfolding p p' Choice_def process.dtor_ctor by simp_all
    show ?thesis using 0 unfolding dtor by simp
  qed
qed

(* Stronger coinduction, up to equality: *)
theorem process_strong_coind[elim, consumes 1, case_names iss Action Choice]:
assumes phi: "\<phi> p p'" and
iss: "\<And>p p'. \<phi> p p' \<Longrightarrow> (isAction p \<longleftrightarrow> isAction p') \<and> (isChoice p \<longleftrightarrow> isChoice p')" and
Act: "\<And> a a' p p'. \<phi> (Action a p) (Action a' p') \<Longrightarrow> a = a' \<and> (\<phi> p p' \<or> p = p')" and
Ch: "\<And> p q p' q'. \<phi> (Choice p q) (Choice p' q') \<Longrightarrow> (\<phi> p p' \<or> p = p') \<and> (\<phi> q q' \<or> q = q')"
shows "p = p'"
proof(intro mp[OF process.rel_strong_coinduct, of \<phi>, OF _ phi], clarify)
  fix p p'  assume \<phi>: "\<phi> p p'"
  show "pre_process_rel (op =) (\<lambda>a b. \<phi> a b \<or> a = b) (process_dtor p) (process_dtor p')"
  proof(cases rule: process.exhaust[of p])
    case (Action a q) note p = Action
    hence "isAction p'" using iss[OF \<phi>] by (cases rule: process.exhaust[of p'], auto)
    then obtain a' q' where p': "p' = Action a' q'" by (cases rule: process.exhaust[of p'], auto)
    have 0: "a = a' \<and> (\<phi> q q' \<or> q = q')" using Act[OF \<phi>[unfolded p p']] .
    have dtor: "process_dtor p = Inl (a,q)" "process_dtor p' = Inl (a',q')"
    unfolding p p' Action_def process.dtor_ctor by simp_all
    show ?thesis using 0 unfolding dtor by simp
  next
    case (Choice p1 p2) note p = Choice
    hence "isChoice p'" using iss[OF \<phi>] by (cases rule: process.exhaust[of p'], auto)
    then obtain p1' p2' where p': "p' = Choice p1' p2'"
    by (cases rule: process.exhaust[of p'], auto)
    have 0: "(\<phi> p1 p1' \<or> p1 = p1') \<and> (\<phi> p2 p2' \<or> p2 = p2')" using Ch[OF \<phi>[unfolded p p']] .
    have dtor: "process_dtor p = Inr (p1,p2)" "process_dtor p' = Inr (p1',p2')"
    unfolding p p' Choice_def process.dtor_ctor by simp_all
    show ?thesis using 0 unfolding dtor by simp
  qed
qed


subsection {* Coiteration (unfold) *}


section{* Coinductive definition of the notion of trace *}

(* Say we have a type of streams: *)

typedecl 'a stream

consts Ccons :: "'a \<Rightarrow> 'a stream \<Rightarrow> 'a stream"

(* Use the existing coinductive package (distinct from our
new codatatype package, but highly compatible with it): *)

coinductive trace where
"trace p as \<Longrightarrow> trace (Action a p) (Ccons a as)"
|
"trace p as \<or> trace q as \<Longrightarrow> trace (Choice p q) as"


section{* Examples of corecursive definitions: *}

subsection{* Single-guard fixpoint definition *}

definition
"BX \<equiv>
 process_unfold
   (\<lambda> P. True)
   (\<lambda> P. ''a'')
   (\<lambda> P. P)
   undefined
   undefined
   ()"

lemma BX: "BX = Action ''a'' BX"
unfolding BX_def
using process.unfolds(1)[of "\<lambda> P. True" "()"  "\<lambda> P. ''a''" "\<lambda> P. P"] by simp


subsection{* Multi-guard fixpoint definitions, simulated with auxiliary arguments *}

datatype x_y_ax = x | y | ax

definition "isA \<equiv> \<lambda> K. case K of x \<Rightarrow> False     |y \<Rightarrow> True  |ax \<Rightarrow> True"
definition "pr  \<equiv> \<lambda> K. case K of x \<Rightarrow> undefined |y \<Rightarrow> ''b'' |ax \<Rightarrow> ''a''"
definition "co  \<equiv> \<lambda> K. case K of x \<Rightarrow> undefined |y \<Rightarrow> x    |ax \<Rightarrow> x"
lemmas Action_defs = isA_def pr_def co_def

definition "c1  \<equiv> \<lambda> K. case K of x \<Rightarrow> ax   |y \<Rightarrow> undefined |ax \<Rightarrow> undefined"
definition "c2  \<equiv> \<lambda> K. case K of x \<Rightarrow> y    |y \<Rightarrow> undefined |ax \<Rightarrow> undefined"
lemmas Choice_defs = c1_def c2_def

definition "F \<equiv> process_unfold isA pr co c1 c2"
definition "X = F x"  definition "Y = F y"  definition "AX = F ax"

lemma X_Y_AX: "X = Choice AX Y"  "Y = Action ''b'' X"  "AX = Action ''a'' X"
unfolding X_def Y_def AX_def F_def
using process.unfolds(2)[of isA x "pr" co c1 c2]
      process.unfolds(1)[of isA y "pr" co c1 c2]
      process.unfolds(1)[of isA ax "pr" co c1 c2]
unfolding Action_defs Choice_defs by simp_all

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

definition
"solution sys \<equiv>
 process_unfold
   (isACT sys)
   (PREF sys)
   (CONT sys)
   (CH1 sys)
   (CH2 sys)"

lemma solution_Action:
assumes "isACT sys T"
shows "solution sys T = Action (PREF sys T) (solution sys (CONT sys T))"
unfolding solution_def
using process.unfolds(1)[of "isACT sys" T "PREF sys" "CONT sys" "CH1 sys" "CH2 sys"]
  assms by simp

lemma solution_Choice:
assumes "\<not> isACT sys T"
shows "solution sys T = Choice (solution sys (CH1 sys T)) (solution sys (CH2 sys T))"
unfolding solution_def
using process.unfolds(2)[of "isACT sys" T "PREF sys" "CONT sys" "CH1 sys" "CH2 sys"]
  assms by simp

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
  unfolding solution_Action[OF T] using solution_Action[of sys "VAR X"] True g
  unfolding guarded_def by (cases "sys X", auto)
next
  case False note FFalse = False
  hence TT: "\<not> isACT sys (sys X)" unfolding isACT_VAR[OF g] .
  show ?thesis
  unfolding solution_Choice[OF TT] using solution_Choice[of sys "VAR X"] FFalse g
  unfolding guarded_def by (cases "sys X", auto)
qed

lemma solution_PROC[simp]:
"solution sys (PROC p) = p"
proof-
  {fix q assume "q = solution sys (PROC p)"
   hence "p = q"
   proof(induct rule: process_coind)
     case (iss p p')
     from isAction_isChoice[of p] show ?case
     proof
       assume p: "isAction p"
       hence 0: "isACT sys (PROC p)" by simp
       thus ?thesis using iss not_isAction_isChoice
       unfolding solution_Action[OF 0] by auto
     next
       assume "isChoice p"
       hence 0: "\<not> isACT sys (PROC p)"
       using not_isAction_isChoice by auto
       thus ?thesis using iss isAction_isChoice
       unfolding solution_Choice[OF 0] by auto
     qed
   next
     case (Action a a' p p')
     hence 0: "isACT sys (PROC (Action a p))" by simp
     show ?case using Action unfolding solution_Action[OF 0] by simp
   next
     case (Choice p q p' q')
     hence 0: "\<not> isACT sys (PROC (Choice p q))" using not_isAction_isChoice by auto
     show ?case using Choice unfolding solution_Choice[OF 0] by simp
   qed
  }
  thus ?thesis by metis
qed

lemma solution_ACT[simp]:
"solution sys (ACT a T) = Action a (solution sys T)"
by (metis CONT.simps(3) PREF.simps(3) isACT.simps(3) solution_Action)

lemma solution_CH[simp]:
"solution sys (CH T1 T2) = Choice (solution sys T1) (solution sys T2)"
by (metis CH1.simps(3) CH2.simps(3) isACT.simps(4) solution_Choice)


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
