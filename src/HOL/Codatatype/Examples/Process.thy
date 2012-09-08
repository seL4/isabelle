(*  Title:      Codatatype_Examples/Process.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Processes.
*)

header {* Processes *}

theory Process
imports "../Codatatype"
begin

codata_raw process: 'p = "'a * 'p + 'p * 'p"
(* codatatype
     'a process = Action (prefOf :: 'a) (contOf :: 'a process) |
                  Choice (ch1Of :: 'a process) (ch2Of :: 'a process)
*)

(* Read: prefix of, continuation of, choice 1 of, choice 2 of *)

section {* Customization *}

subsection{* Setup for map, set, pred  *}

(* These should be eventually inferred from compositionality *)

lemma pre_process_map[simp]:
"pre_process_map fa fp (Inl (a ,p)) = Inl (fa a, fp p)"
"pre_process_map fa fp (Inr (p1, p2)) = Inr (fp p1, fp p2)"
unfolding pre_process_map_def by auto

lemma pre_process_pred[simp]:
"pre_process_pred (op =) \<phi> (Inl (a,p)) (Inl (a',p')) \<longleftrightarrow> a = a' \<and> \<phi> p p'"
"pre_process_pred (op =) \<phi> (Inr (p,q)) (Inr (p',q')) \<longleftrightarrow> \<phi> p p' \<and> \<phi> q q'"
"\<not> pre_process_pred (op =) \<phi> (Inl ap) (Inr q1q2)"
"\<not> pre_process_pred (op =) \<phi> (Inr q1q2) (Inl ap)"
by (auto simp: diag_def pre_process.pred_unfold)


subsection{* Constructors *}

definition Action :: "'a \<Rightarrow> 'a process \<Rightarrow> 'a process"
where "Action a p \<equiv> process_fld (Inl (a,p))"

definition Choice :: "'a process \<Rightarrow> 'a process \<Rightarrow> 'a process"
where "Choice p1 p2 \<equiv> process_fld (Inr (p1,p2))"

lemmas ctor_defs = Action_def Choice_def


subsection {* Discriminators *}

(* One discriminator for each constructor. By the constructor exhaustiveness,
one of them is of course redundant, so for n constructors we only need n-1
discriminators. However, keeping n discriminators seems more uniform.   *)

definition isAction :: "'a process \<Rightarrow> bool"
where "isAction q \<equiv> \<exists> a p. q = Action a p"

definition isChoice :: "'a process \<Rightarrow> bool"
where "isChoice q \<equiv> \<exists> p1 p2. q = Choice p1 p2"

lemmas discr_defs = isAction_def isChoice_def


subsection {* Pre-selectors *}

(* These are mere auxiliaries *)

definition "asAction q \<equiv> SOME ap. q = Action (fst ap) (snd ap)"
definition "asChoice q \<equiv> SOME p1p2. q = Choice (fst p1p2) (snd p1p2)"
lemmas pre_sel_defs = asAction_def asChoice_def


subsection {* Selectors *}

(* One for each pair (constructor, constructor argument) *)

(* For Action: *)
definition prefOf :: "'a process \<Rightarrow> 'a" where "prefOf q = fst (asAction q)"
definition contOf :: "'a process \<Rightarrow> 'a process" where "contOf q = snd (asAction q)"

(* For Choice: *)
definition ch1Of :: "'a process \<Rightarrow> 'a process" where "ch1Of q = fst (asChoice q)"
definition ch2Of :: "'a process \<Rightarrow> 'a process" where "ch2Of q = snd (asChoice q)"

lemmas sel_defs = prefOf_def contOf_def ch1Of_def ch2Of_def


subsection {* Basic properties *}

(* Selectors versus discriminators *)
lemma isAction_asAction:
"isAction q \<longleftrightarrow> q = Action (fst (asAction q)) (snd (asAction q))"
(is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain a p where q: "q = Action a p" unfolding isAction_def by auto
  show ?R unfolding asAction_def q by (rule someI[of _ "(a,p)"]) simp
qed(unfold isAction_def, auto)

theorem isAction_prefOf_contOf:
"isAction q \<longleftrightarrow> q = Action (prefOf q) (contOf q)"
using isAction_asAction unfolding prefOf_def contOf_def .

lemma isChoice_asChoice:
"isChoice q \<longleftrightarrow> q = Choice (fst (asChoice q)) (snd (asChoice q))"
(is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain p1 p2 where q: "q = Choice p1 p2" unfolding isChoice_def by auto
  show ?R unfolding asChoice_def q by (rule someI[of _ "(p1,p2)"]) simp
qed(unfold isChoice_def, auto)

theorem isChoice_ch1Of_ch2Of:
"isChoice q \<longleftrightarrow> q = Choice (ch1Of q) (ch2Of q)"
using isChoice_asChoice unfolding ch1Of_def ch2Of_def .

(* Constructors *)
theorem process_simps[simp]:
"Action a p = Action a' p' \<longleftrightarrow> a = a' \<and> p = p'"
"Choice p1 p2 = Choice p1' p2' \<longleftrightarrow> p1 = p1' \<and> p2 = p2'"
(*  *)
"Action a p \<noteq> Choice p1 p2"
"Choice p1 p2 \<noteq> Action a p"
unfolding ctor_defs process.fld_inject by auto

theorem process_cases[elim, case_names Action Choice]:
assumes Action: "\<And> a p. q = Action a p \<Longrightarrow> phi"
and Choice: "\<And> p1 p2. q = Choice p1 p2 \<Longrightarrow> phi"
shows phi
proof(cases rule: process.fld_exhaust[of q])
  fix x assume "q = process_fld x"
  thus ?thesis
  apply(cases x)
    apply(case_tac a) using Action unfolding ctor_defs apply blast
    apply(case_tac b) using Choice unfolding ctor_defs apply blast
  done
qed

(* Constructors versus discriminators *)
theorem isAction_isChoice:
"isAction p \<or> isChoice p"
unfolding isAction_def isChoice_def by (cases rule: process_cases) auto

theorem isAction_Action[simp]: "isAction (Action a p)"
unfolding isAction_def by auto

theorem isAction_Choice[simp]: "\<not> isAction (Choice p1 p2)"
unfolding isAction_def by auto

theorem isChoice_Choice[simp]: "isChoice (Choice p1 p2)"
unfolding isChoice_def by auto

theorem isChoice_Action[simp]: "\<not> isChoice (Action a p)"
unfolding isChoice_def by auto

theorem not_isAction_isChoice: "\<not> (isAction p \<and> isChoice p)"
by (cases rule: process_cases[of p]) auto

(* Constructors versus selectors *)
theorem dest_ctor[simp]:
"prefOf (Action a p) = a"
"contOf (Action a p) = p"
"ch1Of (Choice p1 p2) = p1"
"ch2Of (Choice p1 p2) = p2"
using isAction_Action[of a p]
      isChoice_Choice[of p1 p2]
unfolding isAction_prefOf_contOf
          isChoice_ch1Of_ch2Of by auto

theorem ctor_dtor[simp]:
"\<And> p. isAction p \<Longrightarrow> Action (prefOf p) (contOf p) = p"
"\<And> p. isChoice p \<Longrightarrow> Choice (ch1Of p) (ch2Of p) = p"
unfolding isAction_def isChoice_def by auto


subsection{* Coinduction *}

theorem process_coind[elim, consumes 1, case_names iss Action Choice, induct pred: "HOL.eq"]:
assumes phi: "\<phi> p p'" and
iss: "\<And>p p'. \<phi> p p' \<Longrightarrow> (isAction p \<longleftrightarrow> isAction p') \<and> (isChoice p \<longleftrightarrow> isChoice p')" and
Act: "\<And> a a' p p'. \<phi> (Action a p) (Action a' p') \<Longrightarrow> a = a' \<and> \<phi> p p'" and
Ch: "\<And> p q p' q'. \<phi> (Choice p q) (Choice p' q') \<Longrightarrow> \<phi> p p' \<and> \<phi> q q'"
shows "p = p'"
proof(intro mp[OF process.pred_coinduct, of \<phi>, OF _ phi], clarify)
  fix p p'  assume \<phi>: "\<phi> p p'"
  show "pre_process_pred (op =) \<phi> (process_unf p) (process_unf p')"
  proof(cases rule: process_cases[of p])
    case (Action a q) note p = Action
    hence "isAction p'" using iss[OF \<phi>] by (cases rule: process_cases[of p'], auto)
    then obtain a' q' where p': "p' = Action a' q'" by (cases rule: process_cases[of p'], auto)
    have 0: "a = a' \<and> \<phi> q q'" using Act[OF \<phi>[unfolded p p']] .
    have unf: "process_unf p = Inl (a,q)" "process_unf p' = Inl (a',q')"
    unfolding p p' Action_def process.unf_fld by simp_all
    show ?thesis using 0 unfolding unf by simp
  next
    case (Choice p1 p2) note p = Choice
    hence "isChoice p'" using iss[OF \<phi>] by (cases rule: process_cases[of p'], auto)
    then obtain p1' p2' where p': "p' = Choice p1' p2'"
    by (cases rule: process_cases[of p'], auto)
    have 0: "\<phi> p1 p1' \<and> \<phi> p2 p2'" using Ch[OF \<phi>[unfolded p p']] .
    have unf: "process_unf p = Inr (p1,p2)" "process_unf p' = Inr (p1',p2')"
    unfolding p p' Choice_def process.unf_fld by simp_all
    show ?thesis using 0 unfolding unf by simp
  qed
qed

(* Stronger coinduction, up to equality: *)
theorem process_coind_upto[elim, consumes 1, case_names iss Action Choice]:
assumes phi: "\<phi> p p'" and
iss: "\<And>p p'. \<phi> p p' \<Longrightarrow> (isAction p \<longleftrightarrow> isAction p') \<and> (isChoice p \<longleftrightarrow> isChoice p')" and
Act: "\<And> a a' p p'. \<phi> (Action a p) (Action a' p') \<Longrightarrow> a = a' \<and> (\<phi> p p' \<or> p = p')" and
Ch: "\<And> p q p' q'. \<phi> (Choice p q) (Choice p' q') \<Longrightarrow> (\<phi> p p' \<or> p = p') \<and> (\<phi> q q' \<or> q = q')"
shows "p = p'"
proof(intro mp[OF process.pred_coinduct_upto, of \<phi>, OF _ phi], clarify)
  fix p p'  assume \<phi>: "\<phi> p p'"
  show "pre_process_pred (op =) (\<lambda>a b. \<phi> a b \<or> a = b) (process_unf p) (process_unf p')"
  proof(cases rule: process_cases[of p])
    case (Action a q) note p = Action
    hence "isAction p'" using iss[OF \<phi>] by (cases rule: process_cases[of p'], auto)
    then obtain a' q' where p': "p' = Action a' q'" by (cases rule: process_cases[of p'], auto)
    have 0: "a = a' \<and> (\<phi> q q' \<or> q = q')" using Act[OF \<phi>[unfolded p p']] .
    have unf: "process_unf p = Inl (a,q)" "process_unf p' = Inl (a',q')"
    unfolding p p' Action_def process.unf_fld by simp_all
    show ?thesis using 0 unfolding unf by simp
  next
    case (Choice p1 p2) note p = Choice
    hence "isChoice p'" using iss[OF \<phi>] by (cases rule: process_cases[of p'], auto)
    then obtain p1' p2' where p': "p' = Choice p1' p2'"
    by (cases rule: process_cases[of p'], auto)
    have 0: "(\<phi> p1 p1' \<or> p1 = p1') \<and> (\<phi> p2 p2' \<or> p2 = p2')" using Ch[OF \<phi>[unfolded p p']] .
    have unf: "process_unf p = Inr (p1,p2)" "process_unf p' = Inr (p1',p2')"
    unfolding p p' Choice_def process.unf_fld by simp_all
    show ?thesis using 0 unfolding unf by simp
  qed
qed


subsection {* Coiteration and corecursion *}

(* Preliminaries: *)
definition
"join22 isA pr co isC c1 c2 \<equiv>
 \<lambda> P. if isA P then Inl (pr P, co P)
 else if isC P then Inr (c1 P, c2 P)
 else undefined"

declare process.unf_fld[simp]
declare process.fld_unf[simp]

lemma unf_Action[simp]:
"process_unf (Action a p) = Inl (a,p)"
unfolding Action_def process.unf_fld ..

lemma unf_Choice[simp]:
"process_unf (Choice p1 p2) = Inr (p1,p2)"
unfolding Choice_def process.unf_fld ..

lemma isAction_unf:
assumes "isAction p"
shows "process_unf p = Inl (prefOf p, contOf p)"
using assms unfolding isAction_def by auto

lemma isChoice_unf:
assumes "isChoice p"
shows "process_unf p = Inr (ch1Of p, ch2Of p)"
using assms unfolding isChoice_def by auto

lemma unf_join22:
"process_unf p = join22 isAction prefOf contOf isChoice ch1Of ch2Of p"
unfolding join22_def
using isAction_unf isChoice_unf not_isAction_isChoice isAction_isChoice by auto

lemma isA_join22:
assumes "isA P"
shows "join22 isA pr co isC c1 c2 P = Inl (pr P, co P)"
using assms unfolding join22_def by auto

lemma isC_join22:
assumes "\<not> isA P" and "isC P"
shows "join22 isA pr co isC c1 c2 P = Inr (c1 P, c2 P)"
using assms unfolding join22_def by auto

(* Coiteration *)
definition pcoiter ::
"('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)
 \<Rightarrow>
 ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b)
 \<Rightarrow>
 'b \<Rightarrow> 'a process"
where "pcoiter isA pr co isC c1 c2 \<equiv> process_unf_coiter (join22 isA pr co isC c1 c2)"

lemma unf_prefOf:
assumes "process_unf q = Inl (a,p)"
shows "prefOf q = a"
using assms by (cases rule: process_cases[of q]) auto

lemma unf_contOf:
assumes "process_unf q = Inl (a,p)"
shows "contOf q = p"
using assms by (cases rule: process_cases[of q]) auto

lemma unf_ch1Of:
assumes "process_unf q = Inr (p1,p2)"
shows "ch1Of q = p1"
using assms by (cases rule: process_cases[of q]) auto

lemma unf_ch2Of:
assumes "process_unf q = Inr (p1,p2)"
shows "ch2Of q = p2"
using assms by (cases rule: process_cases[of q]) auto

theorem pcoiter:
"\<And>P. isA P \<Longrightarrow>
    pcoiter isA pr co isC c1 c2 P =
    Action (pr P)
           (pcoiter isA pr co isC c1 c2 (co P))"
"\<And>P. \<lbrakk>\<not> isA P; isC P\<rbrakk> \<Longrightarrow>
    pcoiter isA pr co isC c1 c2 P =
    Choice (pcoiter isA pr co isC c1 c2 (c1 P))
           (pcoiter isA pr co isC c1 c2 (c2 P))"
proof-
  fix P
  let ?f = "pcoiter isA pr co isC c1 c2"  let ?s = "join22 isA pr co isC c1 c2"
  assume isA: "isA P"
  have unf: "process_unf (process_unf_coiter ?s P) = Inl (pr P, ?f (co P))"
  using process.unf_coiter[of ?s P]
  unfolding isA_join22[of isA P "pr" co isC c1 c2, OF isA]
            pre_process_map id_apply pcoiter_def .
  thus "?f P = Action (pr P) (?f (co P))"
  unfolding pcoiter_def Action_def using process.fld_unf by metis
next
  fix P
  let ?f = "pcoiter isA pr co isC c1 c2"  let ?s = "join22 isA pr co isC c1 c2"
  assume isA: "\<not> isA P" and isC: "isC P"
  have unf: "process_unf (process_unf_coiter ?s P) = Inr (?f (c1 P), ?f (c2 P))"
  using process.unf_coiter[of ?s P]
  unfolding isC_join22[of isA P isC "pr" co c1 c2, OF isA isC]
            pre_process_map id_apply pcoiter_def .
  thus "?f P = Choice (?f (c1 P)) (?f (c2 P))"
  unfolding pcoiter_def Choice_def using process.fld_unf by metis
qed

(* Corecursion, more general than coiteration (often unnecessarily more general): *)
definition pcorec ::
"('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'a process + 'b)
 \<Rightarrow>
 ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a process + 'b) \<Rightarrow> ('b \<Rightarrow> 'a process + 'b)
 \<Rightarrow>
 'b \<Rightarrow> 'a process"
where
"pcorec isA pr co isC c1 c2 \<equiv> process_unf_corec (join22 isA pr co isC c1 c2)"

theorem pcorec_Action:
assumes isA: "isA P"
shows
"case co P of
   Inl p \<Rightarrow> pcorec isA pr co isC c1 c2 P = Action (pr P) p
  |Inr Q \<Rightarrow> pcorec isA pr co isC c1 c2 P =
            Action (pr P)
                   (pcorec isA pr co isC c1 c2 Q)"
proof-
  let ?f = "pcorec isA pr co isC c1 c2"  let ?s = "join22 isA pr co isC c1 c2"
  show ?thesis
  proof(cases "co P")
    case (Inl p)
    have "process_unf (process_unf_corec ?s P) = Inl (pr P, p)"
    using process.unf_corec[of ?s P]
    unfolding isA_join22[of isA P "pr" co isC c1 c2, OF isA]
              pre_process_map id_apply pcorec_def Inl by simp
    thus ?thesis unfolding Inl pcorec_def Action_def using process.fld_unf by (simp, metis)
  next
    case (Inr Q)
    have "process_unf (process_unf_corec ?s P) = Inl (pr P, ?f Q)"
    using process.unf_corec[of ?s P]
    unfolding isA_join22[of isA P "pr" co isC c1 c2, OF isA]
              pre_process_map id_apply pcorec_def Inr by simp
    thus ?thesis unfolding Inr pcorec_def Action_def using process.fld_unf by (simp, metis)
  qed
qed

theorem pcorec_Choice:
assumes isA: "\<not> isA P" and isC: "isC P"
shows
"case (c1 P,c2 P) of
   (Inl p1, Inl p2) \<Rightarrow> pcorec isA pr co isC c1 c2 P =
                      Choice p1 p2
  |(Inl p1, Inr Q2) \<Rightarrow> pcorec isA pr co isC c1 c2 P =
                      Choice p1
                             (pcorec isA pr co isC c1 c2 Q2)
  |(Inr Q1, Inl p2) \<Rightarrow> pcorec isA pr co isC c1 c2 P =
                      Choice (pcorec isA pr co isC c1 c2 Q1)
                             p2
  |(Inr Q1, Inr Q2) \<Rightarrow> pcorec isA pr co isC c1 c2 P =
                      Choice (pcorec isA pr co isC c1 c2 Q1)
                             (pcorec isA pr co isC c1 c2 Q2)"
proof-
  let ?f = "pcorec isA pr co isC c1 c2"  let ?s = "join22 isA pr co isC c1 c2"
  show ?thesis
  proof(cases "c1 P")
    case (Inl p1) note c1 = Inl
    show ?thesis
    proof(cases "c2 P")
      case (Inl p2)  note c2 = Inl
      have "process_unf (process_unf_corec ?s P) = Inr (p1, p2)"
      using process.unf_corec[of ?s P]
      unfolding isC_join22[of isA P isC "pr" co c1 c2, OF isA isC]
                pre_process_map id_apply pcorec_def c1 c2 by simp
      thus ?thesis unfolding c1 c2 pcorec_def Choice_def using process.fld_unf by (simp, metis)
    next
      case (Inr Q2)  note c2 = Inr
      have "process_unf (process_unf_corec ?s P) = Inr (p1, ?f Q2)"
      using process.unf_corec[of ?s P]
      unfolding isC_join22[of isA P isC "pr" co c1 c2, OF isA isC]
                pre_process_map id_apply pcorec_def c1 c2 by simp
      thus ?thesis unfolding c1 c2 pcorec_def Choice_def using process.fld_unf by (simp, metis)
    qed
  next
    case (Inr Q1) note c1 = Inr
    show ?thesis
    proof(cases "c2 P")
      case (Inl p2)  note c2 = Inl
      have "process_unf (process_unf_corec ?s P) = Inr (?f Q1, p2)"
      using process.unf_corec[of ?s P]
      unfolding isC_join22[of isA P isC "pr" co c1 c2, OF isA isC]
                pre_process_map id_apply pcorec_def c1 c2 by simp
      thus ?thesis unfolding c1 c2 pcorec_def Choice_def using process.fld_unf by (simp, metis)
    next
      case (Inr Q2)  note c2 = Inr
      have "process_unf (process_unf_corec ?s P) = Inr (?f Q1, ?f Q2)"
      using process.unf_corec[of ?s P]
      unfolding isC_join22[of isA P isC "pr" co c1 c2, OF isA isC]
                pre_process_map id_apply pcorec_def c1 c2 by simp
      thus ?thesis unfolding c1 c2 pcorec_def Choice_def using process.fld_unf by (simp, metis)
    qed
  qed
qed

theorems pcorec = pcorec_Action pcorec_Choice


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
 pcoiter
   (\<lambda> P. True)
   (\<lambda> P. ''a'')
   (\<lambda> P. P)
   undefined
   undefined
   undefined
   ()"

lemma BX: "BX = Action ''a'' BX"
unfolding BX_def
using pcoiter(1)[of "\<lambda> P. True" "()"  "\<lambda> P. ''a''" "\<lambda> P. P"] by simp


subsection{* Multi-guard fixpoint definitions, simulated with auxiliary arguments *}

datatype x_y_ax = x | y | ax

definition "isA \<equiv> \<lambda> K. case K of x \<Rightarrow> False     |y \<Rightarrow> True  |ax \<Rightarrow> True"
definition "pr  \<equiv> \<lambda> K. case K of x \<Rightarrow> undefined |y \<Rightarrow> ''b'' |ax \<Rightarrow> ''a''"
definition "co  \<equiv> \<lambda> K. case K of x \<Rightarrow> undefined |y \<Rightarrow> x    |ax \<Rightarrow> x"
lemmas Action_defs = isA_def pr_def co_def

definition "isC \<equiv> \<lambda> K. case K of x \<Rightarrow> True |y \<Rightarrow> False     |ax \<Rightarrow> False"
definition "c1  \<equiv> \<lambda> K. case K of x \<Rightarrow> ax   |y \<Rightarrow> undefined |ax \<Rightarrow> undefined"
definition "c2  \<equiv> \<lambda> K. case K of x \<Rightarrow> y    |y \<Rightarrow> undefined |ax \<Rightarrow> undefined"
lemmas Choice_defs = isC_def c1_def c2_def

definition "F \<equiv> pcoiter isA pr co isC c1 c2"
definition "X = F x"  definition "Y = F y"  definition "AX = F ax"

lemma X_Y_AX: "X = Choice AX Y"  "Y = Action ''b'' X"  "AX = Action ''a'' X"
unfolding X_def Y_def AX_def F_def
using pcoiter(2)[of isA x isC "pr" co c1 c2]
      pcoiter(1)[of isA y  "pr" co isC c1 c2]
      pcoiter(1)[of isA ax "pr" co isC c1 c2]
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

fun isCH where
"isCH sys (VAR X) =
 (case sys X of CH T1 T2 \<Rightarrow> True |PROC p \<Rightarrow> isChoice p |_ \<Rightarrow> False)"
|
"isCH sys (PROC p) = isChoice p"
|
"isCH sys (ACT a T) = False"
|
"isCH sys (CH T1 T2) = True"

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

lemma guarded_isACT_isCH:
assumes g: "guarded sys"
shows "isACT sys T \<or> isCH sys T"
proof(induct T)
  case (VAR X)
  thus ?case
  using g isAction_isChoice unfolding guarded_def by (cases "sys X", auto)
qed(insert isAction_isChoice assms, unfold guarded_def, auto)

definition
"solution sys \<equiv>
 pcoiter
   (isACT sys)
   (PREF sys)
   (CONT sys)
   (isCH sys)
   (CH1 sys)
   (CH2 sys)"

lemma solution_Action:
assumes "isACT sys T"
shows "solution sys T = Action (PREF sys T) (solution sys (CONT sys T))"
unfolding solution_def
using pcoiter(1)[of "isACT sys" T "PREF sys" "CONT sys"
                        "isCH sys" "CH1 sys" "CH2 sys"] assms by simp

lemma solution_Choice:
assumes "\<not> isACT sys T" "isCH sys T"
shows "solution sys T = Choice (solution sys (CH1 sys T)) (solution sys (CH2 sys T))"
unfolding solution_def
using pcoiter(2)[of "isACT sys" T "isCH sys" "PREF sys" "CONT sys"
                        "CH1 sys" "CH2 sys"] assms by simp

lemma isACT_VAR:
assumes g: "guarded sys"
shows "isACT sys (VAR X) \<longleftrightarrow> isACT sys (sys X)"
using g unfolding guarded_def by (cases "sys X") auto

lemma isCH_VAR:
assumes g: "guarded sys"
shows "isCH sys (VAR X) \<longleftrightarrow> isCH sys (sys X)"
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
  proof(cases "isCH sys (VAR X)")
    case True
    hence T: "isCH sys (sys X)" unfolding isCH_VAR[OF g] .
    show ?thesis
    unfolding solution_Choice[OF TT T] using solution_Choice[of sys "VAR X"] FFalse True g
    unfolding guarded_def by (cases "sys X", auto)
  next
    case False
    hence False using FFalse guarded_isACT_isCH[OF g, of "VAR X"] by simp
    thus ?thesis by simp
  qed
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
       hence 0: "isCH sys (PROC p)" and p: "\<not> isAction p"
       using not_isAction_isChoice by auto
       hence 1: "\<not> isACT sys (PROC p)" by simp
       show ?thesis using 0 iss not_isAction_isChoice
       unfolding solution_Choice[OF 1 0] by auto
     qed
   next
     case (Action a a' p p')
     hence 0: "isACT sys (PROC (Action a p))" by simp
     show ?case using Action unfolding solution_Action[OF 0] by simp
   next
     case (Choice p q p' q')
     hence 0: "isCH sys (PROC (Choice p q))" by simp
     hence 1: "\<not> isACT sys (PROC (Choice p q))" using not_isAction_isChoice by auto
     show ?case using Choice unfolding solution_Choice[OF 1 0] by simp
   qed
  }
  thus ?thesis by metis
qed

lemma solution_ACT[simp]:
"solution sys (ACT a T) = Action a (solution sys T)"
by (metis CONT.simps(3) PREF.simps(3) isACT.simps(3) solution_Action)

lemma solution_CH[simp]:
"solution sys (CH T1 T2) = Choice (solution sys T1) (solution sys T2)"
by (metis CH1.simps(3) CH2.simps(3) isACT.simps(4) isCH.simps(4) solution_Choice)


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
