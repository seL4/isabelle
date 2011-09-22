(*  Title:      HOL/Proofs/Extraction/Higman.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Monika Seisenberger, LMU Muenchen
*)

header {* Higman's lemma *}

theory Higman
imports Main
begin

text {*
  Formalization by Stefan Berghofer and Monika Seisenberger,
  based on Coquand and Fridlender \cite{Coquand93}.
*}

datatype letter = A | B

inductive emb :: "letter list \<Rightarrow> letter list \<Rightarrow> bool"
where
   emb0 [Pure.intro]: "emb [] bs"
 | emb1 [Pure.intro]: "emb as bs \<Longrightarrow> emb as (b # bs)"
 | emb2 [Pure.intro]: "emb as bs \<Longrightarrow> emb (a # as) (a # bs)"

inductive L :: "letter list \<Rightarrow> letter list list \<Rightarrow> bool"
  for v :: "letter list"
where
   L0 [Pure.intro]: "emb w v \<Longrightarrow> L v (w # ws)"
 | L1 [Pure.intro]: "L v ws \<Longrightarrow> L v (w # ws)"

inductive good :: "letter list list \<Rightarrow> bool"
where
    good0 [Pure.intro]: "L w ws \<Longrightarrow> good (w # ws)"
  | good1 [Pure.intro]: "good ws \<Longrightarrow> good (w # ws)"

inductive R :: "letter \<Rightarrow> letter list list \<Rightarrow> letter list list \<Rightarrow> bool"
  for a :: letter
where
    R0 [Pure.intro]: "R a [] []"
  | R1 [Pure.intro]: "R a vs ws \<Longrightarrow> R a (w # vs) ((a # w) # ws)"

inductive T :: "letter \<Rightarrow> letter list list \<Rightarrow> letter list list \<Rightarrow> bool"
  for a :: letter
where
    T0 [Pure.intro]: "a \<noteq> b \<Longrightarrow> R b ws zs \<Longrightarrow> T a (w # zs) ((a # w) # zs)"
  | T1 [Pure.intro]: "T a ws zs \<Longrightarrow> T a (w # ws) ((a # w) # zs)"
  | T2 [Pure.intro]: "a \<noteq> b \<Longrightarrow> T a ws zs \<Longrightarrow> T a ws ((b # w) # zs)"

inductive bar :: "letter list list \<Rightarrow> bool"
where
    bar1 [Pure.intro]: "good ws \<Longrightarrow> bar ws"
  | bar2 [Pure.intro]: "(\<And>w. bar (w # ws)) \<Longrightarrow> bar ws"

theorem prop1: "bar ([] # ws)" by iprover

theorem lemma1: "L as ws \<Longrightarrow> L (a # as) ws"
  by (erule L.induct, iprover+)

lemma lemma2': "R a vs ws \<Longrightarrow> L as vs \<Longrightarrow> L (a # as) ws"
  apply (induct set: R)
  apply (erule L.cases)
  apply simp+
  apply (erule L.cases)
  apply simp_all
  apply (rule L0)
  apply (erule emb2)
  apply (erule L1)
  done

lemma lemma2: "R a vs ws \<Longrightarrow> good vs \<Longrightarrow> good ws"
  apply (induct set: R)
  apply iprover
  apply (erule good.cases)
  apply simp_all
  apply (rule good0)
  apply (erule lemma2')
  apply assumption
  apply (erule good1)
  done

lemma lemma3': "T a vs ws \<Longrightarrow> L as vs \<Longrightarrow> L (a # as) ws"
  apply (induct set: T)
  apply (erule L.cases)
  apply simp_all
  apply (rule L0)
  apply (erule emb2)
  apply (rule L1)
  apply (erule lemma1)
  apply (erule L.cases)
  apply simp_all
  apply iprover+
  done

lemma lemma3: "T a ws zs \<Longrightarrow> good ws \<Longrightarrow> good zs"
  apply (induct set: T)
  apply (erule good.cases)
  apply simp_all
  apply (rule good0)
  apply (erule lemma1)
  apply (erule good1)
  apply (erule good.cases)
  apply simp_all
  apply (rule good0)
  apply (erule lemma3')
  apply iprover+
  done

lemma lemma4: "R a ws zs \<Longrightarrow> ws \<noteq> [] \<Longrightarrow> T a ws zs"
  apply (induct set: R)
  apply iprover
  apply (case_tac vs)
  apply (erule R.cases)
  apply simp
  apply (case_tac a)
  apply (rule_tac b=B in T0)
  apply simp
  apply (rule R0)
  apply (rule_tac b=A in T0)
  apply simp
  apply (rule R0)
  apply simp
  apply (rule T1)
  apply simp
  done

lemma letter_neq: "(a::letter) \<noteq> b \<Longrightarrow> c \<noteq> a \<Longrightarrow> c = b"
  apply (case_tac a)
  apply (case_tac b)
  apply (case_tac c, simp, simp)
  apply (case_tac c, simp, simp)
  apply (case_tac b)
  apply (case_tac c, simp, simp)
  apply (case_tac c, simp, simp)
  done

lemma letter_eq_dec: "(a::letter) = b \<or> a \<noteq> b"
  apply (case_tac a)
  apply (case_tac b)
  apply simp
  apply simp
  apply (case_tac b)
  apply simp
  apply simp
  done

theorem prop2:
  assumes ab: "a \<noteq> b" and bar: "bar xs"
  shows "\<And>ys zs. bar ys \<Longrightarrow> T a xs zs \<Longrightarrow> T b ys zs \<Longrightarrow> bar zs" using bar
proof induct
  fix xs zs assume "T a xs zs" and "good xs"
  hence "good zs" by (rule lemma3)
  then show "bar zs" by (rule bar1)
next
  fix xs ys
  assume I: "\<And>w ys zs. bar ys \<Longrightarrow> T a (w # xs) zs \<Longrightarrow> T b ys zs \<Longrightarrow> bar zs"
  assume "bar ys"
  thus "\<And>zs. T a xs zs \<Longrightarrow> T b ys zs \<Longrightarrow> bar zs"
  proof induct
    fix ys zs assume "T b ys zs" and "good ys"
    then have "good zs" by (rule lemma3)
    then show "bar zs" by (rule bar1)
  next
    fix ys zs assume I': "\<And>w zs. T a xs zs \<Longrightarrow> T b (w # ys) zs \<Longrightarrow> bar zs"
    and ys: "\<And>w. bar (w # ys)" and Ta: "T a xs zs" and Tb: "T b ys zs"
    show "bar zs"
    proof (rule bar2)
      fix w
      show "bar (w # zs)"
      proof (cases w)
        case Nil
        thus ?thesis by simp (rule prop1)
      next
        case (Cons c cs)
        from letter_eq_dec show ?thesis
        proof
          assume ca: "c = a"
          from ab have "bar ((a # cs) # zs)" by (iprover intro: I ys Ta Tb)
          thus ?thesis by (simp add: Cons ca)
        next
          assume "c \<noteq> a"
          with ab have cb: "c = b" by (rule letter_neq)
          from ab have "bar ((b # cs) # zs)" by (iprover intro: I' Ta Tb)
          thus ?thesis by (simp add: Cons cb)
        qed
      qed
    qed
  qed
qed

theorem prop3:
  assumes bar: "bar xs"
  shows "\<And>zs. xs \<noteq> [] \<Longrightarrow> R a xs zs \<Longrightarrow> bar zs" using bar
proof induct
  fix xs zs
  assume "R a xs zs" and "good xs"
  then have "good zs" by (rule lemma2)
  then show "bar zs" by (rule bar1)
next
  fix xs zs
  assume I: "\<And>w zs. w # xs \<noteq> [] \<Longrightarrow> R a (w # xs) zs \<Longrightarrow> bar zs"
  and xsb: "\<And>w. bar (w # xs)" and xsn: "xs \<noteq> []" and R: "R a xs zs"
  show "bar zs"
  proof (rule bar2)
    fix w
    show "bar (w # zs)"
    proof (induct w)
      case Nil
      show ?case by (rule prop1)
    next
      case (Cons c cs)
      from letter_eq_dec show ?case
      proof
        assume "c = a"
        thus ?thesis by (iprover intro: I [simplified] R)
      next
        from R xsn have T: "T a xs zs" by (rule lemma4)
        assume "c \<noteq> a"
        thus ?thesis by (iprover intro: prop2 Cons xsb xsn R T)
      qed
    qed
  qed
qed

theorem higman: "bar []"
proof (rule bar2)
  fix w
  show "bar [w]"
  proof (induct w)
    show "bar [[]]" by (rule prop1)
  next
    fix c cs assume "bar [cs]"
    thus "bar [c # cs]" by (rule prop3) (simp, iprover)
  qed
qed

primrec
  is_prefix :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
    "is_prefix [] f = True"
  | "is_prefix (x # xs) f = (x = f (length xs) \<and> is_prefix xs f)"

theorem L_idx:
  assumes L: "L w ws"
  shows "is_prefix ws f \<Longrightarrow> \<exists>i. emb (f i) w \<and> i < length ws" using L
proof induct
  case (L0 v ws)
  hence "emb (f (length ws)) w" by simp
  moreover have "length ws < length (v # ws)" by simp
  ultimately show ?case by iprover
next
  case (L1 ws v)
  then obtain i where emb: "emb (f i) w" and "i < length ws"
    by simp iprover
  hence "i < length (v # ws)" by simp
  with emb show ?case by iprover
qed

theorem good_idx:
  assumes good: "good ws"
  shows "is_prefix ws f \<Longrightarrow> \<exists>i j. emb (f i) (f j) \<and> i < j" using good
proof induct
  case (good0 w ws)
  hence "w = f (length ws)" and "is_prefix ws f" by simp_all
  with good0 show ?case by (iprover dest: L_idx)
next
  case (good1 ws w)
  thus ?case by simp
qed

theorem bar_idx:
  assumes bar: "bar ws"
  shows "is_prefix ws f \<Longrightarrow> \<exists>i j. emb (f i) (f j) \<and> i < j" using bar
proof induct
  case (bar1 ws)
  thus ?case by (rule good_idx)
next
  case (bar2 ws)
  hence "is_prefix (f (length ws) # ws) f" by simp
  thus ?case by (rule bar2)
qed

text {*
Strong version: yields indices of words that can be embedded into each other.
*}

theorem higman_idx: "\<exists>(i::nat) j. emb (f i) (f j) \<and> i < j"
proof (rule bar_idx)
  show "bar []" by (rule higman)
  show "is_prefix [] f" by simp
qed

text {*
Weak version: only yield sequence containing words
that can be embedded into each other.
*}

theorem good_prefix_lemma:
  assumes bar: "bar ws"
  shows "is_prefix ws f \<Longrightarrow> \<exists>vs. is_prefix vs f \<and> good vs" using bar
proof induct
  case bar1
  thus ?case by iprover
next
  case (bar2 ws)
  from bar2.prems have "is_prefix (f (length ws) # ws) f" by simp
  thus ?case by (iprover intro: bar2)
qed

theorem good_prefix: "\<exists>vs. is_prefix vs f \<and> good vs"
  using higman
  by (rule good_prefix_lemma) simp+

(*<*)
end
(*>*)
