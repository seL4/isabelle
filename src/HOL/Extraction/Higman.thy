(*  Title:      HOL/Extraction/Higman.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
                Monika Seisenberger, LMU Muenchen
*)

header {* Higman's lemma *}

theory Higman = Main:

text {*
  Formalization by Stefan Berghofer and Monika Seisenberger,
  based on Coquand and Fridlender \cite{Coquand93}.
*}

datatype letter = A | B

consts
  emb :: "(letter list \<times> letter list) set"

inductive emb
intros
  emb0 [CPure.intro]: "([], bs) \<in> emb"
  emb1 [CPure.intro]: "(as, bs) \<in> emb \<Longrightarrow> (as, b # bs) \<in> emb"
  emb2 [CPure.intro]: "(as, bs) \<in> emb \<Longrightarrow> (a # as, a # bs) \<in> emb"

consts
  L :: "letter list \<Rightarrow> letter list list set"

inductive "L y"
intros
  L0 [CPure.intro]: "(w, y) \<in> emb \<Longrightarrow> w # ws \<in> L y"
  L1 [CPure.intro]: "ws \<in> L y \<Longrightarrow> w # ws \<in> L y"

consts
  good :: "letter list list set"

inductive good
intros
  good0 [CPure.intro]: "ws \<in> L w \<Longrightarrow> w # ws \<in> good"
  good1 [CPure.intro]: "ws \<in> good \<Longrightarrow> w # ws \<in> good"

consts
  R :: "letter \<Rightarrow> (letter list list \<times> letter list list) set"

inductive "R a"
intros
  R0 [CPure.intro]: "([], []) \<in> R a"
  R1 [CPure.intro]: "(vs, ws) \<in> R a \<Longrightarrow> (w # vs, (a # w) # ws) \<in> R a"

consts
  T :: "letter \<Rightarrow> (letter list list \<times> letter list list) set"

inductive "T a"
intros
  T0 [CPure.intro]: "a \<noteq> b \<Longrightarrow> (ws, zs) \<in> R b \<Longrightarrow> (w # zs, (a # w) # zs) \<in> T a"
  T1 [CPure.intro]: "(ws, zs) \<in> T a \<Longrightarrow> (w # ws, (a # w) # zs) \<in> T a"
  T2 [CPure.intro]: "a \<noteq> b \<Longrightarrow> (ws, zs) \<in> T a \<Longrightarrow> (ws, (b # w) # zs) \<in> T a"

consts
  bar :: "letter list list set"

inductive bar
intros
  bar1 [CPure.intro]: "ws \<in> good \<Longrightarrow> ws \<in> bar"
  bar2 [CPure.intro]: "(\<And>w. w # ws \<in> bar) \<Longrightarrow> ws \<in> bar"

theorem prop1: "([] # ws) \<in> bar" by rules

theorem lemma1: "ws \<in> L as \<Longrightarrow> ws \<in> L (a # as)"
  by (erule L.induct, rules+)

theorem lemma2' [rule_format]: "(vs, ws) \<in> R a \<Longrightarrow> vs \<in> L as \<longrightarrow> ws \<in> L (a # as)"
  apply (erule R.induct)
  apply (rule impI)
  apply (erule L.elims)
  apply simp+
  apply (rule impI)
  apply (erule L.elims)
  apply simp_all
  apply (rule L0)
  apply (erule emb2)
  apply (erule L1)
  done
 
theorem lemma2 [rule_format]: "(vs, ws) \<in> R a \<Longrightarrow> vs \<in> good \<longrightarrow> ws \<in> good"
  apply (erule R.induct)
  apply rules
  apply (rule impI)
  apply (erule good.elims)
  apply simp_all
  apply (rule good0)
  apply (erule lemma2')
  apply assumption
  apply (erule good1)
  done

theorem lemma3' [rule_format]:
    "(vs, ws) \<in> T a \<Longrightarrow> vs \<in> L as \<longrightarrow> ws \<in> L (a # as)"
  apply (erule T.induct)
  apply (rule impI)
  apply (erule L.elims)
  apply simp_all
  apply (rule L0)
  apply (erule emb2)
  apply (rule L1)
  apply (erule lemma1)
  apply (rule impI)
  apply (erule L.elims)
  apply simp_all
  apply rules+
  done

theorem lemma3 [rule_format]: "(ws, zs) \<in> T a \<Longrightarrow> ws \<in> good \<longrightarrow> zs \<in> good"
  apply (erule T.induct)
  apply (rule impI)
  apply (erule good.elims)
  apply simp_all
  apply (rule good0)
  apply (erule lemma1)
  apply (erule good1)
  apply (rule impI)
  apply (erule good.elims)
  apply simp_all
  apply (rule good0)
  apply (erule lemma3')
  apply rules+
  done

theorem lemma4 [rule_format]: "(ws, zs) \<in> R a \<Longrightarrow> ws \<noteq> [] \<longrightarrow> (ws, zs) \<in> T a"
  apply (erule R.induct)
  apply rules
  apply (rule impI)
  apply (case_tac vs)
  apply (erule R.elims)
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
  apply (erule mp)
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
  assumes ab: "a \<noteq> b" and bar: "xs \<in> bar"
  shows "\<And>ys zs. ys \<in> bar \<Longrightarrow> (xs, zs) \<in> T a \<Longrightarrow> (ys, zs) \<in> T b \<Longrightarrow> zs \<in> bar" using bar
proof induct
  fix xs zs assume "xs \<in> good" and "(xs, zs) \<in> T a"
  show "zs \<in> bar" by (rule bar1) (rule lemma3)
next
  fix xs ys
  assume I: "\<And>w ys zs. ys \<in> bar \<Longrightarrow> (w # xs, zs) \<in> T a \<Longrightarrow> (ys, zs) \<in> T b \<Longrightarrow> zs \<in> bar"
  assume "ys \<in> bar"
  thus "\<And>zs. (xs, zs) \<in> T a \<Longrightarrow> (ys, zs) \<in> T b \<Longrightarrow> zs \<in> bar"
  proof induct
    fix ys zs assume "ys \<in> good" and "(ys, zs) \<in> T b"
    show "zs \<in> bar" by (rule bar1) (rule lemma3)
  next
    fix ys zs assume I': "\<And>w zs. (xs, zs) \<in> T a \<Longrightarrow> (w # ys, zs) \<in> T b \<Longrightarrow> zs \<in> bar"
    and ys: "\<And>w. w # ys \<in> bar" and Ta: "(xs, zs) \<in> T a" and Tb: "(ys, zs) \<in> T b"
    show "zs \<in> bar"
    proof (rule bar2)
      fix w
      show "w # zs \<in> bar"
      proof (cases w)
	case Nil
	thus ?thesis by simp (rule prop1)
      next
	case (Cons c cs)
	from letter_eq_dec show ?thesis
	proof
	  assume ca: "c = a"
	  from ab have "(a # cs) # zs \<in> bar" by (rules intro: I ys Ta Tb)+
	  thus ?thesis by (simp add: Cons ca)
	next
	  assume "c \<noteq> a"
	  with ab have cb: "c = b" by (rule letter_neq)
	  from ab have "(b # cs) # zs \<in> bar" by (rules intro: I' Ta Tb)+
	  thus ?thesis by (simp add: Cons cb)
	qed
      qed
    qed
  qed
qed

theorem prop3:
  assumes bar: "xs \<in> bar"
  shows "\<And>zs. xs \<noteq> [] \<Longrightarrow> (xs, zs) \<in> R a \<Longrightarrow> zs \<in> bar" using bar
proof induct
  fix xs zs
  assume "xs \<in> good" and "(xs, zs) \<in> R a"
  show "zs \<in> bar" by (rule bar1) (rule lemma2)
next
  fix xs zs
  assume I: "\<And>w zs. w # xs \<noteq> [] \<Longrightarrow> (w # xs, zs) \<in> R a \<Longrightarrow> zs \<in> bar"
  and xsb: "\<And>w. w # xs \<in> bar" and xsn: "xs \<noteq> []" and R: "(xs, zs) \<in> R a"
  show "zs \<in> bar"
  proof (rule bar2)
    fix w
    show "w # zs \<in> bar"
    proof (induct w)
      case Nil
      show ?case by (rule prop1)
    next
      case (Cons c cs)
      from letter_eq_dec show ?case
      proof
	assume "c = a"
	thus ?thesis by (rules intro: I [simplified] R)
      next
	from R xsn have T: "(xs, zs) \<in> T a" by (rule lemma4)
	assume "c \<noteq> a"
	thus ?thesis by (rules intro: prop2 Cons xsb xsn R T)
      qed
    qed
  qed
qed

theorem higman: "[] \<in> bar"
proof (rule bar2)
  fix w
  show "[w] \<in> bar"
  proof (induct w)
    show "[[]] \<in> bar" by (rule prop1)
  next
    fix c cs assume "[cs] \<in> bar"
    thus "[c # cs] \<in> bar" by (rule prop3) (simp, rules)
  qed
qed

consts
  is_prefix :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"

primrec
  "is_prefix [] f = True"
  "is_prefix (x # xs) f = (x = f (length xs) \<and> is_prefix xs f)"

theorem good_prefix_lemma:
  assumes bar: "ws \<in> bar"
  shows "is_prefix ws f \<Longrightarrow> \<exists>vs. is_prefix vs f \<and> vs \<in> good" using bar
proof induct
  case bar1
  thus ?case by rules
next
  case (bar2 ws)
  have "is_prefix (f (length ws) # ws) f" by simp
  thus ?case by (rules intro: bar2)
qed

theorem good_prefix: "\<exists>vs. is_prefix vs f \<and> vs \<in> good"
  using higman
  by (rule good_prefix_lemma) simp+

subsection {* Extracting the program *}

declare bar.induct [ind_realizer]

extract good_prefix

text {*
  Program extracted from the proof of @{text good_prefix}:
  @{thm [display] good_prefix_def [no_vars]}
  Corresponding correctness theorem:
  @{thm [display] good_prefix_correctness [no_vars]}
  Program extracted from the proof of @{text good_prefix_lemma}:
  @{thm [display] good_prefix_lemma_def [no_vars]}
  Program extracted from the proof of @{text higman}:
  @{thm [display] higman_def [no_vars]}
  Program extracted from the proof of @{text prop1}:
  @{thm [display] prop1_def [no_vars]}
  Program extracted from the proof of @{text prop2}:
  @{thm [display] prop2_def [no_vars]}
  Program extracted from the proof of @{text prop3}:
  @{thm [display] prop3_def [no_vars]}
*}

generate_code
  test = good_prefix

ML {*
val a = 16807.0;
val m = 2147483647.0;

fun nextRand seed =
  let val t = a*seed
  in  t - m * real (Real.floor(t/m)) end;

fun mk_word seed l =
  let
    val r = nextRand seed;
    val i = Real.round (r / m * 10.0);
  in if i > 7 andalso l > 2 then (r, []) else
    apsnd (cons (if i mod 2 = 0 then A else B)) (mk_word r (l+1))
  end;

fun f s id0 = mk_word s 0
  | f s (Suc n) = f (fst (mk_word s 0)) n;

val g1 = snd o (f 20000.0);

val g2 = snd o (f 50000.0);

fun f1 id0 = [A,A]
  | f1 (Suc id0) = [B]
  | f1 (Suc (Suc id0)) = [A,B]
  | f1 _ = [];

fun f2 id0 = [A,A]
  | f2 (Suc id0) = [B]
  | f2 (Suc (Suc id0)) = [B,A]
  | f2 _ = [];

val xs1 = test g1;
val xs2 = test g2;
val xs3 = test f1;
val xs4 = test f2;
*}

end
