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
  bar2 [CPure.intro]: "(\<forall>w. w # ws \<in> bar) \<Longrightarrow> ws \<in> bar"

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

theorem letter_cases:
  "(a::letter) \<noteq> b \<Longrightarrow> (x = a \<Longrightarrow> P) \<Longrightarrow> (x = b \<Longrightarrow> P) \<Longrightarrow> P"
  apply (case_tac a)
  apply (case_tac b)
  apply (case_tac x, simp, simp)
  apply (case_tac x, simp, simp)
  apply (case_tac b)
  apply (case_tac x, simp, simp)
  apply (case_tac x, simp, simp)
  done
  
theorem prop2:
  "xs \<in> bar \<Longrightarrow> \<forall>ys. ys \<in> bar \<longrightarrow>
     (\<forall>a b zs. a \<noteq> b \<longrightarrow> (xs, zs) \<in> T a \<longrightarrow> (ys, zs) \<in> T b \<longrightarrow> zs \<in> bar)"
  apply (erule bar.induct)
  apply (rule allI impI)+
  apply (rule bar1)
  apply (rule lemma3)
  apply assumption+
  apply (rule allI, rule impI)
  apply (erule bar.induct)
  apply (rule allI impI)+
  apply (rule bar1)
  apply (rule lemma3, assumption, assumption)
  apply (rule allI impI)+
  apply (rule bar2)
  apply (rule allI)
  apply (induct_tac w)
  apply (rule prop1)
  apply (rule_tac x=aa in letter_cases, assumption)
  apply hypsubst
  apply (erule_tac x=list in allE)
  apply (erule conjE)
  apply (erule_tac x=wsa in allE, erule impE)
  apply (rule bar2)
  apply rules
  apply (erule allE, erule allE, erule_tac x="(a # list) # zs" in allE,
    erule impE, assumption)
  apply (erule impE)
  apply (rule T1)
  apply assumption
  apply (erule mp)
  apply (rule T2)
  apply (erule not_sym)
  apply assumption
  apply hypsubst
  apply (rotate_tac 1)
  apply (erule_tac x=list in allE)
  apply (erule conjE)
  apply (erule allE, erule allE, erule_tac x="(b # list) # zs" in allE,
    erule impE)
  apply assumption
  apply (erule impE)
  apply (rule T2)
  apply assumption
  apply assumption
  apply (erule mp)
  apply (rule T1)
  apply assumption
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

theorem R_nil: "([], zs) \<in> R a \<Longrightarrow> zs = []"
  by (erule R.elims, simp+)

theorem letter_eq_dec: "(a::letter) = b \<or> a \<noteq> b"
  apply (case_tac a)
  apply (case_tac b)
  apply simp
  apply simp
  apply (case_tac b)
  apply simp
  apply simp
  done

theorem prop3: "xs \<in> bar \<Longrightarrow> \<forall>zs. (xs, zs) \<in> R a \<longrightarrow> zs \<in> bar"
  apply (erule bar.induct)
  apply (rule allI impI)+
  apply (rule bar1)
  apply (rule lemma2)
  apply assumption+
  apply (rule allI impI)+
  apply (case_tac ws)
  apply simp
  apply (drule R_nil)
  apply simp_all
  apply rules
  apply (rule bar2)
  apply (rule allI)
  apply (induct_tac w)
  apply (rule prop1)
  apply (rule_tac a1=aaa and b1=a in disjE [OF letter_eq_dec])
  apply rules
  apply (rule_tac xs="aa # list" and ys="lista # zs" and zs="(aaa # lista) # zs"
    and b=aaa in prop2 [rule_format])
  apply (rule bar2)
  apply rules
  apply assumption
  apply (erule not_sym)
  apply (rule T2)
  apply (erule not_sym)
  apply (erule lemma4)
  apply simp
  apply (rule T0)
  apply assumption+
  done

theorem prop5: "[w] \<in> bar"
  apply (induct_tac w)
  apply (rule prop1)
  apply (rule prop3 [rule_format])
  apply rules+
  done

theorem higman: "[] \<in> bar"
  apply (rule bar2)
  apply (rule allI)
  apply (rule prop5)
  done

consts
  is_prefix :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"

primrec
  "is_prefix [] f = True"
  "is_prefix (x # xs) f = (x = f (length xs) \<and> is_prefix xs f)"

theorem good_prefix_lemma:
  "ws \<in> bar \<Longrightarrow> is_prefix ws f \<longrightarrow> (\<exists>vs. is_prefix vs f \<and> vs \<in> good)"
  apply (erule bar.induct)
  apply rules
  apply (rule impI)
  apply (erule_tac x="f (length ws)" in allE)
  apply (erule conjE)
  apply (erule impE)
  apply simp
  apply assumption
  done

theorem good_prefix: "\<exists>vs. is_prefix vs f \<and> vs \<in> good"
  apply (insert higman)
  apply (drule good_prefix_lemma)
  apply simp
  done

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
  Program extracted from the proof of @{text prop5}:
  @{thm [display] prop5_def [no_vars]}
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
