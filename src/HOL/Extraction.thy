(*  Title:      HOL/Extraction.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Program extraction for HOL *}

theory Extraction = Datatype
files
  "Tools/rewrite_hol_proof.ML":

subsection {* Setup *}

ML_setup {*
  Context.>> (fn thy => thy |>
    Extraction.set_preprocessor (fn sg =>
      Proofterm.rewrite_proof_notypes
        ([], ("HOL/elim_cong", RewriteHOLProof.elim_cong) ::
          ProofRewriteRules.rprocs true) o
      Proofterm.rewrite_proof (Sign.tsig_of sg)
        (RewriteHOLProof.rews, ProofRewriteRules.rprocs true) o
      ProofRewriteRules.elim_vars (curry Const "arbitrary")))
*}

lemmas [extraction_expand] =
  atomize_eq atomize_all atomize_imp
  allE rev_mp conjE Eq_TrueI Eq_FalseI eqTrueI eqTrueE eq_cong2
  notE' impE' impE iffE imp_cong simp_thms
  induct_forall_eq induct_implies_eq induct_equal_eq
  induct_forall_def induct_implies_def
  induct_atomize induct_rulify1 induct_rulify2

datatype sumbool = Left | Right

subsection {* Type of extracted program *}

extract_type
  "typeof (Trueprop P) \<equiv> typeof P"

  "typeof P \<equiv> Type (TYPE(Null)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE('Q)) \<Longrightarrow>
     typeof (P \<longrightarrow> Q) \<equiv> Type (TYPE('Q))"

  "typeof Q \<equiv> Type (TYPE(Null)) \<Longrightarrow> typeof (P \<longrightarrow> Q) \<equiv> Type (TYPE(Null))"

  "typeof P \<equiv> Type (TYPE('P)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE('Q)) \<Longrightarrow>
     typeof (P \<longrightarrow> Q) \<equiv> Type (TYPE('P \<Rightarrow> 'Q))"

  "(\<lambda>x. typeof (P x)) \<equiv> (\<lambda>x. Type (TYPE(Null))) \<Longrightarrow>
     typeof (\<forall>x. P x) \<equiv> Type (TYPE(Null))"

  "(\<lambda>x. typeof (P x)) \<equiv> (\<lambda>x. Type (TYPE('P))) \<Longrightarrow>
     typeof (\<forall>x::'a. P x) \<equiv> Type (TYPE('a \<Rightarrow> 'P))"

  "(\<lambda>x. typeof (P x)) \<equiv> (\<lambda>x. Type (TYPE(Null))) \<Longrightarrow>
     typeof (\<exists>x::'a. P x) \<equiv> Type (TYPE('a))"

  "(\<lambda>x. typeof (P x)) \<equiv> (\<lambda>x. Type (TYPE('P))) \<Longrightarrow>
     typeof (\<exists>x::'a. P x) \<equiv> Type (TYPE('a \<times> 'P))"

  "typeof P \<equiv> Type (TYPE(Null)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE(Null)) \<Longrightarrow>
     typeof (P \<or> Q) \<equiv> Type (TYPE(sumbool))"

  "typeof P \<equiv> Type (TYPE(Null)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE('Q)) \<Longrightarrow>
     typeof (P \<or> Q) \<equiv> Type (TYPE('Q option))"

  "typeof P \<equiv> Type (TYPE('P)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE(Null)) \<Longrightarrow>
     typeof (P \<or> Q) \<equiv> Type (TYPE('P option))"

  "typeof P \<equiv> Type (TYPE('P)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE('Q)) \<Longrightarrow>
     typeof (P \<or> Q) \<equiv> Type (TYPE('P + 'Q))"

  "typeof P \<equiv> Type (TYPE(Null)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE('Q)) \<Longrightarrow>
     typeof (P \<and> Q) \<equiv> Type (TYPE('Q))"

  "typeof P \<equiv> Type (TYPE('P)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE(Null)) \<Longrightarrow>
     typeof (P \<and> Q) \<equiv> Type (TYPE('P))"

  "typeof P \<equiv> Type (TYPE('P)) \<Longrightarrow> typeof Q \<equiv> Type (TYPE('Q)) \<Longrightarrow>
     typeof (P \<and> Q) \<equiv> Type (TYPE('P \<times> 'Q))"

  "typeof (P = Q) \<equiv> typeof ((P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P))"

  "typeof (x \<in> P) \<equiv> typeof P"

subsection {* Realizability *}

realizability
  "(realizes t (Trueprop P)) \<equiv> (Trueprop (realizes t P))"

  "(typeof P) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<longrightarrow> Q)) \<equiv> (realizes Null P \<longrightarrow> realizes t Q)"

  "(typeof P) \<equiv> (Type (TYPE('P))) \<Longrightarrow>
   (typeof Q) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<longrightarrow> Q)) \<equiv> (\<forall>x::'P. realizes x P \<longrightarrow> realizes Null Q)"

  "(realizes t (P \<longrightarrow> Q)) \<equiv> (\<forall>x. realizes x P \<longrightarrow> realizes (t x) Q)"

  "(\<lambda>x. typeof (P x)) \<equiv> (\<lambda>x. Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (\<forall>x. P x)) \<equiv> (\<forall>x. realizes Null (P x))"

  "(realizes t (\<forall>x. P x)) \<equiv> (\<forall>x. realizes (t x) (P x))"

  "(\<lambda>x. typeof (P x)) \<equiv> (\<lambda>x. Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (\<exists>x. P x)) \<equiv> (realizes Null (P t))"

  "(realizes t (\<exists>x. P x)) \<equiv> (realizes (snd t) (P (fst t)))"

  "(typeof P) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
   (typeof Q) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<or> Q)) \<equiv>
     (case t of Left \<Rightarrow> realizes Null P | Right \<Rightarrow> realizes Null Q)"

  "(typeof P) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<or> Q)) \<equiv>
     (case t of None \<Rightarrow> realizes Null P | Some q \<Rightarrow> realizes q Q)"

  "(typeof Q) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<or> Q)) \<equiv>
     (case t of None \<Rightarrow> realizes Null Q | Some p \<Rightarrow> realizes p P)"

  "(realizes t (P \<or> Q)) \<equiv>
   (case t of Inl p \<Rightarrow> realizes p P | Inr q \<Rightarrow> realizes q Q)"

  "(typeof P) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<and> Q)) \<equiv> (realizes Null P \<and> realizes t Q)"

  "(typeof Q) \<equiv> (Type (TYPE(Null))) \<Longrightarrow>
     (realizes t (P \<and> Q)) \<equiv> (realizes t P \<and> realizes Null Q)"

  "(realizes t (P \<and> Q)) \<equiv> (realizes (fst t) P \<and> realizes (snd t) Q)"

  "typeof P \<equiv> Type (TYPE(Null)) \<Longrightarrow>
     realizes t (\<not> P) \<equiv> \<not> realizes Null P"

  "typeof P \<equiv> Type (TYPE('P)) \<Longrightarrow>
     realizes t (\<not> P) \<equiv> (\<forall>x::'P. \<not> realizes x P)"

  "typeof (P::bool) \<equiv> Type (TYPE(Null)) \<Longrightarrow>
   typeof Q \<equiv> Type (TYPE(Null)) \<Longrightarrow>
     realizes t (P = Q) \<equiv> realizes Null P = realizes Null Q"

  "(realizes t (P = Q)) \<equiv> (realizes t ((P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)))"

subsection {* Computational content of basic inference rules *}

theorem disjE_realizer:
  assumes r: "case x of Inl p \<Rightarrow> P p | Inr q \<Rightarrow> Q q"
  and r1: "\<And>p. P p \<Longrightarrow> R (f p)" and r2: "\<And>q. Q q \<Longrightarrow> R (g q)"
  shows "R (case x of Inl p \<Rightarrow> f p | Inr q \<Rightarrow> g q)"
proof (cases x)
  case Inl
  with r show ?thesis by simp (rule r1)
next
  case Inr
  with r show ?thesis by simp (rule r2)
qed

theorem disjE_realizer2:
  assumes r: "case x of None \<Rightarrow> P | Some q \<Rightarrow> Q q"
  and r1: "P \<Longrightarrow> R f" and r2: "\<And>q. Q q \<Longrightarrow> R (g q)"
  shows "R (case x of None \<Rightarrow> f | Some q \<Rightarrow> g q)"
proof (cases x)
  case None
  with r show ?thesis by simp (rule r1)
next
  case Some
  with r show ?thesis by simp (rule r2)
qed

theorem disjE_realizer3:
  assumes r: "case x of Left \<Rightarrow> P | Right \<Rightarrow> Q"
  and r1: "P \<Longrightarrow> R f" and r2: "Q \<Longrightarrow> R g"
  shows "R (case x of Left \<Rightarrow> f | Right \<Rightarrow> g)"
proof (cases x)
  case Left
  with r show ?thesis by simp (rule r1)
next
  case Right
  with r show ?thesis by simp (rule r2)
qed

theorem conjI_realizer:
  "P p \<Longrightarrow> Q q \<Longrightarrow> P (fst (p, q)) \<and> Q (snd (p, q))"
  by simp

theorem exI_realizer:
  "P x y \<Longrightarrow> P (fst (x, y)) (snd (x, y))" by simp

realizers
  impI (P, Q): "\<lambda>P Q pq. pq"
    "\<Lambda>P Q pq (h: _). allI \<cdot> _ \<bullet> (\<Lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h \<cdot> x))"

  impI (P): "Null"
    "\<Lambda>P Q (h: _). allI \<cdot> _ \<bullet> (\<Lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h \<cdot> x))"

  impI (Q): "\<lambda>P Q q. q" "\<Lambda>P Q q. impI \<cdot> _ \<cdot> _"

  impI: "Null" "\<Lambda>P Q. impI \<cdot> _ \<cdot> _"

  mp (P, Q): "\<lambda>P Q pq. pq"
    "\<Lambda>P Q pq (h: _) p. mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> h)"

  mp (P): "Null"
    "\<Lambda>P Q (h: _) p. mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> h)"

  mp (Q): "\<lambda>P Q q. q" "\<Lambda>P Q q. mp \<cdot> _ \<cdot> _"

  mp: "Null" "\<Lambda>P Q. mp \<cdot> _ \<cdot> _"

  allI (P): "\<lambda>P p. p" "\<Lambda>P p. allI \<cdot> _"

  allI: "Null" "\<Lambda>P. allI \<cdot> _"

  spec (P): "\<lambda>P x p. p x" "\<Lambda>P x p. spec \<cdot> _ \<cdot> x"

  spec: "Null" "\<Lambda>P x. spec \<cdot> _ \<cdot> x"

  exI (P): "\<lambda>P x p. (x, p)" "\<Lambda>P. exI_realizer \<cdot> _"

  exI: "\<lambda>P x. x" "\<Lambda>P x (h: _). h"

  exE (P, Q): "\<lambda>P Q p pq. pq (fst p) (snd p)"
    "\<Lambda>P Q p (h1: _) pq (h2: _). h2 \<cdot> (fst p) \<cdot> (snd p) \<bullet> h1"

  exE (P): "Null"
    "\<Lambda>P Q p (h1: _) (h2: _). h2 \<cdot> (fst p) \<cdot> (snd p) \<bullet> h1"

  exE (Q): "\<lambda>P Q x pq. pq x"
    "\<Lambda>P Q x (h1: _) pq (h2: _). h2 \<cdot> x \<bullet> h1"

  exE: "Null"
    "\<Lambda>P Q x (h1: _) (h2: _). h2 \<cdot> x \<bullet> h1"

  conjI (P, Q): "\<lambda>P Q p q. (p, q)"
    "\<Lambda>P Q p (h: _) q. conjI_realizer \<cdot>
       (\<lambda>p. realizes p P) \<cdot> p \<cdot> (\<lambda>q. realizes q Q) \<cdot> q \<bullet> h"

  conjI (P): "\<lambda>P Q p. p"
    "\<Lambda>P Q p. conjI \<cdot> _ \<cdot> _"

  conjI (Q): "\<lambda>P Q q. q"
    "\<Lambda>P Q (h: _) q. conjI \<cdot> _ \<cdot> _ \<bullet> h"

  conjI: "Null"
    "\<Lambda>P Q. conjI \<cdot> _ \<cdot> _"

  conjunct1 (P, Q): "\<lambda>P Q. fst"
    "\<Lambda>P Q pq. conjunct1 \<cdot> _ \<cdot> _"

  conjunct1 (P): "\<lambda>P Q p. p"
    "\<Lambda>P Q p. conjunct1 \<cdot> _ \<cdot> _"

  conjunct1 (Q): "Null"
    "\<Lambda>P Q q. conjunct1 \<cdot> _ \<cdot> _"

  conjunct1: "Null"
    "\<Lambda>P Q. conjunct1 \<cdot> _ \<cdot> _"

  conjunct2 (P, Q): "\<lambda>P Q. snd"
    "\<Lambda>P Q pq. conjunct2 \<cdot> _ \<cdot> _"

  conjunct2 (P): "Null"
    "\<Lambda>P Q p. conjunct2 \<cdot> _ \<cdot> _"

  conjunct2 (Q): "\<lambda>P Q p. p"
    "\<Lambda>P Q p. conjunct2 \<cdot> _ \<cdot> _"

  conjunct2: "Null"
    "\<Lambda>P Q. conjunct2 \<cdot> _ \<cdot> _"

  disjI1 (P, Q): "\<lambda>P Q. Inl"
    "\<Lambda>P Q p. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sum.cases_1 \<cdot> (\<lambda>p. realizes p P) \<cdot> _ \<cdot> p)"

  disjI1 (P): "\<lambda>P Q. Some"
    "\<Lambda>P Q p. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_2 \<cdot> _ \<cdot> (\<lambda>p. realizes p P) \<cdot> p)"

  disjI1 (Q): "\<lambda>P Q. None"
    "\<Lambda>P Q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_1 \<cdot> _ \<cdot> _)"

  disjI1: "\<lambda>P Q. Left"
    "\<Lambda>P Q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sumbool.cases_1 \<cdot> _ \<cdot> _)"

  disjI2 (P, Q): "\<lambda>Q P. Inr"
    "\<Lambda>Q P q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sum.cases_2 \<cdot> _ \<cdot> (\<lambda>q. realizes q Q) \<cdot> q)"

  disjI2 (P): "\<lambda>Q P. None"
    "\<Lambda>Q P. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_1 \<cdot> _ \<cdot> _)"

  disjI2 (Q): "\<lambda>Q P. Some"
    "\<Lambda>Q P q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_2 \<cdot> _ \<cdot> (\<lambda>q. realizes q Q) \<cdot> q)"

  disjI2: "\<lambda>Q P. Right"
    "\<Lambda>Q P. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sumbool.cases_2 \<cdot> _ \<cdot> _)"

  disjE (P, Q, R): "\<lambda>P Q R pq pr qr.
     (case pq of Inl p \<Rightarrow> pr p | Inr q \<Rightarrow> qr q)"
    "\<Lambda>P Q R pq (h1: _) pr (h2: _) qr.
       disjE_realizer \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes r R) \<cdot> pr \<cdot> qr \<bullet> h1 \<bullet> h2"

  disjE (Q, R): "\<lambda>P Q R pq pr qr.
     (case pq of None \<Rightarrow> pr | Some q \<Rightarrow> qr q)"
    "\<Lambda>P Q R pq (h1: _) pr (h2: _) qr.
       disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes r R) \<cdot> pr \<cdot> qr \<bullet> h1 \<bullet> h2"

  disjE (P, R): "\<lambda>P Q R pq pr qr.
     (case pq of None \<Rightarrow> qr | Some p \<Rightarrow> pr p)"
    "\<Lambda>P Q R pq (h1: _) pr (h2: _) qr (h3: _).
       disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes r R) \<cdot> qr \<cdot> pr \<bullet> h1 \<bullet> h3 \<bullet> h2"

  disjE (R): "\<lambda>P Q R pq pr qr.
     (case pq of Left \<Rightarrow> pr | Right \<Rightarrow> qr)"
    "\<Lambda>P Q R pq (h1: _) pr (h2: _) qr.
       disjE_realizer3 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes r R) \<cdot> pr \<cdot> qr \<bullet> h1 \<bullet> h2"

  disjE (P, Q): "Null"
    "\<Lambda>P Q R pq. disjE_realizer \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes Null R) \<cdot> _ \<cdot> _"

  disjE (Q): "Null"
    "\<Lambda>P Q R pq. disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes Null R) \<cdot> _ \<cdot> _"

  disjE (P): "Null"
    "\<Lambda>P Q R pq (h1: _) (h2: _) (h3: _).
       disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes Null R) \<cdot> _ \<cdot> _ \<bullet> h1 \<bullet> h3 \<bullet> h2"

  disjE: "Null"
    "\<Lambda>P Q R pq. disjE_realizer3 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>r. realizes Null R) \<cdot> _ \<cdot> _"

  FalseE (P): "\<lambda>P. arbitrary"
    "\<Lambda>P. FalseE \<cdot> _"

  FalseE: "Null"
    "\<Lambda>P. FalseE \<cdot> _"

  notI (P): "Null"
    "\<Lambda>P (h: _). allI \<cdot> _ \<bullet> (\<Lambda>x. notI \<cdot> _ \<bullet> (h \<cdot> x))"

  notI: "Null"
    "\<Lambda>P. notI \<cdot> _"

  notE (P, R): "\<lambda>P R p. arbitrary"
    "\<Lambda>P R (h: _) p. notE \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> h)"

  notE (P): "Null"
    "\<Lambda>P R (h: _) p. notE \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> h)"

  notE (R): "\<lambda>P R. arbitrary"
    "\<Lambda>P R. notE \<cdot> _ \<cdot> _"

  notE: "Null"
    "\<Lambda>P R. notE \<cdot> _ \<cdot> _"

  subst (P): "\<lambda>s t P ps. ps"
    "\<Lambda>s t P (h: _) ps. subst \<cdot> s \<cdot> t \<cdot> (\<lambda>x. realizes ps (P x)) \<bullet> h"

  subst: "Null"
    "\<Lambda>s t P. subst \<cdot> s \<cdot> t \<cdot> (\<lambda>x. realizes Null (P x))"

  iffD1 (P, Q): "\<lambda>Q P. fst"
    "\<Lambda>Q P pq (h: _) p.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> (conjunct1 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD1 (P): "\<lambda>Q P p. p"
    "\<Lambda>Q P p (h: _). mp \<cdot> _ \<cdot> _ \<bullet> (conjunct1 \<cdot> _ \<cdot> _ \<bullet> h)"

  iffD1 (Q): "Null"
    "\<Lambda>Q P q1 (h: _) q2.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> q2 \<bullet> (conjunct1 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD1: "Null"
    "\<Lambda>Q P. iffD1 \<cdot> _ \<cdot> _"

  iffD2 (P, Q): "\<lambda>P Q. snd"
    "\<Lambda>P Q pq (h: _) q.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> q \<bullet> (conjunct2 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD2 (P): "\<lambda>P Q p. p"
    "\<Lambda>P Q p (h: _). mp \<cdot> _ \<cdot> _ \<bullet> (conjunct2 \<cdot> _ \<cdot> _ \<bullet> h)"

  iffD2 (Q): "Null"
    "\<Lambda>P Q q1 (h: _) q2.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> q2 \<bullet> (conjunct2 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD2: "Null"
    "\<Lambda>P Q. iffD2 \<cdot> _ \<cdot> _"

  iffI (P, Q): "\<lambda>P Q pq qp. (pq, qp)"
    "\<Lambda>P Q pq (h1 : _) qp (h2 : _). conjI_realizer \<cdot>
       (\<lambda>pq. \<forall>x. realizes x P \<longrightarrow> realizes (pq x) Q) \<cdot> pq \<cdot>
       (\<lambda>qp. \<forall>x. realizes x Q \<longrightarrow> realizes (qp x) P) \<cdot> qp \<bullet>
       (allI \<cdot> _ \<bullet> (\<Lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h1 \<cdot> x))) \<bullet>
       (allI \<cdot> _ \<bullet> (\<Lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h2 \<cdot> x)))"

  iffI (P): "\<lambda>P Q p. p"
    "\<Lambda>P Q (h1 : _) p (h2 : _). conjI \<cdot> _ \<cdot> _ \<bullet>
       (allI \<cdot> _ \<bullet> (\<Lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h1 \<cdot> x))) \<bullet>
       (impI \<cdot> _ \<cdot> _ \<bullet> h2)"

  iffI (Q): "\<lambda>P Q q. q"
    "\<Lambda>P Q q (h1 : _) (h2 : _). conjI \<cdot> _ \<cdot> _ \<bullet>
       (impI \<cdot> _ \<cdot> _ \<bullet> h1) \<bullet>
       (allI \<cdot> _ \<bullet> (\<Lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h2 \<cdot> x)))"

  iffI: "Null"
    "\<Lambda>P Q. iffI \<cdot> _ \<cdot> _"

  classical: "Null"
    "\<Lambda>P. classical \<cdot> _"

end
