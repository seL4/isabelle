(*  Title:      HOL/Extraction.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* Program extraction for HOL *}

theory Extraction
imports Option
begin

ML_file "Tools/rewrite_hol_proof.ML"

subsection {* Setup *}

setup {*
  Extraction.add_types
      [("bool", ([], NONE))] #>
  Extraction.set_preprocessor (fn thy =>
      Proofterm.rewrite_proof_notypes
        ([], RewriteHOLProof.elim_cong :: ProofRewriteRules.rprocs true) o
      Proofterm.rewrite_proof thy
        (RewriteHOLProof.rews,
         ProofRewriteRules.rprocs true @ [ProofRewriteRules.expand_of_class thy]) o
      ProofRewriteRules.elim_vars (curry Const @{const_name default}))
*}

lemmas [extraction_expand] =
  meta_spec atomize_eq atomize_all atomize_imp atomize_conj
  allE rev_mp conjE Eq_TrueI Eq_FalseI eqTrueI eqTrueE eq_cong2
  notE' impE' impE iffE imp_cong simp_thms eq_True eq_False
  induct_forall_eq induct_implies_eq induct_equal_eq induct_conj_eq
  induct_atomize induct_atomize' induct_rulify induct_rulify'
  induct_rulify_fallback induct_trueI
  True_implies_equals TrueE

lemmas [extraction_expand_def] =
  induct_forall_def induct_implies_def induct_equal_def induct_conj_def
  induct_true_def induct_false_def

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
  "P y x \<Longrightarrow> P (snd (x, y)) (fst (x, y))" by simp

theorem exE_realizer: "P (snd p) (fst p) \<Longrightarrow>
  (\<And>x y. P y x \<Longrightarrow> Q (f x y)) \<Longrightarrow> Q (let (x, y) = p in f x y)"
  by (cases p) (simp add: Let_def)

theorem exE_realizer': "P (snd p) (fst p) \<Longrightarrow>
  (\<And>x y. P y x \<Longrightarrow> Q) \<Longrightarrow> Q" by (cases p) simp

realizers
  impI (P, Q): "\<lambda>pq. pq"
    "\<Lambda> (c: _) (d: _) P Q pq (h: _). allI \<cdot> _ \<bullet> c \<bullet> (\<Lambda> x. impI \<cdot> _ \<cdot> _ \<bullet> (h \<cdot> x))"

  impI (P): "Null"
    "\<Lambda> (c: _) P Q (h: _). allI \<cdot> _ \<bullet> c \<bullet> (\<Lambda> x. impI \<cdot> _ \<cdot> _ \<bullet> (h \<cdot> x))"

  impI (Q): "\<lambda>q. q" "\<Lambda> (c: _) P Q q. impI \<cdot> _ \<cdot> _"

  impI: "Null" "impI"

  mp (P, Q): "\<lambda>pq. pq"
    "\<Lambda> (c: _) (d: _) P Q pq (h: _) p. mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> c \<bullet> h)"

  mp (P): "Null"
    "\<Lambda> (c: _) P Q (h: _) p. mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> c \<bullet> h)"

  mp (Q): "\<lambda>q. q" "\<Lambda> (c: _) P Q q. mp \<cdot> _ \<cdot> _"

  mp: "Null" "mp"

  allI (P): "\<lambda>p. p" "\<Lambda> (c: _) P (d: _) p. allI \<cdot> _ \<bullet> d"

  allI: "Null" "allI"

  spec (P): "\<lambda>x p. p x" "\<Lambda> (c: _) P x (d: _) p. spec \<cdot> _ \<cdot> x \<bullet> d"

  spec: "Null" "spec"

  exI (P): "\<lambda>x p. (x, p)" "\<Lambda> (c: _) P x (d: _) p. exI_realizer \<cdot> P \<cdot> p \<cdot> x \<bullet> c \<bullet> d"

  exI: "\<lambda>x. x" "\<Lambda> P x (c: _) (h: _). h"

  exE (P, Q): "\<lambda>p pq. let (x, y) = p in pq x y"
    "\<Lambda> (c: _) (d: _) P Q (e: _) p (h: _) pq. exE_realizer \<cdot> P \<cdot> p \<cdot> Q \<cdot> pq \<bullet> c \<bullet> e \<bullet> d \<bullet> h"

  exE (P): "Null"
    "\<Lambda> (c: _) P Q (d: _) p. exE_realizer' \<cdot> _ \<cdot> _ \<cdot> _ \<bullet> c \<bullet> d"

  exE (Q): "\<lambda>x pq. pq x"
    "\<Lambda> (c: _) P Q (d: _) x (h1: _) pq (h2: _). h2 \<cdot> x \<bullet> h1"

  exE: "Null"
    "\<Lambda> P Q (c: _) x (h1: _) (h2: _). h2 \<cdot> x \<bullet> h1"

  conjI (P, Q): "Pair"
    "\<Lambda> (c: _) (d: _) P Q p (h: _) q. conjI_realizer \<cdot> P \<cdot> p \<cdot> Q \<cdot> q \<bullet> c \<bullet> d \<bullet> h"

  conjI (P): "\<lambda>p. p"
    "\<Lambda> (c: _) P Q p. conjI \<cdot> _ \<cdot> _"

  conjI (Q): "\<lambda>q. q"
    "\<Lambda> (c: _) P Q (h: _) q. conjI \<cdot> _ \<cdot> _ \<bullet> h"

  conjI: "Null" "conjI"

  conjunct1 (P, Q): "fst"
    "\<Lambda> (c: _) (d: _) P Q pq. conjunct1 \<cdot> _ \<cdot> _"

  conjunct1 (P): "\<lambda>p. p"
    "\<Lambda> (c: _) P Q p. conjunct1 \<cdot> _ \<cdot> _"

  conjunct1 (Q): "Null"
    "\<Lambda> (c: _) P Q q. conjunct1 \<cdot> _ \<cdot> _"

  conjunct1: "Null" "conjunct1"

  conjunct2 (P, Q): "snd"
    "\<Lambda> (c: _) (d: _) P Q pq. conjunct2 \<cdot> _ \<cdot> _"

  conjunct2 (P): "Null"
    "\<Lambda> (c: _) P Q p. conjunct2 \<cdot> _ \<cdot> _"

  conjunct2 (Q): "\<lambda>p. p"
    "\<Lambda> (c: _) P Q p. conjunct2 \<cdot> _ \<cdot> _"

  conjunct2: "Null" "conjunct2"

  disjI1 (P, Q): "Inl"
    "\<Lambda> (c: _) (d: _) P Q p. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sum.cases_1 \<cdot> P \<cdot> _ \<cdot> p \<bullet> arity_type_bool \<bullet> c \<bullet> d)"

  disjI1 (P): "Some"
    "\<Lambda> (c: _) P Q p. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_2 \<cdot> _ \<cdot> P \<cdot> p \<bullet> arity_type_bool \<bullet> c)"

  disjI1 (Q): "None"
    "\<Lambda> (c: _) P Q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_1 \<cdot> _ \<cdot> _ \<bullet> arity_type_bool \<bullet> c)"

  disjI1: "Left"
    "\<Lambda> P Q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sumbool.cases_1 \<cdot> _ \<cdot> _ \<bullet> arity_type_bool)"

  disjI2 (P, Q): "Inr"
    "\<Lambda> (d: _) (c: _) Q P q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sum.cases_2 \<cdot> _ \<cdot> Q \<cdot> q \<bullet> arity_type_bool \<bullet> c \<bullet> d)"

  disjI2 (P): "None"
    "\<Lambda> (c: _) Q P. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_1 \<cdot> _ \<cdot> _ \<bullet> arity_type_bool \<bullet> c)"

  disjI2 (Q): "Some"
    "\<Lambda> (c: _) Q P q. iffD2 \<cdot> _ \<cdot> _ \<bullet> (option.cases_2 \<cdot> _ \<cdot> Q \<cdot> q \<bullet> arity_type_bool \<bullet> c)"

  disjI2: "Right"
    "\<Lambda> Q P. iffD2 \<cdot> _ \<cdot> _ \<bullet> (sumbool.cases_2 \<cdot> _ \<cdot> _ \<bullet> arity_type_bool)"

  disjE (P, Q, R): "\<lambda>pq pr qr.
     (case pq of Inl p \<Rightarrow> pr p | Inr q \<Rightarrow> qr q)"
    "\<Lambda> (c: _) (d: _) (e: _) P Q R pq (h1: _) pr (h2: _) qr.
       disjE_realizer \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> R \<cdot> pr \<cdot> qr \<bullet> c \<bullet> d \<bullet> e \<bullet> h1 \<bullet> h2"

  disjE (Q, R): "\<lambda>pq pr qr.
     (case pq of None \<Rightarrow> pr | Some q \<Rightarrow> qr q)"
    "\<Lambda> (c: _) (d: _) P Q R pq (h1: _) pr (h2: _) qr.
       disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> R \<cdot> pr \<cdot> qr \<bullet> c \<bullet> d \<bullet> h1 \<bullet> h2"

  disjE (P, R): "\<lambda>pq pr qr.
     (case pq of None \<Rightarrow> qr | Some p \<Rightarrow> pr p)"
    "\<Lambda> (c: _) (d: _) P Q R pq (h1: _) pr (h2: _) qr (h3: _).
       disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> R \<cdot> qr \<cdot> pr \<bullet> c \<bullet> d \<bullet> h1 \<bullet> h3 \<bullet> h2"

  disjE (R): "\<lambda>pq pr qr.
     (case pq of Left \<Rightarrow> pr | Right \<Rightarrow> qr)"
    "\<Lambda> (c: _) P Q R pq (h1: _) pr (h2: _) qr.
       disjE_realizer3 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> R \<cdot> pr \<cdot> qr \<bullet> c \<bullet> h1 \<bullet> h2"

  disjE (P, Q): "Null"
    "\<Lambda> (c: _) (d: _) P Q R pq. disjE_realizer \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>x. R) \<cdot> _ \<cdot> _ \<bullet> c \<bullet> d \<bullet> arity_type_bool"

  disjE (Q): "Null"
    "\<Lambda> (c: _) P Q R pq. disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>x. R) \<cdot> _ \<cdot> _ \<bullet> c \<bullet> arity_type_bool"

  disjE (P): "Null"
    "\<Lambda> (c: _) P Q R pq (h1: _) (h2: _) (h3: _).
       disjE_realizer2 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>x. R) \<cdot> _ \<cdot> _ \<bullet> c \<bullet> arity_type_bool \<bullet> h1 \<bullet> h3 \<bullet> h2"

  disjE: "Null"
    "\<Lambda> P Q R pq. disjE_realizer3 \<cdot> _ \<cdot> _ \<cdot> pq \<cdot> (\<lambda>x. R) \<cdot> _ \<cdot> _ \<bullet> arity_type_bool"

  FalseE (P): "default"
    "\<Lambda> (c: _) P. FalseE \<cdot> _"

  FalseE: "Null" "FalseE"

  notI (P): "Null"
    "\<Lambda> (c: _) P (h: _). allI \<cdot> _ \<bullet> c \<bullet> (\<Lambda> x. notI \<cdot> _ \<bullet> (h \<cdot> x))"

  notI: "Null" "notI"

  notE (P, R): "\<lambda>p. default"
    "\<Lambda> (c: _) (d: _) P R (h: _) p. notE \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> c \<bullet> h)"

  notE (P): "Null"
    "\<Lambda> (c: _) P R (h: _) p. notE \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> c \<bullet> h)"

  notE (R): "default"
    "\<Lambda> (c: _) P R. notE \<cdot> _ \<cdot> _"

  notE: "Null" "notE"

  subst (P): "\<lambda>s t ps. ps"
    "\<Lambda> (c: _) s t P (d: _) (h: _) ps. subst \<cdot> s \<cdot> t \<cdot> P ps \<bullet> d \<bullet> h"

  subst: "Null" "subst"

  iffD1 (P, Q): "fst"
    "\<Lambda> (d: _) (c: _) Q P pq (h: _) p.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> p \<bullet> d \<bullet> (conjunct1 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD1 (P): "\<lambda>p. p"
    "\<Lambda> (c: _) Q P p (h: _). mp \<cdot> _ \<cdot> _ \<bullet> (conjunct1 \<cdot> _ \<cdot> _ \<bullet> h)"

  iffD1 (Q): "Null"
    "\<Lambda> (c: _) Q P q1 (h: _) q2.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> q2 \<bullet> c \<bullet> (conjunct1 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD1: "Null" "iffD1"

  iffD2 (P, Q): "snd"
    "\<Lambda> (c: _) (d: _) P Q pq (h: _) q.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> q \<bullet> d \<bullet> (conjunct2 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD2 (P): "\<lambda>p. p"
    "\<Lambda> (c: _) P Q p (h: _). mp \<cdot> _ \<cdot> _ \<bullet> (conjunct2 \<cdot> _ \<cdot> _ \<bullet> h)"

  iffD2 (Q): "Null"
    "\<Lambda> (c: _) P Q q1 (h: _) q2.
       mp \<cdot> _ \<cdot> _ \<bullet> (spec \<cdot> _ \<cdot> q2 \<bullet> c \<bullet> (conjunct2 \<cdot> _ \<cdot> _ \<bullet> h))"

  iffD2: "Null" "iffD2"

  iffI (P, Q): "Pair"
    "\<Lambda> (c: _) (d: _) P Q pq (h1 : _) qp (h2 : _). conjI_realizer \<cdot>
       (\<lambda>pq. \<forall>x. P x \<longrightarrow> Q (pq x)) \<cdot> pq \<cdot>
       (\<lambda>qp. \<forall>x. Q x \<longrightarrow> P (qp x)) \<cdot> qp \<bullet>
       (arity_type_fun \<bullet> c \<bullet> d) \<bullet>
       (arity_type_fun \<bullet> d \<bullet> c) \<bullet>
       (allI \<cdot> _ \<bullet> c \<bullet> (\<Lambda> x. impI \<cdot> _ \<cdot> _ \<bullet> (h1 \<cdot> x))) \<bullet>
       (allI \<cdot> _ \<bullet> d \<bullet> (\<Lambda> x. impI \<cdot> _ \<cdot> _ \<bullet> (h2 \<cdot> x)))"

  iffI (P): "\<lambda>p. p"
    "\<Lambda> (c: _) P Q (h1 : _) p (h2 : _). conjI \<cdot> _ \<cdot> _ \<bullet>
       (allI \<cdot> _ \<bullet> c \<bullet> (\<Lambda> x. impI \<cdot> _ \<cdot> _ \<bullet> (h1 \<cdot> x))) \<bullet>
       (impI \<cdot> _ \<cdot> _ \<bullet> h2)"

  iffI (Q): "\<lambda>q. q"
    "\<Lambda> (c: _) P Q q (h1 : _) (h2 : _). conjI \<cdot> _ \<cdot> _ \<bullet>
       (impI \<cdot> _ \<cdot> _ \<bullet> h1) \<bullet>
       (allI \<cdot> _ \<bullet> c \<bullet> (\<Lambda> x. impI \<cdot> _ \<cdot> _ \<bullet> (h2 \<cdot> x)))"

  iffI: "Null" "iffI"

end
