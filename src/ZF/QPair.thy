(*  Title:      ZF/QPair.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Many proofs are borrowed from pair.thy and sum.thy

Do we EVER have rank(a) < rank(<a;b>) ?  Perhaps if the latter rank
is not a limit ordinal?
*)

section\<open>Quine-Inspired Ordered Pairs and Disjoint Sums\<close>

theory QPair imports Sum func begin

text\<open>For non-well-founded data
structures in ZF.  Does not precisely follow Quine's construction.  Thanks
to Thomas Forster for suggesting this approach!

W. V. Quine, On Ordered Pairs and Relations, in Selected Logic Papers,
1966.
\<close>

definition
  QPair     :: "[i, i] \<Rightarrow> i"                      (\<open><(_;/ _)>\<close>)  where
    "<a;b> \<equiv> a+b"

definition
  qfst :: "i \<Rightarrow> i"  where
    "qfst(p) \<equiv> THE a. \<exists>b. p=<a;b>"

definition
  qsnd :: "i \<Rightarrow> i"  where
    "qsnd(p) \<equiv> THE b. \<exists>a. p=<a;b>"

definition
  qsplit    :: "[[i, i] \<Rightarrow> 'a, i] \<Rightarrow> 'a::{}"  (*for pattern-matching*)  where
    "qsplit(c,p) \<equiv> c(qfst(p), qsnd(p))"

definition
  qconverse :: "i \<Rightarrow> i"  where
    "qconverse(r) \<equiv> {z. w \<in> r, \<exists>x y. w=<x;y> \<and> z=<y;x>}"

definition
  QSigma    :: "[i, i \<Rightarrow> i] \<Rightarrow> i"  where
    "QSigma(A,B)  \<equiv>  \<Union>x\<in>A. \<Union>y\<in>B(x). {<x;y>}"

syntax
  "_QSUM"   :: "[idt, i, i] \<Rightarrow> i"  (\<open>(\<open>indent=3 notation=\<open>binder QSUM\<in>\<close>\<close>QSUM _ \<in> _./ _)\<close> 10)
syntax_consts
  "_QSUM" \<rightleftharpoons> QSigma
translations
  "QSUM x \<in> A. B" => "CONST QSigma(A, \<lambda>x. B)"

abbreviation
  qprod  (infixr \<open><*>\<close> 80) where
  "A <*> B \<equiv> QSigma(A, \<lambda>_. B)"

definition
  qsum    :: "[i,i]\<Rightarrow>i"                         (infixr \<open><+>\<close> 65)  where
    "A <+> B      \<equiv> ({0} <*> A) \<union> ({1} <*> B)"

definition
  QInl :: "i\<Rightarrow>i"  where
    "QInl(a)      \<equiv> <0;a>"

definition
  QInr :: "i\<Rightarrow>i"  where
    "QInr(b)      \<equiv> <1;b>"

definition
  qcase     :: "[i\<Rightarrow>i, i\<Rightarrow>i, i]\<Rightarrow>i"  where
    "qcase(c,d)   \<equiv> qsplit(\<lambda>y z. cond(y, d(z), c(z)))"


subsection\<open>Quine ordered pairing\<close>

(** Lemmas for showing that <a;b> uniquely determines a and b **)

lemma QPair_empty [simp]: "<0;0> = 0"
by (simp add: QPair_def)

lemma QPair_iff [simp]: "<a;b> = <c;d> \<longleftrightarrow> a=c \<and> b=d"
apply (simp add: QPair_def)
apply (rule sum_equal_iff)
done

lemmas QPair_inject = QPair_iff [THEN iffD1, THEN conjE, elim!]

lemma QPair_inject1: "<a;b> = <c;d> \<Longrightarrow> a=c"
by blast

lemma QPair_inject2: "<a;b> = <c;d> \<Longrightarrow> b=d"
by blast


subsubsection\<open>QSigma: Disjoint union of a family of sets
     Generalizes Cartesian product\<close>

lemma QSigmaI [intro!]: "\<lbrakk>a \<in> A;  b \<in> B(a)\<rbrakk> \<Longrightarrow> <a;b> \<in> QSigma(A,B)"
by (simp add: QSigma_def)


(** Elimination rules for <a;b>:A*B -- introducing no eigenvariables **)

lemma QSigmaE [elim!]:
    "\<lbrakk>c \<in> QSigma(A,B);
        \<And>x y.\<lbrakk>x \<in> A;  y \<in> B(x);  c=<x;y>\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (simp add: QSigma_def, blast)

lemma QSigmaE2 [elim!]:
    "\<lbrakk><a;b>: QSigma(A,B); \<lbrakk>a \<in> A;  b \<in> B(a)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (simp add: QSigma_def)

lemma QSigmaD1: "<a;b> \<in> QSigma(A,B) \<Longrightarrow> a \<in> A"
by blast

lemma QSigmaD2: "<a;b> \<in> QSigma(A,B) \<Longrightarrow> b \<in> B(a)"
by blast

lemma QSigma_cong:
    "\<lbrakk>A=A';  \<And>x. x \<in> A' \<Longrightarrow> B(x)=B'(x)\<rbrakk> \<Longrightarrow>
     QSigma(A,B) = QSigma(A',B')"
by (simp add: QSigma_def)

lemma QSigma_empty1 [simp]: "QSigma(0,B) = 0"
by blast

lemma QSigma_empty2 [simp]: "A <*> 0 = 0"
by blast


subsubsection\<open>Projections: qfst, qsnd\<close>

lemma qfst_conv [simp]: "qfst(<a;b>) = a"
by (simp add: qfst_def)

lemma qsnd_conv [simp]: "qsnd(<a;b>) = b"
by (simp add: qsnd_def)

lemma qfst_type [TC]: "p \<in> QSigma(A,B) \<Longrightarrow> qfst(p) \<in> A"
by auto

lemma qsnd_type [TC]: "p \<in> QSigma(A,B) \<Longrightarrow> qsnd(p) \<in> B(qfst(p))"
by auto

lemma QPair_qfst_qsnd_eq: "a \<in> QSigma(A,B) \<Longrightarrow> <qfst(a); qsnd(a)> = a"
by auto


subsubsection\<open>Eliminator: qsplit\<close>

(*A META-equality, so that it applies to higher types as well...*)
lemma qsplit [simp]: "qsplit(\<lambda>x y. c(x,y), <a;b>) \<equiv> c(a,b)"
by (simp add: qsplit_def)


lemma qsplit_type [elim!]:
    "\<lbrakk>p \<in> QSigma(A,B);
         \<And>x y.\<lbrakk>x \<in> A; y \<in> B(x)\<rbrakk> \<Longrightarrow> c(x,y):C(<x;y>)
\<rbrakk> \<Longrightarrow> qsplit(\<lambda>x y. c(x,y), p) \<in> C(p)"
by auto

lemma expand_qsplit:
 "u \<in> A<*>B \<Longrightarrow> R(qsplit(c,u)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. u = <x;y> \<longrightarrow> R(c(x,y)))"
apply (simp add: qsplit_def, auto)
done


subsubsection\<open>qsplit for predicates: result type o\<close>

lemma qsplitI: "R(a,b) \<Longrightarrow> qsplit(R, <a;b>)"
by (simp add: qsplit_def)


lemma qsplitE:
    "\<lbrakk>qsplit(R,z);  z \<in> QSigma(A,B);
        \<And>x y. \<lbrakk>z = <x;y>;  R(x,y)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (simp add: qsplit_def, auto)

lemma qsplitD: "qsplit(R,<a;b>) \<Longrightarrow> R(a,b)"
by (simp add: qsplit_def)


subsubsection\<open>qconverse\<close>

lemma qconverseI [intro!]: "<a;b>:r \<Longrightarrow> <b;a>:qconverse(r)"
by (simp add: qconverse_def, blast)

lemma qconverseD [elim!]: "<a;b> \<in> qconverse(r) \<Longrightarrow> <b;a> \<in> r"
by (simp add: qconverse_def, blast)

lemma qconverseE [elim!]:
    "\<lbrakk>yx \<in> qconverse(r);
        \<And>x y. \<lbrakk>yx=<y;x>;  <x;y>:r\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (simp add: qconverse_def, blast)

lemma qconverse_qconverse: "r<=QSigma(A,B) \<Longrightarrow> qconverse(qconverse(r)) = r"
by blast

lemma qconverse_type: "r \<subseteq> A <*> B \<Longrightarrow> qconverse(r) \<subseteq> B <*> A"
by blast

lemma qconverse_prod: "qconverse(A <*> B) = B <*> A"
by blast

lemma qconverse_empty: "qconverse(0) = 0"
by blast


subsection\<open>The Quine-inspired notion of disjoint sum\<close>

lemmas qsum_defs = qsum_def QInl_def QInr_def qcase_def

(** Introduction rules for the injections **)

lemma QInlI [intro!]: "a \<in> A \<Longrightarrow> QInl(a) \<in> A <+> B"
by (simp add: qsum_defs, blast)

lemma QInrI [intro!]: "b \<in> B \<Longrightarrow> QInr(b) \<in> A <+> B"
by (simp add: qsum_defs, blast)

(** Elimination rules **)

lemma qsumE [elim!]:
    "\<lbrakk>u \<in> A <+> B;
        \<And>x. \<lbrakk>x \<in> A;  u=QInl(x)\<rbrakk> \<Longrightarrow> P;
        \<And>y. \<lbrakk>y \<in> B;  u=QInr(y)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
by (simp add: qsum_defs, blast)


(** Injection and freeness equivalences, for rewriting **)

lemma QInl_iff [iff]: "QInl(a)=QInl(b) \<longleftrightarrow> a=b"
by (simp add: qsum_defs )

lemma QInr_iff [iff]: "QInr(a)=QInr(b) \<longleftrightarrow> a=b"
by (simp add: qsum_defs )

lemma QInl_QInr_iff [simp]: "QInl(a)=QInr(b) \<longleftrightarrow> False"
by (simp add: qsum_defs )

lemma QInr_QInl_iff [simp]: "QInr(b)=QInl(a) \<longleftrightarrow> False"
by (simp add: qsum_defs )

lemma qsum_empty [simp]: "0<+>0 = 0"
by (simp add: qsum_defs )

(*Injection and freeness rules*)

lemmas QInl_inject = QInl_iff [THEN iffD1]
lemmas QInr_inject = QInr_iff [THEN iffD1]
lemmas QInl_neq_QInr = QInl_QInr_iff [THEN iffD1, THEN FalseE, elim!]
lemmas QInr_neq_QInl = QInr_QInl_iff [THEN iffD1, THEN FalseE, elim!]

lemma QInlD: "QInl(a): A<+>B \<Longrightarrow> a \<in> A"
by blast

lemma QInrD: "QInr(b): A<+>B \<Longrightarrow> b \<in> B"
by blast

(** <+> is itself injective... who cares?? **)

lemma qsum_iff:
     "u \<in> A <+> B \<longleftrightarrow> (\<exists>x. x \<in> A \<and> u=QInl(x)) | (\<exists>y. y \<in> B \<and> u=QInr(y))"
by blast

lemma qsum_subset_iff: "A <+> B \<subseteq> C <+> D \<longleftrightarrow> A<=C \<and> B<=D"
by blast

lemma qsum_equal_iff: "A <+> B = C <+> D \<longleftrightarrow> A=C \<and> B=D"
apply (simp (no_asm) add: extension qsum_subset_iff)
apply blast
done

subsubsection\<open>Eliminator -- qcase\<close>

lemma qcase_QInl [simp]: "qcase(c, d, QInl(a)) = c(a)"
by (simp add: qsum_defs )


lemma qcase_QInr [simp]: "qcase(c, d, QInr(b)) = d(b)"
by (simp add: qsum_defs )

lemma qcase_type:
    "\<lbrakk>u \<in> A <+> B;
        \<And>x. x \<in> A \<Longrightarrow> c(x): C(QInl(x));
        \<And>y. y \<in> B \<Longrightarrow> d(y): C(QInr(y))
\<rbrakk> \<Longrightarrow> qcase(c,d,u) \<in> C(u)"
by (simp add: qsum_defs, auto)

(** Rules for the Part primitive **)

lemma Part_QInl: "Part(A <+> B,QInl) = {QInl(x). x \<in> A}"
by blast

lemma Part_QInr: "Part(A <+> B,QInr) = {QInr(y). y \<in> B}"
by blast

lemma Part_QInr2: "Part(A <+> B, \<lambda>x. QInr(h(x))) = {QInr(y). y \<in> Part(B,h)}"
by blast

lemma Part_qsum_equality: "C \<subseteq> A <+> B \<Longrightarrow> Part(C,QInl) \<union> Part(C,QInr) = C"
by blast


subsubsection\<open>Monotonicity\<close>

lemma QPair_mono: "\<lbrakk>a<=c;  b<=d\<rbrakk> \<Longrightarrow> <a;b> \<subseteq> <c;d>"
by (simp add: QPair_def sum_mono)

lemma QSigma_mono [rule_format]:
     "\<lbrakk>A<=C;  \<forall>x\<in>A. B(x) \<subseteq> D(x)\<rbrakk> \<Longrightarrow> QSigma(A,B) \<subseteq> QSigma(C,D)"
by blast

lemma QInl_mono: "a<=b \<Longrightarrow> QInl(a) \<subseteq> QInl(b)"
by (simp add: QInl_def subset_refl [THEN QPair_mono])

lemma QInr_mono: "a<=b \<Longrightarrow> QInr(a) \<subseteq> QInr(b)"
by (simp add: QInr_def subset_refl [THEN QPair_mono])

lemma qsum_mono: "\<lbrakk>A<=C;  B<=D\<rbrakk> \<Longrightarrow> A <+> B \<subseteq> C <+> D"
by blast

end
