(*  Title:      ZF/QPair.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Many proofs are borrowed from pair.thy and sum.thy

Do we EVER have rank(a) < rank(<a;b>) ?  Perhaps if the latter rank
is not a limit ordinal? 
*)

header{*Quine-Inspired Ordered Pairs and Disjoint Sums*}

theory QPair imports Sum func begin

text{*For non-well-founded data
structures in ZF.  Does not precisely follow Quine's construction.  Thanks
to Thomas Forster for suggesting this approach!

W. V. Quine, On Ordered Pairs and Relations, in Selected Logic Papers,
1966.
*}

definition
  QPair     :: "[i, i] => i"                      ("<(_;/ _)>")  where
    "<a;b> == a+b"

definition
  qfst :: "i => i"  where
    "qfst(p) == THE a. \<exists>b. p=<a;b>"

definition
  qsnd :: "i => i"  where
    "qsnd(p) == THE b. \<exists>a. p=<a;b>"

definition
  qsplit    :: "[[i, i] => 'a, i] => 'a::{}"  (*for pattern-matching*)  where
    "qsplit(c,p) == c(qfst(p), qsnd(p))"

definition
  qconverse :: "i => i"  where
    "qconverse(r) == {z. w:r, \<exists>x y. w=<x;y> & z=<y;x>}"

definition
  QSigma    :: "[i, i => i] => i"  where
    "QSigma(A,B)  ==  \<Union>x\<in>A. \<Union>y\<in>B(x). {<x;y>}"

syntax
  "_QSUM"   :: "[idt, i, i] => i"               ("(3QSUM _:_./ _)" 10)
translations
  "QSUM x:A. B"  => "CONST QSigma(A, %x. B)"

abbreviation
  qprod  (infixr "<*>" 80) where
  "A <*> B == QSigma(A, %_. B)"

definition
  qsum    :: "[i,i]=>i"                         (infixr "<+>" 65)  where
    "A <+> B      == ({0} <*> A) \<union> ({1} <*> B)"

definition
  QInl :: "i=>i"  where
    "QInl(a)      == <0;a>"

definition
  QInr :: "i=>i"  where
    "QInr(b)      == <1;b>"

definition
  qcase     :: "[i=>i, i=>i, i]=>i"  where
    "qcase(c,d)   == qsplit(%y z. cond(y, d(z), c(z)))"


subsection{*Quine ordered pairing*}

(** Lemmas for showing that <a;b> uniquely determines a and b **)

lemma QPair_empty [simp]: "<0;0> = 0"
by (simp add: QPair_def)

lemma QPair_iff [simp]: "<a;b> = <c;d> \<longleftrightarrow> a=c & b=d"
apply (simp add: QPair_def)
apply (rule sum_equal_iff)
done

lemmas QPair_inject = QPair_iff [THEN iffD1, THEN conjE, elim!]

lemma QPair_inject1: "<a;b> = <c;d> ==> a=c"
by blast

lemma QPair_inject2: "<a;b> = <c;d> ==> b=d"
by blast


subsubsection{*QSigma: Disjoint union of a family of sets
     Generalizes Cartesian product*}

lemma QSigmaI [intro!]: "[| a:A;  b:B(a) |] ==> <a;b> \<in> QSigma(A,B)"
by (simp add: QSigma_def)


(** Elimination rules for <a;b>:A*B -- introducing no eigenvariables **)

lemma QSigmaE [elim!]:
    "[| c: QSigma(A,B);   
        !!x y.[| x:A;  y:B(x);  c=<x;y> |] ==> P  
     |] ==> P"
by (simp add: QSigma_def, blast) 

lemma QSigmaE2 [elim!]:
    "[| <a;b>: QSigma(A,B); [| a:A;  b:B(a) |] ==> P |] ==> P"
by (simp add: QSigma_def) 

lemma QSigmaD1: "<a;b> \<in> QSigma(A,B) ==> a \<in> A"
by blast

lemma QSigmaD2: "<a;b> \<in> QSigma(A,B) ==> b \<in> B(a)"
by blast

lemma QSigma_cong:
    "[| A=A';  !!x. x:A' ==> B(x)=B'(x) |] ==>  
     QSigma(A,B) = QSigma(A',B')"
by (simp add: QSigma_def) 

lemma QSigma_empty1 [simp]: "QSigma(0,B) = 0"
by blast

lemma QSigma_empty2 [simp]: "A <*> 0 = 0"
by blast


subsubsection{*Projections: qfst, qsnd*}

lemma qfst_conv [simp]: "qfst(<a;b>) = a"
by (simp add: qfst_def)

lemma qsnd_conv [simp]: "qsnd(<a;b>) = b"
by (simp add: qsnd_def)

lemma qfst_type [TC]: "p:QSigma(A,B) ==> qfst(p) \<in> A"
by auto

lemma qsnd_type [TC]: "p:QSigma(A,B) ==> qsnd(p) \<in> B(qfst(p))"
by auto

lemma QPair_qfst_qsnd_eq: "a: QSigma(A,B) ==> <qfst(a); qsnd(a)> = a"
by auto


subsubsection{*Eliminator: qsplit*}

(*A META-equality, so that it applies to higher types as well...*)
lemma qsplit [simp]: "qsplit(%x y. c(x,y), <a;b>) == c(a,b)"
by (simp add: qsplit_def)


lemma qsplit_type [elim!]:
    "[|  p:QSigma(A,B);    
         !!x y.[| x:A; y:B(x) |] ==> c(x,y):C(<x;y>)  
     |] ==> qsplit(%x y. c(x,y), p) \<in> C(p)"
by auto 

lemma expand_qsplit: 
 "u: A<*>B ==> R(qsplit(c,u)) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. u = <x;y> \<longrightarrow> R(c(x,y)))"
apply (simp add: qsplit_def, auto)
done


subsubsection{*qsplit for predicates: result type o*}

lemma qsplitI: "R(a,b) ==> qsplit(R, <a;b>)"
by (simp add: qsplit_def)


lemma qsplitE:
    "[| qsplit(R,z);  z:QSigma(A,B);                     
        !!x y. [| z = <x;y>;  R(x,y) |] ==> P            
    |] ==> P"
by (simp add: qsplit_def, auto) 

lemma qsplitD: "qsplit(R,<a;b>) ==> R(a,b)"
by (simp add: qsplit_def)


subsubsection{*qconverse*}

lemma qconverseI [intro!]: "<a;b>:r ==> <b;a>:qconverse(r)"
by (simp add: qconverse_def, blast)

lemma qconverseD [elim!]: "<a;b> \<in> qconverse(r) ==> <b;a> \<in> r"
by (simp add: qconverse_def, blast)

lemma qconverseE [elim!]:
    "[| yx \<in> qconverse(r);   
        !!x y. [| yx=<y;x>;  <x;y>:r |] ==> P  
     |] ==> P"
by (simp add: qconverse_def, blast) 

lemma qconverse_qconverse: "r<=QSigma(A,B) ==> qconverse(qconverse(r)) = r"
by blast

lemma qconverse_type: "r \<subseteq> A <*> B ==> qconverse(r) \<subseteq> B <*> A"
by blast

lemma qconverse_prod: "qconverse(A <*> B) = B <*> A"
by blast

lemma qconverse_empty: "qconverse(0) = 0"
by blast


subsection{*The Quine-inspired notion of disjoint sum*}

lemmas qsum_defs = qsum_def QInl_def QInr_def qcase_def

(** Introduction rules for the injections **)

lemma QInlI [intro!]: "a \<in> A ==> QInl(a) \<in> A <+> B"
by (simp add: qsum_defs, blast)

lemma QInrI [intro!]: "b \<in> B ==> QInr(b) \<in> A <+> B"
by (simp add: qsum_defs, blast)

(** Elimination rules **)

lemma qsumE [elim!]:
    "[| u: A <+> B;   
        !!x. [| x:A;  u=QInl(x) |] ==> P;  
        !!y. [| y:B;  u=QInr(y) |] ==> P  
     |] ==> P"
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

lemma QInlD: "QInl(a): A<+>B ==> a: A"
by blast

lemma QInrD: "QInr(b): A<+>B ==> b: B"
by blast

(** <+> is itself injective... who cares?? **)

lemma qsum_iff:
     "u: A <+> B \<longleftrightarrow> (\<exists>x. x:A & u=QInl(x)) | (\<exists>y. y:B & u=QInr(y))"
by blast

lemma qsum_subset_iff: "A <+> B \<subseteq> C <+> D \<longleftrightarrow> A<=C & B<=D"
by blast

lemma qsum_equal_iff: "A <+> B = C <+> D \<longleftrightarrow> A=C & B=D"
apply (simp (no_asm) add: extension qsum_subset_iff)
apply blast
done

subsubsection{*Eliminator -- qcase*}

lemma qcase_QInl [simp]: "qcase(c, d, QInl(a)) = c(a)"
by (simp add: qsum_defs )


lemma qcase_QInr [simp]: "qcase(c, d, QInr(b)) = d(b)"
by (simp add: qsum_defs )

lemma qcase_type:
    "[| u: A <+> B;  
        !!x. x: A ==> c(x): C(QInl(x));    
        !!y. y: B ==> d(y): C(QInr(y))  
     |] ==> qcase(c,d,u) \<in> C(u)"
by (simp add: qsum_defs, auto) 

(** Rules for the Part primitive **)

lemma Part_QInl: "Part(A <+> B,QInl) = {QInl(x). x: A}"
by blast

lemma Part_QInr: "Part(A <+> B,QInr) = {QInr(y). y: B}"
by blast

lemma Part_QInr2: "Part(A <+> B, %x. QInr(h(x))) = {QInr(y). y: Part(B,h)}"
by blast

lemma Part_qsum_equality: "C \<subseteq> A <+> B ==> Part(C,QInl) \<union> Part(C,QInr) = C"
by blast


subsubsection{*Monotonicity*}

lemma QPair_mono: "[| a<=c;  b<=d |] ==> <a;b> \<subseteq> <c;d>"
by (simp add: QPair_def sum_mono)

lemma QSigma_mono [rule_format]:
     "[| A<=C;  \<forall>x\<in>A. B(x) \<subseteq> D(x) |] ==> QSigma(A,B) \<subseteq> QSigma(C,D)"
by blast

lemma QInl_mono: "a<=b ==> QInl(a) \<subseteq> QInl(b)"
by (simp add: QInl_def subset_refl [THEN QPair_mono])

lemma QInr_mono: "a<=b ==> QInr(a) \<subseteq> QInr(b)"
by (simp add: QInr_def subset_refl [THEN QPair_mono])

lemma qsum_mono: "[| A<=C;  B<=D |] ==> A <+> B \<subseteq> C <+> D"
by blast

end
