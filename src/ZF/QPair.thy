(*  Title:      ZF/qpair.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Many proofs are borrowed from pair.thy and sum.thy

Do we EVER have rank(a) < rank(<a;b>) ?  Perhaps if the latter rank
    is not a limit ordinal? 
*)

header{*Quine-Inspired Ordered Pairs and Disjoint Sums*}

theory QPair = Sum + func:

text{*For non-well-founded data
structures in ZF.  Does not precisely follow Quine's construction.  Thanks
to Thomas Forster for suggesting this approach!

W. V. Quine, On Ordered Pairs and Relations, in Selected Logic Papers,
1966.
*}

constdefs
  QPair     :: "[i, i] => i"                      ("<(_;/ _)>")
    "<a;b> == a+b"

  qfst :: "i => i"
    "qfst(p) == THE a. EX b. p=<a;b>"

  qsnd :: "i => i"
    "qsnd(p) == THE b. EX a. p=<a;b>"

  qsplit    :: "[[i, i] => 'a, i] => 'a::logic"  (*for pattern-matching*)
    "qsplit(c,p) == c(qfst(p), qsnd(p))"

  qconverse :: "i => i"
    "qconverse(r) == {z. w:r, EX x y. w=<x;y> & z=<y;x>}"

  QSigma    :: "[i, i => i] => i"
    "QSigma(A,B)  ==  \<Union>x\<in>A. \<Union>y\<in>B(x). {<x;y>}"

syntax
  "@QSUM"   :: "[idt, i, i] => i"               ("(3QSUM _:_./ _)" 10)
  "<*>"     :: "[i, i] => i"                      (infixr 80)

translations
  "QSUM x:A. B"  => "QSigma(A, %x. B)"
  "A <*> B"      => "QSigma(A, _K(B))"

constdefs
  qsum    :: "[i,i]=>i"                         (infixr "<+>" 65)
    "A <+> B      == ({0} <*> A) Un ({1} <*> B)"

  QInl :: "i=>i"
    "QInl(a)      == <0;a>"

  QInr :: "i=>i"
    "QInr(b)      == <1;b>"

  qcase     :: "[i=>i, i=>i, i]=>i"
    "qcase(c,d)   == qsplit(%y z. cond(y, d(z), c(z)))"


print_translation {* [("QSigma", dependent_tr' ("@QSUM", "op <*>"))] *}


subsection{*Quine ordered pairing*}

(** Lemmas for showing that <a;b> uniquely determines a and b **)

lemma QPair_empty [simp]: "<0;0> = 0"
by (simp add: QPair_def)

lemma QPair_iff [simp]: "<a;b> = <c;d> <-> a=c & b=d"
apply (simp add: QPair_def)
apply (rule sum_equal_iff)
done

lemmas QPair_inject = QPair_iff [THEN iffD1, THEN conjE, standard, elim!]

lemma QPair_inject1: "<a;b> = <c;d> ==> a=c"
by blast

lemma QPair_inject2: "<a;b> = <c;d> ==> b=d"
by blast


subsubsection{*QSigma: Disjoint union of a family of sets
     Generalizes Cartesian product*}

lemma QSigmaI [intro!]: "[| a:A;  b:B(a) |] ==> <a;b> : QSigma(A,B)"
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

lemma QSigmaD1: "<a;b> : QSigma(A,B) ==> a : A"
by blast

lemma QSigmaD2: "<a;b> : QSigma(A,B) ==> b : B(a)"
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

lemma qfst_type [TC]: "p:QSigma(A,B) ==> qfst(p) : A"
by auto

lemma qsnd_type [TC]: "p:QSigma(A,B) ==> qsnd(p) : B(qfst(p))"
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
     |] ==> qsplit(%x y. c(x,y), p) : C(p)"
by auto 

lemma expand_qsplit: 
 "u: A<*>B ==> R(qsplit(c,u)) <-> (ALL x:A. ALL y:B. u = <x;y> --> R(c(x,y)))"
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

lemma qconverseD [elim!]: "<a;b> : qconverse(r) ==> <b;a> : r"
by (simp add: qconverse_def, blast)

lemma qconverseE [elim!]:
    "[| yx : qconverse(r);   
        !!x y. [| yx=<y;x>;  <x;y>:r |] ==> P  
     |] ==> P"
by (simp add: qconverse_def, blast) 

lemma qconverse_qconverse: "r<=QSigma(A,B) ==> qconverse(qconverse(r)) = r"
by blast

lemma qconverse_type: "r <= A <*> B ==> qconverse(r) <= B <*> A"
by blast

lemma qconverse_prod: "qconverse(A <*> B) = B <*> A"
by blast

lemma qconverse_empty: "qconverse(0) = 0"
by blast


subsection{*The Quine-inspired notion of disjoint sum*}

lemmas qsum_defs = qsum_def QInl_def QInr_def qcase_def

(** Introduction rules for the injections **)

lemma QInlI [intro!]: "a : A ==> QInl(a) : A <+> B"
by (simp add: qsum_defs, blast)

lemma QInrI [intro!]: "b : B ==> QInr(b) : A <+> B"
by (simp add: qsum_defs, blast)

(** Elimination rules **)

lemma qsumE [elim!]:
    "[| u: A <+> B;   
        !!x. [| x:A;  u=QInl(x) |] ==> P;  
        !!y. [| y:B;  u=QInr(y) |] ==> P  
     |] ==> P"
by (simp add: qsum_defs, blast) 


(** Injection and freeness equivalences, for rewriting **)

lemma QInl_iff [iff]: "QInl(a)=QInl(b) <-> a=b"
by (simp add: qsum_defs )

lemma QInr_iff [iff]: "QInr(a)=QInr(b) <-> a=b"
by (simp add: qsum_defs )

lemma QInl_QInr_iff [iff]: "QInl(a)=QInr(b) <-> False"
by (simp add: qsum_defs )

lemma QInr_QInl_iff [iff]: "QInr(b)=QInl(a) <-> False"
by (simp add: qsum_defs )

lemma qsum_empty [simp]: "0<+>0 = 0"
by (simp add: qsum_defs )

(*Injection and freeness rules*)

lemmas QInl_inject = QInl_iff [THEN iffD1, standard]
lemmas QInr_inject = QInr_iff [THEN iffD1, standard]
lemmas QInl_neq_QInr = QInl_QInr_iff [THEN iffD1, THEN FalseE]
lemmas QInr_neq_QInl = QInr_QInl_iff [THEN iffD1, THEN FalseE]

lemma QInlD: "QInl(a): A<+>B ==> a: A"
by blast

lemma QInrD: "QInr(b): A<+>B ==> b: B"
by blast

(** <+> is itself injective... who cares?? **)

lemma qsum_iff:
     "u: A <+> B <-> (EX x. x:A & u=QInl(x)) | (EX y. y:B & u=QInr(y))"
by blast

lemma qsum_subset_iff: "A <+> B <= C <+> D <-> A<=C & B<=D"
by blast

lemma qsum_equal_iff: "A <+> B = C <+> D <-> A=C & B=D"
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
     |] ==> qcase(c,d,u) : C(u)"
by (simp add: qsum_defs , auto) 

(** Rules for the Part primitive **)

lemma Part_QInl: "Part(A <+> B,QInl) = {QInl(x). x: A}"
by blast

lemma Part_QInr: "Part(A <+> B,QInr) = {QInr(y). y: B}"
by blast

lemma Part_QInr2: "Part(A <+> B, %x. QInr(h(x))) = {QInr(y). y: Part(B,h)}"
by blast

lemma Part_qsum_equality: "C <= A <+> B ==> Part(C,QInl) Un Part(C,QInr) = C"
by blast


subsubsection{*Monotonicity*}

lemma QPair_mono: "[| a<=c;  b<=d |] ==> <a;b> <= <c;d>"
by (simp add: QPair_def sum_mono)

lemma QSigma_mono [rule_format]:
     "[| A<=C;  ALL x:A. B(x) <= D(x) |] ==> QSigma(A,B) <= QSigma(C,D)"
by blast

lemma QInl_mono: "a<=b ==> QInl(a) <= QInl(b)"
by (simp add: QInl_def subset_refl [THEN QPair_mono])

lemma QInr_mono: "a<=b ==> QInr(a) <= QInr(b)"
by (simp add: QInr_def subset_refl [THEN QPair_mono])

lemma qsum_mono: "[| A<=C;  B<=D |] ==> A <+> B <= C <+> D"
by blast

ML
{*
val qsum_defs = thms "qsum_defs";

val QPair_empty = thm "QPair_empty";
val QPair_iff = thm "QPair_iff";
val QPair_inject = thm "QPair_inject";
val QPair_inject1 = thm "QPair_inject1";
val QPair_inject2 = thm "QPair_inject2";
val QSigmaI = thm "QSigmaI";
val QSigmaE = thm "QSigmaE";
val QSigmaE = thm "QSigmaE";
val QSigmaE2 = thm "QSigmaE2";
val QSigmaD1 = thm "QSigmaD1";
val QSigmaD2 = thm "QSigmaD2";
val QSigma_cong = thm "QSigma_cong";
val QSigma_empty1 = thm "QSigma_empty1";
val QSigma_empty2 = thm "QSigma_empty2";
val qfst_conv = thm "qfst_conv";
val qsnd_conv = thm "qsnd_conv";
val qfst_type = thm "qfst_type";
val qsnd_type = thm "qsnd_type";
val QPair_qfst_qsnd_eq = thm "QPair_qfst_qsnd_eq";
val qsplit = thm "qsplit";
val qsplit_type = thm "qsplit_type";
val expand_qsplit = thm "expand_qsplit";
val qsplitI = thm "qsplitI";
val qsplitE = thm "qsplitE";
val qsplitD = thm "qsplitD";
val qconverseI = thm "qconverseI";
val qconverseD = thm "qconverseD";
val qconverseE = thm "qconverseE";
val qconverse_qconverse = thm "qconverse_qconverse";
val qconverse_type = thm "qconverse_type";
val qconverse_prod = thm "qconverse_prod";
val qconverse_empty = thm "qconverse_empty";
val QInlI = thm "QInlI";
val QInrI = thm "QInrI";
val qsumE = thm "qsumE";
val QInl_iff = thm "QInl_iff";
val QInr_iff = thm "QInr_iff";
val QInl_QInr_iff = thm "QInl_QInr_iff";
val QInr_QInl_iff = thm "QInr_QInl_iff";
val qsum_empty = thm "qsum_empty";
val QInl_inject = thm "QInl_inject";
val QInr_inject = thm "QInr_inject";
val QInl_neq_QInr = thm "QInl_neq_QInr";
val QInr_neq_QInl = thm "QInr_neq_QInl";
val QInlD = thm "QInlD";
val QInrD = thm "QInrD";
val qsum_iff = thm "qsum_iff";
val qsum_subset_iff = thm "qsum_subset_iff";
val qsum_equal_iff = thm "qsum_equal_iff";
val qcase_QInl = thm "qcase_QInl";
val qcase_QInr = thm "qcase_QInr";
val qcase_type = thm "qcase_type";
val Part_QInl = thm "Part_QInl";
val Part_QInr = thm "Part_QInr";
val Part_QInr2 = thm "Part_QInr2";
val Part_qsum_equality = thm "Part_qsum_equality";
val QPair_mono = thm "QPair_mono";
val QSigma_mono = thm "QSigma_mono";
val QInl_mono = thm "QInl_mono";
val QInr_mono = thm "QInr_mono";
val qsum_mono = thm "qsum_mono";
*}

end

