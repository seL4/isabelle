(*  Title:      HOL/NanoJava/AxSem.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Axiomatic Semantics (Hoare Logic)"

theory AxSem = State:

types assn   = "state => bool"
     vassn   = "val => assn"
      triple = "assn \<times> stmt \<times>  assn"
     etriple = "assn \<times> expr \<times> vassn"
translations
  "assn"   \<leftharpoondown> (type)"state => bool"
 "vassn"   \<leftharpoondown> (type)"val => assn"
  "triple" \<leftharpoondown> (type)"assn \<times> stmt \<times>  assn"
 "etriple" \<leftharpoondown> (type)"assn \<times> expr \<times> vassn"

consts   hoare   :: "(triple set \<times>  triple set) set"
consts  ehoare   :: "(triple set \<times> etriple    ) set"
syntax (xsymbols)
 "@hoare"  :: "[triple set,  triple set    ] => bool" ("_ |\<turnstile>/ _" [61,61]    60)
 "@hoare1" :: "[triple set,  assn,stmt,assn] => bool" 
                                   ("_ \<turnstile>/ ({(1_)}/ (_)/ {(1_)})" [61,3,90,3]60)
"@ehoare"  :: "[triple set,  etriple       ] => bool" ("_ |\<turnstile>\<^sub>e/ _"[61,61]60)
"@ehoare1" :: "[triple set,  assn,expr,vassn]=> bool"
                                  ("_ \<turnstile>\<^sub>e/ ({(1_)}/ (_)/ {(1_)})" [61,3,90,3]60)
syntax
 "@hoare"  :: "[triple set,  triple set    ] => bool" ("_ ||-/ _" [61,61] 60)
 "@hoare1" :: "[triple set,  assn,stmt,assn] => bool" 
                                  ("_ |-/ ({(1_)}/ (_)/ {(1_)})" [61,3,90,3] 60)
"@ehoare"  :: "[triple set,  etriple       ] => bool" ("_ ||-e/ _"[61,61] 60)
"@ehoare1" :: "[triple set,  assn,expr,vassn]=> bool"
                                 ("_ |-e/ ({(1_)}/ (_)/ {(1_)})" [61,3,90,3] 60)

translations "A |\<turnstile> C"        \<rightleftharpoons> "(A,C) \<in> hoare"
             "A  \<turnstile> {P}c{Q}"  \<rightleftharpoons> "A |\<turnstile> {(P,c,Q)}"
             "A |\<turnstile>\<^sub>e t"       \<rightleftharpoons> "(A,t) \<in> ehoare"
             "A |\<turnstile>\<^sub>e (P,e,Q)" \<rightleftharpoons> "(A,P,e,Q) \<in> ehoare" (** shouldn't be necess.**)
             "A  \<turnstile>\<^sub>e {P}e{Q}" \<rightleftharpoons> "A |\<turnstile>\<^sub>e (P,e,Q)"


inductive hoare ehoare
intros

  Skip:  "A |- {P} Skip {P}"

  Comp: "[| A |- {P} c1 {Q}; A |- {Q} c2 {R} |] ==> A |- {P} c1;;c2 {R}"

  Cond: "[| A |-e {P} e {Q}; 
            \<forall>v. A |- {Q v} (if v \<noteq> Null then c1 else c2) {R} |] ==>
            A |- {P} If(e) c1 Else c2 {R}"

  Loop: "A |- {\<lambda>s. P s \<and> s<x> \<noteq> Null} c {P} ==>
         A |- {P} While(x) c {\<lambda>s. P s \<and> s<x> = Null}"

  LAcc: "A |-e {\<lambda>s. P (s<x>) s} LAcc x {P}"

  LAss: "A |-e {P} e {\<lambda>v s.  Q (lupd(x\<mapsto>v) s)} ==>
         A |-  {P} x:==e {Q}"

  FAcc: "A |-e {P} e {\<lambda>v s. \<forall>a. v=Addr a --> Q (get_field s a f) s} ==>
         A |-e {P} e..f {Q}"

  FAss: "[| A |-e {P} e1 {\<lambda>v s. \<forall>a. v=Addr a --> Q a s};
        \<forall>a. A |-e {Q a} e2 {\<lambda>v s. R (upd_obj a f v s)} |] ==>
            A |-  {P} e1..f:==e2 {R}"

  NewC: "A |-e {\<lambda>s. \<forall>a. new_Addr s = Addr a --> P (Addr a) (new_obj a C s)}
                new C {P}"

  Cast: "A |-e {P} e {\<lambda>v s. (case v of Null => True 
                                 | Addr a => obj_class s a <=C C) --> Q v s} ==>
         A |-e {P} Cast C e {Q}"

  Call: "[| A |-e {P} e1 {Q}; \<forall>a. A |-e {Q a} e2 {R a};
    \<forall>a p l. A |- {\<lambda>s'. \<exists>s. R a p s \<and> l = s \<and> 
                    s' = lupd(This\<mapsto>a)(lupd(Param\<mapsto>p)(reset_locs s))}
                  Meth (C,m) {\<lambda>s. S (s<Res>) (set_locs l s)} |] ==>
             A |-e {P} {C}e1..m(e2) {S}"

  Meth: "\<forall>D. A |- {\<lambda>s'. \<exists>s a. s<This> = Addr a \<and> D = obj_class s a \<and> D <=C C \<and> 
                        P s \<and> s' = init_locs D m s}
                  Impl (D,m) {Q} ==>
             A |- {P} Meth (C,m) {Q}"

  (*\<Union>z instead of \<forall>z in the conclusion and
      z restricted to type state due to limitations of the inductive package *)
  Impl: "\<forall>z::state. A\<union> (\<Union>z. (\<lambda>Cm. (P z Cm, Impl Cm, Q z Cm))`Ms) ||- 
                            (\<lambda>Cm. (P z Cm, body Cm, Q z Cm))`Ms ==>
                      A ||- (\<lambda>Cm. (P z Cm, Impl Cm, Q z Cm))`Ms"

(* structural rules *)

  Asm:  "   a \<in> A ==> A ||- {a}"

  ConjI: " \<forall>c \<in> C. A ||- {c} ==> A ||- C"

  ConjE: "[|A ||- C; c \<in> C |] ==> A ||- {c}"

  Conseq:"[| \<forall>z::state. A |- {P' z} c {Q' z};
             \<forall>s t. (\<forall>z. P' z s --> Q' z t) --> (P s --> Q t) |] ==>
            A |- {P} c {Q }"

  (* z restricted to type state due to limitations of the inductive package *)
 eConseq:"[| \<forall>z::state. A |-e {P' z} c {Q' z};
             \<forall>s v t. (\<forall>z. P' z s --> Q' z v t) --> (P s --> Q v t) |] ==>
            A |-e {P} c {Q }"


subsection "Derived Rules"

lemma Conseq1: "\<lbrakk>A \<turnstile> {P'} c {Q}; \<forall>s. P s \<longrightarrow> P' s\<rbrakk> \<Longrightarrow> A \<turnstile> {P} c {Q}"
apply (rule hoare_ehoare.Conseq)
apply  (rule allI, assumption)
apply fast
done

lemma Conseq2: "\<lbrakk>A \<turnstile> {P} c {Q'}; \<forall>t. Q' t \<longrightarrow> Q t\<rbrakk> \<Longrightarrow> A \<turnstile> {P} c {Q}"
apply (rule hoare_ehoare.Conseq)
apply  (rule allI, assumption)
apply fast
done

lemma eConseq1: "\<lbrakk>A \<turnstile>\<^sub>e {P'} e {Q}; \<forall>s. P s \<longrightarrow> P' s\<rbrakk> \<Longrightarrow> A \<turnstile>\<^sub>e {P} e {Q}"
apply (rule hoare_ehoare.eConseq)
apply  (rule allI, assumption)
apply fast
done

lemma eConseq2: "\<lbrakk>A \<turnstile>\<^sub>e {P} e {Q'}; \<forall>v t. Q' v t \<longrightarrow> Q v t\<rbrakk> \<Longrightarrow> A \<turnstile>\<^sub>e {P} e {Q}"
apply (rule hoare_ehoare.eConseq)
apply  (rule allI, assumption)
apply fast
done

lemma Weaken: "\<lbrakk>A |\<turnstile> C'; C \<subseteq> C'\<rbrakk> \<Longrightarrow> A |\<turnstile> C"
apply (rule hoare_ehoare.ConjI)
apply clarify
apply (drule hoare_ehoare.ConjE)
apply  fast
apply assumption
done

lemma Union: "A |\<turnstile> (\<Union>z. C z) = (\<forall>z. A |\<turnstile> C z)"
by (auto intro: hoare_ehoare.ConjI hoare_ehoare.ConjE)

lemma Impl1: 
   "\<lbrakk>\<forall>z::state. A\<union> (\<Union>z. (\<lambda>Cm. (P z Cm, Impl Cm, Q z Cm))`Ms) |\<turnstile> 
                        (\<lambda>Cm. (P z Cm, body Cm, Q z Cm))`Ms; 
    Cm \<in> Ms\<rbrakk> \<Longrightarrow> 
                A         \<turnstile>  {P z Cm} Impl Cm {Q z Cm}"
apply (drule hoare_ehoare.Impl)
apply (erule Weaken)
apply (auto del: image_eqI intro: rev_image_eqI)
done

end
