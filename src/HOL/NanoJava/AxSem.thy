(*  Title:      HOL/NanoJava/AxSem.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Axiomatic Semantics (Hoare Logic)"

theory AxSem = State:

types assn   = "state => bool"
      triple = "assn \<times> stmt \<times> assn"
translations
  "assn"   \<leftharpoondown> (type)"state => bool"
  "triple" \<leftharpoondown> (type)"assn \<times> stmt \<times> assn"

consts   hoare   :: "(triple set \<times> triple set) set"
syntax (xsymbols)
 "@hoare"  :: "[triple set,  triple set    ] => bool" ("_ |\<turnstile>/ _" [61,61]    60)
 "@hoare1" :: "[triple set,  assn,stmt,assn] => bool" 
                                   ("_ \<turnstile>/ ({(1_)}/ (_)/ {(1_)})" [61,3,90,3]60)
syntax
 "@hoare"  :: "[triple set,  triple set    ] => bool" ("_ ||-/ _" [61,61] 60)
 "@hoare1" :: "[triple set,  assn,stmt,assn] => bool" 
                                  ("_ |-/ ({(1_)}/ (_)/ {(1_)})" [61,3,90,3] 60)

translations "A |\<turnstile> C"       \<rightleftharpoons> "(A,C) \<in> hoare"
             "A  \<turnstile> {P}c{Q}" \<rightleftharpoons> "A |\<turnstile> {(P,c,Q)}"

inductive hoare
intros

  Skip:  "A |- {P} Skip {P}"

  Comp: "[| A |- {P} c1 {Q}; A |- {Q} c2 {R} |] ==> A |- {P} c1;;c2 {R}"

  Cond: "[| A |- {\<lambda>s. P s \<and> s<e> \<noteq> Null} c1 {Q}; 
            A |- {\<lambda>s. P s \<and> s<e> = Null} c2 {Q}  |] ==>
            A |- {P} If(e) c1 Else c2 {Q}"

  Loop: "A |- {\<lambda>s. P s \<and> s<e> \<noteq> Null} c {P} ==>
         A |- {P} While(e) c {\<lambda>s. P s \<and> s<e> = Null}"

  NewC: "A |- {\<lambda>s.\<forall>a. new_Addr s=Addr a--> P (lupd(x|->Addr a)(new_obj a C s))}
              x:=new C {P}"

  Cast: "A |- {\<lambda>s.(case s<y> of Null=> True | Addr a=> obj_class s a <=C C) -->
              P (lupd(x|->s<y>) s)} x:=(C)y {P}"

  FAcc: "A |- {\<lambda>s.\<forall>a. s<y>=Addr a-->P(lupd(x|->get_field s a f) s)} x:=y..f{P}"

  FAss: "A |- {\<lambda>s. \<forall>a. s<y>=Addr a --> P (upd_obj a f (s<x>) s)} y..f:=x {P}"

  Call: "\<forall>l. A |- {\<lambda>s'. \<exists>s. P s \<and> l = s \<and> 
                    s' = lupd(This|->s<y>)(lupd(Param|->s<p>)(init_locs C m s))}
                  Meth C m {\<lambda>s. Q (lupd(x|->s<Res>)(set_locs l s))} ==>
             A |- {P} x:={C}y..m(p) {Q}"

  Meth: "\<forall>D. A |- {\<lambda>s. \<exists>a. s<This> = Addr a \<and> D=obj_class s a \<and> D <=C C \<and> P s}
                  Impl D m {Q} ==>
             A |- {P} Meth C m {Q}"

  (*\<Union>z instead of \<forall>z in the conclusion and
      z restricted to type state due to limitations of the inductive paackage *)
  Impl: "A\<union>   (\<Union>z::state. (\<lambda>(C,m). (P z C m, Impl C m, Q z C m))`ms) ||- 
               (\<Union>z::state. (\<lambda>(C,m). (P z C m, body C m, Q z C m))`ms) ==>
         A ||- (\<Union>z::state. (\<lambda>(C,m). (P z C m, Impl C m, Q z C m))`ms)"

(* structural rules *)

  (* z restricted to type state due to limitations of the inductive paackage *)
  Conseq:"[| \<forall>z::state. A |- {P' z} c {Q' z};
             \<forall>s t. (\<forall>z::state. P' z s --> Q' z t) --> (P s --> Q t) |] ==>
            A |- {P} c {Q }"

  Asm:  "   a \<in> A ==> A ||- {a}"

  ConjI: " \<forall>c \<in> C. A ||- {c} ==> A ||- C"

  ConjE: "[|A ||- C; c \<in> C |] ==> A ||- {c}";


subsection "Derived Rules"

lemma Conseq1: "\<lbrakk>A \<turnstile> {P'} c {Q}; \<forall>s. P s \<longrightarrow> P' s\<rbrakk> \<Longrightarrow> A \<turnstile> {P} c {Q}"
apply (rule hoare.Conseq)
apply  (rule allI, assumption)
apply fast
done

lemma Weaken: "\<lbrakk>A |\<turnstile> C'; C \<subseteq> C'\<rbrakk> \<Longrightarrow> A |\<turnstile> C"
apply (rule hoare.ConjI)
apply clarify
apply (drule hoare.ConjE)
apply  fast
apply assumption
done

lemma Union: "A |\<turnstile> (\<Union>z. C z) = (\<forall>z. A |\<turnstile> C z)"
by (auto intro: hoare.ConjI hoare.ConjE)

lemma Impl': 
  "\<forall>z. A\<union> (\<Union>z. (\<lambda>(C,m). (P z C m, Impl C m, Q (z::state) C m))`ms) ||- 
                (\<lambda>(C,m). (P z C m, body C m, Q (z::state) C m))`ms ==>
       A    ||- (\<lambda>(C,m). (P z C m, Impl C m, Q (z::state) C m))`ms"
apply (drule Union[THEN iffD2])
apply (drule hoare.Impl)
apply (drule Union[THEN iffD1])
apply (erule spec)
done

lemma Impl1: 
   "\<lbrakk>\<forall>z. A\<union> (\<Union>z. (\<lambda>(C,m). (P z C m, Impl C m, Q (z::state) C m))`ms) ||- 
                 (\<lambda>(C,m). (P z C m, body C m, Q (z::state) C m))`ms; 
    (C,m)\<in> ms\<rbrakk> \<Longrightarrow> 
         A             |- {P z C m} Impl C m {Q (z::state) C m}"
apply (drule Impl')
apply (erule Weaken)
apply (auto del: image_eqI intro: rev_image_eqI)
done

end
